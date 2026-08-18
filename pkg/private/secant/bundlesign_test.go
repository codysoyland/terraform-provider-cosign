package secant

import (
	"context"
	"crypto"
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/x509"
	"crypto/x509/pkix"
	"encoding/asn1"
	"encoding/base64"
	"encoding/json"
	"encoding/pem"
	"fmt"
	"io"
	"math/big"
	"net/http"
	"net/http/httptest"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/digitorus/timestamp"
	protobundle "github.com/sigstore/protobuf-specs/gen/pb-go/bundle/v1"
	protocommon "github.com/sigstore/protobuf-specs/gen/pb-go/common/v1"
	prototrustroot "github.com/sigstore/protobuf-specs/gen/pb-go/trustroot/v1"
	"github.com/sigstore/sigstore-go/pkg/root"
	"github.com/sigstore/sigstore-go/pkg/sign"
	"google.golang.org/protobuf/encoding/protojson"
)

func TestCertNeedsRefreshNilCert(t *testing.T) {
	bs := &BundleSigner{}
	if !bs.certNeedsRefresh() {
		t.Error("expected refresh needed when cert is nil")
	}
}

func TestCertNeedsRefreshValidCert(t *testing.T) {
	_, cert := generateTestCert(t, 10*time.Minute)
	bs := &BundleSigner{cert: cert}
	if bs.certNeedsRefresh() {
		t.Error("expected no refresh needed when cert is valid for 10 minutes")
	}
}

func TestCertNeedsRefreshExpiredCert(t *testing.T) {
	_, cert := generateTestCert(t, -1*time.Minute)
	bs := &BundleSigner{cert: cert}
	if !bs.certNeedsRefresh() {
		t.Error("expected refresh needed when cert is expired")
	}
}

func TestCertNeedsRefreshNearExpiry(t *testing.T) {
	// 10 seconds remaining is within the 30-second buffer.
	_, cert := generateTestCert(t, 10*time.Second)
	bs := &BundleSigner{cert: cert}
	if !bs.certNeedsRefresh() {
		t.Error("expected refresh needed when cert expires within 30s buffer")
	}
}

func TestCacheCertFromBundle(t *testing.T) {
	certPEM, cert := generateTestCert(t, 10*time.Minute)
	derBlock, _ := pem.Decode(certPEM)
	bundleJSON := buildTestBundleJSONCertificate(t, derBlock.Bytes)

	bs := &BundleSigner{}
	if err := bs.cacheCertFromBundle(bundleJSON); err != nil {
		t.Fatalf("cacheCertFromBundle: %v", err)
	}

	if bs.cert == nil {
		t.Fatal("expected cert to be cached")
	}
	if bs.cert.NotAfter != cert.NotAfter {
		t.Errorf("cached cert NotAfter = %v, want %v", bs.cert.NotAfter, cert.NotAfter)
	}
	if len(bs.certPEM) == 0 {
		t.Error("expected certPEM to be set")
	}
}

func TestCacheCertFromBundleNoCerts(t *testing.T) {
	// Bundle with empty verification material.
	bundleJSON := []byte(`{"mediaType":"application/vnd.dev.sigstore.bundle.v0.3+json","verificationMaterial":{}}`)
	bs := &BundleSigner{}
	if err := bs.cacheCertFromBundle(bundleJSON); err == nil {
		t.Fatal("expected error when bundle has no certificate")
	}
}

// generateTestCert creates a self-signed certificate valid for the given duration.
// Negative durations produce already-expired certificates.
func generateTestCert(t *testing.T, validity time.Duration) ([]byte, *x509.Certificate) {
	t.Helper()
	_, certPEM, cert := generateTestCertKey(t, validity)
	return certPEM, cert
}

// generateTestCertKey is generateTestCert but also returns the private key,
// for fakes that need to produce signatures (e.g. RFC3161 responses).
func generateTestCertKey(t *testing.T, validity time.Duration) (*ecdsa.PrivateKey, []byte, *x509.Certificate) {
	t.Helper()

	key, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		t.Fatalf("generating key: %v", err)
	}

	now := time.Now()
	template := &x509.Certificate{
		SerialNumber: big.NewInt(1),
		Subject:      pkix.Name{CommonName: "test"},
		NotBefore:    now.Add(-1 * time.Hour),
		NotAfter:     now.Add(validity),
	}

	derBytes, err := x509.CreateCertificate(rand.Reader, template, template, &key.PublicKey, key)
	if err != nil {
		t.Fatalf("creating certificate: %v", err)
	}

	cert, err := x509.ParseCertificate(derBytes)
	if err != nil {
		t.Fatalf("parsing certificate: %v", err)
	}

	certPEM := pem.EncodeToMemory(&pem.Block{
		Type:  "CERTIFICATE",
		Bytes: derBytes,
	})

	return key, certPEM, cert
}

// recordingTransport wraps http.DefaultTransport and records the URL of
// every request routed through it.
type recordingTransport struct {
	mu   sync.Mutex
	urls []string
}

func (rt *recordingTransport) RoundTrip(req *http.Request) (*http.Response, error) {
	rt.mu.Lock()
	rt.urls = append(rt.urls, req.URL.String())
	rt.mu.Unlock()
	return http.DefaultTransport.RoundTrip(req)
}

func (rt *recordingTransport) countWithPrefix(prefix string) int {
	rt.mu.Lock()
	defer rt.mu.Unlock()
	n := 0
	for _, u := range rt.urls {
		if strings.HasPrefix(u, prefix) {
			n++
		}
	}
	return n
}

// staticOIDCProvider implements fulcio.OIDCProvider with a fixed token.
type staticOIDCProvider struct {
	token string
}

func (p *staticOIDCProvider) Enabled(context.Context) bool { return true }
func (p *staticOIDCProvider) Provide(context.Context, string) (string, error) {
	return p.token, nil
}

// testIDToken builds an unsigned JWT carrying the subject claim the Fulcio
// client extracts before requesting a certificate.
func testIDToken() string {
	header := base64.RawURLEncoding.EncodeToString([]byte(`{"alg":"none"}`))
	payload := base64.RawURLEncoding.EncodeToString([]byte(`{"sub":"test-subject"}`))
	return header + "." + payload + ".unsigned"
}

// fakeSigstore is the httptest trio backing an end-to-end SignContent call:
// a Fulcio that issues a fixed cert, a TSA that produces genuine RFC3161
// responses, and a Rekor v2 log that accepts any entry.
type fakeSigstore struct {
	fulcio *httptest.Server
	tsa    *httptest.Server
	rekor  *httptest.Server

	fulcioHits, tsaHits, rekorHits atomic.Int32
}

func startFakeSigstore(t *testing.T) *fakeSigstore {
	t.Helper()
	f := &fakeSigstore{}

	certPEM, _ := generateTestCert(t, 10*time.Minute)
	f.fulcio = httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		f.fulcioHits.Add(1)
		resp := map[string]any{
			"signedCertificateEmbeddedSct": map[string]any{
				"chain": map[string]any{"certificates": []string{string(certPEM)}},
			},
		}
		if err := json.NewEncoder(w).Encode(resp); err != nil {
			t.Errorf("encoding fulcio response: %v", err)
		}
	}))
	t.Cleanup(f.fulcio.Close)

	tsaKey, _, tsaCert := generateTestCertKey(t, time.Hour)
	f.tsa = httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		f.tsaHits.Add(1)
		body, err := io.ReadAll(r.Body)
		if err != nil {
			t.Errorf("reading tsa request: %v", err)
			return
		}
		req, err := timestamp.ParseRequest(body)
		if err != nil {
			t.Errorf("parsing tsa request: %v", err)
			return
		}
		ts := timestamp.Timestamp{
			HashAlgorithm:     req.HashAlgorithm,
			HashedMessage:     req.HashedMessage,
			Time:              time.Now(),
			Policy:            asn1.ObjectIdentifier{1, 2, 3, 4, 5},
			AddTSACertificate: true,
		}
		resp, err := ts.CreateResponseWithOpts(tsaCert, tsaKey, crypto.SHA256)
		if err != nil {
			t.Errorf("creating tsa response: %v", err)
			return
		}
		w.Header().Set("Content-Type", "application/timestamp-reply")
		if _, err := w.Write(resp); err != nil {
			t.Errorf("writing tsa response: %v", err)
		}
	}))
	t.Cleanup(f.tsa.Close)

	f.rekor = httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		f.rekorHits.Add(1)
		if r.URL.Path != "/api/v2/log/entries" {
			t.Errorf("unexpected rekor path: %s", r.URL.Path)
			http.NotFound(w, r)
			return
		}
		w.WriteHeader(http.StatusCreated)
		fmt.Fprint(w, `{"logIndex":"42"}`)
	}))
	t.Cleanup(f.rekor.Close)

	return f
}

func (f *fakeSigstore) signingConfig(t *testing.T) *root.SigningConfig {
	t.Helper()
	sc, err := root.NewSigningConfig(root.SigningConfigMediaType02,
		[]root.Service{{URL: f.fulcio.URL, MajorAPIVersion: 1}},
		nil,
		[]root.Service{{URL: f.rekor.URL, MajorAPIVersion: 2}},
		root.ServiceConfiguration{Selector: prototrustroot.ServiceSelector_ALL},
		[]root.Service{{URL: f.tsa.URL, MajorAPIVersion: 1}},
		root.ServiceConfiguration{Selector: prototrustroot.ServiceSelector_ALL},
	)
	if err != nil {
		t.Fatalf("building signing config: %v", err)
	}
	return sc
}

// newTestBundleSigner assembles a BundleSigner directly (like the other
// white-box tests) so trustedMaterial can stay nil: sign.Bundle then skips
// its post-sign self-verification, which would otherwise require the fakes
// to produce fully verifiable certs, timestamps, and inclusion proofs.
func newTestBundleSigner(t *testing.T, sc *root.SigningConfig, transport http.RoundTripper) *BundleSigner {
	t.Helper()
	keypair, err := sign.NewEphemeralKeypair(nil)
	if err != nil {
		t.Fatalf("generating keypair: %v", err)
	}
	return &BundleSigner{
		oidc:          &staticOIDCProvider{token: testIDToken()},
		signingConfig: sc,
		keypair:       keypair,
		transport:     transport,
	}
}

func testDSSEContent() *sign.DSSEData {
	return &sign.DSSEData{
		Data:        []byte(`{"hello":"world"}`),
		PayloadType: "application/vnd.in-toto+json",
	}
}

func TestSignContentWithTransport(t *testing.T) {
	fakes := startFakeSigstore(t)
	rt := &recordingTransport{}
	bs := newTestBundleSigner(t, fakes.signingConfig(t), rt)

	bundleBytes, err := bs.SignContent(context.Background(), testDSSEContent())
	if err != nil {
		t.Fatalf("SignContent: %v", err)
	}
	if len(bundleBytes) == 0 {
		t.Fatal("expected bundle bytes")
	}

	// The refresh path goes through Fulcio, the TSA, and Rekor v2 — all on
	// the injected transport.
	for name, url := range map[string]string{
		"fulcio": fakes.fulcio.URL,
		"tsa":    fakes.tsa.URL,
		"rekor":  fakes.rekor.URL,
	} {
		if got := rt.countWithPrefix(url); got != 1 {
			t.Errorf("expected 1 %s request through injected transport, got %d", name, got)
		}
	}

	// Steady state: the cached cert skips Fulcio, but the TSA and Rekor v2
	// requests still ride the injected transport.
	if _, err := bs.SignContent(context.Background(), testDSSEContent()); err != nil {
		t.Fatalf("SignContent (cached cert): %v", err)
	}
	if got := rt.countWithPrefix(fakes.fulcio.URL); got != 1 {
		t.Errorf("expected cached cert to skip Fulcio, got %d requests", got)
	}
	for name, url := range map[string]string{
		"tsa":   fakes.tsa.URL,
		"rekor": fakes.rekor.URL,
	} {
		if got := rt.countWithPrefix(url); got != 2 {
			t.Errorf("expected 2 %s requests through injected transport, got %d", name, got)
		}
	}

	// Nothing reached the fakes around the injected transport.
	if hits := fakes.fulcioHits.Load(); hits != 1 {
		t.Errorf("fulcio saw %d requests, want 1", hits)
	}
	if hits := fakes.tsaHits.Load(); hits != 2 {
		t.Errorf("tsa saw %d requests, want 2", hits)
	}
	if hits := fakes.rekorHits.Load(); hits != 2 {
		t.Errorf("rekor saw %d requests, want 2", hits)
	}
}

func TestSignContentDefaultTransport(t *testing.T) {
	fakes := startFakeSigstore(t)
	bs := newTestBundleSigner(t, fakes.signingConfig(t), nil)

	bundleBytes, err := bs.SignContent(context.Background(), testDSSEContent())
	if err != nil {
		t.Fatalf("SignContent: %v", err)
	}
	if len(bundleBytes) == 0 {
		t.Fatal("expected bundle bytes")
	}

	if hits := fakes.fulcioHits.Load(); hits != 1 {
		t.Errorf("fulcio saw %d requests, want 1", hits)
	}
	if hits := fakes.tsaHits.Load(); hits != 1 {
		t.Errorf("tsa saw %d requests, want 1", hits)
	}
	if hits := fakes.rekorHits.Load(); hits != 1 {
		t.Errorf("rekor saw %d requests, want 1", hits)
	}
}

// testTrustedMaterial is a non-nil TrustedMaterial so NewBundleSigner does
// not reach out to TUF during construction.
type testTrustedMaterial struct {
	root.BaseTrustedMaterial
}

func TestNewBundleSignerWithTransport(t *testing.T) {
	sc, err := root.NewSigningConfig(root.SigningConfigMediaType02,
		[]root.Service{{URL: "https://fulcio.example.com", MajorAPIVersion: 1}},
		nil, nil, root.ServiceConfiguration{}, nil, root.ServiceConfiguration{})
	if err != nil {
		t.Fatalf("building signing config: %v", err)
	}

	rt := &recordingTransport{}
	bs, err := NewBundleSigner(&staticOIDCProvider{token: testIDToken()},
		WithSigningConfig(sc), WithTrustedMaterial(&testTrustedMaterial{}), WithTransport(rt))
	if err != nil {
		t.Fatalf("NewBundleSigner: %v", err)
	}
	if bs.transport != rt {
		t.Error("expected WithTransport to set the signer's transport")
	}
}

func TestSignContentRekorV2RequiresTSA(t *testing.T) {
	// Rekor v2 does not timestamp entries, so requesting a fresh Fulcio cert
	// without a TSA in the signing config must fail before any network call.
	sc, err := root.NewSigningConfig(root.SigningConfigMediaType02,
		[]root.Service{{URL: "https://fulcio.example.com", MajorAPIVersion: 1}},
		nil,
		[]root.Service{{URL: "https://rekor.example.com", MajorAPIVersion: 2}},
		root.ServiceConfiguration{Selector: prototrustroot.ServiceSelector_ALL},
		nil, root.ServiceConfiguration{})
	if err != nil {
		t.Fatalf("building signing config: %v", err)
	}

	bs := newTestBundleSigner(t, sc, nil)
	if _, err := bs.SignContent(context.Background(), testDSSEContent()); err == nil ||
		!strings.Contains(err.Error(), "timestamp authority") {
		t.Fatalf("expected timestamp authority error, got: %v", err)
	}
}

// buildTestBundleJSONCertificate creates a v0.3 protobuf bundle JSON using
// VerificationMaterial.Certificate (the form cbundle.SignData emits).
func buildTestBundleJSONCertificate(t *testing.T, certDER []byte) []byte {
	t.Helper()

	bundle := &protobundle.Bundle{
		MediaType: "application/vnd.dev.sigstore.bundle.v0.3+json",
		VerificationMaterial: &protobundle.VerificationMaterial{
			Content: &protobundle.VerificationMaterial_Certificate{
				Certificate: &protocommon.X509Certificate{RawBytes: certDER},
			},
		},
	}

	data, err := protojson.Marshal(bundle)
	if err != nil {
		t.Fatalf("marshaling test bundle: %v", err)
	}
	return data
}

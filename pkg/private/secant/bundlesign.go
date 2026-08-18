package secant

import (
	"bytes"
	"context"
	"crypto/x509"
	"encoding/json"
	"encoding/pem"
	"errors"
	"fmt"
	"io"
	"net/http"
	"net/url"
	"path"
	"strings"
	"sync"
	"time"

	"github.com/chainguard-dev/terraform-provider-cosign/pkg/private/secant/fulcio"
	"github.com/chainguard-dev/terraform-provider-cosign/pkg/private/secant/types"
	"github.com/google/go-containerregistry/pkg/name"
	v1 "github.com/google/go-containerregistry/pkg/v1"
	"github.com/google/go-containerregistry/pkg/v1/remote"
	"github.com/google/go-containerregistry/pkg/v1/remote/transport"
	ggcrtypes "github.com/google/go-containerregistry/pkg/v1/types"
	intotov1 "github.com/in-toto/attestation/go/v1"
	"github.com/sigstore/cosign/v3/pkg/cosign"
	ociremote "github.com/sigstore/cosign/v3/pkg/oci/remote"
	ctypes "github.com/sigstore/cosign/v3/pkg/types"
	protobundle "github.com/sigstore/protobuf-specs/gen/pb-go/bundle/v1"
	protorekor "github.com/sigstore/protobuf-specs/gen/pb-go/rekor/v1"
	rekortilesclient "github.com/sigstore/rekor-tiles/v2/pkg/client"
	rekortilespb "github.com/sigstore/rekor-tiles/v2/pkg/generated/protobuf"
	"github.com/sigstore/sigstore-go/pkg/root"
	"github.com/sigstore/sigstore-go/pkg/sign"
	"github.com/sigstore/sigstore-go/pkg/util"
	"google.golang.org/protobuf/encoding/protojson"
	"google.golang.org/protobuf/types/known/structpb"
)

// BundleSigner holds the materials needed for the cosign v3 bundle signing path.
// The ephemeral keypair is generated once and reused across all operations.
// Fulcio certificates are cached and refreshed when nearing expiry.
type BundleSigner struct {
	oidc            fulcio.OIDCProvider
	signingConfig   *root.SigningConfig
	trustedMaterial root.TrustedMaterial
	keypair         sign.Keypair
	transport       http.RoundTripper

	mu      sync.Mutex
	certPEM []byte            // Cached PEM-encoded Fulcio certificate
	cert    *x509.Certificate // Parsed cert for expiry checking
}

// BundleSignerOption customizes a BundleSigner at construction.
type BundleSignerOption func(*bundleSignerConfig)

type bundleSignerConfig struct {
	signingConfig   *root.SigningConfig
	trustedMaterial root.TrustedMaterial
	transport       http.RoundTripper
}

// WithSigningConfig overrides the SigningConfig that would otherwise be loaded
// from the public TUF root. Useful when the desired Fulcio/Rekor topology is
// not yet reflected in TUF (e.g. piloting a Rekor v2 instance).
func WithSigningConfig(sc *root.SigningConfig) BundleSignerOption {
	return func(c *bundleSignerConfig) { c.signingConfig = sc }
}

// WithTrustedMaterial overrides the TrustedRoot that would otherwise be loaded
// from the public TUF root. Primarily a test seam.
func WithTrustedMaterial(tm root.TrustedMaterial) BundleSignerOption {
	return func(c *bundleSignerConfig) { c.trustedMaterial = tm }
}

// WithTransport sets the http.RoundTripper used for the Fulcio, timestamp
// authority, and Rekor v2 requests made while signing, so callers can inject
// instrumented transports (e.g. tracing/metrics). Rekor v1 log writes are not
// covered: sigstore-go constructs that client internally with no transport
// hook. When unset, the default transports are used.
func WithTransport(t http.RoundTripper) BundleSignerOption {
	return func(c *bundleSignerConfig) { c.transport = t }
}

// NewBundleSigner loads SigningConfig and TrustedMaterial from TUF (unless
// overridden via options) and generates an ephemeral keypair for signing.
func NewBundleSigner(oidc fulcio.OIDCProvider, opts ...BundleSignerOption) (*BundleSigner, error) {
	cfg := &bundleSignerConfig{}
	for _, opt := range opts {
		opt(cfg)
	}
	if cfg.signingConfig == nil {
		sc, err := cosign.SigningConfig()
		if err != nil {
			return nil, fmt.Errorf("loading signing config from TUF: %w", err)
		}
		cfg.signingConfig = sc
	}
	if cfg.trustedMaterial == nil {
		tr, err := cosign.TrustedRoot()
		if err != nil {
			return nil, fmt.Errorf("loading trusted root from TUF: %w", err)
		}
		cfg.trustedMaterial = tr
	}
	keypair, err := sign.NewEphemeralKeypair(nil)
	if err != nil {
		return nil, fmt.Errorf("generating ephemeral keypair: %w", err)
	}
	return &BundleSigner{
		oidc:            oidc,
		signingConfig:   cfg.signingConfig,
		trustedMaterial: cfg.trustedMaterial,
		keypair:         keypair,
		transport:       cfg.transport,
	}, nil
}

// signWithIDToken signs content using an OIDC token, which internally
// fetches a new Fulcio certificate. The cert is then extracted from the
// resulting bundle and cached for future calls.
// Must be called with bs.mu held.
func (bs *BundleSigner) signWithIDToken(ctx context.Context, content sign.Content) ([]byte, error) {
	idToken, err := bs.oidc.Provide(ctx, "sigstore")
	if err != nil {
		return nil, fmt.Errorf("retrieving ID token: %w", err)
	}

	bundleBytes, err := bs.signBundle(ctx, content, idToken, nil)
	if err != nil {
		return nil, fmt.Errorf("signing bundle: %w", err)
	}

	if err := bs.cacheCertFromBundle(bundleBytes); err != nil {
		return nil, fmt.Errorf("caching cert from bundle: %w", err)
	}

	return bundleBytes, nil
}

// signBundle assembles sign.BundleOptions and invokes sigstore-go's
// sign.Bundle directly instead of delegating to cosign's cbundle.SignData.
// SignData constructs its Rekor clients internally with no way to supply an
// HTTP transport (its SignOptions only cover Fulcio and the TSA), so building
// every client here is what lets bs.transport cover the whole signing flow.
// The construction mirrors SignData for the two modes secant uses: a fresh
// Fulcio cert via OIDC (idToken set) or a previously cached cert (certPEM
// set). Unlike SignData, the context is threaded through to the network
// calls, so cancellation is honored and traces parent correctly.
func (bs *BundleSigner) signBundle(ctx context.Context, content sign.Content, idToken string, certPEM []byte) ([]byte, error) {
	bundleOpts := sign.BundleOptions{
		Context:     ctx,
		TrustedRoot: bs.trustedMaterial,
	}

	switch {
	case idToken != "":
		provider, err := bs.fulcioProvider()
		if err != nil {
			return nil, err
		}
		bundleOpts.CertificateProvider = provider
		bundleOpts.CertificateProviderOptions = &sign.CertificateProviderOptions{IDToken: idToken}
	case certPEM != nil:
		bundleOpts.CertificateProvider = &localCertProvider{cert: certPEM}
	default:
		return nil, fmt.Errorf("either an OIDC token or a cached certificate is required")
	}

	tsas, err := bs.timestampAuthorities()
	if err != nil {
		return nil, err
	}
	bundleOpts.TimestampAuthorities = tsas

	tlogs, usingRekorV2, err := bs.transparencyLogs()
	if err != nil {
		return nil, err
	}
	bundleOpts.TransparencyLogs = tlogs

	// Rekor v2 does not timestamp entries, so a short-lived Fulcio cert can
	// only be verified if a timestamp authority also witnessed the signature.
	// Mirrors the equivalent check in cbundle.SignData.
	if usingRekorV2 && len(tsas) == 0 && idToken != "" {
		return nil, fmt.Errorf("a timestamp authority must be provided to request a short-lived certificate that will be logged to Rekor")
	}

	bundle, err := sign.Bundle(content, bs.keypair, bundleOpts)
	if err != nil {
		return nil, err
	}
	return protojson.Marshal(bundle)
}

// fulcioProvider selects the Fulcio service from the signing config and
// builds a certificate provider for it, mirroring cbundle.SignData's
// unexported (non-caching) provider but with bs.transport threaded through.
// Non-caching is correct here: BundleSigner does its own cert caching.
func (bs *BundleSigner) fulcioProvider() (sign.CertificateProvider, error) {
	urls := bs.signingConfig.FulcioCertificateAuthorityURLs()
	if len(urls) == 0 {
		return nil, fmt.Errorf("no fulcio URLs provided in signing config")
	}
	svc, err := root.SelectService(urls, sign.FulcioAPIVersions, time.Now())
	if err != nil {
		return nil, fmt.Errorf("selecting fulcio service: %w", err)
	}
	return sign.NewFulcio(&sign.FulcioOptions{
		BaseURL:   svc.URL,
		Timeout:   30 * time.Second,
		Retries:   1,
		Transport: bs.transport,
	}), nil
}

// timestampAuthorities builds a TSA client per service selected from the
// signing config, with bs.transport threaded through.
func (bs *BundleSigner) timestampAuthorities() ([]*sign.TimestampAuthority, error) {
	urls := bs.signingConfig.TimestampAuthorityURLs()
	if len(urls) == 0 {
		return nil, nil
	}
	svcs, err := root.SelectServices(urls, bs.signingConfig.TimestampAuthorityURLsConfig(),
		sign.TimestampAuthorityAPIVersions, time.Now())
	if err != nil {
		return nil, fmt.Errorf("selecting timestamp authority services: %w", err)
	}
	tsas := make([]*sign.TimestampAuthority, 0, len(svcs))
	for _, svc := range svcs {
		tsas = append(tsas, sign.NewTimestampAuthority(&sign.TimestampAuthorityOptions{
			URL:       svc.URL,
			Timeout:   30 * time.Second,
			Retries:   1,
			Transport: bs.transport,
		}))
	}
	return tsas, nil
}

// transparencyLogs builds a Rekor client per service selected from the
// signing config, and reports whether any of them is a Rekor v2 log.
func (bs *BundleSigner) transparencyLogs() ([]sign.Transparency, bool, error) {
	urls := bs.signingConfig.RekorLogURLs()
	if len(urls) == 0 {
		return nil, false, nil
	}
	svcs, err := root.SelectServices(urls, bs.signingConfig.RekorLogURLsConfig(),
		sign.RekorAPIVersions, time.Now())
	if err != nil {
		return nil, false, fmt.Errorf("selecting rekor services: %w", err)
	}
	var usingRekorV2 bool
	tlogs := make([]sign.Transparency, 0, len(svcs))
	for _, svc := range svcs {
		rekorOpts := &sign.RekorOptions{
			BaseURL: svc.URL,
			Timeout: 90 * time.Second,
			Retries: 1,
			Version: svc.MajorAPIVersion,
		}
		if svc.MajorAPIVersion == 2 {
			usingRekorV2 = true
			// Only replace the default client when instrumenting; otherwise
			// sigstore-go constructs the stock rekor-tiles writer itself.
			if bs.transport != nil {
				w, err := newRekorV2Writer(svc.URL, bs.transport)
				if err != nil {
					return nil, false, err
				}
				rekorOpts.ClientV2 = w
			}
		}
		tlogs = append(tlogs, sign.NewRekor(rekorOpts))
	}
	return tlogs, usingRekorV2, nil
}

// localCertProvider returns a previously fetched Fulcio certificate, mirroring
// cbundle.SignData's unexported equivalent so the cached-cert path skips Fulcio.
type localCertProvider struct {
	cert []byte
}

func (c *localCertProvider) GetCertificate(context.Context, sign.Keypair, *sign.CertificateProviderOptions) ([]byte, error) {
	block, _ := pem.Decode(c.cert)
	if block == nil {
		return nil, fmt.Errorf("could not decode cert")
	}
	return block.Bytes, nil
}

const (
	// rekorV2AddPath and rekorV2MaxResponseSize mirror rekor-tiles' write client.
	rekorV2AddPath         = "/api/v2/log/entries"
	rekorV2MaxResponseSize = 10 * 1024 * 1024 // 10MB
)

// rekorV2Writer is a minimal Rekor v2 write client mirroring rekor-tiles'
// write.Client, which cannot be used directly because its constructor accepts
// no HTTP transport (only user agent, timeout, and TLS config knobs). It is
// wire-compatible with the stock client: same endpoint, request encoding,
// user agent, and timeout.
type rekorV2Writer struct {
	baseURL *url.URL
	client  *http.Client
}

func newRekorV2Writer(baseURL string, t http.RoundTripper) (*rekorV2Writer, error) {
	u, err := url.Parse(baseURL)
	if err != nil {
		return nil, fmt.Errorf("parsing rekor URL %q: %w", baseURL, err)
	}
	return &rekorV2Writer{
		baseURL: u,
		client: &http.Client{
			Transport: rekortilesclient.CreateRoundTripper(t, util.ConstructUserAgent()),
			Timeout:   30 * time.Second,
		},
	}, nil
}

// Add implements sign.RekorV2Client.
func (w *rekorV2Writer) Add(ctx context.Context, entry any) (*protorekor.TransparencyLogEntry, error) {
	hr, ok := entry.(*rekortilespb.HashedRekordRequestV002)
	if !ok {
		return nil, fmt.Errorf("unsupported entry type: %T", entry)
	}
	payload, err := protojson.Marshal(&rekortilespb.CreateEntryRequest{
		Spec: &rekortilespb.CreateEntryRequest_HashedRekordRequestV002{HashedRekordRequestV002: hr},
	})
	if err != nil {
		return nil, fmt.Errorf("marshaling rekor entry: %w", err)
	}

	endpoint := *w.baseURL
	endpoint.Path = path.Join(endpoint.Path, rekorV2AddPath)
	req, err := http.NewRequestWithContext(ctx, http.MethodPost, endpoint.String(), bytes.NewReader(payload))
	if err != nil {
		return nil, fmt.Errorf("creating request: %w", err)
	}
	req.Header.Set("Content-Type", "application/json")

	resp, err := w.client.Do(req)
	if err != nil {
		return nil, fmt.Errorf("adding rekor entry: %w", err)
	}
	defer resp.Body.Close()
	body, err := io.ReadAll(io.LimitReader(resp.Body, rekorV2MaxResponseSize))
	if err != nil {
		return nil, fmt.Errorf("reading response: %w", err)
	}
	if resp.StatusCode != http.StatusCreated {
		return nil, fmt.Errorf("unexpected response: %v %v", resp.StatusCode, string(body))
	}
	tle := &protorekor.TransparencyLogEntry{}
	if err := protojson.Unmarshal(body, tle); err != nil {
		return nil, fmt.Errorf("unmarshaling response body: %w", err)
	}
	return tle, nil
}

// cacheCertFromBundle extracts the signing certificate from a serialized
// protobuf bundle and caches it for reuse on subsequent sign operations.
func (bs *BundleSigner) cacheCertFromBundle(bundleBytes []byte) error {
	var bundle protobundle.Bundle
	if err := protojson.Unmarshal(bundleBytes, &bundle); err != nil {
		return fmt.Errorf("unmarshaling bundle: %w", err)
	}

	cert := bundle.GetVerificationMaterial().GetCertificate()
	if cert == nil {
		return fmt.Errorf("bundle contains no certificate")
	}
	derBytes := cert.GetRawBytes()

	parsed, err := x509.ParseCertificate(derBytes)
	if err != nil {
		return fmt.Errorf("parsing certificate from bundle: %w", err)
	}

	bs.certPEM = pem.EncodeToMemory(&pem.Block{
		Type:  "CERTIFICATE",
		Bytes: derBytes,
	})
	bs.cert = parsed
	return nil
}

// certNeedsRefresh reports whether the cached cert is missing or nearing
// expiry (within 30 seconds, matching the legacy fulcio path).
func (bs *BundleSigner) certNeedsRefresh() bool {
	return bs.cert == nil || time.Now().Add(30*time.Second).After(bs.cert.NotAfter)
}

// SignContent creates a protobuf bundle by signing the given content.
// On first call (or when the cached cert is nearing expiry), signs with an
// OIDC token, which fetches a new Fulcio cert internally. The cert is
// extracted from the bundle and cached so that subsequent calls pass it
// directly, skipping Fulcio entirely.
func (bs *BundleSigner) SignContent(ctx context.Context, content sign.Content) ([]byte, error) {
	// Lock scope is deliberately split: we hold the mutex across a cert
	// refresh so concurrent callers coalesce onto a single Fulcio fetch,
	// but release it before the steady-state sign so cached-cert signs
	// run in parallel.
	bs.mu.Lock()

	if bs.certNeedsRefresh() {
		// Refresh path: keep the lock held through signWithIDToken so
		// other goroutines observing certNeedsRefresh() block here
		// instead of each issuing their own OIDC + Fulcio round-trip.
		bundleBytes, err := bs.signWithIDToken(ctx, content)
		bs.mu.Unlock()
		return bundleBytes, err
	}

	// Snapshot the cached PEM under the lock so a concurrent refresh
	// can't swap bs.certPEM out from under us mid-sign.
	certPEM := bs.certPEM
	bs.mu.Unlock()

	// Steady state: sign with the cached cert, skipping Fulcio. Safe to
	// run unlocked because certPEM is a local copy and the keypair /
	// signingConfig / trustedMaterial fields are immutable after init.
	bundle, err := bs.signBundle(ctx, content, "", certPEM)
	if err != nil {
		return nil, fmt.Errorf("signing bundle: %w", err)
	}
	return bundle, nil
}

// SignBundle signs container images using the cosign v3 bundle format
// and writes them as OCI referrers. conflict matches the semantics of Sign:
// APPEND (or empty) always writes, SKIPSAME skips when an existing referrer
// has an identical payload, REPLACE deletes existing referrers with matching
// predicate type before writing.
func SignBundle(ctx context.Context, conflict string, annotations map[string]any, signer *BundleSigner, imgs []name.Digest, ropt []remote.Option) error {
	opts := []ociremote.Option{ociremote.WithRemoteOptions(ropt...)}

	for _, digest := range imgs {
		digestParts := strings.Split(digest.DigestStr(), ":")
		if len(digestParts) != 2 {
			return fmt.Errorf("unable to parse digest %s", digest.DigestStr())
		}

		annoStruct, err := structpb.NewStruct(annotations)
		if err != nil {
			return fmt.Errorf("converting annotations to protobuf struct: %w", err)
		}
		subject := intotov1.ResourceDescriptor{
			Digest:      map[string]string{digestParts[0]: digestParts[1]},
			Annotations: annoStruct,
		}

		statement := &intotov1.Statement{
			Type:          intotov1.StatementTypeUri,
			Subject:       []*intotov1.ResourceDescriptor{&subject},
			PredicateType: ctypes.CosignSignPredicateType,
			Predicate:     &structpb.Struct{},
		}

		payload, err := protojson.Marshal(statement)
		if err != nil {
			return fmt.Errorf("marshaling statement: %w", err)
		}

		shouldWrite, err := resolveBundleConflict(digest, ctypes.CosignSignPredicateType, payload, conflict, ropt, opts)
		if err != nil {
			return fmt.Errorf("resolving conflict for %q: %w", digest.String(), err)
		}
		if !shouldWrite {
			continue
		}

		content := &sign.DSSEData{
			Data:        payload,
			PayloadType: ctypes.IntotoPayloadType,
		}

		bundleBytes, err := signer.SignContent(ctx, content)
		if err != nil {
			return fmt.Errorf("signing bundle for %q: %w", digest.String(), err)
		}

		if err := writeBundleReferrer(digest, bundleBytes, ctypes.CosignSignPredicateType, nil, ropt); err != nil {
			return fmt.Errorf("writing sign bundle for %q: %w", digest.String(), err)
		}
	}

	return nil
}

// AttestBundle creates attestations using the cosign v3 bundle format
// and writes them as OCI referrers. See SignBundle for conflict semantics.
// Statements may carry a verbatim subject descriptor (Statement.SubjectDescriptor)
// for subjects that are absent from the target repository.
func AttestBundle(ctx context.Context, conflict string, statements []*types.Statement, signer *BundleSigner, ropt []remote.Option) error {
	if len(statements) == 0 {
		return nil
	}

	ociOpts := []ociremote.Option{ociremote.WithRemoteOptions(ropt...)}

	for _, stmt := range statements {
		predicateType, err := parsePredicateType(stmt.Type)
		if err != nil {
			return err
		}

		shouldWrite, err := resolveBundleConflict(stmt.Digest, predicateType, stmt.Payload, conflict, ropt, ociOpts)
		if err != nil {
			return fmt.Errorf("resolving conflict for %q: %w", stmt.Digest.String(), err)
		}
		if !shouldWrite {
			continue
		}

		content := &sign.DSSEData{
			Data:        stmt.Payload,
			PayloadType: ctypes.IntotoPayloadType,
		}

		bundleBytes, err := signer.SignContent(ctx, content)
		if err != nil {
			return fmt.Errorf("signing attestation bundle for %q: %w", stmt.Digest.String(), err)
		}

		if err := writeBundleReferrer(stmt.Digest, bundleBytes, predicateType, stmt.SubjectDescriptor, ropt); err != nil {
			return fmt.Errorf("writing attestation bundle for %q: %w", stmt.Digest.String(), err)
		}
	}

	return nil
}

// resolveBundleConflict applies the conflict policy to a pending bundle write.
// It returns whether the caller should proceed with the write, after deleting
// the existing referrers the write supersedes. REPLACE deletes every matching
// referrer; SKIPSAME keeps one whose payload is byte-identical to the pending
// write (skipping the write) and deletes the rest. Both modes converge on a
// single bundle per predicate type, so accumulation cannot outlive the next
// write even on repositories whose retention never reaps referrer manifests.
func resolveBundleConflict(digest name.Digest, predicateType string, newPayload []byte, conflict string, ropt []remote.Option, opts []ociremote.Option) (bool, error) {
	switch conflict {
	case "", Append:
		return true, nil
	case SkipSame, Replace:
	default:
		return false, fmt.Errorf("unknown conflict mode: %q", conflict)
	}

	matching, err := matchingBundleReferrers(digest, predicateType, opts, ropt)
	if err != nil {
		return false, err
	}

	var keep *v1.Hash
	if conflict == SkipSame {
		for _, m := range matching {
			payload, err := referrerDSSEPayload(digest.Repository, m.Digest, ropt)
			if err != nil {
				// A stale referrers-index entry (e.g. Artifact Registry's index
				// lagging a bulk deletion) describes a manifest that no longer
				// exists; it cannot match the new payload.
				if isReferrerNotFound(err) {
					continue
				}
				return false, fmt.Errorf("reading referrer %s: %w", m.Digest, err)
			}
			if bytes.Equal(payload, newPayload) {
				d := m.Digest
				keep = &d
				break
			}
		}
	}

	deleted := make([]v1.Hash, 0, len(matching))
	for _, m := range matching {
		if keep != nil && m.Digest == *keep {
			continue
		}
		ref := digest.Digest(m.Digest.String())
		if err := remote.Delete(ref, ropt...); err != nil && !isReferrerNotFound(err) {
			return false, fmt.Errorf("deleting referrer %s: %w", m.Digest, err)
		}
		// A NOT_FOUND delete means a stale referrers-index entry whose manifest
		// is already gone — the outcome the conflict policy wants. Record it as
		// deleted so pruneFallbackReferrers also drops it from a fallback-tag
		// index.
		deleted = append(deleted, m.Digest)
	}

	// On a registry without the native Referrers API, go-containerregistry
	// tracks referrers in a client-maintained sha256-<subject> fallback-tag
	// index. remote.Delete removes the referrer manifest but does NOT prune the
	// descriptor from that index (a documented gap in go-containerregistry's
	// Pusher.Delete). The next writeBundleReferrer would then read the stale
	// index, append the new referrer, and re-PUT an index still referencing the
	// just-deleted manifest, which a registry that validates index members
	// rejects with MANIFEST_UNKNOWN. Prune the deleted descriptors now so the
	// subsequent write commits a consistent index.
	if err := pruneFallbackReferrers(digest, deleted, ropt); err != nil {
		return false, fmt.Errorf("pruning fallback referrers for %q: %w", digest.String(), err)
	}
	return keep == nil, nil
}

// pruneFallbackReferrers removes the given descriptors from the sha256-<subject>
// fallback-tag index, if one exists. It is a no-op on registries that implement
// the native Referrers API (they compute referrers dynamically and maintain no
// fallback tag, so the GET below 404s). The fallback tag layout mirrors
// go-containerregistry's unexported fallbackTag: the subject digest with its
// ":" replaced by "-", as a tag on the subject's repository.
func pruneFallbackReferrers(subject name.Digest, deleted []v1.Hash, ropt []remote.Option) error {
	if len(deleted) == 0 {
		return nil
	}

	tag := subject.Context().Tag(strings.Replace(subject.DigestStr(), ":", "-", 1))
	desc, err := remote.Get(tag, ropt...)
	if err != nil {
		if isReferrerNotFound(err) {
			// No fallback index: native Referrers API, or nothing left to prune.
			return nil
		}
		return fmt.Errorf("fetching fallback index %q: %w", tag.String(), err)
	}

	var im v1.IndexManifest
	if err := json.Unmarshal(desc.Manifest, &im); err != nil {
		return fmt.Errorf("parsing fallback index %q: %w", tag.String(), err)
	}

	drop := make(map[v1.Hash]struct{}, len(deleted))
	for _, h := range deleted {
		drop[h] = struct{}{}
	}
	kept := im.Manifests[:0]
	changed := false
	for _, m := range im.Manifests {
		if _, ok := drop[m.Digest]; ok {
			changed = true
			continue
		}
		kept = append(kept, m)
	}
	if !changed {
		return nil
	}
	im.Manifests = kept

	if err := remote.Put(tag, &fallbackIndex{im: im}, ropt...); err != nil {
		return fmt.Errorf("rewriting fallback index %q: %w", tag.String(), err)
	}
	return nil
}

// fallbackIndex serializes a pruned fallback-tag index for a manifest PUT,
// mirroring go-containerregistry's unexported fallbackTaggable.
type fallbackIndex struct {
	im v1.IndexManifest
}

func (f *fallbackIndex) RawManifest() ([]byte, error)            { return json.Marshal(f.im) }
func (f *fallbackIndex) MediaType() (ggcrtypes.MediaType, error) { return ggcrtypes.OCIImageIndex, nil }

func isReferrerNotFound(err error) bool {
	var terr *transport.Error
	return errors.As(err, &terr) && terr.StatusCode == http.StatusNotFound
}

// bundleMediaTypePrefix matches sigstore bundle media types across all
// versions (v0.1 / v0.2 / v0.3 / future v0.4+). Sigstore-go's MediaTypeString
// is version-specific; prefix-matching here mirrors how cosign itself
// filters bundle referrers in pkg/oci/remote/signatures.go.
const bundleMediaTypePrefix = "application/vnd.dev.sigstore.bundle"

// matchingBundleReferrers returns referrer descriptors for digest that are
// sigstore bundles carrying predicateType. It trusts the referrers-index
// descriptor when the registry populated both artifactType and the
// predicateType annotation, and otherwise consults the referrer manifest, which
// is authoritative on every registry. This keeps REPLACE/SKIPSAME correct on
// registries that omit those fields from the referrers index — notably
// go-containerregistry's tag-schema fallback, whose index descriptors carry an
// artifactType but no annotations.
func matchingBundleReferrers(digest name.Digest, predicateType string, opts []ociremote.Option, ropt []remote.Option) ([]v1.Descriptor, error) {
	idx, err := ociremote.Referrers(digest, "", opts...)
	if err != nil {
		return nil, fmt.Errorf("listing referrers: %w", err)
	}

	var matching []v1.Descriptor
	for _, m := range idx.Manifests {
		ok, err := bundleReferrerMatches(digest.Repository, m, predicateType, ropt)
		if err != nil {
			return nil, err
		}
		if ok {
			matching = append(matching, m)
		}
	}
	return matching, nil
}

// bundleReferrerMatches reports whether the referrer described by m is a
// sigstore bundle carrying predicateType.
func bundleReferrerMatches(repo name.Repository, m v1.Descriptor, predicateType string, ropt []remote.Option) (bool, error) {
	// Fast path: the index descriptor already carries what we need (zot, GAR, …),
	// so no per-referrer manifest fetch is required.
	if strings.HasPrefix(m.ArtifactType, bundleMediaTypePrefix) {
		if pt, ok := m.Annotations[ociremote.BundlePredicateType]; ok {
			return pt == predicateType, nil
		}
	}

	// Slow path: the registry dropped artifactType and/or annotations from the
	// index, or reported the config descriptor's media type as the artifactType
	// (the OCI referrers spec permits this, and cosign bundles use the empty-config
	// media type, so a real bundle can surface here with a non-bundle
	// artifactType). The referrer manifest is authoritative.
	at, ann, err := referrerManifestInfo(repo, m.Digest, ropt)
	if err != nil {
		if isReferrerNotFound(err) {
			// Dangling fallback-index entry for an already-deleted referrer.
			return false, nil
		}
		return false, err
	}
	return strings.HasPrefix(at, bundleMediaTypePrefix) &&
		ann[ociremote.BundlePredicateType] == predicateType, nil
}

// referrerManifestInfo fetches a referrer manifest and returns its top-level
// artifactType and annotations.
func referrerManifestInfo(repo name.Repository, descDigest v1.Hash, ropt []remote.Option) (string, map[string]string, error) {
	d, err := remote.Get(repo.Digest(descDigest.String()), ropt...)
	if err != nil {
		return "", nil, err
	}
	var mf struct {
		ArtifactType string            `json:"artifactType"`
		Annotations  map[string]string `json:"annotations"`
	}
	if err := json.Unmarshal(d.Manifest, &mf); err != nil {
		return "", nil, fmt.Errorf("parsing referrer manifest %s: %w", descDigest, err)
	}
	return mf.ArtifactType, mf.Annotations, nil
}

// referrerDSSEPayload fetches the given referrer manifest, reads its first
// layer (the protobuf bundle), and returns the bytes of the wrapped DSSE
// envelope payload.
func referrerDSSEPayload(repo name.Repository, descDigest v1.Hash, ropt []remote.Option) ([]byte, error) {
	ref := repo.Digest(descDigest.String())
	img, err := remote.Image(ref, ropt...)
	if err != nil {
		return nil, fmt.Errorf("fetching referrer image: %w", err)
	}
	layers, err := img.Layers()
	if err != nil {
		return nil, fmt.Errorf("getting layers: %w", err)
	}
	if len(layers) == 0 {
		return nil, fmt.Errorf("referrer has no layers")
	}
	rc, err := layers[0].Uncompressed()
	if err != nil {
		return nil, fmt.Errorf("opening layer: %w", err)
	}
	defer rc.Close()

	bundleBytes, err := io.ReadAll(rc)
	if err != nil {
		return nil, fmt.Errorf("reading bundle bytes: %w", err)
	}

	var bundle protobundle.Bundle
	if err := protojson.Unmarshal(bundleBytes, &bundle); err != nil {
		return nil, fmt.Errorf("unmarshaling bundle: %w", err)
	}
	env := bundle.GetDsseEnvelope()
	if env == nil {
		return nil, fmt.Errorf("bundle has no DSSE envelope")
	}
	return env.Payload, nil
}

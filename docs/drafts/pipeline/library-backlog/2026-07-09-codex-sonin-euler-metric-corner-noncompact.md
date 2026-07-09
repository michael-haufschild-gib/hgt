# Library ticket: actual Sonin Euler-metric corner noncompactness

- **Target docs:** `docs/drafts/door/00-index.md`; `docs/drafts/door/00-status.md`;
  `docs/drafts/door/bucket-the-seam-archimedean-obstruction.md`;
  `docs/drafts/rh-monodromy-weight-mismatch/129-pinned-carrier-geometry-candidates.md`;
  `docs/drafts/rh-monodromy-weight-mismatch/130-sonin-seam-defect-commutator-nogo.md`;
  `docs/drafts/rh-monodromy-weight-mismatch/131-cross-boundary-cochain.md`
- **Source card:** `docs/drafts/pipeline/2-fully-proven/new/sonin-euler-metric-corner-noncompact.md`
- **Active successor:** `docs/drafts/pipeline/1-in-progress/sonin-cutoff-transversality-realization.md`

## Update needed

Record the source-specific theorem beyond the earlier raw-support no-go.

1. Proposition 4.8 of Connes--Consani--Moscovici realizes every semilocal Sonin space on one
   entire-function set `B_lambda` with place-dependent norms. Relative to the pinned archimedean norm,
   adjoining `p` multiplies the critical-line measure by
   `w_p(s)=|1-p^(-1/2-is)|^2`.
2. Let `Q_lambda` be the orthogonal projection onto the actual archimedean Sonin intersection
   `ker(time cutoff) intersect ker(Fourier cutoff)`. For every `lambda>0` and prime `p`,
   `(1-Q_lambda)(U_p+U_p^*)Q_lambda` is noncompact.
3. The proof is not the raw shell calculation. The time-band prolate block has norm `<1`, which gives
   a bounded projection correction from exterior high-frequency shell modes to exact Sonin vectors.
   One dilation then moves the shell inside the physical cutoff with asymptotically unit norm.
4. Under the dual Hardy--Titchmarsh unitary, the theorem becomes noncompactness of
   `(1-P_lambda)M_{w_p}P_lambda` on the common entire-function carrier. Hence the positive Euler metric
   corner is in no Schatten ideal and has no unsmoothed trace/determinant/Fitting boundary.
5. Scope the result to the pinned archimedean metric and forward weight `w_p`. It does not yet decide
   every `S`-dependent orthogonal projection, the inverse weight, a two-prime product of corners, or the
   formal prolate naturality defect.

## Suggested grade

THEOREM (paper), NEW GATEKEEPER (source-specific route closure), not C5. The generic time-band and
compression ingredients are classical; the new content is that the full physical-and-Fourier Sonin
constraint does not regularize the prime Euler metric crossing. The trace-ideal metric shortcut is closed.

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
   entire-function set `B_lambda` with place-dependent norms. On the archimedean-weighted critical
   line, let `Pi^B_{lambda,infinity}` be the orthogonal projection onto the boundary image in the
   pinned archimedean norm. Adjoining `p` changes the metric by
   `w_p(s)=|1-p^(-1/2-is)|^2`.
   Precisely, `w_p` is the Radon--Nikodym/Gram operator `(iota'_p)^*iota'_p`; the finite Euler factor
   cancels in `upsilon_{infinity,p} theta_p = iota'_p upsilon_infinity`, so it is not a residual
   multiplier in that identity.
2. Let `Q_lambda` be the orthogonal projection onto the actual archimedean Sonin intersection
   `ker(time cutoff) intersect ker(Fourier cutoff)`. For every `lambda>0` and prime `p`,
   `(1-Q_lambda)(U_p+U_p^*)Q_lambda` is noncompact.
3. The proof is not the raw shell calculation. The time-band prolate block has norm `<1`, which gives
   a bounded projection correction from exterior high-frequency shell modes to exact Sonin vectors.
   One dilation then moves the shell inside the physical cutoff with asymptotically unit norm.
4. Under the dual Hardy--Titchmarsh unitary, the theorem becomes noncompactness of
   `(1-Pi^B_{lambda,infinity})M_{w_p}Pi^B_{lambda,infinity}` on the boundary image in the
   archimedean-weighted critical-line space. Hence the positive Euler metric corner is in no finite
   Schatten class and has no unsmoothed trace/determinant/Fitting boundary.
5. Scope the result to the pinned archimedean metric and forward weight `w_p`. It does not yet decide
   every `S`-dependent orthogonal projection, the inverse weight, a two-prime product of corners, or the
   formal prolate naturality defect.

The formal endpoint is
`formal/GaloisForLFunctions/RHTower/HardyTitchmarshEulerConcrete.lean`, recorded by
`docs/drafts/pipeline/3-formalized/new/even-sonin-euler-corner-noncompact.md`. Lean constructs the
source unitary, the pointwise local factor and `M_{w_p}`, the source-image projection, the exact
pullback, and the noncompactness theorem.

## Suggested grade

THEOREM (paper), NEW GATEKEEPER (source-specific route closure), not C5. The generic time-band and
compression ingredients are classical; the new content is that the full physical-and-Fourier Sonin
constraint does not regularize the prime Euler metric crossing. The trace-ideal metric shortcut is closed.

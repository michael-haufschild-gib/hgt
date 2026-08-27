# RBH separated-sign finite-rate cone (2026-08-27)

Formal module: `formal/GaloisForLFunctions/RHTower/ReflectedBiHeatSeparatedSignFiniteRateCone.lean`.

For arbitrary finite nonempty low/high blocks with positive magnitudes and
`lambda_i < kappa ≤ mu_j`, define
`F(t)=-Σ p_i sinh(lambda_i t)+Σ q_j sinh(mu_j t)` and
`D=Σ q_j mu_j-Σ p_i lambda_i`.

Exact theorem: `∀t, F(t)=0 ↔ t=0` iff `0≤D`.
Proof uses strict monotonicity of `sinh u/u` for positivity when `D≥0`.
If `D<0`, divided-wall limit gives a negative value near zero and one
high-rate atom dominates the entire finite low block at infinity, yielding
an additional positive root by IVT.

This closes arbitrary-cardinality incommensurate packets with one rate-order
sign change. Physical arbitrary-real-power aperture factorization and exact
RH equivalence are formalized.

Verification: direct Lean, targeted build, axiom audit passed.
Axioms only `propext`, `Classical.choice`, `Quot.sound`.

Remaining: ≥2 sign changes, rate collisions, source-derived coefficient law,
infinite packets, non-diagonal collision channels.

Card: `docs/drafts/pipeline/3-formalized/reflected-bi-heat-separated-sign-finite-rate-cone.md`.
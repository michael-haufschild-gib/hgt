# Sharp mass cost of a reflected pair

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacles:** B13, B112; positive annihilation of one simple reflected pair.
- **Statement:** For a normalized positive Dirichlet polynomial supported at nonconstant logarithmic frequencies in `[a,B]`, simultaneous zeros at `σ±δ+iγ`, `δ>0`, force the central tail mass to satisfy
  `H(σ) ≥ sinh(δ(B+a)/2)/sinh(δ(B-a)/2)`.
- **Sharpness conjecture:** Positive trinomials supported at frequencies `a` and `B`, with opposite phases, attain the bound when `a=log 2` and `B` is a positive even multiple of `a`.
- **Mechanism to audit:** Combine the two zero identities using the normalized function `sinh(δ((B+a)/2-L))`. Its absolute value is at most `sinh(δ(B-a)/2)` on the support.
- **Expected boundary:** As `δ→0`, the cost approaches `(B+a)/(B-a)`; as `B→∞`, it approaches `exp(δa)`. Neither bound excludes a pair without an independent arithmetic restriction.
- **Corpus audit:** Existing `TheUnitMassBoundaryOfPositiveAnnihilators` handles coalesced double zeros. `TheWeightedSpectrumOfAReflectedPair` concerns a different `L²` quadratic form, not annihilator mass. No paired annihilator bound found.
- **Extremizer to prove:** With `u=δa`, `v=δB`, use coefficients `A=sinh(v)/sinh(v-u)` and `C=sinh(u)/sinh(v-u)` in `1+A X+C X^(B/a)`, where `X=2^(σ-s)` and `B/a` is even. Both coefficients are positive; the two zeros share height `π/log 2`.
- **Next gate:** Lean proof of the lower bound and exact positive extremizers. Uncounted until audited.

# Signed prime-source transfer through complete logarithmic cells

- **ID:** acs-log-cell-source-transfer
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Route ACS; `BiarithmeticGaugeGeometry/EuclideanCellRemainderAndPolarNeutralCollapse.lean`.
- **Statement:** Identify actual mixed correlations of logarithmic cell sections with the complete divisibility-plus-successor sum, and prove a vanishing signed prime-weighted successor error under refinement at high integer scales.

## Goal

Discharge the continuum/source identification and remainder payment in the arithmetic cell model. The target includes actual Bochner correlations and all prime lags meeting the support, not only a formal finite sum. It does not assume positivity, an index budget, or zero exclusion. Full Gamma/pole-compatible positivity remains a separate open ACS input.

## Gates

- [x] Source-pure statement and mechanism identified.
- [ ] Mixed high-cell remainder estimate formalized.
- [ ] Actual cell-integral identity formalized.
- [ ] Complete prime-weighted transfer and refinement consequence formalized.
- [ ] Exact-file Lean checks, transitive axiom audits, umbrella imports.

## Mechanism under formalization

Let `w_a = log(a+1)-log a`. For two signed coefficient families `c,d`, define the mixed remainder

`R = Σ_{A≤a≤X} c_a Σ_{0≤r<m} w_(am+r) (d_(am+r)-d_(am))`.

The existing proof bounds the squared inner remainder divided by `w_a` by a derivative block after replacing `w_a/a` by `1`. Retain that factor: `w_a/a ≤ A⁻²`. Distinct quotient-remainder blocks are disjoint. Weighted Cauchy–Schwarz then gives

`R² ≤ A⁻² (Σ_{A≤a≤X} w_a c_a²) (Σ_{k≤Xm+m} k(d_(k+1)-d_k)²)`.

If `d` vanishes above `X`, the derivative energy stops at `X`, uniformly in `m`. Multiplying by the actual nonnegative von Mangoldt weights pays the entire signed prime remainder. Multiplication by `m` subdivides each integer logarithmic cell exactly; the remaining analytic task is to identify those finite sums with actual integrals and make the refinement consequence explicit.

## Status

No proof claimed. No stage-2 card will be created; completed results go directly to stage 3 after Lean verification.

# Odd-base quadrature for the actual standard taper

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** Argon §4.1.
- **Parent:** [Global model transport](../1-in-progress/odd-stabilizer-finite-aperture-transport.md).
- **Lean:** `TransThresholdPairCorrelation/OddStabilizerSpatialQuadrature.lean`.

## Statements

Fix a smooth height profile Ω_T and an admissible standard taper
`g=autocorr(φ²)`, of length L≥1. For T≥1 and 0<c≤2T, put
`N=ceil(T/c)` and `F(x)=g(log x)Ω_T(cx)`.

`|Σ_{r<N} F(2r+3) − (1/2)∫_1^{1+2N} F(x)dx| ≤ 4T/c + C L`.

The constant depends only on the fixed height profile
(`WindowProfile.exists_oddSpatialQuadratureError_le`).
The error equals the actual finite odd-base error with
`M=(floor(exp L)−1)/2`, sum `r<M`, and integral from 1 to exp L
(`WindowProfile.oddSpatialQuadratureError_eq_taper_cutoff`).

For `A(q)=μ²(q)/φ(q)²`, the sum of these absolute errors over odd q≤Q,
weighted by A(q), and positive coprime frequencies
`c=πn/q`, `n≤floor(2qT/π)`, is at most

`K T (1+L+log((Q+1)T)) (1+log Q)`

(`WindowProfile.exists_sum_oddSpatialQuadratureError_le`).

## Proof

The taper has Lipschitz constant two and absolute bound L. The height profile
is bounded by one and has Lipschitz constant B/T. Thus F on `[1,∞)` has
Lipschitz constant `2+LBc/T`. Right-endpoint quadrature at mesh two gives
error at most `2N(2+LBc/T)`. Using `N≤T/c+1` and `c≤2T` gives
`4T/c+(4+6B)L`.

The taper vanishes at x≥exp L and the height factor at cx≥2T. Extending
both finite sums to a common cutoff adds zero terms. Integrals between either
pair of endpoints also vanish, proving the exact cutoff identity.

For a fixed q, dropping the coprimality filter bounds the frequency error by
`qT[4(1+log((Q+1)T))+CL]`: the reciprocal-frequency sum is harmonic and
the frequency count is at most qT. The existing totient-ratio estimate gives
`Σ_{q≤Q}qA(q)≤64(1+log Q)`, completing the conductor sum.

## Scope

Weighted coprime-harmonic transport, global aperture/boundary summation and
signed spatial/diagonal assembly remain open. No actual prime-discrepancy
bound or improved zero proportion follows from these estimates alone.

All three transitive axiom audits use only `propext`, `Classical.choice` and
`Quot.sound`; the final direct leaf check passes.

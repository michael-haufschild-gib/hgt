# Weighted moment repair on the modular arc

- **ID:** whittaker-arc-weighted-moment-repair
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** quantitative-blind-repair-for-the-quarter-strip; `ModularArcWhittakerStability`.
- **Statement:** Prescribed finite cosine Whittaker moments admit a positive atomic arc measure with mass at most four times their Bessel-weighted absolute sum.

For `c_n=2π(n+1)`, put `C_n(u)=K₀(c_n√(1−u²))cos(c_n u)`.
For every finite real vector `v`, seek nonnegative weights and arc points with

```
Σ_i w_i C_n(u_i)=v_n,
Σ_i w_i ≤ 4 Σ_n |v_n|/K₀(c_n).
```

The existing coefficient stability bound suggests that the convex hull of
`(C_n(u))_n` contains the weighted ball
`Σ_n |v_n|/K₀(c_n)≤1/4`. Finite-dimensional separation and the corpus's
atomic cubature theorem should give the measure.

This concerns ordinary Whittaker moments. Transport to twisted integer
moments, cancellation of the pole contribution, and a bound for the actual
arithmetic source remain separate requirements. No quarter-strip bound is
claimed.

## Gates

- [x] Existing stability and finite atomic cubature statements checked.
- [ ] Complete proof of the weighted convex-hull inclusion.
- [ ] Lean formalization and standard-axiom audit.
- [ ] Actual-source transport and quantitative bound.

# Weighted moment repair on the modular arc

- **ID:** whittaker-arc-weighted-moment-repair
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** quantitative-blind-repair-for-the-quarter-strip; `ModularArcWhittakerStability`.
- **Statement:** Every finite cosine Whittaker moment vector has a positive arc realization on at most `N+1` atoms, with mass exactly twice its Bessel-weighted absolute sum.

For `c_n=2π(n+1)`, put `C_n(u)=K₀(c_n√(1−u²))cos(c_n u)`.
For every `v : Fin N → ℝ`, there are nonnegative weights and arc points with

```
Σ_i w_i C_n(u_i)=v_n,
Σ_i w_i = 2 Σ_n |v_n|/K₀(c_n).
```

The closed convex hull of `(C_n(u))_n` contains the weighted ball
`Σ_n |v_n|/K₀(c_n)≤1/2`.

**Proof.** Put `Q_v(t)=2Σ_n(v_n/K₀(c_n))cos(c_n t)` and
`C(v)=Σ_n |v_n|/K₀(c_n)`. The triangle inequality gives `|Q_v|≤2C(v)`.
For `C(v)>0`, the [joint density theorem](whittaker-arc-joint-moment-repair.md)
with mass `2C(v)` gives the atoms. If `C(v)=0`, every coordinate vanishes
and zero weights suffice. The probability statement follows by applying
the same density theorem to `1+Q_v`.

This concerns ordinary Whittaker moments. Transport to twisted integer
moments, cancellation of the pole contribution, and a bound for the actual
arithmetic source remain separate requirements. No quarter-strip bound is
claimed.

## Verification

Lean: `RHTower/ModularArc/WhittakerMomentRepair.lean`:
`exists_arcCosMoment_atoms`, `exists_arcCosMoment_probability_atoms`,
`mem_closure_convexHull_arcCosMomentVector`, and `abs_arcCosMomentPolynomial_le`.
Foreground `lake --old env lean` check passes; all nine public theorems
use only `propext`, `Classical.choice`, and `Quot.sound`.
Imported by `RHTower.lean`.

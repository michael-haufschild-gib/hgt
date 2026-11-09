# Positive infinite deletion isolates a finite spectrum

- **ID:** B130-PTA-I
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `../1-in-progress/b130-positive-tail-annihilation-and-scale-locality.md`
- **Lean:** `SurfaceOfSpecZ/ScaleLocality/PositiveTailIsolation.lean`

## Statement

Let `f(t)=Σ Re(c_j exp(w_j t))`, with `Σ|c_j|<∞` and
`|Re w_j|≤D` on its nonzero coefficients. For square-summable shifts
`h_n`, the positive prefix averages converge at every `t` to

`Σ Re(c_j M(w_j) exp(w_j t))`,

where `M(w)=Π_n (cosh(h_n w)+cosh(h_n a_n))/(1+cosh(h_n a_n))`.
If every exponent outside a finite set is assigned a factor with
`a_n=Re w_j` and `h_n Im w_j=π`, this limit is exactly the finite sum.

For every fixed exponent `w` and every `ε>0`, a tail of the deletion
sequence has square cost below `ε` and a nonzero multiplier at `w`.
The local lower bound from the finite-filter theorem passes to the limit:

`Σ Re(c_j M(w_j)) ≥ -K-2C exp(-qL+(D'+q)²V/2)`

when `f(u)≥-C exp(D'|u|)` globally and `f(u)≥-K` for `|u|≤L`,
with `V=Σh_n²` and `C,K,q≥0`.

At center `t`, the coefficient mass gives the automatic envelope
`C=(Σ|c_j|)exp(D|t|)`. The corresponding translated floor and conjugate
symmetry of the limiting multiplier are also formalized.

## Proof

Square summability makes all late shifts small. The quadratic multiplier
estimate yields absolute convergence of the product after a finite prefix.
Small factors cannot vanish; their product remains nonzero. Tail square
cost tends to zero by convergence of the nonnegative series.

The strip estimate bounds every prefix mode by
`|c_j| exp(D²V/2+D|t|)`. Dominated convergence therefore interchanges
the mode sum and deletion limit. Every assigned exponent is identically
zero from the prefix containing its factor onward. The local lower bound
is uniform over prefixes, so closedness of the order preserves it.

## Audit and limit

Direct `lake --old env lean` passed. Main declarations:
`tendsto_tailAverage_finite_head`, `exists_small_nonzero_tail_multiplier`,
`infinite_tail_local_floor`, `infinite_tail_translated_floor`, and
`tprod_quartetFactor_conj`. Transitive axioms are only `propext`,
`Classical.choice`, and `Quot.sound`. Umbrella import added.

This proves the infinite analytic deletion step. Instantiation on the
zeta spline trace, finite-head oscillation, and prime-window transfer
remain open. No arithmetic Stepanov bound or solution of B130 is claimed.

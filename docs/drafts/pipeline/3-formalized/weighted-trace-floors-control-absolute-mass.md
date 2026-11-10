# Weighted trace floors control absolute mass

- **ID:** A92-weighted-bound
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** If `F(t)=Re Σ_j a_j exp(iγ_jt)≥−K`, `K≥0`, and `w≥0` is integrable, then `∫w|F|≤2K∫w+Σ_j|a_j||ŵ(γ_j)|`.

## Proof

Pointwise, `|F|≤F+2K`. Multiply by `w` and integrate. The signed mean equals the real part of `Σ_j a_j ŵ(γ_j)`, bounded by its sum of norms. Finite exponential sums are bounded, so all integrals exist.

## Formalization

- Module: `SurfaceOfSpecZ/ScaleLocality/WeightedTraceFloors.lean`.
- Theorems: `integral_weight_abs_le_of_floor`, `weighted_finiteExpSum_abs_le`.
- Direct `lake --old env lean` audit passed; transitive axioms are `propext`, `Classical.choice`, `Quot.sound` only.
- Imported by `SurfaceOfSpecZ.lean`.

Coefficient two is optimal: `exists_weight_violating_any_floor_coefficient_lt_two` in `FejerFloorsMakeCoefficientTwoSharp.lean` supplies integrable nonnegative counterweights for every smaller coefficient. Its direct audit also passed with standard axioms only.

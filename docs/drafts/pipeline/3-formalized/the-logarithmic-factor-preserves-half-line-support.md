# The logarithmic factor preserves half-line support

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** If `u∈L²(ℝ)` is supported in `[0,∞)` and `v̂(ξ)=κ(2πiξ)û(ξ)` is in L², then `v` is supported in `[0,∞)`.

## Proof

The actual continued factor satisfies
`|κ(z)|²≤(C+1)(1+|z|²)` on the closed right half-plane.
For `ε>0`, the denominator obeys
`|1+εz|²≥1+ε²|z|²`; hence `κ(z)/(1+εz)` is bounded and
holomorphic through that half-plane.

Rotate to the upper half-plane and apply the proved bounded Hardy multiplier
theorem. On the factor's actual L² graph domain, the regularized outputs are
contractive scalar resolvents applied to the target vector. Strong multiplier
convergence gives their L² limit as `ε↓0`. Closedness of Hardy space retains
membership. Conjugation and the exact Fourier identification of the two Hardy
spaces transport the result to positive physical support.

## Lean

Module `CanonicalSystemOfTheWindowTower/TheLogarithmicFactorPreservesHalfLineSupport.lean`.
Namespace `GaloisForLFunctions.CanonicalSystemOfTheWindowTower`.

- `continuedLogReferenceFactor_norm_sq_le`
- `norm_regularizedLogReferenceFactor_le`
- `logarithmicHardyRegularizer`
- `logarithmicFactor_mul_mem_hardy`
- `logarithmicFactor_mul_mem_hardy_orthogonal`
- `logarithmicFactor_preserves_halfLine_support`

Production plain audit passed. Transitive axioms are exactly
`[propext, Classical.choice, Quot.sound]`; the umbrella imports the module.
This proves support preservation required by the
[Green operator identity](the-half-line-logarithmic-green-kernel.md)
without a complementary Stieltjes representation.

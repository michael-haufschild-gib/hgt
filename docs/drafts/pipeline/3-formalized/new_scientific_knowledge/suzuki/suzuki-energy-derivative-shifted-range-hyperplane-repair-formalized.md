# Suzuki energy derivative: shifted-range hyperplane repair, formalized

- **ID:** `suzuki-energy-derivative-shifted-range-hyperplane-repair`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PAPER-PROVED] [NOVELTY-UNVERIFIED]`
- **Paper proof:** `./suzuki-energy-derivative-shifted-range-hyperplane-repair.md`
- **Lean:**
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiTaHilbertSpace.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiTaSmoothCore.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiTaDeficiencyIndices.lean`

## Formal content

| Card | Lean |
|---|---|
| the energy space, its core and the physical embedding | `SuzukiTaHilbert`, `suzukiTaSmoothCoreToHilbert`, `suzukiTaPhysicalEmbedding`, `suzukiTaPhysicalEmbedding_smoothCore_ae` |
| the continuous exponential moment functionals `L_ε` | `suzukiTaExponentialContinuous`, `suzukiTaExponentialL2`, `suzukiTaMoment`, `suzukiTaMoment_smoothCore_eq_integral` |
| `L_ε(S_ε u) = 0` on the core | `suzukiTaMoment_shift_eq_zero` |
| the primitive `(2)` and `S_ε u = g` | `suzukiTaWeightedCore`, `suzukiTaWeightedPrimitive`, `deriv_suzukiTaWeightedPrimitive`, `suzukiTaShiftedPrimitiveSolution`, `suzukiTaSmoothCoreShift_solution` |
| `(3)` the exact core range | `range_suzukiTaSmoothCoreShiftToHilbert_eq_correction` |
| `(4)` the normalizing bump and the continuous projection | `suzukiTaUnitIntegralBump`, `suzukiTaMomentNormalizer`, `suzukiTaMoment_normalizer`, `DenseCoreHyperplane.correction` |
| `(1)` the exact shifted-range closure | `topologicalClosure_range_suzukiTaSmoothCoreShiftToHilbert` |
| the densely defined operator `D_a + εi` | `suzukiTaShiftedDerivativePMap`, `suzukiTaShiftedDerivativePMap_apply`, `dense_suzukiTaShiftedDerivativePMap_domain`, `suzukiTaShiftedDerivativePMap_rangeSubmodule` |
| `(5)` `ker T* = (ran T)^⊥`, applied | `suzukiTaShiftedDerivativePMap_adjoint_kernel_eq_moment_orthogonal` |
| codimension one and the spanning Riesz vector | `suzukiTaMoment_adjoint_one_ne_zero`, `suzukiTaMoment_adjoint_range_eq_span`, `suzukiTaMoment_kernel_orthogonal_eq_span` |
| deficiency indices `(1,1)` | `finrank_suzukiTaShiftedDerivativePMap_adjoint_kernel`, `suzukiTaShiftedDerivativePMap_deficiencyIndices` |

## Notes

The repair is exactly what the Lean proof does: it never converts energy-continuity into
`L²`-continuity.  Only the physical embedding `H(T_a) → L²(-a,a)` is used, and only in the direction
it actually holds.  The adjoint domain is never described; instead the closure of the shifted core
range is computed and the general Hilbert-space identity `ker T* = (ran T)^⊥` is applied.

Every declaration audits to `[propext, Classical.choice, Quot.sound]`.

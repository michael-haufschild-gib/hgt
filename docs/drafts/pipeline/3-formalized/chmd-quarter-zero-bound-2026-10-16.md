# CHMD: the quarter-strip Birman–Schwinger bound

- **ID:** chmd-quarter-zero-bound-2026-10-16
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), unconditional
- **Source:** CHMD route; sharpening of chmd-birman-schwinger-bound (MUST-1553); corpus inputs: `conj_paperFT_ofReal` (Zeta23), `CHMDGrowthCollapse.gammaOf_reflect`, `conj_mem_zetaCarrier`, `ZeroConfig.reflect_mem`
- **Statement:** (1) `zeroDefect f (1 − ρ̄) = −zeroDefect f ρ`; for real `v`, `zeroDefect v ρ̄ = conj (zeroDefect v ρ)`. (2) Every off-line zero is a quarter zero `σ ∈ {Re > ½, Im ≥ 0}` up to `σ ↦ σ̄`, `σ ↦ 1 − σ̄`, `σ ↦ 1 − σ`; for real tests, vanishing of the quarter defects forces vanishing of all off-line defects. (3) `2·#quarter ≤ #off-line`. (4) A negative-definite family of `k` real compact tests for the Weil form has `k ≤ 2·#quarter`; every orthonormal family of primitive eigenvectors of `R` above `½` has size `≤ 2·#quarter ≤ #off-line` (off-line set finite).
- **Status:** STATUS MUST-1558. One leaf (`CHMDQuarterZeroBound`; 17 declarations), axioms propext/Classical.choice/Quot.sound; plain `lake env lean` audit clean; `lake build --old` green; wired; global lint clean of proof debt (remaining errors are other agents' unwired `PaperThetaCut*` modules).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper proof below = the Lean development)
- [x] 2 → 3  formalized: `zeroDefect_conj_ofReal`, `exists_quarter_of_offLine`, `card_le_two_mul_quarter_of_negative_definite`, `orthonormal_primitive_bound_states_le_two_mul_quarter`
- [ ] 3 → 4  publication-ready

## Obstacle addressed
MUST-1553 paid two real conditions per off-line zero, ignoring that the zero set is a union of
orbits `{ρ, ρ̄, 1−ρ, 1−ρ̄}` and that the tests of the arithmetic graph are real. The defect
functionals of an orbit are, for real tests, determined by the one at its quarter representative
(sign change under reflection, conjugation under `ρ ↦ ρ̄`). The count therefore drops to two real
conditions per orbit: `k ≤ 2·#quarter`, i.e. `#off-line/2` for non-real orbits. This is the sharp
form of the inertia count matching one indefinite `(1,1)` block per orbit.

## Paper proof
`γ_{1−ρ̄} = γ̄_ρ` gives `zeroDefect f (1−ρ̄) = f̂(γ̄) − f̂(γ) = −zeroDefect f ρ`. `γ_{ρ̄} = −γ̄_ρ` and
`conj f̂(z) = f̂(−z̄)` for real `f` give `zeroDefect f ρ̄ = f̂(−γ̄) − f̂(−γ) = conj(f̂(γ) − f̂(γ̄))`.
Case analysis on the signs of `Re ρ − ½` and `Im ρ` places every off-line zero in an orbit of a
quarter zero (the carrier is closed under conjugation and reflection). In the Birman–Schwinger
argument, the linear map `c ↦ (zeroDefect(Σ cᵢ Θvᵢ, σ))_{σ ∈ quarter}` into `ℂ^{quarter}` is
injective (a nonzero kernel element has all quarter defects zero, hence all off-line defects zero,
hence `Re W ≥ 0` by the defect inequality of MUST-1553, contradicting negative definiteness), so
`k ≤ 2·#quarter`. The quarter zeros and their reflections are disjoint (real parts on opposite
sides of `½`) subsets of the off-line zeros, so `2·#quarter ≤ #off-line`.

## Lean module (namespace `RHTower.CHMDPolar`)
`RHTower/CHMDQuarterZeroBound.lean` — `reflect_re`, `reflect_im`, `reflect_reflect`, `gammaOf_conj`,
`zeroDefect_reflect`, `zeroDefect_conj_ofReal`, `quarterZeros`, `quarterZeros_subset_offLine`,
`exists_quarter_of_offLine`, `zeroDefect_ofReal_eq_zero_of_quarter`, `quarterFinset`, `mem_quarterFinset`,
`card_quarterFinset`, `two_mul_ncard_quarterZeros_le`, `card_le_two_mul_quarter_of_negative_definite`,
`orthonormal_primitive_bound_states_le_two_mul_quarter`, `orthonormal_primitive_bound_states_le_offLine`.

## Big picture
- Two-sided count of the bound states above the essential threshold: `weilNegIndex ζ a ε ≤ dim P`
  (MUST-1557), visible separated deep zero sets `T` give `|T| ≤ dim P + 2`, and orthonormal
  primitive bound-state families have size `≤ 2·#quarter ≤ #off-line` (finite case).

## Next conjectures
1. `P` finite-dimensional with `dim P ≤ 2·#quarter + 1` when the off-line set is finite
   (orthogonal eigenspace decomposition of `P`).
2. Exact signature: one bound state per orbit for well-separated deep orbits (combine the corpus
   visible-pair lower bound with the quarter count).

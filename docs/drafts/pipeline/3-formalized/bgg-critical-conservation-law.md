# Finite-support Bochner inequality and the critical conservation law

- **ID:** bgg-c13
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:**
  1. If `φ : ℝ → ℝ` is even, positive definite on the discrete group `ℝ`, and vanishes off `{0} ∪ ±Z`
     for a finite set `Z` of positive reals, then `φ(0) + 2 Σ_{z ∈ Z} φ(z) cos(θz) ≥ 0` for all `θ`.
  2. (Line conservation) For the Abel–Gram jump `r(t) = ord_{x₀+it}Λ₀ − ord_{x₀+it}Λ` with finitely many
     nonzero values off `0`: `r(0) + 2 Σ_{z∈Z} r(z) cos(θz) ≥ 0`.
  3. (Critical conservation) A positive deformation of `ζ_γ` (no off-critical zero at `γ`) changing
     finitely many critical zeros: `ord_{1/2}Λ_γ − ord_{1/2}Λ ≥ 2 Σ_{t∈Z}(ord_{1/2+it}Λ − ord_{1/2+it}Λ_γ)`,
     i.e. every created critical zero above the axis costs two central orders, net of destroyed ones.

## Paper proof
1. On the Følner sets `F_N = {Σ n_z z : 0 ≤ n_z < N}` the unit Gram sum of `ψ(u) = φ(u)cos(θu)` (positive
   definite as a twisted form) equals `|F_N|ψ(0) + 2Σ_z ψ(z)·#{y : y, y + z ∈ F_N}`. Each count is
   within `ε|F_N|` of `|F_N|` at a step where `|F_{N+1}| ≤ (1 + ε)|F_N|` (polynomial growth), so
   `ψ(0) + 2Σψ(z) ≥ −2εΣ|ψ(z)|` for all `ε > 0`.
2–3. Apply 1 to the even positive-definite jump of the Abel–Gram law.

## Lean
`TheCriticalConservationLaw.lean`: `nonneg_of_finite_support_gram`, `cos_sum_nonneg_of_finite_support`,
`jump_cos_sum_nonneg_of_rel`, `centralDrop_ge_two_mul_created_sub_destroyed`.
Axioms: propext, Classical.choice, Quot.sound.

## Log
- 2026-10-27 — formalized.

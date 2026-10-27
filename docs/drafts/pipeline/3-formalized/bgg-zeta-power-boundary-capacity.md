# The Abel–Gram law and the boundary capacity of deformations of ζ^d

- **ID:** bgg-c10
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** APD README open topic 9 (equality case of completed capacity), beyond the rational class.
- **Statement:**
  1. (Abel–Gram) If entire `Λ, Λ₀` (finite orders) satisfy `Λ₀'/Λ₀ − Λ'/Λ = 𝓛ν + E` on `Re z > x₀` away
     from zeros, `ν ≥ 0` with integrable kernel there, `E` holomorphic on `Re z > σ_E`, `σ_E < x₀`, then
     `(σ − x₀)𝓛ν(σ + it) → ord_{x₀+it}Λ₀ − ord_{x₀+it}Λ`; the jump function is even positive definite;
     every jump is at most the real jump; if `Λ₀` has no zero on the line off the axis,
     `2 Σ_{t∈Z} ord_{x₀+it}Λ ≤ ord_{x₀}Λ₀ − ord_{x₀}Λ`.
  2. (Boundary capacity) `(F, Λ) ∈ CompletedPositiveSystem κ d` with `−F'/F + dζ'/ζ = 𝓛ν + E`, `σ_E < 1`:
     `2 Σ_{t∈Z} ord_{1+it}Λ ≤ κ − d` for every finite set of positive heights. Same for arithmetic members
     whose deficit against `dΛ` has abscissa `< 1`; for `κ ≤ d + 1` no zero on `Re s = 1` off `s = 1`.

## Paper proof
1. Multiply the relation at `σ + it` by `σ − x₀ = z − w`: the logarithmic derivatives give the orders,
   `(z − w)E(z) → 0`. The real part of `(σ − x₀)𝓛ν(σ + it)` is `(σ − x₀)∫e^{−σu}cos(tu)dν`, even positive
   definite; limits keep this. `|𝓛ν(σ + it)| ≤ 𝓛ν(σ)` gives the transfer bound; the total zero mass law
   gives the capacity.
2. Landau–Wronskian principle for `Λ(s(s−1))^{d−κ}` against `(s(s−1))^{κ−d}(2ξ)^d`. If the abscissa is left
   of `Re s = 1`, orders agree on the line, and `ζ(1+it) ≠ 0` gives no boundary zeros. Otherwise the anchor
   is `c = 1` with `d < κ`; the base has order `κ − d` at `1` and no zero on the line off the axis, and
   part 1 at `x₀ = 1` gives the bound. The arithmetic form uses the surplus/deficit split against `dΛ`.

## Lean
`TheAbelGramLawOfPositiveDeformations.lean`: `norm_complexLaplace_le`, `eventually_ne_zero_of_orderAt_ne_top`,
`tendsto_ofReal_add_mul_I_nhdsGT`, `tendsto_abel_of_rel`, `abs_jump_le_of_rel`, `isEvenPosDef_laplace_cos`,
`jump_isEvenPosDef_of_rel`, `sum_jump_le_of_rel`.
`TheBoundaryCapacityOfDeformationsOfPowersOfZeta.lean`: `xi_one_add_mul_I_ne_zero`,
`analyticOrderAt_zetaPow_base_one`, `zetaPowDeformation_boundary_capacity`, `latticeMember_boundary_capacity`,
`latticeMember_ne_zero_on_boundary`. Axioms: propext, Classical.choice, Quot.sound.

## Log
- 2026-10-27 — formalized.

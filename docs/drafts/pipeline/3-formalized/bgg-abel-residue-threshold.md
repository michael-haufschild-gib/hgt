# The Abel-residue threshold of the prime deficit

- **ID:** bgg-c11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Let `(F, Λ) ∈ HeightCoupledSystem 2 1 1 γ` with `−F'/F = Σ b(n)n^{−s}` (`b ≥ 0`), deficit
  `d = (b_γ − b)⁺` whose series `D` converges absolutely on `Re s > 1/2`, and let `ξ` have no off-critical
  zero at ordinate `γ`. If `(σ − 1/2) D(σ) → 0` as `σ ↓ 1/2` and `ord_{1/2}Λ ≥ ord_{1/2}Λ_γ`, then
  `b(n) = b_γ(n)` for all `n ≥ 1` and `F = Kζ_γ`, `K ∈ ℝ^×`. Equivalently, a member keeping the central
  order and differing from `ζ_γ` has a deficit with nonzero Abel residue at `1/2`. Together with the
  deficit–excess law (`ord_{1/2}Λ − ord_{1/2}Λ_γ ≤ liminf (σ − 1/2) D(σ)`), the Abel residue of the
  deficit at the centre is the exact invariant.

## Paper proof
`−F'/F + ζ_γ'/ζ_γ = 𝓛(surplus) + b(1) − D` on `Re s > 1/2`. The Landau–Wronskian principle with
`σ_E = 1/2` and no off-critical zero gives abscissa `c ≤ 1/2` and equal orders on `Re s > 1/2`; by
symmetry on `Re s < 1/2`. On the critical line `|D(σ + it)| ≤ D(σ)`, so `(σ − 1/2)(b(1) − D(σ + it)) → 0`:
the perturbation is Abel-negligible, and the Abel–Gram transfer law bounds every critical jump by the
central drop, which is `≤ 0`. All orders agree; divisor rigidity gives `F = Kζ_γ`, and Dirichlet
coefficients are unique. Abscissa `< 1/2` implies zero residue by continuity.

## Lean
`StrongMultiplicityOneBelowTheSquareRootDeficit.lean`: `norm_LSeries_le_re_of_nonneg`,
`tendsto_sub_mul_LSeries_of_residue_zero`, `tendsto_residue_zero_of_abscissa_lt`,
`latticeMember_eq_of_negligible_deficit`, `latticeMember_eq_of_subcritical_deficit` (corollary),
`not_tendsto_deficit_residue_of_ne`. Abel–Gram API: `tendsto_sub_mul_of_differentiableOn`.
Axioms: propext, Classical.choice, Quot.sound.

## Log
- 2026-10-27 — formalized.

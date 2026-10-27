# Strong multiplicity one below the square-root deficit

- **ID:** bgg-c7
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Let `(F, Λ) ∈ HeightCoupledSystem 2 1 1 γ` with `−F'/F = Σ b(n) n^{−s}`, `b ≥ 0`,
  abscissa `≤ 1`, deficit `d = (b_γ − b)⁺` with `σ_a(d) < 1/2`, and let `ξ` have no off-critical zero at
  ordinate `γ`. If `ord_{1/2} Λ ≥ ord_{1/2} Λ_γ`, then `b(n) = b_γ(n)` for all `n ≥ 1` and `F = K ζ_γ`,
  `K ∈ ℝ^×`. Equivalently: equal central order and `b ≠ b_γ` force `σ_a(d) ≥ 1/2`; with subcritical deficit,
  `b = b_γ` or the central order drops. At ordinates whose horizontal line carries no zero of `ξ`
  (unconditionally at `γ = 0`) every member with subcritical deficit is `K ζ_γ`.

## Paper proof
Split `−F'/F + ζ_γ'/ζ_γ = 𝓛(surplus) + (b(1) − D)`, the surplus atomic and nonnegative, `D` the deficit
series, holomorphic on `Re s > σ_E` for some `σ_E < 1/2`. The perturbed positive theory applies: off-line
rigidity plus the critical transfer law with zero central drop give `ord_w Λ = ord_w Λ_γ` for all `w`.
Divisor rigidity: the entire quotient `Λ/Λ_γ` is zero-free of order one, `= Q e^{Bs}`; `Λ(1 − s) = Λ(s)` and
the same for `Λ_γ` give `e^{B(1−2s)} = 1` on `Re s > 1`, so `B = 0`; conjugation at `s = 2` makes `Q` real;
cancelling the common archimedean factor gives `F = Q ζ_γ` on `Re s > 1`. Then `Σ b(n)n^{−s} = Σ b_γ(n)n^{−s}`
on `Re s > 1`, and Dirichlet coefficients are unique.

## Lean
`StrongMultiplicityOneBelowTheSquareRootDeficit.lean`: `latticeMember_eq_of_subcritical_deficit`,
`half_le_deficit_abscissa_of_ne`, `latticeMember_eq_or_centralDrop`, `centralOrder_heightCoupledΛ_eq_zero`,
`latticeMember_eq_of_xi_ne_zero_on_line`, `latticeMember_eq_of_subcritical_deficit_zero`; uses
`perturbedDeformation_orders_eq_of_central_le`, `eq_const_mul_of_orders_eq` (C6 module).
Axioms: propext, Classical.choice, Quot.sound.

## Log
- 2026-10-27 — formalized.

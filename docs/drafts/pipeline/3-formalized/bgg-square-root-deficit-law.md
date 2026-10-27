# Central excess forces a square-root prime deficit

- **ID:** bgg-c4
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Let `F ∈ HeightCoupledSystem 2 1 1 γ` with `−F'/F = Σ b(n) n^{−s}`, `b ≥ 0`,
  abscissa `≤ 1`, and let `d(n) = (b_γ(n) − b(n))⁺` (`n ≥ 2`), `b_γ(n) = Λ(n)(2 + 2cos(γ log n))`.
  If `ξ` has no off-critical zero at ordinate `γ` and `ord_{1/2} Λ > ord_{1/2} Λ_γ` (or the orders differ
  at some `w` off the critical line), then `abscissaOfAbsConv d ≥ 1/2`.

## Paper proof
`b − b_γ = [n = 1]b(1) + s − d` with `s = (b − b_γ)⁺`. The surplus is the nonnegative atomic measure
`Σ s(n)δ_{log n}`; `E(s) = b(1) − Σ d(n)n^{−s}` is holomorphic on `Re s > σ_E` for any
`σ_E > abscissa(d)`. If `abscissa(d) < 1/2` pick `σ_E < 1/2`. The perturbed version of the positive
deformation theorem (Wronskian on `Re s > max(c, σ_E)`; Landau at the abscissa `c` of the thickened
surplus measure when `c > σ_E`) yields off-line rigidity and the central ceiling — contradiction.

## Lean
`PositivePrimeMassDeformationsAreRigidOffTheCriticalLine.lean`:
`positiveDeformation_orders_and_anchor_of_perturbation`, `perturbedDeformation_offLine_rigid`.
`CentralExcessForcesASquareRootPrimeDeficit.lean`: `latticeMeasure`, `laplace_latticeMeasure`,
`sub_eq_surplus_sub_deficit`, `latticeMember_offLine_rigid_of_subcritical_deficit`,
`centralExcess_forces_squareRoot_deficit`. Axioms: propext, Classical.choice, Quot.sound.

## Log
- 2026-10-27 — formalized.

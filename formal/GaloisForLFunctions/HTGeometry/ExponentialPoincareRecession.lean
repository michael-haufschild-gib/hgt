import GaloisForLFunctions.HTGeometry.PoincareRecession
import GaloisForLFunctions.HTGeometry.ExponentialTowerUnitCost

/-!
# Constraint-order recession for the exponential Poincaré approximants

The `n`-fold exponential has differential order exactly `n`, and an invertible affine
reparametrisation does not move the minimal order, so the normalized Poincaré approximants
`z ↦ exp^{[n]}(ζ + z/λⁿ)` at a repelling fixed point have exact differential orders `1, 2, 3, …`.

`Complex.exp` is a transcendental entire solution of the autonomous first-order equation `f′ = f`,
so this is the recession law for an explicit member of the class, with no residual hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- The iterated exponential is the exponential tower. -/
theorem expTower_eq_iterate (n : ℕ) : expTower n = Complex.exp^[n] := by
  rw [expTower, entireCascade_const]

/-- **The unit-cost law for the iterated exponential.**  Unconditional. -/
theorem exactDifferentialOrder_exp_iterate (m : ℕ) :
    ExactDifferentialOrder (Complex.exp^[m + 1]) (m + 1) := by
  rw [← expTower_eq_iterate]
  exact exactDifferentialOrder_expTower m

/-- **Constraint-order recession for the exponential Poincaré approximants.**  The normalized
approximants `z ↦ exp^{[n]}(ζ + z/λⁿ)` at a repelling fixed point of the exponential have exact
differential orders `1, 2, 3, …`.  Unconditional: `Complex.exp` is a transcendental entire solution
of the autonomous first-order equation `f' = f`, so the card's hypothesis class is inhabited with
the full conclusion. -/
theorem exactDifferentialOrder_poincareApprox_exp {ζ lam : ℂ} (hlam : lam ≠ 0) (m : ℕ) :
    ExactDifferentialOrder
      (fun z => Complex.exp^[m + 1] (ζ + z / lam ^ (m + 1))) (m + 1) :=
  exactDifferentialOrder_poincareApprox hlam (exactDifferentialOrder_exp_iterate m)

/-- The differential orders of the exponential Poincaré approximants are unbounded. -/
theorem exists_exactDifferentialOrder_poincareApprox_exp_ge {ζ lam : ℂ} (hlam : lam ≠ 0)
    (N : ℕ) : ∃ n : ℕ, N ≤ n ∧
      ExactDifferentialOrder (fun z => Complex.exp^[n] (ζ + z / lam ^ n)) n :=
  ⟨N + 1, by omega, exactDifferentialOrder_poincareApprox_exp hlam N⟩

end GaloisForLFunctions.HTGeometry

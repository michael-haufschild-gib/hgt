import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt.FiniteTateTowers
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt.PadicTateTower
import GaloisForLFunctions.HTGeometry.BirchTateCyclotomicNontriviality

/-!
# Squared-cyclotomic invariants in compatible p-adic division towers

For every number field the existing Birch--Tate fixed module is finite.
It therefore has zero Tate tower. Equivalently, no nonzero compatible
division tower in `ℚ_p/ℤ_p` is fixed coordinatewise by the squared cyclotomic
character. Every nonzero p-adic numerator has a division point moved by that
character, despite the possible presence of fixed torsion at finite levels.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt

open GaloisForLFunctions.HTGeometry

variable (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [NumberField F]

/-- The finite Birch--Tate fixed module contributes no compatible Tate tower. -/
theorem birchTate_fixedTower_eq_zero
    (x : tateTower p (padicTateTwistTwoInvariants p F)) : x = 0 := by
  letI := finite_padicTateTwistTwoInvariants p F
  exact finite_tateTower_eq_zero p _ x

/-- Coordinatewise squared-cyclotomic invariance of a tower is equivalent to vanishing. -/
theorem padicTateTower_fixed_iff_zero (x : tateTower p (PadicTateQuotient p)) :
    (∀ n : ℕ, x.1 n ∈ padicTateTwistTwoInvariants p F) ↔ x = 0 := by
  constructor
  · intro h
    let y : tateTower p (padicTateTwistTwoInvariants p F) :=
      ⟨fun n => ⟨x.1 n, h n⟩,
        (fun n => Subtype.ext (x.2.1 n)), (fun n => Subtype.ext (x.2.2 n))⟩
    have hy := birchTate_fixedTower_eq_zero p F y
    apply Subtype.ext
    funext n
    exact congrArg (fun z : tateTower p (padicTateTwistTwoInvariants p F) => (z.1 n).1) hy
  · rintro rfl
    intro n
    exact (padicTateTwistTwoInvariants p F).zero_mem

/-- All division points of a numerator are fixed exactly when the numerator is zero. -/
theorem padicDivisionPoints_fixed_iff_zero (z : ℤ_[p]) :
    (∀ n : ℕ, padicDivisionPoint p n z ∈ padicTateTwistTwoInvariants p F) ↔ z = 0 := by
  constructor
  · intro h
    apply padicTateTowerEmbedding_injective p
    rw [map_zero]
    exact (padicTateTower_fixed_iff_zero p F (padicTateTowerEmbedding p z)).mp h
  · rintro rfl
    intro n
    rw [map_zero]
    exact (padicTateTwistTwoInvariants p F).zero_mem

/-- Every nonzero p-adic numerator has a division point outside the finite fixed module. -/
theorem exists_nonfixed_divisionPoint_iff (z : ℤ_[p]) :
    (∃ n : ℕ, padicDivisionPoint p n z ∉ padicTateTwistTwoInvariants p F) ↔ z ≠ 0 := by
  classical
  simpa only [not_forall] using not_congr (padicDivisionPoints_fixed_iff_zero p F z)

#print axioms birchTate_fixedTower_eq_zero
#print axioms padicTateTower_fixed_iff_zero
#print axioms exists_nonfixed_divisionPoint_iff

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt

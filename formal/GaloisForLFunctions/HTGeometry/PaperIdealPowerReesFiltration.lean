import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.ReesCoefficientKernel
import GaloisForLFunctions.HTGeometry.ReesGrading

/-!
# Ideal powers in the paper's increasing integer-filtration convention

For an arbitrary ideal `I`, set `F(d)=I^max(-d,0)`. Multiplicativity and
monotonicity are proved from the ideal-power laws, so the paper's Laurent
Rees algebra and its specialization require no additional filtration data.
The degree `-n` graded piece is exactly the usual `I^n/I^(n+1)` piece.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

noncomputable section

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- Ideal powers, reindexed as an increasing integer filtration. -/
def paperIdealPowerFiltration (d : ℤ) : Submodule R R :=
  (I ^ (-d).toNat : Ideal R)

/-- The ideal-power filtration is increasing without a Noetherian assumption. -/
theorem paperIdealPowerFiltration_mono : Monotone (paperIdealPowerFiltration I) := by
  intro a b hab
  exact Ideal.pow_le_pow_right (I := I) (by omega)

/-- Multiplicativity follows from the ideal-power product law. -/
instance paperIdealPowerFiltration_gradedMonoid : SetLike.GradedMonoid (paperIdealPowerFiltration I) where
  one_mem := by
    change (1 : R) ∈ I ^ (-(0 : ℤ)).toNat
    simp
  mul_mem := by
    intro i j a b ha hb
    change a * b ∈ I ^ (-(i + j)).toNat
    apply Ideal.pow_le_pow_right (I := I)
      (m := (-(i + j)).toNat) (n := (-i).toNat + (-j).toNat) (by omega)
    rw [pow_add]
    exact Ideal.mul_mem_mul ha hb

/-- Natural ideal order `n` appears at integer degree `-n`. -/
theorem paperIdealPowerFiltration_neg_nat (n : ℕ) :
    paperIdealPowerFiltration I (-(n : ℤ)) = (I ^ n : Ideal R) := by
  simp [paperIdealPowerFiltration]

/-- The previous integer step is exactly the next ideal power. -/
theorem paperIdealPowerFiltration_neg_nat_sub_one (n : ℕ) :
    paperIdealPowerFiltration I (-(n : ℤ) - 1) = (I ^ (n + 1) : Ideal R) := by
  unfold paperIdealPowerFiltration
  have hn : (-(-(n : ℤ) - 1)).toNat = n + 1 := by omega
  rw [hn]

/-- The actual extended Rees algebra for the ideal-power filtration. -/
abbrev PaperIdealExtendedRees := FilteredRees.rees (paperIdealPowerFiltration I)

/-- Its specialization at the positive Laurent parameter. -/
abbrev PaperIdealAssociatedGraded :=
  FilteredRees.Gr (paperIdealPowerFiltration I) (paperIdealPowerFiltration_mono I)

/-- Exact coefficient criterion in the extended native ideal-power Rees algebra. -/
theorem paperIdealExtendedRees_specialization_eq_zero_iff (p : PaperIdealExtendedRees I) :
    Ideal.Quotient.mk
      (FilteredRees.parameterIdeal (paperIdealPowerFiltration I) (paperIdealPowerFiltration_mono I)) p = 0 ↔
      ∀ d : ℤ, (p : LaurentPolynomial R).coeff d ∈ I ^ (1 - d).toNat := by
  rw [FilteredRees.mk_eq_zero_iff_coeff]
  apply forall_congr'
  intro d
  change _ ∈ I ^ (-(d - 1)).toNat ↔ _
  rw [show -(d - 1) = 1 - d by omega]

end

end GaloisForLFunctions.HTGeometry

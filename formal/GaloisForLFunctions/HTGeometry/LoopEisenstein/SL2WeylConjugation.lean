import GaloisForLFunctions.HTGeometry.LoopEisenstein.SL2WeylLifts

/-!
# Finite Weyl conjugation in the symbol extension

The canonical Weyl lift at parameter one inverts every diagonal section.
The matrix relation lifts exactly: its only possible extra symbol is twice
a self-pairing, which is zero by antisymmetry.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable {K A : Type*} [Field K] [AddCommGroup A]

theorem sl2WeylLower_one_mul_diagonal (a : Kˣ) :
    sl2WeylLower 1 * sl2Diagonal a = sl2Diagonal a⁻¹ * sl2WeylLower 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2WeylLower, sl2Diagonal, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two]

private theorem kubotaUnit_weyl_one_diagonal (a : Kˣ) :
    kubotaUnit (sl2WeylLower 1 * sl2Diagonal a) = a := by
  apply Units.ext
  simp [kubotaX, sl2WeylLower, sl2Diagonal, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Fin.sum_univ_two, a.ne_zero]

private theorem cocycle_weyl_one_diagonal (a : Kˣ) :
    kubotaCocycle (sl2WeylLower 1) (sl2Diagonal a) = 0 := by
  rw [kubotaCocycle, kubotaUnit_weyl_one_diagonal, kubotaUnit_weylLower,
    kubotaUnit_diagonal, div_one, div_eq_mul_inv, inv_inv, milnorSym2_mul_right]
  conv_lhs => lhs; rw [milnorSym2_antisymm a a]
  exact neg_add_cancel _

private theorem cocycle_diagonal_inv_weyl_one (a : Kˣ) :
    kubotaCocycle (sl2Diagonal a⁻¹) (sl2WeylLower 1) = 0 := by
  rw [kubotaCocycle, ← sl2WeylLower_one_mul_diagonal, kubotaUnit_weyl_one_diagonal,
    kubotaUnit_diagonal, inv_inv, kubotaUnit_weylLower, div_one,
    div_eq_mul_inv, mul_inv_cancel, milnorSym2_one_left]

namespace SL2SymbolExtension

variable (τ : MilnorKDeg K 2 →+ A)

/-- The matrix Weyl relation lifts without any extra central factor. -/
theorem weylLower_one_mul_diagonal (a : Kˣ) :
    weylLower τ 1 * sectionOf τ (sl2Diagonal a) =
      sectionOf τ (sl2Diagonal a⁻¹) * weylLower τ 1 := by
  apply SL2SymbolExtension.ext
  · exact sl2WeylLower_one_mul_diagonal a
  · change 0 + 0 + τ (kubotaCocycle (sl2WeylLower 1) (sl2Diagonal a)) =
      0 + 0 + τ (kubotaCocycle (sl2Diagonal a⁻¹) (sl2WeylLower 1))
    rw [cocycle_weyl_one_diagonal, cocycle_diagonal_inv_weyl_one]

/-- The canonical finite Weyl lift inverts the diagonal parameter. -/
theorem weylLower_one_conj_diagonal (a : Kˣ) :
    weylLower τ 1 * sectionOf τ (sl2Diagonal a) * (weylLower τ 1)⁻¹ =
      sectionOf τ (sl2Diagonal a⁻¹) := by
  rw [weylLower_one_mul_diagonal, mul_assoc, mul_inv_cancel, mul_one]

end SL2SymbolExtension

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein

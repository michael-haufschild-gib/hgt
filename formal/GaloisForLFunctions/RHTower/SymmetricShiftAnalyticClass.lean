import GaloisForLFunctions.RHTower.SymmetricShiftFunctionalEquation
import GaloisForLFunctions.RHTower.XiZeroCountJensenBound
import GaloisForLFunctions.RHTower.DirichletCompletedLOrderOne

open Complex Set

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem analyticOnNhd_symmetricShiftProduct
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F univ) (a : ℝ) :
    AnalyticOnNhd ℂ (symmetricShiftProduct F a) univ := by
  rw [analyticOnNhd_univ_iff_differentiable] at hF ⊢
  unfold symmetricShiftProduct
  fun_prop

theorem orderOneEnvelope_symmetricShiftProduct
    {F : ℂ → ℂ} (hF : OrderOneEnvelope F) (a : ℝ) :
    OrderOneEnvelope (symmetricShiftProduct F a) := by
  have hplus := hF.comp_affine 1 (a : ℂ)
  have hminus := hF.comp_affine 1 (-(a : ℂ))
  refine (hplus.mul hminus).congr ?_
  intro s
  unfold symmetricShiftProduct
  simp only [one_mul]
  congr 1

theorem xi_symmetricShiftProduct_analyticOnNhd (a : ℝ) :
    AnalyticOnNhd ℂ (symmetricShiftProduct xi a) univ :=
  analyticOnNhd_symmetricShiftProduct xi_analyticOnNhd_univ a

theorem xi_symmetricShiftProduct_orderOneEnvelope (a : ℝ) :
    OrderOneEnvelope (symmetricShiftProduct xi a) :=
  orderOneEnvelope_symmetricShiftProduct orderOneEnvelope_xi a

theorem completedLFunction_symmetricShiftProduct_analyticOnNhd
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (a : ℝ) :
    AnalyticOnNhd ℂ
      (symmetricShiftProduct (DirichletCharacter.completedLFunction χ) a) univ := by
  apply analyticOnNhd_symmetricShiftProduct
  rw [analyticOnNhd_univ_iff_differentiable]
  exact DirichletCharacter.differentiable_completedLFunction hχ

theorem completedLFunction_symmetricShiftProduct_orderOneEnvelope
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (a : ℝ) :
    OrderOneEnvelope
      (symmetricShiftProduct (DirichletCharacter.completedLFunction χ) a) :=
  orderOneEnvelope_symmetricShiftProduct (completedLFunction_orderOneEnvelope hχ) a

end


end RHTower

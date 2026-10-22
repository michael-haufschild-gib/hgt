import GaloisForLFunctions.HTGeometry.RegularizedDeterminantAlgebraicMultiplicity
import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.RHTower.PositiveOperatorKernel
import GaloisForLFunctions.RHTower.Suzuki.SuzukiWeilZeroSeries

/-!
# Positive operators cannot carry exact Xi determinants

The even centered Xi divisor has both positive and negative real zeros unconditionally. A positive
Hilbert--Schmidt operator has no negative eigenvalue, so its Hilbert--Carleman determinant cannot
carry that divisor through any zero-free gauge.
-/

open Complex Set
open HilbertSchmidt

namespace RHTower

noncomputable section

/-- A function has exactly the nonzero reciprocal point spectrum of an operator as its zeros. -/
def HasReciprocalEigenvalueZeroSet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →L[ℂ] E) (D : ℂ → ℂ) : Prop :=
  ∀ z, z ≠ 0 →
    (D z = 0 ↔ ∃ w : E, w ≠ 0 ∧ T w = z⁻¹ • w)

/-- A positive operator cannot supply the centered Xi divisor through any zero-free gauge and any
determinant function whose nonzero zeros are exactly its reciprocal eigenvalues. -/
theorem positiveOperator_not_exactXiSpectralZeroFunction
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {T : E →L[ℂ] E} (hpos : T.IsPositive) :
    ¬ ∃ (D H : ℂ → ℂ),
      HasReciprocalEigenvalueZeroSet T D ∧
      (∀ z, H z ≠ 0) ∧
      (∀ z, XiC z = H z * D z) := by
  rintro ⟨D, H, hzeros, hH, hXi⟩
  obtain ⟨a, b, ha, hb, hab, hza, hzb⟩ :=
    exists_two_distinct_positive_real_XiC_zeros
  let z : ℂ := ((-a : ℝ) : ℂ)
  have hzXi : XiC z = 0 := by
    calc
      XiC z = XiC (-((a : ℝ) : ℂ)) := by simp [z]
      _ = XiC (a : ℂ) := XiC_neg _
      _ = 0 := hza
  have hD : D z = 0 := by
    have hmul : H z * D z = 0 := by simpa [hXi z] using hzXi
    exact (mul_eq_zero.mp hmul).resolve_left (hH z)
  have hz0 : z ≠ 0 := by
    intro hz
    have : a = 0 := by
      have hzre := congrArg Complex.re hz
      simpa [z] using neg_eq_zero.mp hzre
    linarith
  obtain ⟨w, hw0, hw⟩ := (hzeros z hz0).mp hD
  have hzinv : z⁻¹ = (((-a : ℝ)⁻¹ : ℝ) : ℂ) := by
    exact (Complex.ofReal_inv (-a)).symm
  rw [hzinv] at hw
  have hquad := hpos.re_inner_nonneg_right w
  rw [hw] at hquad
  simp only [inner_smul_right, inner_self_eq_norm_sq_to_K] at hquad
  rw [inv_neg] at hquad
  norm_num at hquad
  have hainv : 0 < a⁻¹ := inv_pos.mpr ha
  have hwnorm : 0 < ‖w‖ ^ (2 : ℕ) := sq_pos_of_pos (norm_pos_iff.mpr hw0)
  have hcast : ((↑‖w‖ ^ (2 : ℕ) : ℂ)).re = ‖w‖ ^ (2 : ℕ) := by
    rw [← Complex.ofReal_pow]
    rfl
  rw [hcast] at hquad
  nlinarith

/-- No positive Hilbert--Schmidt kernel operator has an exact zero-free-gauge Xi determinant. -/
theorem positiveOperator_not_exactXiDeterminant
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hpos : (toOperator hK).IsPositive)
    (H : ℂ → ℂ) (hH : ∀ z, H z ≠ 0) :
    ¬ (∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z) := by
  intro hXi
  obtain ⟨a, b, ha, hb, hab, hza, hzb⟩ :=
    exists_two_distinct_positive_real_XiC_zeros
  let z : ℂ := ((-a : ℝ) : ℂ)
  have hzXi : XiC z = 0 := by
    calc
      XiC z = XiC (-((a : ℝ) : ℂ)) := by simp [z]
      _ = XiC (a : ℂ) := XiC_neg _
      _ = 0 := hza
  have hdet : GaloisForLFunctions.HTGeometry.entireDet2 K z = 0 := by
    have hmul : H z * GaloisForLFunctions.HTGeometry.entireDet2 K z = 0 := by
      simpa [hXi z] using hzXi
    exact (mul_eq_zero.mp hmul).resolve_left (hH z)
  have hz0 : z ≠ 0 := by
    intro hz
    have : a = 0 := by
      have hzre := congrArg Complex.re hz
      simpa [z] using neg_eq_zero.mp hzre
    linarith
  obtain ⟨w, hw0, hw⟩ :=
    (GaloisForLFunctions.HTGeometry.entireDet2_eq_zero_iff_exists_eigenvector
      hK hz0).mp hdet
  have hzinv : z⁻¹ = (((-a : ℝ)⁻¹ : ℝ) : ℂ) := by
    exact (Complex.ofReal_inv (-a)).symm
  rw [hzinv] at hw
  have hquad := hpos.re_inner_nonneg_right w
  rw [hw] at hquad
  simp only [inner_smul_right, inner_self_eq_norm_sq_to_K] at hquad
  rw [inv_neg] at hquad
  norm_num at hquad
  have hainv : 0 < a⁻¹ := inv_pos.mpr ha
  have hwnorm : 0 < ‖w‖ ^ (2 : ℕ) := sq_pos_of_pos (norm_pos_iff.mpr hw0)
  have hcast : ((↑‖w‖ ^ (2 : ℕ) : ℂ)).re = ‖w‖ ^ (2 : ℕ) := by
    rw [← Complex.ofReal_pow]
    rfl
  rw [hcast] at hquad
  nlinarith

end

end RHTower

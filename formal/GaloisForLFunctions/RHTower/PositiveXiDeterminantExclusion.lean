import GaloisForLFunctions.HTGeometry.RegularizedDeterminantAlgebraicMultiplicity
import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.RHTower.PositiveOperatorKernel
import GaloisForLFunctions.RHTower.SuzukiWeilZeroSeries

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
  have hwnorm : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw0)
  have hcast : ((↑‖w‖ ^ 2 : ℂ)).re = ‖w‖ ^ 2 := by
    rw [← Complex.ofReal_pow]
    rfl
  rw [hcast] at hquad
  nlinarith

end

end RHTower

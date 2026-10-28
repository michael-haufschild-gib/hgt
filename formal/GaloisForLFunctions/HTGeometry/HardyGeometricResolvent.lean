import GaloisForLFunctions.HTGeometry.HardyBlaschkeMonomialBasis
import GaloisForLFunctions.HTGeometry.HardyBeurlingInvariantSubspace

/-!
# The geometric resolvent and the KMS kernel on Hardy coefficients

A linear combination of the identity and one Blaschke multiplier is the
resolvent of the unilateral shift. Adding its adjoint and subtracting the
identity gives the actual geometric Toeplitz matrix on the half-line.
-/

noncomputable section

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {q : ℝ}

/-- A real Blaschke denominator has no zero in the disk. -/
theorem hardyRealBlaschkeDen_at_ne_zero (hq : ‖(q : ℂ)‖ < 1)
    {z : ℂ} (hz : ‖z‖ < 1) : (1 : ℂ) - (q : ℂ) * z ≠ 0 := by
  have h := blaschke_denom_ne_zero (a := (q : ℂ)) (z := z)
    (by nlinarith only [hq, hz, norm_nonneg (q : ℂ), norm_nonneg z])
  simpa only [Complex.conj_ofReal] using h

/-- The scalar denominator of the real Blaschke resolvent is nonzero. -/
theorem hardyRealBlaschkeDen_ne_zero (hq : ‖(q : ℂ)‖ < 1) :
    (1 : ℂ) - (q : ℂ) ^ 2 ≠ 0 := by
  simpa only [pow_two] using hardyRealBlaschkeDen_at_ne_zero hq hq

/-- The bounded resolvent `(I-qS)^(-1)`, expressed through the Blaschke isometry. -/
def hardyGeometricResolvent (hq : ‖(q : ℂ)‖ < 1) : HardyDisk →L[ℂ] HardyDisk :=
  ((1 : ℂ) - (q : ℂ) ^ 2)⁻¹ • (1 + (q : ℂ) • blaschkeMul hq)

theorem hardyGeometricResolvent_apply (hq : ‖(q : ℂ)‖ < 1) (x : HardyDisk) :
    hardyGeometricResolvent hq x =
      ((1 : ℂ) - (q : ℂ) ^ 2)⁻¹ • (x + (q : ℂ) • blaschkeMul hq x) := rfl

/-- The resolvent has analytic multiplier `1/(1-qz)`. -/
theorem hardyFun_geometricResolvent (hq : ‖(q : ℂ)‖ < 1)
    (x : HardyDisk) {z : ℂ} (hz : ‖z‖ < 1) :
    hardyFun (hardyGeometricResolvent hq x) z = hardyFun x z / (1 - (q : ℂ) * z) := by
  have hden := hardyRealBlaschkeDen_at_ne_zero hq hz
  rw [hardyGeometricResolvent_apply, hardyFun_smul _ _ hz, hardyFun_add _ _ hz,
    hardyFun_smul _ _ hz]
  have hB : hardyFun (blaschkeMul hq x) z = blaschkeFactor (q : ℂ) z * hardyFun x z := by
    rw [blaschkeMul, hardyFun_hardyMul _ _ hz]
    change (singleBlaschke hq).fn z * hardyFun x z = _
    rw [singleBlaschke_fn]
  rw [hB, blaschkeFactor, Complex.conj_ofReal]
  field_simp [hardyRealBlaschkeDen_ne_zero hq, hden]
  ring

theorem hardyFun_shift_difference (q : ℝ) (x : HardyDisk) {z : ℂ} (hz : ‖z‖ < 1) :
    hardyFun (x - (q : ℂ) • hardyShift x) z =
      (1 - (q : ℂ) * z) * hardyFun x z := by
  rw [sub_eq_add_neg, ← neg_smul, hardyFun_add _ _ hz, hardyFun_smul _ _ hz,
    hardyFun_hardyMul diskShift _ hz]
  change hardyFun x z + (-(q : ℂ)) * (z * hardyFun x z) = _
  ring

/-- Left inverse of the actual shift difference. -/
theorem geometricResolvent_shift_difference (hq : ‖(q : ℂ)‖ < 1) (x : HardyDisk) :
    hardyGeometricResolvent hq (x - (q : ℂ) • hardyShift x) = x := by
  apply hardyDisk_ext fun z hz => ?_
  rw [hardyFun_geometricResolvent hq _ hz, hardyFun_shift_difference q x hz]
  have hden := hardyRealBlaschkeDen_at_ne_zero hq hz
  exact mul_div_cancel_left₀ _ hden

/-- Right inverse of the actual shift difference. -/
theorem shift_difference_geometricResolvent (hq : ‖(q : ℂ)‖ < 1) (x : HardyDisk) :
    hardyGeometricResolvent hq x - (q : ℂ) • hardyShift (hardyGeometricResolvent hq x) = x := by
  apply hardyDisk_ext fun z hz => ?_
  rw [hardyFun_shift_difference q _ hz, hardyFun_geometricResolvent hq _ hz]
  have hden := hardyRealBlaschkeDen_at_ne_zero hq hz
  field_simp [hden]

theorem geometricResolvent_apply_zero (hq : ‖(q : ℂ)‖ < 1) (x : HardyDisk) :
    hardyGeometricResolvent hq x 0 = x 0 := by
  have h := congrArg (fun y : HardyDisk => y 0) (shift_difference_geometricResolvent hq x)
  change hardyGeometricResolvent hq x 0 -
    (q : ℂ) * hardyShift (hardyGeometricResolvent hq x) 0 = x 0 at h
  rwa [hardyShift_apply_zero, mul_zero, sub_zero] at h

theorem geometricResolvent_apply_succ (hq : ‖(q : ℂ)‖ < 1) (x : HardyDisk) (n : ℕ) :
    hardyGeometricResolvent hq x (n + 1) = x (n + 1) + (q : ℂ) * hardyGeometricResolvent hq x n := by
  have h := congrArg (fun y : HardyDisk => y (n + 1)) (shift_difference_geometricResolvent hq x)
  change hardyGeometricResolvent hq x (n + 1) -
    (q : ℂ) * hardyShift (hardyGeometricResolvent hq x) (n + 1) = x (n + 1) at h
  rw [hardyShift_apply_succ] at h
  linear_combination h

/-- The resolvent matrix is the lower triangular geometric matrix. -/
theorem geometricResolvent_single_apply (hq : ‖(q : ℂ)‖ < 1) (m n : ℕ) :
    hardyGeometricResolvent hq (lp.single 2 m (1 : ℂ)) n =
      if m ≤ n then (q : ℂ) ^ (n - m) else 0 := by
  induction n with
  | zero =>
    rw [geometricResolvent_apply_zero]
    by_cases hm : m = 0
    · subst m
      simp [lp.single_apply]
    · simp [lp.single_apply, hm, Ne.symm hm]
  | succ n ih =>
    rw [geometricResolvent_apply_succ, ih]
    by_cases hm : m ≤ n
    · have hne : n + 1 ≠ m := by omega
      rw [if_pos hm, if_pos (by omega : m ≤ n + 1), lp.single_apply_ne _ _ _ hne,
        zero_add, show n + 1 - m = (n - m) + 1 by omega, pow_succ]
      ring
    · by_cases heq : m = n + 1
      · subst m
        simp [lp.single_apply]
      · have hmn : ¬ m ≤ n + 1 := by omega
        rw [if_neg hm, if_neg hmn, lp.single_apply_ne _ _ _ (Ne.symm heq),
          mul_zero, add_zero]

/-- The adjoint resolvent is the upper triangular geometric matrix. -/
theorem geometricResolvent_adjoint_single_apply (hq : ‖(q : ℂ)‖ < 1) (m n : ℕ) :
    ContinuousLinearMap.adjoint (hardyGeometricResolvent hq) (lp.single 2 m (1 : ℂ)) n =
      if n ≤ m then (q : ℂ) ^ (m - n) else 0 := by
  have h := ContinuousLinearMap.adjoint_inner_right (hardyGeometricResolvent hq)
    (lp.single 2 n (1 : ℂ)) (lp.single 2 m (1 : ℂ))
  simp only [lp.inner_single_left, lp.inner_single_right, RCLike.inner_apply,
    map_one, one_mul, mul_one] at h
  rw [geometricResolvent_single_apply] at h
  by_cases hnm : n ≤ m
  · rw [if_pos hnm, map_pow, Complex.conj_ofReal] at h
    rw [if_pos hnm]
    exact h
  · rw [if_neg hnm, map_zero] at h
    rw [if_neg hnm]
    exact h

/-- The geometric KMS operator, including its unit diagonal. -/
def hardyGeometricKMS (hq : ‖(q : ℂ)‖ < 1) : HardyDisk →L[ℂ] HardyDisk :=
  hardyGeometricResolvent hq + ContinuousLinearMap.adjoint (hardyGeometricResolvent hq) - 1

theorem hardyGeometricKMS_isSelfAdjoint (hq : ‖(q : ℂ)‖ < 1) :
    IsSelfAdjoint (hardyGeometricKMS hq) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  change inner ℂ (hardyGeometricResolvent hq x +
      ContinuousLinearMap.adjoint (hardyGeometricResolvent hq) x - x) y =
    inner ℂ x (hardyGeometricResolvent hq y +
      ContinuousLinearMap.adjoint (hardyGeometricResolvent hq) y - y)
  rw [inner_sub_left, inner_add_left, inner_sub_right, inner_add_right,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  ring

/-- The bounded operator has exactly the Kac-Murdock-Szego kernel entries. -/
theorem hardyGeometricKMS_single_apply (hq : ‖(q : ℂ)‖ < 1) (m n : ℕ) :
    hardyGeometricKMS hq (lp.single 2 m (1 : ℂ)) n =
      (q : ℂ) ^ (max n m - min n m) := by
  change hardyGeometricResolvent hq (lp.single 2 m (1 : ℂ)) n +
    ContinuousLinearMap.adjoint (hardyGeometricResolvent hq) (lp.single 2 m (1 : ℂ)) n -
      (lp.single 2 m (1 : ℂ) : HardyDisk) n = _
  rw [geometricResolvent_single_apply, geometricResolvent_adjoint_single_apply]
  rcases lt_trichotomy n m with hnm | rfl | hmn
  · rw [if_neg (not_le.mpr hnm), if_pos hnm.le, zero_add,
      lp.single_apply_ne _ _ _ hnm.ne, sub_zero, max_eq_right hnm.le, min_eq_left hnm.le]
  · simp [lp.single_apply]
  · rw [if_pos hmn.le, if_neg (not_le.mpr hmn), add_zero,
      lp.single_apply_ne _ _ _ hmn.ne', sub_zero, max_eq_left hmn.le, min_eq_right hmn.le]

end GaloisForLFunctions.HTGeometry

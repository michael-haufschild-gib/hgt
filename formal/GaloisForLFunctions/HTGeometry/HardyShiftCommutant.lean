import GaloisForLFunctions.HTGeometry.HardyDiskKernelContinuity
import GaloisForLFunctions.HTGeometry.HardyDiskCyclic

/-!
# Commutant theorem for the scalar Hardy shift

Every bounded operator on coefficient `H²(𝔻)` commuting with the unilateral shift is
multiplication by one bounded analytic function.  The multiplier bound is the operator norm.
This is the operator-theoretic factorization interface used by scalar Beurling theory.
-/

open Complex Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem shiftCommutant_apply_shift_pow
    (T : HardyDisk →L[ℂ] HardyDisk)
    (hT : ∀ x, T (hardyMul diskShift x) = hardyMul diskShift (T x))
    (n : ℕ) (x : HardyDisk) :
    T (((hardyMul diskShift) ^ n) x) =
      ((hardyMul diskShift) ^ n) (T x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change T (hardyMul diskShift (((hardyMul diskShift) ^ n) x)) = _
      rw [hT, ih]
      rfl

/-- Pointwise multiplication formula forced by commutation with the unilateral shift. -/
theorem hardyFun_shiftCommutant
    (T : HardyDisk →L[ℂ] HardyDisk)
    (hT : ∀ x, T (hardyMul diskShift x) = hardyMul diskShift (T x))
    (x : HardyDisk) {z : ℂ} (hz : ‖z‖ < 1) :
    hardyFun (T x) z = hardyFun (T hardyOne) z * hardyFun x z := by
  have hsum : HasSum (fun n : ℕ =>
      (lp.single 2 n (x n) : HardyDisk)) x :=
    lp.hasSum_single (by norm_num) x
  have hTsum := hsum.map T T.continuous
  have hevalSum := hTsum.map
    (innerSL ℂ (hardyKernel hz)) (innerSL ℂ (hardyKernel hz)).continuous
  have hterm (n : ℕ) :
      inner ℂ (hardyKernel hz) (T (lp.single 2 n (x n) : HardyDisk)) =
        x n * z ^ n * hardyFun (T hardyOne) z := by
    have hsingle : (lp.single 2 n (x n) : HardyDisk) =
        (x n) • (((hardyMul diskShift) ^ n) hardyOne) := by
      rw [shift_pow_hardyOne]
      apply lp.ext
      funext m
      by_cases hmn : m = n
      · subst m
        simp [lp.single_apply]
      · simp [lp.single_apply, hmn]
    rw [hsingle, map_smul, shiftCommutant_apply_shift_pow T hT,
      inner_hardyKernel, hardyFun_smul _ _ hz, hardyFun_shift_pow _ _ hz]
    ring
  have heval :
      inner ℂ (hardyKernel hz) (T x) =
        hardyFun (T hardyOne) z * hardyFun x z := by
    have hs : HasSum (fun n : ℕ =>
        x n * z ^ n * hardyFun (T hardyOne) z)
        (inner ℂ (hardyKernel hz) (T x)) := by
      exact hevalSum.congr_fun fun n => (hterm n).symm
    have hxsum : HasSum (fun n : ℕ => x n * z ^ n) (hardyFun x z) := by
      exact (summable_hardyDisk_terms x hz).hasSum
    have hmul := hxsum.mul_left (hardyFun (T hardyOne) z)
    have hmul' : HasSum (fun n : ℕ =>
        x n * z ^ n * hardyFun (T hardyOne) z)
        (hardyFun (T hardyOne) z * hardyFun x z) := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul
    exact hs.unique hmul'
  rw [inner_hardyKernel] at heval
  exact heval

private theorem norm_hardyFun_shiftCommutant_one_le
    (T : HardyDisk →L[ℂ] HardyDisk)
    (hT : ∀ x, T (hardyMul diskShift x) = hardyMul diskShift (T x))
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖hardyFun (T hardyOne) z‖ ≤ ‖T‖ := by
  let k : HardyDisk := hardyKernel hz
  have hpoint := hardyFun_shiftCommutant T hT k hz
  have hself : hardyFun k z = ((‖k‖ : ℂ) ^ (2 : ℕ)) := by
    calc
      hardyFun k z = inner ℂ (hardyKernel hz) k :=
        (inner_hardyKernel hz k).symm
      _ = inner ℂ k k := by rfl
      _ = ((‖k‖ : ℂ) ^ (2 : ℕ)) := inner_self_eq_norm_sq_to_K k
  have hkpos : 0 < ‖k‖ := norm_pos_iff.mpr (hardyKernel_ne_zero hz)
  have hevalBound : ‖hardyFun (T k) z‖ ≤ ‖k‖ * ‖T k‖ := by
    rw [← inner_hardyKernel hz (T k)]
    exact norm_inner_le_norm _ _
  have hTbound : ‖T k‖ ≤ ‖T‖ * ‖k‖ := T.le_opNorm k
  have hmul : ‖hardyFun (T hardyOne) z‖ * ‖k‖ ^ (2 : ℕ) ≤
      ‖T‖ * ‖k‖ ^ (2 : ℕ) := by
    calc
      ‖hardyFun (T hardyOne) z‖ * ‖k‖ ^ (2 : ℕ) =
          ‖hardyFun (T k) z‖ := by
        rw [hpoint, hself, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg k)]
      _ ≤ ‖k‖ * ‖T k‖ := hevalBound
      _ ≤ ‖k‖ * (‖T‖ * ‖k‖) :=
        mul_le_mul_of_nonneg_left hTbound (norm_nonneg _)
      _ = ‖T‖ * ‖k‖ ^ (2 : ℕ) := by ring
  exact le_of_mul_le_mul_right hmul (sq_pos_of_pos hkpos)

/-- Bounded analytic symbol of an operator in the unilateral-shift commutant. -/
def diskMultiplierOfShiftCommutant
    (T : HardyDisk →L[ℂ] HardyDisk)
    (hT : ∀ x, T (hardyMul diskShift x) = hardyMul diskShift (T x)) :
    DiskMultiplier where
  fn := hardyFun (T hardyOne)
  diff := differentiableOn_hardyFun (T hardyOne)
  bd := ‖T‖
  bd_nonneg := norm_nonneg T
  bd_le := fun z hz => norm_hardyFun_shiftCommutant_one_le T hT
    (by simpa [mem_ball, dist_zero_right] using hz)

theorem diskMultiplierOfShiftCommutant_fn
    (T : HardyDisk →L[ℂ] HardyDisk)
    (hT : ∀ x, T (hardyMul diskShift x) = hardyMul diskShift (T x)) :
    (diskMultiplierOfShiftCommutant T hT).fn = hardyFun (T hardyOne) := rfl

/-- Scalar Hardy commutant theorem, as an equality of bounded operators. -/
theorem hardyMul_diskMultiplierOfShiftCommutant
    (T : HardyDisk →L[ℂ] HardyDisk)
    (hT : ∀ x, T (hardyMul diskShift x) = hardyMul diskShift (T x)) :
    hardyMul (diskMultiplierOfShiftCommutant T hT) = T := by
  apply ContinuousLinearMap.ext
  intro x
  apply hardyDisk_ext
  intro z hz
  rw [hardyFun_hardyMul _ x hz, diskMultiplierOfShiftCommutant_fn,
    hardyFun_shiftCommutant T hT x hz]

end

end GaloisForLFunctions.HTGeometry

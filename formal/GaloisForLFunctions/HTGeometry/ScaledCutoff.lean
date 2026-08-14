import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# The scaled unit cutoff

A fixed smooth cutoff equal to one on `[-1,1]` and supported in `(-2,2)` gives, after the scaling
`x ↦ x/ε`, a family whose `n`-th derivative is `O(ε^{-n})` and which is one on `[-ε,ε]` and
supported in `(-2ε,2ε)`.  This is the localisation device of every local structure theorem at a
point.
-/

open Set Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A fixed cutoff: one on the unit ball, supported in the ball of radius two. -/
def unitCutoff : ContDiffBump (0:ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

theorem contDiff_unitCutoff : ContDiff ℝ (⊤ : ℕ∞) (unitCutoff : ℝ → ℝ) :=
  unitCutoff.contDiff

theorem hasCompactSupport_unitCutoff : HasCompactSupport (unitCutoff : ℝ → ℝ) :=
  unitCutoff.hasCompactSupport

theorem hasCompactSupport_iteratedDeriv {f : ℝ → ℝ} (hf : HasCompactSupport f) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n f) := by
  induction n with
  | zero => simpa [iteratedDeriv_zero] using hf
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv

theorem exists_bound_iteratedDeriv_unitCutoff (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |iteratedDeriv n (unitCutoff : ℝ → ℝ) x| ≤ C := by
  have hcont : Continuous (iteratedDeriv n (unitCutoff : ℝ → ℝ)) :=
    ContDiff.continuous_iteratedDeriv n contDiff_unitCutoff (by exact_mod_cast le_top)
  have hsupp : HasCompactSupport (iteratedDeriv n (unitCutoff : ℝ → ℝ)) :=
    hasCompactSupport_iteratedDeriv hasCompactSupport_unitCutoff n
  obtain ⟨C, hC⟩ := hsupp.exists_bound_of_continuous hcont
  refine ⟨|C| , abs_nonneg C, fun x => ?_⟩
  have := hC x
  rw [Real.norm_eq_abs] at this
  exact le_trans this (le_abs_self C)

/-- A uniform bound for the `n`-th derivative of the unit cutoff. -/
def cutoffConst (n : ℕ) : ℝ := (exists_bound_iteratedDeriv_unitCutoff n).choose

theorem cutoffConst_nonneg (n : ℕ) : 0 ≤ cutoffConst n :=
  (exists_bound_iteratedDeriv_unitCutoff n).choose_spec.1

theorem abs_iteratedDeriv_unitCutoff_le (n : ℕ) (x : ℝ) :
    |iteratedDeriv n (unitCutoff : ℝ → ℝ) x| ≤ cutoffConst n :=
  (exists_bound_iteratedDeriv_unitCutoff n).choose_spec.2 x

/-- The cutoff at scale `ε`. -/
def cutoffScaled (ε x : ℝ) : ℝ := (unitCutoff : ℝ → ℝ) (ε⁻¹ * x)

theorem contDiff_cutoffScaled (ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (cutoffScaled ε) :=
  contDiff_unitCutoff.comp (contDiff_const.mul contDiff_id)

theorem cutoffScaled_eq_one {ε x : ℝ} (hε : 0 < ε) (hx : |x| ≤ ε) : cutoffScaled ε x = 1 := by
  refine unitCutoff.one_of_mem_closedBall ?_
  rw [mem_closedBall, Real.dist_eq, sub_zero]
  show |ε⁻¹ * x| ≤ unitCutoff.rIn
  rw [abs_mul, abs_of_pos (inv_pos.mpr hε)]
  have : ε⁻¹ * |x| ≤ ε⁻¹ * ε := by
    exact mul_le_mul_of_nonneg_left hx (le_of_lt (inv_pos.mpr hε))
  rw [inv_mul_cancel₀ (ne_of_gt hε)] at this
  exact this

theorem cutoffScaled_eq_zero {ε x : ℝ} (hε : 0 < ε) (hx : 2 * ε ≤ |x|) : cutoffScaled ε x = 0 := by
  have hnot : (ε⁻¹ * x) ∉ Function.support (unitCutoff : ℝ → ℝ) := by
    rw [unitCutoff.support_eq]
    intro hmem
    rw [mem_ball, Real.dist_eq, sub_zero] at hmem
    have hlt : |ε⁻¹ * x| < unitCutoff.rOut := hmem
    have hval : |ε⁻¹ * x| = ε⁻¹ * |x| := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hε)]
    rw [hval] at hlt
    have h2 : (2:ℝ) ≤ ε⁻¹ * |x| := by
      have hmul := mul_le_mul_of_nonneg_left hx (le_of_lt (inv_pos.mpr hε))
      have heq : ε⁻¹ * (2 * ε) = 2 := by field_simp
      rw [heq] at hmul
      exact hmul
    have hrout : unitCutoff.rOut = 2 := rfl
    rw [hrout] at hlt
    linarith
  simpa [cutoffScaled] using Function.notMem_support.mp hnot

theorem iteratedDeriv_cutoffScaled (n : ℕ) (ε : ℝ) (x : ℝ) :
    iteratedDeriv n (cutoffScaled ε) x
      = (ε⁻¹) ^ n * iteratedDeriv n (unitCutoff : ℝ → ℝ) (ε⁻¹ * x) := by
  have h := iteratedDeriv_comp_const_mul
    (f := (unitCutoff : ℝ → ℝ)) (n := n) (contDiff_unitCutoff.of_le (by exact_mod_cast le_top)) (ε⁻¹)
  have hfun : cutoffScaled ε = fun y : ℝ => (unitCutoff : ℝ → ℝ) (ε⁻¹ * y) := rfl
  rw [hfun, h]

theorem abs_iteratedDeriv_cutoffScaled_le (n : ℕ) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    |iteratedDeriv n (cutoffScaled ε) x| ≤ cutoffConst n * (ε⁻¹) ^ n := by
  rw [iteratedDeriv_cutoffScaled n ε, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (ε⁻¹) ^ n)]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_iteratedDeriv_unitCutoff_le n _) (by positivity)

end

end GaloisForLFunctions.HTGeometry

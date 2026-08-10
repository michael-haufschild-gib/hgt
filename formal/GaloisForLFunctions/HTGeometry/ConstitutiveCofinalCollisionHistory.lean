import GaloisForLFunctions.HTGeometry.ConstitutivePositiveOverlapDefect
import Mathlib.Analysis.PSeries

open scoped BigOperators
open Filter

namespace HTGeometry

noncomputable section

/-!
# Cofinal collision depth and nonintegrable history

The probability weights `1 / ((n+1)(n+2))` have unit total mass but infinite first moment.  They
therefore realize a normalized observer-defect chain whose unweighted budget closes while its
depth-weighted history diverges.
-/

/-- Zero-based collision weights: index `n` represents collision depth `n + 1`. -/
def cofinalCollisionWeight (n : ℕ) : ℝ :=
  1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))

theorem cofinalCollisionWeight_eq_telescoping (n : ℕ) :
    cofinalCollisionWeight n =
      1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2) := by
  have h₁ : (n : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  have h₂ : (n : ℝ) + 2 ≠ 0 := ne_of_gt (by positivity)
  rw [cofinalCollisionWeight]
  field_simp
  ring

theorem cofinalCollisionWeight_pos (n : ℕ) :
    0 < cofinalCollisionWeight n := by
  rw [cofinalCollisionWeight]
  positivity

/-- Capacity accumulated through the first `N` collision levels. -/
def cofinalCollisionCapacity (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, cofinalCollisionWeight n

theorem cofinalCollisionCapacity_eq (N : ℕ) :
    cofinalCollisionCapacity N = 1 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => simp [cofinalCollisionCapacity]
  | succ N ih =>
      rw [cofinalCollisionCapacity, Finset.sum_range_succ]
      rw [show (∑ n ∈ Finset.range N, cofinalCollisionWeight n) =
        cofinalCollisionCapacity N from rfl, ih,
        cofinalCollisionWeight_eq_telescoping]
      push_cast
      ring

theorem cofinalCollisionCapacity_strictMono :
    StrictMono cofinalCollisionCapacity := by
  intro m n hmn
  rw [cofinalCollisionCapacity_eq, cofinalCollisionCapacity_eq]
  apply sub_lt_sub_left
  exact one_div_lt_one_div_of_lt (by positivity)
    (by exact_mod_cast (Nat.add_lt_add_right hmn 1))

theorem cofinalCollisionCapacity_tendsto_one :
    Tendsto cofinalCollisionCapacity atTop (nhds 1) := by
  have hzero :
      Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim :
      Tendsto (fun N : ℕ => (1 : ℝ) - 1 / ((N : ℝ) + 1)) atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hzero
  have hfun : cofinalCollisionCapacity =
      fun N : ℕ => 1 - 1 / ((N : ℝ) + 1) := by
    funext N
    exact cofinalCollisionCapacity_eq N
  rw [hfun]
  simpa using hlim

/-- The remaining observed distinguishability after `N` collision levels. -/
def cofinalCollisionTail (N : ℕ) : ℝ :=
  1 - cofinalCollisionCapacity N

theorem cofinalCollisionTail_eq (N : ℕ) :
    cofinalCollisionTail N = 1 / ((N : ℝ) + 1) := by
  rw [cofinalCollisionTail, cofinalCollisionCapacity_eq]
  ring

theorem cofinalCollisionTail_tendsto_zero :
    Tendsto cofinalCollisionTail atTop (nhds 0) := by
  have hfun : cofinalCollisionTail =
      fun N : ℕ => 1 / ((N : ℝ) + 1) := by
    funext N
    exact cofinalCollisionTail_eq N
  rw [hfun]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- Weighting a collision by its one-based depth leaves the shifted harmonic sequence. -/
theorem cofinalCollision_depth_mul_weight (n : ℕ) :
    ((n : ℝ) + 1) * cofinalCollisionWeight n = 1 / ((n : ℝ) + 2) := by
  have h₁ : (n : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  have h₂ : (n : ℝ) + 2 ≠ 0 := ne_of_gt (by positivity)
  rw [cofinalCollisionWeight]
  field_simp

/-- The collision-depth first moment is not summable. -/
theorem not_summable_cofinalCollision_depth_weight :
    ¬ Summable (fun n : ℕ => ((n : ℝ) + 1) * cofinalCollisionWeight n) := by
  simp_rw [cofinalCollision_depth_mul_weight]
  intro hs
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 2).mp
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hs

/-- Depth-weighted partial history tends to `+∞`. -/
theorem cofinalCollision_depth_history_tendsto_atTop :
    Tendsto
      (fun N => ∑ n ∈ Finset.range N,
        ((n : ℝ) + 1) * cofinalCollisionWeight n)
      atTop atTop := by
  apply (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n =>
    mul_nonneg (by positivity) (le_of_lt (cofinalCollisionWeight_pos n)))).mp
  exact not_summable_cofinalCollision_depth_weight

/-- Bounded total defect and divergent depth-weighted history coexist in one exact law. -/
theorem cofinalCollision_bounded_budget_infinite_history :
    (∀ N, cofinalCollisionCapacity N < 1) ∧
      Tendsto cofinalCollisionCapacity atTop (nhds 1) ∧
      Tendsto cofinalCollisionTail atTop (nhds 0) ∧
      Tendsto
        (fun N => ∑ n ∈ Finset.range N,
          ((n : ℝ) + 1) * cofinalCollisionWeight n)
        atTop atTop := by
  refine ⟨?_, cofinalCollisionCapacity_tendsto_one,
    cofinalCollisionTail_tendsto_zero, cofinalCollision_depth_history_tendsto_atTop⟩
  intro N
  rw [cofinalCollisionCapacity_eq]
  exact sub_lt_self 1 (by positivity)

end

end HTGeometry

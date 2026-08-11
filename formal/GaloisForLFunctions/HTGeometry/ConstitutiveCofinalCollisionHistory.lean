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

/-- The collision weights form a probability law: total mass one. -/
theorem hasSum_cofinalCollisionWeight : HasSum cofinalCollisionWeight 1 := by
  have hnn : ∀ n, 0 ≤ cofinalCollisionWeight n := fun n => (cofinalCollisionWeight_pos n).le
  have hbound : ∀ n, (∑ i ∈ Finset.range n, cofinalCollisionWeight i) ≤ 1 := by
    intro n
    rw [show (∑ i ∈ Finset.range n, cofinalCollisionWeight i) =
      cofinalCollisionCapacity n from rfl, cofinalCollisionCapacity_eq]
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hsummable : Summable cofinalCollisionWeight :=
    summable_of_sum_range_le hnn hbound
  exact (hsummable.hasSum_iff_tendsto_nat).mpr cofinalCollisionCapacity_tendsto_one

/-! ## Explicit countable source profiles and their unique simultaneously maximal coupling -/

/-- Collision carrier: a depth together with a binary source label. -/
abbrev CollisionState := ℕ × Bool

/-- Left source profile: all mass on the `false` label. -/
def cofinalCollisionLeft (x : CollisionState) : ℝ :=
  if x.2 = false then cofinalCollisionWeight x.1 else 0

/-- Right source profile: all mass on the `true` label. -/
def cofinalCollisionRight (x : CollisionState) : ℝ :=
  if x.2 = true then cofinalCollisionWeight x.1 else 0

theorem cofinalCollisionLeft_nonneg (x : CollisionState) : 0 ≤ cofinalCollisionLeft x := by
  rw [cofinalCollisionLeft]
  split
  · exact (cofinalCollisionWeight_pos x.1).le
  · exact le_rfl

theorem cofinalCollisionRight_nonneg (x : CollisionState) : 0 ≤ cofinalCollisionRight x := by
  rw [cofinalCollisionRight]
  split
  · exact (cofinalCollisionWeight_pos x.1).le
  · exact le_rfl

/-- The diagonal coupling that merges each depth pair. -/
def cofinalCollisionCoupling (x y : CollisionState) : ℝ :=
  if x.2 = false ∧ y.2 = true ∧ x.1 = y.1 then cofinalCollisionWeight x.1 else 0

theorem cofinalCollisionCoupling_nonneg (x y : CollisionState) :
    0 ≤ cofinalCollisionCoupling x y := by
  rw [cofinalCollisionCoupling]
  split
  · exact (cofinalCollisionWeight_pos x.1).le
  · exact le_rfl

theorem cofinalCollisionCoupling_row (x : CollisionState) :
    HasSum (fun y => cofinalCollisionCoupling x y) (cofinalCollisionLeft x) := by
  classical
  by_cases hx : x.2 = false
  · have hfun : (fun y : CollisionState => cofinalCollisionCoupling x y)
        = fun y => if y = (x.1, true) then cofinalCollisionWeight x.1 else 0 := by
      funext y
      rcases y with ⟨j, b⟩
      by_cases hb : b = true
      · by_cases hj : x.1 = j
        · simp [cofinalCollisionCoupling, hx, hb, hj]
        · simp [cofinalCollisionCoupling, hx, hb, hj, Prod.ext_iff, Ne.symm hj]
      · simp [cofinalCollisionCoupling, hx, hb, Prod.ext_iff]
    rw [hfun, cofinalCollisionLeft, if_pos hx]
    simpa using hasSum_ite_eq (x.1, true) (cofinalCollisionWeight x.1)
  · have hfun : (fun y : CollisionState => cofinalCollisionCoupling x y) = fun _ => 0 := by
      funext y
      simp [cofinalCollisionCoupling, hx]
    rw [hfun, cofinalCollisionLeft, if_neg hx]
    exact hasSum_zero

theorem cofinalCollisionCoupling_agreement (n : ℕ) :
    (∑ j ∈ Finset.range n, cofinalCollisionCoupling (j, false) (j, true))
      = cofinalCollisionCapacity n := by
  rw [cofinalCollisionCapacity]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [cofinalCollisionCoupling]

/-- **Unique simultaneously maximal coupling.**  A nonnegative coupling of the two source profiles
that attains the exact agreement capacity at every finite observer level is the diagonal coupling. -/
theorem cofinalCollisionCoupling_unique
    (γ : CollisionState → CollisionState → ℝ)
    (hnonneg : ∀ x y, 0 ≤ γ x y)
    (hrow : ∀ x, HasSum (fun y => γ x y) (cofinalCollisionLeft x))
    (hagree : ∀ n : ℕ,
      (∑ j ∈ Finset.range n, γ (j, false) (j, true)) = cofinalCollisionCapacity n) :
    ∀ x y : CollisionState, γ x y = cofinalCollisionCoupling x y := by
  classical
  have hdiag : ∀ j : ℕ, γ (j, false) (j, true) = cofinalCollisionWeight j := by
    intro j
    have h1 := hagree (j + 1)
    have h2 := hagree j
    rw [Finset.sum_range_succ, h2, cofinalCollisionCapacity, cofinalCollisionCapacity,
      Finset.sum_range_succ] at h1
    linarith
  intro x y
  rcases x with ⟨j, b⟩
  cases b with
  | false =>
      have hval : cofinalCollisionLeft (j, false) = cofinalCollisionWeight j := by
        simp [cofinalCollisionLeft]
      have hrowx : HasSum (fun y => γ (j, false) y) (cofinalCollisionWeight j) := by
        rw [← hval]; exact hrow (j, false)
      have hsingle : HasSum (fun z : CollisionState =>
          if z = (j, true) then cofinalCollisionWeight j else 0) (cofinalCollisionWeight j) := by
        simpa using hasSum_ite_eq (j, true) (cofinalCollisionWeight j)
      have hle : ∀ z : CollisionState,
          (if z = (j, true) then cofinalCollisionWeight j else 0) ≤ γ (j, false) z := by
        intro z
        by_cases hz : z = (j, true)
        · subst z
          rw [if_pos rfl, hdiag j]
        · rw [if_neg hz]
          exact hnonneg _ _
      have hg : HasSum (fun z : CollisionState =>
          γ (j, false) z - (if z = (j, true) then cofinalCollisionWeight j else 0)) 0 := by
        simpa using hrowx.sub hsingle
      have hnn : ∀ z : CollisionState,
          0 ≤ γ (j, false) z - (if z = (j, true) then cofinalCollisionWeight j else 0) :=
        fun z => sub_nonneg.mpr (hle z)
      have hfun := (hasSum_zero_iff_of_nonneg hnn).mp hg
      have hz := congrFun hfun y
      simp only [Pi.zero_apply, sub_eq_zero] at hz
      rw [hz]
      rcases y with ⟨k, c⟩
      by_cases hc : c = true
      · by_cases hjk : j = k
        · simp [cofinalCollisionCoupling, hc, hjk]
        · simp [cofinalCollisionCoupling, hc, hjk, Prod.ext_iff, Ne.symm hjk]
      · simp [cofinalCollisionCoupling, hc, Prod.ext_iff]
  | true =>
      have hval : cofinalCollisionLeft (j, true) = 0 := by
        simp [cofinalCollisionLeft]
      have hrowx : HasSum (fun y => γ (j, true) y) 0 := by
        rw [← hval]; exact hrow (j, true)
      have hfun := (hasSum_zero_iff_of_nonneg (fun z => hnonneg (j, true) z)).mp hrowx
      have hz := congrFun hfun y
      simp only [Pi.zero_apply] at hz
      rw [hz]
      simp [cofinalCollisionCoupling]

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

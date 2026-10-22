import GaloisForLFunctions.BezoutValuationIncidence.ArithmeticDampingCenteredOperator

/-!
# The centered arithmetic operators form a semigroup

Finite transition composition leaves only a coordinate-constant discrepancy after
centering. Both outputs vanish at infinity, so that discrepancy is zero. This avoids
interchanging two infinite sums and keeps the positive-state convention explicit.
-/

open Finset Filter Topology RHTower
open scoped ZeroAtInfty

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The entrance functional on sequences vanishing at infinity. -/
def arithmeticDampingEntrancePair (η : ℝ) (b : C₀(ℕ, ℝ)) : ℝ :=
  ∑' k, arithmeticDampingEntrance η (k + 1) * b k

/-- Positive states are indexed by their predecessor. Each row action is finite. -/
def arithmeticDampingFiniteAction (η : ℝ) (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range (n + 1), arithmeticDampingTransition η (n + 1) (k + 1) * b k

private theorem acs_entrance_summable {η : ℝ} (hη : 0 < η) (b : C₀(ℕ, ℝ)) :
    Summable (fun k => arithmeticDampingEntrance η (k + 1) * b k) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    ((hasSum_arithmeticDampingEntrance hη).summable.mul_right ‖b‖)
  rw [norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (arithmeticDampingEntrance_nonneg hη _)]
  exact mul_le_mul_of_nonneg_left (b.toBCF.norm_coe_le_norm k)
    (arithmeticDampingEntrance_nonneg hη _)

private theorem acs_row_hasSum (η : ℝ) (b : ℕ → ℝ) (n : ℕ) :
    HasSum (fun k => arithmeticDampingTransition η (n + 1) (k + 1) * b k)
      (arithmeticDampingFiniteAction η b n) := by
  apply hasSum_sum_of_ne_finset_zero
  intro k hk
  rw [arithmeticDampingTransition_eq_zero_of_lt η (by
    simp only [mem_range] at hk
    omega), zero_mul]

/-- The infinite centered row pairing equals finite transition minus entrance mean. -/
theorem arithmeticDampingCenteredOperator_eq_finiteAction {η : ℝ} (hη : 0 < η)
    (b : C₀(ℕ, ℝ)) (n : ℕ) :
    arithmeticDampingCenteredOperator hη b n =
      arithmeticDampingFiniteAction η b n - arithmeticDampingEntrancePair η b := by
  rw [arithmeticDampingCenteredOperator_apply]
  simp_rw [arithmeticDampingCenteredRow, sub_mul]
  rw [(acs_row_hasSum η b n).summable.tsum_sub (acs_entrance_summable hη b),
    (acs_row_hasSum η b n).tsum_eq]
  rfl

private theorem acs_shifted_mass (η : ℝ) (n : ℕ) :
    (∑ k ∈ range (n + 1), arithmeticDampingTransition η (n + 1) (k + 1)) = 1 := by
  simpa only [sum_Icc_eq_sum_range_shift] using
    arithmeticDampingTransition_sum η (Nat.succ_pos n)

theorem arithmeticDampingFiniteAction_sub_const (η : ℝ) (b : ℕ → ℝ) (c : ℝ) (n : ℕ) :
    arithmeticDampingFiniteAction η (fun k => b k - c) n =
      arithmeticDampingFiniteAction η b n - c := by
  unfold arithmeticDampingFiniteAction
  simp_rw [mul_sub]
  rw [sum_sub_distrib, ← sum_mul, acs_shifted_mass, one_mul]

private theorem acs_action_extend (η : ℝ) (b : ℕ → ℝ) {j n : ℕ} (hjn : j ≤ n) :
    arithmeticDampingFiniteAction η b j =
      ∑ k ∈ range (n + 1), arithmeticDampingTransition η (j + 1) (k + 1) * b k := by
  unfold arithmeticDampingFiniteAction
  apply sum_subset (range_mono (Nat.add_le_add_right hjn 1))
  intro k _ hk
  rw [arithmeticDampingTransition_eq_zero_of_lt η (by
    simp only [mem_range] at hk
    omega), zero_mul]

/-- Finite raw action composes without any condition on the input sequence. -/
theorem arithmeticDampingFiniteAction_semigroup (s t : ℝ) (b : ℕ → ℝ) (n : ℕ) :
    arithmeticDampingFiniteAction s (arithmeticDampingFiniteAction t b) n =
      arithmeticDampingFiniteAction (s + t) b n := by
  change (∑ j ∈ range (n + 1), arithmeticDampingTransition s (n + 1) (j + 1) *
    arithmeticDampingFiniteAction t b j) = _
  calc
    _ = ∑ j ∈ range (n + 1), arithmeticDampingTransition s (n + 1) (j + 1) *
        (∑ k ∈ range (n + 1),
          arithmeticDampingTransition t (j + 1) (k + 1) * b k) := by
      apply sum_congr rfl
      intro j hj
      rw [acs_action_extend t b (n := n) (by have := mem_range.mp hj; omega)]
    _ = ∑ k ∈ range (n + 1),
        (∑ j ∈ range (n + 1), arithmeticDampingTransition s (n + 1) (j + 1) *
          arithmeticDampingTransition t (j + 1) (k + 1)) * b k := by
      simp only [mul_sum, sum_mul, mul_assoc]
      rw [sum_comm]
    _ = _ := by
      unfold arithmeticDampingFiniteAction
      apply sum_congr rfl
      intro k _
      have h := arithmeticDampingTransition_semigroup s t (n + 1) (k + 1)
      rw [sum_Icc_eq_sum_range_shift] at h
      rw [h]

private theorem acs_tendsto_zero (b : C₀(ℕ, ℝ)) :
    Tendsto (fun n => b n) atTop (𝓝 0) := by
  have h := b.zero_at_infty'
  rwa [cocompact_eq_cofinite, Nat.cofinite_eq_atTop] at h

private theorem acs_composition_difference {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (b : C₀(ℕ, ℝ)) (n : ℕ) :
    arithmeticDampingCenteredOperator hs (arithmeticDampingCenteredOperator ht b) n -
        arithmeticDampingCenteredOperator (add_pos hs ht) b n =
      arithmeticDampingEntrancePair (s + t) b - arithmeticDampingEntrancePair t b -
        arithmeticDampingEntrancePair s (arithmeticDampingCenteredOperator ht b) := by
  have ha :
      arithmeticDampingFiniteAction s (arithmeticDampingCenteredOperator ht b) n =
        arithmeticDampingFiniteAction (s + t) b n - arithmeticDampingEntrancePair t b := by
    calc
      _ = arithmeticDampingFiniteAction s
          (fun j => arithmeticDampingFiniteAction t b j - arithmeticDampingEntrancePair t b) n := by
        congr 1
        funext j
        exact arithmeticDampingCenteredOperator_eq_finiteAction ht b j
      _ = _ := by
        rw [arithmeticDampingFiniteAction_sub_const, arithmeticDampingFiniteAction_semigroup]
  rw [arithmeticDampingCenteredOperator_eq_finiteAction hs,
    arithmeticDampingCenteredOperator_eq_finiteAction (add_pos hs ht), ha]
  ring

/-- Centering is consistent with finite transition composition on the actual c₀ space. -/
theorem arithmeticDampingEntrancePair_composition {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (b : C₀(ℕ, ℝ)) :
    arithmeticDampingEntrancePair s (arithmeticDampingCenteredOperator ht b) =
      arithmeticDampingEntrancePair (s + t) b - arithmeticDampingEntrancePair t b := by
  have hz := (acs_tendsto_zero
    (arithmeticDampingCenteredOperator hs (arithmeticDampingCenteredOperator ht b))).sub
    (acs_tendsto_zero (arithmeticDampingCenteredOperator (add_pos hs ht) b))
  simp only [sub_zero] at hz
  have hc := hz.congr (acs_composition_difference hs ht b)
  have he := tendsto_nhds_unique hc tendsto_const_nhds
  linarith

/-- The bounded centered operators form the exact positive-time arithmetic semigroup. -/
theorem arithmeticDampingCenteredOperator_semigroup {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (arithmeticDampingCenteredOperator hs).comp (arithmeticDampingCenteredOperator ht) =
      arithmeticDampingCenteredOperator (add_pos hs ht) := by
  apply ContinuousLinearMap.ext
  intro b
  apply ZeroAtInftyContinuousMap.ext
  intro n
  change arithmeticDampingCenteredOperator hs (arithmeticDampingCenteredOperator ht b) n = _
  have h := acs_composition_difference hs ht b n
  rw [arithmeticDampingEntrancePair_composition hs ht b] at h
  exact sub_eq_zero.mp (by simpa only [sub_self] using h)

end
end GaloisForLFunctions.BezoutValuationIncidence

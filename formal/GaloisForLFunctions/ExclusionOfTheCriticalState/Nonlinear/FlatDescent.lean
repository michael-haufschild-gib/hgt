import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatConvexRigidity

/-!
# Flat descent converges to the negative part

Subtracting the flat gradient gives a monotone nonexpansive map. Its
iterates retain exactly the nonpositive part of the initial value. A
finite telescoping identity and a reciprocal bound on the residual
prove convergence without imposing a positive curvature lower bound.
-/

open Filter Topology
open scoped BigOperators
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
noncomputable section

/-- Unit gradient descent for the flat potential. -/
def descent (t : ℝ) : ℝ := t - gradient t

@[simp] theorem descent_zero : descent 0 = 0 := by simp only [descent, gradient_zero, sub_zero]

/-- Exactly the flat half-line consists of fixed points. -/
theorem descent_fixed_iff (t : ℝ) : descent t = t ↔ t ≤ 0 := by
  rw [descent]
  constructor
  · intro h
    apply (gradient_zero_iff t).mp
    linarith only [h]
  · intro h
    rw [(gradient_zero_iff t).mpr h, sub_zero]

theorem descent_monotone : Monotone descent := by
  have hd (t : ℝ) : HasDerivAt descent (1 - expNegInvGlue t) t :=
    (hasDerivAt_id t).fun_sub (gradient_hasDerivAt t)
  apply monotone_of_deriv_nonneg (fun t => (hd t).differentiableAt)
  intro t
  rw [(hd t).deriv]
  exact sub_nonneg.mpr (curvature_bounds t).2

theorem descent_le (t : ℝ) : descent t ≤ t := sub_le_self _ (gradient_nonneg t)

/-- Descent is nonexpansive even though no strictly positive curvature bound is available. -/
theorem descent_contraction : LipschitzWith 1 descent := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  have h := complementary_jump_bound x y
  change (gradient x - gradient y) ^ 2 + (descent x - descent y) ^ 2 ≤ (x - y) ^ 2 at h
  nlinarith only [h, sq_nonneg (gradient x - gradient y),
    sq_abs (descent x - descent y), sq_abs (x - y),
    abs_nonneg (descent x - descent y), abs_nonneg (x - y)]

/-- Every iterate remains between the initial value and its nonpositive part. -/
theorem descent_iterate_bounds (x : ℝ) (n : ℕ) :
    min x 0 ≤ descent^[n] x ∧ descent^[n] x ≤ x := by
  induction n with
  | zero => exact ⟨min_le_left _ _, le_rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hfix := (descent_fixed_iff (min x 0)).mpr (min_le_right _ _)
    exact ⟨by simpa only [hfix] using descent_monotone ih.1,
      (descent_le _).trans ih.2⟩

/-- The entire finite residual sum is the actual decrease, with no truncation error. -/
theorem descent_residual_sum (x : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, gradient (descent^[i] x) = x - descent^[n] x := by
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, Function.iterate_zero_apply, sub_self]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Function.iterate_succ_apply', descent]
    ring

private theorem descent_residual_budget (x : ℝ) (n : ℕ) :
    (n : ℝ) * gradient (descent^[n] x) ≤ x - descent^[n] x := by
  induction n with
  | zero => simp only [Nat.cast_zero, zero_mul, Function.iterate_zero_apply, sub_self, le_refl]
  | succ n ih =>
    have hg := gradient_monotone (descent_le (descent^[n] x))
    have hm := mul_le_mul_of_nonneg_left hg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
    rw [Function.iterate_succ_apply', Nat.cast_add, Nat.cast_one]
    change ((n : ℝ) + 1) * gradient (descent (descent^[n] x)) ≤
      x - (descent^[n] x - gradient (descent^[n] x))
    nlinarith only [ih, hm]

/-- A reciprocal residual bound remains valid despite infinite flatness at zero. -/
theorem descent_gradient_rate (x : ℝ) (n : ℕ) :
    gradient (descent^[n + 1] x) ≤ (x - min x 0) / ((n : ℝ) + 1) := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
  have hb := descent_residual_budget x (n + 1)
  simp only [Nat.cast_add, Nat.cast_one] at hb
  nlinarith only [hb, (descent_iterate_bounds x (n + 1)).1]

/-- Flat descent converges to the negative-part projection for every starting value. -/
theorem descent_tendsto_negative_part (x : ℝ) :
    Tendsto (fun n : ℕ => descent^[n] x) atTop (𝓝 (min x 0)) := by
  by_cases hx : x ≤ 0
  · have hi (n : ℕ) : descent^[n] x = x := by
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply', ih, (descent_fixed_iff x).mpr hx]
    simp_rw [hi, min_eq_left hx]
    exact tendsto_const_nhds
  · have hx0 : 0 ≤ x := (lt_of_not_ge hx).le
    rw [min_eq_right hx0]
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hg : 0 < gradient ε := by
      by_contra h
      have hz := le_antisymm (le_of_not_gt h) (gradient_nonneg ε)
      exact (not_le_of_gt hε) ((gradient_zero_iff ε).mp hz)
    obtain ⟨N, hN⟩ := exists_nat_gt (x / gradient ε)
    rw [div_lt_iff₀ hg] at hN
    refine ⟨N, fun n hn => ?_⟩
    have hlo := (descent_iterate_bounds x n).1
    rw [min_eq_right hx0] at hlo
    have hlt : descent^[n] x < ε := by
      by_contra h
      have hm := mul_le_mul_of_nonneg_left
        (gradient_monotone (le_of_not_gt h)) (by positivity : (0 : ℝ) ≤ n)
      have hNn := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn : (N : ℝ) ≤ n) hg.le
      have hb := descent_residual_budget x n
      linarith only [hN, hNn, hm, hb, hlo]
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hlo] using hlt

#print axioms descent_contraction
#print axioms descent_residual_sum
#print axioms descent_gradient_rate
#print axioms descent_tendsto_negative_part
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex

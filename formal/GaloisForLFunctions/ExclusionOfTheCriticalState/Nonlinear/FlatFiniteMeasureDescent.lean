import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatIntegralDescent

/-!
# Finite measure restores uniform convergence of flat descent

Large positive amplitudes satisfy `T(t) ≤ A + t/A` after one step.
On bounded amplitude intervals, monotonicity reduces convergence to one
scalar endpoint. Splitting these regimes gives a uniform L² estimate
on the unit ball of every finite measure space. Infinite flatness slows
convergence but does not prevent this finite-volume uniformity.
-/

open MeasureTheory Filter Topology Set
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
noncomputable section

/-- The flat curvature tends to one strongly enough to make descent sublinear at infinity. -/
theorem descent_large_amplitude_bound {A : ℝ} (hA : 0 < A) {t : ℝ} (ht : 0 ≤ t) :
    descent t ≤ A + t / A := by
  by_cases htA : t ≤ A
  · exact (descent_le t).trans (htA.trans (le_add_of_nonneg_right (div_nonneg ht hA.le)))
  have hAt := (lt_of_not_ge htA).le
  have hc := (expNegInvGlue.contDiff (n := 0)).continuous
  have hlow : 1 - 1 / A ≤ expNegInvGlue A := by
    rw [expNegInvGlue, if_neg (not_le_of_gt hA)]
    simpa only [one_div, sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-A⁻¹)
  have hi : (∫ _ in A..t, (1 - 1 / A : ℝ)) ≤ ∫ u in A..t, expNegInvGlue u :=
    intervalIntegral.integral_mono_on hAt (continuous_const.intervalIntegrable A t)
      (hc.intervalIntegrable A t) (fun u hu => hlow.trans (expNegInvGlue.monotone hu.1))
  rw [intervalIntegral.integral_const, smul_eq_mul] at hi
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 A) (hc.intervalIntegrable A t)
  change gradient A + (∫ u in A..t, expNegInvGlue u) = gradient t at he
  calc
    descent t ≤ t - (t - A) * (1 - 1 / A) := by
      unfold descent
      linarith only [hi, he, gradient_nonneg A]
    _ = A - 1 + t / A := by field_simp [hA.ne']; ring
    _ ≤ A + t / A := by linarith

/-- An explicit amplitude threshold gives any desired relative decrease after one step. -/
theorem descent_tail_factor {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : 4 / δ ^ 2 ≤ t) :
    descent t ≤ δ * t := by
  have ht0 : 0 ≤ t := (by positivity : (0 : ℝ) ≤ 4 / δ ^ 2).trans ht
  have h := descent_large_amplitude_bound (by positivity : (0 : ℝ) < 2 / δ) ht0
  have hm := mul_le_mul_of_nonneg_left ht (show 0 ≤ δ / 2 by positivity)
  have he : (δ / 2) * (4 / δ ^ 2) = 2 / δ := by field_simp [hδ.ne']; ring
  have hd : t / (2 / δ) = δ / 2 * t := by field_simp [hδ.ne']
  rw [he] at hm
  rw [hd] at h
  linarith only [h, hm]

private theorem square_le_square {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h := mul_nonneg (sub_nonneg.mpr hab) (add_nonneg (ha.trans hab) ha)
  nlinarith only [h]

/-- Low amplitudes are controlled by a single iterate; high amplitudes by their initial L² mass. -/
theorem descent_scalar_split_bound {δ : ℝ} (hδ : 0 < δ) (n : ℕ) (t : ℝ) :
    (descent^[n + 1] t - min t 0) ^ 2 ≤
      (descent^[n + 1] (4 / δ ^ 2)) ^ 2 + δ ^ 2 * t ^ 2 := by
  by_cases ht : t ≤ 0
  · have hb := descent_iterate_bounds t (n + 1)
    rw [min_eq_left ht] at hb ⊢
    rw [le_antisymm hb.2 hb.1, sub_self, zero_pow two_ne_zero]
    positivity
  have ht0 := (lt_of_not_ge ht).le
  have hb := (descent_iterate_bounds t (n + 1)).1
  rw [min_eq_right ht0] at hb ⊢
  rw [sub_zero]
  by_cases htr : t ≤ 4 / δ ^ 2
  · have hs := square_le_square hb ((descent_monotone.iterate (n + 1)) htr)
    exact hs.trans (le_add_of_nonneg_right (mul_nonneg (sq_nonneg δ) (sq_nonneg t)))
  · have hs : descent^[n + 1] t ≤ descent t := by
      rw [Function.iterate_succ_apply']
      exact descent_monotone (descent_iterate_bounds t n).2
    have hsq := square_le_square hb (hs.trans (descent_tail_factor hδ (le_of_not_ge htr)))
    rw [mul_pow] at hsq
    exact hsq.trans (le_add_of_nonneg_left (sq_nonneg _))

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
private theorem integral_sq_norm (f : Lp ℝ 2 μ) : (∫ x, f x ^ 2 ∂μ) = ‖f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by change f x ^ 2 = f x * f x; ring

/-- Uniform error budget on the actual L² quotient, with the measure factor retained exactly. -/
theorem descentLp_finite_measure_bound {δ : ℝ} (hδ : 0 < δ) (n : ℕ) (f : Lp ℝ 2 μ) :
    ‖descentLp^[n + 1] f - negativePartLp f‖ ^ 2 ≤
      μ.real univ * (descent^[n + 1] (4 / δ ^ 2)) ^ 2 + δ ^ 2 * ‖f‖ ^ 2 := by
  have he : (fun x => (descentLp^[n + 1] f - negativePartLp f) x ^ 2) =ᵐ[μ]
      fun x => (descent^[n + 1] (f x) - min (f x) 0) ^ 2 := by
    filter_upwards [Lp.coeFn_sub (descentLp^[n + 1] f) (negativePartLp f),
      descentLp_iterate_ae f (n + 1), negativePartLp_ae f] with x hd hn hp
    rw [hd]
    simp only [Pi.sub_apply]
    rw [hn, hp]
  have hi := ((Lp.memLp (descentLp^[n + 1] f - negativePartLp f)).integrable_sq).congr he
  have hj : Integrable (fun x => (descent^[n + 1] (4 / δ ^ 2)) ^ 2 + δ ^ 2 * f x ^ 2) μ :=
    (integrable_const _).add ((Lp.memLp f).integrable_sq.const_mul _)
  have h := integral_mono hi hj (fun x => descent_scalar_split_bound hδ n (f x))
  rw [← integral_congr_ae he, integral_sq_norm,
    integral_add (integrable_const _) ((Lp.memLp f).integrable_sq.const_mul _),
    integral_const, smul_eq_mul, integral_const_mul, integral_sq_norm] at h
  exact h

/-- Flat descent converges uniformly on the L² unit ball whenever the underlying measure is finite. -/
theorem descentLp_uniform_on_finite_measure_unitBall {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ f : Lp ℝ 2 μ, ‖f‖ ≤ 1 →
      ‖descentLp^[n + 1] f - negativePartLp f‖ < ε := by
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hr : 0 ≤ 4 / δ ^ 2 := by positivity
  have hs := descent_tendsto_negative_part (4 / δ ^ 2)
  rw [min_eq_right hr] at hs
  have hn : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id
  have hb : Tendsto (fun n : ℕ => μ.real univ * (descent^[n + 1] (4 / δ ^ 2)) ^ 2)
      atTop (𝓝 0) := by
    simpa only [zero_pow two_ne_zero, mul_zero, Function.comp_apply] using
      (tendsto_const_nhds.mul ((hs.comp hn).pow 2))
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hb.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε ^ 2 / 4)))
  refine ⟨N, fun n hn f hf => ?_⟩
  have h := descentLp_finite_measure_bound hδ n f
  have hsq : ‖f‖ ^ 2 ≤ 1 := by simpa only [one_pow] using square_le_square (norm_nonneg f) hf
  have hm := mul_le_mul_of_nonneg_left hsq (sq_nonneg δ)
  rw [mul_one] at hm
  have hsmall := hN n hn
  dsimp only [δ] at h hm hsmall
  nlinarith only [h, hm, hsmall, hε, norm_nonneg (descentLp^[n + 1] f - negativePartLp f)]

#print axioms descent_large_amplitude_bound
#print axioms descent_tail_factor
#print axioms descentLp_finite_measure_bound
#print axioms descentLp_uniform_on_finite_measure_unitBall
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex

import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatIntegralDescent
import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatGradientNotFrechet

/-!
# Strong flat descent has no uniform rate on the L² unit ball

Every finite scalar iterate is tangent to the identity at zero.
Spreading small positive amplitudes over long intervals preserves unit
L² norm and transfers that tangency into arbitrarily small relative
decrease. Thus convergence of every profile does not imply uniform
convergence on bounded sets.
-/

open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
noncomputable section

private theorem descent_iterate_zero (n : ℕ) : descent^[n] 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, descent_zero]

/-- Infinite flatness leaves every finite descent iterate tangent to the identity. -/
theorem descent_iterate_hasDerivAt_zero (n : ℕ) : HasDerivAt (descent^[n]) 1 0 := by
  have hd : HasDerivAt descent 1 0 := by
    have h : HasDerivAt descent (1 - expNegInvGlue 0) 0 :=
      (hasDerivAt_id (0 : ℝ)).fun_sub (gradient_hasDerivAt 0)
    simpa only [expNegInvGlue.zero, sub_zero] using h
  induction n with
  | zero => exact hasDerivAt_id 0
  | succ n ih =>
    have hd' : HasDerivAt descent 1 (descent^[n] 0) := by
      rw [descent_iterate_zero]
      exact hd
    have he : descent^[n + 1] = descent ∘ descent^[n] := by
      funext t
      rw [Function.iterate_succ_apply']
      rfl
    rw [he]
    simpa only [one_mul] using hd'.comp 0 ih

/-- Every finite iteration admits positive inputs with relative decrease arbitrarily small. -/
theorem exists_descent_relative_lower_bound (n : ℕ) {c : ℝ} (hc : c < 1) :
    ∃ t : ℝ, 0 < t ∧ c * t < descent^[n] t := by
  have hp : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) := by
    apply nhdsWithin_mono
    intro t ht
    exact ht.ne'
  have hs : Tendsto (fun t : ℝ => descent^[n] t / t) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [descent_iterate_zero, zero_add, sub_zero, smul_eq_mul,
      div_eq_mul_inv, mul_comm] using
      (descent_iterate_hasDerivAt_zero n).tendsto_slope_zero.mono_left hp
  have ht : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hband : ∀ᶠ y in 𝓝 (1 : ℝ), c < y := by
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨1 - c, sub_pos.mpr hc, ?_⟩
    intro y hy
    rw [Real.dist_eq] at hy
    linarith only [(abs_lt.mp hy).1]
  have he : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ c < descent^[n] t / t :=
    ht.and (hs.eventually hband)
  obtain ⟨t, ht, hct⟩ := he.exists
  exact ⟨t, ht, (lt_div_iff₀ ht).mp hct⟩

private theorem descentLp_intervalSpike (t s : ℝ) :
    descentLp (s • intervalSpike t) = descent s • intervalSpike t := by
  rw [descentLp, gradientLp_intervalSpike, ← sub_smul]
  rfl

private theorem descentLp_iterate_intervalSpike (t s : ℝ) (n : ℕ) :
    descentLp^[n] (s • intervalSpike t) = descent^[n] s • intervalSpike t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, descentLp_intervalSpike,
      Function.iterate_succ_apply']

private theorem negativePartLp_positive_spike (t : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    negativePartLp (s • intervalSpike t) = 0 := by
  apply Lp.ext
  have hv : (intervalSpike t : ℝ → ℝ) =ᵐ[volume]
      (Ioc 0 (t ^ 2)).indicator (fun _ => (1 : ℝ)) := indicatorConstLp_coeFn
  filter_upwards [negativePartLp_ae (s • intervalSpike t),
    Lp.coeFn_smul s (intervalSpike t), hv, Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)]
    with x hx hsx hvx hzero
  rw [hx, hsx, hzero]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hvx]
  by_cases hm : x ∈ Ioc 0 (t ^ 2)
  · simp only [indicator_of_mem hm, mul_one, min_eq_right hs]
  · simp only [indicator_of_notMem hm, mul_zero, min_self]

/-- On the positive L² unit sphere, no fixed number of steps gives a uniform factor below one. -/
theorem exists_unit_profile_slow_descent (n : ℕ) {c : ℝ} (hc : c < 1) :
    ∃ f : Lp ℝ 2 (volume : Measure ℝ),
      ‖f‖ = 1 ∧ negativePartLp f = 0 ∧ c < ‖descentLp^[n] f‖ := by
  obtain ⟨t, ht, hct⟩ := exists_descent_relative_lower_bound n hc
  refine ⟨t • intervalSpike (1 / t), ?_, negativePartLp_positive_spike _ ht.le, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, intervalSpike_norm,
      abs_of_pos (one_div_pos.mpr ht)]
    field_simp
  · have hn : 0 ≤ descent^[n] t := by
      simpa only [min_eq_right ht.le] using (descent_iterate_bounds t n).1
    rw [descentLp_iterate_intervalSpike, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hn, intervalSpike_norm, abs_of_pos (one_div_pos.mpr ht)]
    simpa only [one_div, div_eq_mul_inv, one_mul] using (lt_div_iff₀ ht).mpr hct

/-- Strong convergence to the negative part is never uniform on the unit sphere. -/
theorem no_uniform_descent_factor (n : ℕ) {c : ℝ} (hc : c < 1) :
    ¬ ∀ f : Lp ℝ 2 (volume : Measure ℝ), ‖f‖ = 1 →
      ‖descentLp^[n] f - negativePartLp f‖ ≤ c := by
  intro h
  obtain ⟨f, hf, hp, hs⟩ := exists_unit_profile_slow_descent n hc
  have he := h f hf
  rw [hp, sub_zero] at he
  exact (not_lt_of_ge he) hs

private theorem energy_le_gradient_norm_mul_norm (f : Lp ℝ 2 (volume : Measure ℝ)) :
    integralEnergy f ≤ ‖gradientLp f‖ * ‖f‖ := by
  have hz : integralEnergy (0 : Lp ℝ 2 (volume : Measure ℝ)) = 0 := by
    unfold integralEnergy
    calc
      (∫ x, potential ((0 : Lp ℝ 2 (volume : Measure ℝ)) x)) = ∫ _, (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)] with x hx
        simp only [hx, Pi.zero_apply, potential_zero]
      _ = 0 := integral_zero _ _
  have hs := integral_support (0 : Lp ℝ 2 (volume : Measure ℝ)) f
  rw [hz, zero_sub, inner_neg_right] at hs
  have hi : inner ℝ (gradientLp f) f ≤ ‖gradientLp f‖ * ‖f‖ :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) (gradientLp f) f))
  linarith only [hs, hi]

/-- Unit profiles can have arbitrarily small positive energy and gradient simultaneously. -/
theorem exists_unit_approximate_critical_profile {ε : ℝ} (hε : 0 < ε) :
    ∃ f : Lp ℝ 2 (volume : Measure ℝ),
      ‖f‖ = 1 ∧ negativePartLp f = 0 ∧
      (0 < integralEnergy f ∧ integralEnergy f < ε) ∧
      (0 < ‖gradientLp f‖ ∧ ‖gradientLp f‖ < ε) := by
  obtain ⟨t, ht, hct⟩ := exists_descent_relative_lower_bound 1
    (c := 1 - ε) (by linarith only [hε])
  have hgt : gradient t < ε * t := by
    change (1 - ε) * t < descent t at hct
    unfold descent at hct
    nlinarith only [hct]
  have hgpos : 0 < gradient t := by
    have hne : gradient t ≠ 0 := fun h => (not_le_of_gt ht) ((gradient_zero_iff t).mp h)
    exact lt_of_le_of_ne (gradient_nonneg t) hne.symm
  let f : Lp ℝ 2 (volume : Measure ℝ) := t • intervalSpike (1 / t)
  have hnorm : ‖f‖ = 1 := by
    dsimp only [f]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, intervalSpike_norm,
      abs_of_pos (one_div_pos.mpr ht)]
    field_simp
  have hg : ‖gradientLp f‖ = gradient t / t := by
    dsimp only [f]
    rw [gradientLp_intervalSpike, norm_smul, Real.norm_eq_abs,
      abs_of_pos hgpos, intervalSpike_norm, abs_of_pos (one_div_pos.mpr ht)]
    ring
  have hgn : 0 < ‖gradientLp f‖ := by rw [hg]; exact div_pos hgpos ht
  have hge : ‖gradientLp f‖ < ε := by rw [hg]; exact (div_lt_iff₀ ht).mpr hgt
  have heb := energy_le_gradient_norm_mul_norm f
  rw [hnorm, mul_one] at heb
  have hep : 0 < integralEnergy f := by
    have hs := gradientLp_sq_le_energy f
    nlinarith only [hs, sq_pos_of_pos hgn]
  exact ⟨f, hnorm, negativePartLp_positive_spike _ ht.le, ⟨hep, heb.trans_lt hge⟩, hgn, hge⟩

#print axioms descent_iterate_hasDerivAt_zero
#print axioms exists_descent_relative_lower_bound
#print axioms exists_unit_profile_slow_descent
#print axioms no_uniform_descent_factor
#print axioms exists_unit_approximate_critical_profile
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex

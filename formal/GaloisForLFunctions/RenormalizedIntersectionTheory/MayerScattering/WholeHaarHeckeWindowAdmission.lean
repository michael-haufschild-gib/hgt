import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.HeckeWordsPreserveFiniteCuspEnergy
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Whole-Haar admission for the source Hecke image of a window lift

The actual paired window lift has finite whole-axis Haar energy after one source Hecke
step exactly when its first-prime trace vanishes. Universal admission includes the endpoint
stage `A = log 2`, where compact-support admission already fails.
-/

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter Topology
open scoped ENNReal
open GaloisForLFunctions CohomologyOfWindowsOfSpecZ

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-- A finite Haar square integral forces every existing lower-cusp limit to vanish. -/
theorem haarSquareIntegrable_zero_trace {f : ℝ → ℂ} {c : ℂ}
    (hl : Tendsto f (𝓝[>] 0) (𝓝 c)) {r : ℝ} (hr : 0 < r)
    (hint : IntegrableOn (fun a : ℝ => ‖f a‖ ^ 2 / a) (Ioo 0 r)) : c = 0 := by
  by_contra hc
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hb := hl.norm.eventually_const_le (show ‖c‖ / 2 < ‖c‖ by linarith only [hcn])
  obtain ⟨ε, hε, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hb
  have hδ : 0 < min r ε := lt_min hr hε
  have hi := hint.mono_set (Ioo_subset_Ioo le_rfl (min_le_left r ε))
  have hinv : IntegrableOn (fun a : ℝ => a⁻¹) (Ioo 0 (min r ε)) := by
    apply (hi.const_mul (4 / ‖c‖ ^ 2)).mono' measurable_inv.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
    have hlow : ‖c‖ / 2 ≤ ‖f a‖ := hbound ⟨ha.1, ha.2.trans_le (min_le_right r ε)⟩
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha.1)]
    have hsq : ‖c‖ ^ 2 / 4 ≤ ‖f a‖ ^ 2 := by
      have hp := pow_le_pow_left₀ (show 0 ≤ ‖c‖ / 2 by positivity) hlow 2
      nlinarith only [hp]
    have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 4 / ‖c‖ ^ 2)
    have hunit : (4 / ‖c‖ ^ 2) * (‖c‖ ^ 2 / 4) = 1 := by field_simp [hcn.ne']
    rw [hunit] at hmul
    have hdiv := div_le_div_of_nonneg_right hmul ha.1.le
    simpa only [one_div, mul_div_assoc] using hdiv
  have hrpow : IntegrableOn (fun a : ℝ => a ^ (-1 : ℝ)) (Ioo 0 (min r ε)) := by
    simpa only [Real.rpow_neg_one] using hinv
  have hfalse := (intervalIntegral.integrableOn_Ioo_rpow_iff hδ).mp hrpow
  exact (lt_irrefl (-1 : ℝ)) hfalse

private theorem local_linear_bound_of_zero_trace {g : ℝ → ℂ}
    (hg : DifferentiableAt ℝ g 0) (hz : g 0 = 0) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ a ∈ Ioo 0 δ, ‖g a‖ ≤ C * a := by
  obtain ⟨C, hC, hb⟩ := hg.isBigO_sub.exists_pos
  have he : ∀ᶠ a in 𝓝[>] (0 : ℝ), ‖g a‖ ≤ C * a := by
    filter_upwards [hb.bound.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with a ha hp
    have ha0 : 0 < a := hp
    simpa only [hz, sub_zero, Real.norm_eq_abs, abs_of_pos ha0] using ha
  obtain ⟨δ, hδ, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  exact ⟨C, δ, hC, hδ, fun a ha => hbound ha⟩

private theorem measurable_window_lift (s : ℂ) {H : ℝ → ℝ} (hH : Measurable H) :
    Measurable (windowPeriodLift s H) := by
  have hF : Measurable (windowLogLift s H) := by
    unfold windowLogLift
    apply Measurable.ite (measurableSet_lt measurable_const measurable_id)
    · fun_prop
    · apply Measurable.ite (measurableSet_lt measurable_id measurable_const)
      · fun_prop
      · exact measurable_const
  unfold windowPeriodLift logPeriodInverse
  fun_prop

private theorem window_lift_lower_cutoff {A : ℝ} {H : ℝ → ℝ}
    (hH : IsWindowTest A H) (s : ℂ) {a : ℝ} (ha : 0 < a)
    (hsmall : a < min 1 (Real.exp (-A))) : windowPeriodLift s H a = 0 := by
  have ha1 : a < 1 := hsmall.trans_le (min_le_left _ _)
  have hlog : Real.log a < -A := (Real.log_lt_iff_lt_exp ha).mpr
    (hsmall.trans_le (min_le_right _ _))
  have hzero := hH.vanish (Real.log a) (fun h => (not_lt_of_ge h.1) hlog)
  have hl : Real.log a < 0 := Real.log_neg ha ha1
  simp only [windowPeriodLift, logPeriodInverse, windowLogLift,
    if_neg (not_lt.mpr hl.le), if_pos hl, hzero, mul_zero, Complex.ofReal_zero]

private theorem hecke_window_lift_lower_formula {A : ℝ} {H : ℝ → ℝ}
    (hH : IsWindowTest A H) (s : ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ Ioo 0 δ,
      lewisHeckeT2 s (windowPeriodLift s H) a =
        (2 : ℂ) ^ (-(2 * s)) * windowPeriodLift s H ((a + 1) / 2) := by
  let l := min 1 (Real.exp (-A))
  have hl : 0 < l := lt_min zero_lt_one (Real.exp_pos _)
  refine ⟨l / 4, by positivity, fun a ha => ?_⟩
  have ha0 : 0 < a := ha.1
  have h2a : 2 * a < l := by linarith only [ha.2, hl]
  have hhalf : a / 2 < l := by linarith only [ha.2, hl]
  have hr : 2 * a / (a + 1) < l := by
    have he : 2 * a / (a + 1) ≤ 2 * a := div_le_self (by positivity) (by linarith only [ha.1])
    exact he.trans_lt h2a
  rw [lewisHeckeT2, window_lift_lower_cutoff hH s (by positivity) h2a,
    window_lift_lower_cutoff hH s (by positivity) hhalf,
    window_lift_lower_cutoff hH s (by positivity) hr]
  ring

private theorem window_lift_differentiable_half {A : ℝ} {H : ℝ → ℝ}
    (hH : IsWindowTest A H) (s : ℂ) :
    DifferentiableAt ℝ (windowPeriodLift s H) (1 / 2) := by
  let F : ℝ → ℂ := fun a =>
    (((a + a⁻¹) ^ (3 : ℝ) * a ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
      (Complex.exp (-((2 * s - 1 / 2) * (Real.log a : ℂ))) *
        ((Real.exp ((s.re - 1 / 4) * Real.log a) * H (Real.log a) : ℝ) : ℂ))
  have hHd : Differentiable ℝ H := hH.contDiff.differentiable (by simp)
  have hF : DifferentiableAt ℝ F (1 / 2) := by
    dsimp only [F]
    fun_prop (disch := norm_num)
  apply hF.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds (show (1 / 2 : ℝ) ∈ Ioo 0 1 by norm_num)] with a ha
  have hl : Real.log a < 0 := Real.log_neg ha.1 ha.2
  simp only [windowPeriodLift, logPeriodInverse, windowLogLift,
    if_neg (not_lt.mpr hl.le), if_pos hl, F]

private theorem whole_haar_of_local_linear_bound {f : ℝ → ℂ}
    (hf : Measurable f) (hupper : IntegrableOn (fun a : ℝ => ‖f a‖ ^ 2 / a) (Ioi 1))
    {D : ℝ} (hb : ∀ a > 0, ‖f a‖ ≤ D)
    {C δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ a ∈ Ioo 0 δ, ‖f a‖ ≤ C * a) :
    IntegrableOn (fun a : ℝ => ‖f a‖ ^ 2 / a) (Ioi 0) := by
  let e := min δ 1
  have he : 0 < e := lt_min hδ zero_lt_one
  have hi0 : IntegrableOn (fun a : ℝ => ‖f a‖ ^ 2 / a) (Ioo 0 e) := by
    have hc : IntegrableOn (fun _ : ℝ => C ^ 2 * e) (Ioo 0 e) :=
      integrableOn_const (hs := measure_Ioo_lt_top.ne)
    apply hc.mono' ((hf.norm.pow_const 2).div measurable_id).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
    have hfa := hlow a ⟨ha.1, ha.2.trans_le (min_le_left δ 1)⟩
    change ‖(‖f a‖ ^ 2 / a : ℝ)‖ ≤ C ^ 2 * e
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) ha.1.le)]
    calc
      ‖f a‖ ^ 2 / a ≤ (C * a) ^ 2 / a :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hfa 2) ha.1.le
      _ = C ^ 2 * a := by field_simp [ha.1.ne']
      _ ≤ C ^ 2 * e := mul_le_mul_of_nonneg_left ha.2.le (sq_nonneg _)
  have him : IntegrableOn (fun a : ℝ => ‖f a‖ ^ 2 / a) (Icc e 1) := by
    have hc : IntegrableOn (fun _ : ℝ => D ^ 2 / e) (Icc e 1) :=
      integrableOn_const (hs := measure_Icc_lt_top.ne)
    apply hc.mono' ((hf.norm.pow_const 2).div measurable_id).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
    have ha0 : 0 < a := he.trans_le ha.1
    change ‖(‖f a‖ ^ 2 / a : ℝ)‖ ≤ D ^ 2 / e
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) ha0.le)]
    calc
      ‖f a‖ ^ 2 / a ≤ D ^ 2 / a :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hb a ha0) 2) ha0.le
      _ ≤ D ^ 2 / e := div_le_div_of_nonneg_left (sq_nonneg _) he ha.1
  apply ((hi0.union him).union hupper).mono_set
  intro a ha
  by_cases hlt : a < e
  · exact Or.inl (Or.inl ⟨ha, hlt⟩)
  · by_cases ha1 : a ≤ 1
    · exact Or.inl (Or.inr ⟨le_of_not_gt hlt, ha1⟩)
    · exact Or.inr (lt_of_not_ge ha1)

/-- Whole-axis Haar admission depends on the first-prime value, rather than its entire germ. -/
theorem hecke_windowPeriodLift_finite_whole_haar_iff {A : ℝ} (hA : 0 ≤ A)
    {H : ℝ → ℝ} (hH : IsWindowTest A H) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun a : ℝ => ‖lewisHeckeT2 s (windowPeriodLift s H) a‖ ^ 2 / a) (Ioi 0) ↔
      H (-Real.log 2) = 0 := by
  let f := lewisHeckeT2 s (windowPeriodLift s H)
  let g : ℝ → ℂ := fun a => (2 : ℂ) ^ (-(2 * s)) * windowPeriodLift s H ((a + 1) / 2)
  have hinner : DifferentiableAt ℝ (fun a : ℝ => (a + 1) / 2) 0 := by fun_prop
  have hψ : DifferentiableAt ℝ (windowPeriodLift s H) ((fun a : ℝ => (a + 1) / 2) 0) := by
    simpa using window_lift_differentiable_half hH s
  have hg : DifferentiableAt ℝ g 0 := (hψ.comp 0 hinner).const_mul _
  have hg0 : g 0 = windowPeriodLift s H 2 := by
    have h := lewisModularInversion_windowPeriodLift s H (by norm_num : (0 : ℝ) < 2)
    change (2 : ℂ) ^ (-(2 * s)) * windowPeriodLift s H (2 : ℝ)⁻¹ = _ at h
    simpa only [g, zero_add, one_div] using h
  obtain ⟨δ, hδ, heq⟩ := hecke_window_lift_lower_formula hH s
  have he : f =ᶠ[𝓝[>] 0] g := mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨δ, hδ, heq⟩
  have htrace : Tendsto f (𝓝[>] 0) (𝓝 (g 0)) :=
    (tendsto_congr' he).mpr (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  constructor
  · intro hint
    have hz := haarSquareIntegrable_zero_trace htrace zero_lt_one
      (hint.mono_set (show Ioo (0 : ℝ) 1 ⊆ Ioi 0 from fun _ h => h.1))
    exact (windowPeriodLift_eq_zero_iff s H (by norm_num : (1 : ℝ) < 2)).mp (hg0.symm.trans hz)
  · intro hprime
    have hgzero : g 0 = 0 := hg0.trans
      ((windowPeriodLift_eq_zero_iff s H (by norm_num : (1 : ℝ) < 2)).mpr hprime)
    obtain ⟨C, e, _, he0, hlinear⟩ := local_linear_bound_of_zero_trace hg hgzero
    have hmψ := measurable_window_lift s hH.contDiff.continuous.measurable
    have hmf : Measurable f := by dsimp only [f]; unfold lewisHeckeT2; fun_prop
    have hu : IntegrableOn (fun a : ℝ => ‖f a‖ ^ 2 / a) (Ioi 1) := by
      simpa only [f, lewisHeckeWord] using
        (lewisHeckeWord_windowPeriodLift_finite_cusp_energy hA hH hs [LewisHeckePrime.two]).1
    obtain ⟨D, hD, hdecay⟩ := lewisHeckeWord_windowPeriodLift_decay hA hH hs.le [LewisHeckePrime.two]
    have hb : ∀ a > 0, ‖f a‖ ≤ D := by
      intro a ha
      have hpow : (1 + a) ^ (-(2 * s.re)) ≤ 1 := by
        simpa only [Real.one_rpow] using Real.rpow_le_rpow_of_nonpos zero_lt_one
          (show 1 ≤ 1 + a by linarith only [ha]) (show -(2 * s.re) ≤ 0 by linarith only [hs])
      exact (hdecay a ha).trans ((mul_le_mul_of_nonneg_left hpow hD).trans_eq (mul_one D))
    apply whole_haar_of_local_linear_bound (C := C) hmf hu hb (lt_min hδ he0)
    intro a ha
    change ‖lewisHeckeT2 s (windowPeriodLift s H) a‖ ≤ C * a
    rw [heq a ⟨ha.1, ha.2.trans_le (min_le_left δ e)⟩]
    exact hlinear a ⟨ha.1, ha.2.trans_le (min_le_right δ e)⟩

private theorem window_left_endpoint_zero {A : ℝ} {H : ℝ → ℝ}
    (hH : IsWindowTest A H) : H (-A) = 0 := by
  have he : EqOn H (fun _ => (0 : ℝ)) (Iio (-A)) := by
    intro x hx
    exact hH.vanish x (fun hm => (not_lt_of_ge hm.1) hx)
  have hc := he.closure hH.continuous continuous_const
  have hm : -A ∈ closure (Iio (-A)) := by
    rw [closure_Iio]
    exact (le_refl (-A))
  exact hc hm

/-- Every window test has a whole-Haar Hecke image exactly through the first-prime stage,
including the endpoint stage where compact-support admission fails. -/
theorem hecke_windowPeriodLift_all_whole_haar_iff {s : ℂ} (hs : 0 < s.re)
    (A : ℝ) (hA : 0 ≤ A) :
    (∀ H : ℝ → ℝ, IsWindowTest A H →
      IntegrableOn (fun a : ℝ => ‖lewisHeckeT2 s (windowPeriodLift s H) a‖ ^ 2 / a) (Ioi 0)) ↔
      A ≤ Real.log 2 := by
  constructor
  · intro hall
    by_contra hnot
    obtain ⟨H, hH, hprime, _⟩ := exists_windowTest_hecke_no_cutoff s (lt_of_not_ge hnot)
    have hz := (hecke_windowPeriodLift_finite_whole_haar_iff hA hH hs).mp (hall H hH)
    rw [hprime] at hz
    exact one_ne_zero hz
  · intro hle H hH
    apply (hecke_windowPeriodLift_finite_whole_haar_iff hA hH hs).mpr
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hH.vanish _ (fun hm => by linarith only [hm.1, hlt])
    · rw [← heq]
      exact window_left_endpoint_zero hH

/-- A noncompact Hecke tail can have finite whole-axis Haar energy at the exact first-prime stage. -/
theorem exists_first_prime_window_finite_haar_noncompact {s : ℂ} (hs : 0 < s.re) :
    ∃ H : ℝ → ℝ, IsWindowTest (Real.log 2) H ∧
      IntegrableOn (fun a : ℝ => ‖lewisHeckeT2 s (windowPeriodLift s H) a‖ ^ 2 / a) (Ioi 0) ∧
      ¬ ∃ B : ℝ, 0 ≤ B ∧ ∀ a > B, lewisHeckeT2 s (windowPeriodLift s H) a = 0 := by
  obtain ⟨H, hH, hz, hnc⟩ := exists_windowTest_hecke_no_cutoff_of_log_two_le s (le_refl (Real.log 2))
  exact ⟨H, hH, (hecke_windowPeriodLift_finite_whole_haar_iff
    (Real.log_nonneg (by norm_num)) hH hs).mpr hz, hnc⟩

#print axioms haarSquareIntegrable_zero_trace
#print axioms hecke_windowPeriodLift_finite_whole_haar_iff
#print axioms hecke_windowPeriodLift_all_whole_haar_iff
#print axioms exists_first_prime_window_finite_haar_noncompact

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

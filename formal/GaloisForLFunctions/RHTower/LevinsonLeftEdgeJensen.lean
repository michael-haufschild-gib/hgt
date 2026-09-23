import GaloisForLFunctions.RHTower.LittlewoodPoleGaugeCancellation

/-!
# The left edge of a Littlewood rectangle, from a mean square

Jensen's inequality turns the logarithmic integral on the left edge of Littlewood's rectangle into
the second moment there.  The function need only be analytic on the segment (not entire), and may
vanish at finitely many of its points; the statement is the one Levinson's method consumes, with the
mean square of the *meromorphic* mollified detector on the abscissa `σ₀`.
-/

open Complex MeasureTheory Set Filter intervalIntegral Topology
open scoped Interval

namespace RHTower

noncomputable section

/-- **Jensen's left-edge bound.** -/
theorem integral_log_norm_le_of_meanSquare {g : ℂ → ℂ} {c T₁ T₂ Msq : ℝ} (hT : T₁ < T₂)
    (hg : ∀ t ∈ uIcc T₁ T₂, AnalyticAt ℂ g ((c : ℂ) + (t : ℂ) * I))
    (hfin : {t : ℝ | t ∈ uIcc T₁ T₂ ∧ g ((c : ℂ) + (t : ℂ) * I) = 0}.Finite)
    (hex : ∃ t ∈ Set.Ioo T₁ T₂, g ((c : ℂ) + (t : ℂ) * I) ≠ 0)
    (hMsq : (∫ t in T₁..T₂, ‖g ((c : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ)) ≤ Msq) :
    2 * (∫ t in T₁..T₂, Real.log ‖g ((c : ℂ) + (t : ℂ) * I)‖)
      ≤ (T₂ - T₁) * Real.log (Msq / (T₂ - T₁)) := by
  classical
  have hlen : (0 : ℝ) < T₂ - T₁ := by linarith
  have huIcc : uIcc T₁ T₂ = Set.Icc T₁ T₂ := uIcc_of_le hT.le
  have hcontOn : ContinuousOn (fun t : ℝ => g ((c : ℂ) + (t : ℂ) * I)) (uIcc T₁ T₂) := by
    intro t ht
    have hc : ContinuousAt (g ∘ (fun y : ℝ => (c : ℂ) + (y : ℂ) * I)) t :=
      ContinuousAt.comp ((hg t ht).continuousAt)
        (by fun_prop : ContinuousAt (fun y : ℝ => (c : ℂ) + (y : ℂ) * I) t)
    have hc' : ContinuousAt (fun y : ℝ => g ((c : ℂ) + (y : ℂ) * I)) t := by
      simpa [Function.comp_def] using hc
    exact hc'.continuousWithinAt
  have hsqint : IntervalIntegrable
      (fun t : ℝ => ‖g ((c : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ)) volume T₁ T₂ :=
    (hcontOn.norm.pow 2).intervalIntegrable
  have hlogint := intervalIntegrable_log_norm_vertical_of_analyticAt hg
  have hIpos : 0 < ∫ t in T₁..T₂, ‖g ((c : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ) := by
    obtain ⟨t₀, ht₀, hne⟩ := hex
    have hnn : ∀ t ∈ Set.uIoc T₁ T₂, (0 : ℝ) ≤ ‖g ((c : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ) := by
      intro t _; positivity
    have hsupp : 0 < volume (Function.support
        (fun t : ℝ => ‖g ((c : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ)) ∩ Set.Ioc T₁ T₂) := by
      have hcontAt : ContinuousAt (fun t : ℝ => ‖g ((c : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ)) t₀ := by
        have hc : ContinuousAt (g ∘ (fun y : ℝ => (c : ℂ) + (y : ℂ) * I)) t₀ :=
          ContinuousAt.comp ((hg t₀ (by rw [huIcc]; exact Set.Ioo_subset_Icc_self ht₀)).continuousAt)
            (by fun_prop : ContinuousAt (fun y : ℝ => (c : ℂ) + (y : ℂ) * I) t₀)
        have hc' : ContinuousAt (fun y : ℝ => g ((c : ℂ) + (y : ℂ) * I)) t₀ := by
          simpa [Function.comp_def] using hc
        exact (hc'.norm.pow 2)
      have hval : (0 : ℝ) < ‖g ((c : ℂ) + (t₀ : ℂ) * I)‖ ^ (2 : ℕ) := by
        have : 0 < ‖g ((c : ℂ) + (t₀ : ℂ) * I)‖ := norm_pos_iff.mpr hne
        positivity
      have hne_ev : ∀ᶠ x in 𝓝 t₀, (fun t : ℝ => ‖g ((c : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ)) x ≠ 0 :=
        hcontAt.eventually_ne (ne_of_gt hval)
      have hIoo_ev : Set.Ioo T₁ T₂ ∈ 𝓝 t₀ := Ioo_mem_nhds ht₀.1 ht₀.2
      have hnhds : Function.support (fun t : ℝ => ‖g ((c : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ))
          ∩ Set.Ioc T₁ T₂ ∈ 𝓝 t₀ := by
        filter_upwards [hne_ev, hIoo_ev] with x hxne hxIoo
        exact ⟨Function.mem_support.mpr hxne, Set.Ioo_subset_Ioc_self hxIoo⟩
      exact Measure.measure_pos_of_mem_nhds volume hnhds
    rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae' ?_ hsqint]
    · exact ⟨hT, hsupp⟩
    · filter_upwards with x
      positivity
  have hae : ∀ᵐ (t : ℝ) ∂(volume.restrict (Set.Icc T₁ T₂)),
      g ((c : ℂ) + (t : ℂ) * I) ≠ 0 := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr ?_
    have hnull : ∀ᵐ (t : ℝ) ∂volume,
        t ∉ {t : ℝ | t ∈ uIcc T₁ T₂ ∧ g ((c : ℂ) + (t : ℂ) * I) = 0} :=
      MeasureTheory.measure_eq_zero_iff_ae_notMem.mp (hfin.measure_zero volume)
    filter_upwards [hnull] with t ht htmem h0
    exact ht ⟨by rw [huIcc]; exact htmem, h0⟩
  have hJ := two_mul_integral_log_norm_le_ae (f := fun t : ℝ => g ((c : ℂ) + (t : ℂ) * I))
    hT hae hsqint hlogint hIpos
  have hdiv : (∫ t in T₁..T₂, ‖g ((c : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ)) / (T₂ - T₁)
      ≤ Msq / (T₂ - T₁) := by gcongr
  have hlogmono := Real.log_le_log (div_pos hIpos hlen) hdiv
  calc 2 * (∫ t in T₁..T₂, Real.log ‖g ((c : ℂ) + (t : ℂ) * I)‖)
      ≤ (T₂ - T₁) *
          Real.log ((∫ t in T₁..T₂, ‖g ((c : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ)) / (T₂ - T₁)) := hJ
    _ ≤ (T₂ - T₁) * Real.log (Msq / (T₂ - T₁)) :=
        mul_le_mul_of_nonneg_left hlogmono hlen.le

end

end RHTower

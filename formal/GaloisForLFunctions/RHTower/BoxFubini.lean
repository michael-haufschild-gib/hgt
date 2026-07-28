import GaloisForLFunctions.RHTower.LogModulusHorizontal

/-!
# Fubini on a box, and the log-modulus pair

The left-edge term of the `σ`-integrated argument principle is a double integral of `Re (f′/f)` over
a rectangle.  Swapping the order of integration and applying the horizontal log-modulus identity
turns it into Littlewood's log-modulus pair.  For a continuous integrand on a compact box the Fubini
hypothesis is automatic, so this discharges that input of `littlewood_from_edges`.
-/

open MeasureTheory intervalIntegral Complex

namespace RHTower

/-- **Fubini on a box for a continuous integrand.**  Both iterated integrals of a continuous function
over a compact rectangle agree. -/
theorem interval_integral_swap_of_continuous {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {F : ℝ → ℝ → ℝ} (hF : Continuous (Function.uncurry F)) :
    (∫ σ in a..b, ∫ t in c..d, F σ t) = ∫ t in c..d, ∫ σ in a..b, F σ t := by
  have hK : IsCompact (Set.Icc a b ×ˢ Set.Icc c d) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc a b)) := ⟨by simp [Real.volume_Ioc]⟩
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc c d)) := ⟨by simp [Real.volume_Ioc]⟩
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  simp_rw [intervalIntegral.integral_of_le hcd, intervalIntegral.integral_of_le hab]
  refine MeasureTheory.integral_integral_swap ?_
  refine MeasureTheory.Integrable.mono' (integrable_const C) hF.aestronglyMeasurable ?_
  rw [MeasureTheory.Measure.prod_restrict]
  filter_upwards [MeasureTheory.ae_restrict_mem
    (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
  exact hC p ⟨Set.Ioc_subset_Icc_self hp.1, Set.Ioc_subset_Icc_self hp.2⟩

/-- **The log-modulus pair.**  For `f` analytic and nonvanishing on the closed box, the `σ`-integral
of the left-edge term equals Littlewood's pair of log-modulus integrals.  Fubini supplies the swap,
`integral_re_logDeriv_horizontal` the inner evaluation; no branch of the logarithm is used. -/
theorem integral_left_edge_eq_logPair {σ₀ σ₁ T₁ T₂ : ℝ} {f : ℂ → ℂ}
    (hσ : σ₀ ≤ σ₁) (hT : T₁ ≤ T₂)
    (hF : Continuous (Function.uncurry fun σ t : ℝ =>
      (deriv f ((σ : ℂ) + t * I) / f ((σ : ℂ) + t * I)).re))
    (hd : ∀ t : ℝ, ∀ σ ∈ Set.uIcc σ₀ σ₁,
      HasDerivAt f (deriv f ((σ : ℂ) + t * I)) ((σ : ℂ) + t * I))
    (hne : ∀ t : ℝ, ∀ σ ∈ Set.uIcc σ₀ σ₁, f ((σ : ℂ) + t * I) ≠ 0) :
    (∫ σ in σ₀..σ₁, ∫ t in T₁..T₂,
        (deriv f ((σ : ℂ) + t * I) / f ((σ : ℂ) + t * I)).re)
      = ∫ t in T₁..T₂, (Real.log ‖f ((σ₁ : ℂ) + t * I)‖
          - Real.log ‖f ((σ₀ : ℂ) + t * I)‖) := by
  rw [interval_integral_swap_of_continuous hσ hT hF]
  refine intervalIntegral.integral_congr fun t _ => ?_
  refine integral_re_logDeriv_horizontal (hd t) (hne t) ?_
  have hcont : Continuous fun σ : ℝ =>
      (deriv f ((σ : ℂ) + t * I) / f ((σ : ℂ) + t * I)).re := by
    exact hF.comp (continuous_id.prodMk continuous_const)
  exact hcont.intervalIntegrable σ₀ σ₁

end RHTower

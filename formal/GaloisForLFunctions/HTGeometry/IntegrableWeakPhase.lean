import GaloisForLFunctions.HTGeometry.MakarovPoltoratskiWeakPhase

/-!
# Integrable phases have little weak `L¹` Poisson tails

The endpoint form of Kolmogorov's estimate used by the Smirnov phase criterion is automatic for
every phase integrable against standard Poisson measure.  The proof uses a measurable
representative, tail integrals, and the localized Markov inequality.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Integrability against standard Poisson measure implies the little weak-`L¹` tail required by
the Makarov--Poltoratski endpoint criterion. -/
theorem poissonWeakL1LittleO_of_integrable {f : ℝ → ℝ}
    (hf : Integrable (fun x => |f x|)
      (ProbabilityTheory.cauchyMeasure 0 1)) :
    PoissonWeakL1LittleO f := by
  let μ : Measure ℝ := ProbabilityTheory.cauchyMeasure 0 1
  let hfm : AEStronglyMeasurable (fun x => |f x|) μ := hf.aestronglyMeasurable
  let g₀ : ℝ → ℝ := hfm.mk (fun x => |f x|)
  let g : ℝ → ℝ := fun x => |g₀ x|
  have hfg : (fun x => |f x|) =ᵐ[μ] g := by
    filter_upwards [hfm.ae_eq_mk] with x hx
    dsimp [g, g₀]
    rw [← hx, abs_abs]
  have hg_int : Integrable g μ := hf.congr hfg
  have hg_meas : Measurable g := by
    exact hfm.stronglyMeasurable_mk.norm.measurable
  let s : ℝ → Set ℝ := fun A => {x | A < g x}
  have hs_meas : ∀ A, MeasurableSet (s A) := by
    intro A
    exact measurableSet_lt measurable_const hg_meas
  have hs_anti : Antitone s := by
    intro A B hAB x hx
    exact lt_of_le_of_lt hAB hx
  have hs_iInter : ⋂ A : ℝ, s A = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
    intro hx
    exact (lt_irrefl (g x)) (hx (g x))
  have htail : Tendsto (fun A : ℝ => ∫ x in s A, g x ∂μ) atTop (nhds 0) := by
    have h := MeasureTheory.tendsto_setIntegral_of_antitone hs_meas hs_anti
      (f := g) (μ := μ) ⟨0, hg_int.integrableOn⟩
    simpa [hs_iInter] using h
  let T : ℝ → ℝ := fun A => A * (μ {x | A < |f x|}).toReal
  have hmeasure (A : ℝ) : μ {x | A < |f x|} = μ (s A) := by
    apply MeasureTheory.measure_congr
    exact hfg.mono fun x hx => by
      apply propext
      change (A < |f x|) ↔ A < g x
      rw [show |f x| = g x from hx]
  have hnonneg : ∀ᶠ A : ℝ in atTop, 0 ≤ T A := by
    filter_upwards [eventually_ge_atTop 0] with A hA
    exact mul_nonneg hA ENNReal.toReal_nonneg
  have hbound : ∀ᶠ A : ℝ in atTop, T A ≤ ∫ x in s A, g x ∂μ := by
    filter_upwards [eventually_gt_atTop 0] with A hA
    have hlevel : {x | A ≤ (s A).indicator g x} = s A := by
      ext x
      change A ≤ (s A).indicator g x ↔ x ∈ s A
      by_cases hx : x ∈ s A
      · have hx' : A < g x := hx
        rw [Set.indicator_of_mem hx]
        exact ⟨fun _ => hx, fun _ => hx'.le⟩
      · simp [Set.indicator, hx, not_le.mpr hA]
    have hind_int : Integrable ((s A).indicator g) μ :=
      hg_int.integrableOn.integrable_indicator (hs_meas A)
    have hmark := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
      (μ := μ) (f := (s A).indicator g)
      (Filter.Eventually.of_forall fun x => by
        by_cases hx : x ∈ s A <;> simp [Set.indicator, hx, g])
      hind_int A
    rw [hlevel, MeasureTheory.integral_indicator (hs_meas A)] at hmark
    dsimp [T]
    rw [hmeasure A, ← Measure.real_def]
    exact hmark
  unfold PoissonWeakL1LittleO
  change Tendsto T atTop (nhds 0)
  exact squeeze_zero' hnonneg hbound htail

end

end GaloisForLFunctions.HTGeometry

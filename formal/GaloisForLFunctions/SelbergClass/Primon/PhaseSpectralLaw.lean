import GaloisForLFunctions.SelbergClass.Primon.SemicircleFock
import GaloisForLFunctions.HTGeometry.CarriedConclusion

/-!
# Probability laws of the prime Hecke coordinate

Push the normalized phase densities forward by `t ↦ 2 cos(πt)`. This gives
compact probability laws with the already computed moments. Compact moment
determinacy identifies the limiting law with the scalar free Fock spectral
law. Uniform convergence of the phase densities gives weak convergence of
the prime laws, and convergence of every continuous coordinate observable.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

private def phaseCoordinateMeasure (ρ : ℝ → ℝ) : Measure ℝ :=
  Measure.map (fun t => 2 * Real.cos (Real.pi * t))
    ((volume.restrict (Ioo (0 : ℝ) 1)).withDensity (fun t => ENNReal.ofReal (ρ t)))

private theorem phaseCoordinateMeasure_probability (ρ : ℝ → ℝ) (hc : Continuous ρ)
    (hn : ∀ t, 0 ≤ ρ t) (hm : (∫ t in Ioo (0 : ℝ) 1, ρ t) = 1) :
    IsProbabilityMeasure (phaseCoordinateMeasure ρ) := by
  have hi : IntegrableOn ρ (Ioo (0 : ℝ) 1) :=
    hc.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  constructor
  rw [phaseCoordinateMeasure, Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp only [preimage_univ]
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn), hm,
    ENNReal.ofReal_one]

private theorem integral_phaseCoordinateMeasure (ρ : ℝ → ℝ) (hc : Continuous ρ)
    (hn : ∀ t, 0 ≤ ρ t) (f : C(ℝ, ℝ)) :
    (∫ x, f x ∂phaseCoordinateMeasure ρ) =
      ∫ t in Ioo (0 : ℝ) 1, ρ t * f (2 * Real.cos (Real.pi * t)) := by
  rw [phaseCoordinateMeasure, integral_map (by fun_prop) f.continuous.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hc.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hn _), smul_eq_mul]

private theorem integrable_phaseCoordinateMeasure (ρ : ℝ → ℝ) (hc : Continuous ρ)
    (hn : ∀ t, 0 ≤ ρ t) (f : C(ℝ, ℝ)) : Integrable f (phaseCoordinateMeasure ρ) := by
  rw [phaseCoordinateMeasure, integrable_map_measure f.continuous.aestronglyMeasurable
    (by fun_prop), integrable_withDensity_iff hc.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hn _), Function.comp_apply]
  exact ((f.continuous.comp (by fun_prop)).mul hc).continuousOn.integrableOn_Icc.mono_set
    Ioo_subset_Icc_self

private theorem phaseCoordinateMeasure_carried (ρ : ℝ → ℝ) :
    phaseCoordinateMeasure ρ (Icc (-2) 2)ᶜ = 0 := by
  rw [phaseCoordinateMeasure, Measure.map_apply (by fun_prop) measurableSet_Icc.compl]
  have he : (fun t : ℝ => 2 * Real.cos (Real.pi * t)) ⁻¹' (Icc (-2) 2)ᶜ = ∅ := by
    ext t
    constructor
    · intro ht
      apply ht
      constructor
      · linarith only [Real.neg_one_le_cos (Real.pi * t)]
      · linarith only [Real.cos_le_one (Real.pi * t)]
    · intro ht
      exact False.elim ht
  rw [he, measure_empty]

/-- Probability law of the normalized prime Hecke coordinate. -/
def kestenSpectralLaw (p : Nat.Primes) : ProbabilityMeasure ℝ :=
  ⟨phaseCoordinateMeasure (kestenMcKayDensity p),
    phaseCoordinateMeasure_probability _ (continuous_kestenMcKayDensity p)
      (kestenMcKayDensity_nonneg p) (integral_kestenMcKayDensity p)⟩

/-- Semicircle probability law obtained from its explicit sine-square phase density. -/
def semicircleSpectralLaw : ProbabilityMeasure ℝ :=
  ⟨phaseCoordinateMeasure semicirclePhaseDensity,
    phaseCoordinateMeasure_probability _ (by unfold semicirclePhaseDensity; fun_prop)
      (fun t => by unfold semicirclePhaseDensity; positivity) integral_semicirclePhaseDensity⟩

/-- Every continuous prime coordinate observable is its explicit phase integral. -/
theorem integral_kestenSpectralLaw (p : Nat.Primes) (f : C(ℝ, ℝ)) :
    (∫ x, f x ∂(kestenSpectralLaw p : Measure ℝ)) =
      ∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * f (2 * Real.cos (Real.pi * t)) :=
  integral_phaseCoordinateMeasure _ (continuous_kestenMcKayDensity p)
    (kestenMcKayDensity_nonneg p) f

/-- Every continuous semicircle coordinate observable is its explicit phase integral. -/
theorem integral_semicircleSpectralLaw (f : C(ℝ, ℝ)) :
    (∫ x, f x ∂(semicircleSpectralLaw : Measure ℝ)) =
      ∫ t in Ioo (0 : ℝ) 1, semicirclePhaseDensity t * f (2 * Real.cos (Real.pi * t)) :=
  integral_phaseCoordinateMeasure _ (by unfold semicirclePhaseDensity; fun_prop)
    (fun t => by unfold semicirclePhaseDensity; positivity) f

/-- The prime spectral probability law realizes all the actual phase moments. -/
theorem kestenSpectralLaw_hasMoments (p : Nat.Primes) :
    HasHamburgerMoments (kestenMoment p) (kestenSpectralLaw p : Measure ℝ) := by
  intro n
  let f : C(ℝ, ℝ) := ⟨fun x => x ^ n, by fun_prop⟩
  refine ⟨integrable_phaseCoordinateMeasure _ (continuous_kestenMcKayDensity p)
    (kestenMcKayDensity_nonneg p) f, ?_⟩
  exact integral_kestenSpectralLaw p f

/-- The explicit semicircle probability law realizes all the computed limiting moments. -/
theorem semicircleSpectralLaw_hasMoments :
    HasHamburgerMoments semicircleMoment (semicircleSpectralLaw : Measure ℝ) := by
  intro n
  let f : C(ℝ, ℝ) := ⟨fun x => x ^ n, by fun_prop⟩
  refine ⟨integrable_phaseCoordinateMeasure _ (by unfold semicirclePhaseDensity; fun_prop)
    (fun t => by unfold semicirclePhaseDensity; positivity) f, ?_⟩
  exact integral_semicircleSpectralLaw f

/-- Every prime coordinate law is carried by the normalized Hecke interval. -/
theorem kestenSpectralLaw_carried (p : Nat.Primes) :
    (kestenSpectralLaw p : Measure ℝ) (Icc (-2) 2)ᶜ = 0 :=
  phaseCoordinateMeasure_carried _

/-- The explicit limiting law is carried by the semicircle interval. -/
theorem semicircleSpectralLaw_carried :
    (semicircleSpectralLaw : Measure ℝ) (Icc (-2) 2)ᶜ = 0 :=
  phaseCoordinateMeasure_carried _

/-- Compact moment determinacy identifies the explicit phase law with the scalar Fock law. -/
theorem semicircleSpectralLaw_eq_scalarFockSpectralLaw :
    semicircleSpectralLaw = scalarFockSpectralLaw := by
  have he : (semicircleSpectralLaw : Measure ℝ) = (scalarFockSpectralLaw : Measure ℝ) := by
    apply _root_.HTGeometry.measure_eq_of_moments_eq_of_one_carried
      (s := semicircleMoment) (c := 0) (r := 2) (by norm_num)
      (by simpa only [zero_sub, zero_add] using semicircleSpectralLaw_carried)
    · exact fun n => (semicircleSpectralLaw_hasMoments n).2.symm
    · exact fun n => (semicircleSpectralLaw_hasMoments n).1
    · exact fun n => (scalarFockSpectralLaw_hasMoments n).2.symm
    · exact fun n => (scalarFockSpectralLaw_hasMoments n).1
  exact Subtype.ext he

/-- All continuous coordinate observables converge from the prime law to the scalar Fock law. -/
theorem tendsto_integral_kestenSpectralLaw (f : C(ℝ, ℝ)) :
    Tendsto (fun p => ∫ x, f x ∂(kestenSpectralLaw p : Measure ℝ)) cofinite
      (𝓝 (∫ x, f x ∂(scalarFockSpectralLaw : Measure ℝ))) := by
  rw [← semicircleSpectralLaw_eq_scalarFockSpectralLaw, integral_semicircleSpectralLaw]
  simp_rw [integral_kestenSpectralLaw]
  exact tendsto_kestenObservableAverage
    ⟨fun t => f (2 * Real.cos (Real.pi * t)), f.continuous.comp (by fun_prop)⟩

/-- The prime coordinate probability laws converge weakly to the scalar free Fock spectral law. -/
theorem tendsto_kestenSpectralLaw :
    Tendsto kestenSpectralLaw cofinite (𝓝 scalarFockSpectralLaw) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  exact tendsto_integral_kestenSpectralLaw ⟨f, f.continuous⟩

end
end GaloisForLFunctions.SelbergClass.Primon

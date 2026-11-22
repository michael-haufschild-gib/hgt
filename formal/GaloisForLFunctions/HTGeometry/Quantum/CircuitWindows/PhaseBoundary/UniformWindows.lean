import GaloisForLFunctions.HTGeometry.OneSidedCaptureDensity
import GaloisForLFunctions.HTGeometry.BohrMultiFejerOperator

/-! # Phase occupation with arbitrary length-dependent observation origins -/
open Set Filter MeasureTheory Topology
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary
noncomputable section
variable {I : Type} [Fintype I]

private def shiftedLaw (ω : I → ℝ) (a T : ℝ) : ProbabilityMeasure (UnitAddTorus I) :=
  (windowProbabilityMeasure T).map (show AEMeasurable (fun t : ℝ => finiteClockPhasePoint ω (a+t)) _ from
    ((finiteClockPhasePoint_continuous ω).comp (continuous_const.add continuous_id)).aemeasurable)

private theorem shifted_character (ω : I → ℝ) (a T : ℝ) (m : I → ℤ) :
    (∫ x, UnitAddTorus.mFourier m x ∂(shiftedLaw ω a T : Measure _)) =
      expChar (finiteTorusCharacterDetuning m ω) a *
        (∫ x, UnitAddTorus.mFourier m x ∂(clockPhaseWindowLaw ω T : Measure _)) := by
  have ha : Continuous (fun t : ℝ => finiteClockPhasePoint ω (a+t)) :=
    (finiteClockPhasePoint_continuous ω).comp (continuous_const.add continuous_id)
  rw [shiftedLaw,clockPhaseWindowLaw,ProbabilityMeasure.toMeasure_map,
    ProbabilityMeasure.toMeasure_map,integral_map ha.aemeasurable (UnitAddTorus.mFourier m).continuous.aestronglyMeasurable,
    integral_map (finiteClockPhasePoint_continuous ω).aemeasurable (UnitAddTorus.mFourier m).continuous.aestronglyMeasurable]
  simp_rw [mFourier_finiteClockPhasePoint_expChar,expChar_add_arg]
  exact integral_const_mul _ _

/-- Haar convergence holds even for origins chosen arbitrarily as the
observation length changes. Translating time multiplies each nonconstant
Fourier coefficient by a number of unit modulus. -/
private theorem shifted_haar (ω : I → ℝ) (hi : RationallyIndependentFrequency ω) (a : ℝ → ℝ) :
    Tendsto (fun T => shiftedLaw ω (a T) T) atTop (𝓝 (finiteTorusHaarProbabilityMeasure I)) := by
  classical
  apply probabilityMeasure_tendsto_of_mFourier_integral_tendsto
  intro m
  rw [finiteTorusHaarProbabilityMeasure_mFourier_integral]
  by_cases hm : m=0
  · subst m
    simp [UnitAddTorus.mFourier_zero]
  rw [if_neg hm]
  have h := tendsto_integral_mFourier_clockPhaseWindowLaw ω m
  rw [if_neg (fun hz => hm (hi m hz))] at h
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [shifted_character,norm_mul,norm_expChar,one_mul] using
    (tendsto_zero_iff_norm_tendsto_zero.mp h)

/-- Probability of a measurable time target under a translated uniform
observation equals its Lebesgue fraction in the physical interval. -/
private theorem shifted_fraction (E : Set ℝ) (hE : MeasurableSet E) (a T : ℝ) (hT : 0<T) :
    (windowProbabilityMeasure T : Measure ℝ).real ((fun t : ℝ => a+t) ⁻¹' E) =
      volume.real (E ∩ Icc a (a+T))/T := by
  let τ (t : ℝ) := a+t
  have hτ : Measurable τ := measurable_const.add measurable_id
  have heq : (τ ⁻¹' E) ∩ Ioc 0 T = τ ⁻¹' (E ∩ Ioc a (a+T)) := by
    ext t
    change (_ ∧ 0<t ∧ t≤T) ↔ (_ ∧ a<a+t ∧ a+t≤a+T)
    simp only [mem_preimage,lt_add_iff_pos_right,add_le_add_iff_left]
  have hm : volume (τ ⁻¹' (E ∩ Ioc a (a+T))) = volume (E ∩ Ioc a (a+T)) :=
    (measurePreserving_add_left volume a).measure_preimage (hE.inter measurableSet_Ioc).nullMeasurableSet
  have he : volume.real (E ∩ Ioc a (a+T)) = volume.real (E ∩ Icc a (a+T)) :=
    measureReal_congr (ae_eq_set_inter (Filter.EventuallyEq.rfl) Ioc_ae_eq_Icc)
  change (((ENNReal.ofReal (windowLength T))⁻¹ • volume.restrict (Ioc 0 (windowLength T))) : Measure ℝ).real (τ ⁻¹' E) = _
  rw [windowLength_eq hT,Measure.real,Measure.smul_apply,Measure.restrict_apply (hE.preimage hτ),
    heq,hm,smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_ofReal hT.le]
  change T⁻¹ * volume.real (E ∩ Ioc a (a+T)) = _
  rw [he,div_eq_inv_mul]

/-- Every Haar-continuity set has an exact time fraction on arbitrarily
translated long windows. The origins may depend on the length. -/
theorem uniform_phase_fraction (ω : I → ℝ) (hi : RationallyIndependentFrequency ω)
    (A : Set (UnitAddTorus I)) (hA : MeasurableSet A) (hb : volume (frontier A)=0) (a : ℝ → ℝ) :
    Tendsto (fun T => volume.real (finiteClockPhasePoint ω ⁻¹' A ∩ Icc (a T) (a T+T))/T)
      atTop (𝓝 (volume.real A)) := by
  have hnull : (finiteTorusHaarProbabilityMeasure I : Measure _) (frontier A)=0 := by
    rwa [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume]
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' (shifted_haar ω hi a) hnull
  rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume] at h
  have ht := (ENNReal.tendsto_toReal (measure_ne_top volume A)).comp h
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  change (shiftedLaw ω (a T) T : Measure _).real A = _
  have ha : Continuous (fun t : ℝ => finiteClockPhasePoint ω (a T+t)) :=
    (finiteClockPhasePoint_continuous ω).comp (continuous_const.add continuous_id)
  rw [shiftedLaw,Measure.real,ProbabilityMeasure.toMeasure_map,Measure.map_apply ha.measurable hA]
  exact shifted_fraction _ (hA.preimage (finiteClockPhasePoint_continuous ω).measurable) _ _ hT

end
end GaloisForLFunctions.HTGeometry.PhaseBoundary

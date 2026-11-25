import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.PhaseLaws.WeightedDecay
import GaloisForLFunctions.HTGeometry.ActivePhaseLattice

/-! # A single late phase observation with a disorder-dependent origin -/

open Filter Set MeasureTheory Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.PhaseLaws
noncomputable section
variable {X I : Type*} [MeasurableSpace X] [Fintype I]

/-- The torus origin and the frequencies use the same draw. -/
def translatedSnapshot (μ : ProbabilityMeasure X) (f : X→I→ℝ) (hf : Measurable f)
    (u : X→UnitAddTorus I) (hu : Measurable u) (t : ℝ) : ProbabilityMeasure (UnitAddTorus I) :=
  μ.map (hu.add (measurable_pi_lambda _ fun i => (AddCircle.continuous_mk' (1:ℝ)).measurable.comp
    ((((measurable_pi_apply i).comp hf).const_mul t).div_const (2*Real.pi)))).aemeasurable

/-- A measurable origin chosen from the full coupling vector preserves
the Haar limit. Each character of the translation has unit modulus, so
it is an admissible weight in the scalar Fourier decay estimate. -/
theorem translatedSnapshot_haar (μ : ProbabilityMeasure X) (f : X→I→ℝ) (hf : Measurable f)
    (u : X→UnitAddTorus I) (hu : Measurable u)
    (hac : ∀ m : I→ℤ, m≠0 →
      (μ : Measure X).map (fun x => -finiteTorusCharacterDetuning m (f x))≪volume) :
    Tendsto (translatedSnapshot μ f hf u hu) (cocompact ℝ) (𝓝 (finiteTorusHaarProbabilityMeasure I)) := by
  classical
  apply probabilityMeasure_tendsto_of_mFourier_integral_tendsto
  intro m
  rw [finiteTorusHaarProbabilityMeasure_mFourier_integral]
  by_cases hm : m=0
  · subst m
    simp only [if_pos rfl,UnitAddTorus.mFourier_zero,ContinuousMap.one_apply,integral_const,probReal_univ,one_smul]
    exact tendsto_const_nhds
  rw [if_neg hm]
  let A (x : X) := -finiteTorusCharacterDetuning m (f x)
  have hA : Measurable A := (Finset.measurable_fun_sum _ fun i _ =>
    (((measurable_pi_apply i).comp hf).const_mul (m i:ℝ))).neg
  let g (x : X) := UnitAddTorus.mFourier m (u x)
  have hg : Measurable g := (UnitAddTorus.mFourier m).continuous.measurable.comp hu
  have hn (x : X) : ‖g x‖=1 := by
    simp only [g,UnitAddTorus.mFourier,ContinuousMap.coe_mk,norm_prod,fourier_apply,Circle.norm_coe,
      Finset.prod_const_one]
  apply (phase_weight_decay (μ : Measure X) A hA (hac m hm) g hg hn).congr
  intro t
  rw [translatedSnapshot,ProbabilityMeasure.toMeasure_map,integral_map _ (UnitAddTorus.mFourier m).continuous.aestronglyMeasurable]
  · apply integral_congr_ae
    filter_upwards with x
    change g x*oscillation (A x) t=UnitAddTorus.mFourier m (u x+finiteClockPhasePoint (f x) t)
    rw [mFourier_add_point,mFourier_finiteClockPhasePoint]
    simp only [g,A,oscillation,mul_neg,Complex.ofReal_neg,neg_neg]
  · exact (hu.add (measurable_pi_lambda _ fun i => (AddCircle.continuous_mk' (1:ℝ)).measurable.comp
      ((((measurable_pi_apply i).comp hf).const_mul t).div_const (2*Real.pi)))).aemeasurable

#print axioms translatedSnapshot_haar
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.PhaseLaws

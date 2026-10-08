import GaloisForLFunctions.RHTower.WeilPaperNativeEnergyTopology

/-!
# Continuous realification of native spectral laws

Canonical real-test splitting preserves full energy and averages a spectral law
with its reflection. The averaging formula proves weak continuity, independently
of which finite mixture presents the native law.
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Canonical real-test splitting, directly on normalized complex-null mixtures. -/
def paperSymmetricNativeMixture (c : ComplexNullMixture) : ComplexNullMixture :=
  paperSplitRealComplexNullMixture ⟨c.1, defect_complexNullMixture c⟩

@[simp] theorem energy_paperSymmetricNativeMixture (c : ComplexNullMixture) :
    energy (paperSymmetricNativeMixture c).1.1 = energy c.1.1 :=
  energy_paperSplitRealMixture c.1.1

/-- Every surviving test is real-valued. -/
theorem paperSymmetricNativeMixture_real (c : ComplexNullMixture) :
    ∀ f, (paperSymmetricNativeMixture c).1.1 f ≠ 0 → ∀ x, (f.1 x).im = 0 :=
  paperSplitRealMixture_real c.1.1

theorem map_neg_spectralProbability_paperSymmetricNativeMixture (c : ComplexNullMixture) :
    Measure.map (fun ξ : ℝ => -ξ)
      (spectralProbability (paperSymmetricNativeMixture c).1 : Measure ℝ) =
        (spectralProbability (paperSymmetricNativeMixture c).1 : Measure ℝ) :=
  map_neg_spectralProbability_paperSplitRealNormalizedMixture c.1

theorem map_neg_spectralRepresentingMeasure_paperSymmetricNativeMixture
    (c : ComplexNullMixture) :
    Measure.map (fun z : PrimePhaseSpace => -z)
      ((spectralRepresentingMeasure (paperSymmetricNativeMixture c)).1 : Measure PrimePhaseSpace) =
        ((spectralRepresentingMeasure (paperSymmetricNativeMixture c)).1 : Measure PrimePhaseSpace) :=
  map_neg_spectralRepresentingMeasure_paperSplitRealComplexNullMixture
    ⟨c.1, defect_complexNullMixture c⟩

/-- Realification depends only on the complete native law. -/
theorem spectralRepresentingMeasure_paperSymmetricNativeMixture_congr
    (c d : ComplexNullMixture) (h : spectralRepresentingMeasure c = spectralRepresentingMeasure d) :
    spectralRepresentingMeasure (paperSymmetricNativeMixture c) =
      spectralRepresentingMeasure (paperSymmetricNativeMixture d) := by
  have hs : mixtureSample c.1.1 = mixtureSample d.1.1 :=
    (spectralProbability_eq_iff_mixtureSample_eq _ _).mp
      ((spectralTorusProbability_eq_iff_spectralProbability_eq _ _).mp
        (congrArg Subtype.val h))
  apply Subtype.ext
  apply (spectralTorusProbability_eq_iff_spectralProbability_eq _ _).mpr
  apply (spectralProbability_eq_iff_mixtureSample_eq _ _).mpr
  funext y
  change mixtureSample (paperSplitRealMixture c.1.1) y =
    mixtureSample (paperSplitRealMixture d.1.1) y
  rw [mixtureSample_paperSplitRealMixture, mixtureSample_paperSplitRealMixture, hs]

/-- Repeated real-test splitting fixes the actual representing law. -/
theorem spectralRepresentingMeasure_paperSymmetricNativeMixture_idempotent
    (c : ComplexNullMixture) :
    spectralRepresentingMeasure (paperSymmetricNativeMixture (paperSymmetricNativeMixture c)) =
      spectralRepresentingMeasure (paperSymmetricNativeMixture c) := by
  apply Subtype.ext
  apply (spectralTorusProbability_eq_iff_spectralProbability_eq _ _).mpr
  exact spectralProbability_paperSplitRealNormalizedMixture_idempotent c.1

/-- Every bounded phase expectation is replaced by its exact inversion average. -/
theorem integral_spectralRepresentingMeasure_paperSymmetricNativeMixture
    (c : ComplexNullMixture) (F : PrimePhaseSpace →ᵇ ℝ) :
    (∫ z, F z ∂((spectralRepresentingMeasure (paperSymmetricNativeMixture c)).1 :
      Measure PrimePhaseSpace)) = (1/2 : ℝ) *
        ((∫ z, F z ∂((spectralRepresentingMeasure c).1 : Measure PrimePhaseSpace)) +
          ∫ z, F (-z) ∂((spectralRepresentingMeasure c).1 : Measure PrimePhaseSpace)) := by
  change (∫ z, F z ∂(spectralTorusProbability (paperSplitRealNormalizedMixture c.1) :
    Measure PrimePhaseSpace)) = _
  rw [spectralTorusProbability_paperSplitRealNormalizedMixture, integral_smul_measure,
    integral_add_measure (F.integrable _) (F.integrable _),
    integral_map measurable_neg.aemeasurable F.continuous.measurable.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1/2), smul_eq_mul]
  rfl

/-- Canonical real-test splitting preserves arbitrary weak limits of native laws. -/
theorem tendsto_spectralRepresentingMeasure_paperSymmetricNativeMixture
    {α : Type*} {l : Filter α} {c : α → ComplexNullMixture} {a : ComplexNullMixture}
    (h : Tendsto (fun i => spectralRepresentingMeasure (c i)) l
      (𝓝 (spectralRepresentingMeasure a))) :
    Tendsto (fun i => spectralRepresentingMeasure (paperSymmetricNativeMixture (c i))) l
      (𝓝 (spectralRepresentingMeasure (paperSymmetricNativeMixture a))) := by
  apply tendsto_subtype_rng.mpr
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  have hp := (tendsto_subtype_rng.mp h)
  have hF := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hp F
  have hG := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hp
    (F.compContinuous ⟨fun z : PrimePhaseSpace => -z, continuous_neg⟩)
  simpa only [integral_spectralRepresentingMeasure_paperSymmetricNativeMixture,
    BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk] using
      (tendsto_const_nhds.mul (hF.add hG))

end RHTower.WeilWorkPBAP

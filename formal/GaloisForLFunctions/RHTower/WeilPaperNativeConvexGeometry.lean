import GaloisForLFunctions.RHTower.WeilPaperNativeRealificationRetract
import Mathlib.Topology.UnitInterval

/-!
# Intrinsic continuous convex interpolation of native spectral laws

Positive normalized complex-null mixtures are closed under convex interpolation.
The resulting law depends only on the two endpoint laws. Its bounded spectral
expectations interpolate affinely, proving joint weak continuity even when both
endpoints vary. Full energy also interpolates exactly.
-/

open MeasureTheory Filter Set Topology
open scoped BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Complete native laws and complete autocorrelation kernels carry identical equality data. -/
theorem spectralRepresentingMeasure_eq_iff_mixtureSample_eq (a b : ComplexNullMixture) :
    spectralRepresentingMeasure a = spectralRepresentingMeasure b ↔
      mixtureSample a.1.1 = mixtureSample b.1.1 := by
  constructor
  · intro h
    exact (spectralProbability_eq_iff_mixtureSample_eq _ _).mp
      ((spectralTorusProbability_eq_iff_spectralProbability_eq _ _).mp
        (congrArg Subtype.val h))
  · intro h
    apply Subtype.ext
    exact (spectralTorusProbability_eq_iff_spectralProbability_eq _ _).mpr
      ((spectralProbability_eq_iff_mixtureSample_eq _ _).mpr h)

/-- Convex interpolation depends only on its endpoint laws, not their test representatives. -/
theorem spectralRepresentingMeasure_paperComplexNullSegment_congr
    (a b c d : ComplexNullMixture)
    (ha : spectralRepresentingMeasure a = spectralRepresentingMeasure c)
    (hb : spectralRepresentingMeasure b = spectralRepresentingMeasure d)
    (t : Set.Icc (0 : ℝ) 1) :
    spectralRepresentingMeasure (paperComplexNullSegment a b t) =
      spectralRepresentingMeasure (paperComplexNullSegment c d t) := by
  apply (spectralRepresentingMeasure_eq_iff_mixtureSample_eq _ _).mpr
  funext y
  change mixtureSample (paperNormalizedSegment a.1 b.1 t).1 y =
    mixtureSample (paperNormalizedSegment c.1 d.1 t).1 y
  rw [mixtureSample_paperNormalizedSegment, mixtureSample_paperNormalizedSegment,
    (spectralRepresentingMeasure_eq_iff_mixtureSample_eq _ _).mp ha,
    (spectralRepresentingMeasure_eq_iff_mixtureSample_eq _ _).mp hb]

/-- Bounded torus expectations are affine along native convex segments. -/
theorem integral_spectralRepresentingMeasure_paperComplexNullSegment
    (F : PrimePhaseSpace →ᵇ ℝ) (a b : ComplexNullMixture) (t : Set.Icc (0 : ℝ) 1) :
    (∫ z, F z ∂((spectralRepresentingMeasure (paperComplexNullSegment a b t)).1 :
      Measure PrimePhaseSpace)) =
        (1-t.1) * (∫ z, F z ∂((spectralRepresentingMeasure a).1 : Measure PrimePhaseSpace)) +
          t.1 * (∫ z, F z ∂((spectralRepresentingMeasure b).1 : Measure PrimePhaseSpace)) := by
  have hmap (c : NormalizedMixture) :
      (∫ z, F z ∂(spectralTorusProbability c : Measure PrimePhaseSpace)) =
        ∫ ξ, F (primeSpectralPoint ξ) ∂(spectralProbability c : Measure ℝ) := by
    change (∫ z, F z ∂Measure.map primeSpectralPoint (spectralProbability c : Measure ℝ)) = _
    exact integral_map continuous_primeSpectralPoint.measurable.aemeasurable
      F.continuous.measurable.aestronglyMeasurable
  change (∫ z, F z ∂(spectralTorusProbability (paperNormalizedSegment a.1 b.1 t) :
    Measure PrimePhaseSpace)) =
      (1-t.1) * (∫ z, F z ∂(spectralTorusProbability a.1 : Measure PrimePhaseSpace)) +
        t.1 * (∫ z, F z ∂(spectralTorusProbability b.1 : Measure PrimePhaseSpace))
  rw [hmap, hmap, hmap]
  exact integral_spectralProbability_paperNormalizedSegment
    (F.compContinuous ⟨primeSpectralPoint, continuous_primeSpectralPoint⟩) a.1 b.1 t

/-- Convex interpolation intrinsically on the actual native law space. -/
def paperNativeConvexCombination (μ ν : Set.range spectralRepresentingMeasure)
    (t : Set.Icc (0 : ℝ) 1) : Set.range spectralRepresentingMeasure :=
  ⟨spectralRepresentingMeasure
    (paperComplexNullSegment (Classical.choose μ.2) (Classical.choose ν.2) t), Set.mem_range_self _⟩

@[simp] theorem paperNativeConvexCombination_apply (a b : ComplexNullMixture)
    (t : Set.Icc (0 : ℝ) 1) :
    paperNativeConvexCombination
      ⟨spectralRepresentingMeasure a, Set.mem_range_self a⟩
      ⟨spectralRepresentingMeasure b, Set.mem_range_self b⟩ t =
        ⟨spectralRepresentingMeasure (paperComplexNullSegment a b t), Set.mem_range_self _⟩ := by
  apply Subtype.ext
  exact spectralRepresentingMeasure_paperComplexNullSegment_congr _ _ a b
    (Classical.choose_spec (Set.mem_range_self a)) (Classical.choose_spec (Set.mem_range_self b)) t

/-- Intrinsic full energy is affine on every native convex segment. -/
theorem paperNativeSpectralEnergy_convexCombination
    (μ ν : Set.range spectralRepresentingMeasure) (t : Set.Icc (0 : ℝ) 1) :
    paperNativeSpectralEnergy (paperNativeConvexCombination μ ν t) =
      (1-t.1)*paperNativeSpectralEnergy μ + t.1*paperNativeSpectralEnergy ν := by
  rcases μ with ⟨μ, a, rfl⟩
  rcases ν with ⟨ν, b, rfl⟩
  rw [paperNativeConvexCombination_apply, paperNativeSpectralEnergy_apply,
    paperNativeSpectralEnergy_apply, paperNativeSpectralEnergy_apply]
  change energy (paperNormalizedSegment a.1 b.1 t).1 = _
  simpa only [smul_eq_mul] using paperNormalizedSegment_observe energy a.1 b.1 t

/-- Every bounded expectation is affine in the intrinsic convex operation. -/
theorem integral_paperNativeConvexCombination (F : PrimePhaseSpace →ᵇ ℝ)
    (μ ν : Set.range spectralRepresentingMeasure) (t : Set.Icc (0 : ℝ) 1) :
    (∫ z, F z ∂((paperNativeConvexCombination μ ν t).1.1 : Measure PrimePhaseSpace)) =
      (1-t.1)*(∫ z, F z ∂(μ.1.1 : Measure PrimePhaseSpace)) +
        t.1*(∫ z, F z ∂(ν.1.1 : Measure PrimePhaseSpace)) := by
  rcases μ with ⟨μ, a, rfl⟩
  rcases ν with ⟨ν, b, rfl⟩
  rw [paperNativeConvexCombination_apply]
  exact integral_spectralRepresentingMeasure_paperComplexNullSegment F a b t

/-- Both endpoint laws and the interpolation weight may vary under weak convergence. -/
theorem tendsto_paperNativeConvexCombination
    {α : Type*} {l : Filter α}
    {μ ν : α → Set.range spectralRepresentingMeasure} {t : α → Set.Icc (0 : ℝ) 1}
    {μ₀ ν₀ : Set.range spectralRepresentingMeasure} {t₀ : Set.Icc (0 : ℝ) 1}
    (hμ : Tendsto μ l (𝓝 μ₀)) (hν : Tendsto ν l (𝓝 ν₀)) (ht : Tendsto t l (𝓝 t₀)) :
    Tendsto (fun i => paperNativeConvexCombination (μ i) (ν i) (t i)) l
      (𝓝 (paperNativeConvexCombination μ₀ ν₀ t₀)) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_subtype_rng.mpr
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  have hA := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (tendsto_subtype_rng.mp (tendsto_subtype_rng.mp hμ)) F
  have hB := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (tendsto_subtype_rng.mp (tendsto_subtype_rng.mp hν)) F
  have hT := (continuous_subtype_val.tendsto t₀).comp ht
  simpa only [integral_paperNativeConvexCombination, Function.comp_def] using
    ((tendsto_const_nhds.sub hT).mul hA).add (hT.mul hB)

/-- Joint continuity holds on the full native law space, without an energy bound. -/
theorem continuous_paperNativeConvexCombination :
    Continuous (fun p : Set.Icc (0 : ℝ) 1 ×
      Set.range spectralRepresentingMeasure × Set.range spectralRepresentingMeasure =>
        paperNativeConvexCombination p.2.1 p.2.2 p.1) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact tendsto_paperNativeConvexCombination
    ((continuous_fst.comp continuous_snd).tendsto p)
    ((continuous_snd.comp continuous_snd).tendsto p) (continuous_fst.tendsto p)

@[simp] theorem paperNativeConvexCombination_zero (μ ν : Set.range spectralRepresentingMeasure) :
    paperNativeConvexCombination μ ν 0 = μ := by
  rcases μ with ⟨μ, a, rfl⟩
  rcases ν with ⟨ν, b, rfl⟩
  rw [paperNativeConvexCombination_apply]
  apply Subtype.ext
  apply (spectralRepresentingMeasure_eq_iff_mixtureSample_eq _ _).mpr
  funext y
  change mixtureSample (paperNormalizedSegment a.1 b.1 0).1 y = _
  rw [mixtureSample_paperNormalizedSegment]
  simp

@[simp] theorem paperNativeConvexCombination_one (μ ν : Set.range spectralRepresentingMeasure) :
    paperNativeConvexCombination μ ν 1 = ν := by
  rcases μ with ⟨μ, a, rfl⟩
  rcases ν with ⟨ν, b, rfl⟩
  rw [paperNativeConvexCombination_apply]
  apply Subtype.ext
  apply (spectralRepresentingMeasure_eq_iff_mixtureSample_eq _ _).mpr
  funext y
  change mixtureSample (paperNormalizedSegment a.1 b.1 1).1 y = _
  rw [mixtureSample_paperNormalizedSegment]
  simp

@[simp] theorem paperNativeConvexCombination_self (μ : Set.range spectralRepresentingMeasure)
    (t : Set.Icc (0 : ℝ) 1) : paperNativeConvexCombination μ μ t = μ := by
  rcases μ with ⟨μ, a, rfl⟩
  rw [paperNativeConvexCombination_apply]
  apply Subtype.ext
  apply (spectralRepresentingMeasure_eq_iff_mixtureSample_eq _ _).mpr
  funext y
  change mixtureSample (paperNormalizedSegment a.1 a.1 t).1 y = _
  rw [mixtureSample_paperNormalizedSegment, ← add_smul, sub_add_cancel, one_smul]

end RHTower.WeilWorkPBAP

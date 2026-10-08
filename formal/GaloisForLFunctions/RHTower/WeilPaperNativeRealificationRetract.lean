import GaloisForLFunctions.RHTower.WeilPaperRealificationContinuity

/-!
# Real spectral laws form a closed retract of the native image

Realification is an intrinsic continuous idempotent on complete native laws. It
preserves full energy. Its image is exactly the native laws admitting real-valued
test representatives, and this image is closed within the native law space.
-/

open MeasureTheory Filter Set Topology
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Intrinsic realification of the complete native law. -/
def paperNativeRealification (μ : Set.range spectralRepresentingMeasure) :
    Set.range spectralRepresentingMeasure :=
  ⟨spectralRepresentingMeasure (paperSymmetricNativeMixture (Classical.choose μ.2)),
    Set.mem_range_self _⟩

@[simp] theorem paperNativeRealification_apply (c : ComplexNullMixture) :
    paperNativeRealification ⟨spectralRepresentingMeasure c, Set.mem_range_self c⟩ =
      ⟨spectralRepresentingMeasure (paperSymmetricNativeMixture c), Set.mem_range_self _⟩ := by
  apply Subtype.ext
  exact spectralRepresentingMeasure_paperSymmetricNativeMixture_congr _ c
    (Classical.choose_spec (Set.mem_range_self c))

/-- Realification loses no full energy. -/
@[simp] theorem paperNativeSpectralEnergy_realification
    (μ : Set.range spectralRepresentingMeasure) :
    paperNativeSpectralEnergy (paperNativeRealification μ) = paperNativeSpectralEnergy μ := by
  rcases μ with ⟨μ, c, rfl⟩
  simp only [paperNativeRealification_apply, paperNativeSpectralEnergy_apply,
    energy_paperSymmetricNativeMixture]

/-- The intrinsic realification map is weakly continuous. -/
theorem continuous_paperNativeRealification : Continuous paperNativeRealification := by
  apply continuous_iff_continuousAt.mpr
  intro μ
  apply tendsto_subtype_rng.mpr
  let c (ν : Set.range spectralRepresentingMeasure) : ComplexNullMixture := Classical.choose ν.2
  have hc (ν : Set.range spectralRepresentingMeasure) : spectralRepresentingMeasure (c ν) = ν.1 :=
    Classical.choose_spec ν.2
  have h : Tendsto (fun ν => spectralRepresentingMeasure (c ν)) (𝓝 μ)
      (𝓝 (spectralRepresentingMeasure (c μ))) := by
    simpa only [hc] using
      (continuous_subtype_val : Continuous (fun ν : Set.range spectralRepresentingMeasure => ν.1)).tendsto μ
  exact tendsto_spectralRepresentingMeasure_paperSymmetricNativeMixture h

/-- The realification image is fixed pointwise after one application. -/
theorem paperNativeRealification_idempotent (μ : Set.range spectralRepresentingMeasure) :
    paperNativeRealification (paperNativeRealification μ) = paperNativeRealification μ := by
  rcases μ with ⟨μ, c, rfl⟩
  simp only [paperNativeRealification_apply]
  exact Subtype.ext (spectralRepresentingMeasure_paperSymmetricNativeMixture_idempotent c)

/-- The image is exactly the intrinsic fixed-point set. -/
theorem range_paperNativeRealification_eq :
    Set.range paperNativeRealification = {μ | paperNativeRealification μ = μ} := by
  ext μ
  constructor
  · rintro ⟨ν, rfl⟩
    exact paperNativeRealification_idempotent ν
  · intro h
    exact ⟨μ, h⟩

/-- Realification fixes every law already represented by real-valued tests. -/
theorem spectralRepresentingMeasure_paperSymmetricNativeMixture_of_real
    (c : ComplexNullMixture) (hc : ∀ f, c.1.1 f ≠ 0 → ∀ x, (f.1 x).im = 0) :
    spectralRepresentingMeasure (paperSymmetricNativeMixture c) = spectralRepresentingMeasure c := by
  apply Subtype.ext
  apply (spectralTorusProbability_eq_iff_spectralProbability_eq _ _).mpr
  change spectralProbability (paperSplitRealNormalizedMixture c.1) = spectralProbability c.1
  rw [spectralProbability_paperSplitRealNormalizedMixture_eq_realification]
  apply ProbabilityMeasure.toMeasure_injective
  change volume.withDensity _ = volume.withDensity _
  congr 1
  funext ξ
  apply congrArg ENNReal.ofReal
  change mixtureSpectralDensity (paperRealMixture c.1.1) ξ = mixtureSpectralDensity c.1.1 ξ
  rw [mixtureSpectralDensity_paperRealMixture, mixtureSpectralDensity_neg_of_real c.1.1 hc]
  ring

/-- Exactly the native laws admitting real-valued test representatives lie in the image. -/
theorem mem_range_paperNativeRealification_iff (μ : Set.range spectralRepresentingMeasure) :
    μ ∈ Set.range paperNativeRealification ↔
      ∃ c : ComplexNullMixture, μ.1 = spectralRepresentingMeasure c ∧
        ∀ f, c.1.1 f ≠ 0 → ∀ x, (f.1 x).im = 0 := by
  rcases μ with ⟨μ, a, rfl⟩
  rw [range_paperNativeRealification_eq]
  constructor
  · intro h
    refine ⟨paperSymmetricNativeMixture a, ?_, paperSymmetricNativeMixture_real a⟩
    exact (congrArg Subtype.val ((paperNativeRealification_apply a).symm.trans h)).symm
  · rintro ⟨c, hac, hc⟩
    change paperNativeRealification _ = _
    rw [paperNativeRealification_apply]
    apply Subtype.ext
    exact (spectralRepresentingMeasure_paperSymmetricNativeMixture_congr a c hac).trans
      ((spectralRepresentingMeasure_paperSymmetricNativeMixture_of_real c hc).trans hac.symm)

/-- A native law is fixed by realification exactly when its torus probability is inversion-invariant. -/
theorem paperNativeRealification_eq_iff_inversion (μ : Set.range spectralRepresentingMeasure) :
    paperNativeRealification μ = μ ↔
      Measure.map (fun z : PrimePhaseSpace => -z) (μ.1.1 : Measure PrimePhaseSpace) =
        (μ.1.1 : Measure PrimePhaseSpace) := by
  rcases μ with ⟨μ, c, rfl⟩
  rw [paperNativeRealification_apply]
  constructor
  · intro h
    have he := congrArg (fun ν : Set.range spectralRepresentingMeasure =>
      (ν.1.1 : Measure PrimePhaseSpace)) h
    change ((spectralRepresentingMeasure (paperSymmetricNativeMixture c)).1 :
      Measure PrimePhaseSpace) = ((spectralRepresentingMeasure c).1 : Measure PrimePhaseSpace) at he
    rw [← he]
    exact map_neg_spectralRepresentingMeasure_paperSymmetricNativeMixture c
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    apply ProbabilityMeasure.toMeasure_injective
    change (spectralTorusProbability (paperSplitRealNormalizedMixture c.1) :
      Measure PrimePhaseSpace) = (spectralTorusProbability c.1 : Measure PrimePhaseSpace)
    change Measure.map (fun z : PrimePhaseSpace => -z)
      (spectralTorusProbability c.1 : Measure PrimePhaseSpace) =
        (spectralTorusProbability c.1 : Measure PrimePhaseSpace) at h
    rw [spectralTorusProbability_paperSplitRealNormalizedMixture, h,
      smul_add, ← add_smul]
    have hh : ENNReal.ofReal (1/2 : ℝ) + ENNReal.ofReal (1/2 : ℝ) = 1 := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      norm_num
    rw [hh, one_smul]

/-- Real-test representability is precisely intrinsic inversion symmetry of a native law. -/
theorem mem_range_paperNativeRealification_iff_inversion
    (μ : Set.range spectralRepresentingMeasure) :
    μ ∈ Set.range paperNativeRealification ↔
      Measure.map (fun z : PrimePhaseSpace => -z) (μ.1.1 : Measure PrimePhaseSpace) =
        (μ.1.1 : Measure PrimePhaseSpace) := by
  rw [range_paperNativeRealification_eq]
  exact paperNativeRealification_eq_iff_inversion μ

/-- The real-test image is a closed subspace of actual native laws. -/
theorem isClosed_range_paperNativeRealification : IsClosed (Set.range paperNativeRealification) := by
  rw [range_paperNativeRealification_eq]
  exact isClosed_eq continuous_paperNativeRealification continuous_id

end RHTower.WeilWorkPBAP

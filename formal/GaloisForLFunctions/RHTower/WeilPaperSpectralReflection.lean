import GaloisForLFunctions.RHTower.WeilPaperRealTestSplitting
import Zeta23.Taper.Fourier

/-!
# Symmetric spectral probabilities without loss of full energy

Real-test splitting preserves every attainable full energy. The Fourier
conjugation identity makes its actual spectral density even; reflection symmetry
then passes to the probability on the real line and its prime-torus pushforward.
-/

open Complex MeasureTheory Zeta23 GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- A real-valued native test has an even Fourier-square density. -/
theorem testSpectralDensity_neg_of_real (f : WeilTestFn)
    (hf : ∀ x, (f.1 x).im = 0) (ξ : ℝ) :
    testSpectralDensity f (-ξ) = testSpectralDensity f ξ := by
  have heq : f.1 = fun x => ((f.1 x).re : ℂ) := by
    funext x
    apply Complex.ext <;> simp [hf]
  have harg : -(2 * Real.pi * ((-ξ : ℝ) : ℂ)) =
      -conj (-(2 * Real.pi * (ξ : ℂ))) := by simp [map_ofNat]
  unfold testSpectralDensity
  rw [heq, harg, ← Taper.conj_paperFT_ofReal, Complex.norm_conj]

/-- Signed mixtures supported on real-valued tests retain the same evenness. -/
theorem mixtureSpectralDensity_neg_of_real (c : WeilTestFn →₀ ℝ)
    (hc : ∀ f, c f ≠ 0 → ∀ x, (f.1 x).im = 0) (ξ : ℝ) :
    mixtureSpectralDensity c (-ξ) = mixtureSpectralDensity c ξ := by
  classical
  apply Finset.sum_congr rfl
  intro f hf
  dsimp only
  rw [testSpectralDensity_neg_of_real f (hc f (Finsupp.mem_support_iff.mp hf))]

/-- The energy-preserving splitting always produces an even density. -/
theorem mixtureSpectralDensity_paperSplitRealMixture_neg (c : WeilTestFn →₀ ℝ) (ξ : ℝ) :
    mixtureSpectralDensity (paperSplitRealMixture c) (-ξ) =
      mixtureSpectralDensity (paperSplitRealMixture c) ξ :=
  mixtureSpectralDensity_neg_of_real _ (paperSplitRealMixture_real c) ξ

/-- Reflection preserves the actual probability measure of a real-test mixture. -/
theorem map_neg_spectralProbability_of_real (c : NormalizedMixture)
    (hc : ∀ f, c.1 f ≠ 0 → ∀ x, (f.1 x).im = 0) :
    Measure.map (fun ξ : ℝ => -ξ) (spectralProbability c : Measure ℝ) =
      (spectralProbability c : Measure ℝ) := by
  apply Measure.ext
  intro s hs
  change Measure.map (fun ξ : ℝ => -ξ)
    (volume.withDensity (fun ξ => ENNReal.ofReal (mixtureSpectralDensity c.1 ξ))) s = _
  rw [Measure.map_apply measurable_neg hs]
  change volume.withDensity _ ((fun ξ : ℝ => -ξ) ⁻¹' s) = volume.withDensity _ s
  rw [withDensity_apply _ (measurable_neg hs), withDensity_apply _ hs]
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage hs
    (continuous_mixtureSpectralDensity c.1).measurable.ennreal_ofReal
  simpa only [mixtureSpectralDensity_neg_of_real c.1 hc] using h

/-- Every normalized mixture has an energy-preserving reflection-invariant realization. -/
theorem map_neg_spectralProbability_paperSplitRealNormalizedMixture (c : NormalizedMixture) :
    Measure.map (fun ξ : ℝ => -ξ)
      (spectralProbability (paperSplitRealNormalizedMixture c) : Measure ℝ) =
        (spectralProbability (paperSplitRealNormalizedMixture c) : Measure ℝ) :=
  map_neg_spectralProbability_of_real _ (paperSplitRealMixture_real c.1)

/-- Negating frequency inverts all prime phases simultaneously. -/
theorem primeSpectralPoint_neg (ξ : ℝ) : primeSpectralPoint (-ξ) = -primeSpectralPoint ξ := by
  funext p
  simp [primeSpectralPoint, clockPhasePoint, mul_neg, neg_mul, neg_div]

/-- Reflection symmetry descends to inversion symmetry of the prime-torus probability. -/
theorem map_neg_spectralTorusProbability_of_real (c : NormalizedMixture)
    (hc : ∀ f, c.1 f ≠ 0 → ∀ x, (f.1 x).im = 0) :
    Measure.map (fun z : PrimePhaseSpace => -z)
      (spectralTorusProbability c : Measure PrimePhaseSpace) =
        (spectralTorusProbability c : Measure PrimePhaseSpace) := by
  change Measure.map (fun z : PrimePhaseSpace => -z)
    (Measure.map primeSpectralPoint (spectralProbability c : Measure ℝ)) =
      Measure.map primeSpectralPoint (spectralProbability c : Measure ℝ)
  rw [Measure.map_map measurable_neg continuous_primeSpectralPoint.measurable]
  have hcomp : (fun z : PrimePhaseSpace => -z) ∘ primeSpectralPoint =
      primeSpectralPoint ∘ (fun ξ : ℝ => -ξ) := by
    funext ξ
    exact (primeSpectralPoint_neg ξ).symm
  rw [hcomp, ← Measure.map_map continuous_primeSpectralPoint.measurable measurable_neg,
    map_neg_spectralProbability_of_real c hc]

/-- Canonical real-test representing measures are invariant under torus inversion. -/
theorem map_neg_spectralRepresentingMeasure_paperSplitRealComplexNullMixture
    (c : {c : NormalizedMixture // defect c.1 = 0}) :
    Measure.map (fun z : PrimePhaseSpace => -z)
      ((spectralRepresentingMeasure (paperSplitRealComplexNullMixture c)).1 :
        Measure PrimePhaseSpace) =
      ((spectralRepresentingMeasure (paperSplitRealComplexNullMixture c)).1 :
        Measure PrimePhaseSpace) :=
  map_neg_spectralTorusProbability_of_real _ (paperSplitRealMixture_real c.1.1)

/-- Reflection-symmetric real-test spectral representing measures realize exactly all
full energy values in the original normalized real-defect-null cone. -/
theorem attainable_energy_eq_symmetric_real_test_complex_null :
    {e : ℝ | ∃ c : NormalizedMixture, defect c.1 = 0 ∧ energy c.1 = e} =
      {e : ℝ | ∃ c : ComplexNullMixture, energy c.1.1 = e ∧
        (∀ f, c.1.1 f ≠ 0 → ∀ x, (f.1 x).im = 0) ∧
        Measure.map (fun ξ : ℝ => -ξ) (spectralProbability c.1 : Measure ℝ) =
          (spectralProbability c.1 : Measure ℝ) ∧
        Measure.map (fun z : PrimePhaseSpace => -z)
          ((spectralRepresentingMeasure c).1 : Measure PrimePhaseSpace) =
          ((spectralRepresentingMeasure c).1 : Measure PrimePhaseSpace)} := by
  ext e
  constructor
  · rintro ⟨c, hc, he⟩
    let d := paperSplitRealComplexNullMixture ⟨c, hc⟩
    have hd : ∀ f, d.1.1 f ≠ 0 → ∀ x, (f.1 x).im = 0 :=
      paperSplitRealMixture_real c.1
    exact ⟨d, (energy_paperSplitRealMixture c.1).trans he, hd,
      map_neg_spectralProbability_of_real d.1 hd,
      map_neg_spectralTorusProbability_of_real d.1 hd⟩
  · rintro ⟨c, he, _, _, _⟩
    exact ⟨c.1, defect_complexNullMixture c, he⟩

private theorem integral_antisymmetric_eq_zero {A : Type*} [MeasurableSpace A]
    [InvolutiveNeg A] [MeasurableNeg A] (μ : Measure A)
    (hμ : Measure.map (fun x : A => -x) μ = μ) (F : A → ℝ) :
    (∫ x, F x - F (-x) ∂μ) = 0 := by
  have hmp : MeasurePreserving (fun x : A => -x) μ μ := ⟨measurable_neg, hμ⟩
  have h := hmp.integral_comp (MeasurableEquiv.neg A).measurableEmbedding
    (fun x => F x - F (-x))
  have heq : (fun x => F (-x) - F (-(-x))) = fun x => -(F x - F (-x)) := by
    funext x
    simp only [neg_neg]
    ring
  change (∫ x, F (-x) - F (-(-x)) ∂μ) = _ at h
  rw [heq, integral_neg] at h
  linarith

/-- Every odd part of a real spectral observable has zero integral after splitting. -/
theorem integral_antisymmetric_spectralProbability_paperSplitRealNormalizedMixture
    (c : NormalizedMixture) (F : ℝ → ℝ) :
    (∫ ξ, F ξ - F (-ξ)
      ∂(spectralProbability (paperSplitRealNormalizedMixture c) : Measure ℝ)) = 0 :=
  integral_antisymmetric_eq_zero _
    (map_neg_spectralProbability_paperSplitRealNormalizedMixture c) F

/-- Inversion-odd observables cannot distinguish the canonical symmetric representing measures. -/
theorem integral_antisymmetric_spectralRepresentingMeasure_paperSplitRealComplexNullMixture
    (c : {c : NormalizedMixture // defect c.1 = 0}) (F : PrimePhaseSpace → ℝ) :
    (∫ z, F z - F (-z)
      ∂((spectralRepresentingMeasure (paperSplitRealComplexNullMixture c)).1 :
        Measure PrimePhaseSpace)) = 0 :=
  integral_antisymmetric_eq_zero _
    (map_neg_spectralRepresentingMeasure_paperSplitRealComplexNullMixture c) F

end RHTower.WeilWorkPBAP

import GaloisForLFunctions.RHTower.WeilPaperSpectralReflection

/-!
# Exact symmetrization of the actual spectral probabilities

Conjugation averaging of native tests is precisely arithmetic averaging of the
spectral probability with its reflection. The same exact identity holds after
pushforward to the prime torus. No positivity of the Weil functional is assumed.
-/

open Complex MeasureTheory Zeta23
open scoped ComplexConjugate ENNReal
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Fourier conjugation for an arbitrary native complex test. -/
theorem paperFT_paperConjugateTestFn (f : WeilTestFn) (z : ℂ) :
    paperFT (paperConjugateTestFn f).1 z = conj (paperFT f.1 (-conj z)) := by
  unfold paperFT
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only [paperConjugateTestFn]
    rw [map_mul, ← Complex.exp_conj]
    congr 1
    congr 1
    simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
    ring

/-- Conjugating a test reflects its spectral density pointwise. -/
theorem testSpectralDensity_paperConjugateTestFn (f : WeilTestFn) (ξ : ℝ) :
    testSpectralDensity (paperConjugateTestFn f) ξ = testSpectralDensity f (-ξ) := by
  unfold testSpectralDensity
  rw [paperFT_paperConjugateTestFn, Complex.norm_conj]
  congr 3
  simp [map_ofNat]

/-- Conjugation averaging replaces the density by its exact even part. -/
theorem mixtureSpectralDensity_paperRealMixture (c : WeilTestFn →₀ ℝ) (ξ : ℝ) :
    mixtureSpectralDensity (paperRealMixture c) ξ =
      (1 / 2 : ℝ) * (mixtureSpectralDensity c ξ + mixtureSpectralDensity c (-ξ)) := by
  change (Finsupp.linearCombination ℝ (fun f => testSpectralDensity f ξ))
    (paperRealMixture c) = _
  rw [paperRealMixture, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.id_apply, map_smul, map_add, Finsupp.lmapDomain_apply,
    Finsupp.linearCombination_mapDomain]
  simp only [Function.comp_def, testSpectralDensity_paperConjugateTestFn]
  rfl

/-- Reflection transports an arbitrary density by precomposition with negation. -/
theorem map_neg_volume_withDensity (d : ℝ → ℝ≥0∞) :
    Measure.map (fun ξ : ℝ => -ξ) (volume.withDensity d) =
      volume.withDensity (fun ξ => d (-ξ)) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply measurable_neg hs, withDensity_apply _ (measurable_neg hs),
    withDensity_apply _ hs]
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.neg ℝ).measurableEmbedding (fun ξ => d (-ξ)) s
  simpa only [neg_neg] using h

/-- The probability-level operation is literally averaging with the reflected probability. -/
theorem spectralProbability_paperRealNormalizedMixture (c : NormalizedMixture) :
    (spectralProbability (paperRealNormalizedMixture c) : Measure ℝ) =
      ENNReal.ofReal (1 / 2 : ℝ) • ((spectralProbability c : Measure ℝ) +
        Measure.map (fun ξ : ℝ => -ξ) (spectralProbability c : Measure ℝ)) := by
  let d : ℝ → ℝ≥0∞ := fun ξ => ENNReal.ofReal (mixtureSpectralDensity c.1 ξ)
  have hd : Measurable d := (continuous_mixtureSpectralDensity c.1).measurable.ennreal_ofReal
  change volume.withDensity (fun ξ => ENNReal.ofReal
    (mixtureSpectralDensity (paperRealMixture c.1) ξ)) =
      ENNReal.ofReal (1 / 2 : ℝ) • (volume.withDensity d +
        Measure.map (fun ξ : ℝ => -ξ) (volume.withDensity d))
  rw [map_neg_volume_withDensity, ← withDensity_add_left hd (fun ξ => d (-ξ))]
  have hsum : Measurable (d + fun ξ : ℝ => d (-ξ)) := hd.add (hd.comp measurable_neg)
  rw [← withDensity_smul _ hsum]
  congr 1
  funext ξ
  rw [mixtureSpectralDensity_paperRealMixture,
    ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / 2),
    ENNReal.ofReal_add (mixtureSpectralDensity_nonneg c.1 c.2.1 ξ)
      (mixtureSpectralDensity_nonneg c.1 c.2.1 (-ξ))]
  rfl

/-- The compact prime-torus probability undergoes the same exact inversion average. -/
theorem spectralTorusProbability_paperRealNormalizedMixture (c : NormalizedMixture) :
    (spectralTorusProbability (paperRealNormalizedMixture c) : Measure PrimePhaseSpace) =
      ENNReal.ofReal (1 / 2 : ℝ) • ((spectralTorusProbability c : Measure PrimePhaseSpace) +
        Measure.map (fun z : PrimePhaseSpace => -z)
          (spectralTorusProbability c : Measure PrimePhaseSpace)) := by
  change Measure.map primeSpectralPoint
    (spectralProbability (paperRealNormalizedMixture c) : Measure ℝ) =
      ENNReal.ofReal (1 / 2 : ℝ) •
        (Measure.map primeSpectralPoint (spectralProbability c : Measure ℝ) +
          Measure.map (fun z : PrimePhaseSpace => -z)
            (Measure.map primeSpectralPoint (spectralProbability c : Measure ℝ)))
  rw [spectralProbability_paperRealNormalizedMixture, Measure.map_smul,
    Measure.map_add _ _ continuous_primeSpectralPoint.measurable,
    Measure.map_map continuous_primeSpectralPoint.measurable measurable_neg,
    Measure.map_map measurable_neg continuous_primeSpectralPoint.measurable]
  congr 3
  funext ξ
  exact primeSpectralPoint_neg ξ

/-- The density operation is idempotent, even when the mixture has signed weights. -/
theorem mixtureSpectralDensity_paperRealMixture_idempotent (c : WeilTestFn →₀ ℝ) :
    mixtureSpectralDensity (paperRealMixture (paperRealMixture c)) =
      mixtureSpectralDensity (paperRealMixture c) := by
  funext ξ
  simp only [mixtureSpectralDensity_paperRealMixture, neg_neg]
  ring

/-- Repeating realification makes no further change to the actual spectral probability. -/
theorem spectralProbability_paperRealNormalizedMixture_idempotent (c : NormalizedMixture) :
    spectralProbability (paperRealNormalizedMixture (paperRealNormalizedMixture c)) =
      spectralProbability (paperRealNormalizedMixture c) := by
  apply ProbabilityMeasure.toMeasure_injective
  change volume.withDensity _ = volume.withDensity _
  congr 1
  funext ξ
  exact congrArg ENNReal.ofReal
    (congrFun (mixtureSpectralDensity_paperRealMixture_idempotent c.1) ξ)

end RHTower.WeilWorkPBAP

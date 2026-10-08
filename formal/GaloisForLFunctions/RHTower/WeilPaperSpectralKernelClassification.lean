import GaloisForLFunctions.RHTower.WeilPaperSpectralSymmetrization

/-!
# Spectral probabilities are classified by the full autocorrelation kernel

Characteristic-function uniqueness identifies normalized finite-mixture spectral
probabilities exactly with their aggregate autocorrelations. Consequently full
energy depends only on this probability, and real/imaginary splitting realizes
the same exact measure symmetrization as conjugation averaging.
-/

open Complex MeasureTheory Zeta23
open scoped ComplexConjugate ENNReal
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Autocorrelation is the actual probability's characteristic function at `2πy`. -/
theorem mixtureSample_eq_charFun_spectralProbability (c : NormalizedMixture) (y : ℝ) :
    mixtureSample c.1 y = charFun (spectralProbability c : Measure ℝ) (2 * Real.pi * y) := by
  rw [charFun_apply_real, integral_spectralProbability, mixtureSample_eq_integral_density]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => by
    dsimp only
    congr 1
    congr 1
    push_cast
    ring

/-- Equality of actual spectral probabilities is exactly equality of the full kernels. -/
theorem spectralProbability_eq_iff_mixtureSample_eq (c d : NormalizedMixture) :
    spectralProbability c = spectralProbability d ↔ mixtureSample c.1 = mixtureSample d.1 := by
  constructor
  · intro h
    funext y
    rw [mixtureSample_eq_charFun_spectralProbability,
      mixtureSample_eq_charFun_spectralProbability, h]
  · intro h
    apply ProbabilityMeasure.toMeasure_injective
    apply Measure.ext_of_charFun
    funext t
    have ht : 2 * Real.pi * (t / (2 * Real.pi)) = t := by
      field_simp [Real.pi_ne_zero]
    have hh := congrFun h (t / (2 * Real.pi))
    simpa only [mixtureSample_eq_charFun_spectralProbability, ht] using hh

/-- Full Weil energy is constant on each spectral-probability fiber. -/
theorem energy_eq_of_spectralProbability_eq (c d : NormalizedMixture)
    (h : spectralProbability c = spectralProbability d) : energy c.1 = energy d.1 :=
  energy_eq_of_mixtureSample_eq c.1 d.1 ((spectralProbability_eq_iff_mixtureSample_eq c d).mp h)

/-- Real/imaginary splitting and conjugation averaging give identical spectral laws. -/
theorem spectralProbability_paperSplitRealNormalizedMixture_eq_realification
    (c : NormalizedMixture) :
    spectralProbability (paperSplitRealNormalizedMixture c) =
      spectralProbability (paperRealNormalizedMixture c) :=
  (spectralProbability_eq_iff_mixtureSample_eq _ _).mpr
    (mixtureSample_paperSplitRealMixture_eq_realification c.1)

/-- The two positive constructions also give identical compact prime-torus laws. -/
theorem spectralTorusProbability_paperSplitRealNormalizedMixture_eq_realification
    (c : NormalizedMixture) :
    spectralTorusProbability (paperSplitRealNormalizedMixture c) =
      spectralTorusProbability (paperRealNormalizedMixture c) := by
  exact congrArg (fun μ : ProbabilityMeasure ℝ =>
    μ.map continuous_primeSpectralPoint.measurable.aemeasurable)
    (spectralProbability_paperSplitRealNormalizedMixture_eq_realification c)

/-- Splitting into real tests realizes exactly the reflection average of the original law. -/
theorem spectralProbability_paperSplitRealNormalizedMixture (c : NormalizedMixture) :
    (spectralProbability (paperSplitRealNormalizedMixture c) : Measure ℝ) =
      ENNReal.ofReal (1 / 2 : ℝ) • ((spectralProbability c : Measure ℝ) +
        Measure.map (fun ξ : ℝ => -ξ) (spectralProbability c : Measure ℝ)) := by
  rw [spectralProbability_paperSplitRealNormalizedMixture_eq_realification,
    spectralProbability_paperRealNormalizedMixture]

/-- The actual real-test torus law is the exact inversion average of the original law. -/
theorem spectralTorusProbability_paperSplitRealNormalizedMixture (c : NormalizedMixture) :
    (spectralTorusProbability (paperSplitRealNormalizedMixture c) : Measure PrimePhaseSpace) =
      ENNReal.ofReal (1 / 2 : ℝ) • ((spectralTorusProbability c : Measure PrimePhaseSpace) +
        Measure.map (fun z : PrimePhaseSpace => -z)
          (spectralTorusProbability c : Measure PrimePhaseSpace)) := by
  rw [spectralTorusProbability_paperSplitRealNormalizedMixture_eq_realification,
    spectralTorusProbability_paperRealNormalizedMixture]

/-- Splitting fixes a spectral law exactly when every autocorrelation value is real. -/
theorem spectralProbability_paperSplitRealNormalizedMixture_eq_iff (c : NormalizedMixture) :
    spectralProbability (paperSplitRealNormalizedMixture c) = spectralProbability c ↔
      ∀ y, (mixtureSample c.1 y).im = 0 := by
  rw [spectralProbability_eq_iff_mixtureSample_eq]
  constructor
  · intro h y
    have hi := congrArg Complex.im (congrFun h y)
    change (mixtureSample (paperSplitRealMixture c.1) y).im = _ at hi
    rw [mixtureSample_paperSplitRealMixture, Complex.ofReal_im] at hi
    exact hi.symm
  · intro h
    funext y
    change mixtureSample (paperSplitRealMixture c.1) y = _
    rw [mixtureSample_paperSplitRealMixture]
    apply Complex.ext <;> simp [h]

/-- The real-test construction is idempotent at the spectral-probability level. -/
theorem spectralProbability_paperSplitRealNormalizedMixture_idempotent (c : NormalizedMixture) :
    spectralProbability (paperSplitRealNormalizedMixture (paperSplitRealNormalizedMixture c)) =
      spectralProbability (paperSplitRealNormalizedMixture c) := by
  apply (spectralProbability_paperSplitRealNormalizedMixture_eq_iff _).mpr
  intro y
  change (mixtureSample (paperSplitRealMixture c.1) y).im = 0
  rw [mixtureSample_paperSplitRealMixture, Complex.ofReal_im]

end RHTower.WeilWorkPBAP

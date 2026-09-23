import GaloisForLFunctions.HTGeometry.ComplexIntegralGramStrict
import GaloisForLFunctions.HTGeometry.CompactFourierEntire
import GaloisForLFunctions.HTGeometry.CharacteristicFunctionPositiveDefinite
import GaloisForLFunctions.HTGeometry.ComplexHermitianRealification
import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry
import GaloisForLFunctions.Hurwitz.ExpIndependence

/-!
# Strict uniform characteristic Grams and greedy-bump laws

Bochner positivity alone gives only a semidefinite characteristic-function kernel.  Distinct real
frequencies against uniform measure on `[0,1]` are separated by exponential-polynomial
independence, upgrading the Gram to strict positivity.  Its doubled-real form is therefore a
template metric for arXiv:2609.03581.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory Matrix Set
open scoped BigOperators ComplexOrder

noncomputable section

/-- Fourier feature at one real frequency. -/
def uniformFourierFeature {N : ℕ} (frequency : Fin N → ℝ)
    (i : Fin N) (x : ℝ) : ℂ :=
  Complex.exp ((Complex.I * (frequency i : ℂ)) * (x : ℂ))

/-- Gram of distinct Fourier probes against uniform probability measure on `[0,1]`. -/
def uniformCharacteristicGram {N : ℕ} (frequency : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  complexFeatureGram (volume.restrict (Set.Icc (0 : ℝ) 1))
    (uniformFourierFeature frequency)

/-- Entries are the characteristic function of uniform `[0,1]` at frequency differences. -/
theorem uniformCharacteristicGram_apply_eq_charFun {N : ℕ}
    (frequency : Fin N → ℝ) (i j : Fin N) :
    uniformCharacteristicGram frequency i j =
      charFun (volume.restrict (Set.Icc (0 : ℝ) 1))
        (frequency i - frequency j) := by
  rw [uniformCharacteristicGram, complexFeatureGram, charFun_apply_real]
  apply integral_congr_ae
  filter_upwards with x
  change Complex.exp (Complex.I * (frequency i : ℂ) * (x : ℂ)) *
      star (Complex.exp (Complex.I * (frequency j : ℂ) * (x : ℂ))) =
    Complex.exp (((frequency i - frequency j : ℝ) : ℂ) * (x : ℂ) * Complex.I)
  rw [RCLike.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem uniformFourierFeature_pair_integrable {N : ℕ}
    (frequency : Fin N → ℝ) (i j : Fin N) :
    Integrable (fun x : ℝ => uniformFourierFeature frequency i x *
      (starRingEnd ℂ) (uniformFourierFeature frequency j x))
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  apply ContinuousOn.integrableOn_Icc
  have hi : Continuous (uniformFourierFeature frequency i) := by
    unfold uniformFourierFeature
    fun_prop
  have hj : Continuous (uniformFourierFeature frequency j) := by
    unfold uniformFourierFeature
    fun_prop
  exact (hi.mul hj.star).continuousOn

/-- Distinct frequencies make the uniform characteristic Gram strictly positive definite. -/
theorem uniformCharacteristicGram_posDef {N : ℕ} {frequency : Fin N → ℝ}
    (hfrequency : Function.Injective frequency) :
    (uniformCharacteristicGram frequency).PosDef := by
  apply complexFeatureGram_posDef_of_support
  · exact uniformFourierFeature_pair_integrable frequency
  · intro x hx
    by_contra hnot
    have hsupp : (volume.restrict (Set.Icc (0 : ℝ) 1))
        (Function.support
          (complexFeatureCombination (uniformFourierFeature frequency) x)) = 0 := by
      exact nonpos_iff_eq_zero.mp (not_lt.mp hnot)
    have hae : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        complexFeatureCombination (uniformFourierFeature frequency) x s = 0 := by
      apply MeasureTheory.ae_iff.mpr
      simpa [Function.support] using hsupp
    let coefficient : Fin N → ℂ := fun k => (starRingEnd ℂ) (x k)
    let exponent : Fin N → ℂ := fun k => Complex.I * (frequency k : ℂ)
    let G : ℂ → ℂ := fun z => ∑ k, coefficient k * Complex.exp (exponent k * z)
    have hdiff : Differentiable ℂ G := by
      apply Differentiable.fun_sum
      intro k _
      exact (differentiable_const _).mul
        (Complex.differentiable_exp.comp
          ((differentiable_const _).mul differentiable_id))
    have haeG_Icc : ∀ᵐ s : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        G (s : ℂ) = 0 := by
      filter_upwards [hae] with s hs
      simpa [G, coefficient, exponent, uniformFourierFeature,
        complexFeatureCombination] using hs
    have haeG_Ioo : ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
        G (s : ℂ) = 0 :=
      ae_mono (Measure.restrict_mono Set.Ioo_subset_Icc_self le_rfl) haeG_Icc
    have hGzero : ∀ z : ℂ, G z = 0 := fun z =>
      entire_eq_zero_of_ae_vanishing_on_real_interval hdiff
        (t₀ := (1 / 2 : ℝ)) (r := (1 / 2 : ℝ)) (by norm_num) (by
          convert haeG_Ioo using 1 <;> norm_num) z
    have hexponent : Function.Injective exponent := by
      intro i j hij
      apply hfrequency
      have him := congrArg Complex.im hij
      simpa [exponent] using him
    have hLI := HurwitzExp.expLin_linearIndependent hexponent
    rw [Fintype.linearIndependent_iff] at hLI
    have hrel :
        (∑ k, coefficient k • fun z => Complex.exp (exponent k * z)) = 0 := by
      funext z
      simpa [Pi.smul_apply, smul_eq_mul] using hGzero z
    have hc0 : ∀ k, coefficient k = 0 := hLI coefficient hrel
    apply hx
    funext k
    have hk := hc0 k
    simp only [coefficient] at hk
    simpa using congrArg (starRingEnd ℂ) hk

/-- Certified packet of distinct frequency probes. -/
structure GreedyBumpUniformCharacteristicData (N : ℕ) where
  frequency : Fin N → ℝ
  frequency_injective : Function.Injective frequency

/-- Doubled-real uniform characteristic Gram. -/
def GreedyBumpUniformCharacteristicData.realifiedMatrix {N : ℕ}
    (data : GreedyBumpUniformCharacteristicData N) :
    Matrix (Fin (N + N)) (Fin (N + N)) ℝ :=
  (complexMatrixRealification
      (uniformCharacteristicGram data.frequency)).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm

/-- Strict uniform characteristic Gram as a positive template metric. -/
def GreedyBumpUniformCharacteristicData.metric {N : ℕ}
    (data : GreedyBumpUniformCharacteristicData N) : PositiveTemplateMetric (N + N) where
  matrix := data.realifiedMatrix
  posDef := (complexMatrixRealification_posDef
    (uniformCharacteristicGram_posDef data.frequency_injective)).submatrix
      finSumFinEquiv.symm.injective

/-- Every distinct uniform characteristic packet satisfies the complete paper law package. -/
theorem GreedyBumpUniformCharacteristicData.laws {N : ℕ}
    (data : GreedyBumpUniformCharacteristicData N) (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q data.metric :=
  greedyBumpMetricLaws_closed Q data.metric

/-- `N` complex characteristic probes contribute exact leading bias `N / Q`. -/
theorem GreedyBumpUniformCharacteristicData.bias {N : ℕ}
    (data : GreedyBumpUniformCharacteristicData N) (Q : PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q data.metric)⁻¹ * data.metric.matrix) =
      (N : ℝ) / (Q : ℝ) := by
  rw [greedyBump_matched_bias]
  push_cast
  field_simp [ne_of_gt Q.property]
  ring

/-- Metric-unit localization radius of the frequency packet is `2N / Q²`. -/
theorem GreedyBumpUniformCharacteristicData.localizationRadius {N : ℕ}
    (data : GreedyBumpUniformCharacteristicData N) (Q : PositiveSignal) :
    Matrix.trace
        (greedyBumpLocalizationCovariance Q data.metric * data.metric.matrix) =
      ((N + N : ℕ) : ℝ) / (Q : ℝ) ^ (2 : ℕ) :=
  greedyBumpLocalizationCovariance_trace_mul Q data.metric

end

end GaloisForLFunctions.HTGeometry

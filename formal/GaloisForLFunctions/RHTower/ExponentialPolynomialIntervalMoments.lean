import GaloisForLFunctions.HTGeometry.ComplexIntegralGramStrict
import GaloisForLFunctions.HTGeometry.CompactFourierEntire
import GaloisForLFunctions.RHTower.ExponentialPolynomialModeIndependence

/-!
# Interval moment coordinates for exponential-polynomial modes

Distinct exponential-polynomial features have a strictly positive definite Gram matrix on every
nondegenerate real interval.  Consequently compactly supported linear combinations of their
conjugates realize every prescribed finite moment vector.  This supplies the input-coordinate
surjectivity required by finite residue-mode operators.
-/

namespace RHTower

open Complex MeasureTheory Set Matrix
open scoped BigOperators ComplexOrder

noncomputable section

/-- Restriction of a complex exponential-polynomial mode to the real line. -/
def exponentialPolynomialRealFeature {r : ℕ} (lambda : Fin r → ℂ) (mult : Fin r → ℕ)
    (k : Fin (∑ i, mult i)) (s : ℝ) : ℂ :=
  exponentialPolynomialMode lambda mult k (s : ℂ)

/-- Lebesgue measure restricted to a compact interval. -/
def exponentialPolynomialIntervalMeasure (a b : ℝ) : Measure ℝ :=
  volume.restrict (Set.Icc a b)

/-- Hermitian interval Gram matrix of the complete exponential-polynomial feature family. -/
def exponentialPolynomialIntervalGram {r : ℕ} (lambda : Fin r → ℂ)
    (mult : Fin r → ℕ) (a b : ℝ) :
    Matrix (Fin (∑ i, mult i)) (Fin (∑ i, mult i)) ℂ :=
  GaloisForLFunctions.HTGeometry.complexFeatureGram
    (exponentialPolynomialIntervalMeasure a b)
    (exponentialPolynomialRealFeature lambda mult)

theorem exponentialPolynomialRealFeature_pair_integrable
    {r : ℕ} (lambda : Fin r → ℂ) (mult : Fin r → ℕ) (a b : ℝ)
    (i j : Fin (∑ q, mult q)) :
    Integrable (fun s : ℝ => exponentialPolynomialRealFeature lambda mult i s *
      (starRingEnd ℂ) (exponentialPolynomialRealFeature lambda mult j s))
      (exponentialPolynomialIntervalMeasure a b) := by
  have hi : Continuous (fun s : ℝ =>
      exponentialPolynomialRealFeature lambda mult i s) :=
    (contDiff_exponentialPolynomialMode lambda mult i 1).continuous.comp
      Complex.continuous_ofReal
  have hj : Continuous (fun s : ℝ =>
      exponentialPolynomialRealFeature lambda mult j s) :=
    (contDiff_exponentialPolynomialMode lambda mult j 1).continuous.comp
      Complex.continuous_ofReal
  apply ContinuousOn.integrableOn_Icc
  fun_prop

/-- Distinct nodes make the interval feature Gram matrix strictly positive definite. -/
theorem exponentialPolynomialIntervalGram_posDef
    {r : ℕ} {lambda : Fin r → ℂ} (hlambda : Function.Injective lambda)
    (mult : Fin r → ℕ) {a b : ℝ} (hab : a < b) :
    (exponentialPolynomialIntervalGram lambda mult a b).PosDef := by
  apply GaloisForLFunctions.HTGeometry.complexFeatureGram_posDef_of_support
  · exact exponentialPolynomialRealFeature_pair_integrable lambda mult a b
  · intro x hx
    by_contra hnot
    have hsupp : exponentialPolynomialIntervalMeasure a b
        (Function.support
          (GaloisForLFunctions.HTGeometry.complexFeatureCombination
            (exponentialPolynomialRealFeature lambda mult) x)) = 0 := by
      exact nonpos_iff_eq_zero.mp (not_lt.mp hnot)
    have hae : ∀ᵐ s ∂(exponentialPolynomialIntervalMeasure a b),
        GaloisForLFunctions.HTGeometry.complexFeatureCombination
          (exponentialPolynomialRealFeature lambda mult) x s = 0 := by
      apply MeasureTheory.ae_iff.mpr
      simpa [Function.support] using hsupp
    let c : Fin (∑ i, mult i) → ℂ := fun k => (starRingEnd ℂ) (x k)
    let G : ℂ → ℂ := fun z => ∑ k, c k * exponentialPolynomialMode lambda mult k z
    have hdiff : Differentiable ℂ G := by
      apply Differentiable.fun_sum
      intro k _
      exact (differentiable_const _).mul
        ((contDiff_exponentialPolynomialMode lambda mult k 1).differentiable (by norm_num))
    have haeG_Icc : ∀ᵐ s : ℝ ∂(volume.restrict (Set.Icc a b)), G (s : ℂ) = 0 := by
      filter_upwards [hae] with s hs
      simpa [G, c, exponentialPolynomialIntervalMeasure,
        GaloisForLFunctions.HTGeometry.complexFeatureCombination,
        exponentialPolynomialRealFeature] using hs
    have haeG_Ioo : ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo a b)), G (s : ℂ) = 0 :=
      ae_mono (Measure.restrict_mono Set.Ioo_subset_Icc_self le_rfl) haeG_Icc
    let t0 : ℝ := (a + b) / 2
    let delta : ℝ := (b - a) / 2
    have hdelta : 0 < delta := by dsimp [delta]; linarith
    have hset : Set.Ioo (t0 - delta) (t0 + delta) = Set.Ioo a b := by
      congr 1 <;> dsimp [t0, delta] <;> linarith
    have haeG : ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo (t0 - delta) (t0 + delta))),
        G (s : ℂ) = 0 := by
      rw [hset]
      exact haeG_Ioo
    have hGzero : ∀ z : ℂ, G z = 0 := fun z =>
      GaloisForLFunctions.HTGeometry.entire_eq_zero_of_ae_vanishing_on_real_interval
        hdiff hdelta haeG z
    have hLI := exponentialPolynomialMode_linearIndependent hlambda mult
    rw [Fintype.linearIndependent_iff] at hLI
    have hrel : (∑ k, c k • exponentialPolynomialMode lambda mult k) = 0 := by
      funext z
      simpa [Pi.smul_apply, smul_eq_mul] using hGzero z
    have hc0 : ∀ k, c k = 0 := hLI c hrel
    apply hx
    funext k
    have hk := hc0 k
    simp only [c] at hk
    simpa using congrArg (starRingEnd ℂ) hk

/-- Compactly supported test function synthesized from conjugate exponential-polynomial modes. -/
def exponentialPolynomialIntervalSynthesis
    {r : ℕ} (lambda : Fin r → ℂ) (mult : Fin r → ℕ) (a b : ℝ)
    (c : Fin (∑ i, mult i) → ℂ) (s : ℝ) : ℂ :=
  Set.indicator (Set.Icc a b) (fun t => ∑ j, c j *
    (starRingEnd ℂ) (exponentialPolynomialRealFeature lambda mult j t)) s

/-- Moments against the complete exponential-polynomial feature family. -/
def exponentialPolynomialMoment
    {r : ℕ} (lambda : Fin r → ℂ) (mult : Fin r → ℕ)
    (g : ℝ → ℂ) : Fin (∑ i, mult i) → ℂ :=
  fun i => ∫ s, exponentialPolynomialRealFeature lambda mult i s * g s ∂volume

/-- Moments of interval synthesis are exactly multiplication by the interval Gram matrix. -/
theorem exponentialPolynomialMoment_intervalSynthesis
    {r : ℕ} (lambda : Fin r → ℂ) (mult : Fin r → ℕ) (a b : ℝ)
    (c : Fin (∑ i, mult i) → ℂ) :
    exponentialPolynomialMoment lambda mult
        (exponentialPolynomialIntervalSynthesis lambda mult a b c) =
      (exponentialPolynomialIntervalGram lambda mult a b).mulVec c := by
  funext i
  rw [exponentialPolynomialMoment]
  simp only [exponentialPolynomialIntervalSynthesis]
  have hindicator :
      (fun s : ℝ => exponentialPolynomialRealFeature lambda mult i s *
        (Set.Icc a b).indicator (fun t => ∑ j, c j *
          (starRingEnd ℂ) (exponentialPolynomialRealFeature lambda mult j t)) s) =
      (Set.Icc a b).indicator (fun s : ℝ =>
        exponentialPolynomialRealFeature lambda mult i s *
          ∑ j, c j * (starRingEnd ℂ)
            (exponentialPolynomialRealFeature lambda mult j s)) := by
    funext s
    exact (Set.indicator_mul_right (Set.Icc a b)
      (fun t => exponentialPolynomialRealFeature lambda mult i t)
      (fun t => ∑ j, c j * (starRingEnd ℂ)
        (exponentialPolynomialRealFeature lambda mult j t))).symm
  rw [hindicator]
  rw [MeasureTheory.integral_indicator measurableSet_Icc]
  simp only [Matrix.mulVec,
    exponentialPolynomialIntervalGram, GaloisForLFunctions.HTGeometry.complexFeatureGram,
    exponentialPolynomialIntervalMeasure, Finset.mul_sum]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    calc
      (∫ s in Set.Icc a b, exponentialPolynomialRealFeature lambda mult i s *
          (c j * (starRingEnd ℂ) (exponentialPolynomialRealFeature lambda mult j s)) ∂volume) =
          ∫ s in Set.Icc a b, c j * (exponentialPolynomialRealFeature lambda mult i s *
            (starRingEnd ℂ) (exponentialPolynomialRealFeature lambda mult j s)) ∂volume := by
            apply MeasureTheory.integral_congr_ae
            exact Filter.Eventually.of_forall fun s => by ring
      _ = c j * ∫ s in Set.Icc a b, exponentialPolynomialRealFeature lambda mult i s *
            (starRingEnd ℂ) (exponentialPolynomialRealFeature lambda mult j s) ∂volume := by
          rw [MeasureTheory.integral_const_mul]
      _ = (∫ s in Set.Icc a b, exponentialPolynomialRealFeature lambda mult i s *
            (starRingEnd ℂ) (exponentialPolynomialRealFeature lambda mult j s) ∂volume) * c j :=
          mul_comm _ _
  · intro j _
    have h := exponentialPolynomialRealFeature_pair_integrable lambda mult a b i j
    exact (h.const_mul (c j)).congr
      (Filter.Eventually.of_forall fun s => by ring)

/-- Every finite exponential-polynomial moment vector is realized by a compactly supported input. -/
theorem exponentialPolynomialMoment_surjective
    {r : ℕ} {lambda : Fin r → ℂ} (hlambda : Function.Injective lambda)
    (mult : Fin r → ℕ) {a b : ℝ} (hab : a < b) :
    Function.Surjective (exponentialPolynomialMoment lambda mult) := by
  intro y
  obtain ⟨c, hc⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr
    (exponentialPolynomialIntervalGram_posDef hlambda mult hab).isUnit y
  refine ⟨exponentialPolynomialIntervalSynthesis lambda mult a b c, ?_⟩
  rw [exponentialPolynomialMoment_intervalSynthesis]
  exact hc

end

end RHTower

import GaloisForLFunctions.HTGeometry.GaussianGridSamplingAlgebra
import GaloisForLFunctions.HTGeometry.GaussianHasseTailEnvelope

/-!
# Discrete coefficient-uniform Hasse-envelope control

The grid operator ceiling is uniform over all Hasse derivatives and the
coordinate polynomial. Combining that ceiling with factorial derivative
control bounds the complete Taylor envelope with no sample-count factor.
-/

open scoped Real SchwartzMap NNReal
open Complex MeasureTheory
noncomputable section

namespace GaloisForLFunctions

/-- A common grid norm ceiling for a degree-d polynomial, all its derivatives, and its coordinate. -/
def gaussianStripSamplingFactor (d : ℕ) (h : ℝ≥0) : ℝ :=
  Real.sqrt (1 + 2 * (h : ℝ) * Real.sqrt (4 * π * ((d : ℝ) + 2)))

/-- The grid ceiling is nonnegative. -/
theorem gaussianStripSamplingFactor_nonneg (d : ℕ) (h : ℝ≥0) :
    0 ≤ gaussianStripSamplingFactor d h := Real.sqrt_nonneg _

/-- The common ceiling bounds the entire original polynomial. -/
theorem norm_gaussianGridSamples_polyGauss_le_stripFactor (P : Polynomial ℝ)
    (a : ℝ) (h : ℝ≥0) (s : ℕ → Set.Icc (0 : ℝ) 1) (N : ℕ) :
    ‖gaussianGridSamples a h s N (polyGaussSchwartz P)‖ ≤
      gaussianStripSamplingFactor P.natDegree h *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
  refine (norm_gaussianGridSamples_polyGauss_le P a h s N).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.sqrt_le_sqrt
  apply add_le_add (le_refl 1)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.sqrt_le_sqrt
  nlinarith only [Real.pi_pos]

/-- Every Hasse derivative has the same grid ceiling as its original polynomial. -/
theorem norm_gaussianGridSamples_hasse_le_stripFactor (P : Polynomial ℝ) (k : ℕ)
    (a : ℝ) (h : ℝ≥0) (s : ℕ → Set.Icc (0 : ℝ) 1) (N : ℕ) :
    ‖gaussianGridSamples a h s N (polyGaussSchwartz (Polynomial.hasseDeriv k P))‖ ≤
      gaussianStripSamplingFactor P.natDegree h *
        ‖(polyGaussSchwartz (Polynomial.hasseDeriv k P)).toLp 2 (volume : Measure ℝ)‖ := by
  have hdeg : (Polynomial.hasseDeriv k P).natDegree ≤ P.natDegree :=
    (Polynomial.natDegree_hasseDeriv_le P k).trans (Nat.sub_le _ _)
  refine (norm_gaussianGridSamples_polyGauss_le _ a h s N).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.sqrt_le_sqrt
  apply add_le_add (le_refl 1)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.sqrt_le_sqrt
  have hc : ((Polynomial.hasseDeriv k P).natDegree : ℝ) ≤ (P.natDegree : ℝ) := by
    exact_mod_cast hdeg
  nlinarith only [hc, Real.pi_pos]

/-- Coordinate samples obey the oscillator bound with one common grid ceiling. -/
theorem norm_gaussianGridSamples_coordinate_le (P : Polynomial ℝ)
    (a : ℝ) (h : ℝ≥0) (s : ℕ → Set.Icc (0 : ℝ) 1) (N : ℕ) :
    2 * π * ‖gaussianGridSamples a h s N (mulXCLM (polyGaussSchwartz P))‖ ≤
      gaussianStripSamplingFactor P.natDegree h *
        Real.sqrt (4 * π * ((P.natDegree : ℝ) + 1)) *
          ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
  have hdeg : (Polynomial.X * P).natDegree ≤ P.natDegree + 1 := by
    have ht := Polynomial.natDegree_mul_le (p := (Polynomial.X : Polynomial ℝ)) (q := P)
    simpa only [Polynomial.natDegree_X, add_comm] using ht
  have hsample : ‖gaussianGridSamples a h s N (polyGaussSchwartz (Polynomial.X * P))‖ ≤
      gaussianStripSamplingFactor P.natDegree h *
        ‖(polyGaussSchwartz (Polynomial.X * P)).toLp 2 (volume : Measure ℝ)‖ := by
    refine (norm_gaussianGridSamples_polyGauss_le _ a h s N).trans ?_
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Real.sqrt_le_sqrt
    apply add_le_add (le_refl 1)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.sqrt_le_sqrt
    have hc : ((Polynomial.X * P).natDegree : ℝ) ≤ (P.natDegree : ℝ) + 1 := by
      exact_mod_cast hdeg
    nlinarith only [hc, Real.pi_pos]
  rw [← mulXCLM_polyGauss_eq] at hsample
  have hs := mul_le_mul_of_nonneg_left hsample (by positivity : (0 : ℝ) ≤ 2 * π)
  have hc := mul_le_mul_of_nonneg_left (gaussianPolynomialCoordinateNorm_le P)
    (gaussianStripSamplingFactor_nonneg P.natDegree h)
  nlinarith only [hs, hc]

/-- The sampled simultaneous Hasse tail has no factor depending on sample count. -/
theorem norm_gaussianGridSamples_hasseEnvelope_le (P : Polynomial ℝ) (R : ℝ≥0)
    (a : ℝ) (h : ℝ≥0) (s : ℕ → Set.Icc (0 : ℝ) 1) (N : ℕ) :
    ‖gaussianGridSamples a h s N (fun x => (gaussianHasseTailEnvelope P R x : ℂ))‖ ≤
      gaussianStripSamplingFactor P.natDegree h *
        (Real.exp ((R : ℝ) * Real.sqrt (4 * π * P.natDegree)) - 1) *
          ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
  let A : ℝ := Real.sqrt (4 * π * P.natDegree)
  let M : ℝ := ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖
  let C : ℝ := gaussianStripSamplingFactor P.natDegree h
  have hC : 0 ≤ C := gaussianStripSamplingFactor_nonneg _ _
  have hterm (k : ℕ) :
      ‖gaussianGridSamples a h s N (fun x =>
        (((R : ℝ) ^ k : ℝ) : ℂ) * (‖polyGaussSchwartz (Polynomial.hasseDeriv k P) x‖ : ℂ))‖ ≤
        (((R : ℝ) * A) ^ k / (k.factorial : ℝ)) * (C * M) := by
    rw [gaussianGridSamples_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (R : ℝ) ^ k), norm_gaussianGridSamples_norm]
    have hfac : (0 : ℝ) < k.factorial := by positivity
    have hd := gaussianHasseDerivativeFactorialNorm_le P k
    have hd' : ‖(polyGaussSchwartz (Polynomial.hasseDeriv k P)).toLp 2 (volume : Measure ℝ)‖ ≤
        A ^ k * M / (k.factorial : ℝ) := by
      rw [le_div_iff₀ hfac]
      simpa only [A, M, mul_comm] using hd
    calc
      _ ≤ (R : ℝ) ^ k * (C *
          ‖(polyGaussSchwartz (Polynomial.hasseDeriv k P)).toLp 2 (volume : Measure ℝ)‖) :=
        mul_le_mul_of_nonneg_left (norm_gaussianGridSamples_hasse_le_stripFactor P k a h s N)
          (by positivity)
      _ ≤ (R : ℝ) ^ k * (C * (A ^ k * M / (k.factorial : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd' hC) (by positivity)
      _ = _ := by ring
  have hexp : HasSum (fun k : ℕ => ((R : ℝ) * A) ^ k / (k.factorial : ℝ))
      (Real.exp ((R : ℝ) * A)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp ((R : ℝ) * A)
  have hfull := hexp.summable.sum_le_tsum (Finset.range (P.natDegree + 1))
    (fun _ _ => by positivity)
  rw [hexp.tsum_eq, Finset.sum_range_succ'] at hfull
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hfull
  have htail : (∑ k ∈ Finset.range P.natDegree,
      ((R : ℝ) * A) ^ (k + 1) / ((k + 1).factorial : ℝ)) ≤
      Real.exp ((R : ℝ) * A) - 1 := by linarith only [hfull]
  have he : (fun x => (gaussianHasseTailEnvelope P R x : ℂ)) =
      fun x => ∑ k ∈ Finset.range P.natDegree,
        (((R : ℝ) ^ (k + 1) : ℝ) : ℂ) *
          (‖polyGaussSchwartz (Polynomial.hasseDeriv (k + 1) P) x‖ : ℂ) := by
    funext x
    simp only [gaussianHasseTailEnvelope, Complex.ofReal_sum, Complex.ofReal_mul]
  rw [he, gaussianGridSamples_sum]
  calc
    _ ≤ ∑ k ∈ Finset.range P.natDegree,
        ‖gaussianGridSamples a h s N (fun x =>
          (((R : ℝ) ^ (k + 1) : ℝ) : ℂ) *
            (‖polyGaussSchwartz (Polynomial.hasseDeriv (k + 1) P) x‖ : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range P.natDegree,
        (((R : ℝ) * A) ^ (k + 1) / ((k + 1).factorial : ℝ) * (C * M)) :=
      Finset.sum_le_sum fun k _ => hterm (k + 1)
    _ = (∑ k ∈ Finset.range P.natDegree,
        ((R : ℝ) * A) ^ (k + 1) / ((k + 1).factorial : ℝ)) * (C * M) := by
      rw [Finset.sum_mul]
    _ ≤ (Real.exp ((R : ℝ) * A) - 1) * (C * M) :=
      mul_le_mul_of_nonneg_right htail (mul_nonneg hC (norm_nonneg _))
    _ = _ := by dsimp [C, A, M]; ring

end GaloisForLFunctions

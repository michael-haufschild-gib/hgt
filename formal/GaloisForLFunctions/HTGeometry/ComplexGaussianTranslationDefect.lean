import GaloisForLFunctions.HTGeometry.ComplexGaussianPolynomialTranslation

/-!
# Relative Gaussian energy of a complex polynomial translation defect

Removing the zeroth Hasse term improves the translation envelope from exp(b)
to exp(b)-1. The estimate is uniform over every coefficient vector, including
zero and constant polynomials. This concerns the polynomial factor against
the fixed real Gaussian; the complex Gaussian phase and transfer to the
actual Xi counting measure are separate obligations.
-/

open scoped Real SchwartzMap
open Complex MeasureTheory
noncomputable section

namespace GaloisForLFunctions

/-- The exact translation defect is the complete nonconstant Hasse tail. -/
theorem complexTranslatedPolyGauss_sub_eq_sum (P : Polynomial ℝ) (z : ℂ) :
    complexTranslatedPolyGauss P z - polyGaussSchwartz P =
      ∑ k ∈ Finset.range P.natDegree,
        z ^ (k + 1) • polyGaussSchwartz (Polynomial.hasseDeriv (k + 1) P) := by
  rw [complexTranslatedPolyGauss, Finset.sum_range_succ']
  simp only [pow_zero, one_smul, Polynomial.hasseDeriv_zero', add_sub_cancel_right]

/-- Coefficient-uniform relative translation error with a vanishing exponential factor. -/
theorem norm_complexTranslatedPolyGauss_sub_le (P : Polynomial ℝ) (z : ℂ) :
    ‖(complexTranslatedPolyGauss P z - polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ≤
      (Real.exp (‖z‖ * Real.sqrt (4 * π * P.natDegree)) - 1) *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
  let A : ℝ := Real.sqrt (4 * π * P.natDegree)
  let N : ℝ := ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖
  have hterm (k : ℕ) :
      ‖(z ^ k • polyGaussSchwartz (Polynomial.hasseDeriv k P)).toLp 2
          (volume : Measure ℝ)‖ ≤ ((‖z‖ * A) ^ k / (k.factorial : ℝ)) * N := by
    have hfac : (0 : ℝ) < k.factorial := by positivity
    have hh := gaussianHasseDerivativeFactorialNorm_le P k
    have hh' :
        ‖(polyGaussSchwartz (Polynomial.hasseDeriv k P)).toLp 2 (volume : Measure ℝ)‖ ≤
          A ^ k * N / (k.factorial : ℝ) := by
      rw [le_div_iff₀ hfac]
      simpa only [A, N, mul_comm] using hh
    rw [toLp_smul, norm_smul, norm_pow]
    calc
      _ ≤ ‖z‖ ^ k * (A ^ k * N / (k.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left hh' (by positivity)
      _ = _ := by ring
  have hexp : HasSum (fun k : ℕ => (‖z‖ * A) ^ k / (k.factorial : ℝ))
      (Real.exp (‖z‖ * A)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (‖z‖ * A)
  have hfull :
      (∑ k ∈ Finset.range (P.natDegree + 1), (‖z‖ * A) ^ k / (k.factorial : ℝ)) ≤
        Real.exp (‖z‖ * A) := by
    calc
      _ ≤ ∑' k : ℕ, (‖z‖ * A) ^ k / (k.factorial : ℝ) :=
        hexp.summable.sum_le_tsum _ (fun _ _ => by positivity)
      _ = _ := hexp.tsum_eq
  have htail :
      (∑ k ∈ Finset.range P.natDegree, (‖z‖ * A) ^ (k + 1) / ((k + 1).factorial : ℝ)) ≤
        Real.exp (‖z‖ * A) - 1 := by
    rw [Finset.sum_range_succ'] at hfull
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hfull
    linarith only [hfull]
  calc
    _ ≤ ∑ k ∈ Finset.range P.natDegree,
        ‖(z ^ (k + 1) • polyGaussSchwartz (Polynomial.hasseDeriv (k + 1) P)).toLp 2
          (volume : Measure ℝ)‖ := by
      rw [complexTranslatedPolyGauss_sub_eq_sum]
      change ‖(SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ))
        (∑ k ∈ Finset.range P.natDegree,
          z ^ (k + 1) • polyGaussSchwartz (Polynomial.hasseDeriv (k + 1) P))‖ ≤ _
      rw [map_sum]
      exact norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range P.natDegree,
        (((‖z‖ * A) ^ (k + 1) / ((k + 1).factorial : ℝ)) * N) :=
      Finset.sum_le_sum fun k _ => hterm (k + 1)
    _ = (∑ k ∈ Finset.range P.natDegree,
        (‖z‖ * A) ^ (k + 1) / ((k + 1).factorial : ℝ)) * N := by rw [Finset.sum_mul]
    _ ≤ (Real.exp (‖z‖ * A) - 1) * N :=
      mul_le_mul_of_nonneg_right htail (norm_nonneg _)

/-- The same relative error controls the even polynomial used by the Xi heat form. -/
theorem norm_complexTranslatedEvenPolyGauss_sub_le (P : Polynomial ℝ) (z : ℂ) :
    ‖(complexTranslatedPolyGauss (evenSquarePolynomial P) z -
        polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ ≤
      (Real.exp (‖z‖ * Real.sqrt (8 * π * P.natDegree)) - 1) *
        ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ := by
  have h := norm_complexTranslatedPolyGauss_sub_le (evenSquarePolynomial P) z
  rw [natDegree_evenSquarePolynomial] at h
  have he : 4 * π * ((2 * P.natDegree : ℕ) : ℝ) = 8 * π * (P.natDegree : ℝ) := by
    push_cast
    ring
  rwa [he] at h

/-- A lower norm margin follows without a nonzero-polynomial or small-shift premise. -/
theorem norm_complexTranslatedPolyGauss_lower_margin (P : Polynomial ℝ) (z : ℂ) :
    (2 - Real.exp (‖z‖ * Real.sqrt (4 * π * P.natDegree))) *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ≤
      ‖(complexTranslatedPolyGauss P z).toLp 2 (volume : Measure ℝ)‖ := by
  have h := norm_complexTranslatedPolyGauss_sub_le P z
  have htriangle := norm_le_norm_add_norm_sub
    ((complexTranslatedPolyGauss P z).toLp 2 (volume : Measure ℝ))
    ((polyGaussSchwartz P).toLp 2 (volume : Measure ℝ))
  have hmap := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).map_sub
    (complexTranslatedPolyGauss P z) (polyGaussSchwartz P)
  rw [SchwartzMap.toLpCLM_apply, SchwartzMap.toLpCLM_apply,
    SchwartzMap.toLpCLM_apply] at hmap
  rw [hmap] at h
  nlinarith only [h, htriangle]

end GaloisForLFunctions

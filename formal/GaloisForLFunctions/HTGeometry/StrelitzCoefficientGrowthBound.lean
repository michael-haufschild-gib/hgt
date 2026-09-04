import GaloisForLFunctions.HTGeometry.StrelitzNormalizedLeadingBound

/-!
# Polynomial growth of Strelitz coefficient families

Every coefficient in the function-value decomposition is a two-variable logarithmic-jet
polynomial with polynomial dependence on the independent variable.  This module gives one explicit
power of a common radius and one finite constant controlling any subfamily of those coefficients.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Largest crude radius exponent among the logarithmic-jet coefficients of `Q`. -/
def strelitzCoefficientGrowthDegree
    (Q : MvPolynomial (Fin 3) (Polynomial ℂ)) : ℕ :=
  (strelitzValueSupport Q).sup fun d =>
    polynomialMvCoeffDegree (strelitzValueCoeff Q d) +
      3 * (strelitzValueCoeff Q d).totalDegree

/-- Sum of explicit growth constants for all logarithmic-jet coefficients of `Q`. -/
def strelitzCoefficientGrowthConstant
    (Q : MvPolynomial (Fin 3) (Polynomial ℂ)) : ℝ :=
  ∑ d ∈ strelitzValueSupport Q,
    polynomialMvCoeffNormSum (strelitzValueCoeff Q d) *
      (2 : ℝ) ^ polynomialMvCoeffDegree (strelitzValueCoeff Q d) *
      6 ^ (strelitzValueCoeff Q d).totalDegree

/-- One polynomial coefficient has a fixed power bound on the region
`|z| ≤ r`, `|U| ≤ 2r`, `|V| ≤ r²`. -/
theorem norm_eval₂_polynomialCoeff_le_rpow
    (P : MvPolynomial (Fin 2) (Polynomial ℂ))
    (z U V : ℂ) {r : ℝ} (hr : 1 ≤ r)
    (hz : ‖z‖ ≤ r) (hU : ‖U‖ ≤ 2 * r) (hV : ‖V‖ ≤ r ^ 2) :
    ‖MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![U, V] P‖ ≤
      polynomialMvCoeffNormSum P *
        (2 : ℝ) ^ polynomialMvCoeffDegree P * 6 ^ P.totalDegree *
        r ^ (polynomialMvCoeffDegree P + 3 * P.totalDegree) := by
  have hbase := norm_eval₂_le_polynomialMvCoeffNormSum P z ![U, V]
  rw [Fin.prod_univ_two] at hbase
  have hzbase : 1 + ‖z‖ ≤ 2 * r := by linarith
  have hUbase : 1 + ‖U‖ ≤ 3 * r := by linarith
  have hVbase : 1 + ‖V‖ ≤ 2 * r ^ 2 := by nlinarith
  have hzpow : (1 + ‖z‖) ^ polynomialMvCoeffDegree P ≤
      (2 * r) ^ polynomialMvCoeffDegree P :=
    pow_le_pow_left₀ (by positivity) hzbase _
  have hUpow : (1 + ‖U‖) ^ P.totalDegree ≤ (3 * r) ^ P.totalDegree :=
    pow_le_pow_left₀ (by positivity) hUbase _
  have hVpow : (1 + ‖V‖) ^ P.totalDegree ≤ (2 * r ^ 2) ^ P.totalDegree :=
    pow_le_pow_left₀ (by positivity) hVbase _
  have hCnonneg : 0 ≤ polynomialMvCoeffNormSum P := by
    rw [polynomialMvCoeffNormSum]
    exact Finset.sum_nonneg fun e he => coeffNormSum_nonneg _
  refine hbase.trans ?_
  have hmul :
      polynomialMvCoeffNormSum P * (1 + ‖z‖) ^ polynomialMvCoeffDegree P *
          ((1 + ‖U‖) ^ P.totalDegree * (1 + ‖V‖) ^ P.totalDegree) ≤
        polynomialMvCoeffNormSum P * (2 * r) ^ polynomialMvCoeffDegree P *
          ((3 * r) ^ P.totalDegree * (2 * r ^ 2) ^ P.totalDegree) := by
    have hzstep := mul_le_mul_of_nonneg_left hzpow hCnonneg
    have huv := mul_le_mul hUpow hVpow (by positivity) (by positivity)
    exact mul_le_mul hzstep huv (by positivity)
      (mul_nonneg hCnonneg (pow_nonneg (by positivity) _))
  refine hmul.trans_eq ?_
  rw [mul_pow, mul_pow, mul_pow]
  have hr2pow : (r ^ 2) ^ P.totalDegree = r ^ (2 * P.totalDegree) := by
    exact (pow_mul r 2 P.totalDegree).symm
  have hsix : (6 : ℝ) ^ P.totalDegree =
      3 ^ P.totalDegree * 2 ^ P.totalDegree := by
    rw [← mul_pow]
    norm_num
  have hrpow : r ^ (polynomialMvCoeffDegree P + 3 * P.totalDegree) =
      r ^ polynomialMvCoeffDegree P *
        (r ^ P.totalDegree * r ^ (2 * P.totalDegree)) := by
    rw [pow_add]
    congr 1
    rw [show 3 * P.totalDegree = P.totalDegree + 2 * P.totalDegree by omega, pow_add]
  rw [hr2pow, hrpow, hsix]
  ring

/-- **Uniform finite-family bound.** Every subfamily of value coefficients is bounded by the same
explicit constant and radius power attached to `Q`. -/
theorem sum_norm_eval₂_strelitzValueCoeff_le
    (Q : MvPolynomial (Fin 3) (Polynomial ℂ))
    (S : Finset ℕ) (hS : S ⊆ strelitzValueSupport Q)
    (z U V : ℂ) {r : ℝ} (hr : 1 ≤ r)
    (hz : ‖z‖ ≤ r) (hU : ‖U‖ ≤ 2 * r) (hV : ‖V‖ ≤ r ^ 2) :
    ∑ d ∈ S, ‖MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![U, V]
        (strelitzValueCoeff Q d)‖ ≤
      strelitzCoefficientGrowthConstant Q *
        r ^ strelitzCoefficientGrowthDegree Q := by
  classical
  calc
    ∑ d ∈ S, ‖MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![U, V]
        (strelitzValueCoeff Q d)‖ ≤
        ∑ d ∈ S,
          (polynomialMvCoeffNormSum (strelitzValueCoeff Q d) *
            (2 : ℝ) ^ polynomialMvCoeffDegree (strelitzValueCoeff Q d) *
            6 ^ (strelitzValueCoeff Q d).totalDegree) *
              r ^ strelitzCoefficientGrowthDegree Q := by
      exact Finset.sum_le_sum fun d hd => by
        have hbound := norm_eval₂_polynomialCoeff_le_rpow
          (strelitzValueCoeff Q d) z U V hr hz hU hV
        have hdeg : polynomialMvCoeffDegree (strelitzValueCoeff Q d) +
            3 * (strelitzValueCoeff Q d).totalDegree ≤
            strelitzCoefficientGrowthDegree Q := by
          exact Finset.le_sup (f := fun e =>
            polynomialMvCoeffDegree (strelitzValueCoeff Q e) +
              3 * (strelitzValueCoeff Q e).totalDegree) (hS hd)
        refine hbound.trans ?_
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hr hdeg)
          (mul_nonneg
            (mul_nonneg (by
              rw [polynomialMvCoeffNormSum]
              exact Finset.sum_nonneg fun e he => coeffNormSum_nonneg _)
              (pow_nonneg (by norm_num) _))
            (pow_nonneg (by norm_num) _))
    _ ≤ ∑ d ∈ strelitzValueSupport Q,
          (polynomialMvCoeffNormSum (strelitzValueCoeff Q d) *
            (2 : ℝ) ^ polynomialMvCoeffDegree (strelitzValueCoeff Q d) *
            6 ^ (strelitzValueCoeff Q d).totalDegree) *
              r ^ strelitzCoefficientGrowthDegree Q := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hS fun d hdQ hdnot => by
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (by
              rw [polynomialMvCoeffNormSum]
              exact Finset.sum_nonneg fun e he => coeffNormSum_nonneg _)
              (pow_nonneg (by norm_num) _))
            (pow_nonneg (by norm_num) _))
          (pow_nonneg (by linarith) _)
    _ = strelitzCoefficientGrowthConstant Q *
        r ^ strelitzCoefficientGrowthDegree Q := by
      rw [strelitzCoefficientGrowthConstant, Finset.sum_mul]

end

end GaloisForLFunctions.HTGeometry

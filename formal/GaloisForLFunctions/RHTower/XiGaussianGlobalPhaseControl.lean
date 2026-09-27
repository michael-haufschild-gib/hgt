import GaloisForLFunctions.RHTower.XiGaussianNativeMassScale
import GaloisForLFunctions.RHTower.XiGaussianDebtDomination
import GaloisForLFunctions.RHTower.XiHeatThirdScaledPositivity
import GaloisForLFunctions.RHTower.XiPolynomialGaussianExplicitFormula
import GaloisForLFunctions.HTGeometry.GaussianGlobalVerticalSlope

/-!
# Full Xi phase control at every positive heat time

An explicit degree-only budget bounds the full phase debt in native Gaussian
mass. The same bound controls the signed prime source after retaining both the
polar residue and the Gamma contribution. It bounds possible negativity; it
does not establish a sign for the complete heat form.
-/

open scoped Real SchwartzMap NNReal
open MeasureTheory GaloisForLFunctions
noncomputable section

namespace RHTower

/-- A coefficient-independent native-mass budget at arbitrary positive heat time. -/
def xiGaussianGlobalPhaseBudget (d : ℕ) (t : {t : ℝ // 0 < t}) : ℝ :=
  (198 / 3175 : ℝ) * (xiGaussianHeatScale t : ℝ) *
    gaussianGlobalVerticalSlopeEnvelope d ((xiGaussianHeatScale t : ℝ) / 2) ^ 2

theorem xiGaussianGlobalPhaseBudget_nonneg (d : ℕ) (t : {t : ℝ // 0 < t}) :
    0 ≤ xiGaussianGlobalPhaseBudget d t := by
  have hr := (xiGaussianHeatScale t).property
  unfold xiGaussianGlobalPhaseBudget
  positivity

theorem xiGaussianGlobalPhaseBudget_mono (t : {t : ℝ // 0 < t}) :
    Monotone (fun d : ℕ => xiGaussianGlobalPhaseBudget d t) := by
  intro d e hde
  let R : ℝ≥0 := ⟨(xiGaussianHeatScale t : ℝ) / 2,
    div_nonneg (xiGaussianHeatScale t).property.le (by positivity)⟩
  have h := pow_le_pow_left₀ (gaussianGlobalVerticalSlopeEnvelope_nonneg d R)
    (gaussianGlobalVerticalSlopeEnvelope_mono R hde) 2
  exact mul_le_mul_of_nonneg_left h
    (mul_nonneg (by positivity) (xiGaussianHeatScale t).property.le)

/-- The mixed radius-degree exponent has an exact native heat-time expression. -/
theorem xiGaussianHeatScale_mul_degreeRoot (d : ℕ) (t : {t : ℝ // 0 < t}) :
    (xiGaussianHeatScale t : ℝ) * Real.sqrt (4 * π * ((d : ℝ) + 2)) =
      Real.sqrt (2 * (t : ℝ) * ((d : ℝ) + 2)) := by
  change Real.sqrt ((t : ℝ) / (2 * π)) * Real.sqrt (4 * π * ((d : ℝ) + 2)) = _
  rw [← Real.sqrt_mul (div_nonneg t.property.le (by positivity))]
  congr 1
  field_simp
  ring

/-- The exact exponent is `t/4 + r sqrt(4π(d+2))`, with `r² = t/(2π)`. -/
theorem xiGaussianGlobalPhaseBudget_eq (d : ℕ) (t : {t : ℝ // 0 < t}) :
    xiGaussianGlobalPhaseBudget d t =
      (198 / 3175 : ℝ) * (xiGaussianHeatScale t : ℝ) *
        (1 + 2 * Real.sqrt (4 * π * ((d : ℝ) + 3))) *
          Real.exp ((t : ℝ) / 4 + (xiGaussianHeatScale t : ℝ) *
            Real.sqrt (4 * π * ((d : ℝ) + 2))) *
          (4 * (d : ℝ) + 9 + 3 / 4 * (xiGaussianHeatScale t : ℝ) *
            Real.sqrt (4 * π * ((d : ℝ) + 2))) ^ 2 := by
  have hheat := congrArg Subtype.val (xiGaussianScaleHeat_heatScale t)
  change 2 * π * (xiGaussianHeatScale t : ℝ) ^ 2 = (t : ℝ) at hheat
  have hC : gaussianStripSamplingFactor (d + 1) 1 ^ 2 =
      1 + 2 * Real.sqrt (4 * π * ((d : ℝ) + 3)) := by
    unfold gaussianStripSamplingFactor
    rw [Real.sq_sqrt (by positivity)]
    simp only [NNReal.coe_one, Nat.cast_add, Nat.cast_one, mul_one]
    congr 3
    ring
  have he : (Real.exp (π * ((xiGaussianHeatScale t : ℝ) / 2) ^ 2 +
      (xiGaussianHeatScale t : ℝ) / 2 * Real.sqrt (4 * π * ((d : ℝ) + 2)))) ^ 2 =
      Real.exp ((t : ℝ) / 4 + (xiGaussianHeatScale t : ℝ) *
        Real.sqrt (4 * π * ((d : ℝ) + 2))) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    nlinarith only [hheat]
  unfold xiGaussianGlobalPhaseBudget gaussianGlobalVerticalSlopeEnvelope
  rw [mul_pow, mul_pow, hC, he]
  ring

/-- Full-divisor phase debt is controlled uniformly over all coefficients and positive times. -/
theorem xiScaledEvenGaussianPhaseDebt_unscale_le_global (Q : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) :
    xiScaledEvenGaussianPhaseDebt (xiGaussianUnscalePolynomial Q (xiGaussianHeatScale t))
        (xiGaussianHeatScale t) ≤
      xiGaussianGlobalPhaseBudget (2 * Q.natDegree) t * routeUPolynomialGaussianMass Q t := by
  let r := xiGaussianHeatScale t
  let R : ℝ≥0 := ⟨(r : ℝ) / 2, div_nonneg r.property.le (by positivity)⟩
  have hT := pow_le_pow_left₀ (gaussianCoordinateVerticalSlope_nonneg (2 * Q.natDegree) R)
    (gaussianCoordinateVerticalSlope_le_globalEnvelope (2 * Q.natDegree) R) 2
  have hbudget : xiGaussianSlopePhaseBudget (2 * Q.natDegree) r ≤
      (198 / 3175 : ℝ) * gaussianGlobalVerticalSlopeEnvelope (2 * Q.natDegree) R ^ 2 :=
    mul_le_mul xiHeatInverseNormMass_le hT (sq_nonneg _) (by positivity)
  have h := xiScaledEvenGaussianPhaseDebt_le_slope (xiGaussianUnscalePolynomial Q r) r
  rw [natDegree_xiGaussianUnscalePolynomial, xiGaussianUnscalePolynomial_norm_sq] at h
  calc
    _ ≤ xiGaussianSlopePhaseBudget (2 * Q.natDegree) r *
        ((r : ℝ) * routeUPolynomialGaussianMass Q t) := h
    _ ≤ ((198 / 3175 : ℝ) * gaussianGlobalVerticalSlopeEnvelope (2 * Q.natDegree) R ^ 2) *
        ((r : ℝ) * routeUPolynomialGaussianMass Q t) :=
      mul_le_mul_of_nonneg_right hbudget
        (mul_nonneg r.property.le (routeUPolynomialGaussianMass_nonneg Q t))
    _ = xiGaussianGlobalPhaseBudget (2 * Q.natDegree) t * routeUPolynomialGaussianMass Q t := by
      unfold xiGaussianGlobalPhaseBudget
      change ((198 / 3175 : ℝ) * gaussianGlobalVerticalSlopeEnvelope (2 * Q.natDegree)
        ((xiGaussianHeatScale t : ℝ) / 2) ^ 2) *
          ((xiGaussianHeatScale t : ℝ) * routeUPolynomialGaussianMass Q t) = _
      ring

/-- An unconditional native-norm lower bound for every complete polynomial heat form. -/
theorem xiPolynomialGaussianHeatTraceReal_ge_neg_globalPhaseBudget (Q : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) :
    -(xiGaussianGlobalPhaseBudget (2 * Q.natDegree) t * routeUPolynomialGaussianMass Q t) ≤
      xiPolynomialGaussianHeatTraceReal Q t := by
  let r := xiGaussianHeatScale t
  let P := xiGaussianUnscalePolynomial Q r
  have heq := xiScaledEvenGaussian_trace_eq_energy_sub_debt P r
  change xiPolynomialGaussianHeatTraceReal (P.comp (Polynomial.C ((r : ℝ) ^ 2) * Polynomial.X))
      (xiGaussianScaleHeat r : ℝ) = _ at heq
  dsimp only [P, r] at heq
  rw [xiGaussianUnscalePolynomial_comp_scale, xiGaussianScaleHeat_heatScale] at heq
  rw [heq]
  have hD := xiScaledEvenGaussianPhaseDebt_unscale_le_global Q t
  have hK := xiScaledEvenGaussianEnergy_nonneg P r
  linarith only [hD, hK]

/-- Signed prime excess retains the polar term and the complete Gamma integral. -/
theorem routeUPolynomialGaussianPrimeSource_sub_polarGamma_le_globalPhaseBudget
    (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) :
    (routeUPolynomialGaussianPrimeSource Q t).re -
        2 * π * (Q.eval (-(1 / 4 : ℝ))) ^ 2 * Real.exp ((t : ℝ) / 4) -
        (∫ x : ℝ, ‖routeUPolynomialGaussianDensity Q t x‖ * gammaHardyPhaseRate x) ≤
      π * xiGaussianGlobalPhaseBudget (2 * Q.natDegree) t * routeUPolynomialGaussianMass Q t := by
  have h := mul_le_mul_of_nonneg_left
    (xiPolynomialGaussianHeatTraceReal_ge_neg_globalPhaseBudget Q t) Real.pi_pos.le
  have heq := pi_mul_xiPolynomialGaussianHeatTraceReal_eq_primeGamma Q t
  nlinarith only [h, heq]

/-- Every full Hankel order and every coefficient direction obey the same degree ceiling. -/
theorem xiHeatHankelForm_ge_neg_globalPhaseBudget (N : ℕ) (a : ℕ → ℝ)
    (t : {t : ℝ // 0 < t}) :
    -(xiGaussianGlobalPhaseBudget (2 * N) t * routeUPolynomialGaussianMass
      (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t) ≤
      xiHeatHankelForm N a t := by
  classical
  let Q : Polynomial ℝ := ∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j
  have hd : Q.natDegree ≤ N := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    exact (Polynomial.natDegree_C_mul_X_pow_le (a j) j).trans (Finset.mem_range.mp hj).le
  have hB := mul_le_mul_of_nonneg_right
    (xiGaussianGlobalPhaseBudget_mono t (Nat.mul_le_mul_left 2 hd))
    (routeUPolynomialGaussianMass_nonneg Q t)
  have h := (neg_le_neg hB).trans (xiPolynomialGaussianHeatTraceReal_ge_neg_globalPhaseBudget Q t)
  dsimp only [Q] at h
  rwa [xiPolynomialGaussianHeatTraceReal_rangeSum t.property] at h

/-- The complete actual three-by-three form, including all three mixed terms. -/
theorem xiHeatThirdQuadratic_ge_neg_globalPhaseBudget (a b c : ℝ)
    (t : {t : ℝ // 0 < t}) :
    -(xiGaussianGlobalPhaseBudget 4 t * routeUPolynomialGaussianMass
      (xiHeatThirdPolynomial a b c) t) ≤ xiHeatThirdQuadratic a b c t := by
  have hd : (xiHeatThirdPolynomial a b c).natDegree ≤ 2 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · apply Polynomial.natDegree_add_le_of_degree_le
      · simp only [Polynomial.natDegree_C]; omega
      · have h := Polynomial.natDegree_C_mul_X_pow_le b 1
        simp only [pow_one] at h
        omega
    · exact Polynomial.natDegree_C_mul_X_pow_le c 2
  have hB := mul_le_mul_of_nonneg_right
    (xiGaussianGlobalPhaseBudget_mono t (show 2 * (xiHeatThirdPolynomial a b c).natDegree ≤ 4 by
      omega)) (routeUPolynomialGaussianMass_nonneg (xiHeatThirdPolynomial a b c) t)
  have h := (neg_le_neg hB).trans
    (xiPolynomialGaussianHeatTraceReal_ge_neg_globalPhaseBudget (xiHeatThirdPolynomial a b c) t)
  have heq := xiHeatThirdQuadratic_eq_trace a b c (Real.log (t : ℝ))
  rw [Real.exp_log t.property] at heq
  rwa [heq]

end RHTower

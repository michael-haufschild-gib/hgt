import GaloisForLFunctions.RHTower.LevinsonLinearOptimizationInterior

/-!
# A positive Levinson scalar margin with a shorter mollifier

At exponent `13/50` the linear scalar constant is below `18/5`, which is
strictly below `exp(13/10)`. This exponent also permits a Weyl estimate on
the low-height part: with split exponent `53/100`, the head exponent is
`791/800<1` and the remaining local mollifier exponent is `26/53<1/2`.
-/

open MeasureTheory
open RHTower

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

private def shortScalarA : ℝ := 1 + (13 / 50) * (3 / 10) + (13 / 50) ^ 2 * (3 / 10) ^ 2 / 3
private def shortScalarB : ℝ := -2 + (13 / 50) * (1 - 2 * (13 / 10)) -
  2 * (13 / 50) ^ 2 * (13 / 10) * (3 / 10) / 3
private def shortScalarC : ℝ := 1 + (13 / 50) * (13 / 10) + (13 / 50) ^ 2 * (13 / 10) ^ 2 / 3
private def shortScalarPolynomial (v : ℝ) : ℝ := shortScalarA + shortScalarB * v + shortScalarC * v ^ 2

private theorem shortScalar_inner_integral (v : ℝ) :
    (∫ u in (0 : ℝ)..1, levinsonLinearOptimizationDerivativeAt (13 / 50) u v ^ 2) =
      shortScalarPolynomial v := by
  let A : ℝ := 1 - v
  let B : ℝ := (13 / 50) * ((13 / 10) * (1 - v) - 1)
  let F : ℝ → ℝ := fun u => A ^ 2 * u + (A * B) * u ^ 2 + (B ^ 2 / 3) * u ^ 3
  have hd (u : ℝ) : HasDerivAt F (levinsonLinearOptimizationDerivativeAt (13 / 50) u v ^ 2) u := by
    have hh := (((hasDerivAt_id u).const_mul (A ^ 2)).add
      (((hasDerivAt_id u).pow 2).const_mul (A * B))).add
      (((hasDerivAt_id u).pow 3).const_mul (B ^ 2 / 3))
    change HasDerivAt F _ u at hh
    exact hh.congr_deriv (by
      dsimp only [A, B, levinsonLinearOptimizationDerivativeAt]
      simp only [id_eq, Pi.pow_apply]
      ring)
  have hi : IntervalIntegrable
      (fun u : ℝ => levinsonLinearOptimizationDerivativeAt (13 / 50) u v ^ 2) volume 0 1 :=
    (show Continuous (fun u : ℝ => levinsonLinearOptimizationDerivativeAt (13 / 50) u v ^ 2) by
      unfold levinsonLinearOptimizationDerivativeAt
      fun_prop).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hi]
  dsimp only [F, A, B, shortScalarPolynomial, shortScalarA, shortScalarB, shortScalarC]
  norm_num
  ring

private def shortScalarPrimitive (v : ℝ) : ℝ :=
  Real.exp ((13 / 5) * v) *
    (shortScalarC / (13 / 5) * v ^ 2 +
      (shortScalarB / (13 / 5) - 2 * shortScalarC / (13 / 5) ^ 2) * v +
      (shortScalarA / (13 / 5) - shortScalarB / (13 / 5) ^ 2 + 2 * shortScalarC / (13 / 5) ^ 3))

private theorem hasDerivAt_shortScalarPrimitive (v : ℝ) :
    HasDerivAt shortScalarPrimitive (Real.exp ((13 / 5) * v) * shortScalarPolynomial v) v := by
  have hh := (((hasDerivAt_id v).const_mul (13 / 5 : ℝ)).exp).mul
    (((((hasDerivAt_id v).pow 2).const_mul (shortScalarC / (13 / 5))).add
      ((hasDerivAt_id v).const_mul
        (shortScalarB / (13 / 5) - 2 * shortScalarC / (13 / 5) ^ 2))).add
      (hasDerivAt_const v
        (shortScalarA / (13 / 5) - shortScalarB / (13 / 5) ^ 2 + 2 * shortScalarC / (13 / 5) ^ 3)))
  change HasDerivAt shortScalarPrimitive _ v at hh
  exact hh.congr_deriv (by
    dsimp only [shortScalarPolynomial]
    simp only [id_eq, Pi.pow_apply]
    ring)

private theorem shortScalar_exact :
    levinsonLinearOptimizationConstantAt (13 / 50) =
      1 + (50 / 13 : ℝ) * (shortScalarPrimitive 1 - shortScalarPrimitive 0) := by
  rw [levinsonLinearOptimizationConstantAt]
  norm_num
  simp_rw [shortScalar_inner_integral]
  have hi : IntervalIntegrable
      (fun v : ℝ => Real.exp ((13 / 5) * v) * shortScalarPolynomial v) volume 0 1 :=
    (show Continuous (fun v : ℝ => Real.exp ((13 / 5) * v) * shortScalarPolynomial v) by
      unfold shortScalarPolynomial
      fun_prop).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hasDerivAt_shortScalarPrimitive v) hi]

private theorem shortScalar_exponential_bounds :
    Real.exp (13 / 5 : ℝ) < 27 / 2 ∧ (18 / 5 : ℝ) < Real.exp (13 / 10) := by
  have hroot : (19 / 10 : ℝ) < Real.exp (13 / 20) ∧ Real.exp (13 / 20 : ℝ) < 19157 / 10000 := by
    have hh := Real.exp_bound (x := (13 / 20 : ℝ)) (by norm_num) (n := 12) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at hh ⊢
    obtain ⟨hl, hu⟩ := abs_le.mp hh
    constructor <;> linarith only [hl, hu]
  have h4 : Real.exp (13 / 5 : ℝ) = Real.exp (13 / 20 : ℝ) ^ 4 := by
    rw [show (13 / 5 : ℝ) = (4 : ℕ) * (13 / 20 : ℝ) by norm_num, Real.exp_nat_mul]
  have h2 : Real.exp (13 / 10 : ℝ) = Real.exp (13 / 20 : ℝ) ^ 2 := by
    rw [show (13 / 10 : ℝ) = (2 : ℕ) * (13 / 20 : ℝ) by norm_num, Real.exp_nat_mul]
  constructor
  · rw [h4]
    exact (pow_lt_pow_left₀ hroot.2 (Real.exp_pos _).le (by norm_num : (4 : ℕ) ≠ 0)).trans_le (by norm_num)
  · rw [h2]
    exact (show (18 / 5 : ℝ) < (19 / 10) ^ 2 by norm_num).trans
      (pow_lt_pow_left₀ hroot.1 (by norm_num) (by norm_num : (2 : ℕ) ≠ 0))

/-- The exact linear scalar constant at exponent `13/50` is strictly below `18/5`. -/
theorem levinsonLinearOptimizationConstantAt_thirteen_fiftieths_lt :
    levinsonLinearOptimizationConstantAt (13 / 50) < 18 / 5 := by
  rw [shortScalar_exact]
  have he := shortScalar_exponential_bounds.1
  dsimp only [shortScalarPrimitive, shortScalarA, shortScalarB, shortScalarC]
  norm_num at he ⊢
  linarith only [he]

/-- The selected scalar bound gives a strictly positive critical-zero proportion. -/
theorem levinsonShortScalar_positive_margin :
    0 < 1 - Real.log (18 / 5 : ℝ) / (13 / 10) := by
  have hlog : Real.log (18 / 5 : ℝ) < 13 / 10 := by
    apply Real.exp_lt_exp.mp
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 18 / 5)]
    exact shortScalar_exponential_bounds.2
  have hh := (div_lt_one (by norm_num : (0 : ℝ) < 13 / 10)).mpr hlog
  linarith only [hh]

/-- The low-height split is compatible with both the Weyl head estimate and the square-root barrier. -/
theorem levinsonShort_exponents :
    (13 / 50 : ℝ) / (53 / 100) = 26 / 53 ∧ (26 / 53 : ℝ) < 1 / 2 ∧
      (13 / 50 : ℝ) + (11 / 8) * (53 / 100) = 791 / 800 ∧ (791 / 800 : ℝ) < 1 := by
  norm_num

end GaloisForLFunctions.MultiscaleMollifiedZetaField

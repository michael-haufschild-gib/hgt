import GaloisForLFunctions.RHTower.XiShiftedNodalAdaptiveArithmeticSourceLanding

/-!
# Horizontal nodal jets and curvature for shifted Xi

The shifted-Xi Padé normal energy is the exact moment norm of a denominator-cleared polynomial
transport.  Its full Taylor jet at zero therefore gives a connection-free horizontal hierarchy.
The normalized second-jet curvature is exactly a positive degree factor times the Route U weighted
Turán determinant, and at one fixed admissible mass it is the literal completed
rational--Gamma-minus-von-Mangoldt landing.

These statements remove moving-admission bookkeeping.  They do not assert the remaining curvature
sign, which is the RH-equivalent open core for the nodal family.
-/

open Complex Matrix Polynomial

namespace RHTower

noncomputable section

/-- Horizontal shifted-Xi energy: the existing Padé normal energy based at the positive mass
`exp w`, with the denominator exponent forced by the degree of `P`. -/
def xiShiftedHorizontalPolynomialEnergy (w : ℝ) (P : Polynomial ℝ) (u : ℝ) : ℝ :=
  xiShiftedPadeNormalEnergy (Real.exp w) P P.natDegree u

/-- The horizontal energy at zero is the shifted-Xi moment norm of `P`. -/
theorem xiShiftedHorizontalPolynomialEnergy_zero
    (w : ℝ) (P : Polynomial ℝ) :
    xiShiftedHorizontalPolynomialEnergy w P 0 =
      HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment (Real.exp w) k).re) (P ^ (2 : ℕ)) := by
  have h := hasFPowerSeriesAt_xiShiftedPadeNormalEnergy
    (show 0 ≤ Real.exp w by positivity) P P.natDegree
  rcases h with ⟨r, hr⟩
  simpa only [xiShiftedHorizontalPolynomialEnergy,
    HTGeometry.mobiusPadeContactFPowerSeries,
    FormalMultilinearSeries.ofScalars_apply_eq, pow_zero, smul_eq_mul,
    HTGeometry.coeff_mobiusPadeContactSeries,
    Nat.choose_zero_right, one_mul, mul_one, Nat.cast_one] using
      (hr.coeff_zero (fun _ => (0 : ℝ))).symm

/-- **All-order horizontal Xi jet law.**  Every diagonal jet is an exact ascending-factorial
multiple of the next polynomial-weighted shifted-Xi moment.  This is the connection-free hierarchy
behind co-moving nodal transport. -/
theorem iteratedFDeriv_xiShiftedHorizontalPolynomialEnergy_zero
    (w : ℝ) (P : Polynomial ℝ) (j : ℕ) :
    iteratedFDeriv ℝ j (xiShiftedHorizontalPolynomialEnergy w P) 0
      (fun _ => (1 : ℝ)) =
      (-1 : ℝ) ^ j *
        (((2 * P.natDegree + 1).ascFactorial j : ℕ) : ℝ) *
        HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment (Real.exp w) k).re)
          (P ^ (2 : ℕ) * X ^ j) := by
  have h := hasFPowerSeriesAt_xiShiftedPadeNormalEnergy
    (show 0 ≤ Real.exp w by positivity) P P.natDegree
  rcases h with ⟨r, hr⟩
  rw [show xiShiftedHorizontalPolynomialEnergy w P =
      xiShiftedPadeNormalEnergy (Real.exp w) P P.natDegree by rfl]
  rw [hr.iteratedFDeriv_eq_sum_of_completeSpace (fun _ => (1 : ℝ))]
  simp only [HTGeometry.mobiusPadeContactFPowerSeries,
    FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul,
    HTGeometry.coeff_mobiusPadeContactSeries]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  simp only [nsmul_eq_mul]
  rw [Nat.ascFactorial_eq_factorial_mul_choose]
  push_cast
  ring

/-- First horizontal jet. -/
theorem hasDerivAt_xiShiftedHorizontalPolynomialEnergy_zero
    (w : ℝ) (P : Polynomial ℝ) :
    HasDerivAt (xiShiftedHorizontalPolynomialEnergy w P)
      (-((2 * P.natDegree + 1 : ℕ) : ℝ) *
        HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment (Real.exp w) k).re)
          (P ^ (2 : ℕ) * X)) 0 := by
  have h := hasFPowerSeriesAt_xiShiftedPadeNormalEnergy
    (show 0 ≤ Real.exp w by positivity) P P.natDegree
  change HasDerivAt
    (xiShiftedPadeNormalEnergy (Real.exp w) P P.natDegree) _ 0
  simpa only [xiShiftedHorizontalPolynomialEnergy,
    HTGeometry.mobiusPadeContactFPowerSeries,
    FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul,
    pow_one, Nat.cast_one, mul_one, neg_mul, one_mul,
    Nat.choose_one_right, HTGeometry.coeff_mobiusPadeContactSeries] using h.hasDerivAt

/-- Successive horizontal jets advance by the exact odd-cocycle rate `2 deg(P)+1+j`. -/
theorem iteratedFDeriv_xiShiftedHorizontalPolynomialEnergy_succ_zero
    (w : ℝ) (P : Polynomial ℝ) (j : ℕ) :
    iteratedFDeriv ℝ (j + 1) (xiShiftedHorizontalPolynomialEnergy w P) 0
      (fun _ => (1 : ℝ)) =
      -(((2 * P.natDegree + 1 + j : ℕ) : ℝ)) *
        (-1 : ℝ) ^ j *
        (((2 * P.natDegree + 1).ascFactorial j : ℕ) : ℝ) *
        HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment (Real.exp w) k).re)
          (P ^ (2 : ℕ) * X ^ (j + 1)) := by
  rw [iteratedFDeriv_xiShiftedHorizontalPolynomialEnergy_zero]
  rw [Nat.ascFactorial_succ]
  push_cast
  rw [pow_succ]
  ring

/-- Denominator-free curvature numerator of the horizontal energy. -/
def xiShiftedHorizontalPolynomialCurvature (w : ℝ) (P : Polynomial ℝ) : ℝ :=
  ((2 * P.natDegree + 1 : ℕ) : ℝ) *
      xiShiftedHorizontalPolynomialEnergy w P 0 *
        iteratedFDeriv ℝ 2 (xiShiftedHorizontalPolynomialEnergy w P) 0
          (fun _ => (1 : ℝ)) -
    ((2 * P.natDegree + 2 : ℕ) : ℝ) *
      deriv (xiShiftedHorizontalPolynomialEnergy w P) 0 ^ (2 : ℕ)

/-- **Horizontal curvature equals the Route U Turán minor.**  The degree factor is strictly
positive, while no moment-positivity premise is used. -/
theorem xiShiftedHorizontalPolynomialCurvature_eq_turan
    (w : ℝ) (P : Polynomial ℝ) :
    xiShiftedHorizontalPolynomialCurvature w P =
      (((2 * P.natDegree + 1 : ℕ) : ℝ) ^ (2 : ℕ) *
        ((2 * P.natDegree + 2 : ℕ) : ℝ)) *
          xiShiftedAdaptiveMixedMomentLanding (Real.exp w) P := by
  rw [xiShiftedHorizontalPolynomialCurvature,
    xiShiftedHorizontalPolynomialEnergy_zero,
    iteratedFDeriv_xiShiftedHorizontalPolynomialEnergy_zero,
    (hasDerivAt_xiShiftedHorizontalPolynomialEnergy_zero w P).deriv,
    xiShiftedAdaptiveMixedMomentLanding_eq_turan]
  simp only [xiShiftedPolynomialWeightedMass,
    xiShiftedPolynomialWeightedCurrent,
    xiShiftedPolynomialWeightedSecond,
    HTGeometry.momentInner_def]
  norm_num [Nat.ascFactorial]
  ring_nf

/-- **Literal completed-arithmetic curvature landing.**  At the fixed positive base mass `exp 1`,
horizontal curvature is exactly the actual rational--Gamma-minus-von-Mangoldt Route U landing at
the admissible shift `sqrt (exp 1)`. -/
theorem xiShiftedHorizontalPolynomialCurvature_one_eq_completedArithmeticLanding
    (P : Polynomial ℝ) :
    xiShiftedHorizontalPolynomialCurvature 1 P =
      (((2 * P.natDegree + 1 : ℕ) : ℝ) ^ (2 : ℕ) *
        ((2 * P.natDegree + 2 : ℕ) : ℝ)) *
          xiShiftedAdaptiveMixedCompletedArithmeticLanding
            (Real.sqrt (Real.exp 1)) P := by
  rw [xiShiftedHorizontalPolynomialCurvature_eq_turan]
  rw [xiShiftedAdaptiveMixedCompletedArithmeticLanding_eq_turan]
  · rw [Real.sq_sqrt (by positivity)]
    rw [xiShiftedAdaptiveMixedMomentLanding_eq_turan]
    simp only [xiShiftedPolynomialWeightedSecond]
  · have h : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
    nlinarith [Real.sq_sqrt (show 0 ≤ Real.exp 1 by positivity),
      Real.sqrt_pos.2 (show 0 < Real.exp 1 by positivity)]

end

end RHTower

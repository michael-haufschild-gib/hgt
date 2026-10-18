import GaloisForLFunctions.RHTower.ThetaJensenCenteredMomentBounds
import GaloisForLFunctions.RHTower.JensenQuarticXi
import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureHeightLocalizedContraction

/-!
# Polynomial expectations for the actual Xi coefficients

Normalize the positive power-tilted full theta source. Its polynomial moments
are the literal ratios of the moments defining `xiJensenCoeff`.
-/

open Real MeasureTheory Set Filter Topology Polynomial

noncomputable section

namespace RHTower

theorem integrableOn_xiTheta_polynomial (n : ℕ) (P : ℝ[X]) :
    IntegrableOn (fun x : ℝ => P.eval (x ^ 2) * x ^ (2 * n) * thetaCuspFullSource x) (Ioi 0) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    apply (hP.add hQ).congr
    filter_upwards [] with x
    simp only [eval_add, add_mul, Pi.add_apply]
  | monomial k a =>
    apply ((integrableOn_thetaCuspRawMoment (2 * (n + k))).const_mul a).congr
    filter_upwards [] with x
    simp only [eval_monomial, ← pow_mul, Nat.mul_add, pow_add]
    ring

def xiThetaExpectation (n : ℕ) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun P := (2 / thetaCuspRawEvenMoment n) *
    ∫ x : ℝ in Ioi 0, P.eval (x ^ 2) * x ^ (2 * n) * thetaCuspFullSource x
  map_add' P Q := by
    simp only [eval_add, add_mul]
    rw [integral_add (integrableOn_xiTheta_polynomial n P) (integrableOn_xiTheta_polynomial n Q)]
    ring
  map_smul' a P := by
    simp only [eval_smul, smul_eq_mul, RingHom.id_apply]
    have heq : (fun x : ℝ => a * P.eval (x ^ 2) * x ^ (2 * n) * thetaCuspFullSource x) =
        (fun x => a * (P.eval (x ^ 2) * x ^ (2 * n) * thetaCuspFullSource x)) := by
      ext x
      ring
    rw [heq, integral_const_mul]
    ring

theorem xiThetaExpectation_apply (n : ℕ) (P : ℝ[X]) :
    xiThetaExpectation n P = (2 / thetaCuspRawEvenMoment n) *
      ∫ x : ℝ in Ioi 0, P.eval (x ^ 2) * x ^ (2 * n) * thetaCuspFullSource x := rfl

theorem xiThetaExpectation_one (n : ℕ) : xiThetaExpectation n 1 = 1 := by
  rw [xiThetaExpectation_apply]
  simp only [eval_one, one_mul]
  have hm := thetaCuspRawEvenMoment_pos n
  have heq : (∫ x : ℝ in Ioi 0, x ^ (2 * n) * thetaCuspFullSource x) =
      thetaCuspRawEvenMoment n / 2 := by rw [thetaCuspRawEvenMoment]; ring
  rw [heq]
  field_simp

theorem xiThetaExpectation_C (n : ℕ) (a : ℝ) : xiThetaExpectation n (C a) = a := by
  rw [show C a = a • (1 : ℝ[X]) by rw [smul_eq_C_mul, mul_one],
    map_smul, xiThetaExpectation_one, smul_eq_mul, mul_one]

theorem xiThetaExpectation_C_mul (n : ℕ) (a : ℝ) (P : ℝ[X]) :
    xiThetaExpectation n (C a * P) = a * xiThetaExpectation n P := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul]

theorem xiThetaExpectation_X_pow (n j : ℕ) :
    xiThetaExpectation n (X ^ j) = thetaCuspRawEvenMoment (n + j) / thetaCuspRawEvenMoment n := by
  rw [xiThetaExpectation_apply]
  simp only [eval_pow, eval_X]
  have heq : (fun x : ℝ => (x ^ 2) ^ j * x ^ (2 * n) * thetaCuspFullSource x) =
      (fun x => x ^ (2 * (n + j)) * thetaCuspFullSource x) := by
    ext x
    simp only [← pow_mul, Nat.mul_add, pow_add]
    ring
  rw [heq]
  conv_rhs => rw [thetaCuspRawEvenMoment]
  ring

theorem xiThetaExpectation_nonneg (n : ℕ) {P : ℝ[X]}
    (hP : ∀ y : ℝ, 0 ≤ y → 0 ≤ P.eval y) : 0 ≤ xiThetaExpectation n P := by
  rw [xiThetaExpectation_apply]
  apply mul_nonneg (by positivity [thetaCuspRawEvenMoment_pos n])
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_nonneg (mul_nonneg (hP _ (sq_nonneg x)) (pow_nonneg hx.le _))
    (thetaCuspFullSource_pos_of_pos hx).le

def xiThetaCenteredMoment (n k : ℕ) (s : ℝ) : ℝ :=
  xiThetaExpectation n ((X - C (s ^ 2)) ^ k)

theorem xiThetaCenteredMoment_eq_integral (n k : ℕ) (s : ℝ) :
    xiThetaCenteredMoment n k s = (2 / thetaCuspRawEvenMoment n) *
      ∫ x : ℝ in Ioi 0, (x ^ 2 - s ^ 2) ^ k * x ^ (2 * n) * thetaCuspFullSource x := by
  simp only [xiThetaCenteredMoment, xiThetaExpectation_apply, eval_pow, eval_sub, eval_X, eval_C]

theorem xiThetaCenteredMoment_even_nonneg (n p : ℕ) (s : ℝ) :
    0 ≤ xiThetaCenteredMoment n (2 * p) s := by
  apply xiThetaExpectation_nonneg
  intro y hy
  simp only [eval_pow, eval_sub, eval_X, eval_C, pow_mul]
  positivity

theorem xiThetaCenteredMoment_sq_le (n k : ℕ) (s : ℝ) :
    xiThetaCenteredMoment n k s ^ 2 ≤ xiThetaCenteredMoment n (2 * k) s := by
  let Q : ℝ[X] := (X - C (s ^ 2)) ^ k
  let a := xiThetaExpectation n Q
  have hnonneg : 0 ≤ xiThetaExpectation n ((Q - C a) ^ 2) :=
    xiThetaExpectation_nonneg n (by intro y hy; simp only [eval_pow]; positivity)
  have hpoly : (Q - C a) ^ 2 = Q ^ 2 - C (2 * a) * Q + C (a ^ 2) := by
    simp only [map_mul, map_ofNat, map_pow]
    ring
  rw [hpoly, map_add, map_sub, xiThetaExpectation_C_mul, xiThetaExpectation_C] at hnonneg
  have hQ : Q ^ 2 = (X - C (s ^ 2)) ^ (2 * k) := by
    dsimp only [Q]
    rw [← pow_mul, Nat.mul_comm]
  rw [hQ] at hnonneg
  change 0 ≤ xiThetaCenteredMoment n (2 * k) s - 2 * a * a + a ^ 2 at hnonneg
  change a ^ 2 ≤ _
  nlinarith

def xiThetaSourceComparisonFactor : ℝ := 2 * (1 + thetaCuspHigherAtomDominationWeight)

theorem xiThetaSourceComparisonFactor_pos : 0 < xiThetaSourceComparisonFactor := by
  have h := thetaCuspHigherAtomDominationWeight_nonneg
  unfold xiThetaSourceComparisonFactor
  positivity

theorem thetaJensenWeight_eq_polynomialAtom (x : ℝ) :
    thetaJensenWeight x = thetaCuspPolynomialAtom (X ^ 4) 1 x := by
  simpa only [thetaJensenWeight, zero_mul, Real.exp_zero, one_mul] using
    thetaCuspGaussianApertureLeadingChannelWeight_eq 0 x

theorem thetaCuspFullSource_le_jensenWeight {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspFullSource x ≤
      (2 * Real.pi ^ 2 * xiThetaSourceComparisonFactor) * thetaJensenWeight x := by
  have htail := thetaCuspFullSource_sub_first_le hx
  have hfirst := thetaCuspSourceTerm_one_le_four_pi_sq_mul_leadingChannel x
  rw [← thetaJensenWeight_eq_polynomialAtom] at hfirst
  have hfactor : 0 ≤ 1 + thetaCuspHigherAtomDominationWeight := by
    linarith [thetaCuspHigherAtomDominationWeight_nonneg]
  have h := mul_le_mul_of_nonneg_left hfirst hfactor
  unfold xiThetaSourceComparisonFactor
  nlinarith

theorem thetaCuspRawEvenMoment_ge_jensenWeight (n : ℕ) (s : ℝ) :
    4 * Real.pi ^ 2 * thetaJensenCenteredMoment n 0 s ≤ thetaCuspRawEvenMoment n := by
  have hhalf := two_pi_sq_mul_leadingChannelMoment_lt_firstAtomHalfMoment (by rfl : (0 : ℝ) ≤ 0) n
  have hraw := thetaCuspAtomRawEvenMoment_one_le_raw n
  have heq : thetaCuspAtomRawEvenMoment n 1 =
      2 * thetaCuspGaussianApertureFirstAtomHalfMoment 0 n := by
    simp only [thetaCuspAtomRawEvenMoment, thetaCuspGaussianApertureFirstAtomHalfMoment,
      zero_mul, Real.exp_zero, mul_one]
  rw [heq] at hraw
  rw [thetaJensenCenteredMoment_zero]
  linarith

end RHTower

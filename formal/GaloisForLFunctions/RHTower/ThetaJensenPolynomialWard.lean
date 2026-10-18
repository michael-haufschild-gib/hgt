import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureScoreConcentration

/-!
# Polynomial Ward identities for the Xi moment saddle

The positive leading theta channel has score `S(x) = π x exp(2x) - 9x/4`.
Its exact monomial score identity extends to every polynomial in squared
height. Centered polynomial tests supply all orders needed for concentration.
-/

open Real MeasureTheory Set Filter Topology Polynomial

noncomputable section

namespace RHTower

def thetaJensenWeight (x : ℝ) : ℝ := thetaCuspGaussianApertureLeadingChannelWeight 0 x

def thetaJensenScore (x : ℝ) : ℝ := thetaCuspGaussianApertureExactTailSaddleDegree 0 x

def thetaJensenLeadingMoment (n : ℕ) (P : ℝ[X]) : ℝ :=
  ∫ x : ℝ in Ioi 0, P.eval (x ^ 2) * x ^ (2 * n) * thetaJensenWeight x

def thetaJensenLeadingScoreMoment (n : ℕ) (P : ℝ[X]) : ℝ :=
  ∫ x : ℝ in Ioi 0, P.eval (x ^ 2) * x ^ (2 * n) * thetaJensenScore x * thetaJensenWeight x

theorem integrableOn_thetaJensen_polynomial (n : ℕ) (P : ℝ[X]) :
    IntegrableOn (fun x : ℝ => P.eval (x ^ 2) * x ^ (2 * n) * thetaJensenWeight x) (Ioi 0) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    apply (hP.add hQ).congr
    filter_upwards [] with x
    simp only [eval_add, add_mul, Pi.add_apply]
  | monomial k a =>
    have h := (integrableOn_pow_mul_thetaCuspGaussianApertureLeadingChannelWeight
      (show (0 : ℝ) ≤ 0 by rfl) (2 * (n + k))).const_mul a
    apply h.congr
    filter_upwards [] with x
    simp only [eval_monomial, thetaJensenWeight, ← pow_mul, Nat.mul_add, pow_add]
    ring

theorem integrableOn_thetaJensen_score_polynomial (n : ℕ) (P : ℝ[X]) :
    IntegrableOn (fun x : ℝ =>
      P.eval (x ^ 2) * x ^ (2 * n) * thetaJensenScore x * thetaJensenWeight x) (Ioi 0) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    apply (hP.add hQ).congr
    filter_upwards [] with x
    simp only [eval_add, add_mul, Pi.add_apply]
  | monomial k a =>
    have h := (integrableOn_thetaCuspGaussianApertureLeadingChannelScoreMomentIntegrand
      (show (0 : ℝ) ≤ 0 by rfl) (n + k)).const_mul a
    apply h.congr
    filter_upwards [] with x
    simp only [eval_monomial, thetaJensenWeight, thetaJensenScore,
      ← pow_mul, Nat.mul_add, pow_add]
    ring

theorem thetaJensenLeadingMoment_add (n : ℕ) (P Q : ℝ[X]) :
    thetaJensenLeadingMoment n (P + Q) = thetaJensenLeadingMoment n P + thetaJensenLeadingMoment n Q := by
  simp only [thetaJensenLeadingMoment, eval_add, add_mul]
  exact integral_add (integrableOn_thetaJensen_polynomial n P)
    (integrableOn_thetaJensen_polynomial n Q)

theorem thetaJensenLeadingScoreMoment_add (n : ℕ) (P Q : ℝ[X]) :
    thetaJensenLeadingScoreMoment n (P + Q) =
      thetaJensenLeadingScoreMoment n P + thetaJensenLeadingScoreMoment n Q := by
  simp only [thetaJensenLeadingScoreMoment, eval_add, add_mul]
  exact integral_add (integrableOn_thetaJensen_score_polynomial n P)
    (integrableOn_thetaJensen_score_polynomial n Q)

theorem thetaJensenLeadingMoment_monomial (n k : ℕ) (a : ℝ) :
    thetaJensenLeadingMoment n (monomial k a) =
      a * thetaCuspGaussianApertureTailChannelMoment 0 4 (n + k) := by
  have heq : (fun x : ℝ => (monomial k a).eval (x ^ 2) * x ^ (2 * n) * thetaJensenWeight x) =
      (fun x => a * (x ^ (2 * (n + k)) * thetaCuspGaussianApertureLeadingChannelWeight 0 x)) := by
    ext x
    simp only [eval_monomial, thetaJensenWeight, ← pow_mul, Nat.mul_add, pow_add]
    ring
  rw [thetaJensenLeadingMoment, heq, integral_const_mul, integral_pow_leadingChannelWeight_eq_moment]

theorem thetaJensenLeadingScoreMoment_monomial (n k : ℕ) (a : ℝ) :
    thetaJensenLeadingScoreMoment n (monomial k a) =
      a * ((n + k : ℕ) + (1 / 2 : ℝ)) * thetaCuspGaussianApertureTailChannelMoment 0 4 (n + k) := by
  have heq : (fun x : ℝ =>
      (monomial k a).eval (x ^ 2) * x ^ (2 * n) * thetaJensenScore x * thetaJensenWeight x) =
      (fun x => a * (x ^ (2 * (n + k)) * thetaCuspGaussianApertureExactTailSaddleDegree 0 x *
        thetaCuspGaussianApertureLeadingChannelWeight 0 x)) := by
    ext x
    simp only [eval_monomial, thetaJensenWeight, thetaJensenScore,
      ← pow_mul, Nat.mul_add, pow_add]
    ring
  rw [thetaJensenLeadingScoreMoment, heq, integral_const_mul,
    ← thetaCuspGaussianApertureLeadingChannelScoreMoment,
    thetaCuspGaussianApertureLeadingChannelScoreMoment_eq (by rfl)]
  simp only [thetaCuspGaussianApertureGammaShape]
  ring

/-- Exact polynomial integration by parts under the power-tilted leading theta source. -/
theorem thetaJensen_polynomial_ward (n : ℕ) (P : ℝ[X]) :
    thetaJensenLeadingScoreMoment n P =
      ((n : ℝ) + 1 / 2) * thetaJensenLeadingMoment n P +
        thetaJensenLeadingMoment n (X * P.derivative) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [thetaJensenLeadingScoreMoment_add, derivative_add, mul_add,
      thetaJensenLeadingMoment_add, thetaJensenLeadingMoment_add, hP, hQ]
    ring
  | monomial k a =>
    cases k with
    | zero =>
      have h0 : thetaJensenLeadingMoment n 0 = 0 := by simp [thetaJensenLeadingMoment]
      rw [show derivative (monomial 0 a) = 0 by simp, mul_zero,
        thetaJensenLeadingScoreMoment_monomial,
        thetaJensenLeadingMoment_monomial, h0]
      simp only [Nat.add_zero]
      ring
    | succ k =>
      rw [derivative_monomial_succ, Polynomial.X_mul, monomial_mul_X,
        thetaJensenLeadingScoreMoment_monomial, thetaJensenLeadingMoment_monomial,
        thetaJensenLeadingMoment_monomial]
      push_cast
      ring

def thetaJensenCenteredMoment (n k : ℕ) (s : ℝ) : ℝ :=
  thetaJensenLeadingMoment n ((X - C (s ^ 2)) ^ k)

theorem thetaJensenCenteredMoment_eq_integral (n k : ℕ) (s : ℝ) :
    thetaJensenCenteredMoment n k s =
      ∫ x : ℝ in Ioi 0, (x ^ 2 - s ^ 2) ^ k * x ^ (2 * n) * thetaJensenWeight x := by
  simp only [thetaJensenCenteredMoment, thetaJensenLeadingMoment, eval_pow, eval_sub, eval_X, eval_C]

theorem integrableOn_thetaJensen_centered (n k : ℕ) (s : ℝ) :
    IntegrableOn (fun x : ℝ => (x ^ 2 - s ^ 2) ^ k * x ^ (2 * n) * thetaJensenWeight x) (Ioi 0) := by
  apply (integrableOn_thetaJensen_polynomial n ((X - C (s ^ 2)) ^ k)).congr
  filter_upwards [] with x
  simp only [eval_pow, eval_sub, eval_X, eval_C]

theorem integrableOn_thetaJensen_centeredScore (n k : ℕ) (s : ℝ) :
    IntegrableOn (fun x : ℝ => (x ^ 2 - s ^ 2) ^ k *
      (thetaJensenScore x - ((n : ℝ) + 1 / 2)) * x ^ (2 * n) * thetaJensenWeight x) (Ioi 0) := by
  have h := (integrableOn_thetaJensen_score_polynomial n ((X - C (s ^ 2)) ^ k)).sub
    ((integrableOn_thetaJensen_centered n k s).const_mul ((n : ℝ) + 1 / 2))
  convert h using 1
  ext x
  simp only [Pi.sub_apply, eval_pow, eval_sub, eval_X, eval_C]
  ring

/-- Centered tests turn the score correlation into an exact adjacent-moment recurrence. -/
theorem thetaJensen_centered_ward (n k : ℕ) (s : ℝ) :
    (∫ x : ℝ in Ioi 0, (x ^ 2 - s ^ 2) ^ (k + 1) *
      (thetaJensenScore x - ((n : ℝ) + 1 / 2)) * x ^ (2 * n) * thetaJensenWeight x) =
      ((k : ℝ) + 1) *
        (s ^ 2 * thetaJensenCenteredMoment n k s + thetaJensenCenteredMoment n (k + 1) s) := by
  let P : ℝ[X] := (X - C (s ^ 2)) ^ (k + 1)
  have hward := thetaJensen_polynomial_ward n P
  have hleft : (∫ x : ℝ in Ioi 0, (x ^ 2 - s ^ 2) ^ (k + 1) *
      (thetaJensenScore x - ((n : ℝ) + 1 / 2)) * x ^ (2 * n) * thetaJensenWeight x) =
      thetaJensenLeadingScoreMoment n P - ((n : ℝ) + 1 / 2) * thetaJensenLeadingMoment n P := by
    rw [thetaJensenLeadingScoreMoment, thetaJensenLeadingMoment, ← integral_const_mul,
      ← integral_sub (integrableOn_thetaJensen_score_polynomial n P)
        ((integrableOn_thetaJensen_polynomial n P).const_mul ((n : ℝ) + 1 / 2))]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [P, eval_pow, eval_sub, eval_X, eval_C]
    ring
  have hpoly : X * P.derivative = C ((k : ℝ) + 1) *
      (C (s ^ 2) * (X - C (s ^ 2)) ^ k + (X - C (s ^ 2)) ^ (k + 1)) := by
    dsimp only [P]
    rw [derivative_pow]
    simp only [derivative_sub, derivative_X, derivative_C,
      sub_zero, mul_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    rw [pow_succ]
    ring
  have hright : thetaJensenLeadingMoment n (X * P.derivative) =
      ((k : ℝ) + 1) *
        (s ^ 2 * thetaJensenCenteredMoment n k s + thetaJensenCenteredMoment n (k + 1) s) := by
    rw [hpoly]
    simp only [thetaJensenLeadingMoment, eval_mul, eval_add, eval_C,
      eval_pow, eval_sub, eval_X, mul_add]
    have hfun : (fun x : ℝ =>
        (((k : ℝ) + 1) * (s ^ 2 * (x ^ 2 - s ^ 2) ^ k) +
          ((k : ℝ) + 1) * (x ^ 2 - s ^ 2) ^ (k + 1)) * x ^ (2 * n) * thetaJensenWeight x) =
        (fun x => ((k : ℝ) + 1) *
          (s ^ 2 * ((x ^ 2 - s ^ 2) ^ k * x ^ (2 * n) * thetaJensenWeight x) +
            (x ^ 2 - s ^ 2) ^ (k + 1) * x ^ (2 * n) * thetaJensenWeight x)) := by
      ext x
      ring
    rw [hfun, integral_const_mul,
      integral_add ((integrableOn_thetaJensen_centered n k s).const_mul (s ^ 2))
        (integrableOn_thetaJensen_centered n (k + 1) s), integral_const_mul,
      ← thetaJensenCenteredMoment_eq_integral, ← thetaJensenCenteredMoment_eq_integral]
    ring
  rw [hleft]
  linarith

end RHTower

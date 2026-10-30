import GaloisForLFunctions.CompletedArithmeticForms.ScaleJetTransport

/-!
# Positive coefficient envelopes of physical Gaussian reflection jets

The source-scale generator admits an exact polynomial envelope. Its coefficients
are nonnegative, its leading coefficient is the native Gamma moment, and reflection
of its argument recovers the complete signed Gaussian jet at every order.
-/

noncomputable section

open Polynomial Finset

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower.ThetaCuspGaussianLimit

/-- The scale Euler operator on source polynomials. -/
def gaussianScaleEuler (P : ℝ[X]) : ℝ[X] := X * P.derivative

/-- Positive coefficient envelope of the exact physical signed Gaussian jet. -/
def positiveGaussianScalePolynomial : ℕ → ℝ[X]
  | 0 => 1
  | k + 1 =>
    C 8 * (X * positiveGaussianScalePolynomial k) +
      C 16 * (X * gaussianScaleEuler (positiveGaussianScalePolynomial k)) +
      C 4 * gaussianScaleEuler (gaussianScaleEuler (positiveGaussianScalePolynomial k))

@[simp] theorem coeff_gaussianScaleEuler (P : ℝ[X]) (j : ℕ) :
    (gaussianScaleEuler P).coeff j = (j : ℝ) * P.coeff j := by
  cases j with
  | zero => simp [gaussianScaleEuler, Polynomial.mul_coeff_zero]
  | succ j =>
    rw [gaussianScaleEuler, Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
    push_cast
    ring

@[simp] theorem positiveGaussianScalePolynomial_succ_coeff_zero (k : ℕ) :
    (positiveGaussianScalePolynomial (k + 1)).coeff 0 = 0 := by
  simp [positiveGaussianScalePolynomial, Polynomial.mul_coeff_zero]

/-- The envelope coefficients obey a positive triangular recurrence. -/
theorem positiveGaussianScalePolynomial_succ_coeff (k j : ℕ) :
    (positiveGaussianScalePolynomial (k + 1)).coeff (j + 1) =
      8 * (2 * (j : ℝ) + 1) * (positiveGaussianScalePolynomial k).coeff j +
        4 * ((j : ℝ) + 1) ^ 2 * (positiveGaussianScalePolynomial k).coeff (j + 1) := by
  simp only [positiveGaussianScalePolynomial, Polynomial.coeff_add,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, coeff_gaussianScaleEuler,
    Nat.cast_add, Nat.cast_one]
  ring

theorem positiveGaussianScalePolynomial_coeff_nonneg (k j : ℕ) :
    0 ≤ (positiveGaussianScalePolynomial k).coeff j := by
  induction k generalizing j with
  | zero => simp [positiveGaussianScalePolynomial, Polynomial.coeff_one]; split_ifs <;> norm_num
  | succ k ih =>
    cases j with
    | zero => simp
    | succ j =>
      rw [positiveGaussianScalePolynomial_succ_coeff]
      exact add_nonneg (mul_nonneg (by positivity) (ih j))
        (mul_nonneg (by positivity) (ih (j + 1)))

theorem positiveGaussianScalePolynomial_coeff_eq_zero (k j : ℕ) (h : k < j) :
    (positiveGaussianScalePolynomial k).coeff j = 0 := by
  induction k generalizing j with
  | zero => simp [positiveGaussianScalePolynomial, Polynomial.coeff_one, ne_of_gt h]
  | succ k ih =>
    cases j with
    | zero => omega
    | succ j =>
      rw [positiveGaussianScalePolynomial_succ_coeff,
        ih j (by omega), ih (j + 1) (by omega)]
      ring

theorem positiveGaussianScalePolynomial_natDegree_le (k : ℕ) :
    (positiveGaussianScalePolynomial k).natDegree ≤ k :=
  Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    (positiveGaussianScalePolynomial_coeff_eq_zero k)

theorem gaussianMoment_successor (k : ℕ) :
    gaussianMoment (k + 1) = 8 * (2 * (k : ℝ) + 1) * gaussianMoment k := by
  simp only [gaussianMoment, pow_succ, gammaShapeMoment_succ]
  ring

/-- The leading coefficient is the exact native Gaussian moment. -/
theorem positiveGaussianScalePolynomial_top_coeff (k : ℕ) :
    (positiveGaussianScalePolynomial k).coeff k = gaussianMoment k := by
  induction k with
  | zero => simp [positiveGaussianScalePolynomial, gaussianMoment]
  | succ k ih =>
    rw [positiveGaussianScalePolynomial_succ_coeff, ih,
      positiveGaussianScalePolynomial_coeff_eq_zero k (k + 1) (by omega),
      gaussianMoment_successor]
    ring

/-- Nonnegative coefficients control the source polynomial on its positive ray. -/
theorem sourcePolynomial_eval_nonneg {P : ℝ[X]} (hP : ∀ j, 0 ≤ P.coeff j)
    {q : ℝ} (hq : 0 ≤ q) : 0 ≤ P.eval q := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hP j) (pow_nonneg hq j))

theorem sourcePolynomial_eval_le {P Q : ℝ[X]} (hPQ : ∀ j, P.coeff j ≤ Q.coeff j)
    {q : ℝ} (hq : 0 ≤ q) : P.eval q ≤ Q.eval q := by
  have h := sourcePolynomial_eval_nonneg
    (P := Q - P) (fun j => by simpa only [Polynomial.coeff_sub] using sub_nonneg.mpr (hPQ j)) hq
  simpa only [Polynomial.eval_sub, sub_nonneg] using h

/-- Reflection cannot exceed the positive coefficient envelope. -/
theorem sourcePolynomial_abs_eval_neg_le {P : ℝ[X]} (hP : ∀ j, 0 ≤ P.coeff j)
    {q : ℝ} (hq : 0 ≤ q) : |P.eval (-q)| ≤ P.eval q := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def,
    Polynomial.eval_eq_sum, Polynomial.sum_def]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro j _
  simp only [_root_.abs_mul, _root_.abs_pow, abs_neg,
    abs_of_nonneg (hP j), abs_of_nonneg hq, le_refl]

/-- Euler differentiation costs at most the source degree on the positive ray. -/
theorem gaussianScaleEuler_eval_le {P : ℝ[X]} {k : ℕ}
    (hP : ∀ j, 0 ≤ P.coeff j) (hdegree : ∀ j, k < j → P.coeff j = 0)
    {q : ℝ} (hq : 0 ≤ q) :
    (gaussianScaleEuler P).eval q ≤ (k : ℝ) * P.eval q := by
  have hc (j : ℕ) : (gaussianScaleEuler P).coeff j ≤ (C (k : ℝ) * P).coeff j := by
    rw [coeff_gaussianScaleEuler, Polynomial.coeff_C_mul]
    by_cases hj : j ≤ k
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (hP j)
    · rw [hdegree j (by omega)]
      simp
  simpa only [Polynomial.eval_mul, Polynomial.eval_C] using sourcePolynomial_eval_le hc hq

theorem positiveGaussianScalePolynomial_eval_nonneg (k : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ (positiveGaussianScalePolynomial k).eval q :=
  sourcePolynomial_eval_nonneg (positiveGaussianScalePolynomial_coeff_nonneg k) hq

/-- A degree-sensitive one-step bound retains the quadratic order cost. -/
theorem positiveGaussianScalePolynomial_eval_succ_le (k : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    (positiveGaussianScalePolynomial (k + 1)).eval q ≤
      (8 * q * (2 * (k : ℝ) + 1) + 4 * (k : ℝ) ^ 2) *
        (positiveGaussianScalePolynomial k).eval q := by
  let P := positiveGaussianScalePolynomial k
  have hP := positiveGaussianScalePolynomial_coeff_nonneg k
  have hd := positiveGaussianScalePolynomial_coeff_eq_zero k
  have hE := gaussianScaleEuler_eval_le hP hd hq
  have hEE := gaussianScaleEuler_eval_le
    (P := gaussianScaleEuler P) (k := k)
    (fun j => by rw [coeff_gaussianScaleEuler]; exact mul_nonneg (Nat.cast_nonneg j) (hP j))
    (fun j hj => by rw [coeff_gaussianScaleEuler, hd j hj, mul_zero]) hq
  have hEEn : (gaussianScaleEuler (gaussianScaleEuler P)).eval q ≤
      (k : ℝ) ^ 2 * P.eval q := by
    calc
      _ ≤ (k : ℝ) * (gaussianScaleEuler P).eval q := hEE
      _ ≤ (k : ℝ) * ((k : ℝ) * P.eval q) :=
        mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg k)
      _ = _ := by ring
  change (C 8 * (X * P) + C 16 * (X * gaussianScaleEuler P) +
    C 4 * gaussianScaleEuler (gaussianScaleEuler P)).eval q ≤ _
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  change 8 * (q * P.eval q) + 16 * (q * (gaussianScaleEuler P).eval q) +
    4 * (gaussianScaleEuler (gaussianScaleEuler P)).eval q ≤ _
  have hEq := mul_le_mul_of_nonneg_left hE hq
  nlinarith only [hEq, hEEn]

@[simp] theorem gaussianScaleEuler_eval (P : ℝ[X]) (q : ℝ) :
    (gaussianScaleEuler P).eval q = q * P.derivative.eval q := by
  simp [gaussianScaleEuler]

theorem gaussianScaleEuler_twice_eval (P : ℝ[X]) (q : ℝ) :
    (gaussianScaleEuler (gaussianScaleEuler P)).eval q =
      q * P.derivative.eval q + q ^ 2 * P.derivative.derivative.eval q := by
  simp only [gaussianScaleEuler, Polynomial.derivative_mul, Polynomial.derivative_X,
    one_mul, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X]
  ring

theorem positiveGaussianScalePolynomial_eval_succ (k : ℕ) (q : ℝ) :
    (positiveGaussianScalePolynomial (k + 1)).eval q =
      8 * q * (positiveGaussianScalePolynomial k).eval q +
        (16 * q ^ 2 + 4 * q) * (positiveGaussianScalePolynomial k).derivative.eval q +
        4 * q ^ 2 * (positiveGaussianScalePolynomial k).derivative.derivative.eval q := by
  rw [positiveGaussianScalePolynomial]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  rw [gaussianScaleEuler_twice_eval, gaussianScaleEuler_eval]
  ring

private theorem deriv_reflectedPolynomial (c : ℝ) (P : ℝ[X]) :
    deriv (fun q => c * P.eval (-q)) = fun q => -c * P.derivative.eval (-q) := by
  funext q
  have h : HasDerivAt (fun r => c * P.eval (-r))
      (c * (P.derivative.eval (-q) * (-1))) q :=
    ((P.hasDerivAt (-q)).comp q (hasDerivAt_id q).neg).const_mul c
  rw [h.deriv]
  ring

/-- Reflection of the positive envelope is the literal physical signed jet. -/
theorem gaussianScaleSignedJet_eq_polynomial (k : ℕ) (q : ℝ) :
    gaussianScaleSignedJet k q = (-1 : ℝ) ^ k *
      (positiveGaussianScalePolynomial k).eval (-q) := by
  induction k generalizing q with
  | zero => simp [positiveGaussianScalePolynomial]
  | succ k ih =>
    have he : gaussianScaleSignedJet k = fun q => (-1 : ℝ) ^ k *
        (positiveGaussianScalePolynomial k).eval (-q) := funext ih
    rw [gaussianScaleSignedJet_succ, he, deriv_reflectedPolynomial,
      deriv_reflectedPolynomial, positiveGaussianScalePolynomial_eval_succ,
      pow_succ]
    dsimp only
    ring

theorem gaussianScaleSignedJet_deriv_eq_polynomial (k : ℕ) (q : ℝ) :
    deriv (gaussianScaleSignedJet k) q = -((-1 : ℝ) ^ k) *
      (positiveGaussianScalePolynomial k).derivative.eval (-q) := by
  have he : gaussianScaleSignedJet k = fun q => (-1 : ℝ) ^ k *
      (positiveGaussianScalePolynomial k).eval (-q) :=
    funext (gaussianScaleSignedJet_eq_polynomial k)
  rw [he, deriv_reflectedPolynomial]

/-- The complete first-atom affine envelope, including its source-scale derivative. -/
def firstAtomScalePolynomial (B : ℝ) (k : ℕ) : ℝ[X] :=
  C B * positiveGaussianScalePolynomial k +
    C 6 * gaussianScaleEuler (positiveGaussianScalePolynomial k)

theorem firstAtomScalePolynomial_coeff (B : ℝ) (k j : ℕ) :
    (firstAtomScalePolynomial B k).coeff j =
      (B + 6 * (j : ℝ)) * (positiveGaussianScalePolynomial k).coeff j := by
  simp only [firstAtomScalePolynomial, Polynomial.coeff_add,
    Polynomial.coeff_C_mul, coeff_gaussianScaleEuler]
  ring

theorem firstAtomScalePolynomial_coeff_nonneg {B : ℝ} (hB : 0 ≤ B) (k j : ℕ) :
    0 ≤ (firstAtomScalePolynomial B k).coeff j := by
  rw [firstAtomScalePolynomial_coeff]
  exact mul_nonneg (by positivity) (positiveGaussianScalePolynomial_coeff_nonneg k j)

theorem firstAtomScalePolynomial_top_coeff (B : ℝ) (k : ℕ) :
    (firstAtomScalePolynomial B k).coeff k = (B + 6 * (k : ℝ)) * gaussianMoment k := by
  rw [firstAtomScalePolynomial_coeff, positiveGaussianScalePolynomial_top_coeff]

theorem firstAtomScalePolynomial_eval_le (B : ℝ) (k : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    (firstAtomScalePolynomial B k).eval q ≤
      (B + 6 * (k : ℝ)) * (positiveGaussianScalePolynomial k).eval q := by
  have hE := gaussianScaleEuler_eval_le
    (positiveGaussianScalePolynomial_coeff_nonneg k)
    (positiveGaussianScalePolynomial_coeff_eq_zero k) hq
  simp only [firstAtomScalePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C]
  linarith only [hE]

/-- The source amplitude, affine factor, and every reflection order are retained exactly. -/
theorem firstAtomSignedMoment_eq_polynomial (k : ℕ) (x : ℝ) :
    (-1 : ℝ) ^ k * _root_.RHTower.thetaCuspFirstAtomReflectionJet (2 * k) x =
      firstAtomClockAmplitude x * (-1 : ℝ) ^ k *
        (firstAtomScalePolynomial (firstAtomClockShape x) k).eval
          (-_root_.RHTower.thetaCuspSingleAtomReflectionScale 1 x) := by
  rw [firstAtomSignedMoment_eq_scaleJet, gaussianScaleSignedJet_eq_polynomial,
    gaussianScaleSignedJet_deriv_eq_polynomial]
  simp only [firstAtomScalePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, gaussianScaleEuler_eval]
  ring

/-- Removing any one coefficient leaves a positive envelope for the reflected remainder. -/
theorem sourcePolynomial_reflection_coefficient_error {P : ℝ[X]}
    (hP : ∀ j, 0 ≤ P.coeff j) (k : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    |(-1 : ℝ) ^ k * P.eval (-q) - P.coeff k * q ^ k| ≤
      P.eval q - P.coeff k * q ^ k := by
  let R := P - Polynomial.monomial k (P.coeff k)
  have hR (j : ℕ) : 0 ≤ R.coeff j := by
    simp only [R, Polynomial.coeff_sub, Polynomial.coeff_monomial]
    split_ifs with h
    · subst j
      simp
    · simpa using hP j
  have hphase : (-1 : ℝ) ^ k * (-q) ^ k = q ^ k := by
    rw [← mul_pow]
    congr 1
    ring
  have he : (-1 : ℝ) ^ k * P.eval (-q) - P.coeff k * q ^ k =
      (-1 : ℝ) ^ k * R.eval (-q) := by
    simp only [R, Polynomial.eval_sub, Polynomial.eval_monomial]
    linear_combination (P.coeff k) * hphase
  rw [he, _root_.abs_mul, _root_.abs_pow]
  norm_num only [abs_neg, abs_one, one_pow, one_mul]
  simpa only [R, Polynomial.eval_sub, Polynomial.eval_monomial] using
    sourcePolynomial_abs_eval_neg_le hR hq

/-- The full source error is paid by the lower-degree positive polynomial terms. -/
theorem firstAtomSignedMoment_polynomial_error_le (k : ℕ) (x : ℝ) :
    let q := _root_.RHTower.thetaCuspSingleAtomReflectionScale 1 x
    let B := firstAtomClockShape x
    let A := firstAtomClockAmplitude x
    |(-1 : ℝ) ^ k * _root_.RHTower.thetaCuspFirstAtomReflectionJet (2 * k) x -
      A * (B + 6 * (k : ℝ)) * gaussianMoment k * q ^ k| ≤
      A * (B + 6 * (k : ℝ)) *
        ((positiveGaussianScalePolynomial k).eval q - gaussianMoment k * q ^ k) := by
  dsimp only
  let q := _root_.RHTower.thetaCuspSingleAtomReflectionScale 1 x
  let B := firstAtomClockShape x
  let A := firstAtomClockAmplitude x
  have hq : 0 ≤ q := by
    unfold q _root_.RHTower.thetaCuspSingleAtomReflectionScale
    positivity
  have hB : 0 ≤ B := sq_nonneg _
  have hA : 0 ≤ A := (firstAtomClockAmplitude_pos x).le
  have herr := sourcePolynomial_reflection_coefficient_error
    (firstAtomScalePolynomial_coeff_nonneg hB k) k hq
  rw [firstAtomScalePolynomial_top_coeff] at herr
  have henv := firstAtomScalePolynomial_eval_le B k hq
  rw [firstAtomSignedMoment_eq_polynomial]
  change |A * (-1 : ℝ) ^ k * (firstAtomScalePolynomial B k).eval (-q) -
    A * (B + 6 * (k : ℝ)) * gaussianMoment k * q ^ k| ≤ _
  rw [show A * (-1 : ℝ) ^ k * (firstAtomScalePolynomial B k).eval (-q) -
      A * (B + 6 * (k : ℝ)) * gaussianMoment k * q ^ k =
      A * ((-1 : ℝ) ^ k * (firstAtomScalePolynomial B k).eval (-q) -
        (B + 6 * (k : ℝ)) * gaussianMoment k * q ^ k) by ring,
    _root_.abs_mul, abs_of_nonneg hA]
  have hpaid := mul_le_mul_of_nonneg_left herr hA
  have hup := mul_le_mul_of_nonneg_left henv hA
  dsimp only [q, B, A] at *
  nlinarith only [hpaid, hup]

#print axioms positiveGaussianScalePolynomial_top_coeff
#print axioms positiveGaussianScalePolynomial_eval_succ_le
#print axioms gaussianScaleSignedJet_eq_polynomial
#print axioms firstAtomSignedMoment_eq_polynomial
#print axioms firstAtomSignedMoment_polynomial_error_le

end GaloisForLFunctions.CompletedArithmeticForms

import GaloisForLFunctions.HTGeometry.RationalExponentialShadow

/-!
# Rational rigidity for a linear coefficient

The homogeneous equation `z' = c·t·z` with `c ≠ 0` has no nonzero rational solution, and the
inhomogeneous equation `z' = c·t·z + 1` has no rational solution at all.

Both are proved by cross-multiplying into the numerator and denominator.  In the homogeneous case
the right-hand side has degree one more than the Wronskian bound for the left-hand side.  In the
inhomogeneous case the denominator divides its own derivative, so it is constant, and the resulting
polynomial equation compares a derivative against a strictly higher-degree product.

These are the two coefficient obstructions of the Gaussian primitive: no rational function has
logarithmic derivative a nonzero multiple of the coordinate, and the Gaussian exponential has no
rational antiderivative factor.
-/

noncomputable section

open Polynomial

namespace GaloisForLFunctions.RationalShadow

open GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K]

/-- Cross-multiplied form of an affine equation with polynomial coefficients. -/
theorem ratFuncCoordinateDerivation_affine_cross (z : RatFunc K) {a b : K[X]}
    (h : ratFuncCoordinateDerivation K z
      = algebraMap K[X] (RatFunc K) a * z + algebraMap K[X] (RatFunc K) b) :
    z.denom * z.num.derivative - z.num * z.denom.derivative
      = a * z.num * z.denom + b * z.denom ^ (2 : ℕ) := by
  have hden : algebraMap K[X] (RatFunc K) z.denom ≠ 0 := by
    intro hzero
    exact RatFunc.denom_ne_zero z
      (IsFractionRing.injective K[X] (RatFunc K) (by simpa using hzero))
  rw [ratFuncCoordinateDerivation_apply] at h
  conv_rhs at h => rw [← RatFunc.num_div_denom z]
  have hmul : (algebraMap K[X] (RatFunc K) z.denom *
        algebraMap K[X] (RatFunc K) z.num.derivative -
      algebraMap K[X] (RatFunc K) z.num *
        algebraMap K[X] (RatFunc K) z.denom.derivative)
      = algebraMap K[X] (RatFunc K) a * algebraMap K[X] (RatFunc K) z.num
          * algebraMap K[X] (RatFunc K) z.denom
        + algebraMap K[X] (RatFunc K) b * algebraMap K[X] (RatFunc K) z.denom ^ (2 : ℕ) := by
    field_simp at h
    linear_combination h
  exact IsFractionRing.injective K[X] (RatFunc K)
    (by simpa only [map_sub, map_mul, map_add, map_pow] using hmul)

/-- Adding one strictly increases a degree that is not `⊥`. -/
theorem lt_one_add_self_of_ne_bot {a : WithBot ℕ} (ha : a ≠ ⊥) : a < 1 + a := by
  have h := WithBot.add_lt_add_right ha (by norm_num : (0 : WithBot ℕ) < 1)
  rwa [zero_add] at h

/-- A degree that is not `⊥` is nonnegative. -/
theorem zero_le_of_ne_bot {a : WithBot ℕ} (ha : a ≠ ⊥) : (0 : WithBot ℕ) ≤ a :=
  le_of_not_gt fun h => ha (Nat.WithBot.lt_zero_iff.mp h)

/-- One more than a degree that is not `⊥` is positive. -/
theorem zero_lt_one_add_of_ne_bot {a : WithBot ℕ} (ha : a ≠ ⊥) : (0 : WithBot ℕ) < 1 + a :=
  lt_of_le_of_lt (zero_le_of_ne_bot ha) (lt_one_add_self_of_ne_bot ha)

/-- The Wronskian of numerator and denominator has degree below their degree sum. -/
theorem degree_wronskian_lt (z : RatFunc K) (hz : z ≠ 0) :
    (z.denom * z.num.derivative - z.num * z.denom.derivative).degree
      < z.num.degree + z.denom.degree := by
  have hnum : z.num ≠ 0 := RatFunc.num_ne_zero hz
  have hden : z.denom ≠ 0 := RatFunc.denom_ne_zero z
  have hsumne : z.num.degree + z.denom.degree ≠ ⊥ := by
    rw [← Polynomial.degree_mul]
    exact Polynomial.degree_ne_bot.mpr (mul_ne_zero hnum hden)
  have hbotlt : (⊥ : WithBot ℕ) < z.num.degree + z.denom.degree :=
    lt_of_le_of_ne bot_le (Ne.symm hsumne)
  have hdeg1 : (z.denom * z.num.derivative).degree < z.num.degree + z.denom.degree := by
    rcases eq_or_ne z.num.derivative 0 with h0 | h0
    · rw [h0, mul_zero, Polynomial.degree_zero]
      exact hbotlt
    · rw [Polynomial.degree_mul, add_comm]
      exact WithBot.add_lt_add_right (Polynomial.degree_ne_bot.mpr hden)
        (Polynomial.degree_derivative_lt hnum)
  have hdeg2 : (z.num * z.denom.derivative).degree < z.num.degree + z.denom.degree := by
    rcases eq_or_ne z.denom.derivative 0 with h0 | h0
    · rw [h0, mul_zero, Polynomial.degree_zero]
      exact hbotlt
    · rw [Polynomial.degree_mul]
      exact WithBot.add_lt_add_left (Polynomial.degree_ne_bot.mpr hnum)
        (Polynomial.degree_derivative_lt hden)
  exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hdeg1 hdeg2)

/-- **No nonzero rational function has logarithmic derivative a nonzero multiple of the
coordinate.** -/
theorem eq_zero_of_deriv_eq_linear_mul {c : K} (hc : c ≠ 0) {z : RatFunc K}
    (h : ratFuncCoordinateDerivation K z
      = algebraMap K[X] (RatFunc K) (Polynomial.C c * Polynomial.X) * z) :
    z = 0 := by
  by_contra hz
  have hnum : z.num ≠ 0 := RatFunc.num_ne_zero hz
  have hden : z.denom ≠ 0 := RatFunc.denom_ne_zero z
  have hcross : z.denom * z.num.derivative - z.num * z.denom.derivative
      = (Polynomial.C c * Polynomial.X) * z.num * z.denom + 0 * z.denom ^ (2 : ℕ) := by
    refine ratFuncCoordinateDerivation_affine_cross z ?_
    simpa using h
  rw [zero_mul, add_zero] at hcross
  have hlt := degree_wronskian_lt z hz
  rw [hcross] at hlt
  have hdegR : ((Polynomial.C c * Polynomial.X) * z.num * z.denom).degree
      = 1 + (z.num.degree + z.denom.degree) := by
    rw [Polynomial.degree_mul, Polynomial.degree_mul, Polynomial.degree_C_mul_X hc, add_assoc]
  rw [hdegR] at hlt
  have hsumne : z.num.degree + z.denom.degree ≠ ⊥ := by
    rw [← Polynomial.degree_mul]
    exact Polynomial.degree_ne_bot.mpr (mul_ne_zero hnum hden)
  exact absurd (lt_trans hlt (lt_one_add_self_of_ne_bot hsumne)) (lt_irrefl _)

/-- **The Gaussian coefficient equation has no rational solution.**  There is no rational function
with `z' = c·t·z + 1` for `c ≠ 0`. -/
theorem not_deriv_eq_linear_mul_add_one [CharZero K] {c : K} (hc : c ≠ 0) (z : RatFunc K) :
    ratFuncCoordinateDerivation K z
      ≠ algebraMap K[X] (RatFunc K) (Polynomial.C c * Polynomial.X) * z + 1 := by
  intro h
  have hnum : z.num ≠ 0 ∨ z.num = 0 := ne_or_eq _ _
  have hden : z.denom ≠ 0 := RatFunc.denom_ne_zero z
  have hcross : z.denom * z.num.derivative - z.num * z.denom.derivative
      = (Polynomial.C c * Polynomial.X) * z.num * z.denom + 1 * z.denom ^ (2 : ℕ) := by
    refine ratFuncCoordinateDerivation_affine_cross z ?_
    simpa using h
  rw [one_mul] at hcross
  -- the denominator divides its own derivative
  have hdvd : z.denom ∣ z.num * z.denom.derivative := by
    refine ⟨z.num.derivative - (Polynomial.C c * Polynomial.X) * z.num - z.denom, ?_⟩
    linear_combination -hcross
  have hcop : IsCoprime z.denom z.num := (RatFunc.isCoprime_num_denom z).symm
  have hdvd' : z.denom ∣ z.denom.derivative := hcop.dvd_of_dvd_mul_left hdvd
  have hderiv0 : z.denom.derivative = 0 := by
    by_contra h0
    have hle := Polynomial.degree_le_of_dvd hdvd' h0
    exact absurd (lt_of_le_of_lt hle (Polynomial.degree_derivative_lt hden)) (lt_irrefl _)
  have hdeg0 : z.denom.natDegree = 0 := Polynomial.derivative_eq_zero.mp hderiv0
  have hmonic : z.denom.Monic := RatFunc.monic_denom z
  have hden1 : z.denom = 1 := Polynomial.eq_one_of_monic_natDegree_zero hmonic hdeg0
  rw [hden1] at hcross
  simp only [one_mul, mul_one, Polynomial.derivative_one, mul_zero, sub_zero, one_pow] at hcross
  -- the remaining polynomial equation compares a derivative with a higher-degree product
  rcases hnum with hn | hn
  · have hdegL : z.num.derivative.degree < z.num.degree := Polynomial.degree_derivative_lt hn
    have hdegP : ((Polynomial.C c * Polynomial.X) * z.num).degree = 1 + z.num.degree := by
      rw [Polynomial.degree_mul, Polynomial.degree_C_mul_X hc]
    have hnumbot : z.num.degree ≠ ⊥ := Polynomial.degree_ne_bot.mpr hn
    have hone : (1 : K[X]).degree < ((Polynomial.C c * Polynomial.X) * z.num).degree := by
      rw [hdegP]
      exact lt_of_le_of_lt Polynomial.degree_one_le (zero_lt_one_add_of_ne_bot hnumbot)
    have hdegR : ((Polynomial.C c * Polynomial.X) * z.num + 1).degree = 1 + z.num.degree := by
      rw [Polynomial.degree_add_eq_left_of_degree_lt hone, hdegP]
    rw [hcross, hdegR] at hdegL
    exact absurd (lt_trans hdegL (lt_one_add_self_of_ne_bot hnumbot)) (lt_irrefl _)
  · rw [hn] at hcross
    simp only [Polynomial.derivative_zero, mul_zero, zero_add] at hcross
    exact one_ne_zero hcross.symm

end GaloisForLFunctions.RationalShadow

namespace GaloisForLFunctions.RationalShadow

open GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K]

/-- **No nonzero rational function has a nonzero polynomial logarithmic derivative.**  The
Wronskian of numerator and denominator has degree below their degree sum, while the cross-multiplied
right-hand side has degree at least that sum. -/
theorem eq_zero_of_deriv_eq_polynomial_mul {a : Polynomial K} (ha : a ≠ 0) {z : RatFunc K}
    (h : ratFuncCoordinateDerivation K z = algebraMap (Polynomial K) (RatFunc K) a * z) :
    z = 0 := by
  by_contra hz
  have hcross : z.denom * z.num.derivative - z.num * z.denom.derivative
      = a * z.num * z.denom + 0 * z.denom ^ (2 : ℕ) := by
    refine ratFuncCoordinateDerivation_affine_cross z ?_
    simpa using h
  rw [zero_mul, add_zero] at hcross
  have hlt := degree_wronskian_lt z hz
  rw [hcross] at hlt
  have hmul : a * z.num * z.denom = z.num * z.denom * a := by ring
  have hle : (z.num * z.denom).degree ≤ (z.num * z.denom * a).degree :=
    Polynomial.degree_le_mul_left (z.num * z.denom) ha
  rw [Polynomial.degree_mul] at hle
  rw [hmul] at hlt
  exact absurd (lt_of_lt_of_le hlt hle) (lt_irrefl _)

/-- **No nonzero rational function has a nonzero constant logarithmic derivative.** -/
theorem eq_zero_of_deriv_eq_const_mul {c : K} (hc : c ≠ 0) {z : RatFunc K}
    (h : ratFuncCoordinateDerivation K z
      = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C c) * z) :
    z = 0 :=
  eq_zero_of_deriv_eq_polynomial_mul (Polynomial.C_ne_zero.mpr hc) h

end GaloisForLFunctions.RationalShadow

import GaloisForLFunctions.RHTower.GaussianMomentFourier
import GaloisForLFunctions.RHTower.PrimeSquareMeanVarianceDefect

/-!
# The tilted heat weight is exactly the Gaussian saddle

Tilting the heat profile by the half-density factor `e^{L/2}` completes the square:

`e^{L/2}√(π/t)e^{-L²/(4t)} = e^{t/4}√(π/t)e^{-(L-t)²/(4t)}`,

so the continuous prime saddle is the Gaussian law centred at `t` with variance `2t`.  Its second
and fourth central moments come from the jet polynomials at the origin, and feed the boundary
identity of the Lorentz determinant.
-/

open MeasureTheory

namespace RHTower

noncomputable section

/-- **The half-density tilt of the heat profile is a Gaussian centred at `t`.** -/
theorem tiltedHeatProfile_eq (t L : ℝ) :
    Real.exp (L / 2) * heatProfile t L
      = Real.exp (t / 4) * Real.sqrt (Real.pi / t) * Real.exp (-((L - t) ^ 2 / (4 * t))) := by
  rcases eq_or_ne t 0 with ht | ht
  · subst ht
    simp [heatProfile]
  · rw [heatProfile]
    rw [show Real.exp (L / 2) * (Real.sqrt (Real.pi / t) * Real.exp (-(L ^ 2) / (4 * t)))
        = Real.sqrt (Real.pi / t) * (Real.exp (L / 2) * Real.exp (-(L ^ 2) / (4 * t))) by ring,
      ← Real.exp_add]
    rw [show Real.exp (t / 4) * Real.sqrt (Real.pi / t) * Real.exp (-((L - t) ^ 2 / (4 * t)))
        = Real.sqrt (Real.pi / t) * (Real.exp (t / 4) * Real.exp (-((L - t) ^ 2 / (4 * t)))) by ring,
      ← Real.exp_add]
    congr 2
    field_simp
    ring

/-! ## The jet polynomials at the origin -/

theorem gaussJetPoly_one (t : ℝ) :
    gaussJetPoly t 1 = -(Polynomial.C (1 / (2 * t)) * Polynomial.X) := by
  rw [gaussJetPoly_succ, gaussJetPoly_zero]
  simp

theorem gaussJetPoly_two (t : ℝ) :
    gaussJetPoly t 2 = -Polynomial.C (1 / (2 * t))
      + Polynomial.C (1 / (2 * t)) * Polynomial.C (1 / (2 * t)) * Polynomial.X ^ 2 := by
  rw [gaussJetPoly_succ, gaussJetPoly_one]
  simp only [Polynomial.derivative_neg, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, zero_mul, mul_one, zero_add]
  ring

theorem gaussJetPoly_three (t : ℝ) :
    gaussJetPoly t 3 = 3 * (Polynomial.C (1 / (2 * t)) * Polynomial.C (1 / (2 * t)))
        * Polynomial.X
      - Polynomial.C (1 / (2 * t)) * Polynomial.C (1 / (2 * t)) * Polynomial.C (1 / (2 * t))
        * Polynomial.X ^ 3 := by
  rw [gaussJetPoly_succ, gaussJetPoly_two]
  simp only [Polynomial.derivative_add, Polynomial.derivative_neg, Polynomial.derivative_mul,
    Polynomial.derivative_C, Polynomial.derivative_X_pow,
    zero_mul, zero_add, neg_zero]
  push_cast
  simp only [map_ofNat]
  ring

theorem gaussJetPoly_four (t : ℝ) :
    gaussJetPoly t 4 = 3 * (Polynomial.C (1 / (2 * t)) * Polynomial.C (1 / (2 * t)))
      - 6 * (Polynomial.C (1 / (2 * t)) * Polynomial.C (1 / (2 * t))
          * Polynomial.C (1 / (2 * t))) * Polynomial.X ^ 2
      + Polynomial.C (1 / (2 * t)) * Polynomial.C (1 / (2 * t)) * Polynomial.C (1 / (2 * t))
        * Polynomial.C (1 / (2 * t)) * Polynomial.X ^ 4 := by
  rw [gaussJetPoly_succ, gaussJetPoly_three]
  simp only [Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X_pow, Polynomial.derivative_ofNat,
    Polynomial.derivative_X, zero_mul, zero_add]
  push_cast
  simp only [map_ofNat]
  ring

@[simp] theorem gaussJetPoly_one_eval_zero (t : ℝ) : (gaussJetPoly t 1).eval 0 = 0 := by
  rw [gaussJetPoly_one]
  simp

@[simp] theorem gaussJetPoly_two_eval_zero (t : ℝ) :
    (gaussJetPoly t 2).eval 0 = -(1 / (2 * t)) := by
  rw [gaussJetPoly_two]
  simp

@[simp] theorem gaussJetPoly_three_eval_zero (t : ℝ) : (gaussJetPoly t 3).eval 0 = 0 := by
  rw [gaussJetPoly_three]
  simp

@[simp] theorem gaussJetPoly_four_eval_zero (t : ℝ) :
    (gaussJetPoly t 4).eval 0 = 3 * (1 / (2 * t)) ^ 2 := by
  rw [gaussJetPoly_four]
  simp
  ring

/-! ## The Gaussian moments at the origin -/

theorem gaussMoment_zero_freq {a : ℝ} (ha : 0 < a) (n : ℕ) :
    gaussMoment a n 0
      = Complex.I ^ n * (Real.sqrt (Real.pi / a) : ℂ)
        * (((gaussJetPoly a n).eval 0 : ℝ) : ℂ) := by
  rw [gaussMoment_eq ha n 0]
  have hker : ((gaussKernel a 0 : ℝ) : ℂ) = 1 := by
    rw [gaussKernel]
    norm_num
  rw [hker, mul_one]

/-- **The odd Gaussian moments vanish.** -/
theorem gaussMoment_one_zero {a : ℝ} (ha : 0 < a) : gaussMoment a 1 0 = 0 := by
  rw [gaussMoment_zero_freq ha, gaussJetPoly_one_eval_zero]
  simp

theorem gaussMoment_three_zero {a : ℝ} (ha : 0 < a) : gaussMoment a 3 0 = 0 := by
  rw [gaussMoment_zero_freq ha, gaussJetPoly_three_eval_zero]
  simp

/-- **The second Gaussian moment.** -/
theorem gaussMoment_two_eq {a : ℝ} (ha : 0 < a) :
    gaussMoment a 2 0 = ((1 / (2 * a) : ℝ) : ℂ) * gaussMoment a 0 0 := by
  rw [gaussMoment_zero_freq ha, gaussMoment_zero_freq ha, gaussJetPoly_two_eval_zero,
    gaussJetPoly_zero]
  simp only [Polynomial.eval_one, pow_zero, one_mul, pow_two, Complex.I_mul_I]
  push_cast
  ring

/-- **The fourth Gaussian moment.** -/
theorem gaussMoment_four_eq {a : ℝ} (ha : 0 < a) :
    gaussMoment a 4 0 = ((3 / (4 * a ^ 2) : ℝ) : ℂ) * gaussMoment a 0 0 := by
  rw [gaussMoment_zero_freq ha, gaussMoment_zero_freq ha, gaussJetPoly_four_eval_zero,
    gaussJetPoly_zero]
  simp only [Polynomial.eval_one, pow_zero, one_mul]
  have hI : (Complex.I : ℂ) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]
    norm_num
  rw [hI]
  have ha' : (a : ℝ) ≠ 0 := ne_of_gt ha
  push_cast
  field_simp
  ring

/-! ## The saddle moments -/

/-- **(24.170) The second centred moment of the saddle law is `2t`.** -/
theorem gaussianSaddle_second_moment {t : ℝ} (ht : 0 < t) :
    gaussMoment (1 / (4 * t)) 2 0 = ((2 * t : ℝ) : ℂ) * gaussMoment (1 / (4 * t)) 0 0 := by
  have ha : (0 : ℝ) < 1 / (4 * t) := by positivity
  rw [gaussMoment_two_eq ha]
  congr 2
  field_simp

/-- **(24.170) The fourth centred moment of the saddle law is `3(2t)²`.** -/
theorem gaussianSaddle_fourth_moment {t : ℝ} (ht : 0 < t) :
    gaussMoment (1 / (4 * t)) 4 0
      = ((3 * (2 * t) ^ 2 : ℝ) : ℂ) * gaussMoment (1 / (4 * t)) 0 0 := by
  have ha : (0 : ℝ) < 1 / (4 * t) := by positivity
  rw [gaussMoment_four_eq ha]
  congr 2
  field_simp
  ring

/-- **(24.170) The saddle law has the Gaussian square moments.**  With centred moments `0`, `2t`,
`0`, `3(2t)²` the observable `Y = L²` at mean `t` has `𝔼Y = t² + 2t` and `Var Y = 8t³ + 8t²`, so
the bracket of the Lorentz determinant vanishes identically. -/
theorem tiltedHeatSaddle_moments (t : ℝ) :
    t ^ 2 + 2 * t * 0 + 2 * t = t ^ 2 + 2 * t
      ∧ (t ^ 4 + 4 * t ^ 3 * 0 + 6 * t ^ 2 * (2 * t) + 4 * t * 0 + 3 * (2 * t) ^ 2)
          - (t ^ 2 + 2 * t * 0 + 2 * t) ^ 2
        = 8 * t ^ 3 + 8 * t ^ 2 := by
  have h := shifted_square_moments (m := t) (sig2 := 2 * t) (EZ := 0) (EZ2 := 2 * t)
    (EZ3 := 0) (EZ4 := 3 * (2 * t) ^ 2) rfl rfl rfl rfl
  refine ⟨h.1, ?_⟩
  rw [h.2]
  ring

end

end RHTower

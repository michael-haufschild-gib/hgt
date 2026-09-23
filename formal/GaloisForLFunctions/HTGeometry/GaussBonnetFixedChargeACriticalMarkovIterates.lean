import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalMarkovSpectrum

/-!
Exact transition probabilities after any positive number of steps for the
Markov kernel obtained from the critical Gibbs profile of arXiv:2609.00025.
-/
namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every positive iterate has exactly two decaying harmonic pairs. -/
theorem egbFixedChargeACriticalMarkovMatrix_pow_laurent
    (n m : ℕ) (i j : Fin (2 ^ (n + 3))) :
    ((2 : ℝ) ^ (n + 3) : ℂ) * (egbFixedChargeACriticalMarkovMatrix n ^ (m + 1)) i j =
      1 + (2 / 3 : ℂ) ^ (m + 1) *
        (egbFixedChargeAFourierCharacter (n + 3) i j +
          star (egbFixedChargeAFourierCharacter (n + 3) i j)) +
        (1 / 6 : ℂ) ^ (m + 1) *
        (egbFixedChargeAFourierCharacter (n + 3) i j ^ (2 : ℕ) +
          star (egbFixedChargeAFourierCharacter (n + 3) i j) ^ (2 : ℕ)) := by
  rw [egbFixedChargeACriticalMarkovMatrix_pow_QFT, egbFixedChargeAFiveModeSpectrum_scaled_entry]
  have hm (k : Fin 5) := congrFun (egbFixedChargeAFourierCharacter_modes n i j) k
  simp only [hm, egbFixedChargeACriticalMarkovEigenvalues, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, one_pow]
  ring

/-- Real harmonic form of the full transition matrix after any positive number of steps. -/
theorem egbFixedChargeACriticalMarkovMatrix_pow_harmonic
    (n m : ℕ) (i j : Fin (2 ^ (n + 3))) :
    ((2 : ℝ) ^ (n + 3) : ℂ) * (egbFixedChargeACriticalMarkovMatrix n ^ (m + 1)) i j =
      ((1 + 2 * (2 / 3 : ℝ) ^ (m + 1) *
        Real.cos (2 * (egbFixedChargeAFourierGrid (n + 3) i -
          egbFixedChargeAFourierGrid (n + 3) j)) +
        2 * (1 / 6 : ℝ) ^ (m + 1) *
        Real.cos (4 * (egbFixedChargeAFourierGrid (n + 3) i -
          egbFixedChargeAFourierGrid (n + 3) j)) : ℝ) : ℂ) := by
  rw [egbFixedChargeACriticalMarkovMatrix_pow_laurent,
    egbFixedChargeAFourierCharacter_pair, egbFixedChargeAFourierCharacter_square_pair]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

/-- Exact scaled transition probabilities, expressed entirely over the reals. -/
theorem egbFixedChargeACriticalMarkovMatrix_pow_real
    (n m : ℕ) (i j : Fin (2 ^ (n + 3))) :
    (2 : ℝ) ^ (n + 3) * ((egbFixedChargeACriticalMarkovMatrix n ^ (m + 1)) i j).re =
      1 + 2 * (2 / 3 : ℝ) ^ (m + 1) *
        Real.cos (2 * (egbFixedChargeAFourierGrid (n + 3) i -
          egbFixedChargeAFourierGrid (n + 3) j)) +
        2 * (1 / 6 : ℝ) ^ (m + 1) *
        Real.cos (4 * (egbFixedChargeAFourierGrid (n + 3) i -
          egbFixedChargeAFourierGrid (n + 3) j)) := by
  have h := egbFixedChargeACriticalMarkovMatrix_pow_harmonic n m i j
  rw [← Complex.ofReal_pow] at h
  have hr := congrArg Complex.re h
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hr

/-- The complex QFT formula represents actual real transition probabilities. -/
theorem egbFixedChargeACriticalMarkovMatrix_pow_im_zero
    (n m : ℕ) (i j : Fin (2 ^ (n + 3))) :
    ((egbFixedChargeACriticalMarkovMatrix n ^ m) i j).im = 0 := by
  cases m with
  | zero =>
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  | succ m =>
    have h := egbFixedChargeACriticalMarkovMatrix_pow_harmonic n m i j
    rw [← Complex.ofReal_pow] at h
    have hi := congrArg Complex.im h
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at hi
    exact (mul_eq_zero.mp hi).resolve_left (pow_ne_zero _ (by norm_num))

end

end GaloisForLFunctions.HTGeometry

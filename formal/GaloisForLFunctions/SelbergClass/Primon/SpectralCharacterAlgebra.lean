import GaloisForLFunctions.SelbergClass.Primon.SemicircleCharacters

/-!
# Spectral character recurrences

The free Jacobi recurrence restricts to a recurrence within each parity.
The prime Favard polynomials differ from the free characters by one
backward correction, now in the spectral variable rather than phase.
-/

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

@[simp] theorem spectralCharacter_zero (x : ℝ) : spectralCharacter 0 x = 1 := by
  simp [spectralCharacter, Polynomial.Chebyshev.U_zero]

@[simp] theorem spectralCharacter_one (x : ℝ) : spectralCharacter 1 x = x := by
  simp [spectralCharacter, Polynomial.Chebyshev.U_one]
  ring

/-- The normalized spectral characters satisfy the free Jacobi recurrence. -/
theorem spectralCharacter_add_two (n : ℕ) (x : ℝ) :
    spectralCharacter (n + 2) x =
      x * spectralCharacter (n + 1) x - spectralCharacter n x := by
  have h := congrArg (Polynomial.eval (x / 2)) (Polynomial.Chebyshev.U_add_two ℝ (n : ℤ))
  simpa only [spectralCharacter, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
    ContinuousMap.coe_mk, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (2 : ℝ) * (x / 2) = x by ring] using h

/-- Taking two Jacobi steps eliminates the odd character. -/
theorem spectralCharacter_add_four (n : ℕ) (x : ℝ) :
    spectralCharacter (n + 4) x =
      (x ^ 2 - 2) * spectralCharacter (n + 2) x - spectralCharacter n x := by
  have h0 := spectralCharacter_add_two n x
  have h1 := spectralCharacter_add_two (n + 1) x
  have h2 := spectralCharacter_add_two (n + 2) x
  simp only [show n + 1 + 2 = n + 3 by omega,
    show n + 1 + 1 = n + 2 by omega] at h1
  simp only [show n + 2 + 2 = n + 4 by omega,
    show n + 2 + 1 = n + 3 by omega] at h2
  linear_combination h2 + x * h1 + h0

/-- The prime Favard polynomial is a two-character correction at every spectral point. -/
theorem kestenPolynomial_eval_spectral (p : Nat.Primes) (n : ℕ) (x : ℝ) :
    (kestenPolynomial p (n + 2)).eval x =
      spectralCharacter (n + 2) x - (p : ℝ)⁻¹ * spectralCharacter n x := by
  induction n using Nat.twoStepInduction with
  | zero =>
      rw [kestenPolynomial_two, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C, spectralCharacter_add_two]
      simp only [Nat.zero_add, spectralCharacter_zero, spectralCharacter_one]
      ring
  | one =>
      rw [show 1 + 2 = 0 + 3 by omega, kestenPolynomial_add_three,
        Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
        kestenPolynomial_two, kestenPolynomial_one, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      rw [show 0 + 3 = 1 + 2 by omega, spectralCharacter_add_two,
        spectralCharacter_add_two]
      simp only [Nat.zero_add, spectralCharacter_zero, spectralCharacter_one]
      ring
  | more n hn hn1 =>
      rw [show n + 2 + 2 = (n + 1) + 3 by omega, kestenPolynomial_add_three,
        Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, hn1,
        show n + 1 + 1 = n + 2 by omega, hn]
      rw [spectralCharacter_add_two (n + 2), spectralCharacter_add_two n]
      ring

end
end GaloisForLFunctions.SelbergClass.Primon


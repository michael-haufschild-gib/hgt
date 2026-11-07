import GaloisForLFunctions.SelbergClass.Primon.CharacterMoments
import GaloisForLFunctions.HTGeometry.FavardJacobiMomentRealization

/-!
# The orthogonal-polynomial family of the prime phase density

The Kesten–McKay phase measure in Hartnoll–Yang, arXiv:2502.02661v2, (97),
annihilates `Uₙ - p⁻¹ Uₙ₋₂` in positive degree. These are the monic Favard
polynomials with zero diagonal, first lower coefficient `1 + p⁻¹`, and all
subsequent lower coefficients equal to one.
-/

open MeasureTheory Set Polynomial HTGeometry

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Only the first Jacobi edge differs from the free half-line recurrence. -/
def kestenJacobiLower (p : Nat.Primes) (n : ℕ) : ℝ :=
  if n = 1 then 1 + (p : ℝ)⁻¹ else 1

/-- Monic recurrence polynomials in the Hecke coordinate `x = 2 cos θ`. -/
def kestenPolynomial (p : Nat.Primes) (n : ℕ) : Polynomial ℝ :=
  favardPoly (fun _ => 0) (kestenJacobiLower p) n

theorem kestenJacobiLower_pos (p : Nat.Primes) (n : ℕ) :
    0 < kestenJacobiLower p n := by
  unfold kestenJacobiLower
  split_ifs <;> positivity

@[simp] theorem kestenPolynomial_zero (p : Nat.Primes) : kestenPolynomial p 0 = 1 := rfl

@[simp] theorem kestenPolynomial_one (p : Nat.Primes) : kestenPolynomial p 1 = X := by
  simp [kestenPolynomial]

/-- The exceptional first recurrence step records the prime correction. -/
theorem kestenPolynomial_two (p : Nat.Primes) :
    kestenPolynomial p 2 = X ^ 2 - C (1 + (p : ℝ)⁻¹) := by
  simp [kestenPolynomial, favardPoly_succ_succ, kestenJacobiLower, pow_two]

/-- Away from the boundary, the Jacobi recurrence is the free one. -/
theorem kestenPolynomial_add_three (p : Nat.Primes) (n : ℕ) :
    kestenPolynomial p (n + 3) = X * kestenPolynomial p (n + 2) - kestenPolynomial p (n + 1) := by
  change favardPoly (fun _ => 0) (kestenJacobiLower p) ((n + 1) + 2) = _
  rw [favardPoly_succ_succ]
  simp [kestenJacobiLower, kestenPolynomial]

/-- The standard character recurrence in the phase coordinate. -/
theorem phaseCharacter_recurrence (n : ℕ) (t : ℝ) :
    phaseCharacter (n + 2) t =
      (2 * Real.cos (Real.pi * t)) * phaseCharacter (n + 1) t - phaseCharacter n t := by
  have h := congrArg (Polynomial.eval (Real.cos (Real.pi * t)))
    (Polynomial.Chebyshev.U_add_two ℝ (n : ℤ))
  simpa only [phaseCharacter, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X] using h

/-- The prime orthogonal polynomials are an explicit two-character correction. -/
theorem kestenPolynomial_eval_phase (p : Nat.Primes) (n : ℕ) (t : ℝ) :
    (kestenPolynomial p (n + 2)).eval (2 * Real.cos (Real.pi * t)) =
      phaseCharacter (n + 2) t - (p : ℝ)⁻¹ * phaseCharacter n t := by
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [kestenPolynomial_two, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, phaseCharacter_recurrence]
    simp only [Nat.zero_add, phaseCharacter_zero, phaseCharacter_one]
    ring
  | one =>
    rw [show 1 + 2 = 0 + 3 by omega, kestenPolynomial_add_three]
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
      kestenPolynomial_two, kestenPolynomial_one, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    rw [show 0 + 3 = 1 + 2 by omega, phaseCharacter_recurrence,
      phaseCharacter_recurrence]
    simp only [Nat.zero_add, phaseCharacter_zero, phaseCharacter_one]
    ring
  | more n hn hn1 =>
    rw [show n + 2 + 2 = (n + 1) + 3 by omega, kestenPolynomial_add_three,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
    rw [hn1,
      show n + 1 + 1 = n + 2 by omega, hn]
    rw [phaseCharacter_recurrence (n + 2), phaseCharacter_recurrence n]
    ring

/-- Character means propagate geometrically within each parity class. -/
theorem phaseCharacterAverage_add_two (p : Nat.Primes) (n : ℕ) :
    phaseCharacterAverage p (n + 2) = (p : ℝ)⁻¹ * phaseCharacterAverage p n := by
  rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with h | h
  · have hn : n = 2 * (n / 2) := by omega
    rw [hn, show 2 * (n / 2) + 2 = 2 * (n / 2 + 1) by ring,
      phaseCharacterAverage_even, phaseCharacterAverage_even, pow_succ]
    ring
  · have hn : n = 2 * (n / 2) + 1 := by omega
    rw [hn, show 2 * (n / 2) + 1 + 2 = 2 * (n / 2 + 1) + 1 by ring,
      phaseCharacterAverage_odd, phaseCharacterAverage_odd, mul_zero]

/-- Every positive-degree prime polynomial has exactly zero phase mean. -/
theorem integral_kestenPolynomial_succ (p : Nat.Primes) (n : ℕ) :
    (∫ t in Ioo (0 : ℝ) 1,
      kestenMcKayDensity p t * (kestenPolynomial p (n + 1)).eval (2 * Real.cos (Real.pi * t))) = 0 := by
  cases n with
  | zero =>
    simpa only [Nat.mul_zero, Nat.zero_add, kestenPolynomial_one, Polynomial.eval_X, phaseCharacterAverage,
      phaseCharacter_one] using phaseCharacterAverage_odd p 0
  | succ n =>
    have hi (k : ℕ) : IntegrableOn
        (fun t => kestenMcKayDensity p t * phaseCharacter k t) (Ioo (0 : ℝ) 1) :=
      ((continuous_kestenMcKayDensity p).mul (continuous_phaseCharacter k)).continuousOn.integrableOn_Icc.mono_set
        Ioo_subset_Icc_self
    have he : (fun t => kestenMcKayDensity p t *
        (kestenPolynomial p (n + 1 + 1)).eval (2 * Real.cos (Real.pi * t))) =
        fun t => kestenMcKayDensity p t * phaseCharacter (n + 2) t -
          (p : ℝ)⁻¹ * (kestenMcKayDensity p t * phaseCharacter n t) := by
      funext t
      rw [show n + 1 + 1 = n + 2 by omega, kestenPolynomial_eval_phase]
      ring
    rw [he, integral_sub (hi (n + 2)) ((hi n).const_mul _), integral_const_mul]
    change phaseCharacterAverage p (n + 2) - (p : ℝ)⁻¹ * phaseCharacterAverage p n = 0
    rw [phaseCharacterAverage_add_two, sub_self]

theorem kestenPolynomial_monic (p : Nat.Primes) (n : ℕ) :
    (kestenPolynomial p n).Monic := favardPoly_monic _ _ _

theorem kestenPolynomial_natDegree (p : Nat.Primes) (n : ℕ) :
    (kestenPolynomial p n).natDegree = n := favardPoly_natDegree _ _ _

end
end GaloisForLFunctions.SelbergClass.Primon

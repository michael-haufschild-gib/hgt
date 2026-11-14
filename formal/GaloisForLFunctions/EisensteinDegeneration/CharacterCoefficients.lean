import GaloisForLFunctions.RHTower.DirichletCharacterTwist
import GaloisForLFunctions.RHTower.SiegelProductCoefficients
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.DoubleRootSpecialization

/-!
# Character coefficients at an irregular Eisenstein prime

The positive coefficients of a weight-one Eisenstein series are the
Dirichlet convolution of its two characters. This construction makes sense
without parity or primitivity assumptions; no modularity assertion is
needed for its arithmetic identities. A repeated Hecke root is equivalent
to the whole prime-power sequence being `(k+1) α^k`.

At a common modulus, twisting reduces the first character to the principal
character exactly. The common modulus retains the depletion at bad primes.
These are the coefficient and twisting mechanisms in Polo–Rivero, §2.3 and
the proof of Theorem 6.3.
-/

namespace GaloisForLFunctions.EisensteinDegeneration

open ArithmeticFunction _root_.RHTower ArithmeticCorrespondencePositivity

noncomputable section

/-- The character convolution underlying the positive weight-one Eisenstein coefficients. -/
def weightOneEisensteinCoeff {q₁ q₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) :
    ArithmeticFunction ℂ :=
  toArithmeticFunction (fun n : ℕ => χ₁ n) *
    toArithmeticFunction (fun n : ℕ => χ₂ n)

/-- The two characters may have different moduli. -/
theorem weightOneEisensteinCoeff_prime_pow {q₁ q₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (p : Nat.Primes) (k : ℕ) :
    weightOneEisensteinCoeff χ₁ χ₂ ((p : ℕ) ^ k) =
      spectralMertensRow ![χ₁ (p : ℕ), χ₂ (p : ℕ)] k := by
  rw [weightOneEisensteinCoeff, mul_apply_prime_pow _ _ p.property,
    spectralMertensRow_two]
  apply Finset.sum_congr rfl
  intro j _
  simp [toArithmeticFunction, pow_ne_zero _ p.property.ne_zero, map_pow]

/-- Irregularity is characterized by the entire repeated-root coefficient sequence. -/
theorem weightOneEisenstein_irregular_iff {q₁ q₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (p : Nat.Primes) :
    χ₁ (p : ℕ) = χ₂ (p : ℕ) ↔
      ∀ k : ℕ, weightOneEisensteinCoeff χ₁ χ₂ ((p : ℕ) ^ k) =
        ((k + 1 : ℕ) : ℂ) * χ₁ (p : ℕ) ^ k := by
  simp only [weightOneEisensteinCoeff_prime_pow]
  exact (spectralMertensRow_collision_iff _ _).symm

/-- Coincident characters give the repeated-root formula at every prime, including ramified
primes where their common value is zero. -/
theorem weightOneEisensteinCoeff_diagonal {q : ℕ}
    (χ : DirichletCharacter ℂ q) (p : Nat.Primes) (k : ℕ) :
    weightOneEisensteinCoeff χ χ ((p : ℕ) ^ k) =
      ((k + 1 : ℕ) : ℂ) * χ (p : ℕ) ^ k := by
  rw [weightOneEisensteinCoeff_prime_pow, spectralMertensRow_double]

/-- Twisting character coefficients multiplies the character, with the zero index retained. -/
theorem twist_character_coefficients {q : ℕ} (ψ χ : DirichletCharacter ℂ q) :
    dirichletCharacterTwist ψ (toArithmeticFunction (fun n : ℕ => χ n)) =
      toArithmeticFunction (fun n : ℕ => (ψ * χ) n) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  · simp [dirichletCharacterTwist_apply, toArithmeticFunction, hn, MulChar.mul_apply]

/-- Both Hecke roots are twisted by the same character. -/
theorem weightOneEisensteinCoeff_twist {q : ℕ}
    (ψ χ₁ χ₂ : DirichletCharacter ℂ q) :
    dirichletCharacterTwist ψ (weightOneEisensteinCoeff χ₁ χ₂) =
      weightOneEisensteinCoeff (ψ * χ₁) (ψ * χ₂) := by
  rw [weightOneEisensteinCoeff, dirichletCharacterTwist_mul,
    twist_character_coefficients, twist_character_coefficients]
  rfl

/-- The common-level coefficient system is already depleted at every bad prime. -/
theorem weightOneEisensteinCoeff_level_depletion {q : ℕ}
    (χ₁ χ₂ : DirichletCharacter ℂ q) :
    characterLevelDepletion q (weightOneEisensteinCoeff χ₁ χ₂) =
      weightOneEisensteinCoeff χ₁ χ₂ := by
  rw [characterLevelDepletion, weightOneEisensteinCoeff_twist]
  simp

/-- Twisting the auxiliary principal-character Eisenstein system recovers the original
common-level coefficients, with no nonvanishing premise. -/
theorem weightOneEisensteinCoeff_twist_reduction {q : ℕ}
    (χ₁ χ₂ : DirichletCharacter ℂ q) :
    dirichletCharacterTwist χ₁
      (weightOneEisensteinCoeff 1 (χ₁⁻¹ * χ₂)) =
        weightOneEisensteinCoeff χ₁ χ₂ := by
  rw [weightOneEisensteinCoeff_twist]
  simp [← mul_assoc, MulChar.mul_inv]

end

end GaloisForLFunctions.EisensteinDegeneration

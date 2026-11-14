import GaloisForLFunctions.RHTower.DirichletCharacterTwist
import GaloisForLFunctions.RHTower.SiegelProductLFunction
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

/-- Absolute convergence of the character-pair coefficient series needs no cancellation. -/
theorem weightOneEisensteinCoeff_abscissa_le {q₁ q₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) :
    LSeries.abscissaOfAbsConv (fun n => weightOneEisensteinCoeff χ₁ χ₂ n) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro σ hσ
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  exact LSeriesSummable_mul
    (LSeriesSummable_toArithmeticFunction_of_norm_le (fun n => χ₁.norm_le_one n) hs)
    (LSeriesSummable_toArithmeticFunction_of_norm_le (fun n => χ₂.norm_le_one n) hs)

/-- The character-pair Dirichlet series factors throughout the half-plane `Re s > 1`,
written here as `s = 1 + exp σ + it`. -/
theorem weightOneEisensteinCoeff_LSeries (q₁ q₂ : ℕ)
    (χ₁ : DirichletCharacter ℂ (q₁ + 1)) (χ₂ : DirichletCharacter ℂ (q₂ + 1))
    (σ t : ℝ) :
    LSeries (fun n => weightOneEisensteinCoeff χ₁ χ₂ n)
        ((1 + Real.exp σ : ℝ) + (t : ℂ) * Complex.I) =
      DirichletCharacter.LFunction χ₁ ((1 + Real.exp σ : ℝ) + (t : ℂ) * Complex.I) *
        DirichletCharacter.LFunction χ₂ ((1 + Real.exp σ : ℝ) + (t : ℂ) * Complex.I) := by
  have hs : 1 < ((1 + Real.exp σ : ℝ) + (t : ℂ) * Complex.I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_self, add_zero]
    exact lt_add_of_pos_right (1 : ℝ) (Real.exp_pos σ)
  have h₁ := LSeriesSummable_toArithmeticFunction_of_norm_le (fun n => χ₁.norm_le_one n) hs
  have h₂ := LSeriesSummable_toArithmeticFunction_of_norm_le (fun n => χ₂.norm_le_one n) hs
  rw [weightOneEisensteinCoeff, LSeries_mul' h₁ h₂,
    LSeries_toArithmeticFunction, LSeries_toArithmeticFunction,
    DirichletCharacter.LFunction_eq_LSeries χ₁ hs,
    DirichletCharacter.LFunction_eq_LSeries χ₂ hs]

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
  simp [toArithmeticFunction, p.property.ne_zero, map_pow]

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
      (weightOneEisensteinCoeff (1 : DirichletCharacter ℂ q) (χ₁⁻¹ * χ₂)) =
        weightOneEisensteinCoeff χ₁ χ₂ := by
  rw [weightOneEisensteinCoeff_twist]
  simp [← mul_assoc]

end

end GaloisForLFunctions.EisensteinDegeneration

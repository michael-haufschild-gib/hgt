import GaloisForLFunctions.RHTower.DirichletCharacterTwist
import GaloisForLFunctions.RHTower.DirichletLStripBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Contractive character twists of sieve approximations

Multiplication by `χ(n)n^{-ε}` transports Dirichlet convolutions and does not increase
any finite coefficient error moment when `ε ≥ 0`. Thus the algebraic exceptional-twist
step in Lemma 6.1 of arXiv:2610.03707 applies to every existing arithmetic approximation,
with the same error bound. No existence or location of a Siegel zero is assumed.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.zeta
namespace GaloisForLFunctions.ShortIntervalPrimesInProgressions
open RHTower

/-- Character twist with a nonnegative damping magnitude. -/
def dampedCharacterTwist {q : ℕ} (χ : DirichletCharacter ℂ (q + 1))
    (ε : ℝ) (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ where
  toFun n := χ (n : ZMod (q + 1)) * (((n : ℝ) ^ (-|ε|) : ℝ) : ℂ) * f n
  map_zero' := by simp

@[simp] theorem dampedCharacterTwist_apply {q : ℕ} (χ : DirichletCharacter ℂ (q + 1))
    (ε : ℝ) (f : ArithmeticFunction ℂ) (n : ℕ) :
    dampedCharacterTwist χ ε f n =
      χ (n : ZMod (q + 1)) * (((n : ℝ) ^ (-|ε|) : ℝ) : ℂ) * f n := rfl

/-- Damped twisting preserves subtraction. -/
theorem dampedCharacterTwist_sub {q : ℕ} (χ : DirichletCharacter ℂ (q + 1))
    (ε : ℝ) (f g : ArithmeticFunction ℂ) :
    dampedCharacterTwist χ ε (f - g) =
      dampedCharacterTwist χ ε f - dampedCharacterTwist χ ε g := by
  ext n
  change χ (n : ZMod (q + 1)) * (((n : ℝ) ^ (-|ε|) : ℝ) : ℂ) * (f n - g n) =
    χ (n : ZMod (q + 1)) * (((n : ℝ) ^ (-|ε|) : ℝ) : ℂ) * f n -
      χ (n : ZMod (q + 1)) * (((n : ℝ) ^ (-|ε|) : ℝ) : ℂ) * g n
  ring

/-- Complete multiplicativity transports every Dirichlet convolution exactly. -/
theorem dampedCharacterTwist_mul {q : ℕ} (χ : DirichletCharacter ℂ (q + 1))
    (ε : ℝ) (f g : ArithmeticFunction ℂ) :
    dampedCharacterTwist χ ε (f * g) =
      dampedCharacterTwist χ ε f * dampedCharacterTwist χ ε g := by
  ext n
  simp only [dampedCharacterTwist_apply, ArithmeticFunction.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hd).1
  rw [← hprod, Nat.cast_mul, map_mul, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), Complex.ofReal_mul]
  ring

/-- Every individual coefficient contracts under a damped character twist. -/
theorem norm_dampedCharacterTwist_le {q : ℕ} (χ : DirichletCharacter ℂ (q + 1))
    (ε : ℝ) (f : ArithmeticFunction ℂ) (n : ℕ) :
    ‖dampedCharacterTwist χ ε f n‖ ≤ ‖f n‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hw0 := Real.rpow_nonneg (Nat.cast_nonneg n) (-|ε|)
  have hw := Real.rpow_le_one_of_one_le_of_nonpos hn1 (neg_nonpos.mpr (abs_nonneg ε))
  have hc := norm_dirichletCharacter_le_one χ (n : ZMod (q + 1))
  rw [dampedCharacterTwist_apply, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hw0]
  calc
    ‖χ (n : ZMod (q + 1))‖ * (n : ℝ) ^ (-|ε|) * ‖f n‖ ≤
        1 * (n : ℝ) ^ (-|ε|) * ‖f n‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hw0) (norm_nonneg _)
    _ ≤ ‖f n‖ := by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hw (norm_nonneg (f n))

/-- All finite error moments of a convolution approximation survive the twist unchanged. -/
theorem dampedCharacterTwist_convolution_error_moment {q : ℕ}
    (χ : DirichletCharacter ℂ (q + 1)) (ε : ℝ)
    (f a b : ArithmeticFunction ℂ) (I : Finset ℕ) (p : ℕ) :
    (∑ n ∈ I, ‖dampedCharacterTwist χ ε f n -
      (dampedCharacterTwist χ ε a * dampedCharacterTwist χ ε b) n‖ ^ p) ≤
      ∑ n ∈ I, ‖f n - (a * b) n‖ ^ p := by
  rw [← dampedCharacterTwist_mul]
  apply Finset.sum_le_sum
  intro n _
  have he : dampedCharacterTwist χ ε f n - dampedCharacterTwist χ ε (a * b) n =
      dampedCharacterTwist χ ε (f - a * b) n := by
    rw [dampedCharacterTwist_sub]
    rfl
  rw [he]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_dampedCharacterTwist_le χ ε (f - a * b) n) p

#print axioms dampedCharacterTwist_mul
#print axioms norm_dampedCharacterTwist_le
#print axioms dampedCharacterTwist_convolution_error_moment

end GaloisForLFunctions.ShortIntervalPrimesInProgressions

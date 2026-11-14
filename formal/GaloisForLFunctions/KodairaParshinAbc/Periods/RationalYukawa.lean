import GaloisForLFunctions.HTGeometry.RationalFunctionPartialInvariant
import Mathlib.Tactic

/-!
# Rational Yukawa equations and their complete solution spaces

The one-pole symbols `1-a t` of the projective hypersurface examples give
the algebraic Yukawa coupling `1/(t^(n+1)(1-a t))`. Multiplication by its
denominator turns the differential equation into the constant-derivative
equation. The kernel theorem for the corpus's rational derivative then
classifies every rational solution, including the zero solution.
-/

noncomputable section

namespace GaloisForLFunctions.KodairaParshinAbc.Periods

open Polynomial HTGeometry

private abbrev x : RatFunc ℚ := algebraMap ℚ[X] (RatFunc ℚ) X

/-- Denominator of the algebraic coupling for a one-pole symbol. -/
def yukawaDenominator (n : ℕ) (a : ℚ) : ℚ[X] :=
  X ^ (n + 1) * (1 - C a * X)

/-- The normalized rational algebraic coupling. -/
def rationalYukawa (n : ℕ) (a : ℚ) : RatFunc ℚ :=
  (algebraMap ℚ[X] (RatFunc ℚ) (yukawaDenominator n a))⁻¹

private theorem symbol_ne_zero (a : ℚ) : (1 - C a * X : ℚ[X]) ≠ 0 := by
  intro h
  have hc := congrArg (fun p : ℚ[X] => p.coeff 0) h
  simpa using hc

theorem yukawaDenominator_ne_zero (n : ℕ) (a : ℚ) : yukawaDenominator n a ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ X_ne_zero) (symbol_ne_zero a)

theorem derivative_yukawaDenominator (n : ℕ) (a : ℚ) :
    (yukawaDenominator n a).derivative =
      X ^ n * (C (n + 1 : ℚ) - C ((n + 2 : ℚ) * a) * X) := by
  simp only [yukawaDenominator, derivative_mul, derivative_pow, derivative_sub,
    derivative_one, derivative_C, derivative_X, zero_mul, zero_add,
    Nat.add_sub_cancel, mul_one, Nat.cast_add, Nat.cast_one]
  rw [pow_succ]
  simp only [map_add, map_mul, map_natCast, map_one]
  ring

/-- The differential expression with all singular denominators cleared. -/
def yukawaEquation (n : ℕ) (a : ℚ) (f : RatFunc ℚ) : RatFunc ℚ :=
  x * (1 - algebraMap ℚ (RatFunc ℚ) a * x) * ratFuncDerivative ℚ f +
    ((n + 1 : RatFunc ℚ) - (n + 2) * algebraMap ℚ (RatFunc ℚ) a * x) * f

private theorem map_C (a : ℚ) :
    algebraMap ℚ[X] (RatFunc ℚ) (C a) = algebraMap ℚ (RatFunc ℚ) a := by
  rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

/-- The integrating factor is exactly the reciprocal coupling. -/
theorem yukawa_integrating_factor (n : ℕ) (a : ℚ) (f : RatFunc ℚ) :
    ratFuncDerivative ℚ (algebraMap ℚ[X] (RatFunc ℚ) (yukawaDenominator n a) * f) =
      x ^ n * yukawaEquation n a f := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul,
    ratFuncDerivative_algebraMap, derivative_yukawaDenominator]
  simp only [yukawaDenominator, yukawaEquation, map_mul, map_pow, map_sub, map_one,
    map_C, map_add, map_natCast, pow_succ]
  ring

/-- Every rational solution is a constant multiple of the algebraic Yukawa coupling. -/
theorem yukawaEquation_eq_zero_iff (n : ℕ) (a : ℚ) (f : RatFunc ℚ) :
    yukawaEquation n a f = 0 ↔
      ∃ c : ℚ, f = algebraMap ℚ (RatFunc ℚ) c * rationalYukawa n a := by
  have hx : (x : RatFunc ℚ) ≠ 0 := RatFunc.algebraMap_ne_zero X_ne_zero
  have hp := RatFunc.algebraMap_ne_zero (yukawaDenominator_ne_zero n a)
  have he : ratFuncDerivative ℚ
      (algebraMap ℚ[X] (RatFunc ℚ) (yukawaDenominator n a) * f) = 0 ↔
        yukawaEquation n a f = 0 := by
    rw [yukawa_integrating_factor]
    simp only [mul_eq_zero, pow_ne_zero n hx, false_or]
  rw [← he, ratFuncDerivative_eq_zero_iff]
  apply exists_congr
  intro c
  unfold rationalYukawa
  rw [← div_eq_mul_inv, eq_div_iff hp]
  constructor <;> intro h <;> simpa only [mul_comm] using h

/-- The distinguished coupling solves the equation for every exponent and every parameter. -/
theorem rationalYukawa_solves (n : ℕ) (a : ℚ) :
    yukawaEquation n a (rationalYukawa n a) = 0 := by
  exact (yukawaEquation_eq_zero_iff n a _).mpr ⟨1, by simp⟩

/-- The cubic, quartic and quintic symbols all belong to this rational solution family. -/
theorem projective_yukawa_solutions :
    yukawaEquation 0 27 (rationalYukawa 0 27) = 0 ∧
      yukawaEquation 1 256 (rationalYukawa 1 256) = 0 ∧
      yukawaEquation 2 3125 (rationalYukawa 2 3125) = 0 :=
  ⟨rationalYukawa_solves _ _, rationalYukawa_solves _ _, rationalYukawa_solves _ _⟩

end GaloisForLFunctions.KodairaParshinAbc.Periods

#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.yukawaDenominator_ne_zero
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.derivative_yukawaDenominator
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.yukawa_integrating_factor
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.yukawaEquation_eq_zero_iff
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.rationalYukawa_solves
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.projective_yukawa_solutions

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-!
# Arithmetic order of the complete Möbius Neumann remainder

In the Dirichlet-convolution ring put `R = zeta - 1`. The exact second remainder
`moebius * R^2 = zeta - 1 - 1 + moebius` is coefficientwise nonnegative:
away from zero and one its coefficient is `1 + moebius n`. Convolution with
nonnegative `R` preserves this sign at every higher order.

Consequently the complete alternating polynomials bracket the actual Möbius
coefficients: odd degrees give lower bounds, and positive even degrees give
upper bounds. All coefficients and the entire remainder are retained. Against
nonnegative summable physical weights these give one-sided inverse bounds;
this module proves their unconditional arithmetic order, not a critical
estimate for the growing-degree upper polynomial and not RH.
-/

open ArithmeticFunction
open scoped BigOperators

namespace RHTower.MobiusNeumann

/-- The positive Dirichlet-convolution tail of the constant-one arithmetic function. -/
def tailCoeff : ArithmeticFunction ℤ := zeta - 1

/-- The entire alternating convolution polynomial through degree `K`. -/
def prefixCoeff (K : ℕ) : ArithmeticFunction ℤ :=
  ∑ j ∈ Finset.range (K + 1), (-tailCoeff) ^ j

theorem tailCoeff_nonneg (n : ℕ) : 0 ≤ tailCoeff n := by
  change 0 ≤ ((zeta : ArithmeticFunction ℤ) n - (1 : ArithmeticFunction ℤ) n)
  by_cases hn0 : n = 0
  · subst n
    simp
  by_cases hn1 : n = 1
  · subst n
    simp
  simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
    hn0, hn1]

/-- Two inverse-tail factors remove every negative coefficient of the remainder. -/
theorem residual_two :
    moebius * tailCoeff ^ 2 = (zeta : ArithmeticFunction ℤ) - 1 - 1 + moebius := by
  have hmz : (moebius : ArithmeticFunction ℤ) * zeta = 1 :=
    coe_moebius_mul_coe_zeta
  calc
    _ = (moebius * zeta) * zeta - (moebius * zeta) -
        (moebius * zeta) + moebius := by unfold tailCoeff; ring
    _ = _ := by rw [hmz]; ring

theorem residual_two_nonneg (n : ℕ) : 0 ≤ (moebius * tailCoeff ^ 2) n := by
  rw [residual_two]
  change 0 ≤ (zeta : ArithmeticFunction ℤ) n - (1 : ArithmeticFunction ℤ) n -
    (1 : ArithmeticFunction ℤ) n + moebius n
  by_cases hn0 : n = 0
  · subst n
    simp
  by_cases hn1 : n = 1
  · subst n
    simp
  simp only [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
    ArithmeticFunction.one_apply, if_neg hn0, if_neg hn1, Int.natCast_one, sub_zero]
  have h := (abs_le.mp (abs_moebius_le_one (n := n))).1
  omega

/-- Every higher complete remainder has nonnegative arithmetic coefficients. -/
theorem residual_nonneg (k n : ℕ) : 0 ≤ (moebius * tailCoeff ^ (k + 2)) n := by
  induction k generalizing n with
  | zero => simpa using residual_two_nonneg n
  | succ k ih =>
      have he : moebius * tailCoeff ^ (k + 1 + 2) =
          (moebius * tailCoeff ^ (k + 2)) * tailCoeff := by
        rw [show k + 1 + 2 = k + 2 + 1 by omega, pow_succ, mul_assoc]
      rw [he, ArithmeticFunction.mul_apply]
      exact Finset.sum_nonneg fun ab _ => mul_nonneg (ih ab.1) (tailCoeff_nonneg ab.2)

/-- No tail is dropped in the exact alternating inverse formula. -/
theorem remainder (K : ℕ) :
    moebius - prefixCoeff K = moebius * (-tailCoeff) ^ (K + 1) := by
  have hz : 1 - (-tailCoeff) = (zeta : ArithmeticFunction ℤ) := by
    unfold tailCoeff
    ring
  have hgeom : prefixCoeff K * (zeta : ArithmeticFunction ℤ) =
      1 - (-tailCoeff) ^ (K + 1) := by
    simpa only [prefixCoeff, hz] using geom_sum_mul_neg (-tailCoeff) (K + 1)
  have h := congrArg (fun a : ArithmeticFunction ℤ => moebius * a) hgeom
  have hl : moebius * (prefixCoeff K * (zeta : ArithmeticFunction ℤ)) =
      prefixCoeff K := by
    calc
      _ = prefixCoeff K * (moebius * (zeta : ArithmeticFunction ℤ)) := by ring
      _ = _ := by
        have hmz : (moebius : ArithmeticFunction ℤ) * zeta = 1 :=
          coe_moebius_mul_coe_zeta
        rw [hmz, mul_one]
  rw [hl, mul_sub, mul_one] at h
  rw [h]
  abel

/-- Odd truncations are coefficientwise lower bounds for the full Möbius inverse. -/
theorem odd_prefix_le (k n : ℕ) : prefixCoeff (2 * k + 1) n ≤ moebius n := by
  have heven : Even (2 * k + 1 + 1) := ⟨k + 1, by omega⟩
  have h := remainder (2 * k + 1)
  rw [heven.neg_pow] at h
  have hn := congrArg (fun a : ArithmeticFunction ℤ => a n) h
  change moebius n - prefixCoeff (2 * k + 1) n = _ at hn
  have hpos := residual_nonneg (2 * k) n
  have hexp : 2 * k + 1 + 1 = 2 * k + 2 := by omega
  rw [hexp] at hn
  omega

/-- Positive even truncations are coefficientwise upper bounds for the full inverse. -/
theorem le_even_prefix (k n : ℕ) : moebius n ≤ prefixCoeff (2 * k + 2) n := by
  have hodd : Odd (2 * k + 2 + 1) := ⟨k + 1, by omega⟩
  have h := remainder (2 * k + 2)
  rw [hodd.neg_pow, mul_neg] at h
  have hn := congrArg (fun a : ArithmeticFunction ℤ => a n) h
  change moebius n - prefixCoeff (2 * k + 2) n = -(moebius * tailCoeff ^ (2*k+2+1)) n at hn
  have hpos := residual_nonneg (2 * k + 1) n
  have hexp : 2*k+2+1 = (2*k+1)+2 := by omega
  rw [hexp] at hn
  omega

end RHTower.MobiusNeumann

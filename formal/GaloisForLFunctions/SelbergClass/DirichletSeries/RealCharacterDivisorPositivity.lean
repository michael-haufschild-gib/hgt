import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith

/-!
# Positive reciprocal-divisor sums of real characters

For every real Dirichlet character, `∑ d ∣ n, χ(d)/d` is strictly positive
at positive integers. Multiplicativity factors the sum into finite
geometric sums. Each prime ratio exceeds `-1`, even when the character
takes negative values. This gives the nonvanishing mechanism underlying
quadratic-irrational logarithmic coefficients of Euler products.
-/

noncomputable section
namespace GaloisForLFunctions.SelbergClass

open ArithmeticFunction
open scoped ArithmeticFunction.zeta

variable {N : ℕ}

/-- Character coefficients at the reciprocal-divisor weight. -/
def reciprocalRealCharacter (χ : DirichletCharacter ℝ N) : ArithmeticFunction ℝ where
  toFun n := χ (n : ZMod N) / (n : ℝ)
  map_zero' := by simp

private theorem reciprocalRealCharacter_multiplicative (χ : DirichletCharacter ℝ N) :
    (reciprocalRealCharacter χ).IsMultiplicative := by
  constructor
  · simp [reciprocalRealCharacter]
  · intro m n _
    change χ ((m * n : ℕ) : ZMod N) / ((m * n : ℕ) : ℝ) = _
    simp only [Nat.cast_mul, map_mul]
    exact (div_mul_div_comm _ _ _ _).symm

private theorem reciprocalRealCharacter_prime_pow (χ : DirichletCharacter ℝ N)
    (p k : ℕ) :
    reciprocalRealCharacter χ (p ^ k) = (χ (p : ZMod N) / (p : ℝ)) ^ k := by
  simp only [reciprocalRealCharacter, coe_mk, Nat.cast_pow, map_pow, div_pow]

private theorem realCharacter_prime_ratio_add_one_pos (χ : DirichletCharacter ℝ N)
    {p : ℕ} (hp : p.Prime) : 0 < χ (p : ZMod N) / (p : ℝ) + 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hb : |χ (p : ZMod N)| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using χ.norm_le_one (p : ZMod N)
  have hl : (-1 : ℝ) < χ (p : ZMod N) / (p : ℝ) := by
    apply (lt_div_iff₀ hp0).mpr
    linarith only [(abs_le.mp hb).1, hp1]
  linarith only [hl]

/-- Exact Euler factorization of the reciprocal-character divisor sum. -/
theorem reciprocalRealCharacter_divisor_product (χ : DirichletCharacter ℝ N) (n : ℕ) :
    (∑ d ∈ (n + 1).divisors, χ (d : ZMod N) / (d : ℝ)) =
      ∏ p ∈ (n + 1).primeFactors,
        ∑ j ∈ Finset.range ((n + 1).factorization p + 1),
          (χ (p : ZMod N) / (p : ℝ)) ^ j := by
  have hm := isMultiplicative_zeta.natCast.mul
    (reciprocalRealCharacter_multiplicative χ)
  have hf := hm.multiplicative_factorization _ (Nat.succ_ne_zero n)
  rw [coe_zeta_mul_apply, Finsupp.prod, Nat.support_factorization] at hf
  change (∑ d ∈ (n + 1).divisors, reciprocalRealCharacter χ d) = _
  rw [hf]
  apply Finset.prod_congr rfl
  intro p hp
  rw [coe_zeta_mul_apply, Nat.sum_divisors_prime_pow (Nat.prime_of_mem_primeFactors hp)]
  exact Finset.sum_congr rfl fun j _ => reciprocalRealCharacter_prime_pow χ p j

/-- Real character signs cannot cancel the full reciprocal-divisor sum. -/
theorem reciprocalRealCharacter_divisor_sum_pos (χ : DirichletCharacter ℝ N) (n : ℕ) :
    0 < ∑ d ∈ (n + 1).divisors, χ (d : ZMod N) / (d : ℝ) := by
  rw [reciprocalRealCharacter_divisor_product]
  apply Finset.prod_pos
  intro p hp
  exact geom_sum_pos'
    (realCharacter_prime_ratio_add_one_pos χ (Nat.prime_of_mem_primeFactors hp))
    (Nat.succ_ne_zero _)

/-- Rational character sums have the same strict positivity before real embedding. -/
theorem reciprocalRatCharacter_divisor_sum_pos (χ : DirichletCharacter ℚ N) (n : ℕ) :
    0 < ∑ d ∈ (n + 1).divisors, χ (d : ZMod N) / (d : ℚ) := by
  have h := reciprocalRealCharacter_divisor_sum_pos
    (χ.ringHomComp (Rat.castHom ℝ)) n
  simp only [MulChar.ringHomComp_apply] at h
  change (0 : ℝ) < ∑ d ∈ (n + 1).divisors, (χ (d : ZMod N) : ℝ) / (d : ℝ) at h
  exact_mod_cast h

/-- The positive rational character sum prevents any rational correction from
cancelling the `√5` term in a logarithmic Euler-product coefficient. -/
theorem irrational_sqrt_five_character_divisor_coefficient
    (χ : DirichletCharacter ℚ N) (n : ℕ) (r : ℚ) :
    Irrational (Real.sqrt 5 / 2 *
      ((∑ d ∈ (n + 1).divisors, χ (d : ZMod N) / (d : ℚ) : ℚ) : ℝ) + r) := by
  have hq := reciprocalRatCharacter_divisor_sum_pos χ n
  have hs : Irrational (Real.sqrt 5) := by
    simpa using Nat.prime_five.irrational_sqrt
  have h := (hs.mul_ratCast (q :=
    (∑ d ∈ (n + 1).divisors, χ (d : ZMod N) / (d : ℚ)) / 2)
    (div_ne_zero hq.ne' (by norm_num))).add_ratCast r
  convert h using 1
  push_cast
  ring

#print axioms reciprocalRealCharacter_divisor_product
#print axioms reciprocalRealCharacter_divisor_sum_pos
#print axioms reciprocalRatCharacter_divisor_sum_pos
#print axioms irrational_sqrt_five_character_divisor_coefficient

end GaloisForLFunctions.SelbergClass

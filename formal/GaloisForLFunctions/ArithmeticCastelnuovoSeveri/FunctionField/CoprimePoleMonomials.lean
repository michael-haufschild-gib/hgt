import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityFunctionOrders
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RationalPlaceValuations
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.ValuationPowerCoordinates
import Mathlib.Data.Nat.ModEq

/-!
# Coprime pole orders separate Kummer monomials

The weighted-monomial argument in Ma–Wang, Lemma 2.3
(arXiv:2611.14073), applies to the actual Kummer infinity valuation.
The two coordinates have coprime pole orders `Q+1` and `q^r`.
Consequently monomials with radical exponent below `Q+1` have distinct
pole orders. No finite linear combination over the constant field can
cancel to zero unless every coefficient vanishes.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open Polynomial ArithmeticHarmonicAnalysis

/-- Coprime positive weights uniquely encode a monomial when the second exponent is reduced. -/
theorem coprime_monomialWeight_injective {a b : ℕ} (ha : 0 < a) (hab : a.Coprime b) :
    Function.Injective (fun t : ℕ × Fin a => a * t.1 + b * t.2.val) := by
  intro x y h
  dsimp only at h
  have hm : Nat.ModEq a (b * x.2.val) (b * y.2.val) := by
    simpa [Nat.ModEq, Nat.add_mod] using congrArg (fun n => n % a) h
  have hj := (Nat.ModEq.cancel_left_of_coprime hab hm).eq_of_lt_of_lt x.2.isLt y.2.isLt
  apply Prod.ext
  · apply Nat.mul_left_cancel ha
    rw [hj] at h
    exact Nat.add_right_cancel h
  · exact Fin.ext hj

variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)

/-- Reduced raw monomials in the original coordinate and radical. -/
def squareKummerPoleMonomial (t : ℕ × Fin (p ^ (s + 1) + 1)) :
    SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r) :=
  (algebraMap (SquareConstantField p s)[X] _ X) ^ t.1 *
    (AdjoinRoot.root (kummerBranchFieldPolynomial c (p ^ (d + 1) - 2)
      (kummerExponent (p ^ (d + 1)) r) (p ^ (s + 1)))) ^ t.2.val

/-- The actual infinity valuation equals the coprime weighted monomial order. -/
theorem squareKummerPoleMonomial_valuation (t : ℕ × Fin (p ^ (s + 1) + 1)) :
    squareKummerInfinityValuation p s c d r (squareKummerPoleMonomial p s c d r t) =
      WithZero.exp (((p ^ (s + 1) + 1) * t.1 + (p ^ (d + 1)) ^ r * t.2.val : ℕ) : ℤ) := by
  rw [squareKummerPoleMonomial, map_mul, map_pow, map_pow,
    squareKummerInfinityValuation_coordinate, squareKummerInfinityValuation_root,
    ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add]
  congr 1
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_mul]
  ring

/-- Distinct reduced monomials have distinct values at the actual infinity place. -/
theorem squareKummerPoleMonomial_valuation_injective :
    Function.Injective (fun t => squareKummerInfinityValuation p s c d r
      (squareKummerPoleMonomial p s c d r t)) := by
  intro x y h
  dsimp only at h
  rw [squareKummerPoleMonomial_valuation, squareKummerPoleMonomial_valuation] at h
  have hw := WithZero.exp_injective h
  have hab := kummerInfinity_primePower_poleDegree_coprime p s d r
  rw [kummerInfinity_primePower_poleDegree] at hab
  exact coprime_monomialWeight_injective (Nat.succ_pos _) hab (Nat.cast_injective hw)

/-- A nonzero constant has valuation one in the transported infinity chart. -/
theorem squareKummerInfinityValuation_constant (a : SquareConstantField p s) (ha : a ≠ 0) :
    squareKummerInfinityValuation p s c d r (algebraMap (SquareConstantField p s) _ a) = 1 := by
  change (squareKummerInfinityPlace p s c d r).valuation _
    (kummerInfinityFieldEquiv c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)
      (p ^ (s + 1)) (algebraMap (SquareConstantField p s) _ a)) = 1
  rw [AlgEquiv.commutes]
  exact heightOne_valuation_constant _ a ha

/-- The reduced monomials have no nonzero constant-coefficient finite relation. -/
theorem squareKummerPoleMonomial_sum_eq_zero_iff
    (S : Finset (ℕ × Fin (p ^ (s + 1) + 1)))
    (a : ℕ × Fin (p ^ (s + 1) + 1) → SquareConstantField p s) :
    (∑ t ∈ S, algebraMap (SquareConstantField p s) _ (a t) *
      squareKummerPoleMonomial p s c d r t) = 0 ↔ ∀ t ∈ S, a t = 0 := by
  classical
  let v := squareKummerInfinityValuation p s c d r
  let f := fun t => algebraMap (SquareConstantField p s) _ (a t) *
    squareKummerPoleMonomial p s c d r t
  have hf (t) (ht : a t ≠ 0) : v (f t) = v (squareKummerPoleMonomial p s c d r t) := by
    rw [map_mul, squareKummerInfinityValuation_constant p s c d r _ ht, one_mul]
  have hf0 (t) (ht : a t = 0) : v (f t) = 0 := by
    simp only [f, ht, map_zero, zero_mul]
  constructor
  · intro hsum
    have hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → v (f i) = v (f j) → v (f i) = 0 := by
      intro i _ j _ hij heq
      by_cases hi : a i = 0
      · exact hf0 i hi
      by_cases hj : a j = 0
      · exact heq.trans (hf0 j hj)
      rw [hf i hi, hf j hj] at heq
      exact (hij (squareKummerPoleMonomial_valuation_injective p s c d r heq)).elim
    have ht := valuation_terms_le_of_separated v S f hsep 0 (by rw [hsum, map_zero])
    intro i hi
    by_contra hai
    have hzero := le_antisymm (ht i hi) zero_le
    rw [hf i hai, squareKummerPoleMonomial_valuation] at hzero
    exact WithZero.exp_ne_zero hzero
  · intro h
    exact Finset.sum_eq_zero fun i hi => by rw [h i hi, map_zero, zero_mul]

#print axioms squareKummerPoleMonomial_valuation_injective
#print axioms squareKummerPoleMonomial_sum_eq_zero_iff

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

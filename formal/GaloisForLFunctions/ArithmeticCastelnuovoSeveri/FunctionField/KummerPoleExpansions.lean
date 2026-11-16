import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerPoleOrderSeparation
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityPolynomialOrders
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerIntegralMonomialOrders
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.ValuationPowerCoordinates

/-!
# Pole bounds for polynomial radical expansions

Different reduced radical characters have different infinity orders modulo
`Q+1`. Consequently, cancellation cannot lower the largest pole in a
polynomial expansion. A pole bound is exactly a separate degree bound
on every nonzero polynomial coefficient.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)

/-- Synthesize a polynomial expansion in the reduced integral radical monomials. -/
def squareKummerPolynomialExpansion
    (a : Fin (p ^ (s + 1) + 1) → (SquareConstantField p s)[X]) :
    SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r) :=
  ∑ i, algebraMap (SquareConstantField p s)[X]
    (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) (a i) *
      kummerIntegralMonomial c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)
        (p ^ (s + 1)) i.val

/-- A nonzero polynomial character has pole order `N deg(a)+i+(q-1)(iR mod N)`. -/
theorem squareKummerInfinityValuation_polynomialMonomial
    (a : (SquareConstantField p s)[X]) (ha : a ≠ 0) (i : Fin (p ^ (s + 1) + 1)) :
    squareKummerInfinityValuation p s c d r
      (algebraMap (SquareConstantField p s)[X]
        (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) a *
        kummerIntegralMonomial c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)
          (p ^ (s + 1)) i.val) =
      WithZero.exp (((p ^ (s + 1) + 1) * a.natDegree +
        (i.val + (p ^ (d + 1) - 1) *
          (i.val * kummerExponent (p ^ (d + 1)) r % (p ^ (s + 1) + 1))) : ℕ) : ℤ) := by
  rw [map_mul, squareKummerInfinityValuation_polynomial p s c d r a ha,
    squareKummerInfinityValuation_integralMonomial, ← WithZero.exp_add]
  simp only [Nat.cast_add]

/-- Every infinity pole bound is equivalent to the individual polynomial character bounds. -/
theorem squareKummerPolynomialExpansion_pole_bound_iff
    (a : Fin (p ^ (s + 1) + 1) → (SquareConstantField p s)[X]) (m : ℕ) :
    squareKummerInfinityValuation p s c d r (squareKummerPolynomialExpansion p s c d r a) ≤
      WithZero.exp (m : ℤ) ↔
    ∀ i, a i ≠ 0 → (p ^ (s + 1) + 1) * (a i).natDegree +
      (i.val + (p ^ (d + 1) - 1) *
        (i.val * kummerExponent (p ^ (d + 1)) r % (p ^ (s + 1) + 1))) ≤ m := by
  classical
  let K := SquareConstantField p s
  let L := SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)
  let v := squareKummerInfinityValuation p s c d r
  let f : Fin (p ^ (s + 1) + 1) → L := fun i =>
    algebraMap K[X] L (a i) * kummerIntegralMonomial c (p ^ (d + 1) - 2)
      (kummerExponent (p ^ (d + 1)) r) (p ^ (s + 1)) i.val
  have hsep : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
      i ≠ j → v (f i) = v (f j) → v (f i) = 0 := by
    intro i _ j _ hij heq
    by_cases hi : a i = 0
    · simp only [f, hi, map_zero, zero_mul]
    have hj : a j ≠ 0 := by
      intro hj
      have hz : v (f j) = 0 := by simp only [f, hj, map_zero, zero_mul]
      rw [hz, squareKummerInfinityValuation_polynomialMonomial p s c d r (a i) hi i] at heq
      exact WithZero.exp_ne_zero heq
    have hlog := congrArg WithZero.log heq
    rw [squareKummerInfinityValuation_polynomialMonomial p s c d r (a i) hi i,
      squareKummerInfinityValuation_polynomialMonomial p s c d r (a j) hj j,
      WithZero.log_exp, WithZero.log_exp] at hlog
    have hw : (i, (a i).natDegree) = (j, (a j).natDegree) :=
      squareKummer_weightedPoleOrder_injective p s d r (by exact_mod_cast hlog)
    exact (hij (congrArg Prod.fst hw)).elim
  constructor
  · intro h i hi
    have hb := valuation_terms_le_of_separated v Finset.univ f hsep (WithZero.exp (m : ℤ)) h i
      (Finset.mem_univ i)
    rw [squareKummerInfinityValuation_polynomialMonomial p s c d r (a i) hi i,
      WithZero.exp_le_exp] at hb
    exact_mod_cast hb
  · intro h
    apply v.map_sum_le
    intro i _
    by_cases hi : a i = 0
    · simp only [hi, map_zero, zero_mul]
      exact zero_le
    · rw [squareKummerInfinityValuation_polynomialMonomial p s c d r (a i) hi i,
        WithZero.exp_le_exp]
      exact_mod_cast h i hi

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

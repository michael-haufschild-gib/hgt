import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.ReducedResiduePoleOrders
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityRamification

/-!
# Separation of Kummer pole orders

The reduced radical weights are distinct modulo the covering degree.
Thus polynomial degree and radical character are uniquely determined by
the pole order of a polynomial multiple of a reduced radical monomial.
-/

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis

/-- The pole orders of reduced integral basis monomials and their coordinate multiples are distinct. -/
theorem squareKummer_weightedPoleOrder_injective
    (p : ℕ) [Fact p.Prime] (s d r : ℕ) :
    Function.Injective (fun x : Fin (p ^ (s + 1) + 1) × ℕ =>
      (p ^ (s + 1) + 1) * x.2 +
        (x.1.val + (p ^ (d + 1) - 1) *
          (x.1.val * kummerExponent (p ^ (d + 1)) r % (p ^ (s + 1) + 1)))) := by
  have hq : 2 ≤ p ^ (d + 1) :=
    Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  have hcop := (kummerInfinity_primePower_poleDegree_coprime p s d r).symm
  rw [show p ^ (d + 1) - 2 + 1 = p ^ (d + 1) - 1 by omega] at hcop
  exact reducedResidue_weighted_injective _ _ _ hcop

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

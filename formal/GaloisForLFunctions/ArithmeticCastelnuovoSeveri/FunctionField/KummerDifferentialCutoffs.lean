import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.ReducedResidueFloorSum
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityRamification

/-!
# Degree cutoffs for reduced radical differentials

The pole order of a reduced radical monomial gives a polynomial-degree
cutoff. Uniform residue cycles evaluate the sum of these cutoffs in
terms of the common divisor of the covering and branch exponents.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis Finset
variable (p : ℕ) [Fact p.Prime] (s d r : ℕ)

/-- The polynomial-degree cutoff associated with a reduced radical monomial. -/
def kummerDifferentialCutoff (i : ℕ) : ℕ :=
  (i + (p ^ (d + 1) - 1) *
    (i * kummerExponent (p ^ (d + 1)) r % (p ^ (s + 1) + 1))) /
      (p ^ (s + 1) + 1)

/-- The trivial radical character contributes no nonnegative polynomial degree. -/
theorem kummerDifferentialCutoff_zero : kummerDifferentialCutoff p s d r 0 = 0 := by
  simp only [kummerDifferentialCutoff, zero_mul, Nat.zero_mod, mul_zero, zero_add, Nat.zero_div]

/-- Twice the total degree cutoff equals the ramification defect `(q-1)(N-gcd(N,R))`. -/
theorem kummerDifferentialCutoff_sum_twice :
    2 * (∑ i ∈ range (p ^ (s + 1) + 1), kummerDifferentialCutoff p s d r i) =
      (p ^ (d + 1) - 1) *
        (p ^ (s + 1) + 1 - Nat.gcd (p ^ (s + 1) + 1) (kummerExponent (p ^ (d + 1)) r)) := by
  have hq : 2 ≤ p ^ (d + 1) :=
    Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  have hcop := (kummerInfinity_primePower_poleDegree_coprime p s d r).symm
  rw [show p ^ (d + 1) - 2 + 1 = p ^ (d + 1) - 1 by omega] at hcop
  exact two_mul_sum_reducedResidue_floor _ _ _ (Nat.succ_pos _) hcop

/-- The infinity pole-order bound is equivalent to strict polynomial degree below the cutoff. -/
theorem kummerDifferentialCutoff_iff (i : Fin (p ^ (s + 1) + 1)) (k : ℕ) :
    (p ^ (s + 1) + 1) * (k + 1) + 1 ≤
      i.val + (p ^ (d + 1) - 1) *
        (i.val * kummerExponent (p ^ (d + 1)) r % (p ^ (s + 1) + 1)) ↔
      k < kummerDifferentialCutoff p s d r i.val := by
  have hq : 2 ≤ p ^ (d + 1) :=
    Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  have hcop := (kummerInfinity_primePower_poleDegree_coprime p s d r).symm
  rw [show p ^ (d + 1) - 2 + 1 = p ^ (d + 1) - 1 by omega] at hcop
  exact reducedResidue_cutoff_iff _ _ _ (Nat.succ_pos _) hcop i k

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

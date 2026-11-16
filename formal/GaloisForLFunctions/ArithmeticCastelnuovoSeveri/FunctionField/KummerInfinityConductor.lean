import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityGaps
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.ReducedResidueConductor

/-!
# The infinity conductor and its extremal gap

The reduced monomial weights bound every infinity gap by twice the
actual differential genus. Equality at the last possible gap has an
explicit residue criterion, with the rational case included separately.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)
local notation "K" => SquareConstantField p s
local notation "N" => p ^ (s + 1) + 1
local notation "q" => p ^ (d + 1)
local notation "R" => kummerExponent q r
local notation "L" => SquareKummerField p s c (q - 2) R
local notation "g" => Module.finrank K (globalRegularDifferentials K L)

private theorem pole_residue_coprime : Nat.Coprime (1 + (q - 1) * R) N := by
  have hq : 2 ≤ q := Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  have h := (kummerInfinity_primePower_poleDegree_coprime p s d r).symm
  rw [show q - 2 + 1 = q - 1 by omega] at h
  exact h

/-- Every missing infinity pole order is strictly below twice the actual differential genus. -/
theorem squareKummerInfinityGap_lt_twice_genus (a : SquareKummerInfinityGaps p s c d r) :
    a.val < 2 * g := by
  let D : Fin N → ℕ := fun i => i.val + (q - 1) * (i.val * R % N)
  have hresidue (i j : Fin N) (h : D i % N = D j % N) : i = j := by
    dsimp only [D] at h
    rw [reducedResidue_mod, reducedResidue_mod] at h
    have hmod : Nat.ModEq N i.val j.val :=
      Nat.ModEq.cancel_left_of_coprime (pole_residue_coprime p s d r).symm h
    exact Fin.ext (hmod.eq_of_lt_of_lt i.isLt j.isLt)
  let a' : WeightedResidueGaps D := ⟨a.val, fun h => a.property
    ((squareKummer_exists_integral_pole_iff p s c d r a.val).mpr h)⟩
  have h := weightedResidueGap_lt_bound (Nat.succ_pos _) D hresidue
    ((q - 1) * (N - Nat.gcd N R))
    (fun i => reducedResidue_weight_bound N (q - 1) R (Nat.succ_pos _) i) a'
  change a.val < (q - 1) * (N - Nat.gcd N R) at h
  rwa [← squareKummer_regularDifferential_finrank_twice p s c d r] at h

/-- Every order at least twice the actual genus is realized by a function regular away from infinity. -/
theorem squareKummer_exists_integral_pole_of_twice_genus_le (m : ℕ) :
    2 * g ≤ m → ∃ x : L, IsIntegral K[X] x ∧
      squareKummerInfinityValuation p s c d r x = WithZero.exp (m : ℤ) := by
  intro hm
  by_contra h
  exact (not_lt_of_ge hm) (squareKummerInfinityGap_lt_twice_genus p s c d r ⟨m, h⟩)

/-- Outside the rational case, the last possible infinity gap occurs exactly at the maximal last residue. -/
theorem squareKummerInfinity_last_gap_criterion :
    (g = 0 ∨ ¬ ∃ x : L, IsIntegral K[X] x ∧
      squareKummerInfinityValuation p s c d r x = WithZero.exp ((2 * g - 1 : ℕ) : ℤ)) ↔
        (N - 1) * R % N = N - Nat.gcd N R := by
  by_cases hzero : g = 0
  · have hd := (squareKummer_regularDifferential_finrank_eq_zero_iff p s c d r).mp hzero
    have hmul : N ∣ (N - 1) * R := dvd_mul_of_dvd_right hd (N - 1)
    simp only [hzero, true_or, Nat.mod_eq_zero_of_dvd hmul, Nat.gcd_eq_left hd, Nat.sub_self]
  · have hq : 2 ≤ q := Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
    have hB : 0 < (q - 1) * (N - Nat.gcd N R) := by
      rw [← squareKummer_regularDifferential_finrank_twice p s c d r]
      exact Nat.mul_pos (Nat.zero_lt_succ 1) (Nat.pos_of_ne_zero hzero)
    rw [or_iff_right hzero, squareKummer_exists_integral_pole_iff,
      squareKummer_regularDifferential_finrank_twice]
    exact reducedResidue_last_gap_iff N (q - 1) R (Nat.succ_pos _) (by omega)
      (pole_residue_coprime p s d r) hB

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

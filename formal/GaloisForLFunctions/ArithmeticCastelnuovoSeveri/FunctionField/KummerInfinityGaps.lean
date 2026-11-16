import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.WeightedResidueGaps
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerPoleSemigroup
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRegularDifferentialDimension

/-!
# The exact number of infinity gaps

The reduced monomial weights represent every residue modulo `Q+1`.
Their missing pole orders are therefore counted by the sum of their
weight quotients. This is the same sum that counts actual global
regular differentials, proving the gap-genus identity directly for
these Kummer normalizations.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)

/-- Orders not realized by any function regular away from the unique infinity place. -/
abbrev SquareKummerInfinityGaps :=
  {m : ℕ // ¬ ∃ x : SquareKummerField p s c (p ^ (d + 1) - 2)
    (kummerExponent (p ^ (d + 1)) r),
      IsIntegral (SquareConstantField p s)[X] x ∧
      squareKummerInfinityValuation p s c d r x = WithZero.exp (m : ℤ)}

private def poleWeight (i : Fin (p ^ (s + 1) + 1)) : ℕ :=
  i.val + (p ^ (d + 1) - 1) *
    (i.val * kummerExponent (p ^ (d + 1)) r % (p ^ (s + 1) + 1))

private theorem poleWeight_residue_injective
    (i j : Fin (p ^ (s + 1) + 1))
    (h : poleWeight p s d r i % (p ^ (s + 1) + 1) =
      poleWeight p s d r j % (p ^ (s + 1) + 1)) : i = j := by
  have hq : 2 ≤ p ^ (d + 1) :=
    Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  have hcop := (kummerInfinity_primePower_poleDegree_coprime p s d r).symm
  rw [show p ^ (d + 1) - 2 + 1 = p ^ (d + 1) - 1 by omega] at hcop
  dsimp only [poleWeight] at h
  rw [reducedResidue_mod, reducedResidue_mod] at h
  have hi : Nat.ModEq (p ^ (s + 1) + 1) i.val j.val :=
    Nat.ModEq.cancel_left_of_coprime hcop.symm h
  exact Fin.ext (hi.eq_of_lt_of_lt i.isLt j.isLt)

private def infinityGapEquiv :
    SquareKummerInfinityGaps p s c d r ≃ WeightedResidueGaps (poleWeight p s d r) where
  toFun m := ⟨m.val, fun h => m.property
    ((squareKummer_exists_integral_pole_iff p s c d r m.val).mpr h)⟩
  invFun m := ⟨m.val, fun h => m.property
    ((squareKummer_exists_integral_pole_iff p s c d r m.val).mp h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Only finitely many nonnegative orders fail to occur as infinity pole orders.
The explicit residue coordinates give a finite set of witnesses for every gap. -/
instance squareKummerInfinityGaps_finite : Finite (SquareKummerInfinityGaps p s c d r) :=
  Finite.of_injective
    ((infinityGapEquiv p s c d r).trans
      (weightedResidueGapEquiv (Nat.succ_pos _) (poleWeight p s d r)
        (poleWeight_residue_injective p s d r)).symm)
    ((infinityGapEquiv p s c d r).trans
      (weightedResidueGapEquiv (Nat.succ_pos _) (poleWeight p s d r)
        (poleWeight_residue_injective p s d r)).symm).injective

/-- The missing infinity orders are counted by the explicit character degree cutoffs. -/
theorem squareKummerInfinityGaps_card_sum :
    Nat.card (SquareKummerInfinityGaps p s c d r) =
      ∑ i : Fin (p ^ (s + 1) + 1), kummerDifferentialCutoff p s d r i.val := by
  rw [Nat.card_congr (infinityGapEquiv p s c d r),
    weightedResidueGaps_card (Nat.succ_pos _) _ (poleWeight_residue_injective p s d r)]
  rfl

/-- The number of missing infinity pole orders equals the dimension of actual global regular differentials. -/
theorem squareKummerInfinityGaps_card_eq_genus :
    Nat.card (SquareKummerInfinityGaps p s c d r) =
      Module.finrank (SquareConstantField p s)
        (globalRegularDifferentials (SquareConstantField p s)
          (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r))) := by
  rw [squareKummerInfinityGaps_card_sum, squareKummer_regularDifferential_finrank_sum]

/-- The exact number of infinity gaps is the explicit Kummer genus formula. -/
theorem squareKummerInfinityGaps_card :
    Nat.card (SquareKummerInfinityGaps p s c d r) =
      ((p ^ (d + 1) - 1) *
        (p ^ (s + 1) + 1 - Nat.gcd (p ^ (s + 1) + 1)
          (kummerExponent (p ^ (d + 1)) r))) / 2 := by
  rw [squareKummerInfinityGaps_card_eq_genus, squareKummer_regularDifferential_finrank]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

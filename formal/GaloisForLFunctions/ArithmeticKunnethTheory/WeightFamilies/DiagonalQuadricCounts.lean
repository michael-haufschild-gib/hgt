import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Finite-field quadratic counts

The product equation obtained from a difference of squares gives the quadratic
character sum needed for diagonal quadratic forms. All counts refer to actual
finite sets of solutions.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The affine difference-of-squares fibre. -/
def squareDifferencePairs (c : F) : Finset (F × F) :=
  univ.filter (fun p => p.1 ^ 2 - p.2 ^ 2 = c)

/-- A nonzero factor and its complementary factor give a difference-of-squares solution. -/
def squareDifferenceParam (c : F) (u : Fˣ) : F × F :=
  (((u : F) + c / u) / 2, (c / u - u) / 2)

omit [Fintype F] [DecidableEq F] in
theorem squareDifferenceParam_sub (h₂ : (2 : F) ≠ 0) (c : F) (u : Fˣ) :
    (squareDifferenceParam c u).1 - (squareDifferenceParam c u).2 = (u : F) := by
  dsimp [squareDifferenceParam]
  field_simp [h₂, u.ne_zero]
  ring

omit [Fintype F] [DecidableEq F] in
theorem squareDifferenceParam_value (h₂ : (2 : F) ≠ 0) (c : F) (u : Fˣ) :
    (squareDifferenceParam c u).1 ^ 2 - (squareDifferenceParam c u).2 ^ 2 = c := by
  dsimp [squareDifferenceParam]
  field_simp [h₂, u.ne_zero]
  ring

/-- A nonzero difference-of-squares fibre has exactly one point per nonzero factor. -/
theorem squareDifferencePairs_card (h₂ : (2 : F) ≠ 0) {c : F} (hc : c ≠ 0) :
    (squareDifferencePairs c).card = Fintype.card F - 1 := by
  calc (squareDifferencePairs c).card = (univ : Finset Fˣ).card := by
      symm
      apply card_bij (fun u _ => squareDifferenceParam c u)
      · intro u _
        exact mem_filter.mpr ⟨mem_univ _, squareDifferenceParam_value h₂ c u⟩
      · intro u _ v _ h
        apply Units.ext
        have hh := congrArg (fun p : F × F => p.1 - p.2) h
        simpa only [squareDifferenceParam_sub h₂] using hh
      · intro p hp
        have he := (mem_filter.mp hp).2
        have hu : p.1 - p.2 ≠ 0 := by
          intro hz
          apply hc
          calc c = p.1 ^ 2 - p.2 ^ 2 := he.symm
            _ = 0 := by rw [sub_eq_zero.mp hz, sub_self]
        have hprod : (p.1 - p.2) * (p.1 + p.2) = c := by
          linear_combination he
        have hdiv : c / (p.1 - p.2) = p.1 + p.2 := by
          apply (div_eq_iff hu).mpr
          rw [mul_comm]
          exact hprod.symm
        refine ⟨Units.mk0 (p.1 - p.2) hu, mem_univ _, ?_⟩
        apply Prod.ext
        · dsimp [squareDifferenceParam]
          rw [hdiv]
          field_simp [h₂]
          ring
        · dsimp [squareDifferenceParam]
          rw [hdiv]
          field_simp [h₂]
          ring
    _ = _ := by rw [card_univ, Fintype.card_units]

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

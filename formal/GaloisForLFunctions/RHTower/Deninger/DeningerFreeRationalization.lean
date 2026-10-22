import GaloisForLFunctions.RHTower.Deninger.DeningerCCDivisible
import GaloisForLFunctions.RHTower.Deninger.DeningerCCHomology
import GaloisForLFunctions.RHTower.Deninger.DeningerFreeCyclicCentralizers
import GaloisForLFunctions.RHTower.Deninger.DeningerFreeHomology
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.SetTheory.Cardinal.Free

/-!
# The rationalization of a free group of finite rank

A free group of finite rank is countable, has unique roots and has cyclic centralizers, so it starts
a tower of root adjunctions along the fair schedule.  The colimit is a uniquely divisible torsion
free group whose homology with trivial coefficients vanishes in degree two and in every degree at
least three, the free group's own homology vanishing there.

* `deningerCCFreeStage` : the starting stage.
* `deningerFreeRationalization` : the colimit.
* `deningerFreeRationalization_uniqueRoots`, `_divisible`, `_torsionFree`, `_isZero_two`,
  `_isZero` : its four properties.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits Monoid

universe u

namespace RootAdjunction

/-- **The starting stage**: a free group of finite rank, with the chosen enumeration of its elements
and one of its generators as the distinguished element. -/
noncomputable def deningerCCFreeStage (α : Type u) [Nonempty α] : DeningerCCStage.{u} where
  carrier := FreeGroup α
  hist := fun p => deningerCCFresh (FreeGroup α) (Nat.unpair p).2
  witness := FreeGroup.of (Classical.arbitrary α)

/-- **The starting stage satisfies the invariant.** -/
theorem deningerCCFreeStage_good (α : Type u) [Nonempty α] [Countable α] :
    DeningerCCGood (deningerCCFreeStage α) := by
  haveI : Countable (FreeGroup α) := instCountableFreeGroup α
  refine ⟨fun x y n hn h => deningerFreeGroup_uniqueRoots α x y n hn h,
    deningerFreeGroup_cyclicCentralizers α, ?_, ?_, inferInstanceAs (Countable (FreeGroup α))⟩
  · exact FreeGroup.of_ne_one (Classical.arbitrary α)
  · intro w
    obtain ⟨i, hi⟩ := deningerCCFresh_surjective (FreeGroup α) w
    exact ⟨Nat.pair 0 i, by
      show deningerCCFresh (FreeGroup α) (Nat.unpair (Nat.pair 0 i)).2 = w
      rw [Nat.unpair_pair]
      exact hi⟩

/-- **The enumeration of the starting stage uses the first block of indices.** -/
theorem deningerCCFreeStage_hist_zero (α : Type u) [Nonempty α] [Countable α]
    (w : (deningerCCFreeStage α).carrier) :
    ∃ p : ℕ, (Nat.unpair p).1 = 0 ∧ (deningerCCFreeStage α).hist p = w := by
  haveI : Countable (FreeGroup α) := instCountableFreeGroup α
  obtain ⟨i, hi⟩ := deningerCCFresh_surjective (FreeGroup α) w
  refine ⟨Nat.pair 0 i, by rw [Nat.unpair_pair], ?_⟩
  show deningerCCFresh (FreeGroup α) (Nat.unpair (Nat.pair 0 i)).2 = w
  rw [Nat.unpair_pair]
  exact hi

/-- **The rationalization of a free group of finite rank.** -/
noncomputable def deningerFreeRationalization (α : Type u) [Nonempty α] : GrpCat.{u} :=
  deningerCCColimit (deningerCCFreeStage α) deningerCCSched

/-- **The rationalization has unique roots.** -/
theorem deningerFreeRationalization_uniqueRoots (α : Type u) [Nonempty α] [Countable α]
    (x y : deningerFreeRationalization α) (n : ℕ) (hn : 0 < n) (h : x ^ n = y ^ n) : x = y :=
  deningerCCColimit_uniqueRoots (deningerCCFreeStage α) deningerCCSched deningerCCSched_exp
    (deningerCCFreeStage_good α) x y n hn h

/-- **The rationalization is divisible.** -/
theorem deningerFreeRationalization_divisible (α : Type u) [Nonempty α] [Countable α]
    (x : deningerFreeRationalization α) (N : ℤ) (hN : N ≠ 0) :
    ∃ y : deningerFreeRationalization α, y ^ N = x :=
  deningerCCColimit_divisible (deningerCCFreeStage α) (deningerCCFreeStage_good α)
    (deningerCCFreeStage_hist_zero α) x N hN

/-- **The rationalization is torsion free.** -/
theorem deningerFreeRationalization_torsionFree (α : Type u) [Nonempty α] [Countable α]
    (x : deningerFreeRationalization α) (n : ℕ) (hn : 0 < n) (h : x ^ n = 1) : x = 1 :=
  deningerUniqueRoots_torsionFree (deningerFreeRationalization_uniqueRoots α) x n hn h

/-- **The homology of the rationalization vanishes in degree two.** -/
theorem deningerFreeRationalization_isZero_two (k : Type u) [Field k] [CharZero k] (α : Type u)
    [Nonempty α] [Finite α] :
    IsZero (groupHomology (Rep.trivial k (deningerFreeRationalization α) k) 2) := by
  haveI : Countable α := Finite.to_countable
  refine deningerCCColimit_isZero k (deningerCCFreeStage α) deningerCCSched deningerCCSched_exp
    (deningerCCFreeStage_good α) 1 ?_
  intro n
  exact deningerCCTower_isZero_two k (deningerCCFreeStage α) deningerCCSched deningerCCSched_exp
    (deningerCCFreeStage_good α) (deningerFreeGroup_isZero k α 0) n

/-- **The homology of the rationalization vanishes in every degree at least three.** -/
theorem deningerFreeRationalization_isZero (k : Type u) [CommRing k] (α : Type u)
    [Nonempty α] [Finite α] (j : ℕ) :
    IsZero (groupHomology (Rep.trivial k (deningerFreeRationalization α) k) (j + 3)) := by
  haveI : Countable α := Finite.to_countable
  refine deningerCCColimit_isZero k (deningerCCFreeStage α) deningerCCSched deningerCCSched_exp
    (deningerCCFreeStage_good α) (j + 2) ?_
  intro n
  exact deningerCCTower_isZero k (deningerCCFreeStage α) deningerCCSched deningerCCSched_exp
    (deningerCCFreeStage_good α) j (deningerFreeGroup_isZero k α (j + 1)) n

end RootAdjunction

end RHTower

import GaloisForLFunctions.RHTower.Deninger.DeningerCCDescent
import GaloisForLFunctions.RHTower.Deninger.DeningerFreeRationalization
import GaloisForLFunctions.RHTower.Deninger.DeningerBauVanishingCriterion
import GaloisForLFunctions.RHTower.Deninger.DeningerBaumslagGeneration
import GaloisForLFunctions.RHTower.Deninger.DeningerHomologyCohomology
import GaloisForLFunctions.RHTower.Deninger.DeningerBauTrivial

/-!
# The homology of the rationalization of a free group

The colimit of the tower is uniquely divisible and maps onto the rationalization of the free group:
the map exists because the colimit is built from the free group by adjoining roots, which the
rationalization has, and it is onto because its image is a root closed subgroup containing the image
of the free group.  The rationalization is therefore a retract of the colimit, and the vanishing of
homology transfers.

* `deningerFreeRationalization_uniquelyDivisible` : the colimit is uniquely divisible.
* `deningerBauFreeDesc` : the map onto the rationalization, and its surjectivity.
* `deningerBauFree_isZero_two`, `deningerBauFree_isZero` : the vanishing for the rationalization.
* `deningerBauFree_isZero_cohomology` : the same, cohomologically, over a field of characteristic
  zero, and for every rank including zero.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits Monoid

universe u

namespace RootAdjunction

/-- **The rationalization built by the tower is uniquely divisible.** -/
theorem deningerFreeRationalization_uniquelyDivisible (α : Type u) [Nonempty α] [Countable α] :
    DeningerUniquelyDivisible (deningerFreeRationalization α) := by
  intro n hn x
  obtain ⟨y, hy⟩ := deningerFreeRationalization_divisible α x (n : ℤ) (by
    exact_mod_cast hn.ne')
  have hy' : y ^ n = x := by rw [← zpow_natCast]; exact hy
  refine ⟨y, hy', fun z hz => ?_⟩
  exact deningerFreeRationalization_uniqueRoots α z y n hn (by rw [hz, hy'])

/-- **The map from the tower's colimit onto the rationalization of the free group.** -/
noncomputable def deningerBauFreeDesc (α : Type u) [Nonempty α] :
    deningerFreeRationalization α →* DeningerBau (FreeGroup α) :=
  deningerCCColimitDesc (deningerCCFreeStage α) deningerCCSched deningerCCSched_exp
    DeningerBau.uniquelyDivisible DeningerBau.of

/-- **The map onto the rationalization is onto.** -/
theorem deningerBauFreeDesc_surjective (α : Type u) [Nonempty α] [Countable α] :
    Function.Surjective (deningerBauFreeDesc α) := by
  have hK : (deningerBauFreeDesc α).range = ⊤ := by
    refine DeningerBau.eq_top_of_rootClosed (deningerBauFreeDesc α).range ?_ ?_
    · rintro n x ⟨g, rfl⟩
      obtain ⟨h, hh⟩ := deningerFreeRationalization_divisible α g ((n : ℤ) + 1) (by omega)
      have hh' : h ^ (n + 1) = g := by
        rw [← zpow_natCast]
        rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring]
        exact hh
      refine ⟨h, ?_⟩
      show deningerBauFreeDesc α h = DeningerBau.root n (deningerBauFreeDesc α g)
      obtain ⟨w, -, hw⟩ := DeningerBau.uniquelyDivisible (n + 1) n.succ_pos
        (deningerBauFreeDesc α g)
      rw [hw (deningerBauFreeDesc α h) (by
          show deningerBauFreeDesc α h ^ (n + 1) = deningerBauFreeDesc α g
          rw [← map_pow, hh']),
        hw (DeningerBau.root n (deningerBauFreeDesc α g)) (DeningerBau.root_pow n _)]
    · intro a
      refine ⟨deningerCCIota (deningerCCFreeStage α) deningerCCSched 0 a, ?_⟩
      show deningerCCColimitDesc (deningerCCFreeStage α) deningerCCSched deningerCCSched_exp
        DeningerBau.uniquelyDivisible DeningerBau.of
        (deningerCCIota (deningerCCFreeStage α) deningerCCSched 0 a) = DeningerBau.of a
      rw [deningerCCColimitDesc_iota]
      rfl
  intro y
  have hy : y ∈ (deningerBauFreeDesc α).range := by rw [hK]; trivial
  exact hy

/-- **The homology of the rationalization of a free group of finite rank vanishes in degree
two.** -/
theorem deningerBauFree_isZero_two (k : Type u) [Field k] [CharZero k] (α : Type u)
    [Nonempty α] [Finite α] :
    IsZero (groupHomology (Rep.trivial k (DeningerBau (FreeGroup α)) k) 2) := by
  haveI : Countable α := Finite.to_countable
  exact deningerBauFree_isZero_of_surjection k
    (deningerFreeRationalization_uniquelyDivisible α) (deningerBauFreeDesc α)
    (deningerBauFreeDesc_surjective α) 2 (deningerFreeRationalization_isZero_two k α)

/-- **The homology of the rationalization of a free group of finite rank vanishes in every degree
at least three.** -/
theorem deningerBauFree_isZero (k : Type u) [CommRing k] (α : Type u) [Nonempty α] [Finite α]
    (j : ℕ) :
    IsZero (groupHomology (Rep.trivial k (DeningerBau (FreeGroup α)) k) (j + 3)) := by
  haveI : Countable α := Finite.to_countable
  exact deningerBauFree_isZero_of_surjection k
    (deningerFreeRationalization_uniquelyDivisible α) (deningerBauFreeDesc α)
    (deningerBauFreeDesc_surjective α) (j + 3) (deningerFreeRationalization_isZero k α j)

/-- **The homology of the rationalization of a free group of finite rank vanishes in every degree at
least two**, including the rank zero case. -/
theorem deningerBauFree_isZero_succ_succ (k : Type u) [Field k] [CharZero k] (α : Type u)
    [Finite α] (j : ℕ) :
    IsZero (groupHomology (Rep.trivial k (DeningerBau (FreeGroup α)) k) (j + 2)) := by
  rcases isEmpty_or_nonempty α with hα | hα
  · exact deningerBauFree_isZero_of_isEmpty k (j + 1)
  · cases j with
    | zero => exact deningerBauFree_isZero_two k α
    | succ i => exact deningerBauFree_isZero k α i

/-- **The cohomology of the rationalization of a free group of finite rank vanishes in every degree
at least two.** -/
theorem deningerBauFree_isZero_cohomology (k : Type u) [Field k] [CharZero k] (α : Type u)
    [Finite α] (j : ℕ) :
    IsZero (groupCohomology (Rep.trivial k (DeningerBau (FreeGroup α)) k) (j + 2)) :=
  deningerIsZero_cohomology_of_homology k (DeningerBau (FreeGroup α)) (j + 1)
    (deningerBauFree_isZero_succ_succ k α j)

end RootAdjunction

end RHTower

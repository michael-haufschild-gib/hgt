import GaloisForLFunctions.HTGeometry.CriticalMonodromyJordan
import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination

/-!
# Primitivity of the unbalanced occupation-subset action

The pure critical labels are the `m`-element subsets of `Fin (m+n)`.  Permuting the roots therefore
acts faithfully on the critical occupation states.  When `m ≠ n`, mathlib's maximal-stabilizer
theorem makes this action primitive.  Consequently, any subgroup of the full permutation group on
the critical states that contains the entire root-permutation action is primitive; one additional
transposition then forces the full symmetric group.

The balanced case is deliberately excluded: complement pairs form the classical nontrivial block
system when `m = n`.  Closing balanced horizon monodromy still requires the geometric no-hidden-
block argument.
-/

namespace GaloisForLFunctions.HTGeometry

open Equiv MulAction Set
open scoped Pointwise

/-- Root permutations act on the critical `m`-subset labels. -/
instance criticalOccupationRootMulAction (m n : ℕ) :
    MulAction (Equiv.Perm (Fin (m + n)))
      (criticalHorizonOccupationStates m n) := by
  unfold criticalHorizonOccupationStates
  exact Set.powersetCard.instMulActionElemFinset (Equiv.Perm (Fin (m + n)))

/-- The permutation representation of root permutations on critical occupation states. -/
noncomputable def criticalOccupationRootAction (m n : ℕ) :
    Equiv.Perm (Fin (m + n)) →*
      Equiv.Perm (criticalHorizonOccupationStates m n) :=
  MulAction.toPermHom (Equiv.Perm (Fin (m + n)))
    (criticalHorizonOccupationStates m n)

/-- The root-permutation representation on nonempty proper subsets is faithful. -/
theorem criticalOccupationRootAction_injective {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Function.Injective (criticalOccupationRootAction m n) := by
  letI : FaithfulSMul (Equiv.Perm (Fin (m + n)))
      (criticalHorizonOccupationStates m n) := by
    unfold criticalHorizonOccupationStates
    apply Set.powersetCard.faithfulSMul
    · omega
    · rw [ENat.card_eq_coe_natCard, Nat.card_fin]
      exact_mod_cast (show m < m + n by omega)
  exact MulAction.toPerm_injective

/-- **Unbalanced subset primitivity.**  If both sides are positive and unequal, the natural
`S_(m+n)` action on the critical occupation states is primitive. -/
theorem criticalOccupationRootAction_isPreprimitive {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    MulAction.IsPreprimitive (Equiv.Perm (Fin (m + n)))
      (criticalHorizonOccupationStates m n) := by
  unfold criticalHorizonOccupationStates
  apply Set.powersetCard.isPreprimitive_perm
  · omega
  · simp only [Nat.card_fin]
    omega
  · simp only [Nat.card_fin]
    omega

/-- Any monodromy subgroup containing the full unbalanced root-permutation action is primitive. -/
theorem criticalMonodromy_isPreprimitive_of_rootAction_le {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n)
    (G : Subgroup (Equiv.Perm (criticalHorizonOccupationStates m n)))
    (hroot : ∀ σ, criticalOccupationRootAction m n σ ∈ G) :
    MulAction.IsPreprimitive G (criticalHorizonOccupationStates m n) := by
  have hprim : MulAction.IsPreprimitive (Equiv.Perm (Fin (m + n)))
      (criticalHorizonOccupationStates m n) :=
    criticalOccupationRootAction_isPreprimitive hm hn hmn
  letI : MulAction.IsPreprimitive (Equiv.Perm (Fin (m + n)))
      (criticalHorizonOccupationStates m n) := hprim
  have htrans : MulAction.IsPretransitive G
      (criticalHorizonOccupationStates m n) := by
    constructor
    intro S T
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq
      (Equiv.Perm (Fin (m + n))) S T
    exact ⟨⟨criticalOccupationRootAction m n σ, hroot σ⟩, hσ⟩
  letI : MulAction.IsPretransitive G
      (criticalHorizonOccupationStates m n) := htrans
  refine MulAction.IsPreprimitive.mk ?_
  intro B hB
  apply hprim.isTrivialBlock_of_isBlock
  rw [MulAction.isBlock_iff_smul_eq_or_disjoint]
  intro σ
  have hBG := hB.smul_eq_or_disjoint
    (⟨criticalOccupationRootAction m n σ, hroot σ⟩ : G)
  change (MulAction.toPerm σ) • B = B ∨ Disjoint ((MulAction.toPerm σ) • B) B
  exact hBG

/-- In the unbalanced case, root permutations plus one geometric transposition already give the
full symmetric group on all critical states. -/
theorem criticalMonodromy_eq_top_of_rootAction_of_isSwap {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n)
    (G : Subgroup (Equiv.Perm (criticalHorizonOccupationStates m n)))
    (hroot : ∀ σ, criticalOccupationRootAction m n σ ∈ G)
    (g : Equiv.Perm (criticalHorizonOccupationStates m n))
    (hswap : g.IsSwap) (hg : g ∈ G) :
    G = ⊤ :=
  monodromy_eq_top_of_isPreprimitive_of_isSwap G
    (criticalMonodromy_isPreprimitive_of_rootAction_le hm hn hmn G hroot)
    g hswap hg

end GaloisForLFunctions.HTGeometry

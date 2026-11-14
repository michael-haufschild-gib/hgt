import GaloisForLFunctions.HTGeometry.Buildings.BlockConfigurations
import GaloisForLFunctions.HTGeometry.Buildings.FlagIntervals

/-!
# Exact intersection tests for projective block covers

A line in a flag layer must lie in the upper subspace and escape the
lower one. Imposing further subspace constraints intersects the upper
subspace. Such a block is nonempty exactly when that intersection is
not contained in the lower stage.

Combining this incidence criterion with vertex insertion proves the
empty-or-acyclic intersection property for products of projective
simplices, the cover used in Ash--Gunnells, arXiv:2611.03303, Lemma 3.1.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial

universe v u

variable {K V ι κ : Type u} [Field K] [AddCommGroup V] [Module K V]

/-- Lines belonging to the block between two flag stages. -/
def flagBlockLines (A B : Submodule K V) : Set (Submodule K V) :=
  {L | IsAtom L ∧ L ≤ B ∧ ¬ L ≤ A}

/-- A block has a projective vertex precisely when its upper stage escapes its lower stage. -/
theorem flagBlockLines_nonempty_iff (A B : Submodule K V) :
    (flagBlockLines A B).Nonempty ↔ ¬ B ≤ A := by
  classical
  constructor
  · rintro ⟨L, _, hLB, hLA⟩ hBA
    exact hLA (hLB.trans hBA)
  · intro hBA
    by_contra hnone
    apply hBA
    refine le_iff_atom_le_imp.mpr ?_
    intro L hL hLB
    by_contra hLA
    exact hnone ⟨L, hL, hLB, hLA⟩

/-- Intersecting any family of linear incidence constraints only changes the upper stage. -/
theorem flagBlockLines_inter (A B : Submodule K V) (H : κ → Submodule K V) :
    {L ∈ flagBlockLines A B | ∀ j, L ≤ H j} = flagBlockLines A (B ⊓ iInf H) := by
  ext L
  constructor
  · rintro ⟨⟨hL, hLB, hLA⟩, hH⟩
    exact ⟨hL, le_inf hLB (le_iInf hH), hLA⟩
  · rintro ⟨hL, hLB, hLA⟩
    exact ⟨⟨hL, hLB.trans inf_le_left, hLA⟩,
      fun j => hLB.trans (inf_le_right.trans (iInf_le H j))⟩

/-- Every block must survive; this is an exact test, including empty or coincident layers. -/
theorem projectiveBlockConfigurations_nonempty_iff
    (A B : ι → Submodule K V) (H : κ → ι → Submodule K V) :
    Nonempty (blockConfigurations (fun i => flagBlockLines (A i) (B i ⊓ ⨅ j, H j i))) ↔
      ∀ i, ¬ B i ⊓ (⨅ j, H j i) ≤ A i := by
  rw [blockConfigurations_nonempty_iff]
  exact forall_congr' (fun i => flagBlockLines_nonempty_iff _ _)

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

/-- Every projective block-cover intersection has zero positive homology. -/
theorem isZero_projectiveBlockIntersection_homology
    (A B : ι → Submodule K V) (H : κ → ι → Submodule K V) (R : C) (n : ℕ) :
    IsZero ((nerve (blockConfigurations
      (fun i => flagBlockLines (A i) (B i ⊓ ⨅ j, H j i)))).homology R (n + 1)) :=
  isZero_blockConfigurations_homology _ R n

/-- Each intersection is empty or connected and acyclic; no incidence premise is needed. -/
theorem projectiveBlockIntersection_empty_or_connected
    (A B : ι → Submodule K V) (H : κ → ι → Submodule K V) :
    (∃ i, B i ⊓ (⨅ j, H j i) ≤ A i) ∨
      SSet.IsConnected (nerve (blockConfigurations
        (fun i => flagBlockLines (A i) (B i ⊓ ⨅ j, H j i)))) := by
  classical
  by_cases h : ∀ i, ¬ B i ⊓ (⨅ j, H j i) ≤ A i
  · haveI := (projectiveBlockConfigurations_nonempty_iff A B H).mpr h
    exact Or.inr (isConnected_blockConfigurations _)
  · exact Or.inl (not_forall.mp h |>.imp (fun _ hi => not_not.mp hi))

end GaloisForLFunctions.HTGeometry

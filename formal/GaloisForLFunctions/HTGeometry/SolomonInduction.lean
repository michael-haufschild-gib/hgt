import GaloisForLFunctions.HTGeometry.SolomonFrameRank

/-!
# Solomon's theorem by induction on the rank

The induction step carries generation by apartment classes from the family of buildings below the
coatoms to the family above.  Over a division ring the coatoms of the cover have dimension one less
than their component, and a subspace of dimension `r` has a frame indexed by any type with `r`
elements, so the step can be iterated: generation in the smallest rank propagates to every rank.

The smallest rank is the one the descent cannot reach, because there the connecting map lands in
degree zero, where the base and the pieces still have homology.  It is isolated here as the
hypothesis of the induction.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite Module

universe v u

section

variable {K V : Type u} [DivisionRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {C : Type u} [Category.{v} C] [Abelian C] [Limits.HasCoproducts.{u} C]

theorem card_univ_diff_singleton {ι : Type u} [Finite ι] (i₀ : ι) :
    Nat.card ↥(Set.univ \ {i₀} : Set ι) = Nat.card ι - 1 := by
  rw [Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ i₀), Set.ncard_univ]

/-- **Generation by apartment classes in the smallest rank**, the statement the induction starts
from: for a family of planes of a fixed vector space, the classes of the apartments of its frames
generate the first homology of the disjoint union of their buildings. -/
def SolomonBase (K V C : Type u) [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Category.{v} C] [Abelian C] [Limits.HasCoproducts.{u} C] : Prop :=
  ∀ (κ : Type u) (_ : Nonempty κ) (W : κ → Submodule K V) (ι : Type u) (_ : Finite ι)
    (_ : Nat.card ι = 0 + 3) (e₀ : Fin (0 + 3) ≃ ι) (_ : ∀ a, finrank K ↥(W a) = 0 + 3) (R : C),
    Epi (Limits.Sigma.desc (fun D : FrameDatum W ι =>
      apartmentClassIn e₀ (orderHomNerveMap D.vertices) R))

/-- **Solomon's theorem, by induction on the rank**: the apartment classes of the frames of the
components generate the homology of a disjoint union of buildings of subspaces of one dimension,
in the degree that dimension gives. -/
theorem epi_frameDatum_classes (hbase : SolomonBase.{v} K V C) (m : ℕ) :
    ∀ (κ : Type u) (_ : Nonempty κ) (W : κ → Submodule K V) (ι : Type u) (_ : Finite ι)
      (_ : Nat.card ι = m + 3) (e₀ : Fin (m + 3) ≃ ι) (_ : ∀ a, finrank K ↥(W a) = m + 3) (R : C),
      Epi (Limits.Sigma.desc (fun D : FrameDatum W ι =>
        apartmentClassIn e₀ (orderHomNerveMap D.vertices) R)) := by
  induction m with
  | zero => exact hbase
  | succ m ih =>
      intro κ hκ W ι hι hN e₀ hrank R
      classical
      haveI := hι
      haveI := hκ
      -- the atom of each component: the first vector of a chosen frame
      have hframe : ∀ a : κ, Nonempty (LatticeFrame (Submodule K V) ι (W a)) := fun a =>
        nonempty_frame_of_finrank (by rw [hN, hrank a])
      set p : κ → Submodule K V := fun a => (hframe a).some.atom (e₀ (Fin.last (m + 1 + 2)))
        with hpdef
      have hp : ∀ a, IsAtom (p a) := fun a => (hframe a).some.isAtom _
      have hpW : ∀ a, p a ≤ W a := fun a => (hframe a).some.atom_le_top _
      haveI : Nonempty (famCoverIndex W p) := by
        obtain ⟨a⟩ := hκ
        exact ⟨(⟨⟨a, (hframe a).some⟩, e₀ (Fin.last (m + 1 + 2)), rfl⟩ :
          PointedFrame W p ι).coverIndex hN⟩
      refine epi_frameDatum_classes_of_epi hN e₀ hp hpW R (by omega) ?_
      refine ih (famCoverIndex W p) inferInstance (fun c => famCoverTop c)
        ↥(Set.univ \ {e₀ (Fin.last (m + 1 + 2))} : Set ι) inferInstance ?_ _ ?_ R
      · rw [card_univ_diff_singleton, hN]
        omega
      · intro c
        have h := finrank_famCoverTop hp c
        rw [hrank (Subtype.val c).1] at h
        omega

end

end GaloisForLFunctions.HTGeometry

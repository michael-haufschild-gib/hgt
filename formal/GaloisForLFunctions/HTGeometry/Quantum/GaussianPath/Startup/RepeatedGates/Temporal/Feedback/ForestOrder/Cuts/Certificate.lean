import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.ForestOrder.Cuts.Rooting
import Mathlib.Data.Finset.Sum

/-! # One-way cuts of the input and output ports of a component -/
open Finset
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback.ForestOrder
variable {V : Type*} [DecidableEq V]
abbrev Port (V : Type*) := Sum V V

/-- Sources and sinks occupy different ports even when their wire agrees. -/
def ports (C : Finset V) := C.disjSum C

def NoExit (R : V→V→Prop) (C : Finset V) (S : Finset (Port V)) :=
  ∀ i∈C, ∀ j∈C, R i j → Sum.inl i∈S → Sum.inr j∈S

def NoEntry (R : V→V→Prop) (C : Finset V) (S : Finset (Port V)) :=
  ∀ i∈C, ∀ j∈C, R i j → Sum.inr j∈S → Sum.inl i∈S

/-- One of the two orientations certifies that i cannot signal to j. -/
def Separates (R : V→V→Prop) (C : Finset V) (S : Finset (Port V)) (i j : V) :=
  (Sum.inl i∈S ∧ Sum.inr j∉S ∧ NoExit R C S) ∨
    (Sum.inl i∉S ∧ Sum.inr j∈S ∧ NoEntry R C S)

def CutFamily (R : V→V→Prop) (C : Finset V) (F : Finset (Finset (Port V))) :=
  NestedFamily F ∧ (∀ S∈F, S⊆ports C) ∧
    ∀ i∈C, ∀ j∈C, ¬R i j → ∃ S∈F, Separates R C S i j

private theorem reverse_cut {R : V→V→Prop} {C : Finset V} {S : Finset (Port V)} {i j : V}
    (hi : i∈C) (hj : j∈C) (h : Separates R C S i j) : Separates R C (ports C\S) i j := by
  rcases h with ⟨hx,hy,he⟩|⟨hx,hy,he⟩
  · refine Or.inr ⟨fun h => (mem_sdiff.mp h).2 hx,mem_sdiff.mpr ⟨inr_mem_disjSum.mpr hj,hy⟩,?_⟩
    intro x hx y hy hxy hab
    exact mem_sdiff.mpr ⟨inl_mem_disjSum.mpr hx,fun h => (mem_sdiff.mp hab).2 (he x hx y hy hxy h)⟩
  · refine Or.inl ⟨mem_sdiff.mpr ⟨inl_mem_disjSum.mpr hi,hx⟩,fun h => (mem_sdiff.mp h).2 hy,?_⟩
    intro x hx y hy hxy hab
    exact mem_sdiff.mpr ⟨inr_mem_disjSum.mpr hy,fun h => (mem_sdiff.mp hab).2 (he x hx y hy hxy h)⟩

/-- All cuts may be oriented away from the next joining port at once.
Nestedness and the missing-input certificate are both preserved. -/
theorem root_cut_family {R : V→V→Prop} {C : Finset V} {F : Finset (Finset (Port V))}
    (hf : CutFamily R C F) (p : Port V) :
    let G := F.image (away (ports C) p)
    CutFamily R C G ∧ ∀ S∈G, p∉S := by
  intro G
  obtain ⟨hn,hs,hw⟩ := hf
  refine ⟨⟨away_nested hn _ p hs,?_,?_⟩,?_⟩
  · intro T ht
    obtain ⟨S,hS,rfl⟩ := mem_image.mp ht
    exact away_subset (hs S hS) p
  · intro i hi j hj hmiss
    obtain ⟨S,hS,hcut⟩ := hw i hi j hj hmiss
    refine ⟨_,mem_image_of_mem _ hS,?_⟩
    by_cases hp : p∈S
    · simpa only [away,if_pos hp] using reverse_cut hi hj hcut
    · simpa only [away,if_neg hp] using hcut
  · intro T ht
    obtain ⟨S,_,rfl⟩ := mem_image.mp ht
    exact notMem_away _ _ _

#print axioms root_cut_family
end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback.ForestOrder

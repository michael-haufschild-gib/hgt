import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset

/-!
# Finite ranks under adversarial erasure and replacement

For a finite population, the smallest peak left by r deletions is the
(r+1)-st reading in decreasing order. Its strict upper levels invert
the counting function exactly, including ties and exhausted ranks.
Changing q entries shifts every possible rank by at most q positions.
-/
namespace GaloisForLFunctions.FiniteRanks
open Finset

variable {ι α : Type*} [DecidableEq ι] [LinearOrder α] [OrderBot α]

/-- Smallest possible peak after deleting at most r observations.
The empty population has peak equal to the bottom value. -/
def erasedPeak (S : Finset ι) (v : ι → α) (r : ℕ) : α :=
  let choices := S.powerset.filter (fun D => D.card ≤ r)
  choices.inf' (show choices.Nonempty from ⟨∅, by simp [choices]⟩)
    (fun D => (S \ D).sup v)

/-- A threshold is exceeded at rank r precisely when more than r
observations strictly exceed it. -/
theorem lt_erasedPeak_iff (S : Finset ι) (v : ι → α) (r : ℕ) (y : α) :
    y < erasedPeak S v r ↔ r < (S.filter fun i => y < v i).card := by
  let H := S.filter fun i => y < v i
  unfold erasedPeak
  rw [Finset.lt_inf'_iff]
  constructor
  · intro h
    by_contra! hc
    have hH : H ∈ S.powerset.filter (fun D => D.card ≤ r) :=
      mem_filter.mpr ⟨mem_powerset.mpr (filter_subset _ _), hc⟩
    obtain ⟨i, hi, hiy⟩ := Finset.lt_sup_iff.mp (h H hH)
    exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨(mem_sdiff.mp hi).1, hiy⟩)
  · intro h D hD
    obtain ⟨i, hi, hkeep⟩ := exists_mem_notMem_of_card_lt_card ((mem_filter.mp hD).2.trans_lt h)
    exact Finset.lt_sup_iff.mpr ⟨i, mem_sdiff.mpr ⟨(mem_filter.mp hi).1, hkeep⟩, (mem_filter.mp hi).2⟩

/-- Changing q observations can move a reading upward by at most q
places in the ordering. Swapping the two populations gives the other side. -/
theorem replacement_interlacing (S : Finset ι) (v w : ι → α) (r q : ℕ)
    (hq : (S.filter fun i => v i ≠ w i).card ≤ q) :
    erasedPeak S v (r+q) ≤ erasedPeak S w r := by
  by_contra! h
  let y := erasedPeak S w r
  let V := S.filter fun i => y < v i
  let W := S.filter fun i => y < w i
  let D := S.filter fun i => v i ≠ w i
  have hv : r+q < V.card := (lt_erasedPeak_iff S v _ y).mp h
  have hw : W.card ≤ r := le_of_not_gt (fun hh => (lt_irrefl y) ((lt_erasedPeak_iff S w _ y).mpr hh))
  have hsub : V \ D ⊆ W := by
    intro i hi
    obtain ⟨hv,hd⟩ := mem_sdiff.mp hi
    obtain ⟨hs,hv⟩ := mem_filter.mp hv
    have he : v i = w i := by
      by_contra hn
      exact hd (mem_filter.mpr ⟨hs,hn⟩)
    exact mem_filter.mpr ⟨hs, he ▸ hv⟩
  exact (not_lt_of_ge ((card_le_card_sdiff_add_card (s:=V) (t:=D)).trans
    (Nat.add_le_add ((card_le_card hsub).trans hw) hq))) hv

#print axioms lt_erasedPeak_iff
#print axioms replacement_interlacing
end GaloisForLFunctions.FiniteRanks

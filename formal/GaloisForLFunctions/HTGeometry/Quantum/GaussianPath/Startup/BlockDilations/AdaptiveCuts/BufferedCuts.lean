import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.CutIntervals

/-! # One cut in every full buffer bounds every intervening packet -/

open Finset
namespace GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
noncomputable section
variable {n L : ℕ}

private abbrev Buffer (n L : ℕ) := Fin ((n+1)/L)

/-- Place a cut at the chosen offset in each complete buffer of L edges. -/
def bufferEdge (hL : 0<L) (p : Buffer n L→Fin L) (j : Buffer n L) : Fin (n+1) :=
  ⟨j.val*L+(p j).val, by
    have h := (Nat.le_div_iff_mul_le hL).mp (Nat.succ_le_of_lt j.isLt)
    rw [Nat.succ_mul] at h
    omega⟩

def bufferedCuts (hL : 0<L) (p : Buffer n L→Fin L) : Finset (Fin (n+1)) :=
  univ.image (bufferEdge hL p)

private theorem bufferEdge_bounds (hL : 0<L) (p : Buffer n L→Fin L) (j : Buffer n L) :
    j.val*L≤(bufferEdge hL p j).val ∧ (bufferEdge hL p j).val<(j.val+1)*L := by
  change j.val*L≤j.val*L+(p j).val ∧ j.val*L+(p j).val<(j.val+1)*L
  rw [Nat.add_mul,one_mul]
  exact ⟨Nat.le_add_right ..,Nat.add_lt_add_left (p j).isLt _⟩

theorem bufferedCuts_card (hL : 0<L) (p : Buffer n L→Fin L) :
    (bufferedCuts hL p).card=(n+1)/L := by
  have hlt {i j : Buffer n L} (h : i<j) : (bufferEdge hL p i).val<(bufferEdge hL p j).val :=
    (bufferEdge_bounds hL p i).2.trans_le ((Nat.mul_le_mul_right L (Nat.succ_le_of_lt h)).trans
      (bufferEdge_bounds hL p j).1)
  have hinj : Function.Injective (bufferEdge hL p) := by
    intro i j hij
    rcases lt_trichotomy i j with h|h|h
    · exact ((hlt h).ne (congrArg Fin.val hij)).elim
    · exact h
    · exact ((hlt h).ne (congrArg Fin.val hij.symm)).elim
  simp only [bufferedCuts,card_image_of_injective _ hinj,card_univ,Fintype.card_fin]

/-- This includes the two end packets and the possibly incomplete last buffer. -/
theorem buffered_packet_size (hL : 0<L) (p : Buffer n L→Fin L)
    (i : Fin ((bufferedCuts hL p).card+1)) :
    (sites (intervalOf (bufferedCuts hL p)) i).card≤2*L := by
  apply interval_size _ (by omega)
  intro v w hvw
  let k := v.val/L+1
  have hk : (k+1)*L≤w.val := calc
    _ = (v.val/L)*L+2*L := by dsimp only [k]; ring
    _ ≤ v.val+2*L := Nat.add_le_add_right (Nat.div_mul_le_self ..) _
    _ ≤ _ := hvw
  have hkb : k<(n+1)/L := (Nat.le_div_iff_mul_le hL).mpr (hk.trans (by omega : w.val≤n+1))
  let j : Buffer n L := ⟨k,hkb⟩
  have hv : v.val≤k*L := (Nat.lt_mul_div_succ v.val hL).le.trans_eq (Nat.mul_comm ..)
  exact ⟨bufferEdge hL p j,mem_image_of_mem _ (mem_univ _),
    hv.trans (bufferEdge_bounds hL p j).1,(bufferEdge_bounds hL p j).2.trans_le hk⟩

#print axioms bufferedCuts_card
#print axioms buffered_packet_size
end
end GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts

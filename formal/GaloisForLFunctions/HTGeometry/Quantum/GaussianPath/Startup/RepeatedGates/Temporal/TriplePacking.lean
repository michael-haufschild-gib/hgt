import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.ComponentCount
import Mathlib.Tactic

/-! # A positive density of excess gates for all distance-two exchanges -/
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal

/-- Every disjoint physical triple needs a marked endpoint. Adjacent
exchanges connect the whole path, leaving only the excess gates to mark wires. -/
theorem path_exchange_budget {N : ℕ} (w : List (Fin N×Fin N))
    (h : ∀ i j : Fin N, i.val ≤ j.val+2 → j.val ≤ i.val+2 → j∈inputs w i) :
    2*N+N/3 ≤ 2*(w.length+1) := by
  classical
  by_cases hN : N=0
  · simp [hN]
  let o : Fin N := ⟨0,by omega⟩
  have same (k : ℕ) (hk : k<N) : label w ⟨k,hk⟩=label w o := by
    induction k with
    | zero => rfl
    | succ k ih =>
      exact (label_of_input w (i:=⟨k,by omega⟩) (j:=⟨k+1,hk⟩) (h _ _ (by dsimp; omega) (by dsimp; omega))).trans (ih (by omega))
  have hp : parts w ⊆ {label w o} := by
    intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_singleton.mpr (same i i.isLt)
  have hcard := Finset.card_le_card hp
  rw [Finset.card_singleton] at hcard
  let blocks := (marked w).image (fun i => i.val/3)
  have hs : Finset.range (N/3) ⊆ blocks := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    let a : Fin N := ⟨3*k,by omega⟩
    let b : Fin N := ⟨3*k+1,by omega⟩
    let c : Fin N := ⟨3*k+2,by omega⟩
    have hab : a≠b := fun hh => by have := congrArg Fin.val hh; dsimp only [a,b] at this; omega
    have hac : a≠c := fun hh => by have := congrArg Fin.val hh; dsimp only [a,c] at this; omega
    have hbc : b≠c := fun hh => by have := congrArg Fin.val hh; dsimp only [b,c] at this; omega
    let S : Finset (Fin N) := {a,b,c}
    have hsize : 2<S.card := by simp [S,hab,hac,hbc]
    have bounds (i : Fin N) (hi : i∈S) : 3*k≤i.val ∧ i.val≤3*k+2 := by
      simp only [S,Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl|rfl <;> dsimp only [a,b,c] <;> omega
    obtain ⟨i,hi,hm⟩ := exchanging_meets_marked w S hsize (fun i hi j hj =>
      h i j (by have := bounds i hi; have := bounds j hj; omega) (by have := bounds i hi; have := bounds j hj; omega))
    exact Finset.mem_image.mpr ⟨i,hm,by have := bounds i hi; omega⟩
  have hc := (Finset.card_le_card hs).trans Finset.card_image_le
  rw [Finset.card_range] at hc
  have hm := mark_budget w
  rw [Fintype.card_fin] at hm
  omega

end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal

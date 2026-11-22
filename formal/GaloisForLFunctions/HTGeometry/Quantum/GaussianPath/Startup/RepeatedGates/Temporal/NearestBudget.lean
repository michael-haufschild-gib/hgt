import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.IntervalTests

/-! # Exact temporal gate lower bound for nearest-neighbor architectures -/
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal
variable {N : ℕ}

def Adjacent (e : Fin N×Fin N) : Prop := e.1.val+1=e.2.val ∨ e.2.val+1=e.1.val

private def group (e : Fin N×Fin N) := min e.1.val e.2.val / 2
private def bin (k : ℕ) (i : Fin N) : Fin 3 := ⟨min 2 (i.val-2*k),by omega⟩
private def tally (w : List (Fin N×Fin N)) (k : ℕ) := (w.filter (fun e => decide (group e=k))).length

private theorem crossed_iff (k : ℕ) (e : Fin N×Fin N) (he : Adjacent e) :
    bin k e.1≠bin k e.2 ↔ group e=k := by
  rw [←Fin.val_inj]
  dsimp only [bin,group,Adjacent] at *
  omega

private theorem tally_cons (e : Fin N×Fin N) (w : List (Fin N×Fin N)) (k : ℕ) :
    tally (e::w) k=tally w k+(if group e=k then 1 else 0) := by
  by_cases h : group e=k <;> simp [tally,h]

private theorem contract_length (w : List (Fin N×Fin N)) (hw : ∀ e∈w, Adjacent e) (k : ℕ) :
    (contract (bin k) w).length=tally w k := by
  induction w with
  | nil => rfl
  | cons e w ih =>
    have h := ih (fun _ he => hw _ (List.mem_cons_of_mem _ he))
    have he := crossed_iff k e (hw _ List.mem_cons_self)
    by_cases hb : bin k e.1=bin k e.2
    · rw [contract,if_pos hb,tally_cons,if_neg (fun h => he.mpr h hb),Nat.add_zero,h]
    · rw [contract,if_neg hb,List.length_cons,tally_cons,if_pos (he.mp hb),h]

private theorem tally_sum (w : List (Fin N×Fin N)) (m : ℕ) : (∑ k∈Finset.range m,tally w k)≤w.length := by
  induction w with
  | nil => simp [tally]
  | cons e w ih =>
    simp only [tally_cons,Finset.sum_add_distrib,Finset.sum_ite_eq, List.length_cons]
    split <;> omega

/-- Each pair of consecutive physical cuts must receive three distinct
calls. An unpaired final cut takes one more. -/
theorem nearest_exchange_budget (w : List (Fin N×Fin N)) (hw : ∀ e∈w, Adjacent e)
    (h : ∀ i j : Fin N, i.val ≤ j.val+2 → j.val ≤ i.val+2 → j∈inputs w i) :
    N-1+(N-1)/2 ≤ w.length := by
  let m := (N-1)/2
  have three (k : ℕ) (hk : k<m) : 3≤tally w k := by
    have hs : 2*k+2<N := by dsimp only [m] at hk; omega
    let v (j : Fin 3) : Fin N := ⟨2*k+j.val,by have := j.isLt; omega⟩
    have hv (i) : bin k (v i)=i := by apply Fin.ext; dsimp only [v,bin]; omega
    have hh (i j) : v j∈inputs w (v i) := h _ _ (by have := i.isLt; dsimp only [v]; omega) (by have := j.isLt; dsimp only [v]; omega)
    rw [←contract_length w hw k]
    exact three_bin_floor w (bin k) v hv hh
  have hm : 3*m≤∑ k∈Finset.range m,tally w k := by
    simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.mul_comm m 3] using
      Finset.sum_le_sum (s:=Finset.range m) (fun k hk => three k (Finset.mem_range.mp hk))
  by_cases hp : N-1=2*m
  · have hsize := hm.trans (tally_sum w m)
    omega
  · have hlast : 2*m+1<N := by dsimp only [m] at hp ⊢; omega
    let a : Fin N := ⟨2*m,by omega⟩
    let b : Fin N := ⟨2*m+1,hlast⟩
    have hh := contract_input (bin m) w (h a b (by dsimp only [a,b]; omega) (by dsimp only [a,b]; omega))
    have hpos : 0<tally w m := by
      by_contra! hz
      have he : (contract (bin m) w).length=0 := by rw [contract_length w hw m]; omega
      rw [List.length_eq_zero_iff.mp he,inputs,Finset.mem_singleton] at hh
      have hval := congrArg Fin.val hh
      dsimp only [a,b,bin] at hval; omega
    have hsize := tally_sum w (m+1)
    rw [Finset.sum_range_succ] at hsize
    dsimp only [m] at *
    omega

end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal

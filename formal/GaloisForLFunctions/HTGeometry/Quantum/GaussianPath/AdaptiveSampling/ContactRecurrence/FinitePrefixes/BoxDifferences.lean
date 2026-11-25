import GaloisForLFunctions.HTGeometry.SimultaneousDirichlet

/-! # Simultaneous Dirichlet approximation for every return index -/

open Finset
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.FinitePrefixes
noncomputable section

/-- Partition each coordinate separately. Subtracting the least
index in a most populated box gives distinct simultaneous returns. -/
theorem many_box_returns {I : Type*} [Fintype I] (β : I → ℝ) (Q : I → ℕ) (hQ : ∀ k, 0<Q k) (i : ℕ) :
    ∃ S : Finset ℕ, i<S.card ∧ ∀ j∈S, j≤(∏ k, Q k)*i ∧ ∀ k, latticeClose ((j:ℝ)*β k) (1/Q k) := by
  classical
  let box (j : ℕ) (k : I) : Fin (Q k) := ⟨boxIndex (Q k) ((j:ℝ)*β k),boxIndex_lt (hQ k) _⟩
  let U := range ((∏ k, Q k)*i+1)
  have hcard : (univ : Finset (∀ k, Fin (Q k))).card*i<U.card := by
    simp [U,Fintype.card_pi]
  obtain ⟨c,_,hc⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (f:=box) (fun j (_ : j∈U) => mem_univ (box j)) hcard
  let F := U.filter (fun j => box j=c)
  have hn : F.Nonempty := card_pos.mp ((Nat.zero_le i).trans_lt hc)
  let a := F.min' hn
  have ha : a∈F := min'_mem F hn
  have hle (j : ℕ) (hj : j∈F) : a≤j := min'_le F j hj
  have hinj : Set.InjOn (fun j : ℕ => j-a) F := by
    intro j hj l hl h
    have := hle j hj
    have := hle l hl
    dsimp only at h
    omega
  refine ⟨F.image (fun j => j-a),by rwa [card_image_of_injOn hinj],?_⟩
  intro n hn'
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hn'
  have hj' := mem_filter.mp hj
  have hra : j<(∏ k, Q k)*i+1 := mem_range.mp hj'.1
  refine ⟨(Nat.sub_le _ _).trans (Nat.le_of_lt_succ hra),fun k => ?_⟩
  have hh : boxIndex (Q k) ((j:ℝ)*β k)=boxIndex (Q k) ((a:ℝ)*β k) :=
    congrArg Fin.val (congrFun (hj'.2.trans (mem_filter.mp ha).2.symm) k)
  have hclose := abs_fract_sub_lt_of_boxIndex_eq (hQ k) hh
  refine ⟨⌊(j:ℝ)*β k⌋-⌊(a:ℝ)*β k⌋,?_⟩
  rw [Nat.cast_sub (hle j hj),Int.cast_sub]
  simp only [Int.fract] at hclose
  convert hclose using 2
  ring

/-- With a common subdivision Q, the ith return is available by
index i Q^d, counting the origin as the zeroth return. -/
theorem many_dirichlet_returns {d : ℕ} (β : Fin d → ℝ) {Q : ℕ} (hQ : 0<Q) (i : ℕ) :
    ∃ S : Finset ℕ, i<S.card ∧ ∀ j∈S, j≤Q^d*i ∧ ∀ k, latticeClose ((j:ℝ)*β k) (1/Q) := by
  simpa only [prod_const,card_univ,Fintype.card_fin] using many_box_returns β (fun _ => Q) (fun _ => hQ) i

#print axioms many_dirichlet_returns
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.FinitePrefixes

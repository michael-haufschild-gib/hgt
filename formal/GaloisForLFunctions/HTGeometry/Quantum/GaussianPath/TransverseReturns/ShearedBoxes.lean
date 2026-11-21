import GaloisForLFunctions.HTGeometry.SimultaneousDirichlet

/-! # Simultaneous recurrence with short transverse phase corrections -/
namespace GaloisForLFunctions.HTGeometry.TransverseReturns
noncomputable section

private def bin {m : ℕ} (hm : 0 < m) (x : ℝ) : Fin m := ⟨boxIndex m x,boxIndex_lt hm x⟩

/-- Coarse cells on the transverse coordinates and fine cells after
subtracting their lifted shear save one factor of m per transverse
direction compared with ordinary simultaneous approximation at m⁻². -/
theorem sheared_dirichlet {I K : Type*} [Fintype I] [Fintype K]
    (v : K → ℝ) (w : I → ℝ) (c : I → K → ℝ) {m : ℕ} (hm : 0 < m) :
    ∃ q : ℕ, 0 < q ∧ q ≤ m^(Fintype.card K)*(m^2)^(Fintype.card I) ∧
      ∃ d : K → ℝ, (∀ j, |d j| < 1/(m:ℝ) ∧ ∃ z : ℤ, (q:ℝ)*v j-d j=z) ∧
        ∀ i, latticeClose ((q:ℝ)*w i-∑ j, c i j*d j) (1/(m:ℝ)^2) := by
  classical
  let L := m^(Fintype.card K)*(m^2)^(Fintype.card I)
  let x (k : ℕ) (j : K) := Int.fract ((k:ℝ)*v j)
  let y (k : ℕ) (i : I) := (k:ℝ)*w i-∑ j, c i j*x k j
  have h2 : 0 < m^2 := pow_pos hm _
  let f (k : Fin (L+1)) : (K → Fin m)×(I → Fin (m^2)) :=
    (fun j => bin hm ((k.val:ℝ)*v j),fun i => bin h2 (y k i))
  have hcard : Fintype.card ((K → Fin m)×(I → Fin (m^2))) < Fintype.card (Fin (L+1)) := by simp [L]
  obtain ⟨a,b,hab,he⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have ordered : ∃ k l : Fin (L+1), k<l ∧ f k=f l := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨a,b,h,he⟩
    · exact ⟨b,a,h,he.symm⟩
  obtain ⟨k,l,hkl,hf⟩ := ordered
  let q := l.val-k.val
  let d (j : K) := x l j-x k j
  have hq : (q:ℝ)=(l.val:ℝ)-k.val := Nat.cast_sub hkl.le
  refine ⟨q,Nat.sub_pos_of_lt hkl,(Nat.sub_le _ _).trans (Nat.lt_succ_iff.mp l.isLt),d,?_,?_⟩
  · intro j
    have hbin := congrArg Fin.val (congrFun (congrArg Prod.fst hf.symm) j)
    refine ⟨abs_fract_sub_lt_of_boxIndex_eq hm hbin,⌊(l.val:ℝ)*v j⌋-⌊(k.val:ℝ)*v j⌋,?_⟩
    dsimp only [d,x,Int.fract]
    rw [hq,Int.cast_sub]
    ring
  · intro i
    have hbin := congrArg Fin.val (congrFun (congrArg Prod.snd hf.symm) i)
    have hclose := abs_fract_sub_lt_of_boxIndex_eq h2 hbin
    refine ⟨⌊y l i⌋-⌊y k i⌋,?_⟩
    have hd : (q:ℝ)*w i-∑ j, c i j*d j = y l i-y k i := by
      dsimp only [y,d]
      simp only [mul_sub,Finset.sum_sub_distrib,hq,sub_mul]
      ring
    rw [hd,Int.cast_sub,show y l i-y k i-(↑⌊y l i⌋-↑⌊y k i⌋) = Int.fract (y l i)-Int.fract (y k i) by
      unfold Int.fract; ring]
    simpa only [Nat.cast_pow] using hclose

#print axioms sheared_dirichlet
end
end GaloisForLFunctions.HTGeometry.TransverseReturns

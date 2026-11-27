import GaloisForLFunctions.HTGeometry.SimultaneousDirichlet

/-! # Independent resolutions for spectral controls and residual phases -/
namespace GaloisForLFunctions.HTGeometry.TransverseReturns
noncomputable section

private def bin {m : ℕ} (hm : 0 < m) (x : ℝ) : Fin m := ⟨boxIndex m x,boxIndex_lt hm x⟩

/-- Pigeonholing coarse control coordinates and fine residual coordinates
at independent resolutions costs precisely the product of their cell counts. -/
theorem two_scale_clock {I K : Type*} [Fintype I] [Fintype K]
    (v : K → ℝ) (w : I → ℝ) (c : I → K → ℝ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ∃ q : ℕ, 0 < q ∧ q ≤ m^(Fintype.card K)*n^(Fintype.card I) ∧
      ∃ d : K → ℝ, (∀ j, |d j| < 1/(m:ℝ) ∧ ∃ z : ℤ, (q:ℝ)*v j-d j=z) ∧
        ∀ i, latticeClose ((q:ℝ)*w i-∑ j, c i j*d j) (1/(n:ℝ)) := by
  classical
  let L := m^(Fintype.card K)*n^(Fintype.card I)
  let x (k : ℕ) (j : K) := Int.fract ((k:ℝ)*v j)
  let y (k : ℕ) (i : I) := (k:ℝ)*w i-∑ j, c i j*x k j
  let f (k : Fin (L+1)) : (K → Fin m)×(I → Fin n) :=
    (fun j => bin hm ((k.val:ℝ)*v j),fun i => bin hn (y k i))
  have hcard : Fintype.card ((K → Fin m)×(I → Fin n)) < Fintype.card (Fin (L+1)) := by simp [L]
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
    have hbin : boxIndex m ((l.val:ℝ)*v j)=boxIndex m ((k.val:ℝ)*v j) :=
      congrArg Fin.val (congrFun (congrArg Prod.fst hf.symm) j)
    refine ⟨abs_fract_sub_lt_of_boxIndex_eq hm hbin,⌊(l.val:ℝ)*v j⌋-⌊(k.val:ℝ)*v j⌋,?_⟩
    dsimp only [d,x,Int.fract]
    rw [hq,Int.cast_sub]
    ring
  · intro i
    have hbin : boxIndex n (y l i)=boxIndex n (y k i) :=
      congrArg Fin.val (congrFun (congrArg Prod.snd hf.symm) i)
    have hclose := abs_fract_sub_lt_of_boxIndex_eq hn hbin
    refine ⟨⌊y l i⌋-⌊y k i⌋,?_⟩
    have hd : (q:ℝ)*w i-∑ j, c i j*d j = y l i-y k i := by
      dsimp only [y,d]
      simp only [mul_sub,Finset.sum_sub_distrib,hq,sub_mul]
      ring
    rw [hd,Int.cast_sub,show y l i-y k i-(↑⌊y l i⌋-↑⌊y k i⌋) = Int.fract (y l i)-Int.fract (y k i) by
      unfold Int.fract; ring]
    exact hclose

#print axioms two_scale_clock
end
end GaloisForLFunctions.HTGeometry.TransverseReturns

import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.TransverseReturns.PolynomialControls.TwoScales

/-! # Clocks with several independently adjustable spectral coordinates -/
open Finset
namespace GaloisForLFunctions.HTGeometry.TransverseReturns
noncomputable section

/-- The two anchors wind integrally on every tick. Independently adjusting
the coordinates in S leaves only D−2−|S| residual coordinates to resolve
at the fine precision. -/
theorem pinned_coordinates {I : Type*} [Fintype I] [DecidableEq I]
    (S : Finset I) (a b : I) (hab : a≠b) (ha : a∉S) (hb : b∉S)
    (X : I → ℝ) (xa xb : ℤ) (hxa : X a=xa) (hxb : X b=xb)
    (G : S → I → ℝ) (hga : ∀ j, G j a=0) (hgb : ∀ j, G j b=0)
    (hg : ∀ j i : S, G j i=if j=i then 1 else 0)
    {m n : ℕ} (hm : 0<m) (hn : 0<n) :
    ∃ q : ℕ, 0<q ∧ q≤m^S.card*n^(Fintype.card I-2-S.card) ∧
      ∃ d : S → ℝ, (∀ j, |d j|<1/(m:ℝ)) ∧
        ∀ i, latticeClose ((q:ℝ)*X i-∑ j:S, G j i*d j) (1/(n:ℝ)) := by
  classical
  let A := (univ.erase a).erase b
  let R := A \ S
  have hsub : S⊆A := by
    intro i hi
    exact mem_erase.mpr ⟨fun h => hb (h ▸ hi),mem_erase.mpr ⟨fun h => ha (h ▸ hi),mem_univ _⟩⟩
  have hdim : Fintype.card R=Fintype.card I-2-S.card := by
    rw [Fintype.card_coe,show R=A \ S from rfl,card_sdiff_of_subset hsub,
      show A=(univ.erase a).erase b from rfl,card_erase_of_mem (mem_erase.mpr ⟨hab.symm,mem_univ _⟩),
      card_erase_of_mem (mem_univ a),card_univ]
    omega
  obtain ⟨q,hq,hbound,d,hd,hr⟩ := two_scale_clock (fun j : S => X j) (fun i : R => X i)
    (fun i j => G j i) hm hn
  refine ⟨q,hq,by simpa only [Fintype.card_coe S,hdim] using hbound,d,fun j => (hd j).1,?_⟩
  intro i
  have hpos : 0<1/(n:ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hn)
  have anchor (z : ℤ) (hx : X i=z) (hzero : ∀ j, G j i=0) :
      latticeClose ((q:ℝ)*X i-∑ j:S, G j i*d j) (1/(n:ℝ)) := by
    refine ⟨(q:ℤ)*z,?_⟩
    simpa only [hx,hzero,zero_mul,sum_const_zero,sub_zero,Int.cast_mul,Int.cast_natCast,sub_self,
      abs_zero] using hpos
  by_cases hia : i=a
  · subst i; exact anchor xa hxa hga
  by_cases hib : i=b
  · subst i; exact anchor xb hxb hgb
  by_cases hi : i∈S
  · let k : S := ⟨i,hi⟩
    obtain ⟨z,hz⟩ := (hd k).2
    have hsum : (∑ j:S, G j i*d j)=d k := by
      change (∑ j:S, G j k*d j)=d k
      simp [hg,ite_mul]
    refine ⟨z,?_⟩
    simpa only [hsum,show (q:ℝ)*X i-d k=z from hz,sub_self,abs_zero] using hpos
  · let k : R := ⟨i,mem_sdiff.mpr ⟨mem_erase.mpr ⟨hib,mem_erase.mpr ⟨hia,mem_univ _⟩⟩,hi⟩⟩
    exact hr k

#print axioms pinned_coordinates
end
end GaloisForLFunctions.HTGeometry.TransverseReturns

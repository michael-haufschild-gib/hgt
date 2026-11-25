import GaloisForLFunctions.HTGeometry.SimultaneousDirichlet

/-! # A simultaneous Dirichlet deadline on an integral affine hyperplane -/

open Finset
namespace GaloisForLFunctions.HTGeometry.ResonantReturns
noncomputable section

/-- One integer relation removes a coordinate from the Dirichlet
deadline. Clearing a nonzero pivot recovers its approximation with
constants independent of the subdivision parameter. -/
theorem integer_row_deadline {d : ℕ} (β : Fin (d+1) → ℝ) (m : Fin (d+1) → ℤ) (hm : m≠0)
    (z : ℤ) (hz : ∑ i, (m i:ℝ)*β i=z) :
    ∃ L : ℕ, 0 < L ∧ ∃ K > (0:ℝ), ∀ Q : ℕ, 0 < Q →
      ∃ n : ℕ, 1 ≤ n ∧ n ≤ L*Q^d ∧ ∀ i, latticeClose ((n:ℝ)*β i) (K/Q) := by
  classical
  obtain ⟨p,hp⟩ : ∃ i, m i≠0 := by
    by_contra! h
    exact hm (funext h)
  let a := m p
  let L := a.natAbs*a.natAbs
  have hL : 0 < L := Nat.mul_pos (Int.natAbs_pos.mpr hp) (Int.natAbs_pos.mpr hp)
  have hsq : (L:ℝ)=(a:ℝ)*a := by exact_mod_cast (Int.natAbs_mul_self (a:=a))
  let w (i : Fin d) := m (p.succAbove i)
  let γ (i : Fin d) := β (p.succAbove i)
  let S := ∑ i, |(w i:ℝ)|
  have hS : 0 ≤ S := sum_nonneg fun _ _ => abs_nonneg _
  let K := (L:ℝ)+|(a:ℝ)|*S+1
  have hrad : 0 ≤ |(a:ℝ)|*S := mul_nonneg (abs_nonneg _) hS
  have hLK : (L:ℝ) < K := by dsimp only [K]; linarith only [hrad]
  have hAK : |(a:ℝ)|*S < K := by dsimp only [K]; linarith only [Nat.cast_nonneg (α:=ℝ) L]
  refine ⟨L,hL,K,(Nat.cast_nonneg L).trans_lt hLK,?_⟩
  intro Q hQ
  have hQr : 0 < (Q:ℝ) := Nat.cast_pos.mpr hQ
  obtain ⟨q,hq,hbound,hclose⟩ := exists_simultaneous_dirichlet γ hQ
  choose n hn using hclose
  have hs : (a:ℝ)*β p+∑ i, (w i:ℝ)*γ i=z := (Fin.sum_univ_succAbove _ p).symm.trans hz
  have he : ∑ i, (w i:ℝ)*((q:ℝ)*γ i-n i)=(q:ℝ)*(∑ i, (w i:ℝ)*γ i)-(∑ i, w i*n i:ℤ) := by
    push_cast
    simp only [mul_sub,sum_sub_distrib,mul_sum]
    congr 1
    exact sum_congr rfl fun _ _ => by ring
  have herr : |∑ i, (w i:ℝ)*((q:ℝ)*γ i-n i)| ≤ S/Q := calc
    _ ≤ ∑ i, |(w i:ℝ)*((q:ℝ)*γ i-n i)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |(w i:ℝ)|*(1/(Q:ℝ)) := sum_le_sum fun i _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hn i).le (abs_nonneg _)
    _ = _ := by rw [←sum_mul,mul_one_div]
  refine ⟨q*L,Nat.mul_pos hq hL,by rw [mul_comm q L]; exact Nat.mul_le_mul_left L hbound,?_⟩
  intro j
  refine Fin.succAboveCases p ?_ (fun i => ?_) j
  · refine ⟨(q:ℤ)*a*z-a*∑ i, w i*n i,?_⟩
    have hid : ((q*L:ℕ):ℝ)*β p-(((q:ℤ)*a*z-a*∑ i, w i*n i:ℤ):ℝ)=
        -(a:ℝ)*∑ i, (w i:ℝ)*((q:ℝ)*γ i-n i) := by
      rw [he]
      push_cast
      rw [hsq]
      linear_combination ((q:ℝ)*(a:ℝ))*hs
    rw [hid,abs_mul,abs_neg]
    exact (mul_le_mul_of_nonneg_left herr (abs_nonneg _)).trans_lt
      (by rw [←mul_div_assoc]; exact div_lt_div_of_pos_right hAK hQr)
  · refine ⟨(L:ℤ)*n i,?_⟩
    have hid : ((q*L:ℕ):ℝ)*β (p.succAbove i)-(((L:ℤ)*n i:ℤ):ℝ)=
        (L:ℝ)*((q:ℝ)*γ i-n i) := by dsimp only [γ]; push_cast; ring
    rw [hid,abs_mul,abs_of_nonneg (Nat.cast_nonneg L)]
    exact (mul_le_mul_of_nonneg_left (hn i).le (Nat.cast_nonneg L)).trans_lt
      (by rw [mul_one_div]; exact div_lt_div_of_pos_right hLK hQr)

#print axioms integer_row_deadline
end
end GaloisForLFunctions.HTGeometry.ResonantReturns

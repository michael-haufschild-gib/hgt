import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.FirstResidues

/-! # Choosing a time stride before a first return -/

open Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding
open SharpOccupation EmptyVisitFlux
noncomputable section

private theorem dilated_residues {I : Type*} [Fintype I] (z : I → ℤ) (p d : ℕ) :
    (residues (fun i => (p:ℤ)*z i) d).card ≤ (residues z d).card := by
  classical
  let f := fun x : ℤ => ((p:ℤ)*x) % (d:ℤ)
  apply (Finset.card_le_card (t:=(residues z d).image f) ?_).trans Finset.card_image_le
  intro x hx
  obtain ⟨hx,hmem⟩ := Finset.mem_erase.mp hx
  obtain ⟨i,_,hix⟩ := Finset.mem_image.mp hmem
  let y := z i % (d:ℤ)
  have he : f y = x := by
    change ((p:ℤ)*(z i % (d:ℤ))) % (d:ℤ)=x
    rw [Int.mul_emod,Int.emod_emod,←Int.mul_emod]
    exact hix
  have hy : y ≠ 0 := by
    intro h
    rw [h] at he
    exact hx (by simpa only [f,mul_zero,Int.zero_emod] using he.symm)
  exact Finset.mem_image.mpr ⟨y,Finset.mem_erase.mpr
    ⟨hy,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩,he⟩

/-- Multiplying the time tick by p cannot increase the number of residues
that must be rounded, even if d has no small divisors. -/
theorem stride_visit {I : Type*} [Fintype I] [Nonempty I] {w : I → ℝ} {t R : ℝ}
    {b z} (hz : Anchored w t R b z) (p : ℕ) {d Q : ℕ} (hd : 0 < d) (hQ : 0 < Q) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ Q^(residues z d).card ∧
      ∃ b' y, Anchored w (((p*j:ℕ):ℝ)/d*t) (2/Q+((p*j:ℕ):ℝ)/d*R) b' y := by
  have ha : Anchored w ((p:ℝ)*t) ((p:ℝ)*R) b (fun i => (p:ℤ)*z i) := by
    intro i
    rw [Int.cast_mul,Int.cast_natCast,show (p:ℝ)*t*(w i-w b)-p*(z i:ℝ)=p*(t*(w i-w b)-(z i:ℝ)) by ring]
    exact ⟨mul_nonneg (Nat.cast_nonneg p) (hz i).1,
      mul_le_mul_of_nonneg_left (hz i).2 (Nat.cast_nonneg p)⟩
  obtain ⟨j,hj,hJ,b',y,hy⟩ := compressed_visit ha hd hQ
  refine ⟨j,hj,hJ.trans (Nat.pow_le_pow_right hQ (dilated_residues z p d)),b',y,?_⟩
  rw [Nat.cast_mul,show (p:ℝ)*j/d*t=(j:ℝ)/d*(p*t) by ring,
    show (p:ℝ)*j/d*R=(j:ℝ)/d*(p*R) by ring]
  exact hy

/-- Once the date itself allows the search, every sufficiently large
modulus needs at least m+1 different nonzero winding residues.
There is no upper cutoff on d. -/
theorem large_modulus_count {N s K d Q m : ℕ} (H : selfAdjoint (Register N)) {a ε t R : ℝ}
    (ha : 0 < a) (hε : ε ∈ Ioo (0:ℝ) (sqrt 2)) (hK : 1 < K) (hQ : 0 < Q)
    (hgrid : 4/(Q:ℝ) ≤ physicalArc ε) (hR : 0 ≤ R) (hRK : R ≤ (K:ℝ)*(physicalArc ε/2))
    (hd : K*Q^m ≤ d) (hdate : a*((2*(K*Q^m):ℕ):ℝ) ≤ t) (ht : t ≤ firstVisit H a s ε)
    {b z} (hz : Anchored (fun i => -H.2.isHermitian.eigenvalues i/(2*π)) t R b z) :
    m < (residues z d).card := by
  by_contra! hn
  let M := Q^m
  let L := K*M
  let p := d/L
  have hM : 0 < M := pow_pos hQ _
  have hK₀ : 0 < K := by omega
  have hL : 0 < L := Nat.mul_pos hK₀ hM
  have hp : 0 < p := (Nat.div_pos hd hL)
  have hpd : p*L ≤ d := Nat.div_mul_le_self ..
  have hdp : d ≤ p*(2*L) := by
    have h := Nat.mod_add_div d L
    have h' := Nat.mod_lt d hL
    have h'' := Nat.le_mul_of_pos_left L hp
    change L ≤ p*L at h''
    rw [Nat.mul_comm L] at h
    change d%L+p*L=d at h
    rw [show p*(2*L)=p*L+p*L by ring]
    omega
  have hd₀ : 0 < d := hL.trans_le hd
  obtain ⟨j,hj,hJ,b',y,hy⟩ := stride_visit hz p hd₀ hQ
  let f := ((p*j:ℕ):ℝ)/d
  have hjM : j ≤ M := hJ.trans (Nat.pow_le_pow_right hQ hn)
  have hmul : K*(p*j) ≤ d := by
    apply le_trans _ hpd
    change K*(p*j) ≤ p*(K*M)
    rw [←Nat.mul_assoc, Nat.mul_comm K p, Nat.mul_assoc]
    exact Nat.mul_le_mul_left p (Nat.mul_le_mul_left K hjM)
  have hd' := Nat.cast_pos (α:=ℝ).mpr hd₀
  have hK' := Nat.cast_pos (α:=ℝ).mpr hK₀
  have hf : f ≤ 1/(K:ℝ) := by
    apply (div_le_div_iff₀ hd' hK').mpr
    rw [one_mul,mul_comm]
    exact_mod_cast hmul
  have hf' : f < 1 := hf.trans_lt ((div_lt_one hK').mpr (by exact_mod_cast hK))
  have ht₀ : 0 < t := (mul_pos ha (Nat.cast_pos.mpr (Nat.mul_pos (by norm_num) hL))).trans_le hdate
  have horigin : a ≤ f*t := by
    have hl : a*(d:ℝ) ≤ ((p*j:ℕ):ℝ)*t := calc
      _ ≤ a*((p*(2*L):ℕ):ℝ) := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hdp) ha.le
      _ = (p:ℝ)*(a*((2*L:ℕ):ℝ)) := by rw [Nat.cast_mul]; ring
      _ ≤ (p:ℝ)*t := mul_le_mul_of_nonneg_left hdate (Nat.cast_nonneg _)
      _ ≤ ((p*j:ℕ):ℝ)*t := mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (Nat.le_mul_of_pos_right p (by omega))) ht₀.le
    have hh := (le_div_iff₀ hd').mpr hl
    exact hh.trans_eq (by dsimp only [f]; ring)
  have hlim := mul_le_mul hf hRK hR (one_div_nonneg.mpr hK'.le)
  rw [show 1/(K:ℝ)*((K:ℝ)*(physicalArc ε/2))=physicalArc ε/2 by field_simp] at hlim
  rw [show (4:ℝ)/Q=2*(2/Q) by ring] at hgrid
  have hwidth : 2/(Q:ℝ)+f*R ≤ physicalArc ε := by linarith only [hgrid,hlim]
  have hh := (anchored_iff (physicalArc_spec hε.1 hε.2).1.1.le).mpr
    ⟨b',y,fun i => ⟨(hy i).1,(hy i).2.trans hwidth⟩⟩
  obtain ⟨c,hc,C,hC,he⟩ := (physical_visit H hε.1 hε.2 (f*t)).mp hh
  have hfirst := (firstVisit_isLeast H a s hε.1).2
    (show f*t ∈ PrecisionReturns.visitSet H a s ε from ⟨horigin,c,hc,C,hC.trans (Nat.zero_le s),he⟩)
  exact (mul_lt_of_lt_one_left ht₀ hf').not_ge (ht.trans hfirst)

#print axioms stride_visit
#print axioms large_modulus_count
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding

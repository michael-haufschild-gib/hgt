import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ClockSpectrum.DirichletMultiples

/-! # A rational pair removes a coordinate from the scalar return deadline -/

open Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ResonantReturns
noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Approximating every anchored gap in turns gives an empty circuit in
operator norm. -/
theorem empty_of_anchored_gaps {n : ℕ} (H : selfAdjoint (Reg n)) (a : Fin n → Bool)
    (t : ℝ) {r : ℝ} (hr : 0≤r) (h : ∀ i, latticeClose
      (t*(H.2.isHermitian.eigenvalues i-H.2.isHermitian.eigenvalues a)/(2*π)) r) :
    HasProjectiveCircuitApproximation n (2*π*r) 0 (unitaryEvolution H.val t) := by
  let E := H.2.isHermitian.eigenvalues
  refine ⟨anchorPhase E a t,by simp [anchorPhase,Complex.norm_exp],TwoQubitCircuit.one n,le_rfl,?_⟩
  rw [TwoQubitCircuit.one_eval]
  change ‖unitaryEvolution H.val t-anchorPhase E a t • (1:Reg n)‖ ≤ _
  rw [l2_opNorm_unitaryEvolution_sub_anchorPhase H.2.isHermitian a t]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0≤2*π*r)).mpr
  intro i
  simpa only [Complex.ofReal_mul,Complex.ofReal_sub] using
    phase_chord_of_turn_error (t*(E i-E a)) (h i)

/-- If two eigenphases agree after L clock ticks, one of the first
L Q^(D−2) positive ticks fits the empty circuit at error 2π/Q. -/
theorem rational_pair_deadline {n : ℕ} (H : selfAdjoint (Reg n)) (τ : ℝ)
    (a b : Fin n → Bool) (hab : a≠b) {L : ℕ} (hL : 0<L) (z : ℤ)
    (hz : (L:ℝ)*τ*(H.2.isHermitian.eigenvalues b-H.2.isHermitian.eigenvalues a)/(2*π)=z)
    {Q : ℕ} (hQ : 0<Q) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ L*Q^(2^n-2) ∧
      HasProjectiveCircuitApproximation n (2*π/(Q:ℝ)) 0 (unitaryEvolution H.val ((m:ℝ)*τ)) := by
  classical
  let E := H.2.isHermitian.eigenvalues
  let S := (univ.erase a).erase b
  have hsize : S.card=2^n-2 := by
    simp only [S,card_erase_of_mem (mem_erase.mpr ⟨hab.symm,mem_univ _⟩),
      card_erase_of_mem (mem_univ a),card_univ,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
    omega
  let e := Fintype.equivFin ↥S
  let β (i : Fin (Fintype.card ↥S)) := (L:ℝ)*τ*(E (e.symm i).val-E a)/(2*π)
  obtain ⟨q,hq,hbound,hclose⟩ := exists_simultaneous_dirichlet β hQ
  have hdim : Fintype.card ↥S=2^n-2 := (Fintype.card_coe S).trans hsize
  refine ⟨q*L,Nat.mul_pos hq hL,?_,?_⟩
  · rw [mul_comm q L]
    exact Nat.mul_le_mul_left L (hdim ▸ hbound)
  rw [←mul_one_div]
  apply empty_of_anchored_gaps H a _ (by positivity)
  intro i
  by_cases ha : i=a
  · subst i
    exact ⟨0,by simpa only [sub_self,mul_zero,zero_div,Int.cast_zero,abs_zero] using
      (one_div_pos.mpr (Nat.cast_pos.mpr hQ) : 0<1/(Q:ℝ))⟩
  have he : ((q*L:ℕ):ℝ)*τ*(E i-E a)/(2*π)=(q:ℝ)*((L:ℝ)*τ*(E i-E a)/(2*π)) := by push_cast; ring
  change latticeClose (((q*L:ℕ):ℝ)*τ*(E i-E a)/(2*π)) _
  rw [he]
  by_cases hb : i=b
  · subst i
    rw [hz]
    exact ⟨(q:ℤ)*z,by simpa only [Int.cast_mul,Int.cast_natCast,sub_self,abs_zero] using
      (one_div_pos.mpr (Nat.cast_pos.mpr hQ) : 0<1/(Q:ℝ))⟩
  let j : S := ⟨i,mem_erase.mpr ⟨hb,mem_erase.mpr ⟨ha,mem_univ _⟩⟩⟩
  simpa only [β,Equiv.symm_apply_apply] using hclose (e j)

#print axioms rational_pair_deadline
end
end GaloisForLFunctions.HTGeometry.ResonantReturns

import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.ScalarTail

/-! # A rare eigenphase tail forces a large circuit after every basis change -/
open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation
noncomputable section

/-- Keeping just the spectral displacement above a cutoff gives an
approximant whose rank is bounded by the number of retained eigenlines. -/
theorem truncate_displacement {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (V : unitaryGroup I ℂ) (z : I → ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ B : Matrix I I ℂ, ‖(1-V.val*diagonal z*star V.val)-B‖ ≤ ρ ∧
      B.rank ≤ (univ.filter fun j => ρ < ‖1-z j‖).card := by
  classical
  let d (i : I) := 1-z i
  let S := univ.filter (fun i => ρ < ‖d i‖)
  let f (i : I) := if i ∈ S then d i else 0
  let B := V.val*diagonal f*star V.val
  have h1 : (1 : Matrix I I ℂ) - diagonal z = diagonal d := by
    simpa only [Matrix.diagonal_one] using Matrix.diagonal_sub (fun _ : I => (1:ℂ)) z
  have hV : V.val * star V.val = 1 := V.property.2
  have he : (1-V.val*diagonal z*star V.val)-B = V.val*diagonal (fun i => d i-f i)*star V.val := by
    rw [←Matrix.diagonal_sub,←h1]
    simp only [B,mul_sub,sub_mul,mul_one,hV]
  refine ⟨B,?_,?_⟩
  · rw [he,l2_opNorm_unitary_conj_eq V.property,Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg hρ).mpr
    intro i
    by_cases hi : i ∈ S
    · simpa only [f,if_pos hi,sub_self,norm_zero] using hρ
    · simpa only [f,if_neg hi,sub_zero] using (not_lt.mp fun h => hi (mem_filter.mpr ⟨mem_univ _,h⟩))
  · apply ((Matrix.rank_mul_le_left ..).trans (Matrix.rank_mul_le_right ..)).trans
    rw [Matrix.rank_diagonal,Fintype.card_subtype]
    apply card_le_card
    intro i hi
    by_contra h
    have hi' := (mem_filter.mp hi).2
    exact hi' (if_neg (show i ∉ S from h))

/-- A spectrum extending more than twice the allowed error beyond a
cutoff needs at least one entire spectator block outside the cutoff. -/
theorem circuit_phase_tail_count {N : ℕ} (V W : unitaryGroup (Fin N → Bool) ℂ)
    (z : (Fin N → Bool) → ℂ) {ε ρ : ℝ} (hρ : 0 ≤ ρ)
    (hfar : 2*ε+ρ < ‖1-V.val*diagonal z*star V.val‖) {s : ℕ}
    (hfit : HasProjectiveCircuitApproximation N ε s
      (W.val*(V.val*diagonal z*star V.val)*star W.val)) :
    2^(N-2*s) ≤ (univ.filter fun i => ρ < ‖1-z i‖).card := by
  obtain ⟨B,hB,hr⟩ := truncate_displacement V z hρ
  exact (conjugate_scalar_tail _ B W hB hfar hfit).trans hr

#print axioms circuit_phase_tail_count
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation

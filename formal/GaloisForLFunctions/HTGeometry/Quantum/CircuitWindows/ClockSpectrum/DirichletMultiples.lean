import GaloisForLFunctions.HTGeometry.ProjectiveOperatorNormReturnTarget
import GaloisForLFunctions.HTGeometry.FidelityPhaseRadius
import GaloisForLFunctions.HTGeometry.UniformProjectiveContinuousCircuitFirstReturnLaw
import GaloisForLFunctions.HTGeometry.ProjectiveContinuousCircuitConeLaw
import GaloisForLFunctions.HTGeometry.Quantum.TranslatedCircuitOccupation

/-! # Empty-circuit recurrence on an arbitrary sampled clock -/
open Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Distance in turns from an integer bounds the chord to identity. -/
theorem phase_chord_of_turn_error (x : ℝ) {r : ℝ}
    (h : latticeClose (x/(2*Real.pi)) r) :
    ‖Complex.exp (-(Complex.I*(x : ℂ))) - 1‖ ≤ 2*Real.pi*r := by
  obtain ⟨m,hm⟩ := h
  rw [norm_exp_neg_I_mul_sub_one, mul_comm Complex.I]
  have hc := norm_expI_sub_expI_le x 0 m
  simp only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,sub_zero] at hc
  have hpi : 0 < 2*Real.pi := by positivity
  apply hc.trans
  rw [show x-2*Real.pi*m = 2*Real.pi*(x/(2*Real.pi)-m) by field_simp,
    abs_mul,abs_of_pos hpi]
  exact mul_le_mul_of_nonneg_left hm.le hpi.le

/-- One of the first (Q+1)^d positive multiples of any real clock step
fits the empty circuit. The dimension counts only relative eigenphases. -/
theorem zero_gate_at_integer_multiple {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (H : selfAdjoint (Reg n)) (tick : ℝ) (Q : ℕ) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ (Q+1)^d ∧ HasProjectiveCircuitApproximation n
      (2*Real.pi/(Q+1:ℝ)) 0 (unitaryEvolution H.val (tick*(q:ℝ))) := by
  let E := H.2.isHermitian.eigenvalues
  let a := e.symm 0
  let β (j : Fin d) := tick*(E (e.symm j.succ)-E a)/(2*Real.pi)
  obtain ⟨q,hq,hQ,hb⟩ := exists_simultaneous_dirichlet β (Nat.succ_pos Q)
  let t := tick*q
  refine ⟨q,hq,hQ,?_⟩
  refine ⟨anchorPhase E a t,by simp [anchorPhase,Complex.norm_exp],TwoQubitCircuit.one n,by rfl,?_⟩
  rw [TwoQubitCircuit.one_eval]
  change ‖unitaryEvolution (H : Reg n) t - anchorPhase E a t • (1:Reg n)‖ ≤ _
  rw [l2_opNorm_unitaryEvolution_sub_anchorPhase H.2.isHermitian a t]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2*Real.pi/(Q+1:ℝ))).mpr
  intro i
  let x := t * (E i-E a)
  have he : -(Complex.I * ((t:ℂ) * ((E i:ℂ)-(E a:ℂ)))) = -(Complex.I*(x:ℂ)) := by
    dsimp [x]; push_cast; rfl
  change ‖Complex.exp (-(Complex.I*((t:ℂ)*((E i:ℂ)-(E a:ℂ))))) - 1‖ ≤ _
  rw [he]
  rw [←mul_one_div (2*Real.pi) ((Q:ℝ)+1)]
  apply phase_chord_of_turn_error
  dsimp only [x]
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  refine Fin.cases ?_ (fun k => ?_) j
  · refine ⟨0,?_⟩
    simp only [a,sub_self,mul_zero,zero_div,Int.cast_zero,abs_zero]
    positivity
  · have h := hb k
    have hz : t*(E (e.symm k.succ)-E a)/(2*Real.pi) = (q:ℝ)*β k := by dsimp [t,β]; ring
    change latticeClose (t*(E (e.symm k.succ)-E a)/(2*Real.pi)) _
    rw [hz]
    simpa only [Nat.cast_succ] using h

#print axioms zero_gate_at_integer_multiple
end
end GaloisForLFunctions.HTGeometry

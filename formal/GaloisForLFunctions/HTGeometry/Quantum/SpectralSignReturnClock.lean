import GaloisForLFunctions.HTGeometry.Quantum.TranslatedCircuitExcursion
import GaloisForLFunctions.HTGeometry.ProjectiveSpectralRandomizedCircuitHardIntervalLaw

/-!
# Doubling the time of a spectral-sign visit

A unitary close to a phased involution squares to a near-scalar. Thus a
positive hard window certified from a sign visit has a return to the empty
circuit by twice its start, regardless of the spectrum.
-/

open Set
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry
noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

private theorem spectralSign_square {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ) (b : Fin d → Bool) :
    anchoredSpectralBooleanReflection e V b * anchoredSpectralBooleanReflection e V b = 1 := by
  let A := (V : Reg n)
  let I := (V⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).val
  let D : Reg n := Matrix.diagonal (anchoredBooleanPacket b ∘ e)
  have hIA : I*A = 1 := congrArg Subtype.val (inv_mul_cancel V)
  have hAI : A*I = 1 := congrArg Subtype.val (mul_inv_cancel V)
  have hD : D*D = 1 := by
    rw [show D*D = Matrix.diagonal ((anchoredBooleanPacket b ∘ e) * (anchoredBooleanPacket b ∘ e)) from
      Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    change anchoredBooleanPacket b (e i) * anchoredBooleanPacket b (e i) = 1
    generalize e i = j
    refine Fin.cases (by simp [anchoredBooleanPacket]) (fun k => ?_) j
    cases hk : b k <;> simp [anchoredBooleanPacket,hk]
  change A*D*I*(A*D*I) = 1
  calc
    _ = A*(D*(I*A)*D)*I := by noncomm_ring
    _ = 1 := by rw [hIA,mul_one,hD,mul_one,hAI]

/-- The distance to one phase times identity at twice the physical time is
at most twice the distance to any phased spectral reflection at the original
time. The eigenbasis of the reflection is arbitrary. -/
theorem spectral_sign_doubled_time_zero_gate {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d+1)) (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (b : Fin d → Bool) (H : selfAdjoint (Reg n)) (t : ℝ) (z : Circle) :
    HasProjectiveCircuitApproximation n
      (2*‖unitaryEvolution (H : Reg n) t - (z : ℂ) • anchoredSpectralBooleanReflection e V b‖)
      0 (unitaryEvolution (H : Reg n) (2*t)) := by
  let U := unitaryEvolution (H : Reg n) t
  let J := anchoredSpectralBooleanReflection e V b
  let X := (z:ℂ) • J
  have hJ : ‖J‖ = 1 := by
    let S := projectiveSpectralUnitary e V (anchoredBooleanProjectivePhase b)
    have hs : (S : Reg n) = J := projectiveSpectralMatrix_anchoredBooleanProjectivePhase e V b
    rw [← hs]; exact CStarRing.norm_of_mem_unitary S.2
  have hX : ‖X‖ = 1 := by simp [X,norm_smul,hJ]
  have hU : ‖U‖ = 1 := CStarRing.norm_of_mem_unitary (unitaryEvolution_mem_unitary H.2 _)
  have hXX : X*X = (z:ℂ)^2 • (1 : Reg n) := by
    dsimp only [X]
    rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,← pow_two,spectralSign_square]
  have hUU : U*U = unitaryEvolution (H : Reg n) (2*t) := by
    simpa only [two_mul,add_sub_cancel_right] using unitaryEvolution_sub_mul H (t+t) t
  refine ⟨(z:ℂ)^2,by simp,TwoQubitCircuit.one n,by rfl,?_⟩
  rw [TwoQubitCircuit.one_eval]
  change ‖unitaryEvolution (H : Reg n) (2*t) - (z:ℂ)^2 • (1 : Reg n)‖ ≤ 2*‖U-X‖
  rw [← hUU,← hXX]
  calc
    _ ≤ ‖U*U-U*X‖ + ‖U*X-X*X‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖U‖*‖U-X‖ + ‖U-X‖*‖X‖ := by
      rw [← mul_sub,← sub_mul]
      exact add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by rw [hU,hX,one_mul,mul_one,two_mul]

/-- At positive start, a sign visit which begins a hard window forces its
width to be shorter than the time since identity. -/
theorem spectral_sign_hard_window_width_lt_start {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d+1)) (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (b : Fin d → Bool) (H : selfAdjoint (Reg n)) (u W : ℝ) (s : ℕ)
    (hu : 0 ≤ u) (z : Circle)
    (hclose : ‖unitaryEvolution (H : Reg n) u - (z : ℂ) • anchoredSpectralBooleanReflection e V b‖ ≤ 1/20)
    (hhard : ∀ t ∈ Icc u (u+W), ProjectiveCircuitSeparated n (1/10:ℝ) s
      (unitaryEvolution (H : Reg n) t)) : W < u := by
  by_contra! h
  obtain ⟨c,hc,C,hC,he⟩ := spectral_sign_doubled_time_zero_gate e V b H u z
  have hf := hhard (2*u) ⟨by linarith,by linarith⟩ c hc C (hC.trans (Nat.zero_le _))
  linarith only [hf,he,hclose]

#print axioms spectral_sign_doubled_time_zero_gate
#print axioms spectral_sign_hard_window_width_lt_start

end
end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.ProjectiveContinuousCircuitConeLaw
import GaloisForLFunctions.HTGeometry.ContinuousPlateauGrid

/-! # A translated circuit-net certificate extends from a time grid to a whole interval -/
open Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- A phased reference matrix at the initial time may be transported by the
same increments as the physical orbit. A 1/40 error at the reference and
another 1/40 between samples preserve a 1/10 circuit separation. -/
theorem circuit_window_of_reference_grid {n s : ℕ} (H : selfAdjoint (Reg n))
    (J : Reg n) (z : ℂ) (u W mesh : ℝ) (hz : ‖z‖ = 1) (hm : 0 < mesh)
    (hspeed : ‖H.val‖*mesh ≤ 1/40) (hclose : ‖unitaryEvolution H.val u-z • J‖ ≤ 1/40)
    (hfar : ∀ j : Fin (plateauGridCount W mesh), ∀ b : ℂ, ‖b‖ = 1 → ∀ C : TwoQubitCircuit n,
      C.gateCount ≤ s → 3/20 < ‖J*unitaryEvolution H.val ((j.val:ℝ)*mesh)-b • (C.eval : Reg n)‖) :
    ∀ t ∈ Icc u (u+W), ProjectiveCircuitSeparated n (1/10:ℝ) s (unitaryEvolution H.val t) := by
  intro t ht c hc C hC
  obtain ⟨j,hj⟩ := exists_plateauGrid_near hm u ht
  let τ := (j.val:ℝ)*mesh
  let v := u+τ
  let U : Matrix.unitaryGroup (Fin n → Bool) ℂ := ⟨unitaryEvolution H.val τ,unitaryEvolution_mem_unitary H.2 _⟩
  have hstep : ‖unitaryEvolution H.val t-unitaryEvolution H.val v‖ ≤ 1/40 :=
    (norm_unitaryEvolution_time_sub_le H.2 t v).trans ((mul_le_mul_of_nonneg_left hj (norm_nonneg _)).trans hspeed)
  have hprod : unitaryEvolution H.val u*(U:Reg n) = unitaryEvolution H.val v := by
    simpa only [v,add_sub_cancel_right] using unitaryEvolution_sub_mul H v τ
  have hnear : ‖unitaryEvolution H.val v-z • (J*(U:Reg n))‖ ≤ 1/40 := by
    rw [← hprod,← Matrix.smul_mul,← sub_mul,CStarRing.norm_mul_coe_unitary]; exact hclose
  have h := hfar j (z⁻¹*c) (by rw [norm_mul,norm_inv,hz,hc,inv_one,one_mul]) C hC
  have he : z • (J*(U:Reg n)-(z⁻¹*c) • (C.eval:Reg n)) = z • (J*(U:Reg n))-c • (C.eval:Reg n) := by
    rw [smul_sub,smul_smul,← mul_assoc,mul_inv_cancel₀ (norm_ne_zero_iff.mp (by rw [hz]; exact one_ne_zero)),one_mul]
  have hsep : 3/20 < ‖z • (J*(U:Reg n))-c • (C.eval:Reg n)‖ := by rw [← he,norm_smul,hz,one_mul]; exact h
  have h1 := norm_sub_le_norm_sub_add_norm_sub (z • (J*(U:Reg n))) (unitaryEvolution H.val v) (c • (C.eval:Reg n))
  have h2 := norm_sub_le_norm_sub_add_norm_sub (unitaryEvolution H.val v) (unitaryEvolution H.val t) (c • (C.eval:Reg n))
  rw [norm_sub_rev] at hnear hstep
  linarith only [h1,h2,hnear,hstep,hsep]

end
end GaloisForLFunctions.HTGeometry

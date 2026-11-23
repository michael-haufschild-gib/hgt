import GaloisForLFunctions.HTGeometry.Quantum.TranslatedCircuitExcursion

/-! # Syndetic approximation to prescribed unit eigenphases -/
open Matrix Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralArcs
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- Every open ball about a prescribed energy-diagonal unitary is visited
with bounded gaps up to global phase on a maximally projective orbit. -/
theorem syndetic_packet_approach {n d : ℕ} (e : (Fin n→Bool) ≃ Fin (d+1))
    {H : Reg n} (hH : H.IsHermitian)
    (hmax : MaximallyProjectiveEnergy (fun i => hH.eigenvalues (e.symm i)))
    (f : Fin (d+1) → ℂ) (hf : ∀ i, ‖f i‖=1) {η : ℝ} (hη : 0<η) :
    ∃ G : ℝ, 0≤G ∧ ∀ a : ℝ, ∃ t∈Icc a (a+G), ∃ z : ℂ, ‖z‖=1 ∧
      ‖unitaryEvolution H t-z • (spectralPhaseUnitary e (hermitianEigenbasisUnitary hH) f hf : Reg n)‖ < η := by
  let V := hermitianEigenbasisUnitary hH
  let θ := projectivePhaseOfUnitPacket f hf
  let B := projectiveSpectralMatrix e V θ
  let O := (projectiveSpectralMatrix e V) ⁻¹' Metric.ball B η
  have ho : IsOpen O := Metric.isOpen_ball.preimage (continuous_projectiveSpectralMatrix e V)
  have hn : O.Nonempty := ⟨θ,Metric.mem_ball_self hη⟩
  let E (i : Fin (d+1)) := hH.eigenvalues (e.symm i)
  obtain ⟨G,hG,hh⟩ := denseAddOrbit_open_hits_syndetically
    (RHTower.projectivePhysicalPhaseFlowHom E) (RHTower.denseRange_projectivePhysicalPhaseFlowHom E hmax) ho hn
  refine ⟨G,hG,fun a => ?_⟩
  obtain ⟨t,ht,hx⟩ := hh a
  let c := Complex.exp (-(Complex.I*((t:ℂ)*hH.eigenvalues (e.symm 0))))
  have hc : ‖c‖=1 := by simp [c,Complex.norm_exp]
  refine ⟨t,ht,c/(f 0),by rw [norm_div,hc,hf,div_one],?_⟩
  rw [unitaryEvolution_eq_anchorPhase_smul_projectiveSpectralMatrix e hH,
    spectralPhaseUnitary_eq_phase_zero_smul_projectiveSpectralMatrix,smul_smul,
    div_mul_cancel₀ _ (norm_ne_zero_iff.mp (by rw [hf]; exact one_ne_zero))]
  change ‖c • _-c • B‖<η
  rw [←smul_sub,norm_smul,hc,one_mul]
  change (RHTower.projectivePhysicalPhaseFlow E t) ∈ O at hx
  exact Metric.mem_ball.mp hx

#print axioms syndetic_packet_approach
end
end GaloisForLFunctions.HTGeometry.SpectralArcs

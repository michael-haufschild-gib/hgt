import GaloisForLFunctions.HTGeometry.Quantum.FirstCircuitSaturationBoundary
import GaloisForLFunctions.HTGeometry.Quantum.SpectralSignReturnClock
import GaloisForLFunctions.HTGeometry.FiniteWindowContinuousCircuitOccupationLaw
import GaloisForLFunctions.HTGeometry.ArithmeticWindowHardCell

/-! # From phase-box precision to operator precision for spectral reflections -/
open Set Real Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

private theorem norm_spectral_phase_difference_le {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ) (θ : Fin d → ℝ) (y : Fin d → UnitAddCircle)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (h : ∀ j, turnDist (θ j-2*π*unitCircleRepresentative (y j)) ≤ ρ) :
    ‖projectiveSpectralMatrix e V (angularPhasePoint θ) - projectiveSpectralMatrix e V y‖ ≤ ρ := by
  let f (q : Fin (d+1)) := fourier 1 (RHTower.zeroAnchoredPhase d (angularPhasePoint θ) q)
  let g (q : Fin (d+1)) := fourier 1 (RHTower.zeroAnchoredPhase d y q)
  have hcoord (q) : ‖f q-g q‖ ≤ ρ := by
    refine Fin.cases ?_ (fun j => ?_) q
    · simpa [f,g,RHTower.zeroAnchoredPhase] using hρ
    · change ‖fourier 1 (angularPhasePoint θ j)-fourier 1 (y j)‖ ≤ ρ
      rw [fourier_one_angularPhasePoint,fourier_one_unitCircleRepresentative]
      exact (norm_exp_ofReal_mul_I_sub_le_turnDist _ _).trans (h j)
  unfold projectiveSpectralMatrix
  rw [← Matrix.sub_mul,← Matrix.mul_sub,Matrix.diagonal_sub]
  have hstar : (V⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).val = star V.val := by simp
  rw [hstar,l2_opNorm_unitary_conj_eq V.2,Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hρ).mpr fun q => hcoord (e q)

/-- Filling the relative phases in a prescribed interval approximates each
spectral reflection there, up to the phase of the anchor energy. -/
theorem phase_interval_approaches_reflection_at_error {n d : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (e : (Fin n → Bool) ≃ Fin (d+1)) (H : selfAdjoint (Reg n)) (a b : ℝ)
    (hphase : ∀ c : Fin d → ℝ, ∃ t ∈ Icc a b, ∀ j,
      turnDist (t*RHTower.zeroProjectiveFrequency (fun i => H.2.isHermitian.eigenvalues (e.symm i)) j-c j) < ρ)
    (x : Fin d → Bool) :
    ∃ t ∈ Icc a b, ∃ z : ℂ, ‖z‖ = 1 ∧
      ‖unitaryEvolution H.val t-z • anchoredSpectralBooleanReflection e (hermitianEigenbasisUnitary H.2.isHermitian) x‖ ≤ ρ := by
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  let E (i) := H.2.isHermitian.eigenvalues (e.symm i)
  let y := anchoredBooleanProjectivePhase x
  obtain ⟨t,ht,hθ⟩ := hphase (fun j => 2*π*unitCircleRepresentative (y j))
  let z : ℂ := Complex.exp (-(Complex.I*(t*E 0)))
  have hz : ‖z‖ = 1 := by simp [z,Complex.norm_exp]
  let J := anchoredSpectralBooleanReflection e V x
  have hclose : ‖unitaryEvolution H.val t-z • J‖ ≤ ρ := by
    rw [unitaryEvolution_eq_anchorPhase_smul_projectiveSpectralMatrix e H.2.isHermitian,
      projectivePhysicalPhaseFlow_eq_angularPhasePoint]
    change ‖z • _ - z • J‖ ≤ _
    rw [← smul_sub,norm_smul,hz,one_mul]
    rw [show J = projectiveSpectralMatrix e V y from (projectiveSpectralMatrix_anchoredBooleanProjectivePhase e V x).symm]
    exact norm_spectral_phase_difference_le e V _ y hρ (fun j => (hθ j).le)
  exact ⟨t,ht,z,hz,hclose⟩

/-- A filled phase box around the identity gives a zero-gate visit in the
same interval, even when its starting point depends on the trajectory. -/
theorem phase_interval_zero_gate_at_error {n d : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (e : (Fin n → Bool) ≃ Fin (d+1)) (H : selfAdjoint (Reg n)) (a b : ℝ)
    (hphase : ∀ c : Fin d → ℝ, ∃ t ∈ Icc a b, ∀ j,
      turnDist (t*RHTower.zeroProjectiveFrequency (fun i => H.2.isHermitian.eigenvalues (e.symm i)) j-c j) < ρ) :
    ∃ t ∈ Icc a b, HasProjectiveCircuitApproximation n ρ 0 (unitaryEvolution H.val t) := by
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  let x : Fin d → Bool := fun _ => false
  obtain ⟨t,ht,z,hz,hclose⟩ := phase_interval_approaches_reflection_at_error hρ e H a b hphase x
  have hone : anchoredBooleanPacket x ∘ e = (fun _ : Fin n → Bool => (1:ℂ)) := by
    funext i
    change anchoredBooleanPacket x (e i) = 1
    generalize e i = j
    exact Fin.cases rfl (fun _ => rfl) j
  have hJ : anchoredSpectralBooleanReflection e V x = 1 := by
    rw [anchoredSpectralBooleanReflection,hone,Matrix.diagonal_one,Matrix.mul_one]
    exact congrArg Subtype.val (mul_inv_cancel V)
  change ‖unitaryEvolution H.val t-z • anchoredSpectralBooleanReflection e V x‖ ≤ _ at hclose
  rw [hJ] at hclose
  refine ⟨t,ht,z,hz,TwoQubitCircuit.one n,le_rfl,?_⟩
  rw [TwoQubitCircuit.one_eval]
  exact hclose

#print axioms phase_interval_zero_gate_at_error
end
end GaloisForLFunctions.HTGeometry

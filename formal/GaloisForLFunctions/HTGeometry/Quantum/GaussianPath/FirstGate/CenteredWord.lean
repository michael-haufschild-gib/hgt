import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.PauliTerm
import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension

/-! # Single-gate implementation of a centered physical observable in the energy basis -/
open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstGate
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

/-- Subtracting a scalar from a local observable and choosing a signed
time costs exactly one gate up to the global phase. -/
private theorem centered_word {n : ℕ} (l : PathLabel n) (q t : ℝ) :
    ∃ z : ℂ, ‖z‖=1 ∧ ∃ C : TwoQubitCircuit (n+2), C.gateCount=1 ∧
      unitaryEvolution (finitePauliMatrix (pathWord l)-(q:ℂ) • (1:Reg (n+2))) t=z • (C.eval : Reg (n+2)) := by
  let u : PathShell n := WithLp.toLp 2 (fun _ => (1:ℝ))
  obtain ⟨z,hz,C,hC,he⟩ := (LocalPatches.pathTerm_properties u l).2.2 t
  have hf : unitaryEvolution (finitePauliMatrix (pathWord l)) t=z • (C.eval : Reg (n+2)) := by
    simpa only [LocalPatches.pathTermGenerator,u,WithLp.ofLp_toLp,Complex.ofReal_one,one_smul,unitaryEvolution] using he
  let P : selfAdjoint (Reg (n+2)) := ⟨_,finitePauliMatrix_isHermitian (pathWord l)⟩
  let w := Complex.exp (((-(t*q):ℝ):ℂ)*Complex.I)
  have hw : ‖w‖=1 := by simp [w,Complex.norm_exp]
  have hne : w≠0 := Complex.exp_ne_zero _
  refine ⟨w⁻¹*z,by rw [norm_mul,norm_inv,hw,hz,inv_one,mul_one],C,hC,?_⟩
  rw [←smul_smul,←hf]
  have hs := unitaryEvolution_eq_phase_smul_scalarCentered P q t
  change unitaryEvolution P.val t=w • unitaryEvolution (scalarCenteredHamiltonian P q).val t at hs
  rw [hs,smul_smul,inv_mul_cancel₀ hne,one_smul]
  rfl

/-- Conjugating the centered derivative back out of the energy basis
recovers a physical one-gate word for every real amplitude and duration. -/
theorem centered_eigenbasis_word {n : ℕ} (V : Reg (n+2)) (hV : V ∈ unitary (Reg (n+2)))
    (l : PathLabel n) (q s t : ℝ) :
    let B := star V*finitePauliMatrix (pathWord l)*V
    let A := (s:ℂ) • (B-(q:ℂ) • 1)
    ∃ z : ℂ, ‖z‖=1 ∧ ∃ C : TwoQubitCircuit (n+2), C.gateCount=1 ∧
      V*exp (t • (Complex.I • A))*star V=z • (C.eval : Reg (n+2)) := by
  intro B A
  let Q := finitePauliMatrix (pathWord l)-(q:ℂ) • (1:Reg (n+2))
  have hv := Unitary.mem_iff.mp hV
  have hcenter : V*(B-(q:ℂ) • 1)*star V=Q := by
    dsimp only [B,Q]
    rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,hv.2]
    congr 1
    simp only [mul_assoc,hv.2,mul_one]
    rw [←mul_assoc,hv.2,one_mul]
  have htime : exp (t • (Complex.I • A))=unitaryEvolution (B-(q:ℂ) • 1) (-t*s) := by
    unfold unitaryEvolution
    dsimp only [A]
    rw [←Complex.coe_smul t,←Complex.coe_smul (-t*s)]
    simp only [smul_smul]
    congr 2
    push_cast
    ring
  have hu : IsUnit V := ⟨⟨V,star V,hv.2,hv.1⟩,rfl⟩
  have conjFlow := unitaryEvolution_conj V (B-(q:ℂ) • 1) hu (-t*s)
  rw [inv_eq_star_of_mem_unitary hV,hcenter] at conjFlow
  rw [htime,←conjFlow]
  exact centered_word l q (-t*s)

#print axioms centered_eigenbasis_word
end
end GaloisForLFunctions.HTGeometry.FirstGate

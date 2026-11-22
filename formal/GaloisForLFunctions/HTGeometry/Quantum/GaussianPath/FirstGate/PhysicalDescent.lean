import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.FacePacket
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.SpectralDescent
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.EnergyWitness
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.CenteredWord
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.EntryFaces

/-! # Strict one-gate approximation at a scalar entry -/
open Real Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstGate
noncomputable section
open SharpOccupation EmptyVisitFlux

/-- At a simple entry, every Hermitian observable whose expectations
differ in the two endpoint eigenstates has a rotation improving the error. -/
theorem strict_rotation_at_entry {n : ℕ} (p : PathShell n) {ε t : ℝ} (hε : 0 < ε) (hs : ε < sqrt 2)
    (ht : 0 < t) :
    let hH := (isSelfAdjoint_pathHamiltonian p).isHermitian
    let E := fun k => -hH.eigenvalues k
    Function.Injective E → AvoidsTie E (physicalArc ε) → AvoidsTie E (-(physicalArc ε)) →
    visitEntry (fun k => E k/(2*π)) (physicalArc ε) t →
    let V : Register (n+2) := hH.eigenvectorUnitary
    ∃ a b, a≠b ∧ ∀ P : selfAdjoint (Register (n+2)),
      ((star V*P.val*V) a a).re≠((star V*P.val*V) b b).re →
      ∃ θ : ℝ, ∃ z : ℂ, ‖z‖=1 ∧
        ‖unitaryEvolution (pathHamiltonian p) t-z • unitaryEvolution P.val θ‖ < ε := by
  intro hH E hi hp hn he
  let x := physicalArc ε
  have hx := (physicalArc_spec hε hs).1
  obtain ⟨b,a,hface⟩ := (entry_iff_closed_face _ hx.1.le hx.2).mp he
  have hab : a≠b := by rintro rfl; exact hface.1.false
  obtain ⟨w,u,hw,hu,hphase,hconj,him,hre,hint⟩ := face_packet E hi hε hs ht hp hn hface
  let V : Register (n+2) := hH.eigenvectorUnitary
  have hV : V ∈ unitary (Register (n+2)) := hH.eigenvectorUnitary.2
  refine ⟨a,b,hab,?_⟩
  intro P hl
  let B := star V*P.val*V
  have hB : B.IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul V P.2.isHermitian
  let q := ((B a a).re+(B b b).re)/2
  let s : ℝ := if (B b b).re < (B a a).re then 1 else -1
  let d := |(B a a).re-(B b b).re|/2
  let A := (s:ℂ) • (B-(q:ℂ) • 1)
  obtain ⟨hA,ha,hb,_⟩ := centered_axis B hB a b
  have hd : 0<d := half_pos (abs_pos.mpr (sub_ne_zero.mpr hl))
  obtain ⟨v,_,hv⟩ := spectral_descent u (StaticLocalLaboratoryComplexityGrowthLaw.mem_unitaryGroup_diagonal_general u hu)
    a b hab hconj him hε hre hint A hA hd ha hb
  obtain ⟨z,hz,hword⟩ := centered_eigenbasis_rotation V hV P q s v
  have hspec : unitaryEvolution (pathHamiltonian p) t=w • (V*Matrix.diagonal u*star V) := by
    rw [unitaryEvolution_spectral hH,←Matrix.smul_mul,←Matrix.mul_smul]
    congr 2
    ext i j
    by_cases h : i=j
    · subst j
      simp only [Matrix.diagonal_apply_eq,Matrix.smul_apply,smul_eq_mul]
      convert hphase i using 2
      dsimp only [E]; push_cast; ring
    · simp [Matrix.diagonal_apply_ne _ h]
  refine ⟨-v*s,w*z,by rw [norm_mul,hw,hz,mul_one],?_⟩
  rw [hspec,←smul_smul,←hword,←smul_sub,norm_smul,hw,one_mul,←Matrix.sub_mul,←Matrix.mul_sub,
    l2_opNorm_unitary_conj_eq hV]
  exact hv

/-- At a genuine scalar entry with no endpoint ties, a local Pauli
direction chosen from the Hamiltonian improves the physical error
strictly. Its implementation uses exactly one gate. -/
theorem strict_gate_at_entry {n : ℕ} (p : PathShell n) {ε t : ℝ} (hε : 0 < ε) (hs : ε < sqrt 2)
    (ht : 0 < t) :
    let hH := (isSelfAdjoint_pathHamiltonian p).isHermitian
    let E := fun k => -hH.eigenvalues k
    Function.Injective E → AvoidsTie E (physicalArc ε) → AvoidsTie E (-(physicalArc ε)) →
    visitEntry (fun k => E k/(2*π)) (physicalArc ε) t →
    ∃ z : ℂ, ‖z‖=1 ∧ ∃ C : TwoQubitCircuit (n+2), C.gateCount=1 ∧
      ‖unitaryEvolution (pathHamiltonian p) t-z • (C.eval : Register (n+2))‖ < ε := by
  intro hH E hi hp hn he
  obtain ⟨a,b,hab,hr⟩ := strict_rotation_at_entry p hε hs ht hi hp hn he
  have hne : hH.eigenvalues a≠hH.eigenvalues b := fun h => hi.ne hab (congrArg Neg.neg h)
  obtain ⟨l,hl⟩ := exists_distinguishing_term p a b hne
  let P : selfAdjoint (Register (n+2)) := ⟨_,finitePauliMatrix_isHermitian (pathWord l)⟩
  obtain ⟨θ,w,hw,herr⟩ := hr P hl
  obtain ⟨z,hz,C,hC,hword⟩ := pauli_rotation_word l θ
  exact ⟨w*z,by rw [norm_mul,hw,hz,mul_one],C,hC,by rwa [←smul_smul,←hword]⟩

#print axioms strict_gate_at_entry
end
end GaloisForLFunctions.HTGeometry.FirstGate

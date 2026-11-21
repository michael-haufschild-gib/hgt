import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.FacePacket
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.SpectralDescent
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.EnergyWitness
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.CenteredWord

/-! # Strict one-gate approximation at a scalar entry -/
open Real Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstGate
noncomputable section
open SharpOccupation EmptyVisitFlux

private theorem unitary_diagonal {I : Type*} [Fintype I] [DecidableEq I] (u : I → ℂ)
    (hu : ∀ k, ‖u k‖=1) : Matrix.diagonal u ∈ unitary (Matrix I I ℂ) := by
  change _ ∈ Matrix.unitaryGroup I ℂ
  rw [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal,←Matrix.diagonal_one]
  congr 1
  funext k
  change u k*(starRingEnd ℂ) (u k)=1
  rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,hu]
  norm_num

private theorem diagonal_real {I : Type*} (B : Matrix I I ℂ) (hB : B.IsHermitian) (j : I) :
    B j j=((B j j).re:ℂ) := by
  have h := congrArg Complex.im (hB.apply j j)
  change -(B j j).im=(B j j).im at h
  exact Complex.ext rfl (by change (B j j).im=0; linarith only [h])

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
  let x := physicalArc ε
  have hx := (physicalArc_spec hε hs).1
  obtain ⟨b,a,hface⟩ := (entry_iff_closed_face _ hx.1.le hx.2).mp he
  have hab : a≠b := by rintro rfl; exact hface.1.false
  obtain ⟨w,u,hw,hu,hphase,hconj,him,hre,hint⟩ := face_packet E hi hε hs ht hp hn hface
  let V : Register (n+2) := hH.eigenvectorUnitary
  have hV : V ∈ unitary (Register (n+2)) := hH.eigenvectorUnitary.2
  have hne : hH.eigenvalues a≠hH.eigenvalues b := fun h => hi.ne hab (congrArg Neg.neg h)
  obtain ⟨l,hl⟩ := exists_distinguishing_term p a b hne
  let B := star V*finitePauliMatrix (pathWord l)*V
  have hB : B.IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul V (finitePauliMatrix_isHermitian _)
  let q := ((B a a).re+(B b b).re)/2
  let s : ℝ := if (B b b).re < (B a a).re then 1 else -1
  let d := s*((B a a).re-(B b b).re)/2
  have hd : 0 < d := by
    change (B a a).re ≠ (B b b).re at hl
    rcases lt_or_gt_of_ne hl with h|h
    · dsimp only [d,s]; rw [if_neg h.not_gt]; linarith only [h]
    · dsimp only [d,s]; rw [if_pos h]; linarith only [h]
  let A := (s:ℂ) • (B-(q:ℂ) • 1)
  have hA : A.IsHermitian := (hB.sub (Matrix.isHermitian_one.smul (show IsSelfAdjoint (q:ℂ) by simp [IsSelfAdjoint]))).smul
    (show IsSelfAdjoint (s:ℂ) by simp [IsSelfAdjoint])
  have heA (k) : A k k=(s:ℂ)*(((B k k).re:ℂ)-(q:ℂ)) := by
    simp only [A,Matrix.smul_apply,Matrix.sub_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one]
    rw [←diagonal_real B hB]
  have hdiag : A a a=(d:ℂ) ∧ A b b=-(d:ℂ) := by
    rw [heA,heA]
    dsimp only [d,q]
    push_cast
    constructor <;> ring
  obtain ⟨v,_,hv⟩ := spectral_descent u (unitary_diagonal u hu) a b hab hconj him hε hre hint A hA hd hdiag.1 hdiag.2
  obtain ⟨z,hz,C,hC,hword⟩ := centered_eigenbasis_word V hV l q s v
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
  refine ⟨w*z,by rw [norm_mul,hw,hz,mul_one],C,hC,?_⟩
  rw [hspec,←smul_smul,←hword,←smul_sub,norm_smul,hw,one_mul,←Matrix.sub_mul,←Matrix.mul_sub,
    l2_opNorm_unitary_conj_eq hV]
  exact hv

#print axioms strict_gate_at_entry
end
end GaloisForLFunctions.HTGeometry.FirstGate

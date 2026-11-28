import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Roots.PauliAverages.Pulses.Commutator
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Roots.PauliAverages.Twirl
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.PauliRotations
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.TransferCoefficient

/-! # Ancilla-free circuits for a small Pauli bracket -/

open Matrix Finset Real Complex
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Pulses
open private involution_evolution from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.TransferCoefficient
noncomputable section
private abbrev Reg (K : ℕ) := Matrix (Fin K → Bool) (Fin K → Bool) ℂ

/-- The global phase of the synthesized Pauli rotation cancels in the
four-pulse word. The resulting circuit acts on the original register. -/
theorem bracket_circuit {K : ℕ} (hK : 2≤K) (C : TwoQubitCircuit K)
    (j : Fin K → Option (Fin 3)) {b : ℝ} (hb : 0≤b) (hb' : b≤1) :
    ∃ D : TwoQubitCircuit K, D.gateCount ≤ 4*(C.gateCount+2*K+1) ∧
      ‖D.eval.val-(1+b^2 • pauliBracket C.eval.val j)‖≤8*b^3 := by
  let P := finitePauliMatrix j
  let U := C.eval
  let Q := U.val*P*star U.val
  let t := arcsin b
  let a := Real.cos t
  have hP : P∈unitary (Reg K) := by
    have hp : star P=P := finitePauliMatrix_isHermitian _
    rw [Unitary.mem_iff,hp]
    exact ⟨finitePauliMatrix_mul_self _,finitePauliMatrix_mul_self _⟩
  have hQ : Q∈unitary (Reg K) := mul_mem (mul_mem U.2 hP) (U⁻¹).2
  let A : unitary (Reg K) := ⟨unitaryEvolution P t,unitaryEvolution_mem_unitary
    (show IsSelfAdjoint P from finitePauliMatrix_isHermitian _) t⟩
  let B := U*A*U⁻¹
  have hs : Real.sin t=b := Real.sin_arcsin (by linarith) hb'
  have ha : |a-1|≤b := by
    have h₀ : 0≤a := Real.cos_nonneg_of_mem_Icc ⟨Real.neg_pi_div_two_le_arcsin _,Real.arcsin_le_pi_div_two _⟩
    have h₁ : a≤1 := Real.cos_le_one _
    rw [abs_of_nonpos (sub_nonpos.mpr h₁)]
    have h := Real.sin_sq_add_cos_sq t
    rw [hs] at h
    change b^2+a^2=1 at h
    by_contra! hn
    have hl := mul_self_lt_mul_self h₀ (show a<1-b by linarith)
    nlinarith only [h,hl,mul_nonneg hb (sub_nonneg.mpr hb')]
  have hA : A.val=(a:ℂ) • 1+(-Complex.I*(b:ℂ)) • P := by
    change unitaryEvolution P t=_
    rw [involution_evolution P (finitePauliMatrix_mul_self _) t,hs]
  have hB : B.val=(a:ℂ) • 1+(-Complex.I*(b:ℂ)) • Q := by
    change U.val*A.val*star U.val=_
    rw [hA,mul_add,add_mul,Matrix.mul_smul,Matrix.mul_smul,Matrix.smul_mul,Matrix.smul_mul,
      mul_one,(Unitary.mem_iff.mp U.2).2]
  have hbound := commutator_error A B P Q (CStarRing.norm_of_mem_unitary hP).le
    (CStarRing.norm_of_mem_unitary hQ).le hb ha hA hB
  obtain ⟨z,hz,G,hG,hrot⟩ := exists_projective_pauli_rotation_circuit hK j t
  let V := (C.mul G).mul C.adjoint
  let D := ((G.mul V).mul G.adjoint).mul V.adjoint
  have hzA : A.val=z • G.eval.val := hrot
  have hzB : B.val=z • V.eval.val := by
    change U.val*A.val*star U.val=_
    simp only [hzA,V,Matrix.mul_smul,Matrix.smul_mul,TwoQubitCircuit.mul_eval,TwoQubitCircuit.adjoint_eval]
    rfl
  have hw : (A*B*A⁻¹*B⁻¹).val=D.eval.val := by
    change A.val*B.val*star A.val*star B.val=_
    rw [hzA,hzB]
    simp only [star_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,Complex.star_def]
    have hzz : z*conj z=1 := by
      rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,hz]; norm_num
    have hc : conj z*(conj z*(z*z))=1 := by
      calc _ = (z*conj z)^2 := by ring
           _ = _ := by rw [hzz,one_pow]
    rw [hc,one_smul]
    simp only [D,TwoQubitCircuit.mul_eval,TwoQubitCircuit.adjoint_eval]
    rfl
  have hj : pauliWeight j≤K := (Finset.card_le_univ _).trans (by simp)
  refine ⟨D,?_,?_⟩
  · simp only [D,V,TwoQubitCircuit.mul_gateCount,show ∀ E : TwoQubitCircuit K, E.adjoint.gateCount=E.gateCount from fun _ => rfl]
    omega
  · rw [hw] at hbound
    exact hbound

#print axioms bracket_circuit
end
end GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Pulses

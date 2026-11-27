import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Frames.RotatedShell

/-! # Optimal circuit error is invariant under product changes of Pauli frame -/

open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
noncomputable section
variable {n : ℕ}

/-- A product change of Pauli axes preserves the operator error of a concrete
circuit, gate by gate on the identical ordered architecture. -/
theorem frame_preserves_fit (a : Fin (n+2)→Fin 3) (u : PathShell n) (C : TwoQubitCircuit (n+2))
    (t : ℝ) (z : ℂ) :
    ∃ T, let D : TwoQubitCircuit (n+2) := ⟨C.gateCount,C.architecture,T⟩
      ‖unitaryEvolution (pathHamiltonian (rotatedShell a u)) t-z • D.eval.val‖=
        ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖ := by
  let V := localFrame (fun i => axisFrame (a i))
  obtain ⟨T,hT⟩ := conjugate_architecture (fun i => axisFrame (a i)) C.architecture C.gates
  refine ⟨T,?_⟩
  intro D
  have hD : D.eval.val=V.val*C.eval.val*V.valᴴ := congrArg Subtype.val hT
  have hV := (Unitary.mem_iff.mp V.2).2
  have his : IsUnit V.val := ⟨⟨V.val,star V.val,hV,(Unitary.mem_iff.mp V.2).1⟩,rfl⟩
  have he : unitaryEvolution (pathHamiltonian (rotatedShell a u)) t=
      V.val*unitaryEvolution (pathHamiltonian u) t*V.valᴴ := by
    rw [←rotatedShell_hamiltonian]
    change unitaryEvolution (V.val*pathHamiltonian u*V.valᴴ) t=_
    simpa only [inv_eq_star_of_mem_unitary V.2,Matrix.star_eq_conjTranspose] using
      unitaryEvolution_conj V.val (pathHamiltonian u) his t
  rw [he,hD,←Matrix.smul_mul,←Matrix.mul_smul,←sub_mul,←mul_sub,
    CStarRing.norm_mul_mem_unitary _ (show V.valᴴ∈unitary _ from Unitary.star_mem V.2),
    CStarRing.norm_mem_unitary_mul _ V.2]

#print axioms frame_preserves_fit
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit

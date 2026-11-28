import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.UniformGateCap

/-! # A sparse Pauli tangent realized with a bounded number of physical gates -/

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.LocalTangents.Multiplicity
open private product_circuit from GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.UniformGateCap
open private list_exp_linear_error from GaloisForLFunctions.HTGeometry.Quantum.CoefficientMassLieProduct
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ
local instance (n : ℕ) : CStarAlgebra (Reg n) where

/-- One ordered sweep of d arbitrary Pauli rotations realizes the affine
rotation to quadratic error using at most d(2N+1) extra two-qubit gates,
without auxiliary qubits. -/
theorem sparse_sweep {n d : ℕ} (hn : 2≤n) (w : Fin d → Fin n → Option (Fin 3)) (a : Fin d → ℝ)
    (C : TwoQubitCircuit n) {v : ℂ} (hv : ‖v‖=1) :
    let B := ∑ i, a i • finitePauliSelfAdjoint (w i)
    let Q := v • C.eval.val
    ∃ M≥(0:ℝ), ∀ r : ℝ, ∃ D : TwoQubitCircuit n, D.gateCount≤C.gateCount+d*(2*n+1) ∧
      ∃ z : ℂ, ‖z‖=1 ∧ ‖Q+(r:ℂ) • ((Complex.I • B.val)*Q)-z • D.eval.val‖≤M*r^2 := by
  intro B Q
  let G (i : Fin d) : Reg n := Complex.I • ((a i:ℂ) • finitePauliMatrix (w i))
  let Z := List.ofFn G
  have hZ : Z.sum=Complex.I • B.val := by
    rw [List.sum_ofFn]
    dsimp only [G,B]
    rw [←Finset.smul_sum]
    congr 1
    exact (map_sum (selfAdjoint.submodule ℝ (Reg n)).subtype (fun i => a i • finitePauliSelfAdjoint (w i)) Finset.univ).symm
  have hskews (x) (hx : x∈Z) : x∈skewAdjoint (Reg n) := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    rw [skewAdjoint.mem_iff]
    change star (Complex.I • ((a i:ℂ) • finitePauliMatrix (w i)))=_
    rw [star_smul,star_smul,show star (finitePauliMatrix (w i))=_ from finitePauliMatrix_isHermitian _]
    simp [G]
  refine ⟨(Z.map norm).sum^2/2,by positivity,?_⟩
  intro r
  let A := Z.map fun x => exp (r • x)
  have hgate (y) (hy : y∈A) : ∃ z : ℂ, ‖z‖=1 ∧ ∃ D : TwoQubitCircuit n,
      D.gateCount≤2*n+1 ∧ y=z • D.eval.val := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    obtain ⟨z,hz,D,hD,hrot⟩ := exists_projective_pauli_rotation_circuit hn (w i) (-r*a i)
    have hw : pauliWeight (w i)≤n := (Finset.card_le_univ _).trans (by simp)
    refine ⟨z,hz,D,by omega,?_⟩
    rw [←hrot,unitaryEvolution]
    congr 1
    ext j k
    simp [G,Matrix.smul_apply]
    ring
  obtain ⟨z,hz,D,hD,hprod⟩ := product_circuit A hgate
  refine ⟨D.mul C,Nat.add_le_add_left (by simpa only [A,Z,List.length_map,List.length_ofFn] using hD) _,z*v,by rw [norm_mul,hz,hv,one_mul],?_⟩
  have h := list_exp_linear_error Z hskews r
  change ‖A.prod-(1+r • Z.sum)‖≤_ at h
  rw [hZ,hprod,sq_abs,norm_sub_rev] at h
  have hlin : Q+(r:ℂ) • ((Complex.I • B.val)*Q)=(1+r • (Complex.I • B.val))*Q := by
    simp only [add_mul,one_mul,Matrix.smul_mul,Complex.coe_smul]
  have hword : (z • D.eval.val)*Q=(z*v) • (D.mul C).eval.val := by
    rw [TwoQubitCircuit.mul_eval]
    change (z • D.eval.val)*(v • C.eval.val)=(z*v) • (D.eval.val*C.eval.val)
    rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [hlin,←hword,←sub_mul]
  change ‖_*(v • C.eval.val)‖≤_
  rw [Matrix.mul_smul,norm_smul,hv,one_mul,CStarRing.norm_mul_mem_unitary _ C.eval.2]
  exact h.trans_eq (by ring)

#print axioms sparse_sweep
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.LocalTangents.Multiplicity

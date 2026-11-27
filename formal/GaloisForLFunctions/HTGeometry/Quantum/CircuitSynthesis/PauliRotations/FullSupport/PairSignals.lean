import GaloisForLFunctions.HTGeometry.ConstraintRelativity.InteractionCrossFibre
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.PauliRotations
import GaloisForLFunctions.HTGeometry.PauliCharacterFirstDefectCovariance
import GaloisForLFunctions.HTGeometry.TwoReplicaGlobalPauliHallSymmetryReduction
import GaloisForLFunctions.HTGeometry.NearestNeighborPathSpectrumRealRelationEscape

/-! # A Pauli rotation with maximal signals between every two wires -/
open Matrix Real NormedSpace Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FullPauliRotation
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ
variable {n : ℕ}
local instance (n : ℕ) : CStarAlgebra (Reg n) where

/-- A quarter turn about the product of all Z axes. -/
def parityRotation (n : ℕ) := unitaryEvolution (finitePauliMatrix (fun _ : Fin n => some 2)) (π/4)

/-- The same X probe on each wire attains commutator norm two in every
ordered direction. The rotation changes Xᵢ into i (Z₁⋯Zₙ) Xᵢ. -/
theorem maximal_pair_signals (n : ℕ) :
    ∃ X : Fin n→Reg n, (∀ i, IsSiteSupported {i} (X i) ∧ X i∈unitary _) ∧
      ∀ i j, i≠j → let Y := star (parityRotation n)*X i*parityRotation n
        ‖Y*X j-X j*Y‖=2 := by
  let W := fun _ : Fin n => some (2:Fin 3)
  let J := finitePauliMatrix W
  let X (i : Fin n) := finitePauliMatrix (singlePauliAxisLabel i 0)
  have hJ := (finitePauliMatrix_isHermitian W).isSelfAdjoint
  have hs (i : Fin n) : IsSiteSupported {i} (X i) := by
    apply finitePauliMatrix_isSiteSupported_of_eq_none
    intro j hj
    simp only [singlePauliAxisLabel,if_neg (show j≠i from fun h => hj (mem_singleton.mpr h))]
  have hX (i : Fin n) : X i∈unitary _ := finitePauliMatrix_mem_unitary _
  have ha (i : Fin n) : X i*J= -(J*X i) := by
    have h := finitePauliMatrix_mul_eq_sign_mul (singlePauliAxisLabel i 0) W
    rw [finitePauliConjugationSign_singlePauliAxisLabel] at h
    have hsgn : boolPauliConjugationSign (some 0) (W i)= -1 := by
      norm_num [W,boolPauliConjugationSign]
    rwa [hsgn,neg_one_smul] at h
  have hU : parityRotation n∈unitary _ := unitaryEvolution_mem_unitary hJ _
  let t := π/4
  have hu : parityRotation n=exp ((-(Complex.I*(t:ℂ))) • J) := by
    change exp (t • ((-Complex.I) • J))=_
    rw [←Complex.coe_smul,smul_smul]
    congr 2
    ring
  have hc (i : Fin n) : star (parityRotation n)*X i*parityRotation n=Complex.I • (J*X i) := by
    have h := _root_.HTGeometry.ConstraintRelativity.conjugation_of_involution_anticommute J (X i)
      (finitePauliMatrix_mul_self W) (by rw [ha,neg_neg]) t
    rw [show 2*t=π/2 by dsimp only [t]; ring,cos_pi_div_two,sin_pi_div_two] at h
    rw [hu,NormedSpace.star_exp,star_smul,hJ.star_eq]
    simpa only [Complex.star_def,map_neg,map_mul,Complex.conj_I,Complex.conj_ofReal,neg_mul,neg_neg,
      Complex.ofReal_zero,Complex.ofReal_one,zero_smul,zero_add,mul_one] using h
  refine ⟨X,fun i => ⟨hs i,hX i⟩,?_⟩
  intro i j hij Y
  have hcomm := (commute_of_isSiteSupported_disjoint (Finset.disjoint_singleton.mpr hij) (hs i) (hs j)).eq
  have hanti : X j*Y= -(Y*X j) := by
    dsimp only [Y]
    rw [hc,Matrix.mul_smul,Matrix.smul_mul,←smul_neg]
    congr 1
    rw [←mul_assoc,ha,neg_mul,mul_assoc,←hcomm,mul_assoc]
  have hnorm : ‖Y*X j‖=1 := CStarRing.norm_of_mem_unitary
    (mul_mem (mul_mem (mul_mem (Unitary.star_mem hU) (hX i)) hU) (hX j))
  rw [hanti,sub_neg_eq_add,←two_smul ℝ (Y*X j),norm_smul,hnorm]
  norm_num

/-- A single exact circuit of linear size realizes all the signals. -/
theorem exact_synthesis (hn : 2≤n) :
    ∃ z : ℂ, ‖z‖=1 ∧ ∃ C : TwoQubitCircuit n, C.gateCount≤2*n+1 ∧ parityRotation n=z • C.eval.val := by
  obtain ⟨z,hz,C,hC,h⟩ := exists_projective_pauli_rotation_circuit hn (fun _ => some 2) (π/4)
  refine ⟨z,hz,C,?_,h⟩
  simpa [pauliWeight] using hC

#print axioms maximal_pair_signals
#print axioms exact_synthesis
end
end GaloisForLFunctions.HTGeometry.FullPauliRotation

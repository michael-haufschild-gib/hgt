import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Transverse
import GaloisForLFunctions.HTGeometry.ExpSelfAdjointNormBound

/-! # Pinching along an arbitrary local spin axis -/

open Finset Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut.Tilted
open DiagonalSynthesis
noncomputable section
variable {n : ℕ}

abbrev onsiteAxis (q : Fin (n+2)) (i : Fin 3) := finitePauliMatrix (onsiteWord q i)

/-- The real magnetic field evaluated on the Pauli triple at one site. -/
def spinVector (q : Fin (n+2)) (v : Fin 3 → ℝ) : Register (n+2) :=
  ∑ i, v i • onsiteAxis q i

private theorem axis_anticommute (q : Fin (n+2)) {i j : Fin 3} (h : i≠j) :
    onsiteAxis q i * onsiteAxis q j = -(onsiteAxis q j * onsiteAxis q i) := by
  apply finitePauliMatrix_anticommute_of_not_commute
  rw [finitePauli_commute_iff_sign]
  change finitePauliConjugationSign (singlePauliAxisLabel q i) (onsiteWord q j) ≠ 1
  rw [finitePauliConjugationSign_singlePauliAxisLabel]
  simp [onsiteWord,boolPauliConjugationSign,h]

private theorem anticommute_axis_sum (q : Fin (n+2)) (v : Fin 3 → ℝ) (j : Fin 3) :
    spinVector q v * onsiteAxis q j + onsiteAxis q j * spinVector q v =
      (2*v j) • (1 : Register (n+2)) := by
  rw [spinVector,sum_mul,mul_sum,←sum_add_distrib]
  simp only [smul_mul_assoc,mul_smul_comm,←smul_add]
  rw [sum_eq_single j]
  · rw [finitePauliMatrix_mul_self,smul_add,two_mul,add_smul]
  · intro i _ hi
    rw [axis_anticommute q hi,neg_add_cancel,smul_zero]
  · exact fun hj => (hj (mem_univ j)).elim

/-- Anticommuting two local fields gives twice their ordinary
Euclidean inner product times the identity. -/
theorem spinVector_anticommutator (q : Fin (n+2)) (u v : Fin 3 → ℝ) :
    spinVector q u * spinVector q v + spinVector q v * spinVector q u =
      (2*∑ i, u i*v i) • (1 : Register (n+2)) := by
  change spinVector q u*(∑ i, v i • onsiteAxis q i)+(∑ i, v i • onsiteAxis q i)*spinVector q u=_
  simp only [mul_sum,sum_mul,mul_smul_comm,smul_mul_assoc,←sum_add_distrib,
    ←smul_add,anticommute_axis_sum,smul_smul]
  rw [mul_sum,sum_smul]
  exact sum_congr rfl fun i _ => congrArg (fun c : ℝ => c • (1 : Register (n+2))) (by ring)

/-- A unit field gives a self-adjoint involution on the physical
register, including its spectator wires. -/
theorem spinVector_unit (q : Fin (n+2)) {u : Fin 3 → ℝ} (hu : ∑ i, u i^2=1) :
    IsSelfAdjoint (spinVector q u) ∧ spinVector q u * spinVector q u = 1 ∧
      ‖spinVector q u‖ = 1 := by
  have hself : IsSelfAdjoint (spinVector q u) := by
    change star (∑ i, u i • onsiteAxis q i) = _
    rw [star_sum]
    apply sum_congr rfl
    intro i _
    rw [star_smul,star_trivial,(finitePauliMatrix_isHermitian (onsiteWord q i)).isSelfAdjoint.star_eq]
  have hanti := spinVector_anticommutator q u u
  simp only [←sq,hu,mul_one,two_smul ℝ] at hanti
  have hs : spinVector q u * spinVector q u = 1 := by
    apply eq_of_sub_eq_zero
    have he : (2:ℝ) • (spinVector q u * spinVector q u - 1) = 0 := by
      rw [smul_sub,two_smul ℝ,two_smul ℝ,sub_eq_zero]
      exact hanti
    exact (smul_eq_zero.mp he).resolve_left (by norm_num)
  have hU : spinVector q u ∈ unitary (Register (n+2)) :=
    ⟨by rwa [hself.star_eq],by rwa [hself.star_eq]⟩
  exact ⟨hself,hs,norm_eq_one_of_mem_unitary hU⟩

/-- The part of a field even under the local involution is its
orthogonal projection onto that axis. -/
theorem spinVector_even (q : Fin (n+2)) {u : Fin 3 → ℝ} (hu : ∑ i, u i^2=1)
    (v : Fin 3 → ℝ) :
    let Z := spinVector q u
    let A := spinVector q v
    (1/2 : ℝ) • (A+Z*A*Z) = (∑ i, u i*v i) • Z := by
  intro Z A
  have hz : Z*Z=1 := (spinVector_unit q hu).2.1
  have h := congrArg (fun M : Register (n+2) => M*Z) (spinVector_anticommutator q u v)
  change (Z*A+A*Z)*Z = ((2*∑ i, u i*v i) • (1 : Register (n+2)))*Z at h
  rw [add_mul,mul_assoc A,hz,mul_one,smul_mul_assoc,one_mul,add_comm] at h
  rw [h,smul_smul]
  congr 1
  ring

#print axioms spinVector_even
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut.Tilted

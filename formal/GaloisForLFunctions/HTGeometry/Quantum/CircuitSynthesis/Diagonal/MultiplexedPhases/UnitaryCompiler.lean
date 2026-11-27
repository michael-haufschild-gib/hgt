import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.MultiplexedPhases.Eigenlines
import GaloisForLFunctions.HTGeometry.CommutingNormalMatrixEigenbasis

/-! # A quadratic exact compiler for arbitrary changes of basis -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.DiagonalSynthesis.MultiplexedPhases
noncomputable section

/-- Diagonalize the unitary itself, then apply one exact phase rotation
per eigenline. The bound also covers the eigenbasis of an arbitrary block. -/
theorem quadratic_unitary_gate_cap {n : ℕ} (hn : 2 ≤ n) (U : unitaryGroup (Config n) ℂ) :
    Realizes (35*(2^n)^2) (U : Register n) := by
  classical
  let A : Register n := U
  have hU := Unitary.mem_iff.mp U.property
  have hc : Commute A (star A) := hU.2.trans hU.1.symm
  obtain ⟨b,hb⟩ := exists_orthonormalBasis_eigen_of_pairwise_commute_star
    (fun _ : Unit => A) (fun _ _ => Commute.refl _) (fun _ _ => hc)
  let e := Fintype.equivFin (Config n)
  let v := b.reindex e.symm
  let std := EuclideanSpace.basisFun (Config n) ℂ
  let V : unitaryGroup (Config n) ℂ := ⟨std.toBasis.toMatrix v,std.toMatrix_orthonormalBasis_mem_unitary v⟩
  have hcol (i j : Config n) : (V : Register n) i j=b (e j) i := by
    change v j i=_
    rw [show v j=b (e j) from b.reindex_apply e.symm j]
  choose p hp using fun j : Config n => hb () (e j)
  have he : A*(V : Register n)=(V : Register n)*diagonal p := by
    ext i j
    rw [mul_diagonal,mul_apply,hcol]
    simp only [hcol]
    have hi := congrArg (fun z : EuclideanSpace ℂ (Config n) => z i) (hp j)
    simpa only [toLpLin_apply,mulVec,dotProduct,PiLp.smul_apply,smul_eq_mul,mul_comm (p j)] using hi
  have hV := Unitary.mem_iff.mp V.property
  have hD : diagonal p=star (V : Register n)*A*(V : Register n) := by
    rw [mul_assoc,he,←mul_assoc,hV.1,one_mul]
  have hunit : diagonal p ∈ unitaryGroup (Config n) ℂ := hD ▸ mul_mem (mul_mem (V⁻¹).property U.property) V.property
  have hz (j : Config n) : ‖p j‖=1 := by
    rw [mem_unitaryGroup_iff,star_eq_conjTranspose,diagonal_conjTranspose,diagonal_mul_diagonal] at hunit
    have h := congrArg (fun M : Register n => ‖M j j‖) hunit
    simp only [diagonal_apply_eq,one_apply_eq,norm_one,norm_mul] at h
    change ‖p j‖*‖star (p j)‖=1 at h
    rw [norm_star] at h
    nlinarith only [h,norm_nonneg (p j)]
  have hback : A=(V : Register n)*diagonal p*star (V : Register n) := by
    rw [←he,mul_assoc,hV.2,mul_one]
  rw [show (U : Register n)=A from rfl,hback]
  exact quadratic_eigenbasis_phases hn V p hz

#print axioms quadratic_unitary_gate_cap
end
end GaloisForLFunctions.HTGeometry.DiagonalSynthesis.MultiplexedPhases

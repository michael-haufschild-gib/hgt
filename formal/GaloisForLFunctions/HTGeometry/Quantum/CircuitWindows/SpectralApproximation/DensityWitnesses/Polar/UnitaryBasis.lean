import GaloisForLFunctions.HTGeometry.CommutingNormalMatrixEigenbasis
import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension

/-! # The phase spectrum of a relative unitary -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation.DensityWitnesses.Polar
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- Diagonalize the relative unitary itself. The same columns test its
real part and its distance from identity. -/
theorem unitary_phase_basis (U : unitaryGroup I ℂ) :
    ∃ V : unitaryGroup I ℂ, ∃ p : I → ℂ, (∀ i, ‖p i‖=1) ∧
      star V.val*U.val*V.val=diagonal p := by
  classical
  have hu := Unitary.mem_iff.mp U.property
  obtain ⟨b,hb⟩ := exists_orthonormalBasis_eigen_of_pairwise_commute_star
    (fun _ : Unit => U.val) (fun _ _ => Commute.refl _) (fun _ _ => hu.2.trans hu.1.symm)
  let e := Fintype.equivFin I
  let v := b.reindex e.symm
  let std := EuclideanSpace.basisFun I ℂ
  let V : unitaryGroup I ℂ := ⟨std.toBasis.toMatrix v,std.toMatrix_orthonormalBasis_mem_unitary v⟩
  have hcol (i j : I) : V.val i j=b (e j) i := by
    change v j i=_
    rw [show v j=b (e j) from b.reindex_apply e.symm j]
  choose p hp using fun j : I => hb () (e j)
  have he : U.val*V.val=V.val*diagonal p := by
    ext i j
    rw [mul_diagonal,mul_apply,hcol]
    simp only [hcol]
    have hi := congrArg (fun z : EuclideanSpace ℂ I => z i) (hp j)
    simpa only [toLpLin_apply,mulVec,dotProduct,PiLp.smul_apply,smul_eq_mul,mul_comm (p j)] using hi
  have hd : star V.val*U.val*V.val=diagonal p := by
    rw [mul_assoc,he,←mul_assoc,(Unitary.mem_iff.mp V.property).1,one_mul]
  refine ⟨V,p,?_,hd⟩
  have hunit : diagonal p∈unitaryGroup I ℂ :=
    hd ▸ mul_mem (mul_mem (V⁻¹).property U.property) V.property
  rw [mem_unitaryGroup_iff,star_eq_conjTranspose,diagonal_conjTranspose,diagonal_mul_diagonal] at hunit
  intro i
  have hi := congrArg (fun M : Mat I => ‖M i i‖) hunit
  simp only [diagonal_apply_eq,one_apply_eq,norm_one,norm_mul] at hi
  change ‖p i‖*‖star (p i)‖=1 at hi
  rw [norm_star] at hi
  nlinarith only [hi,norm_nonneg (p i)]

#print axioms unitary_phase_basis
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation.DensityWitnesses.Polar

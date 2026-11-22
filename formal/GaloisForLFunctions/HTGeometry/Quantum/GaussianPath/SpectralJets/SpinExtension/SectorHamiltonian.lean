import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.SchurTangent
import GaloisForLFunctions.HTGeometry.ParametricSpectralBranch

/-! # Restoring the physical energy and spin splitting -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

def sectorMatrix (H W V : Mat I) (d : ℂ) : Mat (I ⊕ I) :=
  fromBlocks (H+d • 1) W V (H-d • 1)

theorem scalar_eq_smul (z : ℂ) : scalar I z = z • (1 : Mat I) := by
  ext i j
  by_cases hij : i=j <;> simp [scalar_apply,hij]

/-- The determinant is multiplied only by the row scaling uᴰ. The old energy
coordinate e is measured from the added spin energy d. -/
theorem splitDet_physical (H W V : Mat I) (d u e : ℂ) :
    splitDet (scalar I e-H) W V (u*(2*d)) u =
      u^(Fintype.card I)*matrixCharpolyRelation (sectorMatrix H W V d,e+d) := by
  let A := scalar I e-H
  let R := fromBlocks (1 : Mat I) (0 : Mat I) (0 : Mat I) (u • (1 : Mat I))
  have hR : R.det=u^(Fintype.card I) := by simp [R,det_fromBlocks_zero₂₁]
  have hab : scalar (I⊕I) (e+d)-sectorMatrix H W V d = fromBlocks A (-W) (-V) (A+(2*d) • 1) := by
    rw [scalar_eq_smul (I := I⊕I),←fromBlocks_one (l := I) (m := I),fromBlocks_smul,sectorMatrix,
      sub_eq_add_neg,fromBlocks_neg,fromBlocks_add]
    simp only [smul_zero,zero_add]
    congr 1 <;> simp only [A,scalar_eq_smul,add_smul,sub_eq_add_neg,neg_add_rev,neg_neg,two_mul] <;> abel
  have hm : R * (scalar (I⊕I) (e+d)-sectorMatrix H W V d) =
      fromBlocks A (-W) (-(u • V)) ((u*(2*d)) • 1+u • A) := by
    rw [hab]
    dsimp only [R]
    rw [fromBlocks_multiply]
    simp only [one_mul,zero_mul,zero_add,add_zero,Matrix.smul_mul,smul_neg,smul_add,smul_smul,
      add_comm (u • A)]
  change _ = u^(Fintype.card I)*(scalar (I⊕I) (e+d)-sectorMatrix H W V d).det
  rw [←hR,←det_mul,hm]
  rfl

/-- Interchanging the two spin sectors exchanges the transverse blocks and
changes the sign of the added energy. -/
theorem sector_swap (H W V : Mat I) (d z : ℂ) :
    matrixCharpolyRelation (sectorMatrix H V W (-d),z) =
      matrixCharpolyRelation (sectorMatrix H W V d,z) := by
  let e := Equiv.sumComm I I
  have he : sectorMatrix H V W (-d) = Matrix.reindex e e (sectorMatrix H W V d) := by
    change _ = (sectorMatrix H W V d).submatrix Sum.swap Sum.swap
    simp only [sectorMatrix,fromBlocks_submatrix_sum_swap_sum_swap,neg_smul,sub_eq_add_neg,neg_neg]
  simp only [matrixCharpolyRelation,←Matrix.eval_charpoly,he,Matrix.charpoly_reindex]

end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension

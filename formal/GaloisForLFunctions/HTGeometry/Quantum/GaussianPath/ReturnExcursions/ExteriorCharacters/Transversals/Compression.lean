import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.ArcCoefficients
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-! # Determinants of isometric compressions of a unitary near the identity -/

open Matrix Polynomial WithLp
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.Transversals
noncomputable section
private abbrev Space (I : Type*) := EuclideanSpace ℂ I
private def act {I J : Type*} [Fintype J] (B : Matrix I J ℂ) (x : Space J) : Space I :=
  toLp 2 (B *ᵥ ofLp x)

private theorem act_mul {I J K : Type*} [Fintype J] [Fintype K]
    (A : Matrix I J ℂ) (B : Matrix J K ℂ) (x : Space K) : act A (act B x)=act (A*B) x :=
  congrArg (toLp 2) (mulVec_mulVec ..)

private theorem adjoint_inner {I J : Type*} [Fintype I] [Fintype J]
    (B : Matrix I J ℂ) (x : Space J) (y : Space I) :
    inner ℂ (act B x) y=inner ℂ x (act B.conjTranspose y) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct,EuclideanSpace.inner_eq_star_dotProduct]
  change ofLp y ⬝ᵥ star (B *ᵥ ofLp x)=(B.conjTranspose *ᵥ ofLp y) ⬝ᵥ star (ofLp x)
  rw [star_mulVec,dotProduct_comm (ofLp y),←dotProduct_mulVec,dotProduct_comm]

private theorem act_one {I : Type*} [Fintype I] [DecidableEq I] (x : Space I) :
    act (1 : Matrix I I ℂ) x=x := (ofLp_injective 2) (one_mulVec _)

private theorem isometry_norm {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (B : Matrix I J ℂ) (hB : B.conjTranspose*B=1) (x : Space J) :
    ‖act B x‖=‖x‖ := by
  have hh := congrArg Complex.re (adjoint_inner B x (act B x))
  rw [act_mul,hB,act_one] at hh
  change RCLike.re (inner ℂ (act B x) (act B x))=RCLike.re (inner ℂ x x) at hh
  simp only [inner_self_eq_norm_sq] at hh
  nlinarith only [hh,norm_nonneg (act B x),norm_nonneg x]

private theorem compression_root {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (Y : unitary (Matrix I I ℂ)) (B : Matrix I J ℂ) (hB : B.conjTranspose*B=1)
    {e : ℝ} (hfit : ‖1-Y.val‖≤e) {z : ℂ} (hz : z∈spectrum ℂ (B.conjTranspose*Y.val*B)) :
    1-e^2/2≤z.re := by
  rw [←Matrix.spectrum_toLin'] at hz
  obtain ⟨u,hu⟩ := (Module.End.HasEigenvalue.of_mem_spectrum hz).exists_hasEigenvector
  let x : Space J := toLp 2 u
  let y := act B x
  have hy : ‖y‖=‖x‖ := isometry_norm B hB x
  have hY : ‖act Y.val y‖=‖y‖ := isometry_norm Y.val (Unitary.mem_iff.mp Y.property).1 y
  have hact : act (B.conjTranspose*Y.val*B) x=z • x :=
    (ofLp_injective 2) hu.apply_eq_smul
  have hinner : inner ℂ y (act Y.val y)=z*(‖x‖^2:ℝ) := by
    change inner ℂ (act B x) (act Y.val (act B x))=_
    rw [adjoint_inner,act_mul,act_mul,hact,inner_smul_right,inner_self_eq_norm_sq_to_K]
    norm_cast
  have hdiff : act (1-Y.val) y=y-act Y.val y := by
    apply ofLp_injective 2
    exact (sub_mulVec ..).trans (congrArg (· - Y.val *ᵥ ofLp y) (one_mulVec _))
  have hd : ‖y-act Y.val y‖≤e*‖y‖ := by
    rw [←hdiff]
    exact ((1-Y.val).l2_opNorm_mulVec y).trans (mul_le_mul_of_nonneg_right hfit (norm_nonneg _))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hd 2
  rw [norm_sub_sq (𝕜:=ℂ),hinner,hY,hy] at hs
  change ‖x‖^2-2*(z*(‖x‖^2:ℝ)).re+‖x‖^2≤(e*‖x‖)^2 at hs
  rw [Complex.re_mul_ofReal] at hs
  have hn : 0<‖x‖ := norm_pos_iff.mpr (fun h => hu.2 (congrArg ofLp h))
  apply le_of_mul_le_mul_right _ (sq_pos_of_pos hn)
  nlinarith only [hs]

/-- Every root of the compressed unitary has real part at least
`1-e²/2`. Their product bounds the modulus of the compression determinant. -/
theorem compression_det {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (Y : unitary (Matrix I I ℂ)) (B : Matrix I J ℂ) (hB : B.conjTranspose*B=1)
    {e : ℝ} (hfit : ‖1-Y.val‖≤e) (hc : 0≤1-e^2/2) :
    (1-e^2/2)^Fintype.card J≤‖(B.conjTranspose*Y.val*B).det‖ := by
  let A := B.conjTranspose*Y.val*B
  have hroot : A.charpoly.rootSet ℂ ⊆ {z | 1-e^2/2≤z.re} := by
    intro z hz
    apply compression_root Y B hB hfit
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    simpa only [IsRoot.def,coe_aeval_eq_eval] using (mem_rootSet.mp hz).2
  have h := coefficient_floor A.charpoly hc hroot 0 (Nat.zero_le _)
  change (1-e^2/2)^Fintype.card J≤‖A.det‖
  rw [A.det_eq_sign_charpoly_coeff,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
  simpa [A.charpoly_monic.leadingCoeff,A.charpoly_natDegree_eq_dim] using h

#print axioms compression_det
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.Transversals

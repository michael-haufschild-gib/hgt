import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension
import GaloisForLFunctions.HTGeometry.PauliCommutatorReturnTubeLaw

/-! # Spectral dephasing and the off-diagonal commutator equation -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev M (I : Type*) := Matrix I I ℂ

/-- Project onto the diagonal in the specified energy eigenbasis. -/
def pinching {H : M I} (hH : H.IsHermitian) (Z : M I) : M I :=
  let U : M I := hH.eigenvectorUnitary
  let B := star U*Z*U
  U*diagonal (fun i => B i i)*star U

theorem pinching_hermitian {H Z : M I} (hH : H.IsHermitian) (hZ : Z.IsHermitian) :
    (pinching hH Z).IsHermitian := by
  let U : M I := hH.eigenvectorUnitary
  let B := star U*Z*U
  let D := diagonal (fun i => B i i)
  have hb : star B=B := by simp only [B,star_mul,star_star,hZ.isSelfAdjoint.star_eq,mul_assoc]
  have hd : star D=D := by
    rw [show star D=Matrix.conjTranspose D from rfl,diagonal_conjTranspose]
    congr 1
    funext i
    exact congrFun (congrFun hb i) i
  change star (U*D*star U)=U*D*star U
  simp only [star_mul,star_star,hd,mul_assoc]

/-- The self-adjoint field obtained by retaining the energy-basis diagonal. -/
def pinchedField (H Z : selfAdjoint (M I)) : selfAdjoint (M I) :=
  ⟨pinching H.2.isHermitian Z.val,(pinching_hermitian H.2.isHermitian Z.2.isHermitian).isSelfAdjoint⟩

private theorem conj_mul (U : M I) (hU : U∈unitary (M I)) (B C : M I) :
    (U*B*star U)*(U*C*star U)=U*(B*C)*star U := by
  simp only [mul_assoc]
  rw [←mul_assoc (star U) U,(Unitary.mem_iff.mp hU).1,one_mul]

/-- For simple H, the dephased field is Hermitian, commutes with H, and
the entire discarded field is a commutator [H,X]. In the energy basis
the off-diagonal entries of X are divided by their energy differences. -/
theorem pinching_commutator {H Z : M I} (hH : H.IsHermitian) (hZ : Z.IsHermitian)
    (hi : Function.Injective hH.eigenvalues) :
    (pinching hH Z).IsHermitian ∧ Commute H (pinching hH Z) ∧
      ∃ X : M I, H*X-X*H=Z-pinching hH Z := by
  let U : M I := hH.eigenvectorUnitary
  let E (i : I) := (hH.eigenvalues i:ℂ)
  let B := star U*Z*U
  let D := diagonal (fun i => B i i)
  let Y : M I := fun i j => B i j/(E i-E j)
  have hu : U∈unitary (M I) := hH.eigenvectorUnitary.2
  have hH' : H=U*diagonal E*star U := isHermitian_eq_conj_diagonal hH
  have hZ' : U*B*star U=Z := by
    calc _ = (U*star U)*Z*(U*star U) := by simp only [B,mul_assoc]
         _ = Z := by rw [(Unitary.mem_iff.mp hu).2,one_mul,mul_one]
  have hDC : diagonal E*D=D*diagonal E := by
    dsimp only [D]
    rw [diagonal_mul_diagonal,diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have heq : diagonal E*Y-Y*diagonal E=B-D := by
    ext i j
    simp only [Matrix.sub_apply,diagonal_mul,mul_diagonal]
    by_cases hij : i=j
    · subst j
      simp [Y,D]
    · have he : E i-E j≠0 := sub_ne_zero.mpr ((Complex.ofReal_injective.comp hi).ne hij)
      rw [show D i j=0 from diagonal_apply_ne _ hij,sub_zero]
      change E i*(B i j/(E i-E j))-(B i j/(E i-E j))*E j=B i j
      field_simp [he]
  change (U*D*star U).IsHermitian ∧ Commute H (U*D*star U) ∧ _
  refine ⟨?_,?_,U*Y*star U,?_⟩
  · exact pinching_hermitian hH hZ
  · change H*(U*D*star U)=(U*D*star U)*H
    rw [hH',conj_mul U hu,conj_mul U hu,hDC]
  · change H*(U*Y*star U)-(U*Y*star U)*H=Z-U*D*star U
    rw [hH',conj_mul U hu,conj_mul U hu,←sub_mul,←mul_sub,heq,mul_sub,sub_mul,hZ']

#print axioms pinching_commutator
end
end GaloisForLFunctions.HTGeometry.Dephasing

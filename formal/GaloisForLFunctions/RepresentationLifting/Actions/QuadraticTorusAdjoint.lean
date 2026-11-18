import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Conjugation on the plane transverse to a quadratic torus

The coefficient matrix of Finkelberg–Kazhdan, Lemma 3.3.1
(arXiv:2610.38371), comes from ordinary conjugation on the matrices
anticommuting with the quadratic generator. Its determinant is one.
The transverse Weyl determinant and the degeneration in characteristic
two follow from the same formulas.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open Matrix
variable {K : Type*} [Field K]
local notation "M" => Matrix (Fin 2) (Fin 2) K

/-- Multiplication matrix of a+b√ε and its norm. -/
def quadraticTorusMatrix (ε a b : K) : M := !![a,b;ε*b,a]
def quadraticTorusNorm (ε a b : K) : K := a^2-ε*b^2

/-- The two-coordinate plane of matrices anticommuting with the quadratic generator. -/
def quadraticAntiPlane (ε x y : K) : M := !![x,y;-ε*y,-x]

/-- Explicit transverse coefficients of the torus action. -/
def quadraticAdjointCoefficients (ε a b : K) : K × K :=
  let d := quadraticTorusNorm ε a b
  ((a^2+ε*b^2)/d,-(2*a*b)/d)

def quadraticAdjointMatrix (ε a b : K) : M :=
  let (u,v) := quadraticAdjointCoefficients ε a b
  !![u,ε*v;v,u]

theorem quadraticTorusMatrix_det (ε a b : K) : (quadraticTorusMatrix ε a b).det = quadraticTorusNorm ε a b := by
  rw [quadraticTorusMatrix,Matrix.det_fin_two_of,quadraticTorusNorm]; ring

/-- Anticommutation recovers the coefficient plane, including in characteristic two. -/
theorem quadraticAntiPlane_range (ε : K) :
    Set.range (fun t : K × K => quadraticAntiPlane ε t.1 t.2) =
      {Y : M | quadraticTorusMatrix ε 0 1 * Y = -(Y * quadraticTorusMatrix ε 0 1)} := by
  ext Y
  constructor
  · rintro ⟨⟨x,y⟩,rfl⟩
    change quadraticTorusMatrix ε 0 1 * quadraticAntiPlane ε x y =
      -(quadraticAntiPlane ε x y * quadraticTorusMatrix ε 0 1)
    simp only [quadraticTorusMatrix,quadraticAntiPlane,Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
  · intro h
    change quadraticTorusMatrix ε 0 1 * Y = -(Y * quadraticTorusMatrix ε 0 1) at h
    have h₁ := congrArg (fun A : M => A 0 0) h
    have h₂ := congrArg (fun A : M => A 0 1) h
    simp only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.neg_apply] at h₁ h₂
    simp [quadraticTorusMatrix] at h₁ h₂
    refine ⟨(Y 0 0,Y 0 1),?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [quadraticAntiPlane,h₁,h₂]
    ring

/-- Conjugation acts on the two coordinates by the transverse matrix from Lemma 3.3.1. -/
theorem quadraticTorus_conjugates_plane (ε a b x y : K) (hd : quadraticTorusNorm ε a b ≠ 0) :
    let (u,v) := quadraticAdjointCoefficients ε a b
    let A := quadraticTorusMatrix ε a b
    A * quadraticAntiPlane ε x y * A⁻¹ =
      quadraticAntiPlane ε (u*x+ε*v*y) (v*x+u*y) := by
  let A := quadraticTorusMatrix ε a b
  let t := quadraticAdjointCoefficients ε a b
  let Y := quadraticAntiPlane ε (t.1*x+ε*t.2*y) (t.2*x+t.1*y)
  have hinv : IsUnit A.det := isUnit_iff_ne_zero.mpr ((quadraticTorusMatrix_det ε a b).symm ▸ hd)
  have he : A*quadraticAntiPlane ε x y = Y*A := by
    dsimp only [A,Y,t,quadraticAntiPlane,quadraticTorusMatrix,quadraticAdjointCoefficients]
    rw [Matrix.mul_fin_two,Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp [hd] <;> unfold quadraticTorusNorm <;> ring
  change A * quadraticAntiPlane ε x y * A⁻¹ = Y
  rw [he,mul_assoc,Matrix.mul_nonsing_inv A hinv,mul_one]

/-- The transverse matrix preserves the alternating area form. -/
theorem quadraticAdjointMatrix_det (ε a b : K) (hd : quadraticTorusNorm ε a b ≠ 0) :
    (quadraticAdjointMatrix ε a b).det = 1 := by
  rw [quadraticAdjointMatrix,quadraticAdjointCoefficients,Matrix.det_fin_two_of]
  field_simp [hd]
  unfold quadraticTorusNorm; ring

/-- The Weyl determinant on the coefficient plane is -4εb² divided by the norm. -/
theorem quadraticAdjoint_weyl (ε a b : K) (hd : quadraticTorusNorm ε a b ≠ 0) :
    (1-quadraticAdjointMatrix ε a b).det = -(4*ε*b^2)/quadraticTorusNorm ε a b := by
  have hdet := quadraticAdjointMatrix_det ε a b hd
  rw [Matrix.det_fin_two] at hdet ⊢
  simp [quadraticAdjointMatrix,quadraticAdjointCoefficients,Matrix.sub_apply] at hdet ⊢
  field_simp [hd]
  unfold quadraticTorusNorm
  ring

/-- Away from characteristic two and a degenerate norm, the transverse determinant
vanishes exactly on the scalar subgroup. -/
theorem quadraticAdjoint_weyl_zero_iff {ε a b : K} (hc : (2:K) ≠ 0) (he : ε ≠ 0)
    (hd : quadraticTorusNorm ε a b ≠ 0) : (1-quadraticAdjointMatrix ε a b).det = 0 ↔ b=0 := by
  have h4 : (4:K) ≠ 0 := by rw [show (4:K) = 2*2 by norm_num]; exact mul_ne_zero hc hc
  rw [quadraticAdjoint_weyl ε a b hd]
  simp [div_eq_zero_iff,hd,he,h4]

/-- In characteristic two the entire action on this plane is trivial. -/
theorem quadraticAdjoint_char_two (ε a b : K) [CharP K 2] (hd : quadraticTorusNorm ε a b ≠ 0) :
    quadraticAdjointMatrix ε a b = 1 := by
  have h2 : (2:K) = 0 := CharP.cast_eq_zero K 2
  have hadd : a^2 + ε*b^2 = quadraticTorusNorm ε a b := by
    unfold quadraticTorusNorm
    linear_combination (ε*b^2)*h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quadraticAdjointMatrix,quadraticAdjointCoefficients,h2,hadd,hd]

#print axioms quadraticTorusMatrix_det
#print axioms quadraticAntiPlane_range
#print axioms quadraticTorus_conjugates_plane
#print axioms quadraticAdjointMatrix_det
#print axioms quadraticAdjoint_weyl
#print axioms quadraticAdjoint_weyl_zero_iff
#print axioms quadraticAdjoint_char_two

end GaloisForLFunctions.RepresentationLifting

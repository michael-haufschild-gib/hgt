import GaloisForLFunctions.RHTower.RealCoronaFixedCrossedProductKZero
import Mathlib.Data.Matrix.Basic

/-!
# Free-orbit reflection crossed product as a matrix block

For the free two-point `C₂` orbit, the function algebra crossed with reflection is exactly the
full two-by-two complex matrix algebra.  This is the free-orbit companion to the fixed-sector
Fourier splitting in `RealCoronaFixedCrossedProductKZero`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Left-translation reflection action on functions over the free two-point orbit. -/
@[reducible] def freeCoordinateFunctionAction :
    MulSemiringAction ReflectionParity (ReflectionParity → ℂ) where
  smul p f q := f (p * q)
  one_smul f := by funext q; cases q <;> rfl
  mul_smul p q f := by
    funext r
    cases p <;> cases q <;> cases r <;> rfl
  smul_zero p := by funext q; rfl
  smul_add p f g := by funext q; rfl
  smul_one p := by funext q; rfl
  smul_mul p f g := by funext q; rfl

@[simp] theorem freeCoordinateFunction_smul_apply
    (p : ReflectionParity) (f : ReflectionParity → ℂ) (q : ReflectionParity) :
    letI := freeCoordinateFunctionAction
    (p • f) q = f (p * q) := by
  rfl

/-- Free-orbit reflection commutes with complex scalar multiplication. -/
theorem freeCoordinateFunction_smulCommClass :
    letI := freeCoordinateFunctionAction
    SMulCommClass ReflectionParity ℂ (ReflectionParity → ℂ) := by
  letI := freeCoordinateFunctionAction
  constructor
  intro p c f
  funext q
  rfl

/-- Regular crossed-product representation on the free orbit. -/
def freeReflectionMatrixToFun
    (F : SkewMonoidAlgebra (ReflectionParity → ℂ) ReflectionParity) :
    Matrix ReflectionParity ReflectionParity ℂ :=
  fun p q => if q = p then F.coeff ReflectionParity.even p
    else F.coeff ReflectionParity.odd p

/-- Inverse regular-representation transform. -/
def freeReflectionMatrixInvFun
    (M : Matrix ReflectionParity ReflectionParity ℂ) :
    SkewMonoidAlgebra (ReflectionParity → ℂ) ReflectionParity :=
  SkewMonoidAlgebra.single ReflectionParity.even (fun p => M p p) +
    SkewMonoidAlgebra.single ReflectionParity.odd
      (fun p => M p (ReflectionParity.odd * p))

theorem freeReflectionMatrixInvFun_leftInverse :
    letI := freeCoordinateFunctionAction
    Function.LeftInverse freeReflectionMatrixInvFun freeReflectionMatrixToFun := by
  letI := freeCoordinateFunctionAction
  intro F
  rw [reflectionParity_decompose F]
  ext g p
  cases g <;> cases p <;>
    simp [freeReflectionMatrixToFun, freeReflectionMatrixInvFun]

theorem freeReflectionMatrixInvFun_rightInverse :
    letI := freeCoordinateFunctionAction
    Function.RightInverse freeReflectionMatrixInvFun freeReflectionMatrixToFun := by
  letI := freeCoordinateFunctionAction
  intro M
  ext p q
  cases p <;> cases q <;>
    simp [freeReflectionMatrixToFun, freeReflectionMatrixInvFun]

theorem sum_reflectionParity (f : ReflectionParity → ℂ) :
    ∑ p, f p = f ReflectionParity.even + f ReflectionParity.odd := by
  classical
  rw [show (Finset.univ : Finset ReflectionParity) =
      {ReflectionParity.even, ReflectionParity.odd} by
        ext p
        cases p <;> simp]
  simp

theorem freeReflectionMatrixToFun_mul
    (F H : SkewMonoidAlgebra (ReflectionParity → ℂ) ReflectionParity) :
    letI := freeCoordinateFunctionAction
    freeReflectionMatrixToFun (F * H) =
      freeReflectionMatrixToFun F * freeReflectionMatrixToFun H := by
  letI := freeCoordinateFunctionAction
  rw [reflectionParity_decompose F, reflectionParity_decompose H]
  ext p q
  cases p <;> cases q
  <;> simp only [mul_add, add_mul]
  <;> simp [freeReflectionMatrixToFun, freeCoordinateFunction_smul_apply,
    SkewMonoidAlgebra.single_mul_single, Matrix.mul_apply, sum_reflectionParity]
  <;> ring

/-- Exact matrix normal form for the crossed product of a free `C₂` orbit. -/
def freeReflectionMatrixRingEquiv :
    letI := freeCoordinateFunctionAction
    SkewMonoidAlgebra (ReflectionParity → ℂ) ReflectionParity ≃+*
      Matrix ReflectionParity ReflectionParity ℂ := by
  letI := freeCoordinateFunctionAction
  exact
    { toFun := freeReflectionMatrixToFun
      invFun := freeReflectionMatrixInvFun
      left_inv := freeReflectionMatrixInvFun_leftInverse
      right_inv := freeReflectionMatrixInvFun_rightInverse
      map_mul' := freeReflectionMatrixToFun_mul
      map_add' := by
        intro F H
        ext p q
        simp [freeReflectionMatrixToFun]
        split_ifs <;> simp }

/-- Sign orientation on the two points of a free reflection orbit. -/
def freeOrbitOrientation : ReflectionParity → ℂ
  | .even => 1
  | .odd => -1

/-- Free-orbit orientation as a degree-zero crossed-product coefficient. -/
def freeOrbitOrientationCrossed :
    SkewMonoidAlgebra (ReflectionParity → ℂ) ReflectionParity :=
  SkewMonoidAlgebra.single (1 : ReflectionParity) freeOrbitOrientation

/-- Diagonal grading matrix corresponding to the free-orbit orientation. -/
def freeOrbitOrientationMatrix : Matrix ReflectionParity ReflectionParity ℂ :=
  fun p q => if q = p then freeOrbitOrientation p else 0

/-- Under the free-orbit normal form, the corona orientation is exactly the sign grading. -/
theorem freeReflectionMatrixRingEquiv_orientation :
    letI := freeCoordinateFunctionAction
    freeReflectionMatrixRingEquiv freeOrbitOrientationCrossed =
      freeOrbitOrientationMatrix := by
  letI := freeCoordinateFunctionAction
  ext p q
  cases p <;> cases q <;>
    simp [freeReflectionMatrixRingEquiv, freeReflectionMatrixToFun,
      freeOrbitOrientationCrossed, freeOrbitOrientationMatrix, freeOrbitOrientation]

/-- Atomic detectability law: commutation with the free-orbit orientation kills diagonal entries
and multiplies each off-diagonal entry by the exact difference of its endpoint signs. -/
theorem freeOrbitOrientationMatrix_commutator_entry
    (M : Matrix ReflectionParity ReflectionParity ℂ) (p q : ReflectionParity) :
    (M * freeOrbitOrientationMatrix - freeOrbitOrientationMatrix * M) p q =
      (freeOrbitOrientation q - freeOrbitOrientation p) * M p q := by
  cases p <;> cases q <;>
    simp [Matrix.mul_apply, freeOrbitOrientationMatrix, freeOrbitOrientation]
  <;> ring

end GaloisForLFunctions.RHTower

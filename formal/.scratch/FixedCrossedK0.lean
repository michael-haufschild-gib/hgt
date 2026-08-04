import GaloisForLFunctions.RHTower.RealCoronaKZeroMultiplicityFracture
import GaloisForLFunctions.RHTower.RealCoronaHolomorphicReflectionCrossedProduct

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

def fixedCoordinateFunctionAction (ι : Type*) :
    MulSemiringAction ReflectionParity (ι → ℂ) where
  smul _ f := f
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

theorem fixedCoordinateFunction_smulCommClass (ι : Type*) :
    letI := fixedCoordinateFunctionAction ι
    SMulCommClass ReflectionParity ℂ (ι → ℂ) := by
  letI := fixedCoordinateFunctionAction ι
  constructor
  intro _ _ _
  rfl

theorem reflectionParity_decompose {A : Type*} [Semiring A]
    [MulSemiringAction ReflectionParity A]
    (F : SkewMonoidAlgebra A ReflectionParity) :
    F = SkewMonoidAlgebra.single ReflectionParity.even (F.coeff ReflectionParity.even) +
      SkewMonoidAlgebra.single ReflectionParity.odd (F.coeff ReflectionParity.odd) := by
  ext p
  cases p <;> simp

def fixedReflectionFourierToFun (ι : Type*)
    (F : SkewMonoidAlgebra (ι → ℂ) ReflectionParity) : (ι → ℂ) × (ι → ℂ) :=
  (F.coeff ReflectionParity.even + F.coeff ReflectionParity.odd,
    F.coeff ReflectionParity.even - F.coeff ReflectionParity.odd)

def fixedReflectionFourierInvFun (ι : Type*)
    (p : (ι → ℂ) × (ι → ℂ)) : SkewMonoidAlgebra (ι → ℂ) ReflectionParity :=
  SkewMonoidAlgebra.single ReflectionParity.even ((p.1 + p.2) / 2) +
    SkewMonoidAlgebra.single ReflectionParity.odd ((p.1 - p.2) / 2)

theorem fixedReflectionFourierInvFun_leftInverse (ι : Type*) :
    Function.LeftInverse (fixedReflectionFourierInvFun ι)
      (fixedReflectionFourierToFun ι) := by
  intro F
  rw [reflectionParity_decompose F]
  ext p i
  cases p <;> simp [fixedReflectionFourierToFun, fixedReflectionFourierInvFun]
  <;> ring

theorem fixedReflectionFourierInvFun_rightInverse (ι : Type*) :
    Function.RightInverse (fixedReflectionFourierInvFun ι)
      (fixedReflectionFourierToFun ι) := by
  intro p
  apply Prod.ext <;> funext i
  <;> simp [fixedReflectionFourierToFun, fixedReflectionFourierInvFun]
  <;> ring

theorem fixedReflectionFourierToFun_mul (ι : Type*)
    (F H : SkewMonoidAlgebra (ι → ℂ) ReflectionParity) :
    letI := fixedCoordinateFunctionAction ι
    fixedReflectionFourierToFun ι (F * H) =
      fixedReflectionFourierToFun ι F * fixedReflectionFourierToFun ι H := by
  letI := fixedCoordinateFunctionAction ι
  rw [reflectionParity_decompose F, reflectionParity_decompose H]
  apply Prod.ext <;> funext i
  <;> simp [fixedReflectionFourierToFun, SkewMonoidAlgebra.single_mul_single,
    fixedCoordinateFunctionAction]
  <;> ring

def fixedReflectionFourierAlgEquiv (ι : Type*) :
    letI := fixedCoordinateFunctionAction ι
    SkewMonoidAlgebra (ι → ℂ) ReflectionParity ≃ₐ[ℂ] ((ι → ℂ) × (ι → ℂ)) := by
  letI := fixedCoordinateFunctionAction ι
  letI : SMulCommClass ReflectionParity ℂ (ι → ℂ) :=
    fixedCoordinateFunction_smulCommClass ι
  exact
    { toFun := fixedReflectionFourierToFun ι
      invFun := fixedReflectionFourierInvFun ι
      left_inv := fixedReflectionFourierInvFun_leftInverse ι
      right_inv := fixedReflectionFourierInvFun_rightInverse ι
      map_mul' := fixedReflectionFourierToFun_mul ι
      map_add' := by
        intro F H
        apply Prod.ext <;> funext i <;> simp [fixedReflectionFourierToFun]
      map_smul' := by
        intro c F
        apply Prod.ext <;> funext i <;> simp [fixedReflectionFourierToFun]
      commutes' := by
        intro c
        apply Prod.ext <;> funext i
        <;> simp [fixedReflectionFourierToFun, Algebra.algebraMap_eq_smul_one] }

theorem fixedReflectionFourierAlgEquiv_coefficient (ι : Type*) (a : ι → ℂ) :
    letI := fixedCoordinateFunctionAction ι
    fixedReflectionFourierAlgEquiv ι
        (SkewMonoidAlgebra.single (1 : ReflectionParity) a) = (a, a) := by
  letI := fixedCoordinateFunctionAction ι
  letI : SMulCommClass ReflectionParity ℂ (ι → ℂ) :=
    fixedCoordinateFunction_smulCommClass ι
  apply Prod.ext <;> funext i
  <;> simp [fixedReflectionFourierAlgEquiv, fixedReflectionFourierToFun]

end GaloisForLFunctions.RHTower

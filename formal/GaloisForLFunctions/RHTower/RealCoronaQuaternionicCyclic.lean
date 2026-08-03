import GaloisForLFunctions.RHTower.KRealCyclicWord
import GaloisForLFunctions.RHTower.KRealStructureRealization
import GaloisForLFunctions.RHTower.SeamSuspensionTrace

/-!
# Real-corona quaternionic and cyclic algebra

This file formalizes the algebraic core of the Real-corona construction.  An
idempotent exchanged with its complement by a Real involution produces an odd
quaternionic structure.  A fixed Real sector gives the exact defect of its
square.  After adjoining the functional-equation involution, the orientation
is a commutator and hence invisible to every additive cyclic trace, while an
explicit graded matrix model detects it.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

/-- Orientation attached to an idempotent splitting. -/
def realCoronaOrientation {A : Type*} [Ring A] (e : A) : A :=
  2 * e - 1

theorem realCoronaOrientation_sq {A : Type*} [Ring A] {e : A}
    (he : IsIdempotentElem e) :
    realCoronaOrientation e * realCoronaOrientation e = 1 := by
  rw [IsIdempotentElem] at he
  simp only [realCoronaOrientation]
  calc
    (2 * e - 1) * (2 * e - 1) = 4 * (e * e) - 4 * e + 1 := by
      noncomm_ring
    _ = 1 := by rw [he]; noncomm_ring

/-- An even Real module over an even Real algebra. -/
structure RealCoronaModule
    (A V : Type*) [Ring A] [Algebra ℂ A]
    [AddCommGroup V] [Module ℂ V] [Module A V]
    [IsScalarTower ℂ A V] [SMulCommClass ℂ A V]
    (K : KRealAlgebraStructure A) where
  real : KRealStructure false V
  sigma_smul : ∀ a x, real.sigma (a • x) = K.sigma a • real.sigma x

theorem KRealAlgebraStructure.sigma_realCoronaOrientation
    {A : Type*} [Ring A] [Algebra ℂ A]
    (K : KRealAlgebraStructure A) {e : A}
    (heSigma : K.sigma e = 1 - e) :
    K.sigma (realCoronaOrientation e) = -realCoronaOrientation e := by
  simp only [realCoronaOrientation]
  rw [map_sub, K.map_mul, K.map_one, heSigma]
  have htwo : K.sigma (2 : A) = 2 := by
    calc
      K.sigma (2 : A) = K.sigma (1 + 1) := by norm_num
      _ = K.sigma 1 + K.sigma 1 := map_add K.sigma 1 1
      _ = 2 := by rw [K.map_one]; norm_num
  rw [htwo]
  noncomm_ring

/-- Sign-conjugation induced by a Real-corona idempotent. -/
def RealCoronaModule.quaternionicSigma
    {A V : Type*} [Ring A] [Algebra ℂ A]
    [AddCommGroup V] [Module ℂ V] [Module A V]
    [IsScalarTower ℂ A V] [SMulCommClass ℂ A V]
    {K : KRealAlgebraStructure A}
    (M : RealCoronaModule A V K) (e : A) :
    V →ₗ⋆[ℂ] V where
  toFun x := realCoronaOrientation e • M.real.sigma x
  map_add' x y := by simp
  map_smul' c x := by
    rw [map_smulₛₗ]
    exact smul_comm (realCoronaOrientation e) (starRingEnd ℂ c) (M.real.sigma x)

theorem RealCoronaModule.quaternionicSigma_sq
    {A V : Type*} [Ring A] [Algebra ℂ A]
    [AddCommGroup V] [Module ℂ V] [Module A V]
    [IsScalarTower ℂ A V] [SMulCommClass ℂ A V]
    {K : KRealAlgebraStructure A}
    (M : RealCoronaModule A V K) {e : A}
    (he : IsIdempotentElem e) (heSigma : K.sigma e = 1 - e)
    (x : V) :
    M.quaternionicSigma e (M.quaternionicSigma e x) = -x := by
  change realCoronaOrientation e •
      M.real.sigma (realCoronaOrientation e • M.real.sigma x) = -x
  rw [M.sigma_smul, K.sigma_realCoronaOrientation heSigma]
  rw [M.real.sq]
  simp only [kRealParityAction, Bool.false_eq_true, ↓reduceIte]
  rw [smul_smul, show realCoronaOrientation e * -realCoronaOrientation e = -1 by
    rw [mul_neg, realCoronaOrientation_sq he]]
  simp

/-- Real-corona sign-conjugation as an odd `K_R` object. -/
def RealCoronaModule.quaternionicKReal
    {A V : Type*} [Ring A] [Algebra ℂ A]
    [AddCommGroup V] [Module ℂ V] [Module A V]
    [IsScalarTower ℂ A V] [SMulCommClass ℂ A V]
    {K : KRealAlgebraStructure A}
    (M : RealCoronaModule A V K) (e : A)
    (he : IsIdempotentElem e) (heSigma : K.sigma e = 1 - e) :
    KRealStructure true V where
  sigma := M.quaternionicSigma e
  sq x := by
    rw [M.quaternionicSigma_sq he heSigma]
    rfl

/-- Orientation of the nonreal summand in a three-sector splitting. -/
def realCoronaNonrealOrientation {A : Type*} [Ring A]
    (ePlus eMinus : A) : A :=
  ePlus - eMinus

theorem realCoronaNonrealOrientation_sq
    {A : Type*} [Ring A] {ePlus eReal eMinus : A}
    (hPlus : IsIdempotentElem ePlus)
    (hMinus : IsIdempotentElem eMinus)
    (hPlusMinus : ePlus * eMinus = 0)
    (hMinusPlus : eMinus * ePlus = 0)
    (hSum : ePlus + eReal + eMinus = 1) :
    realCoronaNonrealOrientation ePlus eMinus *
        realCoronaNonrealOrientation ePlus eMinus = 1 - eReal := by
  rw [IsIdempotentElem] at hPlus hMinus
  simp only [realCoronaNonrealOrientation]
  calc
    (ePlus - eMinus) * (ePlus - eMinus) =
        ePlus * ePlus - ePlus * eMinus - eMinus * ePlus + eMinus * eMinus := by
      noncomm_ring
    _ = ePlus + eMinus := by
      rw [hPlus, hMinus, hPlusMinus, hMinusPlus]
      simp
    _ = 1 - eReal := by
      apply eq_sub_iff_add_eq.mpr
      calc
        (ePlus + eMinus) + eReal = ePlus + eReal + eMinus := by abel
        _ = 1 := hSum

theorem KRealAlgebraStructure.sigma_realCoronaNonrealOrientation
    {A : Type*} [Ring A] [Algebra ℂ A]
    (K : KRealAlgebraStructure A) {ePlus eMinus : A}
    (hPlus : K.sigma ePlus = eMinus)
    (hMinus : K.sigma eMinus = ePlus) :
    K.sigma (realCoronaNonrealOrientation ePlus eMinus) =
      -realCoronaNonrealOrientation ePlus eMinus := by
  simp [realCoronaNonrealOrientation, hPlus, hMinus]

/-- Partial sign-conjugation retained after isolating a real obstruction sector. -/
def RealCoronaModule.partialQuaternionicSigma
    {A V : Type*} [Ring A] [Algebra ℂ A]
    [AddCommGroup V] [Module ℂ V] [Module A V]
    [IsScalarTower ℂ A V] [SMulCommClass ℂ A V]
    {K : KRealAlgebraStructure A}
    (M : RealCoronaModule A V K) (ePlus eMinus : A) :
    V →ₗ⋆[ℂ] V where
  toFun x := realCoronaNonrealOrientation ePlus eMinus • M.real.sigma x
  map_add' x y := by simp
  map_smul' c x := by
    rw [map_smulₛₗ]
    exact smul_comm (realCoronaNonrealOrientation ePlus eMinus)
      (starRingEnd ℂ c) (M.real.sigma x)

theorem RealCoronaModule.partialQuaternionicSigma_sq
    {A V : Type*} [Ring A] [Algebra ℂ A]
    [AddCommGroup V] [Module ℂ V] [Module A V]
    [IsScalarTower ℂ A V] [SMulCommClass ℂ A V]
    {K : KRealAlgebraStructure A}
    (M : RealCoronaModule A V K) {ePlus eReal eMinus : A}
    (hPlus : IsIdempotentElem ePlus)
    (hMinus : IsIdempotentElem eMinus)
    (hPlusMinus : ePlus * eMinus = 0)
    (hMinusPlus : eMinus * ePlus = 0)
    (hSum : ePlus + eReal + eMinus = 1)
    (hSigmaPlus : K.sigma ePlus = eMinus)
    (hSigmaMinus : K.sigma eMinus = ePlus)
    (x : V) :
    M.partialQuaternionicSigma ePlus eMinus
        (M.partialQuaternionicSigma ePlus eMinus x) =
      -((1 - eReal) • x) := by
  change realCoronaNonrealOrientation ePlus eMinus •
      M.real.sigma
        (realCoronaNonrealOrientation ePlus eMinus • M.real.sigma x) =
      -((1 - eReal) • x)
  rw [M.sigma_smul,
    K.sigma_realCoronaNonrealOrientation hSigmaPlus hSigmaMinus]
  rw [M.real.sq]
  simp only [kRealParityAction, Bool.false_eq_true, ↓reduceIte]
  rw [smul_smul, show realCoronaNonrealOrientation ePlus eMinus *
      -realCoronaNonrealOrientation ePlus eMinus = -(1 - eReal) by
    rw [mul_neg,
      realCoronaNonrealOrientation_sq hPlus hMinus hPlusMinus hMinusPlus hSum]]
  rw [← neg_smul]

section CrossedProduct

variable {R : Type*} [Ring R]

def realCoronaCrossedX (e u : R) : R := e * u
def realCoronaCrossedY (e u : R) : R := u * e

theorem realCoronaCrossed_xy {e u : R}
    (he : IsIdempotentElem e) (hu : u * u = 1) :
    realCoronaCrossedX e u * realCoronaCrossedY e u = e := by
  rw [IsIdempotentElem] at he
  change e * u * (u * e) = e
  calc
    e * u * (u * e) = e * (u * u) * e := by simp only [mul_assoc]
    _ = e * 1 * e := by rw [hu]
    _ = e := by simp [he]

theorem realCoronaCrossed_yx {e u : R}
    (he : IsIdempotentElem e) (hconj : u * e * u = 1 - e) :
    realCoronaCrossedY e u * realCoronaCrossedX e u = 1 - e := by
  rw [IsIdempotentElem] at he
  change u * e * (e * u) = 1 - e
  calc
    u * e * (e * u) = u * (e * e) * u := by simp only [mul_assoc]
    _ = u * e * u := by rw [he]
    _ = 1 - e := hconj

theorem realCoronaOrientation_eq_commutator {e u : R}
    (he : IsIdempotentElem e) (hu : u * u = 1)
    (hconj : u * e * u = 1 - e) :
    realCoronaOrientation e =
      realCoronaCrossedX e u * realCoronaCrossedY e u -
        realCoronaCrossedY e u * realCoronaCrossedX e u := by
  rw [realCoronaCrossed_xy he hu, realCoronaCrossed_yx he hconj]
  simp [realCoronaOrientation]
  noncomm_ring

theorem realCoronaOrientation_trace_eq_zero
    {G : Type*} [AddCommGroup G] (tau : R →+ G)
    (hcyclic : ∀ a b, tau (a * b) = tau (b * a))
    {e u : R} (he : IsIdempotentElem e) (hu : u * u = 1)
    (hconj : u * e * u = 1 - e) :
    tau (realCoronaOrientation e) = 0 := by
  rw [realCoronaOrientation_eq_commutator he hu hconj, map_sub,
    hcyclic, sub_self]

theorem realCoronaOrientation_anticommutes {e u : R}
    (hu : u * u = 1) (hconj : u * e * u = 1 - e) :
    realCoronaOrientation e * u = -(u * realCoronaOrientation e) := by
  have heu : e * u = u * (1 - e) := by
    calc
      e * u = (u * u) * e * u := by rw [hu, one_mul]
      _ = u * (u * e * u) := by simp only [mul_assoc]
      _ = u * (1 - e) := by rw [hconj]
  simp only [realCoronaOrientation]
  calc
    (2 * e - 1) * u = 2 * (e * u) - u := by noncomm_ring
    _ = 2 * (u * (1 - e)) - u := by rw [heu]
    _ = -(u * (2 * e - 1)) := by noncomm_ring

end CrossedProduct

open Matrix

def realCoronaMatrixGrading : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

def realCoronaMatrixSwap : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

theorem realCoronaMatrixGrading_sq :
    realCoronaMatrixGrading * realCoronaMatrixGrading = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realCoronaMatrixGrading, Matrix.mul_apply]

theorem realCoronaMatrixSwap_sq :
    realCoronaMatrixSwap * realCoronaMatrixSwap = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realCoronaMatrixSwap, Matrix.mul_apply]

theorem realCoronaMatrixGrading_anticommutes_swap :
    realCoronaMatrixGrading * realCoronaMatrixSwap =
      -(realCoronaMatrixSwap * realCoronaMatrixGrading) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realCoronaMatrixGrading, realCoronaMatrixSwap, Matrix.mul_apply]

theorem gradedMatrixTrace_realCoronaMatrixGrading_self :
    _root_.RHTower.gradedMatrixTrace
        realCoronaMatrixGrading realCoronaMatrixGrading = 2 := by
  norm_num [_root_.RHTower.gradedMatrixTrace, realCoronaMatrixGrading,
    Matrix.trace]

end RHTower
end GaloisForLFunctions

import GaloisForLFunctions.HTGeometry.GomesHermiteCoordinateRigidity
import Mathlib.RingTheory.AlgebraTower
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Polynomial coordinates for all connection orbit chains

The degree-m connection orbit basis becomes a free m-component polynomial space.
Its natural index splits into orbit length and seed index by division with remainder.
In these coordinates the connection acts by multiplication by the polynomial variable
on every component, retaining the entire operator rather than a finite truncation.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- The real basis of a finite family of polynomial coordinates, indexed by power and component. -/
def gomesPolynomialOrbitBlockBasis (m : ℕ) : Module.Basis (ℕ × Fin m) ℝ (Fin m → ℝ[X]) :=
  (Polynomial.basisMonomials ℝ).smulTower (Pi.basisFun ℝ[X] (Fin m))

/-- A block basis vector is one monomial in one component. -/
theorem gomesPolynomialOrbitBlockBasis_apply (m k : ℕ) (j : Fin m) :
    gomesPolynomialOrbitBlockBasis m (k, j) = (X : ℝ[X]) ^ k • Pi.single j 1 := by
  classical
  simp only [gomesPolynomialOrbitBlockBasis, Module.Basis.smulTower_apply,
    Polynomial.coe_basisMonomials, Pi.basisFun_apply, ← C_mul_X_pow_eq_monomial, map_one, one_mul]

/-- Multiplication by the polynomial variable on every component. -/
def gomesPolynomialOrbitBlockShift (m : ℕ) :
    (Fin m → ℝ[X]) →ₗ[ℝ] (Fin m → ℝ[X]) :=
  LinearMap.pi fun j => (gomesPolynomialMultiplicationMap X).comp (LinearMap.proj j)

/-- Componentwise evaluation of the polynomial shift. -/
theorem gomesPolynomialOrbitBlockShift_apply (m : ℕ) (P : Fin m → ℝ[X]) (j : Fin m) :
    gomesPolynomialOrbitBlockShift m P j = X * P j := rfl

/-- The block shift increments the power without changing the component. -/
theorem gomesPolynomialOrbitBlockShift_basis (m k : ℕ) (j : Fin m) :
    gomesPolynomialOrbitBlockShift m (gomesPolynomialOrbitBlockBasis m (k, j)) =
      gomesPolynomialOrbitBlockBasis m (k + 1, j) := by
  classical
  rw [gomesPolynomialOrbitBlockBasis_apply, gomesPolynomialOrbitBlockBasis_apply]
  funext i
  simp only [gomesPolynomialOrbitBlockShift_apply, Pi.smul_apply, smul_eq_mul]
  rw [pow_succ]
  ring

/-- Split the natural orbit index into length and one of the finitely many seeds. -/
def gomesPolynomialConnectionOrbitIndex (A : GomesNonconstantPolynomialCoefficient) :
    ℕ ≃ ℕ × Fin A.val.natDegree :=
  @Nat.divModEquiv A.val.natDegree
    ⟨Nat.ne_of_gt (gomesNonconstantPolynomialCoefficient_degree_pos A)⟩

/-- The index split is exactly quotient and remainder. -/
theorem gomesPolynomialConnectionOrbitIndex_apply
    (A : GomesNonconstantPolynomialCoefficient) (n : ℕ) :
    gomesPolynomialConnectionOrbitIndex A n =
      (n / A.val.natDegree, ⟨n % A.val.natDegree,
        Nat.mod_lt n (gomesNonconstantPolynomialCoefficient_degree_pos A)⟩) := rfl

/-- One connection application moves forward in the same orbit chain. -/
theorem gomesPolynomialConnectionOrbitIndex_shift
    (A : GomesNonconstantPolynomialCoefficient) (n : ℕ) :
    gomesPolynomialConnectionOrbitIndex A (n + A.val.natDegree) =
      ((gomesPolynomialConnectionOrbitIndex A n).1 + 1,
        (gomesPolynomialConnectionOrbitIndex A n).2) := by
  apply Prod.ext
  · exact Nat.add_div_right n (gomesNonconstantPolynomialCoefficient_degree_pos A)
  · apply Fin.ext
    exact Nat.add_mod_right n A.val.natDegree

/-- Complete polynomial coordinates for all the orbit chains of a nonconstant connection. -/
def gomesPolynomialConnectionOrbitCoordinates (A : GomesNonconstantPolynomialCoefficient) :
    ℝ[X] ≃ₗ[ℝ] (Fin A.val.natDegree → ℝ[X]) :=
  (gomesPolynomialConnectionOrbitBasis A).equiv
    (gomesPolynomialOrbitBlockBasis A.val.natDegree) (gomesPolynomialConnectionOrbitIndex A)

/-- The coordinate equivalence sends each orbit basis vector to its power/component label. -/
theorem gomesPolynomialConnectionOrbitCoordinates_basis
    (A : GomesNonconstantPolynomialCoefficient) (n : ℕ) :
    gomesPolynomialConnectionOrbitCoordinates A (gomesPolynomialConnectionOrbitBasis A n) =
      gomesPolynomialOrbitBlockBasis A.val.natDegree (gomesPolynomialConnectionOrbitIndex A n) :=
  (gomesPolynomialConnectionOrbitBasis A).equiv_apply n
    (gomesPolynomialOrbitBlockBasis A.val.natDegree) (gomesPolynomialConnectionOrbitIndex A)

/-- The full connection is the componentwise polynomial shift in orbit coordinates. -/
theorem gomesPolynomialConnectionOrbitCoordinates_intertwines
    (A : GomesNonconstantPolynomialCoefficient) :
    (gomesPolynomialConnectionOrbitCoordinates A).toLinearMap.comp
        (gomesPolynomialFirstOrderLinearMap A.val) =
      (gomesPolynomialOrbitBlockShift A.val.natDegree).comp
        (gomesPolynomialConnectionOrbitCoordinates A).toLinearMap := by
  apply (gomesPolynomialConnectionOrbitBasis A).ext
  intro n
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    gomesPolynomialConnectionOrbitBasis_shift, gomesPolynomialConnectionOrbitCoordinates_basis]
  rw [gomesPolynomialConnectionOrbitIndex_shift]
  exact (gomesPolynomialOrbitBlockShift_basis A.val.natDegree
    (gomesPolynomialConnectionOrbitIndex A n).1 (gomesPolynomialConnectionOrbitIndex A n).2).symm

/-- Pointwise form suitable for promoting the equivalence to a polynomial-linear map. -/
theorem gomesPolynomialConnectionOrbitCoordinates_operator
    (A : GomesNonconstantPolynomialCoefficient) (P : ℝ[X]) :
    gomesPolynomialConnectionOrbitCoordinates A (gomesPolynomialFirstOrderLinearMap A.val P) =
      (X : ℝ[X]) • gomesPolynomialConnectionOrbitCoordinates A P :=
  congrArg (fun f : ℝ[X] →ₗ[ℝ] (Fin A.val.natDegree → ℝ[X]) => f P)
    (gomesPolynomialConnectionOrbitCoordinates_intertwines A)

/-- The low-degree monomial seeds give the standard free-module generators. -/
theorem gomesPolynomialConnectionOrbitCoordinates_seed
    (A : GomesNonconstantPolynomialCoefficient) (j : Fin A.val.natDegree) :
    gomesPolynomialConnectionOrbitCoordinates A (X ^ j.val) = Pi.single j 1 := by
  have hb : gomesPolynomialConnectionOrbitBasis A j.val = X ^ j.val := by
    rw [gomesPolynomialConnectionOrbitBasis_apply, gomesPolynomialConnectionOrbitPolynomial]
    simp only [Nat.div_eq_of_lt j.2, Nat.mod_eq_of_lt j.2,
      Function.iterate_zero, id_eq]
  rw [← hb, gomesPolynomialConnectionOrbitCoordinates_basis,
    gomesPolynomialConnectionOrbitIndex_apply]
  simp only [Nat.div_eq_of_lt j.2, Nat.mod_eq_of_lt j.2,
    gomesPolynomialOrbitBlockBasis_apply, pow_zero, one_smul]

end GaloisForLFunctions.HTGeometry

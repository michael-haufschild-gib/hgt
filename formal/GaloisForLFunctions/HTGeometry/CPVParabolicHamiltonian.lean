import GaloisForLFunctions.HTGeometry.CPVTwoModeFock
import GaloisForLFunctions.HTGeometry.MvPolynomialPDerivDegree
import Mathlib

/-!
# Parabolic Hamiltonian and its polynomial-domain boundary

The Hamiltonian numerator in arXiv:2601.07437, equations (7) and (22),
factors into the paired quadrature and its formal Fock adjoint. Its quadrature
has trivial kernel on the actual polynomial domain, by the corpus coordinate
degree bound. The charge-sector decomposition is preserved by this Hamiltonian.
-/
noncomputable section
namespace GaloisForLFunctions.HTGeometry.CPV
open MvPolynomial

/-- Paired annihilation/creation quadrature `a - i b†`. -/
def pairedQuadrature : FockEnd := fockAnn ℂ Bool false - Complex.I • fockCre ℂ Bool true

/-- Formal Fock adjoint `a† + i b` on the polynomial domain. -/
def pairedQuadratureAdjoint : FockEnd := fockCre ℂ Bool false + Complex.I • fockAnn ℂ Bool true

/-- The unscaled physical Hamiltonian numerator. -/
def parabolicHamiltonian : FockEnd := pairCartan - Complex.I • (pairCreate - pairAnn)

/-- Exact noncommutative factorization of the paper's Hamiltonian. -/
theorem parabolicHamiltonian_factor :
    parabolicHamiltonian = pairedQuadratureAdjoint * pairedQuadrature := by
  apply LinearMap.ext
  intro p
  have hI : (C Complex.I : Fock) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  simp [parabolicHamiltonian, pairedQuadratureAdjoint, pairedQuadrature,
    Module.End.mul_apply, MvPolynomial.smul_eq_C_mul,
    GaloisForLFunctions.pderiv_comm true false]
  linear_combination (X true * pderiv true p + p) * hI

/-- The Hamiltonian preserves every number-difference charge sector. -/
theorem parabolicHamiltonian_charge :
    pairCharge * parabolicHamiltonian = parabolicHamiltonian * pairCharge := by
  simp only [parabolicHamiltonian, mul_sub, sub_mul, Algebra.mul_smul_comm,
    smul_mul_assoc, pairCharge_cartan, pairCharge_create, pairCharge_ann]

/-- No nonzero finite polynomial is killed by the parabolic quadrature. -/
theorem pairedQuadrature_eq_zero_iff (p : Fock) : pairedQuadrature p = 0 ↔ p = 0 := by
  constructor
  · intro h
    by_contra hp
    have hd : pderiv false p = C Complex.I * (X true * p) := by
      simpa [pairedQuadrature, MvPolynomial.smul_eq_C_mul] using sub_eq_zero.mp h
    have hC : (C Complex.I : Fock) ≠ 0 := by simp
    have hX : (X true : Fock) ≠ 0 := X_ne_zero true
    have hdne : pderiv false p ≠ 0 := by rw [hd]; exact mul_ne_zero hC (mul_ne_zero hX hp)
    have hdegree := GaloisForLFunctions.degreeOf_pderiv_lt hdne
    rw [hd, degreeOf_mul_eq hC (mul_ne_zero hX hp), degreeOf_mul_eq hX hp,
      degreeOf_C, degreeOf_X_of_ne (by simp : false ≠ true)] at hdegree
    omega
  · rintro rfl
    exact map_zero _

/-- The quadrature is injective on finite polynomial Fock states. -/
theorem pairedQuadrature_injective : Function.Injective pairedQuadrature := by
  intro p q h
  apply sub_eq_zero.mp
  apply (pairedQuadrature_eq_zero_iff (p - q)).mp
  rw [map_sub, h, sub_self]

/-- The physical coupling may be any positive real exponential without changing charge conservation. -/
theorem scaledParabolicHamiltonian_charge (j : ℝ) :
    pairCharge * ((Real.exp j : ℂ) • parabolicHamiltonian) =
      ((Real.exp j : ℂ) • parabolicHamiltonian) * pairCharge := by
  rw [Algebra.mul_smul_comm, smul_mul_assoc, parabolicHamiltonian_charge]

end GaloisForLFunctions.HTGeometry.CPV

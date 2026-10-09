import GaloisForLFunctions.HTGeometry.PaperUniversalVandermondeRegular
import GaloisForLFunctions.HTGeometry.AlternantVandermondeDivisibility

/-!
# Integral antisymmetrization and the universal Vandermonde

The native polynomial-evaluation determinant divisibility theorem applies
to every monomial antisymmetrization over every commutative ring. A
staircase monomial has antisymmetrization exactly the universal
Vandermonde, supplying a normalization without factorial denominators.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial
open scoped BigOperators

noncomputable section

variable (K : Type*) [CommRing K] (n : ℕ)

/-- The signed sum of native root permutations, with integral coefficients. -/
def paperIntegralAntisymmetrization :
    MvPolynomial (Fin n) K →ₗ[K] MvPolynomial (Fin n) K :=
  ∑ e : Equiv.Perm (Fin n), (Equiv.Perm.sign e : ℤ) •
    (rename e : MvPolynomial (Fin n) K →ₐ[K] _).toLinearMap

/-- Antisymmetrization is the literal signed permutation sum. -/
theorem paperIntegralAntisymmetrization_apply (p : MvPolynomial (Fin n) K) :
    paperIntegralAntisymmetrization K n p =
      ∑ e : Equiv.Perm (Fin n), (Equiv.Perm.sign e : ℤ) • rename e p := by
  simp only [paperIntegralAntisymmetrization, LinearMap.sum_apply, LinearMap.smul_apply,
    AlgHom.toLinearMap_apply]

/-- The signed sum transforms by the permutation sign in every characteristic. -/
theorem paperIntegralAntisymmetrization_rename
    (p : MvPolynomial (Fin n) K) (e : Equiv.Perm (Fin n)) :
    rename e (paperIntegralAntisymmetrization K n p) =
      (Equiv.Perm.sign e : ℤ) • paperIntegralAntisymmetrization K n p := by
  simp only [paperIntegralAntisymmetrization_apply, map_sum, map_zsmul, rename_rename]
  have hs := (Function.Bijective.sum_comp (Group.mulLeft_bijective e)
    (fun f : Equiv.Perm (Fin n) => (Equiv.Perm.sign f : ℤ) • rename f p)).symm
  rw [hs, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro f _
  simp only [map_mul, Units.val_mul, smul_smul, ← mul_assoc, Int.units_coe_mul_self,
    one_mul, Equiv.Perm.coe_mul]

/-- Invariant polynomial factors pass through integral antisymmetrization. -/
theorem paperIntegralAntisymmetrization_mul
    (p q : MvPolynomial (Fin n) K) (hp : p.IsSymmetric) :
    paperIntegralAntisymmetrization K n (p * q) =
      p * paperIntegralAntisymmetrization K n q := by
  change ∀ e : Equiv.Perm (Fin n), rename e p = p at hp
  simp only [paperIntegralAntisymmetrization_apply, map_mul, hp, Finset.mul_sum,
    mul_smul_comm]

/-- A monomial signed sum is exactly its native polynomial-evaluation determinant. -/
theorem paperIntegralAntisymmetrization_monomial (m : Fin n →₀ ℕ) (c : K) :
    paperIntegralAntisymmetrization K n (monomial m c) =
      C c * (Matrix.of fun i j : Fin n => (X i : MvPolynomial (Fin n) K) ^ m j).det := by
  have hm : monomial m c = C c * ∏ j : Fin n, (X j : MvPolynomial (Fin n) K) ^ m j := by
    rw [monomial_eq, Finsupp.prod_fintype _ _ fun _ => pow_zero _]
  rw [paperIntegralAntisymmetrization_apply, Matrix.det_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [hm, map_mul, rename_C, map_prod]
  simp only [map_pow, rename_X, Matrix.of_apply, Units.smul_def, zsmul_eq_mul]
  ring

/-- Every integral signed sum is divisible by the universal Vandermonde. -/
theorem paperUniversalVandermonde_dvd_antisymmetrization (p : MvPolynomial (Fin n) K) :
    paperUniversalVandermonde K n ∣ paperIntegralAntisymmetrization K n p := by
  classical
  rw [p.as_sum, map_sum]
  apply Finset.dvd_sum
  intro m _
  rw [paperIntegralAntisymmetrization_monomial]
  exact dvd_mul_of_dvd_right
    (vandermondeProd_dvd_det_pow (X : Fin n → MvPolynomial (Fin n) K) m) _

/-- The staircase monomial in the determinant's native column convention. -/
def paperSymmetricStaircase : MvPolynomial (Fin n) K :=
  ∏ i : Fin n, X i ^ (i : ℕ)

/-- The staircase normalizes integral antisymmetrization exactly, without division by a factorial. -/
theorem paperIntegralAntisymmetrization_staircase :
    paperIntegralAntisymmetrization K n (paperSymmetricStaircase K n) =
      paperUniversalVandermonde K n := by
  rw [paperIntegralAntisymmetrization_apply, paperUniversalVandermonde,
    ← det_vandermonde_eq_vandermondeProd, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro e _
  simp only [paperSymmetricStaircase, map_prod, map_pow, rename_X,
    Matrix.vandermonde_apply, Units.smul_def]

end

end GaloisForLFunctions.HTGeometry

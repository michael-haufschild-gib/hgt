import GaloisForLFunctions.HTGeometry.PaperIntegralAntisymmetrization

/-!
# Integral projection onto the symmetric coefficient algebra

Divide the antisymmetrization of the staircase times a polynomial by the
universal Vandermonde. Native determinant divisibility supplies existence;
universal Vandermonde regularity supplies uniqueness over every commutative
ring. The resulting projection is linear over the symmetric algebra.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable (K : Type*) [CommRing K] (n : ℕ)

private def integralSymmetricQuotient (p : MvPolynomial (Fin n) K) :
    MvPolynomial (Fin n) K :=
  (paperUniversalVandermonde_dvd_antisymmetrization K n
    (paperSymmetricStaircase K n * p)).choose

private theorem integralSymmetricQuotient_spec (p : MvPolynomial (Fin n) K) :
    paperUniversalVandermonde K n * integralSymmetricQuotient K n p =
      paperIntegralAntisymmetrization K n (paperSymmetricStaircase K n * p) :=
  (paperUniversalVandermonde_dvd_antisymmetrization K n
    (paperSymmetricStaircase K n * p)).choose_spec.symm

/-- A denominator-free linear projection from root polynomials to symmetric polynomials. -/
def paperIntegralSymmetricProjection :
    MvPolynomial (Fin n) K →ₗ[K] MvPolynomial (Fin n) K where
  toFun := integralSymmetricQuotient K n
  map_add' p q := by
    apply (paperUniversalVandermonde_regular K n).left
    simp only [integralSymmetricQuotient_spec, mul_add, map_add]
  map_smul' a p := by
    apply (paperUniversalVandermonde_regular K n).left
    simp only [RingHom.id_apply, mul_smul_comm, integralSymmetricQuotient_spec, map_smul]

/-- The defining division identity holds over every commutative base ring. -/
theorem paperIntegralSymmetricProjection_spec (p : MvPolynomial (Fin n) K) :
    paperUniversalVandermonde K n * paperIntegralSymmetricProjection K n p =
      paperIntegralAntisymmetrization K n (paperSymmetricStaircase K n * p) :=
  integralSymmetricQuotient_spec K n p

/-- The quotient is symmetric, including in characteristic two and over rings with torsion. -/
theorem paperIntegralSymmetricProjection_isSymmetric (p : MvPolynomial (Fin n) K) :
    (paperIntegralSymmetricProjection K n p).IsSymmetric := by
  intro e
  apply (paperUniversalVandermonde_regular K n).left
  have h := congrArg (rename e) (paperIntegralSymmetricProjection_spec K n p)
  rw [map_mul, paperUniversalVandermonde_rename,
    paperIntegralAntisymmetrization_rename] at h
  have hs := congrArg (fun z : MvPolynomial (Fin n) K => (Equiv.Perm.sign e : ℤ) • z) h
  simp only [smul_mul_assoc, smul_smul, Int.units_coe_mul_self, one_smul] at hs
  exact hs.trans (paperIntegralSymmetricProjection_spec K n p).symm

/-- Every symmetric polynomial factor passes through the integral projection. -/
theorem paperIntegralSymmetricProjection_mul
    (p q : MvPolynomial (Fin n) K) (hp : p.IsSymmetric) :
    paperIntegralSymmetricProjection K n (p * q) =
      p * paperIntegralSymmetricProjection K n q := by
  apply (paperUniversalVandermonde_regular K n).left
  dsimp only
  rw [paperIntegralSymmetricProjection_spec,
    mul_left_comm (paperUniversalVandermonde K n) p,
    paperIntegralSymmetricProjection_spec,
    mul_left_comm (paperSymmetricStaircase K n) p,
    paperIntegralAntisymmetrization_mul K n p _ hp]

/-- The integral projection fixes every symmetric polynomial pointwise. -/
theorem paperIntegralSymmetricProjection_fixed
    (p : MvPolynomial (Fin n) K) (hp : p.IsSymmetric) :
    paperIntegralSymmetricProjection K n p = p := by
  apply (paperUniversalVandermonde_regular K n).left
  dsimp only
  rw [paperIntegralSymmetricProjection_spec, mul_comm (paperSymmetricStaircase K n) p,
    paperIntegralAntisymmetrization_mul K n p _ hp,
    paperIntegralAntisymmetrization_staircase, mul_comm]

end

end GaloisForLFunctions.HTGeometry

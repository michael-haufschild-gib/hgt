import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic

/-!
# Scaling a matrix does not change the Galois group of its characteristic polynomial

Multiplying a matrix by a nonzero scalar multiplies its eigenvalues by that scalar, so the splitting
field is unchanged.  At the level of polynomials this is the identity
`(aM).charpoly ∘ (aX) = a^D · M.charpoly`, together with the invariance of the Galois group under
composition with a linear substitution and under multiplication by a nonzero constant.  This is what
lets a rational Hamiltonian be replaced by an integral multiple of itself.

## Main results

* `charpoly_smul_comp` — the scaling identity for characteristic polynomials.
* `card_gal_comp_scale`, `card_gal_C_mul` — the two invariances.
* `card_gal_charpoly_smul` — **the Galois group is unchanged by scaling the matrix.**
-/

open Polynomial Matrix
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The scaling identity for characteristic polynomials.** -/
theorem charpoly_smul_comp {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]
    (a : R) (M : Matrix n n R) :
    ((a • M).charpoly).comp (C a * X) = C (a ^ Fintype.card n) * M.charpoly := by
  classical
  have hmap : (Polynomial.compRingHom (C a * X)).mapMatrix (charmatrix (a • M))
      = (C a : R[X]) • charmatrix M := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      Polynomial.coe_compRingHom_apply]
    by_cases hij : i = j
    · subst hij
      rw [charmatrix_apply_eq, charmatrix_apply_eq, Polynomial.sub_comp, Polynomial.X_comp,
        Polynomial.C_comp]
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
      ring_nf
    · rw [charmatrix_apply_ne _ _ _ hij, charmatrix_apply_ne _ _ _ hij, Polynomial.neg_comp,
        Polynomial.C_comp]
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
      ring_nf
  calc ((a • M).charpoly).comp (C a * X)
      = (Polynomial.compRingHom (C a * X)) ((charmatrix (a • M)).det) := rfl
    _ = ((Polynomial.compRingHom (C a * X)).mapMatrix (charmatrix (a • M))).det :=
        RingHom.map_det _ _
    _ = ((C a : R[X]) • charmatrix M).det := by rw [hmap]
    _ = (C a : R[X]) ^ Fintype.card n * (charmatrix M).det := Matrix.det_smul _ _
    _ = C (a ^ Fintype.card n) * M.charpoly := by rw [← map_pow, charpoly]

theorem card_gal_comp_scale {F : Type*} [Field F] (p : F[X]) {a : F} (ha : a ≠ 0) :
    Nat.card (p.comp (C a * X)).Gal = Nat.card p.Gal := by
  have hdeg : (C a * X : F[X]).natDegree ≠ 0 := by
    rw [Polynomial.natDegree_C_mul_X a ha]
    exact one_ne_zero
  have hdeg' : (C a⁻¹ * X : F[X]).natDegree ≠ 0 := by
    rw [Polynomial.natDegree_C_mul_X _ (inv_ne_zero ha)]
    exact one_ne_zero
  have h1 : Nat.card p.Gal ≤ Nat.card (p.comp (C a * X)).Gal :=
    Nat.card_le_card_of_surjective _ (Polynomial.Gal.restrictComp_surjective p (C a * X) hdeg)
  have hinv : (p.comp (C a * X)).comp (C a⁻¹ * X) = p := by
    rw [Polynomial.comp_assoc]
    have hx : ((C a * X : F[X]).comp (C a⁻¹ * X)) = X := by
      rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, ← mul_assoc, ← map_mul,
        mul_inv_cancel₀ ha, map_one, one_mul]
    rw [hx, Polynomial.comp_X]
  have h2 : Nat.card (p.comp (C a * X)).Gal
      ≤ Nat.card ((p.comp (C a * X)).comp (C a⁻¹ * X)).Gal :=
    Nat.card_le_card_of_surjective _
      (Polynomial.Gal.restrictComp_surjective (p.comp (C a * X)) (C a⁻¹ * X) hdeg')
  rw [hinv] at h2
  omega

theorem card_gal_C_mul {F : Type*} [Field F] {b : F} (hb : b ≠ 0) (p : F[X]) (hp : p ≠ 0) :
    Nat.card (C b * p).Gal = Nat.card p.Gal := by
  have hCb : (C b : F[X]) ≠ 0 := Polynomial.C_ne_zero.mpr hb
  have hq : (C b * p) ≠ 0 := mul_ne_zero hCb hp
  have hdvd1 : p ∣ C b * p := ⟨C b, by ring⟩
  have hdvd2 : C b * p ∣ p := ⟨C b⁻¹, by
    rw [mul_comm (C b) p, mul_assoc, ← map_mul, mul_inv_cancel₀ hb, map_one, mul_one]⟩
  have h1 := Nat.card_le_card_of_surjective _ (Polynomial.Gal.restrictDvd_surjective hdvd1 hq)
  have h2 := Nat.card_le_card_of_surjective _ (Polynomial.Gal.restrictDvd_surjective hdvd2 hp)
  omega

/-- **Scaling a matrix does not change the Galois group of its characteristic polynomial.** -/
theorem card_gal_charpoly_smul {F : Type*} [Field F] {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] {a : F} (ha : a ≠ 0) (M : Matrix n n F) :
    Nat.card ((a • M).charpoly).Gal = Nat.card (M.charpoly).Gal := by
  have hM : M.charpoly ≠ 0 := M.charpoly_monic.ne_zero
  have h1 : Nat.card ((a • M).charpoly).Gal
      = Nat.card ((((a • M).charpoly).comp (C a * X))).Gal :=
    (card_gal_comp_scale _ ha).symm
  rw [charpoly_smul_comp] at h1
  rw [h1, card_gal_C_mul (pow_ne_zero _ ha) M.charpoly hM]

end

end GaloisForLFunctions.HTGeometry

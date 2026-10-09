import GaloisForLFunctions.HTGeometry.PaperSplitIdealContraction
import GaloisForLFunctions.HTGeometry.SymmetricCoefficientNonSquare

/-!
# A proved splitting of the native symmetric coefficient ring

Average root permutations, then use the existing fundamental symmetric
isomorphism to return to coefficient coordinates. The resulting map is
linear over the coefficient ring, not merely over the base field.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial
open scoped BigOperators

noncomputable section

variable (K : Type*) [Field K] (n : ℕ)

/-- The normalized average of the native root-permutation maps. -/
def paperSymmetricAverage : MvPolynomial (Fin n) K →ₗ[K] MvPolynomial (Fin n) K :=
  (Fintype.card (Equiv.Perm (Fin n)) : K)⁻¹ •
    ∑ e : Equiv.Perm (Fin n), (rename e : MvPolynomial (Fin n) K →ₐ[K] _).toLinearMap

/-- The average is the literal finite permutation sum. -/
theorem paperSymmetricAverage_apply (p : MvPolynomial (Fin n) K) :
    paperSymmetricAverage K n p = (Fintype.card (Equiv.Perm (Fin n)) : K)⁻¹ •
      ∑ e : Equiv.Perm (Fin n), rename e p := by
  simp only [paperSymmetricAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    AlgHom.toLinearMap_apply]

/-- Averaging produces an actual symmetric polynomial. -/
theorem paperSymmetricAverage_isSymmetric (p : MvPolynomial (Fin n) K) :
    (paperSymmetricAverage K n p).IsSymmetric := by
  intro e
  rw [paperSymmetricAverage_apply, map_smul, map_sum]
  congr 1
  simpa only [rename_rename, Equiv.Perm.coe_mul] using
    Function.Bijective.sum_comp (Group.mulLeft_bijective e)
      (fun f : Equiv.Perm (Fin n) => rename f p)

/-- Multiplication by an invariant polynomial passes through the average. -/
theorem paperSymmetricAverage_mul (p q : MvPolynomial (Fin n) K) (hp : p.IsSymmetric) :
    paperSymmetricAverage K n (p * q) = p * paperSymmetricAverage K n q := by
  change ∀ e : Equiv.Perm (Fin n), rename e p = p at hp
  simp only [paperSymmetricAverage_apply, map_mul, hp]
  rw [← Finset.mul_sum, Algebra.mul_smul_comm]

/-- In characteristic zero the average fixes every symmetric polynomial. -/
theorem paperSymmetricAverage_fixed [CharZero K]
    (p : MvPolynomial (Fin n) K) (hp : p.IsSymmetric) :
    paperSymmetricAverage K n p = p := by
  change ∀ e : Equiv.Perm (Fin n), rename e p = p at hp
  have hc : (Fintype.card (Equiv.Perm (Fin n)) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [paperSymmetricAverage_apply]
  simp only [hp, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- Return a root polynomial to the native elementary-symmetric coefficient coordinates. -/
def paperSymmetricCoefficientRetraction :
    MvPolynomial (Fin n) K →ₗ[K] MvPolynomial (Fin n) K :=
  (esymmAlgEquiv K n).symm.toLinearMap.comp
    ((paperSymmetricAverage K n).codRestrict (symmetricSubalgebra (Fin n) K).toSubmodule
      (paperSymmetricAverage_isSymmetric K n))

/-- Substitution of the returned coefficients recovers exactly the symmetric average. -/
theorem paperSymmetricCoefficientRetraction_spec (p : MvPolynomial (Fin n) K) :
    aeval (fun i : Fin n => esymm (Fin n) K (i + 1))
      (paperSymmetricCoefficientRetraction K n p) = paperSymmetricAverage K n p := by
  rw [← esymmAlgEquiv_apply_coe]
  exact congrArg Subtype.val ((esymmAlgEquiv K n).apply_symm_apply
    ⟨paperSymmetricAverage K n p, paperSymmetricAverage_isSymmetric K n p⟩)

/-- The retraction fixes the native polynomial coefficient ring pointwise. -/
theorem paperSymmetricCoefficientRetraction_map [CharZero K] (p : MvPolynomial (Fin n) K) :
    paperSymmetricCoefficientRetraction K n
      (aeval (fun i : Fin n => esymm (Fin n) K (i + 1)) p) = p := by
  apply (esymmAlgEquiv K n).injective
  apply Subtype.ext
  rw [esymmAlgEquiv_apply_coe, paperSymmetricCoefficientRetraction_spec,
    esymmAlgEquiv_apply_coe]
  apply paperSymmetricAverage_fixed
  rw [← esymmAlgEquiv_apply_coe]
  exact (esymmAlgEquiv K n p).property

/-- The retraction is linear over every polynomial in the elementary symmetric generators. -/
theorem paperSymmetricCoefficientRetraction_mul (p q : MvPolynomial (Fin n) K) :
    paperSymmetricCoefficientRetraction K n
      (aeval (fun i : Fin n => esymm (Fin n) K (i + 1)) p * q) =
        p * paperSymmetricCoefficientRetraction K n q := by
  apply (esymmAlgEquiv K n).injective
  apply Subtype.ext
  rw [esymmAlgEquiv_apply_coe, esymmAlgEquiv_apply_coe,
    paperSymmetricCoefficientRetraction_spec]
  rw [map_mul (aeval (R := K) (fun i : Fin n => esymm (Fin n) K (i + 1))) p
    (paperSymmetricCoefficientRetraction K n q), paperSymmetricCoefficientRetraction_spec]
  apply paperSymmetricAverage_mul
  rw [← esymmAlgEquiv_apply_coe]
  exact (esymmAlgEquiv K n p).property

/-- All splitting requirements are proved for the native symmetric coefficient map. -/
def paperElementarySymmetricRetraction [CharZero K] :
    PaperIdealRetraction
      (aeval (R := K) (fun i : Fin n => esymm (Fin n) K (i + 1))).toRingHom where
  retract := (paperSymmetricCoefficientRetraction K n).toAddMonoidHom
  retract_map := paperSymmetricCoefficientRetraction_map K n
  retract_mul := paperSymmetricCoefficientRetraction_mul K n

end

end GaloisForLFunctions.HTGeometry

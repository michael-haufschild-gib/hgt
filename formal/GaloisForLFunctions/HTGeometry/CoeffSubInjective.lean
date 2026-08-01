import GaloisForLFunctions.HTGeometry.UniversalToGeneric
import GaloisForLFunctions.HTGeometry.GenericPolynomialVieta
import GaloisForLFunctions.HTGeometry.MonomialSubstitution
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# Specialising to the generic coefficients is injective

Up to sign and a reversal of the indices, the coefficients of the generic polynomial are the
elementary symmetric functions of its roots.  So the substitution sending the indeterminate
coefficients to the generic ones factors as a signed reversal of the variables, followed by the
substitution of the elementary symmetric functions, followed by the passage to fractions.

Each of the three is injective — the middle one by the fundamental theorem of symmetric
polynomials — so relations among the generic coefficients are relations among the variables.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {K : Type*} [Field K] {d : ℕ}

/-- Substituting the elementary symmetric functions for the variables. -/
noncomputable def esymmSub (K : Type*) [Field K] (d : ℕ) :
    MvPolynomial (Fin d) K →ₐ[K] MvPolynomial (Fin d) K :=
  (MvPolynomial.symmetricSubalgebra (Fin d) K).val.comp (MvPolynomial.esymmAlgHom (Fin d) K d)

theorem esymmSub_X (i : Fin d) :
    esymmSub K d (MvPolynomial.X i) = MvPolynomial.esymm (Fin d) K ((i : ℕ) + 1) := by
  show ((MvPolynomial.esymmAlgHom (Fin d) K d) (MvPolynomial.X i)).val = _
  rw [MvPolynomial.esymmAlgHom_apply, MvPolynomial.aeval_X]

theorem esymmSub_injective : Function.Injective (esymmSub K d) :=
  Subtype.val_injective.comp (MvPolynomial.esymmAlgHom_fin_injective K le_rfl)

/-- Reversing the variables and attaching the alternating sign. -/
noncomputable def signRev (K : Type*) [Field K] (d : ℕ) :
    MvPolynomial (Fin d) K →ₐ[K] MvPolynomial (Fin d) K :=
  monomialSub (fun j : Fin d => (-1 : K) ^ (d - (j : ℕ))) Fin.revPerm

theorem signRev_X (j : Fin d) :
    signRev K d (MvPolynomial.X j) =
      MvPolynomial.C ((-1 : K) ^ (d - (j : ℕ))) * MvPolynomial.X (Fin.rev j) :=
  monomialSub_X _ _ j

theorem signRev_injective : Function.Injective (signRev K d) :=
  monomialSub_injective (fun _ => pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) _

/-- Passing from the polynomials to the rational functions. -/
noncomputable def toFractions (K : Type*) [Field K] (d : ℕ) :
    MvPolynomial (Fin d) K →ₐ[K] SymmetricRationalField K d :=
  IsScalarTower.toAlgHom K (MvPolynomial (Fin d) K) (SymmetricRationalField K d)

theorem toFractions_apply (p : MvPolynomial (Fin d) K) :
    toFractions K d p =
      algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d) p := rfl

theorem toFractions_injective : Function.Injective (toFractions K d) :=
  IsFractionRing.injective (MvPolynomial (Fin d) K) (SymmetricRationalField K d)

theorem toFractions_C_pow_neg_one (k : ℕ) :
    toFractions K d (MvPolynomial.C ((-1 : K) ^ k)) =
      (-1 : SymmetricRationalField K d) ^ k := by
  rw [toFractions_apply, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
    map_pow, map_neg, map_one]

/-- The factorisation of the specialisation. -/
noncomputable def coeffSubFactor (K : Type*) [Field K] (d : ℕ) :
    MvPolynomial (Fin d) K →ₐ[K] SymmetricRationalField K d :=
  (toFractions K d).comp ((esymmSub K d).comp (signRev K d))

/-- **The specialisation is a signed reversal followed by the symmetric substitution.** -/
theorem coeffSub_eq_coeffSubFactor : coeffSub K d = coeffSubFactor K d := by
  refine MvPolynomial.algHom_ext fun j => ?_
  have hj : (j : ℕ) < d := j.isLt
  have hidx : ((Fin.rev j : Fin d) : ℕ) + 1 = d - (j : ℕ) := by
    rw [Fin.val_rev]
    omega
  have hC : esymmSub K d (MvPolynomial.C ((-1 : K) ^ (d - (j : ℕ)))) =
      MvPolynomial.C ((-1 : K) ^ (d - (j : ℕ))) := by
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  rw [coeffSub_X, coeff_genericMonicF (le_of_lt hj), coeffSubFactor, AlgHom.comp_apply,
    AlgHom.comp_apply, signRev_X, map_mul, hC, map_mul, toFractions_C_pow_neg_one,
    esymmSub_X, hidx, toFractions_apply]

/-- **Specialising the indeterminate coefficients to the generic ones is injective.** -/
theorem coeffSub_injective : Function.Injective (coeffSub K d) := by
  rw [coeffSub_eq_coeffSubFactor]
  exact toFractions_injective.comp (esymmSub_injective.comp signRev_injective)

end GaloisForLFunctions.HTGeometry

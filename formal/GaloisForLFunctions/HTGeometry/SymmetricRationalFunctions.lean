import GaloisForLFunctions.HTGeometry.SymmetricVariableAction
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# Symmetric rational functions

The rational function field is Galois over its symmetric part with the symmetric group as Galois
group, by Artin's theorem.

A symmetric rational function is moreover a ratio of symmetric polynomials: multiplying numerator
and denominator by the images of the denominator under every nonidentity permutation makes the
denominator symmetric, and the numerator is then symmetric because the quotient is.  With the
fundamental theorem of symmetric polynomials this says that a symmetric rational function is a
rational function of the elementary symmetric functions.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {K : Type*} [Field K] {d : ℕ}

/-! ## The Galois group -/

instance isGalois_symmetricPart (K : Type*) [Field K] (d : ℕ) :
    IsGalois (symmetricPart K d) (SymmetricRationalField K d) where

/-- **The Galois group of the rational function field over its symmetric part is the symmetric
group.** -/
noncomputable def symmetricGaloisEquiv (K : Type*) [Field K] (d : ℕ) :
    Equiv.Perm (Fin d) ≃*
      (SymmetricRationalField K d ≃ₐ[symmetricPart K d] SymmetricRationalField K d) :=
  FixedPoints.toAlgAutMulEquiv _ _

@[simp]
theorem symmetricGaloisEquiv_apply (K : Type*) [Field K] (d : ℕ) (e : Equiv.Perm (Fin d))
    (z : SymmetricRationalField K d) : symmetricGaloisEquiv K d e z = e • z := rfl

/-! ## Symmetric rational functions are ratios of symmetric polynomials -/

theorem smul_eq_of_mem_symmetricPart {z : SymmetricRationalField K d}
    (hz : z ∈ symmetricPart K d) (e : Equiv.Perm (Fin d)) : e • z = z := by
  have h : z ∈ MulAction.fixedPoints (Equiv.Perm (Fin d)) (SymmetricRationalField K d) := hz
  exact h e

theorem algebraMap_smul_mvPolynomial (e : Equiv.Perm (Fin d)) (p : MvPolynomial (Fin d) K) :
    algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d) (e • p) =
      e • algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d) p :=
  algebraMap.smul' _ _ _

/-- The symmetrised denominator: the product of the images of an element under every
permutation. -/
noncomputable def symmetrise (b : MvPolynomial (Fin d) K) : MvPolynomial (Fin d) K :=
  ∏ e : Equiv.Perm (Fin d), e • b

theorem isSymmetric_symmetrise (b : MvPolynomial (Fin d) K) : (symmetrise b).IsSymmetric := by
  intro t
  show t • symmetrise b = symmetrise b
  rw [symmetrise, Finset.smul_prod']
  refine Fintype.prod_equiv (Equiv.mulLeft t) _ _ fun e => ?_
  rw [← mul_smul]
  rfl

theorem symmetrise_ne_zero {b : MvPolynomial (Fin d) K} (hb : b ≠ 0) : symmetrise b ≠ 0 := by
  rw [symmetrise]
  refine Finset.prod_ne_zero_iff.2 fun e _ => ?_
  rw [perm_smul_mvPolynomial]
  exact fun hcon => hb (rename_injective (e : Fin d → Fin d) e.injective hcon)

/-- **A symmetric rational function is a ratio of symmetric polynomials.** -/
theorem exists_isSymmetric_ratio_of_mem_symmetricPart {z : SymmetricRationalField K d}
    (hz : z ∈ symmetricPart K d) :
    ∃ A B : MvPolynomial (Fin d) K, A.IsSymmetric ∧ B.IsSymmetric ∧ B ≠ 0 ∧
      z = algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d) A /
        algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d) B := by
  classical
  obtain ⟨a, b, hb, hzab⟩ := IsFractionRing.div_surjective
    (A := MvPolynomial (Fin d) K) (K := SymmetricRationalField K d) z
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d)) :=
    IsFractionRing.injective _ _
  have hbF : algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d) b ≠ 0 :=
    fun hcon => hb0 (hinj (by rw [hcon, map_zero]))
  have hBC : symmetrise b =
      b * ∏ e ∈ (Finset.univ.erase (1 : Equiv.Perm (Fin d))), e • b := by
    rw [symmetrise, ← Finset.mul_prod_erase Finset.univ
      (fun e : Equiv.Perm (Fin d) => e • b) (Finset.mem_univ 1), one_smul]
  have hkey : algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d)
        (a * ∏ e ∈ (Finset.univ.erase (1 : Equiv.Perm (Fin d))), e • b) =
      z * algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d) (symmetrise b) := by
    rw [hBC, map_mul, map_mul, ← hzab]
    field_simp
  refine ⟨a * ∏ e ∈ (Finset.univ.erase (1 : Equiv.Perm (Fin d))), e • b, symmetrise b, ?_,
    isSymmetric_symmetrise b, symmetrise_ne_zero hb0, ?_⟩
  · intro t
    show t • (a * ∏ e ∈ (Finset.univ.erase (1 : Equiv.Perm (Fin d))), e • b) = _
    refine hinj ?_
    rw [algebraMap_smul_mvPolynomial, hkey, smul_mul', smul_eq_of_mem_symmetricPart hz,
      ← algebraMap_smul_mvPolynomial]
    congr 2
    exact isSymmetric_symmetrise b t
  · have hsymF : algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d)
        (symmetrise b) ≠ 0 :=
      fun hcon => symmetrise_ne_zero hb0 (hinj (by rw [hcon, map_zero]))
    rw [hkey, mul_div_assoc, div_self hsymF, mul_one]

end GaloisForLFunctions.HTGeometry

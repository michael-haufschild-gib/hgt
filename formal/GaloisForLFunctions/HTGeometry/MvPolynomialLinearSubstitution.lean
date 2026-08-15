import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Linear substitutions of the variables of a polynomial ring

Replacing each variable by a fixed linear combination of the variables is an algebra endomorphism,
and it is an automorphism exactly when the matrix of the combination is invertible: the inverse
matrix gives the inverse substitution, because substitutions compose by matrix multiplication.

A triangular matrix with invertible diagonal is invertible, which is the case that arises when one
family of jets is expressed through another.
-/

open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The substitution attached to a matrix: each variable becomes the corresponding row combination
of the variables. -/
noncomputable def matrixSubst (M : Matrix (Fin n) (Fin n) R) :
    MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  MvPolynomial.aeval fun i => ∑ j, MvPolynomial.C (M i j) * MvPolynomial.X j

@[simp] theorem matrixSubst_X (M : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    matrixSubst M (MvPolynomial.X i) = ∑ j, MvPolynomial.C (M i j) * MvPolynomial.X j := by
  rw [matrixSubst, MvPolynomial.aeval_X]

@[simp] theorem matrixSubst_C (M : Matrix (Fin n) (Fin n) R) (a : R) :
    matrixSubst M (MvPolynomial.C a) = MvPolynomial.C a := by
  rw [matrixSubst, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

/-- Substitutions compose by matrix multiplication. -/
theorem matrixSubst_comp (M N : Matrix (Fin n) (Fin n) R) :
    (matrixSubst N).comp (matrixSubst M) = matrixSubst (M * N) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [AlgHom.comp_apply, matrixSubst_X, map_sum, matrixSubst_X]
  have hstep : ∀ j : Fin n,
      matrixSubst N (MvPolynomial.C (M i j) * MvPolynomial.X j)
        = ∑ k, MvPolynomial.C (M i j * N j k) * MvPolynomial.X k := by
    intro j
    rw [map_mul, matrixSubst_C, matrixSubst_X, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, ← map_mul]
  rw [Finset.sum_congr rfl fun j _ => hstep j, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_mul, ← map_sum]
  rfl

/-- **A substitution by an invertible matrix is injective.** -/
theorem matrixSubst_injective {M : Matrix (Fin n) (Fin n) R} (hM : IsUnit M.det) :
    Function.Injective (matrixSubst M) := by
  have hinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  have hcomp : (matrixSubst M⁻¹).comp (matrixSubst M) = matrixSubst (1 : Matrix (Fin n) (Fin n) R) := by
    rw [matrixSubst_comp, hinv]
  have hone : matrixSubst (1 : Matrix (Fin n) (Fin n) R) = AlgHom.id R (MvPolynomial (Fin n) R) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [matrixSubst_X, AlgHom.id_apply]
    rw [Finset.sum_eq_single i]
    · rw [Matrix.one_apply_eq, map_one, one_mul]
    · intro j _ hji
      rw [Matrix.one_apply_ne (Ne.symm hji), map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  intro p q hpq
  have h := congrArg (matrixSubst M⁻¹) hpq
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, hcomp, hone] at h
  exact h

/-- A lower-triangular matrix with nonzero diagonal over a field is invertible. -/
theorem isUnit_det_of_lowerTriangular {K : Type*} [Field K]
    {M : Matrix (Fin n) (Fin n) K} (htri : ∀ i j, i < j → M i j = 0)
    (hdiag : ∀ i, M i i ≠ 0) : IsUnit M.det := by
  rw [Matrix.det_of_lowerTriangular M htri]
  exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => hdiag i)


/-! ### Base change -/

theorem matrixSubst_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (φ : R →+* S) (M : Matrix (Fin n) (Fin n) R) (p : MvPolynomial (Fin n) R) :
    MvPolynomial.map φ (matrixSubst M p) = matrixSubst (M.map φ) (MvPolynomial.map φ p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp only [matrixSubst_C, MvPolynomial.map_C]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, matrixSubst_X, MvPolynomial.map_X]
      rw [hp, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, MvPolynomial.map_C, MvPolynomial.map_X, Matrix.map_apply]

/-- **Injectivity after an injective base change.** -/
theorem matrixSubst_injective_of_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (φ : R →+* S) (hφ : Function.Injective φ) {M : Matrix (Fin n) (Fin n) R}
    (hM : IsUnit (M.map φ).det) : Function.Injective (matrixSubst M) := by
  intro p q hpq
  refine MvPolynomial.map_injective φ hφ ?_
  refine matrixSubst_injective hM ?_
  rw [← matrixSubst_map, ← matrixSubst_map, hpq]

/-- A lower-triangular matrix with unit diagonal is invertible. -/
theorem isUnit_det_of_lowerTriangular_units {R : Type*} [CommRing R] {n : ℕ}
    {M : Matrix (Fin n) (Fin n) R} (htri : ∀ i j, i < j → M i j = 0)
    (hdiag : ∀ i, IsUnit (M i i)) : IsUnit M.det := by
  rw [Matrix.det_of_lowerTriangular M htri]
  refine Finset.prod_induction _ IsUnit ?_ isUnit_one fun i _ => hdiag i
  intro a b ha hb
  exact ha.mul hb


/-- Evaluating after a linear substitution is evaluating at the substituted points. -/
theorem eval₂_matrixSubst {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (g : Fin n → S) (M : Matrix (Fin n) (Fin n) R) (p : MvPolynomial (Fin n) R) :
    MvPolynomial.eval₂ f g (matrixSubst M p)
      = MvPolynomial.eval₂ f (fun i => ∑ j, f (M i j) * g j) p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => rw [matrixSubst_C, MvPolynomial.eval₂_C, MvPolynomial.eval₂_C]
  | add p q hp hq => rw [map_add, MvPolynomial.eval₂_add, MvPolynomial.eval₂_add, hp, hq]
  | mul_X p i hp =>
      rw [map_mul, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_mul, hp, matrixSubst_X,
        MvPolynomial.eval₂_X]
      congr 1
      rw [MvPolynomial.eval₂_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]

end GaloisForLFunctions.HTGeometry

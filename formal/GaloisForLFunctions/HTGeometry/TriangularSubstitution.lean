import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Invertible linear substitutions of polynomial variables

A square matrix over a commutative ring induces a linear substitution of the variables of a
multivariate polynomial ring.  Substitutions compose contravariantly to matrix multiplication, so
an invertible matrix induces an injective substitution.  A lower-triangular matrix with unit
diagonal is invertible, hence a triangular change of jet coordinates carries nonzero polynomial
relations to nonzero polynomial relations.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {K : Type*} [CommRing K] {m : ℕ}

/-- The linear substitution of variables attached to a square matrix. -/
noncomputable def linSub (M : Matrix (Fin m) (Fin m) K) :
    MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin m) K :=
  MvPolynomial.aeval fun j => ∑ i, MvPolynomial.C (M j i) * MvPolynomial.X i

theorem linSub_X (M : Matrix (Fin m) (Fin m) K) (j : Fin m) :
    linSub M (MvPolynomial.X j) = ∑ i, MvPolynomial.C (M j i) * MvPolynomial.X i := by
  rw [linSub, MvPolynomial.aeval_X]

theorem linSub_one : linSub (1 : Matrix (Fin m) (Fin m) K) = AlgHom.id K _ := by
  refine MvPolynomial.algHom_ext fun j => ?_
  rw [linSub_X, AlgHom.id_apply]
  rw [Finset.sum_eq_single j]
  · rw [Matrix.one_apply_eq, map_one, one_mul]
  · intro i _ hij
    rw [Matrix.one_apply_ne (Ne.symm hij), map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem linSub_comp (M N : Matrix (Fin m) (Fin m) K) :
    (linSub N).comp (linSub M) = linSub (M * N) := by
  refine MvPolynomial.algHom_ext fun j => ?_
  rw [AlgHom.comp_apply, linSub_X, map_sum, linSub_X]
  have hterm : ∀ i : Fin m, (linSub N) (MvPolynomial.C (M j i) * MvPolynomial.X i)
      = ∑ k, MvPolynomial.C (M j i * N i k) * MvPolynomial.X k := by
    intro i
    rw [map_mul, MvPolynomial.algHom_C, linSub_X, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [MvPolynomial.algebraMap_eq, ← mul_assoc, ← map_mul]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_apply, map_sum, Finset.sum_mul]

/-- An invertible substitution is injective. -/
theorem linSub_injective {M : Matrix (Fin m) (Fin m) K} (hM : IsUnit M.det) :
    Function.Injective (linSub M) := by
  have hinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  have hcomp : (linSub M⁻¹).comp (linSub M) = AlgHom.id K _ := by
    rw [linSub_comp, hinv, linSub_one]
  intro P Q hPQ
  have h1 : (linSub M⁻¹) ((linSub M) P) = (linSub M⁻¹) ((linSub M) Q) := by rw [hPQ]
  have h2 : ((linSub M⁻¹).comp (linSub M)) P = ((linSub M⁻¹).comp (linSub M)) Q := h1
  rwa [hcomp, AlgHom.id_apply, AlgHom.id_apply] at h2

/-- A lower-triangular matrix with unit diagonal is invertible. -/
theorem isUnit_det_of_lowerTriangular {M : Matrix (Fin m) (Fin m) K}
    (htri : ∀ i j : Fin m, j < i → M j i = 0) (hdiag : ∀ i, IsUnit (M i i)) :
    IsUnit M.det := by
  have hblock : M.BlockTriangular OrderDual.toDual := by
    intro i j hij
    exact htri j i hij
  rw [Matrix.det_of_lowerTriangular M hblock]
  classical
  refine Finset.prod_induction _ (fun x => IsUnit x) (fun a b ha hb => ha.mul hb) isUnit_one ?_
  intro i _
  exact hdiag i

end GaloisForLFunctions.HTGeometry

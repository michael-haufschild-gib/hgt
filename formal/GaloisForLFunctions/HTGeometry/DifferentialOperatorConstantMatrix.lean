import GaloisForLFunctions.HTGeometry.DifferentialOperatorTopCoefficientMatrix
import GaloisForLFunctions.HTGeometry.DifferentialOperatorOreMatrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Constant matrices, and when the degree of a product is exactly additive

Two consequences of the multiplicativity of the leading matrix.

A matrix with *constant* entries which is invertible over the operator ring is already invertible
over the coefficient field: a left kernel vector over the field stays a left kernel vector over the
operator ring, and an invertible matrix has none.  So the degree-zero case of the growth problem is
trivial.

And when the leading matrices of two factors do not annihilate each other, the degree of the
product is exactly the sum: some entry of the product has a nonzero coefficient in the top slot.

* `CRingHom` — the coefficients as a ring homomorphism into the operator ring;
* `isUnit_det_of_map_C_mul_eq_one`;
* `exists_degree_eq_of_topCoeffMatrix_mul_ne_zero`.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]

@[simp] theorem coeff_C (a : K) : coeff (C a) 0 = a := by
  rw [C, coeff_mono_self]

theorem C_mul_C (a b : K) : (C a : DiffOp K) * C b = C (a * b) := by
  rw [C_mul, C, smul_mono, C]

theorem C_add' (a b : K) : (C (a + b) : DiffOp K) = C a + C b := by
  rw [C, C, C, mono_add]

/-- The coefficients, as a ring homomorphism into the operator ring. -/
def CRingHom : K →+* DiffOp K where
  toFun := C
  map_one' := by rw [C, ← one_def]
  map_mul' := fun a b => (C_mul_C a b).symm
  map_zero' := by rw [C, mono_zero]
  map_add' := C_add'

theorem CRingHom_injective : Function.Injective (CRingHom : K →+* DiffOp K) := by
  intro a b hab
  have h : coeff (C a : DiffOp K) 0 = coeff (C b : DiffOp K) 0 :=
    congrArg (fun p : DiffOp K => coeff p 0) hab
  rwa [coeff_C, coeff_C] at h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A constant matrix invertible over the operator ring is invertible over the field.** -/
theorem isUnit_det_of_map_C_mul_eq_one {A : Matrix ι ι K} {B : Matrix ι ι (DiffOp K)}
    (hAB : (A.map (CRingHom : K →+* DiffOp K)) * B = 1) : IsUnit (Matrix.det A) := by
  classical
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  have hmapzero : Matrix.vecMul (fun i => (CRingHom : K →+* DiffOp K) (v i))
      (A.map (CRingHom : K →+* DiffOp K)) = 0 := by
    funext j
    show ∑ i, (CRingHom : K →+* DiffOp K) (v i) * (CRingHom : K →+* DiffOp K) (A i j) = 0
    have hstep : ∑ i, (CRingHom : K →+* DiffOp K) (v i) * (CRingHom : K →+* DiffOp K) (A i j)
        = (CRingHom : K →+* DiffOp K) (∑ i, v i * A i j) := by
      rw [map_sum]
      exact (Finset.sum_congr rfl fun i _ => (map_mul _ _ _)).symm
    rw [hstep]
    have : (∑ i, v i * A i j) = 0 := congrFun hv j
    rw [this, map_zero]
  have hzero : (fun i => (CRingHom : K →+* DiffOp K) (v i)) = 0 := by
    have := congrArg (fun w : ι → DiffOp K => Matrix.vecMul w B) hmapzero
    simp only [Matrix.vecMul_vecMul, hAB, Matrix.vecMul_one, Matrix.zero_vecMul] at this
    exact this
  refine hv0 ?_
  funext i
  have := congrFun hzero i
  exact CRingHom_injective (by simpa using this)

omit [DecidableEq ι] in
/-- **The degree of a product is exactly additive when the leading matrices do not annihilate.** -/
theorem exists_degree_eq_of_topCoeffMatrix_mul_ne_zero (A B : Matrix ι ι (DiffOp K)) (d e : ℕ)
    (hA : ∀ i j, degree (A i j) ≤ d) (hB : ∀ i j, degree (B i j) ≤ e)
    (hne : topCoeffMatrix A d * topCoeffMatrix B e ≠ 0) :
    ∃ i j, degree ((A * B) i j) = d + e := by
  have hmul : topCoeffMatrix (A * B) (d + e) = topCoeffMatrix A d * topCoeffMatrix B e :=
    topCoeffMatrix_mul A B d e hA hB
  have hne' : topCoeffMatrix (A * B) (d + e) ≠ 0 := by rw [hmul]; exact hne
  obtain ⟨i, j, hij⟩ : ∃ i j, coeff ((A * B) i j) (d + e) ≠ 0 := by
    by_contra hcon
    refine hne' ?_
    ext i j
    by_contra hij
    exact hcon ⟨i, j, hij⟩
  refine ⟨i, j, le_antisymm ?_ (le_degree hij)⟩
  have hentry : (A * B) i j = ∑ k, A i k * B k j := Matrix.mul_apply
  rw [hentry]
  refine le_trans (degree_sum_le _ _) (Finset.sup_le fun k _ => ?_)
  exact le_trans (degree_mul_le _ _) (Nat.add_le_add (hA i k) (hB k j))

end

end DiffOp

end GaloisForLFunctions.HTGeometry

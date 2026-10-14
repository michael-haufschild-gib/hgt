import GaloisForLFunctions.HTGeometry.FiniteSupportOperatorFredholm
import GaloisForLFunctions.HTGeometry.CompactObserverTraceBlindness

/-! # Finite weighted shifts on the full bilateral Hilbert space

The finite chain remains an actual continuous linear operator on `ℓ²(ℤ)`.
Its coordinate matrix is strictly lower triangular, hence its ordinary
Fredholm determinant is one for every choice of the finite edge weights.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open HilbertSchmidt ContinuousLinearMap InnerProductSpace RHTower
open scoped InnerProductSpace

theorem coordTruncation_apply_coordinate {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (y : lp (fun _ : ι => ℂ) 2) (i : ι) :
    coordTruncation F y i = if i ∈ F then y i else 0 := by
  rw [coordTruncation_apply, lp.coeFn_sum, Finset.sum_apply]
  simp [lp.single_apply]

theorem coordTruncation_basis {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (j : ι) :
    coordTruncation F (lpBasisVec j) = if j ∈ F then lpBasisVec j else 0 := by
  apply lp.ext
  funext i
  rw [coordTruncation_apply_coordinate]
  by_cases h : i = j
  · subst i
    split_ifs <;> simp
  · by_cases hj : j ∈ F <;> simp [lpBasisVec, lp.single_apply, h, hj]

def bilateralShiftEdges (N : ℕ) : Finset ℤ := Finset.Ico 0 (N : ℤ)

def bilateralShiftWindow (N : ℕ) : Finset ℤ := Finset.Icc 0 (N : ℤ)

def finiteBilateralWeightedShift (N : ℕ) (w : ℤ → ℂ) :
    lp (fun _ : ℤ => ℂ) 2 →L[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  ∑ j ∈ bilateralShiftEdges N, rankOne ℂ (w j • lpBasisVec (j + 1)) (lpBasisVec j)

theorem finiteBilateralWeightedShift_traceClass (N : ℕ) (w : ℤ → ℂ) :
    RHTower.MemSchattenClass 1 (finiteBilateralWeightedShift N w) :=
  memSchattenClass_one_sum_rankOne (bilateralShiftEdges N)
    (fun j => w j • lpBasisVec (j + 1)) lpBasisVec

theorem finiteBilateralWeightedShift_basis (N : ℕ) (w : ℤ → ℂ) (j : ℤ) :
    finiteBilateralWeightedShift N w (lpBasisVec j) =
      if j ∈ bilateralShiftEdges N then w j • lpBasisVec (j + 1) else 0 := by
  rw [finiteBilateralWeightedShift, FunLike.coe_sum, Finset.sum_apply]
  have hterm (k : ℤ) :
      rankOne ℂ (w k • lpBasisVec (k + 1)) (lpBasisVec k) (lpBasisVec j) =
        if k = j then w j • lpBasisVec (j + 1) else 0 := by
    rw [rankOne_apply, inner_lpBasisVec]
    by_cases h : k = j
    · subst k
      simp [lpBasisVec, lp.single_apply]
    · simp [lpBasisVec, lp.single_apply, h]
  simp_rw [hterm]
  simp

theorem coordMatrix_finiteBilateralWeightedShift (N : ℕ) (w : ℤ → ℂ) (i j : ℤ) :
    RHTower.coordMatrix (lpBasis ℤ) (finiteBilateralWeightedShift N w) (i, j) =
      if j ∈ bilateralShiftEdges N ∧ i = j + 1 then w j else 0 := by
  rw [RHTower.coordMatrix_apply, lpBasis_apply, lpBasis_apply]
  change ⟪lpBasisVec i, finiteBilateralWeightedShift N w (lpBasisVec j)⟫_ℂ = _
  rw [inner_lpBasisVec, finiteBilateralWeightedShift_basis]
  by_cases hj : j ∈ bilateralShiftEdges N <;>
    simp [hj, lpBasisVec, lp.single_apply, Pi.single_apply, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul]

theorem finiteBilateralWeightedShift_coordinate_support (N : ℕ) (w : ℤ → ℂ)
    (p : ℤ × ℤ) (hp : p ∉ bilateralShiftWindow N ×ˢ bilateralShiftWindow N) :
    RHTower.coordMatrix (lpBasis ℤ) (finiteBilateralWeightedShift N w) p = 0 := by
  rcases p with ⟨i, j⟩
  rw [coordMatrix_finiteBilateralWeightedShift]
  apply if_neg
  rintro ⟨hj, hi⟩
  have hj' : 0 ≤ j ∧ j < (N : ℤ) := by simpa only [bilateralShiftEdges, Finset.mem_Ico] using hj
  apply hp
  exact Finset.mem_product.mpr ⟨by simp only [bilateralShiftWindow, Finset.mem_Icc]; omega,
    by simp only [bilateralShiftWindow, Finset.mem_Icc]; omega⟩

theorem finiteBilateralWeightedShift_strict_lower (N : ℕ) (w : ℤ → ℂ) (i j : ℤ)
    (hij : i ≤ j) :
    RHTower.coordMatrix (lpBasis ℤ) (finiteBilateralWeightedShift N w) (i, j) = 0 := by
  rw [coordMatrix_finiteBilateralWeightedShift]
  apply if_neg
  rintro ⟨_, he⟩
  omega

theorem opTrace_finiteBilateralWeightedShift (N : ℕ) (w : ℤ → ℂ) :
    opTrace (finiteBilateralWeightedShift N w) = 0 := by
  rw [opTrace_eq_hsTraceDiag_coordMatrix (lpBasis ℤ) (finiteBilateralWeightedShift_traceClass N w),
    hsTraceDiag]
  have hz : (fun i => RHTower.coordMatrix (lpBasis ℤ) (finiteBilateralWeightedShift N w) (i, i)) =
      fun _ => 0 := funext fun i => finiteBilateralWeightedShift_strict_lower N w i i le_rfl
  rw [hz]
  simp

theorem fredholmDetOp_finiteBilateralWeightedShift (N : ℕ) (w : ℤ → ℂ) :
    RHTower.fredholmDetOp (lpBasis ℤ) (finiteBilateralWeightedShift N w) = 1 :=
  fredholmDetOp_eq_one_of_strict_lower (lpBasis ℤ) (finiteBilateralWeightedShift_traceClass N w)
    (bilateralShiftWindow N) (finiteBilateralWeightedShift_coordinate_support N w)
    (finiteBilateralWeightedShift_strict_lower N w)

end
end GaloisForLFunctions.HTGeometry

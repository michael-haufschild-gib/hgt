import GaloisForLFunctions.HTGeometry.BorisovGabberVasiuDeterminant
import GaloisForLFunctions.RHTower.SourceHorizontalHolomorphicUnitizationOddCompoundNoGo

open scoped BigOperators Matrix
open Matrix

namespace RHTower

/-- The reservoir determinant is division-free, including every value `b i = -1`. -/
theorem bgv_unitizedRealReservoirDeterminant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) :
    unitizedRealReservoirDeterminant b =
      (∏ i, (1 + b i)) - ∑ i, b i * ∏ j ∈ Finset.univ.erase i, (1 + b j) := by
  have hm : (1 + realReservoirDiagonalMatrix b : Matrix ι ι ℝ) =
      diagonal (fun i => 1 + b i) + vecMulVec (fun _ => -1) b := by
    ext i j
    rw [Matrix.add_apply, realReservoirDiagonalMatrix_apply]
    by_cases h : i = j
    · subst j
      simp [realReservoirBaseMatrix, realReservoirOnesMatrix, Matrix.vecMulVec_apply]
    · simp [realReservoirBaseMatrix, realReservoirOnesMatrix, Matrix.vecMulVec_apply, h]
  rw [unitizedRealReservoirDeterminant, hm,
    GaloisForLFunctions.HTGeometry.bgv_det_diagonal_add_vecMulVec]
  simp only [neg_mul, one_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- At a deleted diagonal factor, the determinant is exactly the complementary product. -/
theorem bgv_unitizedRealReservoirDeterminant_replace_neg_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → ℝ) (k : ι) :
    unitizedRealReservoirDeterminant (Function.update b k (-1)) =
      ∏ j ∈ Finset.univ.erase k, (1 + b j) := by
  rw [bgv_unitizedRealReservoirDeterminant]
  have hp : (∏ i, (1 + Function.update b k (-1) i)) = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  rw [hp]
  have hs : (∑ i, Function.update b k (-1) i *
      ∏ j ∈ Finset.univ.erase i, (1 + Function.update b k (-1) j)) =
        -(∏ j ∈ Finset.univ.erase k, (1 + b j)) := by
    rw [Finset.sum_eq_single k]
    · simp only [Function.update_self, neg_one_mul]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
    · intro i _ hik
      have hk : k ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hik.symm, Finset.mem_univ k⟩
      rw [Finset.prod_eq_zero hk (by simp), mul_zero]
    · simp
  rw [hs, zero_sub, neg_neg]

end RHTower

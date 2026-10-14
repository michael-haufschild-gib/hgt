import GaloisForLFunctions.HTGeometry.FiniteBilateralWeightedShiftGram

/-! # Linear combinations of finite bilateral weighted shifts -/

namespace GaloisForLFunctions.HTGeometry
open HilbertSchmidt ContinuousLinearMap InnerProductSpace
noncomputable section

theorem finiteBilateralWeightedShift_smul (N : ℕ) (w : ℤ → ℂ) (z : ℂ) :
    z • finiteBilateralWeightedShift N w =
      finiteBilateralWeightedShift N (fun j => z * w j) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [finiteBilateralWeightedShift, smul_apply, FunLike.coe_sum, Finset.sum_apply,
    rankOne_apply, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

theorem finiteBilateralWeightedShift_sum {ι : Type*} (s : Finset ι) (N : ℕ) (w : ι → ℤ → ℂ) :
    (∑ i ∈ s, finiteBilateralWeightedShift N (w i)) =
      finiteBilateralWeightedShift N (fun j => ∑ i ∈ s, w i j) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [finiteBilateralWeightedShift, FunLike.coe_sum, Finset.sum_apply, rankOne_apply,
    Finset.sum_smul, Finset.smul_sum]
  rw [Finset.sum_comm]

theorem prod_bilateralShiftEdges {M : Type*} [CommMonoid M] (N : ℕ) (f : ℤ → M) :
    (∏ j ∈ bilateralShiftEdges N, f j) = ∏ j ∈ Finset.range N, f (j : ℤ) := by
  apply Finset.prod_bij (fun j _ => j.toNat)
  · intro j hj
    simp only [bilateralShiftEdges, Finset.mem_Ico] at hj
    exact Finset.mem_range.mpr (by omega)
  · intro j hj k hk h
    simp only [bilateralShiftEdges, Finset.mem_Ico] at hj hk
    omega
  · intro j hj
    refine ⟨j, ?_, by simp⟩
    simp only [bilateralShiftEdges, Finset.mem_Ico]
    have := Finset.mem_range.mp hj
    omega
  · intro j hj
    have : 0 ≤ j := (Finset.mem_Ico.mp hj).1
    simp [Int.toNat_of_nonneg this]

end
end GaloisForLFunctions.HTGeometry

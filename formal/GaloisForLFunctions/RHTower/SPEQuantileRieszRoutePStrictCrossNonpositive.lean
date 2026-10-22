import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePolarParabolicCrossKernelRankFactorization
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePSourceIntegerHistoryNoGo

/-!
# Cofinal failure of positive-semidefinite strict-cross landing

The full literal Route-P/SP-E strict-cross source matrix has its all-ones
quadratic form equal to the physical source current. The normalized history
is cofinally unbounded below, so this matrix is not positive semidefinite at
arbitrarily late physical heads.

Thus a positive rank-one environment block cannot be identified with the
complete signed current without an additional indefinite channel or
source-derived compensator. This does not construct that channel, bound its
cofinal action, or prove RH.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

open Matrix

private theorem routeP_crossKernel_diagonal_zero (n : ℕ) :
    ccmActualHeadMatchedQuantileParabolicCrossKernelValue n n = 0 := by
  unfold ccmActualHeadMatchedQuantileParabolicCrossKernelValue
  rw [ccmActualHeadQuantileParabolicPairing_self_eq_matched]
  ring

private theorem routeP_sourceCurrent_eq_all_crossKernel_sum (K : ℕ) :
    ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
        (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) =
      ∑ m ∈ Finset.range (K + 1), ∑ n ∈ Finset.range (K + 1),
        ccmActualHeadMatchedQuantileParabolicCrossKernelValue (m + 2) (n + 2) := by
  rw [ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_strictCross]
  apply Finset.sum_congr rfl
  intro m hm
  have h := Finset.sum_erase_add (Finset.range (K + 1))
    (fun n => ccmActualHeadMatchedQuantileParabolicCrossKernelValue (m + 2) (n + 2)) hm
  rw [routeP_crossKernel_diagonal_zero] at h
  simp only [add_zero] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro n hn
  rfl

/-- Exact positive survivor of the matrix obstruction: the complete signed
strict-cross current is the all-ones quadratic form of its literal finite
source matrix. No source sign is imposed. -/
theorem routeP_crossKernel_ones_quadratic_eq_sourceCurrent (K : ℕ) :
    dotProduct (fun _ : Fin (K + 1) => (1 : ℝ))
        ((ccmActualHeadMatchedQuantileParabolicCrossKernelMatrix K).mulVec
          (fun _ : Fin (K + 1) => (1 : ℝ))) =
      ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
        (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) := by
  rw [routeP_sourceCurrent_eq_all_crossKernel_sum]
  simp only [dotProduct, Matrix.mulVec, one_mul, mul_one,
    ccmActualHeadMatchedQuantileParabolicCrossKernelMatrix]
  rw [← Fin.sum_univ_eq_sum_range
    (fun m : ℕ => ∑ n ∈ Finset.range (K + 1),
      ccmActualHeadMatchedQuantileParabolicCrossKernelValue (m + 2) (n + 2)) (K + 1)]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Fin.sum_univ_eq_sum_range
    (fun n : ℕ =>
      ccmActualHeadMatchedQuantileParabolicCrossKernelValue (m.val + 2) (n + 2))
      (K + 1)]

/-- Arbitrarily late literal heads have a negative all-ones strict-cross
quadratic form, so their full source matrix is not positive semidefinite. -/
theorem routeP_cofinal_strictCrossMatrix_not_posSemidef (M : ℕ) :
    ∃ K : ℕ, M ≤ K ∧
      ¬ (ccmActualHeadMatchedQuantileParabolicCrossKernelMatrix K).PosSemidef := by
  obtain ⟨K, hKM, hnegative⟩ :=
    routeP_normalized_history_cofinally_unbounded_below 0 M
  refine ⟨K, hKM, ?_⟩
  intro hpsd
  have hmass : 0 < ccmActualHeadParabolicMass K :=
    ccmActualHeadParabolicMass_pos K
  have hsource :
      ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
          (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) < 0 := by
    rw [ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect_eq_sourceCurrent]
      at hnegative
    have h := (div_lt_iff₀ hmass).mp hnegative
    simpa using h
  have hquad := hpsd.dotProduct_mulVec_nonneg
    (fun _ : Fin (K + 1) => (1 : ℝ))
  have hquad' : 0 ≤ dotProduct (fun _ : Fin (K + 1) => (1 : ℝ))
      ((ccmActualHeadMatchedQuantileParabolicCrossKernelMatrix K).mulVec
        (fun _ : Fin (K + 1) => (1 : ℝ))) := by
    simpa using hquad
  rw [routeP_crossKernel_ones_quadratic_eq_sourceCurrent] at hquad'
  linarith

end
end RHTower

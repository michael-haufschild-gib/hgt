import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanCanonicalDeterminant

/-!
# Rank-two canonical determinant-root profile

The determinant root occurring in rank-two Minkowski reduction separates exactly into one fixed
coordinate-volume factor and the exponential of half the weighted local log-determinant mean.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder Matrix NumberField BigOperators

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- In rank two, the canonical determinant root is a fixed coordinate factor times one half of
the weighted local log-determinant mean. -/
theorem rpow_numberFieldArchimedeanCanonicalMatrix_rankTwo
    (A : numberFieldArchimedeanPositiveForms K 2) :
    Real.rpow (numberFieldArchimedeanCanonicalMatrix A).det
        (((2 * Module.finrank ℚ K : ℕ) : ℝ)⁻¹) =
      Real.exp
          (Real.log ((numberFieldArchimedeanSquareCoordinateMatrix
            (K := K) (n := 2)).det ^ 2) *
            (((2 * Module.finrank ℚ K : ℕ) : ℝ)⁻¹)) *
        Real.exp ((1 / 2 : ℝ) *
          numberFieldWeightedPlaceMean
            (fun w ↦ Real.log (numberFieldArchimedeanDet A w))) := by
  let c : ℝ := (numberFieldArchimedeanSquareCoordinateMatrix
    (K := K) (n := 2)).det
  let M : ℝ := numberFieldWeightedPlaceMean
    (fun w ↦ Real.log (numberFieldArchimedeanDet A w))
  have hc : c ≠ 0 :=
    numberFieldArchimedeanSquareCoordinateMatrix_det_ne_zero
      (K := K) (n := 2)
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  have hd : (0 : ℝ) < Module.finrank ℚ K := by
    rw [← numberFieldInfinitePlaceWeight_eq_finrank (K := K)]
    exact numberFieldInfinitePlaceWeight_pos (K := K)
  have hdet : 0 < (numberFieldArchimedeanCanonicalMatrix A).det :=
    (numberFieldArchimedeanCanonicalMatrix_posDef A).det_pos
  change (numberFieldArchimedeanCanonicalMatrix A).det ^
      (((2 * Module.finrank ℚ K : ℕ) : ℝ)⁻¹) = _
  rw [Real.rpow_def_of_pos hdet]
  rw [det_numberFieldArchimedeanCanonicalMatrix_eq_coordinate_exp]
  rw [numberFieldInfinitePlaceWeight_eq_finrank]
  change Real.exp
      (Real.log (c ^ 2 * Real.exp (Module.finrank ℚ K * M)) *
        (((2 * Module.finrank ℚ K : ℕ) : ℝ)⁻¹)) = _
  rw [Real.log_mul hc2.ne' (Real.exp_ne_zero _), Real.log_exp, add_mul,
    Real.exp_add]
  congr 1
  congr 1
  norm_num [Nat.cast_mul]
  field_simp [ne_of_gt hd]
  ring

end

end GaloisForLFunctions.HTGeometry

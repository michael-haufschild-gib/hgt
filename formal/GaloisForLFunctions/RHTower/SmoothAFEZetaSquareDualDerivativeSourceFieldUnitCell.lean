import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualDerivativeSourceField
import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualDerivativeUnitCellAffineMeanSquare

noncomputable section

open Complex Set MeasureTheory Filter Topology

namespace RHTower

/-- Unit-cell affine energy for the literal, phase-faithful carrier-height source. -/
theorem exists_integral_unitCell_normSq_smoothAFEZetaSquareDualDerivativeSourceField_reflected_le_logCube :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {N : ℕ} {r center : ℝ}, 4 ≤ N →
        r ∈ Set.Icc (N : ℝ) (2 * N : ℝ) →
        (∫ y in Set.Icc (-1 : ℝ) 1,
          ‖smoothAFEZetaSquareDualDerivativeSourceField
            (N : ℝ) r (center - y)‖ ^ (2 : ℕ)) ≤
          K * (1 + Real.log (N : ℝ)) ^ (3 : ℕ) / (N : ℝ) := by
  obtain ⟨K, hK, hmv⟩ :=
    exists_integral_unitCell_normSq_smoothAFEZetaSquareDualDerivativeLSeries_le_logCube
  refine ⟨K, hK, ?_⟩
  intro N r center hN hr
  have hN0 : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hr4 : (4 : ℝ) ≤ r :=
    (by exact_mod_cast hN : (4 : ℝ) ≤ N) |>.trans hr.1
  have hbound := hmv (center := center) hN hr
  have heq :
      (fun y : ℝ =>
        ‖LSeries
          (smoothAFEZetaSquareDualDerivativeNatCoefficient (N : ℝ) r center)
          ((y : ℝ) * I)‖ ^ (2 : ℕ)) =
      (fun y : ℝ =>
        ‖smoothAFEZetaSquareDualDerivativeSourceField
          (N : ℝ) r (center - y)‖ ^ (2 : ℕ)) := by
    funext y
    rw [smoothAFEZetaSquareDualDerivativeLSeries_eq_sourceField hr4 hN0]
  rwa [heq] at hbound

/-- Physical unit-cell form of the literal source energy. -/
theorem exists_integral_unitCell_normSq_smoothAFEZetaSquareDualDerivativeSourceField_le_logCube :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {N : ℕ} {r center : ℝ}, 4 ≤ N →
        r ∈ Set.Icc (N : ℝ) (2 * N : ℝ) →
        (∫ t in Set.Icc (center - 1) (center + 1),
          ‖smoothAFEZetaSquareDualDerivativeSourceField (N : ℝ) r t‖ ^ (2 : ℕ)) ≤
          K * (1 + Real.log (N : ℝ)) ^ (3 : ℕ) / (N : ℝ) := by
  obtain ⟨K, hK, hmv⟩ :=
    exists_integral_unitCell_normSq_smoothAFEZetaSquareDualDerivativeSourceField_reflected_le_logCube
  refine ⟨K, hK, ?_⟩
  intro N r center hN hr
  have hreflect :
      (∫ y in Set.Icc (-1 : ℝ) 1,
          ‖smoothAFEZetaSquareDualDerivativeSourceField
            (N : ℝ) r (center - y)‖ ^ (2 : ℕ)) =
        ∫ t in Set.Icc (center - 1) (center + 1),
          ‖smoothAFEZetaSquareDualDerivativeSourceField (N : ℝ) r t‖ ^ (2 : ℕ) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    rw [intervalIntegral.integral_comp_sub_left
      (fun t : ℝ =>
        ‖smoothAFEZetaSquareDualDerivativeSourceField (N : ℝ) r t‖ ^ (2 : ℕ))
      center]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : center - 1 ≤ center + 1)]
    congr 1
    all_goals ring
  rw [← hreflect]
  exact hmv hN hr

end RHTower

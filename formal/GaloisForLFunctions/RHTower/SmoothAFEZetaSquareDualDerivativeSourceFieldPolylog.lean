import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualDerivativeSourceField
import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualDerivativePlainMassPolylog

/-! # Polylogarithmic physical-cell mean square for the square-dual derivative source -/

noncomputable section

open Complex Set MeasureTheory Filter Topology

namespace RHTower

theorem exists_integral_normSq_smoothAFEZetaSquareDualDerivativeSourceField_reflected_le_polylog :
    ∃ A K : ℝ, 0 ≤ A ∧ 0 ≤ K ∧
      ∀ {N : ℕ} {r center H : ℝ}, 4 ≤ N →
        r ∈ Set.Icc (N : ℝ) (2 * N : ℝ) → 1 ≤ H →
        (∫ y in Set.Icc (-H) H,
          ‖smoothAFEZetaSquareDualDerivativeSourceField
            (N : ℝ) r (center - y)‖ ^ (2 : ℕ)) ≤
          5 * Real.pi * Real.exp 1 *
              (K * (1 + Real.log (N : ℝ)) ^ (3 : ℕ) / (N : ℝ)) +
            (5 * Real.pi / 2) *
              (A * (1 + Real.log (N : ℝ)) ^ (4 : ℕ) / (N : ℝ) ^ (2 : ℕ)) * H := by
  obtain ⟨A, K, hA, hK, hmv⟩ :=
    exists_integral_normSq_smoothAFEZetaSquareDualDerivativeLSeries_le_polylog
  refine ⟨A, K, hA, hK, ?_⟩
  intro N r center H hN hr hH
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hr4 : (4 : ℝ) ≤ r :=
    (by exact_mod_cast hN : (4 : ℝ) ≤ N) |>.trans hr.1
  have hbound := hmv (center := center) hN hr hH
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

theorem exists_integral_normSq_smoothAFEZetaSquareDualDerivativeSourceField_le_polylog :
    ∃ A K : ℝ, 0 ≤ A ∧ 0 ≤ K ∧
      ∀ {N : ℕ} {r center H : ℝ}, 4 ≤ N →
        r ∈ Set.Icc (N : ℝ) (2 * N : ℝ) → 1 ≤ H →
        (∫ t in Set.Icc (center - H) (center + H),
          ‖smoothAFEZetaSquareDualDerivativeSourceField (N : ℝ) r t‖ ^ (2 : ℕ)) ≤
          5 * Real.pi * Real.exp 1 *
              (K * (1 + Real.log (N : ℝ)) ^ (3 : ℕ) / (N : ℝ)) +
            (5 * Real.pi / 2) *
              (A * (1 + Real.log (N : ℝ)) ^ (4 : ℕ) / (N : ℝ) ^ (2 : ℕ)) * H := by
  obtain ⟨A, K, hA, hK, hmv⟩ :=
    exists_integral_normSq_smoothAFEZetaSquareDualDerivativeSourceField_reflected_le_polylog
  refine ⟨A, K, hA, hK, ?_⟩
  intro N r center H hN hr hH
  have hleft : center - H ≤ center + H := by linarith
  have hreflect :
      (∫ y in Set.Icc (-H) H,
          ‖smoothAFEZetaSquareDualDerivativeSourceField
            (N : ℝ) r (center - y)‖ ^ (2 : ℕ)) =
        ∫ t in Set.Icc (center - H) (center + H),
          ‖smoothAFEZetaSquareDualDerivativeSourceField (N : ℝ) r t‖ ^ (2 : ℕ) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -H ≤ H)]
    rw [intervalIntegral.integral_comp_sub_left
      (fun t : ℝ =>
        ‖smoothAFEZetaSquareDualDerivativeSourceField (N : ℝ) r t‖ ^ (2 : ℕ))
      center]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hleft]
    congr 1
    all_goals ring
  rw [← hreflect]
  exact hmv hN hr hH

end RHTower

import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualDerivativeDivisorSquareAffineMeanSquare

noncomputable section

open Complex Set MeasureTheory

namespace RHTower

private theorem normSq_natCoefficient_le_weighted
    (T r center : ℝ) (k : ℕ) :
    ‖smoothAFEZetaSquareDualDerivativeNatCoefficient T r center k‖ ^ (2 : ℕ) ≤
      (k : ℝ) *
        ‖smoothAFEZetaSquareDualDerivativeNatCoefficient T r center k‖ ^ (2 : ℕ) := by
  cases k with
  | zero => simp
  | succ k =>
      calc
        ‖smoothAFEZetaSquareDualDerivativeNatCoefficient T r center (k + 1)‖ ^ (2 : ℕ) =
            1 * ‖smoothAFEZetaSquareDualDerivativeNatCoefficient T r center (k + 1)‖ ^ (2 : ℕ) := by
              ring
        _ ≤ ((k + 1 : ℕ) : ℝ) *
            ‖smoothAFEZetaSquareDualDerivativeNatCoefficient T r center (k + 1)‖ ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)

theorem tsum_norm_smoothAFEZetaSquareDualDerivativeNatCoefficient_sq_le_weighted
    {T r center : ℝ} (hr : 4 ≤ r) (hT : 0 < T) :
    (∑' k : ℕ,
      ‖smoothAFEZetaSquareDualDerivativeNatCoefficient T r center k‖ ^ (2 : ℕ)) ≤
      ∑' k : ℕ,
        (k : ℝ) *
          ‖smoothAFEZetaSquareDualDerivativeNatCoefficient T r center k‖ ^ (2 : ℕ) := by
  obtain ⟨_, hplain, hweighted⟩ :=
    summable_smoothAFEZetaSquareDualDerivativeNatCoefficient_affine_masses
      (center := center) hr hT
  exact hplain.tsum_le_tsum
    (normSq_natCoefficient_le_weighted T r center) hweighted

/-- On every dyadic block, the phase-faithful square-dual height derivative has
unit-cell affine mean square `O(log^(3 : ℕ) N / N)`. -/
theorem exists_integral_unitCell_normSq_smoothAFEZetaSquareDualDerivativeLSeries_le_logCube :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {N : ℕ} {r center : ℝ}, 4 ≤ N →
        r ∈ Set.Icc (N : ℝ) (2 * N : ℝ) →
        (∫ y in Set.Icc (-1 : ℝ) 1,
          ‖LSeries
            (smoothAFEZetaSquareDualDerivativeNatCoefficient (N : ℝ) r center)
            ((y : ℝ) * I)‖ ^ (2 : ℕ)) ≤
          K * (1 + Real.log (N : ℝ)) ^ (3 : ℕ) / (N : ℝ) := by
  obtain ⟨K₀, hK₀, hmass⟩ :=
    exists_tsum_weighted_norm_smoothAFEZetaSquareDualDerivativeCoefficient_sq_le_logCube
  let K := (5 * Real.pi * Real.exp 1 + 5 * Real.pi / 2) * K₀
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro N r center hN hr
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hr4 : (4 : ℝ) ≤ r :=
    (by exact_mod_cast hN : (4 : ℝ) ≤ N) |>.trans hr.1
  obtain ⟨habs, hplain, hweighted⟩ :=
    summable_smoothAFEZetaSquareDualDerivativeNatCoefficient_affine_masses
      (center := center) hr4 hN0
  have hmv :=
    RHTower.Sieve.integral_Icc_normSq_LSeries_le_general_affine_infinite
      (a := smoothAFEZetaSquareDualDerivativeNatCoefficient (N : ℝ) r center)
      (smoothAFEZetaSquareDualDerivativeNatCoefficient_zero _ _ _) 0
      (by simpa using habs) (by simpa using hplain) (by simpa using hweighted)
      (show (1 : ℝ) ≤ 1 by norm_num)
  have hmv' :
      (∫ y in Set.Icc (-1 : ℝ) 1,
        ‖LSeries
          (smoothAFEZetaSquareDualDerivativeNatCoefficient (N : ℝ) r center)
          ((y : ℝ) * I)‖ ^ (2 : ℕ)) ≤
        5 * Real.pi * Real.exp 1 *
            (∑' k : ℕ, (k : ℝ) *
              ‖smoothAFEZetaSquareDualDerivativeNatCoefficient
                (N : ℝ) r center k‖ ^ (2 : ℕ)) +
          (5 * Real.pi / 2) *
            (∑' k : ℕ,
              ‖smoothAFEZetaSquareDualDerivativeNatCoefficient
                (N : ℝ) r center k‖ ^ (2 : ℕ)) := by
    simpa using hmv
  have hweightedMass :
      (∑' k : ℕ, (k : ℝ) *
        ‖smoothAFEZetaSquareDualDerivativeNatCoefficient
          (N : ℝ) r center k‖ ^ (2 : ℕ)) ≤
        K₀ * (1 + Real.log (N : ℝ)) ^ (3 : ℕ) / (N : ℝ) := by
    rw [tsum_weighted_norm_smoothAFEZetaSquareDualDerivativeNatCoefficient_sq_eq
      (center := center) hr4 hN0]
    exact hmass (center := center) hN hr
  have hplainWeighted :=
    tsum_norm_smoothAFEZetaSquareDualDerivativeNatCoefficient_sq_le_weighted
      (center := center) hr4 hN0
  calc
    (∫ y in Set.Icc (-1 : ℝ) 1,
        ‖LSeries
          (smoothAFEZetaSquareDualDerivativeNatCoefficient (N : ℝ) r center)
          ((y : ℝ) * I)‖ ^ (2 : ℕ))
        ≤ 5 * Real.pi * Real.exp 1 *
            (∑' k : ℕ, (k : ℝ) *
              ‖smoothAFEZetaSquareDualDerivativeNatCoefficient
                (N : ℝ) r center k‖ ^ (2 : ℕ)) +
          (5 * Real.pi / 2) *
            (∑' k : ℕ,
              ‖smoothAFEZetaSquareDualDerivativeNatCoefficient
                (N : ℝ) r center k‖ ^ (2 : ℕ)) := hmv'
    _ ≤ (5 * Real.pi * Real.exp 1 + 5 * Real.pi / 2) *
          (∑' k : ℕ, (k : ℝ) *
            ‖smoothAFEZetaSquareDualDerivativeNatCoefficient
              (N : ℝ) r center k‖ ^ (2 : ℕ)) := by
      calc
        _ ≤ 5 * Real.pi * Real.exp 1 *
              (∑' k : ℕ, (k : ℝ) *
                ‖smoothAFEZetaSquareDualDerivativeNatCoefficient
                  (N : ℝ) r center k‖ ^ (2 : ℕ)) +
            (5 * Real.pi / 2) *
              (∑' k : ℕ, (k : ℝ) *
                ‖smoothAFEZetaSquareDualDerivativeNatCoefficient
                  (N : ℝ) r center k‖ ^ (2 : ℕ)) := by
            exact add_le_add le_rfl
              (mul_le_mul_of_nonneg_left hplainWeighted (by positivity))
        _ = _ := by ring
    _ ≤ (5 * Real.pi * Real.exp 1 + 5 * Real.pi / 2) *
          (K₀ * (1 + Real.log (N : ℝ)) ^ (3 : ℕ) / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hweightedMass (by positivity)
    _ = K * (1 + Real.log (N : ℝ)) ^ (3 : ℕ) / (N : ℝ) := by
      dsimp only [K]
      ring

end RHTower

import GaloisForLFunctions.ConjugateDiagonalGeometry.FiniteThetaReadingError

/-!
# Finite theta readings recover compact currents

For each compactly supported C² test, the prescribed integer theta-prefix
reading tends to the multiplicity-exact zeta divisor trace. Its error is bounded
by a test-dependent constant times `exp(-n⁴ + 56n² + 62)`.
-/

open Complex MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Laplacian Topology

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

noncomputable section

private theorem compact_source_decay_bound {C : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    (Real.pi * ((n : ℝ) + 2) ^ 2 / 2 + 8 * C * ((n : ℝ) + 1) ^ 6) *
        Real.exp (-(((n : ℝ) + 1) ^ 4)) ≤
      (2 * Real.pi + 8 * C) * Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) := by
  have h := source_poly_exp_window_le hC 0 n 0 0
    (by simpa only [abs_zero] using Nat.cast_nonneg (α := ℝ) n)
    (by simp only [Nat.cast_zero, abs_zero, zero_mul];
        exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith only [Nat.cast_nonneg (α := ℝ) n])))
  simp only [abs_zero, Nat.cast_zero, zero_mul, add_zero] at h
  refine le_trans ?_ h
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  linarith only [sq_nonneg ((n : ℝ) + 3)]

/-- Compact tests have a quartic exponential current error along the prescribed theta prefixes. -/
theorem exists_finiteTheta_compact_current_error (φ : ℂ → ℝ)
    (hp : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop,
      |finiteThetaSourceReading φ n - zetaSourceTrace φ| ≤
        B * Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) := by
  let Δφ : BoundedContinuousFunction ℂ ℝ :=
    ofCompactSupport (Δ φ) (continuous_test_laplacian hp)
      (compact_test_laplacian hp hc)
  let B := ‖Δφ‖
  have hB : 0 ≤ B := norm_nonneg _
  have hbound (z : ℂ) : |Δ φ z| ≤ B := by
    change ‖Δφ z‖ ≤ ‖Δφ‖
    exact Δφ.norm_coe_le_norm z
  obtain ⟨C, hC, hlocal⟩ := exists_explicitSourceLocalError_bound
  let K := 2 * B * finiteThetaPotentialConstant + (2 * Real.pi)⁻¹ * B * (2 * Real.pi + 8 * C)
  have hK : 0 ≤ K := by
    have hF := finiteThetaPotentialConstant_nonneg
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [sourceCutoff_eventually_mul_eq_self hc, eventually_ge_atTop 1] with n hn hn1
  have hb : ∀ z ∈ closedBall (0 : ℂ) |(n : ℝ) + 2|,
      |Δ (fun w => sourceCutoff n w * φ w) z| ≤ sourceCutoffControl n * B := by
    intro z _
    rw [hn]
    exact (hbound z).trans (by nlinarith only [one_le_sourceCutoffControl n, hB])
  have hf := abs_finiteThetaSourceReading_sub_explicit_le φ hp hn1 hB hb
  have hs := abs_explicitSourceReading_sub_current_le φ hp n hb
  rw [hn, xiCurrentPairing_eq_trace φ hp hc] at hs
  have hf' : |finiteThetaSourceReading φ n - explicitSourceReading φ n| ≤
      (2 * B * finiteThetaPotentialConstant) *
        Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) := by
    have hF := finiteThetaPotentialConstant_nonneg
    have h := mul_le_mul_of_nonneg_left (compact_source_decay_bound (C := 0) (by norm_num) n)
      (show 0 ≤ B * finiteThetaPotentialConstant / Real.pi by positivity)
    simp only [mul_zero, zero_mul, add_zero] at h
    have heq : (2 * Real.pi)⁻¹ * B * finiteThetaPotentialConstant *
        Real.exp (-(((n : ℝ) + 1) ^ 4)) * (Real.pi * ((n : ℝ) + 2) ^ 2) =
      B * finiteThetaPotentialConstant / Real.pi *
        (Real.pi * ((n : ℝ) + 2) ^ 2 / 2 * Real.exp (-(((n : ℝ) + 1) ^ 4))) := by
      field_simp
    rw [heq] at hf
    exact hf.trans (h.trans_eq (by field_simp))
  have hs' : |explicitSourceReading φ n - zetaSourceTrace φ| ≤
      ((2 * Real.pi)⁻¹ * B * (2 * Real.pi + 8 * C)) *
        Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) := by
    have h := (hlocal n hn1).trans (compact_source_decay_bound hC.le n)
    have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ (2 * Real.pi)⁻¹ * B by positivity)
    exact hs.trans (by nlinarith only [hm])
  have ht := dist_triangle (finiteThetaSourceReading φ n) (explicitSourceReading φ n)
    (zetaSourceTrace φ)
  simp only [Real.dist_eq] at ht
  exact (ht.trans (add_le_add hf' hs')).trans_eq (by dsimp only [K]; ring)

/-- Finite integer theta curvature recovers every compactly supported C² divisor test. -/
theorem tendsto_finiteThetaSourceReading_compact (φ : ℂ → ℝ)
    (hp : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    Tendsto (finiteThetaSourceReading φ) atTop (𝓝 (zetaSourceTrace φ)) := by
  obtain ⟨B, _, hb⟩ := exists_finiteTheta_compact_current_error φ hp hc
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hb.and ((tendsto_explicitWindowError B).eventually_lt_const hε))
  refine ⟨N, fun n hn => ?_⟩
  simpa only [Real.dist_eq] using (hN n hn).1.trans_lt (hN n hn).2

#print axioms tendsto_finiteThetaSourceReading_compact

end

end GaloisForLFunctions.ConjugateDiagonalGeometry

import GaloisForLFunctions.RHTower.PaperCriticalFeatureXiHistogram

/-!
# Native HCF variance controlled by actual Xi histogram entropy

The source boundary alias, its phase variance, and its normalized saving all admit
an unconditional entropy budget. The grid reference and quantization errors are
explicit; any further cofinal estimate must control the actual arithmetic
histogram deficit at an appropriate source-dependent resolution.
-/

open GaloisForLFunctions.HTGeometry FourierLLogL MeasureTheory

namespace RHTower

noncomputable section

private theorem histogram_deficit_bdd (n N : ℕ) :
    BddAbove (Set.range fun theta : ℝ => Real.log ((N + 1 : ℕ) : ℝ) -
      (paperCriticalFeatureXiHistogram n N theta).entropy) := by
  refine ⟨Real.log ((N + 1 : ℕ) : ℝ), ?_⟩
  rintro _ ⟨theta, rfl⟩
  exact sub_le_self _ (Law.entropy_nonneg _)

/-- Maximum entropy deficit of the literal Xi phase histogram over phase shifts. -/
def paperCriticalFeatureXiEntropyDeficit (n N : ℕ) : ℝ :=
  ⨆ theta : ℝ, Real.log ((N + 1 : ℕ) : ℝ) -
    (paperCriticalFeatureXiHistogram n N theta).entropy

theorem paperCriticalFeatureXiHistogram_deficit_le (n N : ℕ) (theta : ℝ) :
    Real.log ((N + 1 : ℕ) : ℝ) - (paperCriticalFeatureXiHistogram n N theta).entropy ≤
      paperCriticalFeatureXiEntropyDeficit n N :=
  le_ciSup (histogram_deficit_bdd n N) theta

theorem paperCriticalFeatureXiEntropyDeficit_nonneg (n N : ℕ) :
    0 ≤ paperCriticalFeatureXiEntropyDeficit n N := by
  have h := Law.entropy_le_log_card (paperCriticalFeatureXiHistogram n N 0)
  simp only [Fintype.card_fin] at h
  exact (sub_nonneg.mpr h).trans (paperCriticalFeatureXiHistogram_deficit_le n N 0)

theorem paperCriticalFeatureXiEntropyDeficit_le_log (n N : ℕ) :
    paperCriticalFeatureXiEntropyDeficit n N ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
  ciSup_le fun _ => sub_le_self _ (Law.entropy_nonneg _)

/-- A fully paid uniform alias budget using the actual arithmetic phase histogram. -/
def paperCriticalFeatureXiEntropyBudget (n N : ℕ) : ℝ :=
  paperCriticalFeatureXiLineMass n *
    (|(criticalFeatureUniformGridAlias (N + 1)).re| + paperCriticalFeatureQuantizationError N +
      (37 : ℝ) / 100 * Real.sqrt (paperCriticalFeatureXiEntropyDeficit n N))

theorem paperCriticalFeatureXiEntropyBudget_nonneg (n N : ℕ) :
    0 ≤ paperCriticalFeatureXiEntropyBudget n N := by
  unfold paperCriticalFeatureXiEntropyBudget
  exact mul_nonneg (paperCriticalFeatureXiLineMass_nonneg n)
    (add_nonneg (add_nonneg (abs_nonneg _) (paperCriticalFeatureQuantizationError_nonneg N))
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _)))

/-- The actual source boundary alias obeys the same phase-uniform entropy budget. -/
theorem paperCriticalFeatureSourceAlias_entropy_budget (n N : ℕ) (theta : ℝ) :
    |criticalFeatureCompactSourceBoundaryAliasAtPhase n theta| ≤
      paperCriticalFeatureXiEntropyBudget n N := by
  let A := criticalFeatureCompactSourceBoundaryAliasAtPhase n theta
  let M := paperCriticalFeatureXiLineMass n
  let U := (criticalFeatureUniformGridAlias (N + 1)).re
  have hM : 0 ≤ M := paperCriticalFeatureXiLineMass_nonneg n
  have he := paperCriticalFeatureXiAlias_entropy n N theta
  have hd := Real.sqrt_le_sqrt (paperCriticalFeatureXiHistogram_deficit_le n N theta)
  calc
    |A| = |(A - M * U) + M * U| := by congr 1; ring
    _ ≤ |A - M * U| + |M * U| := abs_add_le _ _
    _ ≤ M * (paperCriticalFeatureQuantizationError N + (37 : ℝ) / 100 *
        Real.sqrt (Real.log ((N + 1 : ℕ) : ℝ) -
          (paperCriticalFeatureXiHistogram n N theta).entropy)) + M * |U| := by
      rw [abs_mul, abs_of_nonneg hM]
      exact _root_.add_le_add he le_rfl
    _ ≤ M * (paperCriticalFeatureQuantizationError N + (37 : ℝ) / 100 *
        Real.sqrt (paperCriticalFeatureXiEntropyDeficit n N)) + M * |U| := by
      have hc : (37 : ℝ) / 100 *
          Real.sqrt (Real.log ((N + 1 : ℕ) : ℝ) -
            (paperCriticalFeatureXiHistogram n N theta).entropy) ≤
          (37 : ℝ) / 100 * Real.sqrt (paperCriticalFeatureXiEntropyDeficit n N) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
      exact _root_.add_le_add
        (mul_le_mul_of_nonneg_left (_root_.add_le_add le_rfl hc) hM) le_rfl
    _ = paperCriticalFeatureXiEntropyBudget n N := by
      unfold paperCriticalFeatureXiEntropyBudget
      dsimp [M, U]
      ring

/-- Integrating the actual continuous source alias pays the native HCF variance receiver. -/
theorem paperCriticalFeatureSourceVariance_entropy_budget (n N : ℕ) :
    criticalFeatureCompactSourceBoundaryAliasRealVariance n ≤
      (paperCriticalFeatureXiEntropyBudget n N) ^ (2 : ℕ) := by
  let B := paperCriticalFeatureXiEntropyBudget n N
  have hB : 0 ≤ B := paperCriticalFeatureXiEntropyBudget_nonneg n N
  have hsquare (theta : ℝ) :
      (criticalFeatureCompactSourceBoundaryAliasAtPhase n theta) ^ (2 : ℕ) ≤ B ^ (2 : ℕ) := by
    have h := paperCriticalFeatureSourceAlias_entropy_budget n N theta
    have hp := mul_nonneg (sub_nonneg.mpr h)
      (add_nonneg hB (abs_nonneg (criticalFeatureCompactSourceBoundaryAliasAtPhase n theta)))
    nlinarith only [hp, sq_abs (criticalFeatureCompactSourceBoundaryAliasAtPhase n theta)]
  unfold criticalFeatureCompactSourceBoundaryAliasRealVariance
  have h : (∫ theta in (0 : ℝ)..1,
        (criticalFeatureCompactSourceBoundaryAliasAtPhase n theta) ^ (2 : ℕ)) ≤
      ∫ _theta in (0 : ℝ)..1, B ^ (2 : ℕ) :=
    intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 from zero_le_one)
    (((continuous_criticalFeatureCompactSourceBoundaryAliasAtPhase n).pow 2).intervalIntegrable 0 1)
    (continuous_const.intervalIntegrable 0 1) (fun theta _ => hsquare theta)
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] using h

/-- The native variance-saving quantity receives the entropy budget with its actual envelope. -/
theorem paperCriticalFeatureVarianceSaving_entropy_budget (n N : ℕ) :
    criticalFeatureCompactSourceBoundaryAliasRealVariance n /
        criticalFeatureCompactSourceBoundaryAliasUpperEnvelope n ≤
      (paperCriticalFeatureXiEntropyBudget n N) ^ (2 : ℕ) /
        criticalFeatureCompactSourceBoundaryAliasUpperEnvelope n :=
  div_le_div_of_nonneg_right (paperCriticalFeatureSourceVariance_entropy_budget n N)
    (criticalFeatureCompactSourceBoundaryAliasUpperEnvelope_nonnegative n)

end

end RHTower

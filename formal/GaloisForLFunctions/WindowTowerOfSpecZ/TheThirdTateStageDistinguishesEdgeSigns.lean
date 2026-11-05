import GaloisForLFunctions.WindowTowerOfSpecZ.TheTateHorizonBeforeNineHalves
import GaloisForLFunctions.WindowTowerOfSpecZ.TheWindowBartaCriterion

/-!
# The third Tate stage is not controlled by absolute edge costs

At dimension one, the seven-vertex Tate form is positive semidefinite.
Reversing every edge sign gives a negative direction. The ratio-four
triangle therefore distinguishes signed positivity from an absolute-cost bound.
-/

noncomputable section

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ MeasureTheory

private theorem thirdStageAlpha_one : thirdStageAlpha 1 = Real.sqrt 2 / 4 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  unfold thirdStageAlpha
  norm_num
  field_simp [hn]
  nlinarith only [hs]

private theorem thirdStageBeta_one : thirdStageBeta 1 = Real.sqrt 3 / 3 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  unfold thirdStageBeta
  norm_num
  field_simp [hn]
  nlinarith only [hs]

private theorem thirdStageChi_one : thirdStageChi 1 = 1 / 2 := by
  norm_num [thirdStageChi]

/-- Every window in the first part of stage three is Tate-positive at dimension one. -/
theorem tateFunction_one_nonneg_beforeNineHalves {A : ℝ}
    (hA4 : Real.log 4 < A) (hA9 : A ≤ Real.log (9 / 2)) :
    ∀ H : ℝ → ℝ, IsWindowTest A H → 0 ≤ tateFunction A H 1 := by
  apply (tateFunction_nonneg_iff_thirdStage_beforeNineHalves hA4 hA9 (by norm_num)).mpr
  rw [thirdStageChi_one, thirdStageAlpha_one, thirdStageBeta_one]
  norm_num [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

/-- Reversing all three edge weights at dimension one produces an exact negative value. -/
theorem thirdStage_all_negative_edges_witness :
    thirdStageSevenForm (-thirdStageAlpha 1) (-thirdStageBeta 1) (-thirdStageChi 1)
      ![7 * Real.sqrt 2 * Real.sqrt 3, 7 * Real.sqrt 3, 7 * Real.sqrt 2 * Real.sqrt 3,
        8 * Real.sqrt 2, 4, 8 * Real.sqrt 2, 4] = -77 := by
  rw [thirdStageSevenForm_vec, thirdStageAlpha_one, thirdStageBeta_one, thirdStageChi_one]
  ring_nf
  norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

private def signComparisonAmplitude (q : ℚ) : ℝ :=
  if q = 1 ∨ q = 4 then 7 * Real.sqrt 2 * Real.sqrt 3 else
    if q = 2 then 7 * Real.sqrt 3 else
      if q = 3 ∨ q = 4 / 3 then 8 * Real.sqrt 2 else 4

private theorem signComparison_graph_value :
    rationalHeckeForm 4
      (fun n => -thirdStageCoefficients (thirdStageAlpha 1) (thirdStageBeta 1) (thirdStageChi 1) n)
      thirdStageNodes signComparisonAmplitude = -77 := by
  have hI : Finset.Icc 2 4 = ({2, 3, 4} : Finset ℕ) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [rationalHeckeForm_eq_neighbor_sum, hI]
  norm_num [thirdStageCoefficients, thirdStageNodes, signComparisonAmplitude,
    thirdStageAlpha_one, thirdStageBeta_one, thirdStageChi_one]
  ring_nf
  norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

private theorem thirdStageCoefficients_one_nonneg (n : ℕ) :
    0 ≤ thirdStageCoefficients (thirdStageAlpha 1) (thirdStageBeta 1) (thirdStageChi 1) n := by
  unfold thirdStageCoefficients
  rw [thirdStageAlpha_one, thirdStageBeta_one, thirdStageChi_one]
  split_ifs <;> positivity

/-- Above ratio four, the dimension-one absolute correlation costs exceed
the norm on some smooth window test. -/
theorem exists_thirdStage_absolute_cost_exceeds_norm {A : ℝ} (hA : Real.log 4 < A) :
    ∃ H : ℝ → ℝ, IsWindowTest A H ∧ (∫ u, H u ^ 2) <
      ∑ n ∈ Finset.Icc 2 4,
        thirdStageCoefficients (thirdStageAlpha 1) (thirdStageBeta 1) (thirdStageChi 1) n *
          |∫ u, H u * H (u + Real.log n)| := by
  have hb : ∀ r ∈ thirdStageNodes, (1 : ℚ) ≤ r ∧ r ≤ 4 := by
    intro r hr
    norm_num only [thirdStageNodes, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hp : ∀ r ∈ thirdStageNodes, (0 : ℚ) < r := fun r hr =>
    lt_of_lt_of_le (by norm_num) (hb r hr).1
  have hs : ∀ r ∈ thirdStageNodes, ∀ s ∈ thirdStageNodes,
      Real.log s - Real.log r < A := by
    intro r hr s hs
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (hb r hr).1
    have hs0 : (0 : ℝ) < s := by exact_mod_cast hp s hs
    have hs4 : (s : ℝ) ≤ 4 := by exact_mod_cast (hb s hs).2
    have hrl := Real.log_nonneg hr1
    have hsl := Real.log_le_log hs0 hs4
    linarith only [hA, hrl, hsl]
  obtain ⟨H, hH, I, hI, he⟩ := exists_windowTest_eq_heckeForm thirdStageNodes hp hs 4
    (fun n => -thirdStageCoefficients (thirdStageAlpha 1) (thirdStageBeta 1) (thirdStageChi 1) n)
    signComparisonAmplitude
  change (∫ u, H u ^ 2) + ∑ n ∈ Finset.Icc 2 4,
      -thirdStageCoefficients (thirdStageAlpha 1) (thirdStageBeta 1) (thirdStageChi 1) n *
        ∫ u, H u * H (u + Real.log n) =
      I * rationalHeckeForm 4
        (fun n => -thirdStageCoefficients (thirdStageAlpha 1) (thirdStageBeta 1) (thirdStageChi 1) n)
        thirdStageNodes signComparisonAmplitude at he
  rw [signComparison_graph_value] at he
  simp only [neg_mul, Finset.sum_neg_distrib] at he
  have hc : (∑ n ∈ Finset.Icc 2 4,
      thirdStageCoefficients (thirdStageAlpha 1) (thirdStageBeta 1) (thirdStageChi 1) n *
        ∫ u, H u * H (u + Real.log n)) ≤
      ∑ n ∈ Finset.Icc 2 4,
        thirdStageCoefficients (thirdStageAlpha 1) (thirdStageBeta 1) (thirdStageChi 1) n *
          |∫ u, H u * H (u + Real.log n)| := by
    exact Finset.sum_le_sum fun n _ =>
      mul_le_mul_of_nonneg_left (le_abs_self _) (thirdStageCoefficients_one_nonneg n)
  refine ⟨H, hH, ?_⟩
  linarith only [he, hI, hc]

/-- Dimension-one Tate weights admit no bounded positive Barta weight
for their absolute edge costs once ratio four is visible. -/
theorem no_thirdStage_absolute_cost_balancing_weight {A : ℝ} (hA : Real.log 4 < A) :
    ¬ ∃ (h : ℝ → ℝ) (C : ℝ), Measurable h ∧ (∀ u, 1 ≤ h u) ∧ (∀ u, h u ≤ C) ∧
      ∀ u ∈ Set.Icc (-A) 0,
        ∑ n ∈ Finset.Icc 2 4,
          (thirdStageCoefficients (thirdStageAlpha 1) (thirdStageBeta 1) (thirdStageChi 1) n / 2) *
            (windowGate A h (u + Real.log n) + windowGate A h (u - Real.log n)) ≤ h u := by
  rintro ⟨h, C, hm, h1, hC, hbal⟩
  obtain ⟨H, hH, hbad⟩ := exists_thirdStage_absolute_cost_exceeds_norm hA
  have hh := sum_two_mul_abs_autocorr_le hH hm h1 hC (Finset.Icc 2 4)
    (fun n => div_nonneg (thirdStageCoefficients_one_nonneg n) (by norm_num)) hbal
  norm_num only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at hh
  exact (not_lt_of_ge hh) hbad

#print axioms tateFunction_one_nonneg_beforeNineHalves
#print axioms thirdStage_all_negative_edges_witness
#print axioms exists_thirdStage_absolute_cost_exceeds_norm
#print axioms no_thirdStage_absolute_cost_balancing_weight

end GaloisForLFunctions.WindowTowerOfSpecZ

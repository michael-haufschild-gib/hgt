import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EndpointDecayRemovesTheCrossKernelGapLoss
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilEnergyControlsThePrimeDefect

/-!
# One cross-error budget through touching

Distinct integer logarithms up to `N` are separated by more than `1/N`.
Endpoint decay therefore controls the actual archimedean cross replacement
uniformly at every ratio `0<c<=1`. The common constant controls the whole
quadratic form and the residual on every bounded pole profile.
-/

noncomputable section

open MeasureTheory Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory HTGeometry

private theorem inv_horizon_lt_log_difference {n j N : ℕ}
    (hn : n ∈ Icc 1 N) (hj : j ∈ Icc 1 N) (hnj : n < j) :
    1 / (N : ℝ) < Real.log j - Real.log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
  have hjN : (j : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hj).2
  have hstep : (n : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt hnj
  have hratio : (n : ℝ) / j < 1 := (div_lt_one hj0).mpr (by exact_mod_cast hnj)
  have hlog := Real.log_lt_sub_one_of_pos (div_pos hn0 hj0) (ne_of_lt hratio)
  rw [Real.log_div hn0.ne' hj0.ne'] at hlog
  have heq : ((j : ℝ) - n) / j = 1 - (n : ℝ) / j := by field_simp
  calc
    1 / (N : ℝ) ≤ 1 / (j : ℝ) := one_div_le_one_div_of_le hj0 hjN
    _ ≤ ((j : ℝ) - n) / j := div_le_div_of_nonneg_right (by linarith only [hstep]) hj0.le
    _ < Real.log j - Real.log n := by rw [heq]; linarith only [hlog]

/-- The endpoint ratio still leaves every actual pair of atom supports separated. -/
theorem inv_horizon_lt_integer_log_gap {n j N : ℕ}
    (hn : n ∈ Icc 1 N) (hj : j ∈ Icc 1 N) (hnj : n ≠ j) :
    1 / (N : ℝ) < |Real.log j - Real.log n| := by
  rcases lt_or_gt_of_ne hnj with hlt | hlt
  · exact (inv_horizon_lt_log_difference hn hj hlt).trans_le (le_abs_self _)
  · have h := (inv_horizon_lt_log_difference hj hn hlt).trans_le (le_abs_self _)
    simpa only [abs_sub_comm] using h

/-- Endpoint vanishing gives one entry constant for every ratio up to one. -/
theorem exists_uniform_atomCrossError_entry_at_touching {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ N : ℕ,
      ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N,
        |atomCrossErrorKernel (atomDilate φ (c / N)) n j| ≤
          (C * (c / (N : ℝ)) ^ 2) * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_profile_crossError_uniform hφ hsupp hM
  refine ⟨C, hC, fun c hc0 hc1 N n hn j hj => ?_⟩
  by_cases hnj : n = j
  · subst j
    simp only [atomCrossErrorKernel_self, abs_zero, sub_self, abs_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), div_zero, le_refl]
  have hn0 : 0 < n := (mem_Icc.mp hn).1
  have hj0 : 0 < j := (mem_Icc.mp hj).1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hn0.trans_le (mem_Icc.mp hn).2
  let w : ℝ := c / N
  let s : ℝ := |Real.log j - Real.log n|
  have hw : 0 < w := div_pos hc0 hN0
  have hws : w < s :=
    (div_le_div_of_nonneg_right hc1 hN0.le).trans_lt (inv_horizon_lt_integer_log_gap hn hj hnj)
  have hG : 0 < ∫ u, atomDilate φ w u ^ 2 := by
    rw [integral_atomDilate_sq hw]
    exact mul_pos hw hM
  have hinv : 1 / s ^ 2 ≤ (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2 := by
    have h := inv_sq_integer_log_gap_sub_window_le (c := 0) (w := 0) hn hj hnj
      (by norm_num) (by norm_num) (by simp)
    simpa only [s, sub_zero, one_pow, one_mul, abs_sub_comm] using h
  change |atomCrossErrorKernel (atomDilate φ w) n j| ≤ _
  rw [atomCrossErrorKernel, if_neg hnj, archimedeanCenterKernel,
    if_neg (by simp only [hnj, hn0.ne', hj0.ne', or_self, not_false_eq_true])]
  have heq : atomCrossTerm (atomDilate φ w) s / (∫ u, atomDilate φ w u ^ 2) -
      ((∫ u, atomDilate φ w u) ^ 2 / (∫ u, atomDilate φ w u ^ 2)) *
        _root_.RHTower.archLevyDensity s =
      (atomCrossTerm (atomDilate φ w) s -
        _root_.RHTower.archLevyDensity s * (∫ u, atomDilate φ w u) ^ 2) /
          (∫ u, atomDilate φ w u ^ 2) := by ring
  rw [heq, abs_div, abs_of_pos hG]
  calc
    _ ≤ C * w ^ 2 / s ^ 2 := hbound w s hw hws
    _ = (C * w ^ 2) * (1 / s ^ 2) := by ring
    _ ≤ (C * w ^ 2) * ((max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = _ := by ring

/-- The actual cross-error form has one budget, uniform in the horizon and up to touching. -/
theorem exists_uniform_crossError_quadratic_at_touching {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ N : ℕ, 1 ≤ N → ∀ x : ℕ → ℝ,
      |∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        x n * x j * atomCrossErrorKernel (atomDilate φ (c / N)) n j| ≤
          (4 * C * c ^ 2) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_atomCrossError_entry_at_touching hφ hsupp hM
  refine ⟨C, hC, fun c hc0 hc1 N hN x => ?_⟩
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have h := abs_kernel_quadratic_le_of_integer_distance
    (mul_nonneg hC.le (sq_nonneg (c / (N : ℝ)))) (hb c hc0 hc1 N)
    (fun n _ j _ => atomCrossErrorKernel_comm _ n j) x
  convert h using 1
  field_simp [hN0]

/-- Every bounded pole profile has a uniform square-residual budget up to touching. -/
theorem exists_uniform_crossError_poleResidual_at_touching {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ N : ℕ, 1 ≤ N →
      ∀ (a : ℕ → ℝ) (A : ℝ), 0 ≤ A → (∀ j ∈ Icc 1 N, |a j| ≤ A) →
        (∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N,
          atomCrossErrorKernel (atomDilate φ (c / N)) n j * (a j / Real.sqrt j)) ^ 2) ≤
            (36 * C * A * c ^ 2) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_atomCrossError_entry_at_touching hφ hsupp hM
  refine ⟨C, hC, fun c hc0 hc1 N hN a A hA ha => ?_⟩
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have h := sum_sq_kernel_poleProfile_le (mul_nonneg hC.le (sq_nonneg (c / (N : ℝ))))
    (hb c hc0 hc1 N) hA ha
  convert h using 1
  field_simp [hN0]

/-- The whole literal cross-error matrix retains this budget at the endpoint ratio. -/
theorem exists_uniform_fullWeilCrossError_at_touching {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ N : ℕ, 1 ≤ N →
      ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        |⟪Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c N) x, x⟫| ≤
          (4 * C * c ^ 2) * ‖x‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_crossError_quadratic_at_touching hφ hsupp hM
  refine ⟨C, hC, fun c hc0 hc1 N hN x => ?_⟩
  change |⟪Matrix.toEuclideanLin
    (horizonKernelMatrix (atomCrossErrorKernel (atomDilate φ (c / N))) N) x, x⟫| ≤ _
  rw [horizonKernelMatrix_inner, ← sum_primeHorizonExtension_sq]
  exact hb c hc0 hc1 N hN _

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_uniform_fullWeilCrossError_at_touching
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_uniform_crossError_poleResidual_at_touching

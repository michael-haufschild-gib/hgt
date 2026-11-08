import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TopWindowConductorRowCancellation
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.LogarithmicAnnuliHaveUniformRowMeans

/-!
# The polar near row reduces to a smooth annular mean and one harmonic collar

The two logarithmic Gram terms are retained exactly. All remaining local errors
are of second order in the atomic width.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped BigOperators
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis

/-- The near polar Gamma row is its smooth kernel sum minus the exact logarithmic Gram row,
with an error of order `w²√n`. -/
theorem abs_nearGammaDownwardRow_one_sub_smooth_le
    {c : ℝ} {N n : ℕ} (hc : 0 < c) (hN : 1 ≤ N) (hw3 : c / N ≤ 1 / 3)
    (hn : n ∈ Icc 1 N) :
    |nearGammaDownwardRow tiltedUnitSpline c N 1 n -
        ((∑ j ∈ nearRowIndices c N n,
          (nearKernel tiltedUnitSpline (|Real.log j - Real.log n| / (c / N)) /
            (∫ u, tiltedUnitSpline u ^ 2)) / Real.sqrt j) -
          (Real.log c + Real.log ((n : ℝ) / N)) * nearPoleRow tiltedUnitSpline c N n)| ≤
      20 * Real.exp 3 * c ^ 2 * Real.sqrt n / N ^ 2 := by
  have hφ := contDiff_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_eq_zero
  have hM := integral_tiltedUnitSpline_sq_pos
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hw0 : 0 < c / N := div_pos hc hN0
  have hw1 : c / N ≤ 1 := hw3.trans (by norm_num)
  obtain ⟨hcard, hpoint⟩ := nearRowIndices_card_and_pointwise_local hφ hsupp hM hc hN0 hw1 hn
  let A : ℕ → ℝ := fun j => shellAutocorr tiltedUnitSpline
    (|Real.log j - Real.log n| / (c / N)) / (∫ u, tiltedUnitSpline u ^ 2)
  let K : ℕ → ℝ := fun j => nearKernel tiltedUnitSpline
    (|Real.log j - Real.log n| / (c / N)) / (∫ u, tiltedUnitSpline u ^ 2)
  have hrow : nearGammaDownwardRow tiltedUnitSpline c N 1 n -
        ((∑ j ∈ nearRowIndices c N n, K j / Real.sqrt j) -
          (Real.log c + Real.log ((n : ℝ) / N)) * nearPoleRow tiltedUnitSpline c N n) =
      ∑ j ∈ nearRowIndices c N n,
        (nearArchimedeanRemainder tiltedUnitSpline (c / N) n j - K j +
          (Real.log n - Real.log j) * A j) / Real.sqrt j := by
    unfold nearGammaDownwardRow nearPoleRow nearGram
    rw [mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun j hj => ?_
    have hj1 := (mem_Icc.mp (mem_filter.mp hj).1).1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    rw [nearGammaDownwardCoefficient_one_eq hc hN hj1 n,
      Real.log_div hn0.ne' hN0.ne', Real.log_div hj0.ne' hN0.ne']
    dsimp only [A, K]
    ring
  rw [hrow]
  have hterm : ∀ j ∈ nearRowIndices c N n,
      |(nearArchimedeanRemainder tiltedUnitSpline (c / N) n j - K j +
          (Real.log n - Real.log j) * A j) / Real.sqrt j| ≤
        5 * (c / N) * Real.exp 1 / Real.sqrt n := by
    intro j hj
    have hgap : |Real.log j - Real.log n| ≤ 2 * (c / N) := by
      simpa only [mul_div_assoc] using (mem_filter.mp hj).2.2
    have hrem := abs_nearArchimedeanRemainder_sub_le hφ hsupp hM hw0 hw3 hgap
    obtain ⟨hsj, hAj⟩ := hpoint j hj
    have hlog : |(Real.log n - Real.log j) * A j| ≤ 2 * (c / N) := by
      rw [abs_mul, abs_sub_comm (Real.log n)]
      exact (mul_le_mul hgap hAj (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
    have hb : |nearArchimedeanRemainder tiltedUnitSpline (c / N) n j - K j +
        (Real.log n - Real.log j) * A j| ≤ 5 * (c / N) := by
      have hh := (abs_add_le _ _).trans (add_le_add hrem hlog)
      exact hh.trans_eq (by ring)
    rw [div_eq_mul_one_div, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt (j : ℝ))]
    exact (mul_le_mul hb hsj (by positivity) (by positivity)).trans_eq (by ring)
  calc
    _ ≤ ((nearRowIndices c N n).card : ℝ) * (5 * (c / N) * Real.exp 1 / Real.sqrt n) := by
      rw [← nsmul_eq_mul, ← sum_const]
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
    _ ≤ (2 * (n : ℝ) * (linearNearRowRadius c / N)) *
        (5 * (c / N) * Real.exp 1 / Real.sqrt n) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by
      have he : Real.exp 2 * Real.exp 1 = Real.exp 3 := by rw [← Real.exp_add]; norm_num
      unfold linearNearRowRadius
      field_simp [hsn.ne', hN0.ne']
      rw [Real.sq_sqrt hn0.le, ← he]
      ring

/-- The logarithmic Gram term cancels the corresponding harmonic collar logarithm exactly. -/
theorem polar_nearGram_center_decomposition (φ : ℝ → ℝ) (c : ℝ) (N n : ℕ) :
    -(Real.log c + Real.log ((n : ℝ) / N)) * nearPoleRow φ c N n +
        (completeWeilPoleShift φ c / N) *
          (∑ j ∈ nearRowIndices c N n, archimedeanCenterKernel n j / Real.sqrt j) =
      -(Real.log c + Real.log ((n : ℝ) / N)) * poleRowDefect φ c N n -
        (Real.log c + Real.log ((n : ℝ) / N)) * atomPoleErrorCoefficient φ c N * Real.sqrt n +
        (completeWeilPoleShift φ c / N) *
          ((∑ j ∈ nearRowIndices c N n, archimedeanCenterKernel n j / Real.sqrt j) -
            (Real.log c + Real.log ((n : ℝ) / N)) * Real.sqrt n) := by
  have he : nearPoleRow φ c N n = poleRowDefect φ c N n +
      (atomPoleErrorCoefficient φ c N + completeWeilPoleShift φ c / N) * Real.sqrt n := by
    unfold poleRowDefect
    rw [exactPoleCoefficient_eq]
    ring
  rw [he]
  ring

#print axioms abs_nearGammaDownwardRow_one_sub_smooth_le
#print axioms polar_nearGram_center_decomposition
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

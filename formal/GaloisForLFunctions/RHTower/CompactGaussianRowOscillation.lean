import GaloisForLFunctions.RHTower.CompactGaussianSlowRowVariation
import GaloisForLFunctions.RHTower.ZetaChiIntegerGradeAmplitude

open Complex Set Filter Topology MeasureTheory
noncomputable section
namespace RHTower

/-- The literal full complex reflected row, uniformly over a right-strip disc,
has physical square-root oscillatory cancellation at every Dirichlet frequency. -/
theorem exists_compactGaussianRow_disc_oscillation
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ s ∈ Metric.closedBall c r, ∀ ω : ℝ,
      ‖∫ tau in (N : ℝ)..(2 * N), reflectedCompactGaussianRow s N tau *
        Complex.exp (((ω * tau : ℝ) : ℂ) * I)‖ ≤
          C / Real.sqrt (1 / (100 * (N : ℝ))) := by
  obtain ⟨C, hC, hvar⟩ := exists_compactGaussianSlowRow_disc_variation c hr hc0 hc1
  refine ⟨6 * C, by positivity, ?_⟩
  filter_upwards [hvar, eventually_ge_atTop (4 : ℕ)] with N hN hN4
  have hNR4 : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hNR : (0 : ℝ) < N := by linarith
  have hab : (N : ℝ) ≤ 2 * N := by linarith
  intro s hs ω
  have hre : |s.re - c.re| ≤ r := (by
    simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s - c) :
      |s.re - c.re| ≤ dist s c).trans hs
  have hs0 : 0 < s.re := by linarith [(abs_le.mp hre).1]
  have hs1 : s.re < 1 := by linarith [(abs_le.mp hre).2]
  obtain ⟨hi, hvariation⟩ := hN s hs
  have hu : ∀ x ∈ uIcc (N : ℝ) (2 * N),
      HasDerivAt (compactGaussianSlowRow s N) (deriv (compactGaussianSlowRow s N) x) x :=
    fun x _ => (hasDerivAt_compactGaussianSlowRow hs0 hs1 N x).differentiableAt.hasDerivAt
  have h := norm_integral_complexAmplitude_mul_zetaChi_line_zpow_mul_exp_le
    (T := (N : ℝ)) hNR4 (le_refl _) hab (le_refl _) (k := (1 : ℤ)) (by norm_num) ω hu hi
  have heq (tau : ℝ) : compactGaussianSlowRow s N tau *
      (zetaChi (linePt tau) ^ (1 : ℤ) * Complex.exp (((ω * tau : ℝ) : ℂ) * I)) =
      reflectedCompactGaussianRow s N tau * Complex.exp (((ω * tau : ℝ) : ℂ) * I) := by
    rw [zpow_one, ← mul_assoc, compactGaussianSlowRow,
      div_mul_cancel₀ _ (zetaChi_line_ne_zero tau)]
  rw [intervalIntegral.integral_congr (fun tau _ => heq tau)] at h
  norm_num only [Int.cast_one, abs_one] at h
  calc
    _ ≤ (6 / Real.sqrt (1 / (100 * (N : ℝ)))) *
        (‖compactGaussianSlowRow s N (2 * N)‖ +
          ∫ tau in (N : ℝ)..(2 * N), ‖deriv (compactGaussianSlowRow s N) tau‖) := h
    _ ≤ (6 / Real.sqrt (1 / (100 * (N : ℝ)))) * C :=
      mul_le_mul_of_nonneg_left hvariation (by positivity)
    _ = _ := by ring

end RHTower

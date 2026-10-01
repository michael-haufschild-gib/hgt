import GaloisForLFunctions.RHTower.ZetaChiAmplitudeStationary
import GaloisForLFunctions.RHTower.CompactGaussianSlowRowVariation

open Complex Set Filter Topology MeasureTheory
noncomputable section
namespace RHTower

/-- The literal full reflected row has a stationary main value uniformly
on a right-strip disc. Its slow amplitude is evaluated at each actual saddle. -/
theorem exists_compactGaussianRow_disc_stationary
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ s ∈ Metric.closedBall c r,
      ∀ a h : ℝ, 8 ≤ a → 0 < h → h ≤ a / 2 → a / 2 ≤ (N : ℝ) →
      (N : ℝ) ≤ a - h → a + h ≤ 2 * N → 2 * (N : ℝ) ≤ 2 * a →
      ‖(∫ tau in (N : ℝ)..(2 * N), reflectedCompactGaussianRow s N tau *
          bourgainOscillation (tau * Real.log (a / (2 * Real.pi)))) -
        compactGaussianSlowRow s N a *
          ((Real.sqrt (2 * Real.pi * a) : ℂ) * bourgainOscillation a)‖ ≤
        C * (78 + 2 * h ^ 2 / N + 40 * a ^ 2 / ((N : ℝ) * h) +
          4 * h ^ 4 / a ^ 2 + 40 * a / h) := by
  obtain ⟨C, hC, hbound⟩ := exists_compactGaussianSlowRow_disc_bounds c hr hc0 hc1
  obtain ⟨_, _, hvar⟩ := exists_compactGaussianSlowRow_disc_variation c hr hc0 hc1
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, hvar, eventually_ge_atTop (1 : ℕ)] with N hN hvarN hN1
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  intro s hs a h ha hh hha hl hlh hhu hu
  have hre : |s.re - c.re| ≤ r := (by
    simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s - c) :
      |s.re - c.re| ≤ dist s c).trans hs
  have hs0 : 0 < s.re := by linarith [(abs_le.mp hre).1]
  have hs1 : s.re < 1 := by linarith [(abs_le.mp hre).2]
  have hv : ∀ t ∈ Icc (N : ℝ) (2 * N),
      HasDerivAt (compactGaussianSlowRow s N) (deriv (compactGaussianSlowRow s N) t) t :=
    fun t _ => (hasDerivAt_compactGaussianSlowRow hs0 hs1 N t).differentiableAt.hasDerivAt
  have hb := norm_integral_zetaChi_complexAmplitude_stationary_le 1 (by decide)
    ha hh hha hl hlh hhu hu (by positivity : 0 ≤ C / (N : ℝ)) hv (hvarN s hs).1
    (fun t ht => (hN t ht s hs).2) (fun t ht => (hN t ht s hs).1)
  norm_num only [Nat.cast_one, pow_one, one_mul, inv_one, sub_self, zero_mul, add_zero] at hb
  have he (t : ℝ) : compactGaussianSlowRow s N t *
      (zetaChi (linePt t) * bourgainOscillation (t * Real.log (a / (2 * Real.pi)))) =
      reflectedCompactGaussianRow s N t * bourgainOscillation (t * Real.log (a / (2 * Real.pi))) := by
    rw [← mul_assoc, compactGaussianSlowRow, div_mul_cancel₀ _ (zetaChi_line_ne_zero t)]
  rw [intervalIntegral.integral_congr (fun t _ => he t)] at hb
  have hva : ‖compactGaussianSlowRow s N a‖ ≤ C :=
    (hN a ⟨by linarith, by linarith⟩ s hs).1
  calc
    _ ≤ 78 * C + 2 * (C / (N : ℝ)) * h ^ 2 + 40 * (C / (N : ℝ)) * a ^ 2 / h +
        ‖compactGaussianSlowRow s N a‖ * (4 * h ^ 4 / a ^ 2 + 40 * a / h) := hb
    _ ≤ 78 * C + 2 * (C / (N : ℝ)) * h ^ 2 + 40 * (C / (N : ℝ)) * a ^ 2 / h +
        C * (4 * h ^ 4 / a ^ 2 + 40 * a / h) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hva (by positivity))
    _ = _ := by ring

end RHTower

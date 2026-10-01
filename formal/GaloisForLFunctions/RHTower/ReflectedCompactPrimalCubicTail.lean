import GaloisForLFunctions.RHTower.CompactGaussianNormalizedCubicTail
import GaloisForLFunctions.RHTower.CompactGaussianReflectedRowBounds
import GaloisForLFunctions.RHTower.SmoothAFEFullReflectedCubicTail

open Complex Filter Topology Set Metric
noncomputable section
namespace RHTower

/-- The exact row norm converts normalized Gaussian error back to the original
reflected carrier, including the physical height in its spectral argument. -/
theorem norm_chi_mul_eq_row_mul_normalized (s w : ℂ) {N : ℝ}
    (hN : 0 < N) (tau : ℝ) :
    ‖zetaChi (s + (tau : ℂ) * I) * w‖ =
      ‖reflectedCompactGaussianRow s N tau‖ *
        ‖(N : ℂ) ^ ((1 / 2 : ℂ) - (s + (tau : ℂ) * I)) * w‖ := by
  have hre : ((1 / 2 : ℂ) - (s + (tau : ℂ) * I)).re = 1 / 2 - s.re := by simp
  have hpow : N ^ (s.re - 1 / 2) * N ^ (1 / 2 - s.re) = 1 := by
    rw [← Real.rpow_add hN, show s.re - 1 / 2 + (1 / 2 - s.re) = 0 by ring, Real.rpow_zero]
  rw [norm_mul, norm_reflectedCompactGaussianRow s hN tau, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hN, hre]
  calc
    _ = ‖zetaChi (s + (tau : ℂ) * I)‖ *
        (N ^ (s.re - 1 / 2) * N ^ (1 / 2 - s.re)) * ‖w‖ := by rw [hpow, mul_one]
    _ = _ := by ring

/-- The original full reflected primal has an arbitrary-power deterministic
cubic tail on the entire compact disc, uniformly in every phase and physical
height throughout each large square-conductor window. -/
theorem exists_fullReflectedPrimal_compact_cubic_tail_le
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 < c.re - r) (hc1 : c.re + r < 1)
    {q : ℝ} (hq : 0 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ tau ∈ Icc ((n ^ 2 : ℕ) : ℝ) (2 * (n ^ 2 : ℕ)), ∀ s ∈ closedBall c r,
        ∀ ω : SteinhausModel.Omega,
          ‖steinhausFullReflectedPrimalCarrier (s.re - 1 / 2) (s.im + tau) (n ^ 2) ω -
            ∑ m ∈ Finset.Icc 1 (n ^ 3),
              smoothAFEZetaRightReflectedPrimalPositiveCoefficient
                (s.re - 1 / 2) (s.im + tau) 1 (n ^ 2) m * SteinhausModel.X m ω‖ ≤
                  C * (n : ℝ) ^ (-q) := by
  obtain ⟨K, hK, htail⟩ := exists_normalizedFullGaussian_cubic_tail_le
    (b := c.re + r) (by linarith) hq
  obtain ⟨D, hD, hrow⟩ := exists_reflectedCompactGaussianRow_disc_bounds c hr hc0.le hc1
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hrow
  refine ⟨D * K, mul_nonneg hD.le hK, ?_⟩
  filter_upwards [eventually_ge_atTop (max N₀ 1)] with n hn
  have hn1 : 1 ≤ n := (le_max_right N₀ 1).trans hn
  have hnpos : 0 < n := hn1
  have hnn : n ≤ n ^ 2 := by nlinarith
  have hN0 : N₀ ≤ n ^ 2 := ((le_max_left N₀ 1).trans hn).trans hnn
  have hNR : (0 : ℝ) < ((n ^ 2 : ℕ) : ℝ) := by positivity
  intro tau htau s hs ω
  have hre0 : |s.re - c.re| ≤ dist s c := by
    simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s - c)
  have hre : s.re ≤ c.re + r := by linarith [(abs_le.mp (hre0.trans hs)).2]
  have hz : rightDisplacedLinePt (s.re - 1 / 2) (s.im + tau) = s + (tau : ℂ) * I := by
    apply Complex.ext <;> simp [rightDisplacedLinePt]
  have ht := htail n hnpos (s + (tau : ℂ) * I) (by simpa using hre) ω
  have hd := (hN₀ (n ^ 2) hN0 tau htau s hs).1
  rw [reflectedPrimalWindowCarrier_eq_chi_mul_truncated, steinhausFullReflectedPrimalCarrier,
    ← mul_sub, hz, norm_chi_mul_eq_row_mul_normalized _ _ hNR tau]
  calc
    _ ≤ D * (K * (n : ℝ) ^ (-q)) := mul_le_mul hd ht (norm_nonneg _) hD.le
    _ = _ := by ring

end RHTower

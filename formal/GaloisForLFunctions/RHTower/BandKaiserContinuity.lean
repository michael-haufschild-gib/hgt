import GaloisForLFunctions.RHTower.BandKaiserTail
import GaloisForLFunctions.RHTower.BandFormBridge
import GaloisForLFunctions.RHTower.BandLeakageSpectralTail

/-!
# Continuity of the Kaiser–Bessel trial, and its spectral density

The trial weight is the entire series `sum_k u^k/(k!)²` evaluated at `u = c²(1-x²)/4`.  On every ball
the series is dominated by `sum_k R^k/(k!)²`, so it converges uniformly there and the sum is
continuous; continuity at every point follows, and the trial is continuous as a composition.

With continuity in hand the trial is a legitimate test function for the variational bound, and its
spectral density is the square of its cosine transform: by the even-test bridge and the Fourier
normalisation, `‖𝓕 (trunc K_c) xi‖² = (∫ K_c(x) cos(2 pi xi x) dx)²`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set intervalIntegral FourierTransform

open _root_.RHTower

/-- The entire series behind the trial weight. -/
def kaiserSeries (u : ℝ) : ℝ := ∑' k : ℕ, u ^ k / (Nat.factorial k : ℝ) ^ (2 : ℕ)

theorem kaiserTrial_eq_kaiserSeries (c x : ℝ) :
    kaiserTrial c x = kaiserSeries (c ^ (2 : ℕ) * (1 - x ^ (2 : ℕ)) / 4) := rfl

/-- The trial series is continuous on every closed ball, by uniform domination. -/
theorem continuousOn_kaiserSeries (R : ℝ) :
    ContinuousOn kaiserSeries (Metric.closedBall (0 : ℝ) R) := by
  refine continuousOn_tsum (u := fun k : ℕ => R ^ k / (Nat.factorial k : ℝ) ^ (2 : ℕ))
    (fun k => by fun_prop) (summable_kaiserTerm R) ?_
  intro k u hu
  have hu' : |u| ≤ R := by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hu
    exact hu
  have hR : 0 ≤ R := le_trans (abs_nonneg u) hu'
  have hkpos : (0 : ℝ) < (Nat.factorial k : ℝ) ^ (2 : ℕ) := by
    have : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
    positivity
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hkpos]
  gcongr

/-- The trial series is continuous. -/
theorem continuous_kaiserSeries : Continuous kaiserSeries := by
  rw [continuous_iff_continuousAt]
  intro u
  have hmem : u ∈ Metric.ball (0 : ℝ) (|u| + 1) := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    linarith [le_abs_self u, abs_nonneg u]
  have hsub : Metric.ball (0 : ℝ) (|u| + 1) ⊆ Metric.closedBall (0 : ℝ) (|u| + 1) :=
    Metric.ball_subset_closedBall
  have hcont := (continuousOn_kaiserSeries (|u| + 1)).mono hsub
  exact hcont.continuousAt (Metric.isOpen_ball.mem_nhds hmem)

/-- **The trial weight is continuous.** -/
theorem continuous_kaiserTrial (c : ℝ) : Continuous (kaiserTrial c) := by
  have hinner : Continuous fun x : ℝ => c ^ (2 : ℕ) * (1 - x ^ (2 : ℕ)) / 4 := by fun_prop
  exact continuous_kaiserSeries.comp hinner

/-! ## The spectral density of an even test function -/

/-- **The spectral density is the square of the cosine transform.** -/
theorem norm_sq_fourier_bandTrunc_of_even {Φ : ℝ → ℝ} (hΦ : Continuous Φ)
    (heven : ∀ x, Φ (-x) = Φ x) (ξ : ℝ) :
    ‖𝓕 (bandTrunc Φ) ξ‖ ^ (2 : ℕ)
      = (∫ x in (-1 : ℝ)..1, Φ x * Real.cos (2 * Real.pi * ξ * x)) ^ (2 : ℕ) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hfreq : -(-(2 * Real.pi * ξ) / (2 * Real.pi)) = ξ := by
    field_simp
  have hband : 𝓕 (bandTrunc Φ) ξ = bandFourier (-(2 * Real.pi * ξ)) Φ := by
    rw [bandFourier_eq_fourier (-(2 * Real.pi * ξ)) Φ, hfreq]
  rw [hband, bandFourier_of_even hΦ heven]
  have hcos : ∀ x : ℝ, Real.cos (-(2 * Real.pi * ξ) * x) = Real.cos (2 * Real.pi * ξ * x) := by
    intro x
    rw [show -(2 * Real.pi * ξ) * x = -(2 * Real.pi * ξ * x) by ring, Real.cos_neg]
  rw [intervalIntegral.integral_congr (g := fun x => Φ x * Real.cos (2 * Real.pi * ξ * x))
    fun x _ => by rw [hcos x]]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **The spectral density of the trial beyond the band edge.**  The Cauchy envelope of the tail, in
the Fourier variable. -/
theorem norm_sq_fourier_bandTrunc_kaiser_le {c ξ : ℝ} (hc : 0 ≤ c)
    (h : c < |2 * Real.pi * ξ|) :
    ‖𝓕 (bandTrunc (kaiserTrial c)) ξ‖ ^ (2 : ℕ) ≤ 8 / (1 + (|2 * Real.pi * ξ| - c) ^ (2 : ℕ)) := by
  have hsq : c ^ (2 : ℕ) < (2 * Real.pi * ξ) ^ (2 : ℕ) := by
    have habs : |2 * Real.pi * ξ| ^ (2 : ℕ) = (2 * Real.pi * ξ) ^ (2 : ℕ) := sq_abs _
    nlinarith [abs_nonneg (2 * Real.pi * ξ), hc]
  rw [norm_sq_fourier_bandTrunc_of_even (continuous_kaiserTrial c) (kaiserTrial_even c) ξ]
  have hbound := sq_integral_kaiserTrial_cos_le (c := c) (ω := 2 * Real.pi * ξ) hc hsq
  have hcongr : (∫ x in (-1 : ℝ)..1, kaiserTrial c x * Real.cos (2 * Real.pi * ξ * x))
      = ∫ x in (-1 : ℝ)..1, kaiserTrial c x * Real.cos ((2 * Real.pi * ξ) * x) := rfl
  rw [hcongr]
  exact hbound

end GaloisForLFunctions.RHTower

end

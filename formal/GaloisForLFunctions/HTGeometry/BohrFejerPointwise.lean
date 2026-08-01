import GaloisForLFunctions.HTGeometry.BohrLatticeAlmostPeriod
import GaloisForLFunctions.HTGeometry.CosineLatticeDistance
import GaloisForLFunctions.HTGeometry.BohrFejerConcentration

/-!
# The pointwise Fejér estimate

At every point the kernel times the increment of the function is bounded by the kernel times a small
constant plus a term that vanishes with the kernel bound: near a peak the increment is small, because
the peak is a dual-lattice point and hence an almost period, and away from the peaks the kernel is
small.  No cutoff function appears, so the estimate survives taking Bohr means.
-/

open Filter Topology

open scoped BoundedContinuousFunction Real

namespace GaloisForLFunctions

open _root_.HTGeometry

variable {f : ℝ →ᵇ ℂ}

/-- **The pointwise Fejér estimate.** -/
theorem fejer_pointwise_bound {β : ℝ} (hβ : β ≠ 0)
    (hf : UniformContinuous fun x => f x) (htb : HasTotallyBoundedOrbit fun x => f x)
    (hfreq : ∀ μ : ℝ, IsBohrHullFrequency f μ → ∃ k : ℤ, μ = k * β)
    {ε ρ ω : ℝ} (hε : 0 < ε) (hρ : 0 < ρ)
    (hmod : ∀ x y : ℝ, |x - y| ≤ ρ → ‖f x - f y‖ ≤ ω)
    {c : ℝ} (hc : 0 < c) (hcρ : Real.pi * Real.sqrt (c / 2) ≤ |β| * ρ)
    (N : ℕ) (t u : ℝ) :
    (‖fejerSum β N u‖ ^ 2 / ((N : ℝ) + 1)) * ‖f (t + u) - f t‖
      ≤ (‖fejerSum β N u‖ ^ 2 / ((N : ℝ) + 1)) * (2 * ε + ω)
        + 2 * ‖f‖ * (2 / (((N : ℝ) + 1) * c)) := by
  have hKnn : 0 ≤ ‖fejerSum β N u‖ ^ 2 / ((N : ℝ) + 1) := fejerKernel_nonneg β N u
  have hfnorm : ∀ x : ℝ, ‖f x‖ ≤ ‖f‖ := fun x => f.norm_coe_le_norm x
  have hboundnn : 0 ≤ 2 * ‖f‖ * (2 / (((N : ℝ) + 1) * c)) := by
    have h1 : (0 : ℝ) ≤ ‖f‖ := norm_nonneg f
    have h2 : (0 : ℝ) ≤ 2 / (((N : ℝ) + 1) * c) := by positivity
    positivity
  by_cases hcos : Real.cos (β * u) ≤ 1 - c
  · -- away from the peaks: the kernel is small
    have hK : ‖fejerSum β N u‖ ^ 2 / ((N : ℝ) + 1) ≤ 2 / (((N : ℝ) + 1) * c) :=
      fejerKernel_norm_le_of_cos_le β N hc hcos
    have hincr : ‖f (t + u) - f t‖ ≤ 2 * ‖f‖ := by
      calc ‖f (t + u) - f t‖ ≤ ‖f (t + u)‖ + ‖f t‖ := norm_sub_le _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add (hfnorm _) (hfnorm _)
        _ = 2 * ‖f‖ := by ring
    have hprod : (‖fejerSum β N u‖ ^ 2 / ((N : ℝ) + 1)) * ‖f (t + u) - f t‖
        ≤ (2 / (((N : ℝ) + 1) * c)) * (2 * ‖f‖) := by
      refine mul_le_mul hK hincr (norm_nonneg _) (by positivity)
    have hrest : (0 : ℝ) ≤ (‖fejerSum β N u‖ ^ 2 / ((N : ℝ) + 1)) * (2 * ε + ω) := by
      have hω : 0 ≤ 2 * ε + ω := by
        have h0 := hmod 0 0 (by simpa using hρ.le)
        have : ‖f 0 - f 0‖ = 0 := by simp
        rw [this] at h0
        linarith
      positivity
    nlinarith [hprod, hrest]
  · -- near a peak: the increment is small
    push Not at hcos
    have hcosle : 1 - Real.cos (β * u) ≤ c := by linarith
    obtain ⟨m, hm⟩ := exists_int_abs_sub_two_pi_mul_le hc.le hcosle
    have hβabs : 0 < |β| := abs_pos.mpr hβ
    have hdist : |u - m * (2 * Real.pi / β)| ≤ ρ := by
      have hfac : β * u - 2 * Real.pi * m = β * (u - m * (2 * Real.pi / β)) := by
        field_simp
      rw [hfac, abs_mul] at hm
      have hle : |β| * |u - m * (2 * Real.pi / β)| ≤ |β| * ρ := le_trans hm hcρ
      exact le_of_mul_le_mul_left hle hβabs
    have hstep1 : ‖f (t + u) - f (t + m * (2 * Real.pi / β))‖ ≤ ω := by
      refine hmod _ _ ?_
      have : (t + u) - (t + m * (2 * Real.pi / β)) = u - m * (2 * Real.pi / β) := by ring
      rw [this]
      exact hdist
    have hstep2 : ‖f (t + m * (2 * Real.pi / β)) - f t‖ ≤ 2 * ε :=
      norm_translate_sub_le_of_freq_lattice hβ hf htb hfreq hε m t
    have hincr : ‖f (t + u) - f t‖ ≤ 2 * ε + ω := by
      calc ‖f (t + u) - f t‖
          ≤ ‖f (t + u) - f (t + m * (2 * Real.pi / β))‖
            + ‖f (t + m * (2 * Real.pi / β)) - f t‖ := by
            have hsplit : f (t + u) - f t
                = (f (t + u) - f (t + m * (2 * Real.pi / β)))
                  + (f (t + m * (2 * Real.pi / β)) - f t) := by ring
            rw [hsplit]
            exact norm_add_le _ _
        _ ≤ ω + 2 * ε := add_le_add hstep1 hstep2
        _ = 2 * ε + ω := by ring
    have hprod : (‖fejerSum β N u‖ ^ 2 / ((N : ℝ) + 1)) * ‖f (t + u) - f t‖
        ≤ (‖fejerSum β N u‖ ^ 2 / ((N : ℝ) + 1)) * (2 * ε + ω) :=
      mul_le_mul_of_nonneg_left hincr hKnn
    linarith [hprod, hboundnn]

end GaloisForLFunctions

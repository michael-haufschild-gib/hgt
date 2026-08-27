import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureSourceRetentionWall
import GaloisForLFunctions.RHTower.GammaSewnSynchronizedRecoveryContraction

/-!
# Adaptive physical apertures censor fixed divisor modes

A positive fixed-width physical log window censors no exponential mode in the open left
half-plane. That pointwise fact is not uniform as the aperture shrinks: its exact multiplier
`exp(c z) - 1` tends to zero, with first-order jet `z` after division by `c`.

Thus adaptive shrinking cannot combine the Mertens energy gain with uniform divisor-mode
observability. Every finite stage remains algebraically faithful, while inverse reconstruction
loses a factor of order `1 / c`. This is the mode-level companion to the normalized carrier
source-retention wall.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Global linear-exponential bound for attenuation of one divisor mode. -/
theorem norm_xiPhysicalLogWindowModeMultiplier_le
    (c : ℝ) (z : ℂ) :
    ‖xiPhysicalLogWindowModeMultiplier c z‖ ≤
      |c| * ‖z‖ * Real.exp (|c| * ‖z‖) := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp ((c : ℂ) * z) 1
  simpa [xiPhysicalLogWindowModeMultiplier, Finset.sum_range_succ,
    Nat.factorial, norm_mul, abs_mul] using h

/-- An adaptive aperture collapsing to zero attenuates every fixed divisor mode to zero. -/
theorem tendsto_xiPhysicalLogWindowModeMultiplier_zero_of_width
    {ι : Type*} {l : Filter ι} {c : ι → ℝ}
    (hc : Tendsto c l (𝓝 0)) (z : ℂ) :
    Tendsto (fun i => xiPhysicalLogWindowModeMultiplier (c i) z) l (𝓝 0) := by
  have hcC : Tendsto (fun i => (c i : ℂ)) l (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hc
  have harg : Tendsto (fun i => (c i : ℂ) * z) l (𝓝 0) := by
    simpa using hcC.mul_const z
  simpa [xiPhysicalLogWindowModeMultiplier] using
    (Complex.continuous_exp.continuousAt.tendsto.comp harg).sub_const 1

/-- The lost multiplier has exact first-order divisor jet `z` along positive widths. -/
theorem tendsto_xiPhysicalLogWindowModeMultiplier_div_width
    (z : ℂ) :
    Tendsto
      (fun c : ℝ => xiPhysicalLogWindowModeMultiplier c z / (c : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 z) := by
  have hderiv : HasDerivAt
      (fun w : ℂ => Complex.exp (w * z) - 1) z 0 := by
    simpa using
      (((hasDerivAt_id (x := (0 : ℂ))).mul_const z).cexp.sub_const 1)
  simpa [xiPhysicalLogWindowModeMultiplier] using
    hasDerivAt_tendsto_real_slope_zero_right hderiv

/-- Every positive adaptive-width schedule inherits the exact first-order divisor jet. -/
theorem tendsto_xiPhysicalLogWindowModeMultiplier_div_width_of_width
    {ι : Type*} {l : Filter ι} {c : ι → ℝ}
    (hc : Tendsto c l (𝓝[>] (0 : ℝ))) (z : ℂ) :
    Tendsto
      (fun i => xiPhysicalLogWindowModeMultiplier (c i) z / (c i : ℂ))
      l (𝓝 z) :=
  (tendsto_xiPhysicalLogWindowModeMultiplier_div_width z).comp hc

/-- Multiplier norm is asymptotic to `c * ‖z‖` along positive widths. -/
theorem tendsto_norm_xiPhysicalLogWindowModeMultiplier_div_width
    (z : ℂ) :
    Tendsto
      (fun c : ℝ => ‖xiPhysicalLogWindowModeMultiplier c z‖ / c)
      (𝓝[>] (0 : ℝ)) (𝓝 ‖z‖) := by
  have h := continuous_norm.continuousAt.tendsto.comp
    (tendsto_xiPhysicalLogWindowModeMultiplier_div_width z)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  change 0 < c at hc
  simp [Real.norm_eq_abs, abs_of_pos hc]

/-- The attenuation is eventually two-sided linear for every nonzero mode. -/
theorem eventually_norm_xiPhysicalLogWindowModeMultiplier_two_sided
    {z : ℂ} (hz : z ≠ 0) :
    ∀ᶠ c in 𝓝[>] (0 : ℝ),
      (‖z‖ / 2) * c ≤ ‖xiPhysicalLogWindowModeMultiplier c z‖ ∧
        ‖xiPhysicalLogWindowModeMultiplier c z‖ ≤ (2 * ‖z‖) * c := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hq := tendsto_norm_xiPhysicalLogWindowModeMultiplier_div_width z
  filter_upwards
      [hq.eventually (eventually_gt_nhds (by linarith : ‖z‖ / 2 < ‖z‖)),
       hq.eventually (eventually_lt_nhds (by linarith : ‖z‖ < 2 * ‖z‖)),
       self_mem_nhdsWithin] with c hl hu hc
  change 0 < c at hc
  constructor
  · exact le_of_lt ((lt_div_iff₀ hc).mp hl)
  · exact le_of_lt ((div_lt_iff₀ hc).mp hu)

/-- Positive shrinking windows never exactly censor a left-half-plane divisor mode, but their
response still converges to zero. -/
theorem xiPhysicalLogWindowModeMultiplier_adaptive_censorship
    {ι : Type*} {l : Filter ι} {c : ι → ℝ}
    (hcpos : ∀ i, 0 < c i) (hc : Tendsto c l (𝓝 0))
    {z : ℂ} (hz : z.re < 0) :
    (∀ i, xiPhysicalLogWindowModeMultiplier (c i) z ≠ 0) ∧
      Tendsto (fun i => xiPhysicalLogWindowModeMultiplier (c i) z) l (𝓝 0) := by
  exact ⟨fun i => xiPhysicalLogWindowModeMultiplier_ne_zero (hcpos i) hz,
    tendsto_xiPhysicalLogWindowModeMultiplier_zero_of_width hc z⟩

/-- No positive uniform response floor survives a shrinking aperture, even for one fixed mode. -/
theorem not_exists_uniform_positive_norm_xiPhysicalLogWindowModeMultiplier_of_width
    (c : ℕ → ℝ) (hc : Tendsto c atTop (𝓝 0)) (z : ℂ) :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ n,
      ε ≤ ‖xiPhysicalLogWindowModeMultiplier (c n) z‖ := by
  rintro ⟨ε, hε, hfloor⟩
  have hzero : Tendsto
      (fun n => ‖xiPhysicalLogWindowModeMultiplier (c n) z‖)
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using continuous_norm.continuousAt.tendsto.comp
      (tendsto_xiPhysicalLogWindowModeMultiplier_zero_of_width hc z)
  have hε0 : ε ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hzero
    (Eventually.of_forall hfloor)
  exact (not_lt_of_ge hε0) hε

end

end RHTower

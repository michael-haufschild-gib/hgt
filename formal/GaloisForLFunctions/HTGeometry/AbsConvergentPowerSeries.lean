import Mathlib

/-!
# Coefficients of an absolutely convergent power series

A power series `∑ aₙ wⁿ` whose coefficients decay geometrically past the unit circle is analytic on
a disc strictly larger than the closed unit disc.  If its sum vanishes on the unit circle — a set
with accumulation points inside that disc — the identity theorem forces the whole sum to vanish,
and the uniqueness of power-series coefficients forces every `aₙ` to vanish.
-/

namespace GaloisForLFunctions.HTGeometry

open FormalMultilinearSeries Filter Topology

noncomputable section

/-- The coefficients of an absolutely convergent power series vanishing near the origin are
zero. -/
theorem powerCoeff_eq_zero_of_eventuallyEq_zero {a : ℕ → ℂ} {ρ : NNReal} (hρ : 0 < ρ)
    (hsum : Summable fun n : ℕ => ‖a n‖ * (ρ : ℝ) ^ n)
    (hzero : (fun w : ℂ => ∑' n : ℕ, a n * w ^ n) =ᶠ[𝓝 0] 0) : ∀ n, a n = 0 := by
  set p : FormalMultilinearSeries ℂ ℂ ℂ := ofScalars ℂ a with hp
  have hradius : (ρ : ENNReal) ≤ p.radius := by
    refine p.le_radius_of_summable_norm ?_
    refine hsum.congr fun n => ?_
    rw [hp, ofScalars_norm]
  have hpos : 0 < p.radius := lt_of_lt_of_le (by exact_mod_cast hρ) hradius
  have hsumfun : p.sum = fun w : ℂ => ∑' n : ℕ, a n * w ^ n := by
    funext w
    rw [FormalMultilinearSeries.sum]
    refine tsum_congr fun n => ?_
    rw [hp, ofScalars_apply_eq, smul_eq_mul]
  have hat : HasFPowerSeriesAt (0 : ℂ → ℂ) p 0 := by
    refine (p.hasFPowerSeriesOnBall hpos).hasFPowerSeriesAt.congr ?_
    rw [hsumfun]
    exact hzero
  have hp0 : p = 0 := hat.eq_zero
  intro n
  refine (ofScalars_eq_zero ℂ n).mp ?_
  rw [← hp]
  exact congrFun hp0 n

/-- The analytic sum of an absolutely convergent power series on the disc of radius `ρ`. -/
theorem analyticOnNhd_powerSum {a : ℕ → ℂ} {ρ : NNReal} (hρ : 0 < ρ)
    (hsum : Summable fun n : ℕ => ‖a n‖ * (ρ : ℝ) ^ n) :
    AnalyticOnNhd ℂ (fun w : ℂ => ∑' n : ℕ, a n * w ^ n) (Metric.ball 0 (ρ : ℝ)) := by
  set p : FormalMultilinearSeries ℂ ℂ ℂ := ofScalars ℂ a with hp
  have hradius : (ρ : ENNReal) ≤ p.radius := by
    refine p.le_radius_of_summable_norm ?_
    refine hsum.congr fun n => ?_
    rw [hp, ofScalars_norm]
  have hpos : 0 < p.radius := lt_of_lt_of_le (by exact_mod_cast hρ) hradius
  have hsumfun : p.sum = fun w : ℂ => ∑' n : ℕ, a n * w ^ n := by
    funext w
    rw [FormalMultilinearSeries.sum]
    refine tsum_congr fun n => ?_
    rw [hp, ofScalars_apply_eq, smul_eq_mul]
  have hball := (p.hasFPowerSeriesOnBall hpos).analyticOnNhd
  rw [hsumfun] at hball
  refine hball.mono fun w hw => ?_
  have hw' : ‖w‖ < (ρ : ℝ) := by simpa using hw
  have hlt : ‖w‖ₑ < (ρ : ENNReal) := enorm_lt_coe.mpr hw'
  simpa [Metric.mem_eball, edist_eq_enorm_sub] using lt_of_lt_of_le hlt hradius

/-- Points of the unit circle accumulate at `1`. -/
theorem frequently_circle_ne_one {P : ℂ → Prop}
    (h : ∀ θ : ℝ, P (Complex.exp (Complex.I * (θ : ℂ)))) :
    ∃ᶠ z : ℂ in 𝓝[≠] (1 : ℂ), P z := by
  have hcont : Filter.Tendsto (fun θ : ℝ => Complex.exp (Complex.I * (θ : ℂ))) (𝓝 0) (𝓝 1) := by
    have : Continuous fun θ : ℝ => Complex.exp (Complex.I * (θ : ℂ)) := by fun_prop
    have h0 := this.tendsto 0
    simpa using h0
  have hne : ∀ᶠ θ : ℝ in 𝓝[≠] (0 : ℝ), Complex.exp (Complex.I * (θ : ℂ)) ≠ 1 := by
    have hball : ∀ᶠ θ : ℝ in 𝓝 (0 : ℝ), |θ| < 2 * Real.pi := by
      have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
      have := Metric.ball_mem_nhds (0 : ℝ) hpos
      filter_upwards [this] with θ hθ
      simpa [Real.dist_eq] using hθ
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hball] with θ hθ0 hθ
    intro hEq
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hEq
    have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    have hθk : (θ : ℂ) = (k : ℂ) * (2 * (Real.pi : ℂ)) := by
      refine mul_left_cancel₀ hI ?_
      rw [hk]
      ring
    have hθr : θ = (k : ℝ) * (2 * Real.pi) := by
      exact_mod_cast hθk
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0] at hθr
      simp at hθr
      exact hθ0 hθr
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs (by omega)
      have hcast : ((|k| : ℤ) : ℝ) = |(k : ℝ)| := by push_cast; rfl
      calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
        _ ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast this
        _ = |(k : ℝ)| := hcast
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    rw [hθr, abs_mul, abs_of_pos hpi] at hθ
    nlinarith
  have htend : Filter.Tendsto (fun θ : ℝ => Complex.exp (Complex.I * (θ : ℂ)))
      (𝓝[≠] (0 : ℝ)) (𝓝[≠] (1 : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hcont.mono_left nhdsWithin_le_nhds) hne
  exact htend.frequently ((Filter.Eventually.of_forall h).frequently)

/-- **Vanishing on the unit circle kills every coefficient.** -/
theorem powerCoeff_eq_zero_of_circle {a : ℕ → ℂ} {ρ : NNReal} (hρ : 1 < ρ)
    (hsum : Summable fun n : ℕ => ‖a n‖ * (ρ : ℝ) ^ n)
    (hcirc : ∀ θ : ℝ, ∑' n : ℕ, a n * Complex.exp (Complex.I * (θ : ℂ)) ^ n = 0) :
    ∀ n, a n = 0 := by
  have hρ0 : 0 < ρ := lt_trans zero_lt_one hρ
  have hρ1 : (1 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ
  have hanalytic := analyticOnNhd_powerSum hρ0 hsum
  have hmem : (1 : ℂ) ∈ Metric.ball (0 : ℂ) (ρ : ℝ) := by
    simp only [Metric.mem_ball, dist_zero_right, norm_one]
    exact hρ1
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] (1 : ℂ), (fun w : ℂ => ∑' n : ℕ, a n * w ^ n) z = 0 :=
    frequently_circle_ne_one hcirc
  have hEqOn : Set.EqOn (fun w : ℂ => ∑' n : ℕ, a n * w ^ n) 0 (Metric.ball 0 (ρ : ℝ)) :=
    hanalytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
      (convex_ball (0 : ℂ) (ρ : ℝ)).isPreconnected hmem hfreq
  refine powerCoeff_eq_zero_of_eventuallyEq_zero hρ0 hsum ?_
  have hnhds : Metric.ball (0 : ℂ) (ρ : ℝ) ∈ 𝓝 (0 : ℂ) :=
    Metric.ball_mem_nhds _ (lt_trans zero_lt_one hρ1)
  filter_upwards [hnhds] with w hw using hEqOn hw

end

end GaloisForLFunctions.HTGeometry

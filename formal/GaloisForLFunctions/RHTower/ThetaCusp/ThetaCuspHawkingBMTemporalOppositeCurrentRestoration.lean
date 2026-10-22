import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMTemporalNormalizableCurrentDensity
import GaloisForLFunctions.HTGeometry.LogarithmicEndpointFinitePart

/-! Logarithmic restoration and analytic continuation of the full original opposite current. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric MeasureTheory D4BMLaplaceRadial D4BMModularCore
  D4BMJointWave GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-- The actual missing normalizable-current contribution has a derived logarithmic counterterm
and an analytic restored value at every sufficiently small common cutoff. -/
theorem physicalOppositeTemporalCurrent_horizon_restoration (q : XiZeroCopy) (branch side : Bool)
    (a : ℂ) (zang : D4BMHorizon.Point) :
    ∃ R B : ℝ, ∃ d : ℂ → ℂ, 0 < R ∧ 0 < B ∧ B ≤ 1 / 2 ∧
      ∀ b : ℝ, 0 < b → b ≤ B →
        AnalyticAt ℂ (LogarithmicEndpoint.finitePart (oppositeTemporalProfile q branch a zang) d b)
          (physicalFundamentalFrequency q side) ∧
        Tendsto (fun w => (w - physicalFundamentalFrequency q side) *
          LogarithmicEndpoint.finitePart (oppositeTemporalProfile q branch a zang) d b w)
          (𝓝[≠] physicalFundamentalFrequency q side) (𝓝 0) ∧
        ∀ w ∈ ball (physicalFundamentalFrequency q side) R,
          connection w (physicalRadialFrequency q) ≠ 0 →
          Tendsto (fun e : ℝ => (∫ z in e..b, oppositeTemporalRadialDensity q branch a zang w z) +
            d w * (Real.log e : ℂ)) (𝓝[>] (0:ℝ))
            (𝓝 (LogarithmicEndpoint.finitePart (oppositeTemporalProfile q branch a zang) d b w)) := by
  let w₀ := physicalFundamentalFrequency q side
  have hw : w₀.im ≠ 0 := (physicalFundamentalFrequency_strip q side).1
  have hwr : -2 < w₀.re := (abs_lt.mp (physicalFundamentalFrequency_strip q side).2).1
  have hs : w₀ - 2 * physicalRate q branch ≠ 0 :=
    physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side
  obtain ⟨RG, BG, CG, hRG, hBG, _, _, hg⟩ :=
    horizonGauss_uniform_nonzero w₀ (physicalRadialFrequency q) hw
  obtain ⟨RJ, B, hRJ, hRJG, hB, hBBG, hBh, d, d₁, C, M, hC, _, hd, _, _, hd₁, hj⟩ :=
    (oppositeTemporalProfile_germ q branch side a zang).exists_bounded hRG hBG
  have hreal : ∀ᶠ u : ℂ in 𝓝 w₀, -2 < u.re :=
    continuousAt_const.eventually_lt Complex.continuous_re.continuousAt hwr
  have hsource : ∀ᶠ u : ℂ in 𝓝 w₀, u - 2 * physicalRate q branch ≠ 0 :=
    (continuousAt_id.sub continuousAt_const).eventually_ne hs
  have hprincipal : ∀ᶠ u : ℂ in 𝓝 w₀, ∀ i : Fin 3, connection u (principalFrequency q i) ≠ 0 :=
    Filter.eventually_all.mpr (fun i =>
      (connection_frequency_analyticAt w₀ (principalFrequency q i) hw).continuousAt.eventually_ne
        (physicalFundamental_principal_connection_ne_zero q side i))
  obtain ⟨RA, hRA, hdata⟩ := Metric.eventually_nhds_iff.mp
    ((Complex.continuous_im.continuousAt.eventually_ne hw).and
      (hreal.and (hsource.and (hprincipal.and hd.eventually_analyticAt))))
  let R := min RJ RA
  have hR : 0 < R := lt_min hRJ hRA
  have hJ (u : ℂ) (hu : u ∈ ball w₀ R) : u ∈ closedBall w₀ RJ :=
    ball_subset_closedBall (ball_subset_ball (min_le_left RJ RA) hu)
  have hD (u : ℂ) (hu : u ∈ ball w₀ R) :=
    hdata (mem_ball.mp (ball_subset_ball (min_le_right RJ RA) hu))
  have hG (u : ℂ) (hu : u ∈ ball w₀ R) (z : ℝ) (hz : z ∈ Ioc (0:ℝ) B) :
      gaussProfile q u z ≠ 0 := by
    have hn := (hg u (ball_subset_ball ((min_le_left RJ RA).trans hRJG) hu)
      z ⟨hz.1.le, hz.2.trans hBBG⟩).2.1
    change (1/2 : ℝ) ≤ ‖gaussProfile q u z‖ at hn
    intro he
    rw [he, norm_zero] at hn
    linarith
  have hbound (u : ℂ) (hu : u ∈ ball w₀ R) (z : ℝ) (hz : z ∈ Ioc (0:ℝ) B) :
      ‖oppositeTemporalProfile q branch a zang u z - d u‖ ≤ (C + M) * z := by
    have hrem := hj u (hJ u hu) z hz
    have hlinear : ‖d₁ u * (z : ℂ)‖ ≤ M * z := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz.1]
      exact mul_le_mul_of_nonneg_right (hd₁ u (hJ u hu)) hz.1.le
    have hzsq : z ^ (2 : ℕ) ≤ z := by nlinarith [hz.1, hz.2, hBh]
    calc
      _ = ‖(oppositeTemporalProfile q branch a zang u z - d u - d₁ u * (z : ℂ)) +
          d₁ u * (z : ℂ)‖ := by congr 1; ring
      _ ≤ ‖oppositeTemporalProfile q branch a zang u z - d u - d₁ u * (z : ℂ)‖ +
          ‖d₁ u * (z : ℂ)‖ := norm_add_le _ _
      _ ≤ C * z ^ (2 : ℕ) + M * z := add_le_add hrem hlinear
      _ ≤ (C + M) * z := by nlinarith [mul_le_mul_of_nonneg_left hzsq hC]
  refine ⟨R, B, d, hR, hB, hBh, ?_⟩
  intro b hb hbB
  have hb1 : b < 1 := by linarith
  have hsp (u : ℂ) (hu : u ∈ ball w₀ R) :
      ContinuousOn (oppositeTemporalProfile q branch a zang u) (Ioc (0:ℝ) b) := by
    intro z hz
    exact (oppositeTemporalProfile_continuousAt q branch a u zang (hD u hu).1 (hD u hu).2.1
      ⟨hz.1, hz.2.trans_lt hb1⟩ (hG u hu z ⟨hz.1, hz.2.trans hbB⟩)).continuousWithinAt
  have hA : AnalyticAt ℂ
      (LogarithmicEndpoint.finitePart (oppositeTemporalProfile q branch a zang) d b) w₀ :=
    LogarithmicEndpoint.finitePart_analyticAt hR hsp (fun u hu => (hD u hu).2.2.2.2)
      (fun z hz u hu => oppositeTemporalProfile_analyticAt q branch a u zang
        (hD u hu).1 (hD u hu).2.1 (hD u hu).2.2.1 (hD u hu).2.2.2.1
        ⟨hz.1, hz.2.trans_lt hb1⟩ (hG u hu z ⟨hz.1, hz.2.trans hbB⟩))
      (fun u hu z hz => hbound u hu z ⟨hz.1, hz.2.trans hbB⟩)
  refine ⟨hA, ?_, ?_⟩
  · have hx : Tendsto (fun u : ℂ => u - w₀) (𝓝[≠] w₀) (𝓝 0) := by
      have hi : Tendsto (fun u : ℂ => u) (𝓝[≠] w₀) (𝓝 w₀) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [sub_self] using hi.sub_const w₀
    simpa only [zero_mul] using hx.mul (hA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  intro u hu hc
  have hlim := LogarithmicEndpoint.cutoff_tendsto hb (hsp u hu)
    (fun z hz => hbound u hu z ⟨hz.1, hz.2.trans hbB⟩)
  apply hlim.congr'
  have heb : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e < b :=
    (show ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e < b from Iio_mem_nhds hb).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, heb] with e he heb
  congr 1
  apply intervalIntegral.integral_congr
  intro z hz
  rw [uIcc_of_le heb.le] at hz
  exact (oppositeTemporalRadialDensity_eq_profile q branch a u zang (hD u hu).1 (hD u hu).2.2.1 hc
    ⟨he.trans_le hz.1, hz.2.trans_lt hb1⟩).symm

end
end RHTower.D4BMJointSource

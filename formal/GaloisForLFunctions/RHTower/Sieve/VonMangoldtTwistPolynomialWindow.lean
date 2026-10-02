import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicFullFrequencySchedule

/-!
# Uniform Mangoldt cancellation on a growing frequency window

The free-width Route-T estimate applies directly to the Mangoldt prefix.
The full-frequency majorant therefore gives uniform little-o of the
prefix length throughout its entire growing cutoff and frequency window.
Prime powers are retained. This is the high-frequency input for the
prime-polar multiplier in the actual Suzuki source equation.
-/

namespace RHTower.Sieve
open Filter Topology
noncomputable section

/-- The complete twisted Mangoldt prefix is uniformly small, from the
polylogarithmic frequency floor to the full ambient frequency, for every
cutoff in the stated growing window. -/
theorem eventually_norm_vonMangoldtTwist_prefix_le_polynomialWindow
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ (N : ℕ) (τ : ℝ),
      twoRangeXmin ((19 : ℝ) / 20) x ≤ (N : ℝ) →
      Real.log (N : ℝ) ≤ twoRangeLx 2 x →
      twoRangeT₀ 2 100 x ≤ |τ| → |τ| ≤ 2 * Real.pi * x →
      ‖∑ n ∈ Finset.range (N + 1), vonMangoldtTwist τ n‖ ≤ ε * (N : ℝ) := by
  obtain ⟨A, Creg, delta, Ctot, τ₀, _, hdelta, hCtot, _, hroute⟩ :=
    exists_norm_partialSum_vonMangoldtTwist_routeT_scaled
  let R : ℝ → ℝ := fun x =>
    relScaledMajorant Ctot (twoRangeWidth 2 100 x) (twoRangeLx 2 x)
      ((Real.log x) ^ (2 : ℝ)) (menonHarmonicFullFrequencyMu A delta x)
      (twoRangeQ ((19 : ℝ) / 20) x) (twoRangeT₀ 2 100 x)
      (twoRangeXmin ((19 : ℝ) / 20) x)
  have hlim : Tendsto (fun x => (Real.log x) ^ (40 : ℝ) * R x) atTop (𝓝 0) :=
    tendsto_logPow_forty_mul_menonHarmonicFullFrequencyRelMajorant hdelta hCtot
  have hbase : ∀ᶠ x : ℝ in atTop,
      Real.exp 9 ≤ twoRangeXmin ((19 : ℝ) / 20) x :=
    (tendsto_cardLength (by norm_num : (0 : ℝ) < 19 / 20)).eventually_ge_atTop _
  filter_upwards [hbase, hlim.eventually_le_const hε,
    one_le_twoRangeWidth (b := (2 : ℝ)) (A₃ := (100 : ℝ)) (by norm_num) (by norm_num),
    twoRangeDisc_ge (b := (2 : ℝ)) (A₃ := (100 : ℝ)) (by norm_num) (by norm_num) τ₀,
    eventually_menonHarmonicFullFrequency_heightCost_le_logSq
      (A := A) (b := (2 : ℝ)) (A₃ := (100 : ℝ)) (by norm_num) (by norm_num),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    eventually_gt_atTop (1 : ℝ)] with x hbase hsmall hD hdisc hheight hlog hx
  intro N τ hN hlogN hlo hhi
  have hNlarge : Real.exp 9 ≤ (N : ℝ) := hbase.trans hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) :=
    (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 9)).trans hNlarge
  have hN0 : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one hN1
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hdisc' : max τ₀ (16 * Real.pi / 3) ≤ twoRangeT₀ 2 100 x := by
    simpa only [two_pi_mul_twoRangeDisc] using hdisc
  have hτ₀ : τ₀ ≤ |τ| := (le_max_left _ _).trans (hdisc'.trans hlo)
  have hτ : 16 * Real.pi / 3 ≤ |τ| := (le_max_right _ _).trans (hdisc'.trans hlo)
  have hσ : 0 < 2 * Real.pi * x := by positivity
  have hhi' : |τ| ≤ |2 * Real.pi * x| := by rwa [abs_of_pos hσ]
  have hq : twoRangeQ ((19 : ℝ) / 20) x ≤ Real.log (N : ℝ) := by
    have h := Real.log_le_log (twoRangeXmin_pos _ _) hN
    simpa only [twoRangeXmin, log_cardLength, twoRangeQ] using h
  have hmu : menonHarmonicFullFrequencyMu A delta x ≤
      min delta (routeTWidthPolylogLower A τ) / 2 := by
    rw [menonHarmonicFullFrequencyMu]
    exact div_le_div_of_nonneg_right
      (min_le_min_left delta (routeTWidthPolylogLower_antitone hhi')) (by norm_num)
  have hrel : relScaledEnvelope A delta Ctot (twoRangeWidth 2 100 x) τ (N : ℝ) ≤ R x :=
    relScaledEnvelope_le_uniform hCtot.le (twoRangeWidth_pos hx) hτ hN1
      (twoRangeT₀_pos hx) hlo hhi' hlogN (twoRangeQ_nonneg hx) hq
      (menonHarmonicFullFrequencyMu_nonneg hdelta.le x) hmu
      (twoRangeXmin_pos _ _) hN (by simpa only [abs_of_pos hσ] using hheight)
  have hR0 : 0 ≤ R x := by
    exact relScaledMajorant_nonneg hCtot.le (twoRangeWidth_pos hx)
      (by rw [twoRangeLx]; positivity) (by positivity)
      (twoRangeT₀_pos hx) (twoRangeXmin_pos _ _)
  have hlogpow : (1 : ℝ) ≤ (Real.log x) ^ (40 : ℝ) := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hlog (by norm_num : (0 : ℝ) ≤ 40)
  have hRε : R x ≤ ε := by
    have h := mul_le_mul_of_nonneg_right hlogpow hR0
    simpa only [one_mul] using h.trans hsmall
  have hbound := hroute N (twoRangeWidth 2 100 x) τ hNlarge hD hτ₀
  have hrewrite : (3 * (N : ℝ)) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2))) =
      (3 : ℝ) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2))) *
        (N : ℝ) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2))) :=
    Real.mul_rpow (by norm_num) hN0.le
  rw [hrewrite] at hbound
  have hextra : 0 ≤ 2 * Real.log (N : ℝ) / Real.sqrt (N : ℝ) := by positivity
  have hscaled : ‖∑ n ∈ Finset.range (N + 1), vonMangoldtTwist τ n‖ ≤
      (N : ℝ) * relScaledEnvelope A delta Ctot (twoRangeWidth 2 100 x) τ (N : ℝ) := by
    rw [relScaledEnvelope, scaledHeightFactor]
    convert hbound.trans (le_add_of_nonneg_right (mul_nonneg hN0.le hextra)) using 1 <;>
      first | rfl | ring
  exact hscaled.trans ((mul_le_mul_of_nonneg_left (hrel.trans hRε) hN0.le).trans_eq
    (mul_comm (N : ℝ) ε))

end
end RHTower.Sieve

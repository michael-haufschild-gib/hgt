import GaloisForLFunctions.BezoutValuationIncidence.ExactDampedSingularSeriesAndGallagherPrefixDiscrepancy
import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedLinearDissipationExactRate
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusSmallDampingVariance

/-!
# Second-order small-damping laws from the singular series

The variance `V(ε) = E[τ_ε²] - ρ_ε²` and the Haar dissipation rate `R(ε)` of the damped source
both behave like `ε/2` to first order. The second-order terms differ:

`V(ε) = ε/2 - ε² + o(ε²)`,   `R(ε) = ε/2 + o(ε²)`.

**The variance.** The second density factors as `E[τ_ε²] = C(ε) ζ(1+2ε)/ζ(1+ε)²`. Each prime
deficit of the correction `C(ε) = ∏_p (1 - ((t - t²)/(p - t))²)`, with `t = p^{-ε}`, is at most
`ε² (log p/(p-1))²`, so `C(ε) = 1 - O(ε²)`. With `ζ(1+δ) = 1/δ + γ + o(1)`,

`V(ε) = (C(ε) ζ(1+2ε) - 1)/ζ(1+ε)² = ε/2 - ε² + o(ε²)`;

the Euler constant cancels between the two zeta values.

**The dissipation rate.** The Bézout limit `Σ_e μ(e) w_ε(e)²` equals `ρ_ε² 𝔖_ε(1)`, the lag-one
damped singular series, because the Ramanujan sum at lag one is `c_e(1) = μ(e)`. Hence

`R(ε) = V(ε) + ρ_ε² (1 - 𝔖_ε(1))`,

and `𝔖_ε(1) → 𝔖(1) = 0`: of two consecutive integers one is even. The extra `ρ_ε² ~ ε²` exactly
cancels the second-order term of the variance.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-! ## §1. The variance correction is `1 - O(ε²)` -/

theorem pmPowerDampedVariancePrimeDeficit_le_sq {ε : ℝ} (hε : 0 ≤ ε) (p : Nat.Primes) :
    RHTower.pmPowerDampedVariancePrimeDeficit ε p ≤
      ε ^ 2 * (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1)) ^ 2 := by
  set t := ((p : ℕ) : ℝ) ^ (-ε) with ht
  have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.prop.two_le
  have ht0 : 0 ≤ t := Real.rpow_nonneg (by linarith) _
  have ht1 : t ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (neg_nonpos.mpr hε)
  have hlog : 1 - t ≤ ε * Real.log (p : ℕ) := by
    have he : t = Real.exp (-(ε * Real.log (p : ℕ))) := by
      rw [ht, Real.rpow_def_of_pos (by linarith)]
      ring_nf
    have := Real.add_one_le_exp (-(ε * Real.log (p : ℕ)))
    linarith
  have hd : (0 : ℝ) < ((p : ℕ) : ℝ) - 1 := by linarith
  have hq : (t - t ^ 2) / (((p : ℕ) : ℝ) - t) ≤ ε * Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1) := by
    calc (t - t ^ 2) / (((p : ℕ) : ℝ) - t) ≤ (1 - t) / (((p : ℕ) : ℝ) - 1) := by
          rw [div_le_div_iff₀ (by linarith) hd]
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (p : ℕ)) (sq_nonneg (1 - t))]
      _ ≤ _ := div_le_div_of_nonneg_right hlog hd.le
  have hq0 : 0 ≤ (t - t ^ 2) / (((p : ℕ) : ℝ) - t) := div_nonneg (by nlinarith) (by linarith)
  unfold RHTower.pmPowerDampedVariancePrimeDeficit
  calc ((t - t ^ 2) / (((p : ℕ) : ℝ) - t)) ^ 2
      ≤ (ε * Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1)) ^ 2 := pow_le_pow_left₀ hq0 hq 2
    _ = _ := by ring

theorem summable_log_div_sub_one_sq :
    Summable fun p : Nat.Primes => (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1)) ^ 2 := by
  have hs : Summable fun p : Nat.Primes => 64 * ((((p : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    ((Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 3 / 2)).comp_injective
      Subtype.val_injective).mul_left 64
  refine Summable.of_nonneg_of_le (fun p => sq_nonneg _) (fun p => ?_) hs
  have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.prop.two_le
  have hp0 : (0 : ℝ) < (p : ℕ) := by linarith
  have hlog0 : 0 ≤ Real.log (p : ℕ) := Real.log_nonneg (by linarith)
  have hlog : Real.log (p : ℕ) ≤ 4 * ((p : ℕ) : ℝ) ^ (1 / 4 : ℝ) := by
    have := Real.log_le_rpow_div (x := (p : ℕ)) (ε := 1 / 4) hp0.le (by norm_num)
    linarith
  have hsq : Real.log (p : ℕ) ^ 2 ≤ 16 * ((p : ℕ) : ℝ) ^ (1 / 2 : ℝ) := by
    have h1 : (((p : ℕ) : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = ((p : ℕ) : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
      norm_num
    nlinarith [pow_le_pow_left₀ hlog0 hlog 2]
  have hden : ((p : ℕ) : ℝ) ^ 2 / 4 ≤ (((p : ℕ) : ℝ) - 1) ^ 2 := by nlinarith
  have hsplit : ((p : ℕ) : ℝ) ^ (1 / 2 : ℝ) * ((p : ℕ) : ℝ) ^ (3 / 2 : ℝ) = ((p : ℕ) : ℝ) ^ 2 := by
    rw [← Real.rpow_add hp0]
    norm_num
  have hpos32 : 0 < ((p : ℕ) : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hp0 _
  rw [div_pow, div_le_iff₀ (by nlinarith)]
  calc Real.log (p : ℕ) ^ 2 ≤ 16 * ((p : ℕ) : ℝ) ^ (1 / 2 : ℝ) := hsq
    _ = 64 * (((p : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹ * (((p : ℕ) : ℝ) ^ 2 / 4) := by
        rw [← hsplit]
        field_simp
        norm_num
    _ ≤ 64 * (((p : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹ * (((p : ℕ) : ℝ) - 1) ^ 2 :=
        mul_le_mul_of_nonneg_left hden (by positivity)

/-- **The correction is `1 - O(ε²)`.** -/
theorem pmPowerDampedVarianceCorrection_ge {ε : ℝ} (hε : 0 < ε) :
    1 - ε ^ 2 * (∑' p : Nat.Primes, (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1)) ^ 2) ≤
      RHTower.pmPowerDampedVarianceCorrection ε := by
  have hb := (RHTower.pmPowerDampedVarianceCorrection_bounds hε).1
  have hle : ∑' p : Nat.Primes, RHTower.pmPowerDampedVariancePrimeDeficit ε p ≤
      ε ^ 2 * ∑' p : Nat.Primes, (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1)) ^ 2 := by
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun p => pmPowerDampedVariancePrimeDeficit_le_sq hε.le p)
      (RHTower.summable_pmPowerDampedVariancePrimeDeficit hε.le)
      (summable_log_div_sub_one_sq.mul_left _)
  linarith

/-! ## §2. The zeta expansion at `1` -/

/-- `1/ρ(δ) = ζ(1+δ)` is real, and `1/ρ(δ) - 1/δ → γ`. -/
theorem tendsto_inv_density_sub_inv :
    Tendsto (fun δ : ℝ => 1 / (RHTower.pmPowerDampedDivisorDensity δ).re - 1 / δ) (𝓝[>] 0)
      (𝓝 Real.eulerMascheroniConstant) := by
  have hshift : Tendsto (fun δ : ℝ => 1 + δ) (𝓝[>] 0) (𝓝[>] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h0 : Tendsto (fun δ : ℝ => 1 + δ) (𝓝 0) (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add tendsto_id
      simpa using h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      simp only [Set.mem_Ioi]
      linarith [Set.mem_Ioi.mp hδ]
  have h := (Complex.continuous_re.tendsto _).comp
    (ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right.comp hshift)
  simp only [Complex.ofReal_re] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : 0 < δ := hδ
  have hD := RHTower.pmPowerDampedDivisorDensity_eq_ofReal_re hδ0
  have hρ := RHTower.pmPowerDampedDivisorDensity_re_pos hδ0
  have hζ : riemannZeta (1 + (δ : ℂ)) =
      ((1 / (RHTower.pmPowerDampedDivisorDensity δ).re : ℝ) : ℂ) := by
    have h1 : 1 / riemannZeta (1 + (δ : ℂ)) = ((RHTower.pmPowerDampedDivisorDensity δ).re : ℂ) :=
      hD
    have hz : riemannZeta (1 + (δ : ℂ)) ≠ 0 :=
      riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
    push_cast
    rw [← h1, one_div_one_div]
  simp only [Function.comp_apply]
  rw [show ((1 + δ : ℝ) : ℂ) = 1 + (δ : ℂ) by push_cast; ring, hζ,
    show (1 + (δ : ℂ) - 1) = (δ : ℂ) by ring]
  push_cast
  simp

/-! ## §3. The second-order law of the variance -/

/-- **`V(ε) = ε/2 - ε² + o(ε²)`.** -/
theorem tendsto_variance_second_order :
    Tendsto (fun ε => (RHTower.pmPowerDampedDivisorVariance ε - ε / 2) / ε ^ 2) (𝓝[>] 0)
      (𝓝 (-1)) := by
  set K := ∑' p : Nat.Primes, (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1)) ^ 2
  set γ := Real.eulerMascheroniConstant with hγdef
  set z : ℝ → ℝ := fun δ => 1 / (RHTower.pmPowerDampedDivisorDensity δ).re
  set C : ℝ → ℝ := RHTower.pmPowerDampedVarianceCorrection
  have hu : Tendsto (fun ε => z ε - 1 / ε - γ) (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_inv_density_sub_inv.sub_const γ
    rw [← hγdef, sub_self] at h
    exact h
  have hdouble : Tendsto (fun ε : ℝ => 2 * ε) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h0 : Tendsto (fun ε : ℝ => 2 * ε) (𝓝 0) (𝓝 (2 * 0)) :=
        tendsto_const_nhds.mul tendsto_id
      simpa using h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact mul_pos two_pos (Set.mem_Ioi.mp hε)
  have hv : Tendsto (fun ε => z (2 * ε) - 1 / (2 * ε) - γ) (𝓝[>] 0) (𝓝 0) := hu.comp hdouble
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  -- the correction term `(1 - C) z(2ε)` vanishes
  have hc : Tendsto (fun ε => (1 - C ε) * z (2 * ε)) (𝓝[>] 0) (𝓝 0) := by
    have hbound : Tendsto (fun ε : ℝ => K * (ε / 2 + ε ^ 2 * |γ + (z (2 * ε) - 1 / (2 * ε) - γ)|))
        (𝓝[>] 0) (𝓝 0) := by
      have := ((he.div_const 2).add ((he.pow 2).mul ((hv.const_add γ).abs))).const_mul K
      simpa using this
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : 0 < ε := hε
    have hC := pmPowerDampedVarianceCorrection_ge hε0
    have hC1 := (RHTower.pmPowerDampedVarianceCorrection_bounds hε0).2
    have hK : 0 ≤ K := tsum_nonneg fun p => sq_nonneg _
    have hz2 : z (2 * ε) = 1 / (2 * ε) + (γ + (z (2 * ε) - 1 / (2 * ε) - γ)) := by ring
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - C ε)]
    calc (1 - C ε) * |z (2 * ε)| ≤ ε ^ 2 * K * |z (2 * ε)| :=
          mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ ≤ ε ^ 2 * K * (1 / (2 * ε) + |γ + (z (2 * ε) - 1 / (2 * ε) - γ)|) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          conv_lhs => rw [hz2]
          refine (abs_add_le _ _).trans ?_
          rw [abs_of_pos (by positivity : 0 < 1 / (2 * ε))]
      _ = K * (ε / 2 + ε ^ 2 * |γ + (z (2 * ε) - 1 / (2 * ε) - γ)|) := by
          field_simp
  -- the numerator tends to `-1`
  have hN : Tendsto (fun ε => (z (2 * ε) - 1 / (2 * ε) - γ) - (z ε - 1 / ε - γ) - 1 -
      (1 - C ε) * z (2 * ε) - ε / 2 * (γ + (z ε - 1 / ε - γ)) ^ 2) (𝓝[>] 0) (𝓝 (-1)) := by
    have := (((hv.sub hu).sub_const 1).sub hc).sub
      ((he.div_const 2).mul ((hu.const_add γ).pow 2))
    simpa using this
  -- `ε z(ε) → 1`
  have hez : Tendsto (fun ε => (ε * z ε) ^ 2) (𝓝[>] 0) (𝓝 1) := by
    have h1 : Tendsto (fun ε => 1 + ε * (γ + (z ε - 1 / ε - γ))) (𝓝[>] 0) (𝓝 1) := by
      simpa using (he.mul (hu.const_add γ)).const_add 1
    have h2 := h1.pow 2
    rw [one_pow] at h2
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : ε ≠ 0 := ne_of_gt hε
    field_simp
    ring
  have hlim := hN.div hez one_ne_zero
  rw [div_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : 0 < ε := hε
  have hρ1 := RHTower.pmPowerDampedDivisorDensity_re_pos hε0
  have hρ2 := RHTower.pmPowerDampedDivisorDensity_re_pos (by linarith : 0 < 2 * ε)
  have hV : RHTower.pmPowerDampedDivisorVariance ε =
      (C ε * z (2 * ε) - 1) / z ε ^ 2 := by
    simp only [RHTower.pmPowerDampedDivisorVariance, C, RHTower.pmPowerDampedVarianceCorrection, z]
    field_simp
  have hzpos : 0 < z ε := by simp only [z]; positivity
  simp only [Pi.div_apply]
  rw [hV]
  field_simp
  ring

/-! ## §4. The second-order law of the dissipation rate -/

theorem ramanujanLagWeight_one_left (e : ℕ) : ramanujanLagWeight 1 e = moebiusReal e := by
  rw [ramanujanLagWeight_eq_ramanujanLagCoefficient, ramanujanLagCoefficient]
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp [moebiusReal]
  rw [sum_eq_single 1]
  · simp
  · intro d hd hd1
    rw [if_neg (fun h => hd1 (Nat.dvd_one.mp h)), mul_zero]
  · intro h
    exact absurd (Nat.one_mem_divisors.mpr he.ne') h

/-- The Bézout limit is the lag-one damped singular series. -/
theorem dampedBezoutLimit_eq {ε : ℝ} (hε : 0 < ε) :
    dampedBezoutLimit ε =
      (RHTower.pmPowerDampedDivisorDensity ε).re ^ 2 * dampedSingularSeries ε 1 := by
  rw [dampedBezoutLimit, dampedSingularSeries, ← tsum_mul_left]
  refine tsum_congr fun e => ?_
  have hρ := RHTower.pmPowerDampedDivisorDensity_re_pos hε
  have hw := dampedRamanujanCoeff_div_density hε e
  rw [div_eq_iff hρ.ne'] at hw
  rw [dampedSingularSeriesTerm, ramanujanLagWeight_one_left, hw]
  ring

/-- `R(ε) = V(ε) + ρ_ε² (1 - 𝔖_ε(1))`. -/
theorem dampedDissipationRate_eq {ε : ℝ} (hε : 0 < ε) :
    dampedDissipationRate ε = RHTower.pmPowerDampedDivisorVariance ε +
      (RHTower.pmPowerDampedDivisorDensity ε).re ^ 2 * (1 - dampedSingularSeries ε 1) := by
  rw [dampedDissipationRate, dampedBezoutLimit_eq hε, RHTower.pmPowerDampedDivisorVariance]
  ring

/-- **`R(ε) = ε/2 + o(ε²)`.** -/
theorem tendsto_dissipationRate_second_order :
    Tendsto (fun ε => (dampedDissipationRate ε - ε / 2) / ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hS := tendsto_dampedSingularSeries (h := 1) le_rfl
  rw [hardyLittlewoodSingularSeries_eq_zero_of_odd le_rfl (by norm_num)] at hS
  have hρ := RHTower.tendsto_pmPowerDampedDivisorDensity_re_div_parameter
  have h := tendsto_variance_second_order.add ((hρ.pow 2).mul (hS.const_sub 1))
  simp only [one_pow, sub_zero, mul_one, neg_add_cancel] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε ≠ 0 := ne_of_gt hε
  rw [dampedDissipationRate_eq hε]
  field_simp
  ring

end

end GaloisForLFunctions.BezoutValuationIncidence

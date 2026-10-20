import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedPeriodVarianceAndNonCommutingLimits
import GaloisForLFunctions.TransHorizonIncidenceMechanics.MoebiusBandAverageStepAndEnergyProfile

/-!
# The damped prefix energy is linear: band structure dissolves under damping

On a linear trans-horizon window `k ≤ (B+1)N` an integer has at most `B` divisors above the
horizon (their cofactors are `≤ B`), each damped by at least `(N+1)^{-ε}`. So the damped response is
uniformly close to the complete damped divisor function:

`|τ_ε(k) - s_N(k; c_ε)| ≤ B (N+1)^{-ε}`   for `1 ≤ k ≤ (B+1)N`,

and since `0 ≤ τ_ε ≤ 1` the prefix energy is the Cesàro sum of `τ_ε²` up to a vanishing error:

`E_N((B+1)N; c_ε)/N → (B+1) E[τ_ε²]`.

At every fixed damping the trans-horizon energy profile is linear in the band index, with slope
`E[τ_ε²] ~ ε/2`: the Möbius band structure (the profile `P(B)` with its band averages) is invisible.
The Möbius profile satisfies `P(B) ≥ 6/π²` for `B ≥ 1`, so for every band the cofinal and damping
limits of the prefix energy do not commute, and at all small dampings the damped prefix energy
stays strictly below the Möbius one at all large horizons.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- On the window `k ≤ (B+1)N` at most `B` divisors of `k` exceed the horizon. -/
theorem card_divisors_gt_le {N B k : ℕ} (hk : k ≤ (B + 1) * N) :
    (k.divisors.filter (fun d => N < d)).card ≤ B := by
  calc (k.divisors.filter (fun d => N < d)).card ≤ (Icc 1 B).card := by
        refine card_le_card_of_injOn (fun d => k / d) (fun d hd => ?_) (fun d₁ hd₁ d₂ hd₂ h => ?_)
        · simp only [coe_filter, Nat.mem_divisors, Set.mem_setOf_eq] at hd
          obtain ⟨⟨hdk, hk0⟩, hNd⟩ := hd
          have hd0 : 0 < d := by omega
          simp only [coe_Icc, Set.mem_Icc]
          refine ⟨Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hdk) hd0, ?_⟩
          have : k / d < B + 1 := (Nat.div_lt_iff_lt_mul hd0).mpr (by nlinarith)
          omega
        · simp only [coe_filter, Nat.mem_divisors, Set.mem_setOf_eq] at hd₁ hd₂
          rw [← Nat.div_div_self hd₁.1.1 hd₁.1.2, ← Nat.div_div_self hd₂.1.1 hd₂.1.2]
          exact congrArg (k / ·) h
    _ = B := by simp

/-- **Uniform trans-horizon approximation.** For `1 ≤ k ≤ (B+1)N` and `ε ≥ 0`,
`|τ_ε(k) - s_N(k; c_ε)| ≤ B (N+1)^{-ε}`. -/
theorem abs_divisorCoeff_sub_sieveSeq_le {ε : ℝ} (hε : 0 ≤ ε) {N B k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ (B + 1) * N) :
    |RHTower.pmPowerDampedDivisorCoeff ε k - sieveSeq N (pmPowerDampedRealWeight ε) k| ≤
      B * ((N : ℝ) + 1) ^ (-ε) := by
  rw [pmPowerDampedDivisorCoeff_sub_sieveSeq ε N hk1]
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  calc |∑ d ∈ k.divisors.filter (fun d => N < d), pmPowerDampedRealWeight ε d|
      ≤ ∑ d ∈ k.divisors.filter (fun d => N < d), ((N : ℝ) + 1) ^ (-ε) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
        have hNd : N < d := (mem_filter.mp hd).2
        have hdR : (N : ℝ) + 1 ≤ d := by exact_mod_cast hNd
        rw [pmPowerDampedRealWeight, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
        have hμ : |moebiusReal d| ≤ 1 := by
          unfold moebiusReal; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have hpow : (d : ℝ) ^ (-ε) ≤ ((N : ℝ) + 1) ^ (-ε) :=
          Real.rpow_le_rpow_of_nonpos hN1 hdR (by linarith)
        nlinarith [Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) d) (-ε)]
    _ = (k.divisors.filter (fun d => N < d)).card * ((N : ℝ) + 1) ^ (-ε) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ B * ((N : ℝ) + 1) ^ (-ε) := by
        gcongr
        exact_mod_cast card_divisors_gt_le hk

/-- The damped prefix energy is the Cesàro energy of `τ_ε` up to `(B+1)N δ(2+δ)`,
`δ = B(N+1)^{-ε}`. -/
theorem abs_sieveL2PrefixEnergy_pmPowerDamped_sub_le {ε : ℝ} (hε : 0 ≤ ε) (N B : ℕ) :
    |sieveL2PrefixEnergy N ((B + 1) * N) (pmPowerDampedRealWeight ε) -
        ∑ k ∈ Icc 1 ((B + 1) * N), RHTower.pmPowerDampedDivisorCoeff ε k ^ 2| ≤
      ((B + 1) * N : ℕ) * ((B * ((N : ℝ) + 1) ^ (-ε)) * (2 + B * ((N : ℝ) + 1) ^ (-ε))) := by
  set δ := (B : ℝ) * ((N : ℝ) + 1) ^ (-ε)
  have hδ : 0 ≤ δ := by positivity
  unfold sieveL2PrefixEnergy
  rw [← sum_sub_distrib]
  calc |∑ k ∈ Icc 1 ((B + 1) * N), (sieveSeq N (pmPowerDampedRealWeight ε) k ^ 2 -
        RHTower.pmPowerDampedDivisorCoeff ε k ^ 2)|
      ≤ ∑ k ∈ Icc 1 ((B + 1) * N), δ * (2 + δ) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
        obtain ⟨hk1, hkX⟩ := mem_Icc.mp hk
        set s := sieveSeq N (pmPowerDampedRealWeight ε) k
        set τ := RHTower.pmPowerDampedDivisorCoeff ε k
        have h1 : |τ - s| ≤ δ := abs_divisorCoeff_sub_sieveSeq_le hε hk1 hkX
        have hτ0 := RHTower.pmPowerDampedDivisorCoeff_nonneg hε k
        have hτ1 := RHTower.pmPowerDampedDivisorCoeff_le_one hε k
        have h2 : |s + τ| ≤ 2 + δ := by
          rw [abs_le] at h1 ⊢; constructor <;> linarith
        rw [show s ^ 2 - τ ^ 2 = (s + τ) * (s - τ) by ring, abs_mul, abs_sub_comm]
        calc |s + τ| * |τ - s| ≤ (2 + δ) * δ :=
              mul_le_mul h2 h1 (abs_nonneg _) (by linarith)
          _ = δ * (2 + δ) := by ring
    _ = ((B + 1) * N : ℕ) * (δ * (2 + δ)) := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp

/-- **Linear damped profile.** For `ε > 0`, `E_N((B+1)N; c_ε)/N → (B+1) E[τ_ε²]`. -/
theorem tendsto_sieveL2PrefixEnergy_pmPowerDamped_linear_horizon {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    Tendsto (fun N : ℕ => sieveL2PrefixEnergy N ((B + 1) * N) (pmPowerDampedRealWeight ε) / N)
      atTop (𝓝 ((B + 1) * RHTower.pmPowerDampedSecondDensity ε)) := by
  -- the Cesàro part
  have hX : Tendsto (fun N : ℕ => (((B + 1) * N : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_id.const_mul_atTop' (by omega : 0 < B + 1))
  have hmean := (RHTower.tendsto_pmPowerDampedDivisorCoeff_sq_mean hε).comp hX
  simp only [Function.comp_def, Nat.floor_natCast] at hmean
  have hces : Tendsto (fun N : ℕ =>
      (∑ k ∈ Icc 1 ((B + 1) * N), RHTower.pmPowerDampedDivisorCoeff ε k ^ 2) / N) atTop
      (𝓝 ((B + 1) * RHTower.pmPowerDampedSecondDensity ε)) := by
    refine ((hmean.const_mul ((B : ℝ) + 1))).congr' ?_ |>.trans (by rw [mul_comm])
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    push_cast
    field_simp
  -- the error part
  have hδ : Tendsto (fun N : ℕ => (B : ℝ) * ((N : ℝ) + 1) ^ (-ε)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop hε).comp
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    simpa using h.const_mul (B : ℝ)
  have herr : Tendsto (fun N : ℕ => ((B : ℝ) + 1) * ((B * ((N : ℝ) + 1) ^ (-ε)) *
      (2 + B * ((N : ℝ) + 1) ^ (-ε)))) atTop (𝓝 0) := by
    simpa using ((hδ.mul (hδ.const_add 2)).const_mul ((B : ℝ) + 1))
  have hdiff : Tendsto (fun N : ℕ =>
      sieveL2PrefixEnergy N ((B + 1) * N) (pmPowerDampedRealWeight ε) / N -
        (∑ k ∈ Icc 1 ((B + 1) * N), RHTower.pmPowerDampedDivisorCoeff ε k ^ 2) / N) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ herr
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hNR, div_le_iff₀ hNR]
    have h := abs_sieveL2PrefixEnergy_pmPowerDamped_sub_le hε.le N B
    push_cast at h
    linarith
  simpa using hdiff.add hces

/-- `E[τ_ε²] → 0` as `ε → 0⁺`. -/
theorem tendsto_pmPowerDampedSecondDensity_zero :
    Tendsto RHTower.pmPowerDampedSecondDensity (𝓝[>] 0) (𝓝 0) := by
  have h := RHTower.tendsto_pmPowerDampedSecondDensity_div_parameter.mul
    (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0))
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have : ε ≠ 0 := ne_of_gt hε
  simp only [id]
  field_simp

/-- **Band non-commutation.** In every band `B ≥ 1`, for all small dampings and all large horizons,
the damped trans-horizon prefix energy is strictly below the Möbius one. -/
theorem eventually_sieveL2PrefixEnergy_pmPowerDamped_lt_moebius {B : ℕ} (hB : 1 ≤ B) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      sieveL2PrefixEnergy N ((B + 1) * N) (pmPowerDampedRealWeight ε) <
        sieveL2PrefixEnergy N ((B + 1) * N) moebiusReal := by
  have hP : RHTower.Sieve.squarefreeDensity ≤ cofinalMobiusQuadraticProfile B :=
    squarefreeDensity_le_cofinalMobiusQuadraticProfile hB
  have hD : 0 < RHTower.Sieve.squarefreeDensity := by
    rw [RHTower.Sieve.squarefreeDensity_eq]; positivity
  have hsmall := ((tendsto_pmPowerDampedSecondDensity_zero.const_mul ((B : ℝ) + 1))).eventually
    (eventually_lt_nhds (show ((B : ℝ) + 1) * 0 < RHTower.Sieve.squarefreeDensity by simpa using hD))
  filter_upwards [hsmall, self_mem_nhdsWithin] with ε hε hpos
  have h1 := (tendsto_sieveL2PrefixEnergy_pmPowerDamped_linear_horizon hpos B).eventually
    (eventually_lt_nhds (show ((B : ℝ) + 1) * RHTower.pmPowerDampedSecondDensity ε <
      (((B : ℝ) + 1) * RHTower.pmPowerDampedSecondDensity ε + cofinalMobiusQuadraticProfile B) / 2 by
        linarith))
  have h2 := (tendsto_sieveL2PrefixEnergy_moebiusReal_linear_horizon B).eventually
    (eventually_gt_nhds (show (((B : ℝ) + 1) * RHTower.pmPowerDampedSecondDensity ε +
      cofinalMobiusQuadraticProfile B) / 2 < cofinalMobiusQuadraticProfile B by linarith))
  filter_upwards [h1, h2, eventually_gt_atTop 0] with N hN1 hN2 hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have := (div_lt_div_iff_of_pos_right hNR).mp (hN1.trans hN2)
  exact this

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics

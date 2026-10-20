import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedPrimitiveEnergyHalfThreshold

/-!
# The half-damping law

The Haar dissipation of the damped divisor function splits into its variance and its lag-one
autocorrelation,

`R(ε) = Σ_{e ≥ 2} (φ(e) - μ(e)) w_ε(e)² = V(ε) - A_ε(1)`,

and the autocorrelation is quadratically small, `|A_ε(1)| ≤ 16 E[τ_ε]² = O(ε²)`, while
`V(ε) ~ ε/2`. Hence

`R(ε)/ε → 1/2`,   `R(ε)/V(ε) → 1`,

and, through the exact linear rate of the damped defect, the trans-horizon defect on the window
`(B+1)N` has slope

`lim_{ε→0} (1/ε) lim_{N→∞} D̃_N((B+1)N; c_ε)/N = -(B+1)/2`:

at small damping every unit of window dissipates half the damping parameter.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- `Σ_e μ(e) w_ε(e)²` converges absolutely. -/
private theorem summable_moebius_mul_dampedRamanujanCoeff_sq {ε : ℝ} (hε : 0 < ε) :
    Summable (fun e : ℕ => moebiusReal e * dampedRamanujanCoeff ε e ^ 2) := by
  obtain ⟨hs, -⟩ := summable_sqfreeTotientInv_div_totient
  refine Summable.of_norm_bounded
    (hs.mul_left ((RHTower.pmPowerDampedDivisorDensity ε).re ^ 2)) fun e => ?_
  have hμ : |moebiusReal e| ≤ 1 := by
    unfold moebiusReal; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (dampedRamanujanCoeff ε e))]
  calc |moebiusReal e| * dampedRamanujanCoeff ε e ^ 2 ≤ 1 * dampedRamanujanCoeff ε e ^ 2 :=
        mul_le_mul_of_nonneg_right hμ (sq_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact dampedRamanujanCoeff_sq_le hε e

/-- **Dissipation = variance − lag-one autocorrelation.** `R(ε) = V(ε) - A_ε(1)`. -/
theorem dampedDissipationRate_eq_variance_sub_autocorrelation {ε : ℝ} (hε : 0 < ε) :
    dampedDissipationRate ε =
      RHTower.pmPowerDampedDivisorVariance ε - dampedAutocorrelation ε 1 := by
  have hs := summable_moebius_mul_dampedRamanujanCoeff_sq hε
  set g : ℕ → ℝ := fun e =>
    if 2 ≤ e then ramanujanLagWeight 1 e * dampedRamanujanCoeff ε e ^ 2 else 0
  have hsA : Summable g := by
    refine Summable.of_norm_bounded hs.norm fun e => ?_
    simp only [g]
    split_ifs
    · rw [ramanujanLagWeight_one_left]; rfl
    · rw [norm_zero]; exact norm_nonneg _
  have h1 : dampedBezoutLimit ε = dampedRamanujanCoeff ε 1 ^ 2 +
      ∑' i, moebiusReal (i + 2) * dampedRamanujanCoeff ε (i + 2) ^ 2 := by
    unfold dampedBezoutLimit
    rw [← hs.sum_add_tsum_nat_add 2]
    simp [Finset.sum_range_succ, moebiusReal]
  have h2 : dampedAutocorrelation ε 1 =
      ∑' i, moebiusReal (i + 2) * dampedRamanujanCoeff ε (i + 2) ^ 2 := by
    unfold dampedAutocorrelation
    rw [← hsA.sum_add_tsum_nat_add 2]
    simp only [g, Finset.sum_range_succ, Finset.sum_range_zero, show ¬ 2 ≤ 0 by omega,
      show ¬ 2 ≤ 1 by omega, if_false, zero_add, show ∀ i : ℕ, 2 ≤ i + 2 from fun i => by omega,
      if_true, ramanujanLagWeight_one_left]
    rfl
  rw [dampedDissipationRate, h1, ← h2, RHTower.pmPowerDampedDivisorVariance,
    ← dampedRamanujanCoeff_one hε]
  ring

/-- **Half-damping law.** `R(ε)/ε → 1/2` as `ε → 0⁺`. -/
theorem tendsto_dampedDissipationRate_div_parameter :
    Tendsto (fun ε : ℝ => dampedDissipationRate ε / ε) (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have hV := RHTower.tendsto_pmPowerDampedDivisorVariance_div_parameter
  have hρ := RHTower.tendsto_pmPowerDampedDivisorDensity_re_div_parameter
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  -- the autocorrelation part is `O(E[τ_ε]²) = O(ε²)`
  have hA : Tendsto (fun ε : ℝ => dampedAutocorrelation ε 1 / ε) (𝓝[>] 0) (𝓝 0) := by
    have hb : Tendsto (fun ε : ℝ => 16 * (((RHTower.pmPowerDampedDivisorDensity ε).re / ε) ^ 2 * ε))
        (𝓝[>] 0) (𝓝 0) := by
      simpa using ((hρ.pow 2).mul he).const_mul 16
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : (0 : ℝ) < ε := hε
    have hbd := abs_dampedAutocorrelation_le hε0 (h := 1) le_rfl
    simp only [Nat.divisors_one, sum_singleton, Nat.cast_one, mul_one] at hbd
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hε0, div_le_iff₀ hε0]
    calc |dampedAutocorrelation ε 1| ≤ 16 * (RHTower.pmPowerDampedDivisorDensity ε).re ^ 2 := hbd
      _ = 16 * (((RHTower.pmPowerDampedDivisorDensity ε).re / ε) ^ 2 * ε) * ε := by
          field_simp
  have h := hV.sub hA
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [dampedDissipationRate_eq_variance_sub_autocorrelation hε, sub_div]

/-- **Dissipation equals variance at small damping.** `R(ε)/V(ε) → 1`. -/
theorem tendsto_dampedDissipationRate_div_variance :
    Tendsto (fun ε : ℝ => dampedDissipationRate ε / RHTower.pmPowerDampedDivisorVariance ε)
      (𝓝[>] 0) (𝓝 1) := by
  have h := (tendsto_dampedAutocorrelation_div_variance (h := 1) le_rfl).const_sub 1
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hV : 0 < RHTower.pmPowerDampedDivisorVariance ε := RHTower.pmPowerDampedDivisorVariance_pos hε
  rw [dampedDissipationRate_eq_variance_sub_autocorrelation hε, sub_div, div_self hV.ne']

/-- **The trans-horizon defect slope at small damping.** The exact linear rate of the damped
defect on the window `(B+1)N`, divided by the damping, tends to `-(B+1)/2`:
`lim_{ε→0} (1/ε) lim_N D̃_N((B+1)N; c_ε)/N = -(B+1)/2`. -/
theorem tendsto_linear_defect_rate_div_parameter (B : ℕ) :
    Tendsto (fun ε : ℝ => -((B : ℝ) + 1) * dampedDissipationRate ε / ε) (𝓝[>] 0)
      (𝓝 (-((B : ℝ) + 1) / 2)) := by
  have h := tendsto_dampedDissipationRate_div_parameter.const_mul (-((B : ℝ) + 1))
  rw [show -((B : ℝ) + 1) * (1 / 2) = -((B : ℝ) + 1) / 2 by ring] at h
  refine h.congr fun ε => ?_
  ring

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics

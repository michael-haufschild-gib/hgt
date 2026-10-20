import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedVarianceAndDissipationSecondOrderLaw
import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedPrimeHorizonCrossoverScale
import GaloisForLFunctions.RHTower.Sieve.MoebiusHarmonicLogRate

/-!
# The damped crossover: Euler's constant and an additive window

The damped prime slope `λ_ε(p) = p^{-ε} - 2 H_ε(p-1)` changes sign at the crossover scale
`Λ(ε) = log(1/(2ρ_ε))/ε`, `ρ_ε = 1/ζ(1+ε)`, which is known to first order,
`ε Λ(ε) = log(1/(2ε)) + o(1)`, with a multiplicative window `(1 ± δ) Λ(ε)`. Two refinements:

* **Location.** `ρ_ε = ε - γ ε² + o(ε²)` (from `ζ(1+s) = 1/s + γ + o(1)`), hence
  `Λ(ε) = log(1/(2ε))/ε + γ + o(1)`: the crossover prime is `e^{γ + o(1)} (2ε)^{-1/ε}`.
* **Window.** At the crossover `log p ≍ ε^{-1} log(1/ε)`, and the Möbius harmonic sums decay like
  `(log t)^{-3}`, so the Abel error `|ρ_ε - H_ε(p-1)| ≤ 2 sup_{t ≥ p-1} |m(t)| p^{-ε}` is
  `O(ε³ p^{-ε})`, far below the gap `|p^{-ε} - 2ρ_ε| ≥ ε² · 2ρ_ε` that holds once `log p` leaves
  `Λ(ε) ± ε`. Hence the slope is positive for `log p ≤ Λ(ε) - ε` and negative for
  `log p ≥ Λ(ε) + ε`, for all large primes and all small damping.

Together: past one absolute threshold, the prime horizon `p` injects energy when
`p ≤ e^{γ-δ} (2ε)^{-1/ε}` and dissipates when `p ≥ e^{γ+δ} (2ε)^{-1/ε}`.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open RHTower RHTower.Sieve

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Second-order location of the crossover -/

/-- **The density to second order.** `ρ_ε = ε - γ ε² + o(ε²)`. -/
theorem tendsto_pmPowerDampedDivisorDensity_re_second_order :
    Tendsto (fun ε : ℝ => ((pmPowerDampedDivisorDensity ε).re - ε) / ε ^ 2) (𝓝[>] 0)
      (𝓝 (-Real.eulerMascheroniConstant)) := by
  have hu := tendsto_riemannZeta_one_add_sub_inv (c := 1) one_pos
  simp only [one_mul] at hu
  have he : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Complex.continuous_ofReal.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  set γ : ℂ := (Real.eulerMascheroniConstant : ℂ)
  have hc := hu.neg.div ((he.mul hu).const_add 1) (by simp)
  rw [zero_mul, add_zero, div_one] at hc
  have hr := (Complex.continuous_re.tendsto _).comp hc
  rw [Complex.neg_re, Complex.ofReal_re] at hr
  refine hr.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : (0 : ℝ) < ε := hε
  have hεc : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε0.ne'
  have hZ : riemannZeta (1 + (ε : ℂ)) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  have hρ : ((pmPowerDampedDivisorDensity ε).re : ℂ) = 1 / riemannZeta (1 + (ε : ℂ)) := by
    rw [← pmPowerDampedDivisorDensity_eq_ofReal_re hε0]; rfl
  have key : -(riemannZeta (1 + (ε : ℂ)) - 1 / (ε : ℂ)) /
      (1 + (ε : ℂ) * (riemannZeta (1 + (ε : ℂ)) - 1 / (ε : ℂ))) =
      ((((pmPowerDampedDivisorDensity ε).re - ε) / ε ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [hρ]
    field_simp
    ring
  simp only [Function.comp_apply, Pi.div_apply]
  rw [key, Complex.ofReal_re]

/-- **Euler's constant in the crossover.** `Λ(ε) = log(1/(2ε))/ε + γ + o(1)`. -/
theorem tendsto_dampedCrossoverScale_sub_main :
    Tendsto (fun ε : ℝ => dampedCrossoverScale ε - Real.log (1 / (2 * ε)) / ε) (𝓝[>] 0)
      (𝓝 Real.eulerMascheroniConstant) := by
  have hr := tendsto_pmPowerDampedDivisorDensity_re_second_order
  have hq := tendsto_pmPowerDampedDivisorDensity_re_div_parameter
  -- `(ρ-ε)/(ερ) ≤ log(ρ/ε)/ε ≤ (ρ-ε)/ε²`, and both bounds tend to `-γ`
  have hlo : Tendsto (fun ε : ℝ => ((pmPowerDampedDivisorDensity ε).re - ε) / ε ^ 2 /
      ((pmPowerDampedDivisorDensity ε).re / ε)) (𝓝[>] 0) (𝓝 (-Real.eulerMascheroniConstant)) := by
    have h := hr.div hq one_ne_zero
    rw [div_one] at h
    exact h
  have hmid : Tendsto (fun ε : ℝ => Real.log ((pmPowerDampedDivisorDensity ε).re / ε) / ε)
      (𝓝[>] 0) (𝓝 (-Real.eulerMascheroniConstant)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hr ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : (0 : ℝ) < ε := hε
      have hρ := RHTower.pmPowerDampedDivisorDensity_re_pos hε0
      have h := Real.one_sub_inv_le_log_of_pos (div_pos hρ hε0)
      have : 1 - ((pmPowerDampedDivisorDensity ε).re / ε)⁻¹ =
          ((pmPowerDampedDivisorDensity ε).re - ε) / (pmPowerDampedDivisorDensity ε).re := by
        field_simp
      rw [this] at h
      have e1 : ((pmPowerDampedDivisorDensity ε).re - ε) / ε ^ 2 /
          ((pmPowerDampedDivisorDensity ε).re / ε) =
          ((pmPowerDampedDivisorDensity ε).re - ε) / (pmPowerDampedDivisorDensity ε).re / ε := by
        field_simp
      rw [e1]
      exact div_le_div_of_nonneg_right h hε0.le
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : (0 : ℝ) < ε := hε
      have hρ := RHTower.pmPowerDampedDivisorDensity_re_pos hε0
      have h := Real.log_le_sub_one_of_pos (div_pos hρ hε0)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (pmPowerDampedDivisorDensity ε).re / ε - 1 =
          ((pmPowerDampedDivisorDensity ε).re - ε) / ε := by field_simp
      rw [this, le_div_iff₀ hε0] at h
      nlinarith [mul_le_mul_of_nonneg_right h hε0.le]
  have h := hmid.neg
  rw [neg_neg] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : (0 : ℝ) < ε := hε
  have hρ := RHTower.pmPowerDampedDivisorDensity_re_pos hε0
  unfold dampedCrossoverScale
  rw [Real.log_div hρ.ne' hε0.ne', Real.log_mul two_ne_zero hρ.ne', one_div, Real.log_inv,
    Real.log_mul two_ne_zero hε0.ne']
  field_simp
  ring

/-- **The crossover prime.** `e^{Λ(ε)} (2ε)^{1/ε} → e^γ`. -/
theorem tendsto_exp_dampedCrossoverScale_mul :
    Tendsto (fun ε : ℝ => Real.exp (dampedCrossoverScale ε) * (2 * ε) ^ (1 / ε)) (𝓝[>] 0)
      (𝓝 (Real.exp Real.eulerMascheroniConstant)) := by
  refine ((Real.continuous_exp.tendsto _).comp tendsto_dampedCrossoverScale_sub_main).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : (0 : ℝ) < ε := hε
  simp only [Function.comp_apply]
  rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_add, one_div, Real.log_inv]
  congr 1
  ring

/-! ### The Möbius harmonic sums at rate `(log t)^{-3}` -/

private theorem finiteHarmonicSum_moebiusReal_eq_deninger (t : ℕ) :
    finiteHarmonicSum t moebiusReal = deningerHarmonicPartial t := by
  unfold finiteHarmonicSum deningerHarmonicPartial
  change ∑ n ∈ Finset.Ico 1 (t + 1), moebiusReal n / n =
    ∑ n ∈ Finset.range (t + 1), ((moebius n : ℤ) : ℝ) / (n : ℝ)
  rw [Finset.sum_Ico_eq_sub _ (by omega : 1 ≤ t + 1)]
  simp [moebiusReal]

/-- `|m(t)| ≤ C (log t)^{-3}` at all large `t`. -/
private theorem exists_abs_finiteHarmonicSum_moebius_le_log_cube :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ K : ℕ, ∀ t, K ≤ t →
      |finiteHarmonicSum t moebiusReal| ≤ C / Real.log t ^ 3 := by
  obtain ⟨B, hB, h⟩ := exists_abs_deningerHarmonicPartial_log_rate
  obtain ⟨K, hK⟩ := eventually_atTop.mp (h.and (eventually_ge_atTop 3))
  refine ⟨3 * B, by positivity, K, fun t ht => ?_⟩
  obtain ⟨hb, ht3⟩ := hK t ht
  have hlog : 1 ≤ Real.log t := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have h3 : (3 : ℝ) ≤ t := by exact_mod_cast ht3
    linarith [Real.exp_one_lt_d9]
  have hl3 : 0 < Real.log t ^ 3 := by positivity
  have hl4 : Real.log t ^ 3 ≤ Real.log t ^ 4 := pow_le_pow_right₀ hlog (by norm_num)
  rw [finiteHarmonicSum_moebiusReal_eq_deninger]
  refine hb.trans ?_
  calc 2 * B / Real.log t ^ 4 + B / (3 * Real.log t ^ 3)
      ≤ 2 * B / Real.log t ^ 3 + B / Real.log t ^ 3 := by
        gcongr
        · linarith
    _ = 3 * B / Real.log t ^ 3 := by ring

/-! ### The additive window -/

/-- **Additive crossover window.** There is an absolute `P₀` such that for all small `ε > 0` and
primes `p ≥ P₀`: the slope is positive for `log p ≤ Λ(ε) - ε` and negative for
`log p ≥ Λ(ε) + ε`. -/
theorem dampedPrimeSlope_additive_crossover :
    ∃ P₀ : ℕ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p : ℕ, P₀ ≤ p → p.Prime →
      (Real.log p ≤ dampedCrossoverScale ε - ε → 0 < dampedPrimeSlope ε p) ∧
      (dampedCrossoverScale ε + ε ≤ Real.log p → dampedPrimeSlope ε p < 0) := by
  obtain ⟨C, hC, K, hK⟩ := exists_abs_finiteHarmonicSum_moebius_le_log_cube
  obtain ⟨T, hT⟩ := eventually_atTop.mp (tendsto_finiteHarmonicSum_moebiusReal_zero.eventually
    (Metric.closedBall_mem_nhds (0 : ℝ) (show (0 : ℝ) < 1 / 8 by norm_num)))
  refine ⟨T + K + 4, ?_⟩
  have hε₁ : (0 : ℝ) < 1 / (64 * C + 2) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hε₁, tendsto_pmPowerDampedDivisorDensity_re_zero.eventually
    (eventually_lt_nhds (show (0 : ℝ) < Real.exp (-1) / 6 by positivity))]
    with ε hε hρsmall p hpP hp
  obtain ⟨hε0, hε1⟩ := hε
  have hεC : 64 * C * ε < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hε1; nlinarith
  have hεh : ε ≤ 1 / 2 := by
    have : 1 / (64 * C + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  set ρ := (pmPowerDampedDivisorDensity ε).re
  have hρ : 0 < ρ := RHTower.pmPowerDampedDivisorDensity_re_pos hε0
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  set x := (p : ℝ) ^ (-ε)
  have hx0 : 0 < x := Real.rpow_pos_of_pos hp0 _
  have hpow : x = Real.exp (-(ε * Real.log p)) := by
    simp only [x]; rw [Real.rpow_def_of_pos hp0]; ring_nf
  set u := Real.log (2 * ρ)
  have hexpu : Real.exp u = 2 * ρ := Real.exp_log (by positivity)
  have hscale : ε * dampedCrossoverScale ε = -u := by
    unfold dampedCrossoverScale; field_simp; rfl
  -- the coarse Abel bound `|m| ≤ 1/8` past `p - 1`
  have h8 : |ρ - finiteHarmonicSum (p - 1) (pmPowerDampedRealWeight ε)| ≤ 2 * (1 / 8) * x := by
    have h := abs_pmPowerDampedDivisorDensity_re_sub_le hε0 (n := p - 1) (η := 1 / 8)
      fun t ht => by
        have := hT t (by omega)
        simpa [Metric.mem_closedBall, Real.dist_eq] using this
    rwa [show p - 1 + 1 = p by have := hp.one_le; omega] at h
  -- the fine Abel bound `|m| ≤ 8Cε³` once `log p ≥ 1/ε`
  have hfine : 1 / ε ≤ Real.log p →
      |ρ - finiteHarmonicSum (p - 1) (pmPowerDampedRealWeight ε)| ≤ 2 * (8 * C * ε ^ 3) * x := by
    intro hlp
    have h := abs_pmPowerDampedDivisorDensity_re_sub_le hε0 (n := p - 1) (η := 8 * C * ε ^ 3)
      fun t ht => by
        have htK : K ≤ t := by omega
        have ht1 : (p : ℝ) - 1 ≤ t := by
          have : ((p - 1 : ℕ) : ℝ) ≤ t := by exact_mod_cast ht
          rwa [Nat.cast_sub hp.one_le, Nat.cast_one] at this
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
        have hlt : Real.log p - 1 ≤ Real.log t := by
          have hhalf : (p : ℝ) / 2 ≤ t := by linarith
          have := Real.log_le_log (by positivity) hhalf
          rw [Real.log_div hp0.ne' two_ne_zero] at this
          linarith [Real.log_two_lt_d9]
        have hlt' : 1 / (2 * ε) ≤ Real.log t := by
          have : 1 / (2 * ε) ≤ 1 / ε - 1 := by
            rw [div_le_iff₀ (by positivity)]
            field_simp
            nlinarith
          linarith
        have hpos : 0 < 1 / (2 * ε) := by positivity
        calc |finiteHarmonicSum t moebiusReal| ≤ C / Real.log t ^ 3 := hK t htK
          _ ≤ C / (1 / (2 * ε)) ^ 3 :=
              div_le_div_of_nonneg_left hC (by positivity) (pow_le_pow_left₀ hpos.le hlt' 3)
          _ = 8 * C * ε ^ 3 := by field_simp; ring
    rwa [show p - 1 + 1 = p by have := hp.one_le; omega] at h
  -- `log p ≥ 1/ε` whenever `x < 6ρ`
  have hlarge : x < 6 * ρ → 1 / ε ≤ Real.log p := by
    intro hx
    have h1 : Real.log (6 * ρ) ≤ -1 := by
      rw [Real.log_le_iff_le_exp (by positivity)]; linarith
    have h2 : -(ε * Real.log p) < Real.log (6 * ρ) := by
      rw [hpow] at hx
      exact (Real.exp_lt_exp.mp (by rw [Real.exp_log (by positivity)]; exact hx))
    rw [div_le_iff₀ hε0]; nlinarith
  have hε2 : 0 < ε ^ 2 := by positivity
  have hgap : 32 * C * ε ^ 3 * (1 + ε ^ 2) < ε ^ 2 := by
    have : ε ^ 2 ≤ 1 := by nlinarith
    have : 32 * C * ε * (1 + ε ^ 2) < 1 := by nlinarith
    nlinarith
  constructor
  · intro hle
    -- `x ≥ 2ρ e^{ε²} ≥ 2ρ (1 + ε²)`
    have hx : 2 * ρ * (1 + ε ^ 2) ≤ x := by
      have h1 : u + ε ^ 2 ≤ -(ε * Real.log p) := by
        have := mul_le_mul_of_nonneg_left hle hε0.le
        nlinarith
      rw [hpow]
      calc 2 * ρ * (1 + ε ^ 2) ≤ Real.exp u * Real.exp (ε ^ 2) := by
            rw [hexpu]; nlinarith [Real.add_one_le_exp (ε ^ 2)]
        _ = Real.exp (u + ε ^ 2) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr h1
    unfold dampedPrimeSlope
    by_cases h6 : 6 * ρ ≤ x
    · have := abs_le.mp h8; nlinarith
    · have hb := abs_le.mp (hfine (hlarge (not_le.mp h6)))
      nlinarith
  · intro hge
    -- `x ≤ 2ρ e^{-ε²}`, so `x (1 + ε²) ≤ 2ρ`
    have hx : x * (1 + ε ^ 2) ≤ 2 * ρ := by
      have h1 : -(ε * Real.log p) ≤ u - ε ^ 2 := by
        have := mul_le_mul_of_nonneg_left hge hε0.le
        nlinarith
      have hxe : x ≤ Real.exp (u - ε ^ 2) := by rw [hpow]; exact Real.exp_le_exp.mpr h1
      have he : Real.exp (u - ε ^ 2) * (1 + ε ^ 2) ≤ 2 * ρ := by
        rw [Real.exp_sub, hexpu, div_mul_eq_mul_div, div_le_iff₀ (Real.exp_pos _)]
        nlinarith [Real.add_one_le_exp (ε ^ 2)]
      nlinarith
    have hlp : 1 / ε ≤ Real.log p := by
      apply hlarge
      nlinarith
    have hb := abs_le.mp (hfine hlp)
    unfold dampedPrimeSlope
    nlinarith

/-- **The explicit crossover.** For every `δ > 0` there is an absolute `P₀` such that for all small
`ε > 0` and primes `p ≥ P₀`: the slope is positive for `p ≤ e^{γ-δ} (2ε)^{-1/ε}` and negative for
`p ≥ e^{γ+δ} (2ε)^{-1/ε}`. -/
theorem dampedPrimeSlope_explicit_crossover {δ : ℝ} (hδ : 0 < δ) :
    ∃ P₀ : ℕ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p : ℕ, P₀ ≤ p → p.Prime →
      (Real.log p ≤ Real.log (1 / (2 * ε)) / ε + Real.eulerMascheroniConstant - δ →
        0 < dampedPrimeSlope ε p) ∧
      (Real.log (1 / (2 * ε)) / ε + Real.eulerMascheroniConstant + δ ≤ Real.log p →
        dampedPrimeSlope ε p < 0) := by
  obtain ⟨P₀, hP₀⟩ := dampedPrimeSlope_additive_crossover
  refine ⟨P₀, ?_⟩
  have hloc := tendsto_dampedCrossoverScale_sub_main.eventually
    (Metric.ball_mem_nhds Real.eulerMascheroniConstant (show 0 < δ / 2 by positivity))
  filter_upwards [hP₀, hloc, Ioo_mem_nhdsGT (show (0 : ℝ) < δ / 2 by positivity)]
    with ε hε hl hεδ p hpP hp
  rw [Real.dist_eq, abs_lt] at hl
  obtain ⟨-, hεδ⟩ := hεδ
  constructor
  · intro hle; exact (hε p hpP hp).1 (by linarith)
  · intro hge; exact (hε p hpP hp).2 (by linarith)

/-- **Energy steps in the additive window.** Past one absolute `P₀`, for all small `ε > 0`: a prime
horizon with `log p ≤ Λ(ε) - ε` raises, and one with `log p ≥ Λ(ε) + ε` lowers, the damped prefix
energy at all large prefixes. -/
theorem pmPowerDamped_prime_step_additive_crossover :
    ∃ P₀ : ℕ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p : ℕ, P₀ ≤ p → p.Prime →
      (Real.log p ≤ dampedCrossoverScale ε - ε → ∀ᶠ M in atTop,
        sieveL2PrefixEnergy (p - 1) M (pmPowerDampedRealWeight ε) <
          sieveL2PrefixEnergy p M (pmPowerDampedRealWeight ε)) ∧
      (dampedCrossoverScale ε + ε ≤ Real.log p → ∀ᶠ M in atTop,
        sieveL2PrefixEnergy p M (pmPowerDampedRealWeight ε) <
          sieveL2PrefixEnergy (p - 1) M (pmPowerDampedRealWeight ε)) := by
  obtain ⟨P₀, hP₀⟩ := dampedPrimeSlope_additive_crossover
  refine ⟨P₀, ?_⟩
  filter_upwards [hP₀, self_mem_nhdsWithin] with ε hε hεpos p hpP hp
  have hε0 : (0 : ℝ) ≤ ε := le_of_lt hεpos
  have hB : Tendsto (fun M : ℕ => ((M / p : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (Nat.tendsto_div_const_atTop hp.ne_zero)
  constructor
  · intro hle
    have hlam := (hε p hpP hp).1 hle
    filter_upwards [(hB.atTop_mul_const hlam).eventually_gt_atTop (2 * ((p : ℝ) - 1))] with M hM
    exact pmPowerDamped_prime_step_pos_of_slope hp hε0 hM
  · intro hge
    have hlam := (hε p hpP hp).2 hge
    filter_upwards [(hB.atTop_mul_const (neg_pos.mpr hlam)).eventually_gt_atTop
      (2 * ((p : ℝ) - 1))] with M hM
    exact pmPowerDamped_prime_step_neg_of_slope hp hε0 (by linarith)

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics

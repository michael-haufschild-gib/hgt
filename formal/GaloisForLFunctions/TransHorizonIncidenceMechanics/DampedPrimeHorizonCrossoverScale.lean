import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedPrimeHorizonSlopeReversalAndCrossover
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusSmallDampingVariance

/-!
# The crossover scale of damped prime horizons

The damped prime slope `λ_ε(p) = p^{-ε} - 2 H_ε(p-1)`, `H_ε(x) = Σ_{d≤x} μ(d) d^{-1-ε}`, decides
whether the prime horizon `p` injects or dissipates prefix energy at large ratios `⌊M/p⌋`.
Abel summation against the Möbius harmonic sums `m(t) = Σ_{d≤t} μ(d)/d` gives

`|ρ_ε - H_ε(n)| ≤ 2 sup_{t≥n} |m(t)| · (n+1)^{-ε}`,  `ρ_ε = Σ_d μ(d) d^{-1-ε} = 1/ζ(1+ε)`,

so `H_ε(p-1)` agrees with its limit up to `o(p^{-ε})`, uniformly in the damping, because
`m(t) → 0`. Hence the sign of `λ_ε(p)` is the sign of `p^{-ε} - 2ρ_ε`, and with the
**crossover scale** `Λ(ε) = log(1/(2ρ_ε))/ε` there is one absolute threshold `P₀` such that for
all small `ε > 0` and all primes `p ≥ P₀`:

* `log p ≤ (1-δ) Λ(ε)`: the slope is positive and the horizon injects energy;
* `log p ≥ (1+δ) Λ(ε)`: the slope is negative and the horizon dissipates energy.

Since `ρ_ε/ε → 1`, `ε Λ(ε) = log(1/(2ε)) + o(1)`: the damped observer behaves like the Möbius
observer (injecting at primes) up to horizons `exp((1+o(1)) log(1/(2ε))/ε)` and dissipates
beyond. The receivers at fixed small damping live beyond this scale.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The damped harmonic sums converge to `ρ_ε` at rate `o(n^{-ε})` -/

private theorem finiteHarmonicSum_succ (t : ℕ) (c : ℕ → ℝ) :
    finiteHarmonicSum (t + 1) c = finiteHarmonicSum t c + c (t + 1) / ((t + 1 : ℕ) : ℝ) := by
  unfold finiteHarmonicSum
  rw [sum_Icc_succ_top (by omega)]

private theorem finiteHarmonicSum_eq_sum_range (N : ℕ) (c : ℕ → ℝ) :
    finiteHarmonicSum N c = ∑ i ∈ range (N + 1), c i / (i : ℝ) := by
  induction N with
  | zero => simp [finiteHarmonicSum]
  | succ N ih => rw [finiteHarmonicSum_succ, ih, Finset.sum_range_succ _ (N + 1)]

/-- `Σ_{d≥1} μ(d) d^{-1-ε} = ρ_ε` as a real series. -/
theorem hasSum_pmPowerDampedRealWeight_div {ε : ℝ} (hε : 0 < ε) :
    HasSum (fun n : ℕ => pmPowerDampedRealWeight ε n / n) (pmPowerDampedDivisorDensity ε).re := by
  have h := (summable_pmPowerDampedDivisorDensity_terms hε).hasSum
  rw [← pmPowerDampedDivisorDensity_eq_tsum hε] at h
  convert Complex.hasSum_re h using 1
  funext n
  unfold pmPowerDampedMobiusCoeff pmPowerDampedRealWeight moebiusReal
  rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by simp, ← Complex.ofReal_div, Complex.ofReal_re]

theorem tendsto_finiteHarmonicSum_pmPowerDamped {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ => finiteHarmonicSum N (pmPowerDampedRealWeight ε)) atTop
      (𝓝 (pmPowerDampedDivisorDensity ε).re) := by
  have h := (hasSum_pmPowerDampedRealWeight_div hε).tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)
  refine h.congr fun N => ?_
  simp only [Function.comp, finiteHarmonicSum_eq_sum_range]

/-- Abel summation of the damped harmonic sum against the Möbius harmonic sums `A = m`. -/
private theorem harmonic_abel (ε : ℝ) (n k : ℕ) :
    finiteHarmonicSum (n + 1 + k) (pmPowerDampedRealWeight ε) -
        finiteHarmonicSum n (pmPowerDampedRealWeight ε) =
      finiteHarmonicSum (n + 1 + k) moebiusReal * ((n + 1 + k : ℕ) : ℝ) ^ (-ε) -
        finiteHarmonicSum n moebiusReal * ((n + 1 : ℕ) : ℝ) ^ (-ε) +
        ∑ i ∈ range k, finiteHarmonicSum (n + 1 + i) moebiusReal *
          (((n + 1 + i : ℕ) : ℝ) ^ (-ε) - ((n + 1 + i + 1 : ℕ) : ℝ) ^ (-ε)) := by
  induction k with
  | zero =>
    simp only [add_zero, range_zero, sum_empty]
    rw [finiteHarmonicSum_succ, finiteHarmonicSum_succ]
    unfold pmPowerDampedRealWeight
    ring
  | succ k ih =>
    rw [show n + 1 + (k + 1) = n + 1 + k + 1 by ring, finiteHarmonicSum_succ,
      finiteHarmonicSum_succ (n + 1 + k) moebiusReal, Finset.sum_range_succ]
    unfold pmPowerDampedRealWeight at ih ⊢
    linear_combination ih

/-- **Abel tail bound.** If `|m(t)| ≤ η` for all `t ≥ n`, then
`|H_ε(n + 1 + k) - H_ε(n)| ≤ 2 η (n+1)^{-ε}` for every `k` and every `ε ≥ 0`. -/
theorem abs_finiteHarmonicSum_pmPowerDamped_sub_le {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} {η : ℝ}
    (hη : ∀ t, n ≤ t → |finiteHarmonicSum t moebiusReal| ≤ η) (k : ℕ) :
    |finiteHarmonicSum (n + 1 + k) (pmPowerDampedRealWeight ε) -
        finiteHarmonicSum n (pmPowerDampedRealWeight ε)| ≤ 2 * η * ((n + 1 : ℕ) : ℝ) ^ (-ε) := by
  set f : ℕ → ℝ := fun i => ((n + 1 + i : ℕ) : ℝ) ^ (-ε)
  have hf_anti : ∀ i, f (i + 1) ≤ f i := fun i =>
    Real.rpow_le_rpow_of_nonpos (by positivity) (by push_cast; linarith) (by linarith)
  have hf_nn : ∀ i, 0 ≤ f i := fun i => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hf0 : f 0 = ((n + 1 : ℕ) : ℝ) ^ (-ε) := by simp [f]
  have habel := harmonic_abel ε n k
  rw [habel]
  have h1 : |finiteHarmonicSum (n + 1 + k) moebiusReal * ((n + 1 + k : ℕ) : ℝ) ^ (-ε)| ≤ η * f k := by
    rw [abs_mul, abs_of_nonneg (hf_nn k)]
    exact mul_le_mul_of_nonneg_right (hη _ (by omega)) (hf_nn k)
  have h2 : |finiteHarmonicSum n moebiusReal * ((n + 1 : ℕ) : ℝ) ^ (-ε)| ≤ η * f 0 := by
    rw [hf0, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact mul_le_mul_of_nonneg_right (hη n le_rfl) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have h3 : |∑ i ∈ range k, finiteHarmonicSum (n + 1 + i) moebiusReal *
      (((n + 1 + i : ℕ) : ℝ) ^ (-ε) - ((n + 1 + i + 1 : ℕ) : ℝ) ^ (-ε))| ≤ η * (f 0 - f k) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [← sum_range_sub' f k, mul_sum]
    refine sum_le_sum fun i _ => ?_
    have hfi : ((n + 1 + i : ℕ) : ℝ) ^ (-ε) - ((n + 1 + i + 1 : ℕ) : ℝ) ^ (-ε) = f i - f (i + 1) := by
      simp only [f]; ring_nf
    rw [hfi, abs_mul, abs_of_nonneg (sub_nonneg.mpr (hf_anti i))]
    exact mul_le_mul_of_nonneg_right (hη _ (by omega)) (sub_nonneg.mpr (hf_anti i))
  have hk : ((n + 1 + k : ℕ) : ℝ) ^ (-ε) = f k := rfl
  rw [← hf0]
  calc _ ≤ |finiteHarmonicSum (n + 1 + k) moebiusReal * ((n + 1 + k : ℕ) : ℝ) ^ (-ε) -
          finiteHarmonicSum n moebiusReal * ((n + 1 : ℕ) : ℝ) ^ (-ε)| +
        |∑ i ∈ range k, finiteHarmonicSum (n + 1 + i) moebiusReal *
          (((n + 1 + i : ℕ) : ℝ) ^ (-ε) - ((n + 1 + i + 1 : ℕ) : ℝ) ^ (-ε))| := abs_add_le _ _
    _ ≤ (η * f k + η * f 0) + η * (f 0 - f k) := add_le_add ((abs_sub _ _).trans (add_le_add h1 h2)) h3
    _ = 2 * η * f 0 := by ring

/-- **Uniform rate to the limit.** If `|m(t)| ≤ η` for `t ≥ n`, then `|ρ_ε - H_ε(n)| ≤ 2η(n+1)^{-ε}`. -/
theorem abs_pmPowerDampedDivisorDensity_re_sub_le {ε : ℝ} (hε : 0 < ε) {n : ℕ} {η : ℝ}
    (hη : ∀ t, n ≤ t → |finiteHarmonicSum t moebiusReal| ≤ η) :
    |(pmPowerDampedDivisorDensity ε).re - finiteHarmonicSum n (pmPowerDampedRealWeight ε)| ≤
      2 * η * ((n + 1 : ℕ) : ℝ) ^ (-ε) := by
  have hlim := ((tendsto_finiteHarmonicSum_pmPowerDamped hε).comp
    (tendsto_atTop_atTop.mpr fun b => ⟨b, fun k hk => by omega⟩ :
      Tendsto (fun k : ℕ => n + 1 + k) atTop atTop)).sub_const
    (finiteHarmonicSum n (pmPowerDampedRealWeight ε))
  exact le_of_tendsto' hlim.abs fun k => abs_finiteHarmonicSum_pmPowerDamped_sub_le hε.le hη k

/-! ### The sign of the damped prime slope -/

/-- With `|m(t)| ≤ 1/8` beyond `p - 1`: `p^{-ε}/2 - 2ρ_ε ≤ λ_ε(p) ≤ (3/2) p^{-ε} - 2ρ_ε`. -/
theorem dampedPrimeSlope_bounds {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime)
    (hη : ∀ t, p - 1 ≤ t → |finiteHarmonicSum t moebiusReal| ≤ 1 / 8) :
    (p : ℝ) ^ (-ε) / 2 - 2 * (pmPowerDampedDivisorDensity ε).re ≤ dampedPrimeSlope ε p ∧
      dampedPrimeSlope ε p ≤ 3 / 2 * (p : ℝ) ^ (-ε) - 2 * (pmPowerDampedDivisorDensity ε).re := by
  have h := abs_pmPowerDampedDivisorDensity_re_sub_le hε hη
  rw [show p - 1 + 1 = p by have := hp.one_le; omega] at h
  have h' := abs_le.mp h
  unfold dampedPrimeSlope
  constructor <;> linarith [h'.1, h'.2]

/-- The **crossover scale** `Λ(ε) = log(1/(2ρ_ε))/ε`, `ρ_ε = 1/ζ(1+ε)`. -/
def dampedCrossoverScale (ε : ℝ) : ℝ :=
  -Real.log (2 * (pmPowerDampedDivisorDensity ε).re) / ε

theorem tendsto_pmPowerDampedDivisorDensity_re_zero :
    Tendsto (fun ε : ℝ => (pmPowerDampedDivisorDensity ε).re) (𝓝[>] 0) (𝓝 0) := by
  have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have h := tendsto_pmPowerDampedDivisorDensity_re_div_parameter.mul hid
  rw [one_mul] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  field_simp [ne_of_gt (Set.mem_Ioi.mp hε)]

/-- **Sharp crossover of the damped prime slope.** For every `δ > 0` there is an absolute
threshold `P₀` such that for all small `ε > 0` and primes `p ≥ P₀`: the slope is positive when
`log p ≤ (1-δ) Λ(ε)` and negative when `log p ≥ (1+δ) Λ(ε)`. -/
theorem dampedPrimeSlope_crossover {δ : ℝ} (hδ : 0 < δ) :
    ∃ P₀ : ℕ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p : ℕ, P₀ ≤ p → p.Prime →
      (Real.log p ≤ (1 - δ) * dampedCrossoverScale ε → 0 < dampedPrimeSlope ε p) ∧
      ((1 + δ) * dampedCrossoverScale ε ≤ Real.log p → dampedPrimeSlope ε p < 0) := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (tendsto_finiteHarmonicSum_moebiusReal_zero.eventually
    (Metric.closedBall_mem_nhds (0 : ℝ) (show (0 : ℝ) < 1 / 8 by norm_num)))
  refine ⟨T + 1, ?_⟩
  set θ := Real.exp (-Real.log 2 / δ)
  have hθ : 0 < θ := Real.exp_pos _
  filter_upwards [self_mem_nhdsWithin, tendsto_pmPowerDampedDivisorDensity_re_zero.eventually
    (eventually_lt_nhds (show (0 : ℝ) < θ / 2 by positivity))] with ε hε hsmall p hpT hp
  have hε0 : 0 < ε := hε
  set ρ := (pmPowerDampedDivisorDensity ε).re
  have hρ : 0 < ρ := RHTower.pmPowerDampedDivisorDensity_re_pos hε0
  have hη : ∀ t, p - 1 ≤ t → |finiteHarmonicSum t moebiusReal| ≤ 1 / 8 := fun t ht => by
    have := hT t (by omega)
    simpa [Metric.mem_closedBall, Real.dist_eq] using this
  obtain ⟨hlo, hhi⟩ := dampedPrimeSlope_bounds hε0 hp hη
  set u := Real.log (2 * ρ)
  have hu : u < -Real.log 2 / δ := by
    have := Real.log_lt_log (by positivity) (show 2 * ρ < θ by linarith)
    rwa [Real.log_exp] at this
  have hδu : δ * u < -Real.log 2 := by
    have := mul_lt_mul_of_pos_left hu hδ
    rwa [mul_div_cancel₀ _ hδ.ne'] at this
  have hexpu : Real.exp u = 2 * ρ := Real.exp_log (by positivity)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpow : (p : ℝ) ^ (-ε) = Real.exp (-(ε * Real.log p)) := by
    rw [Real.rpow_def_of_pos hp0]; ring_nf
  have hscale : ε * dampedCrossoverScale ε = -u := by
    unfold dampedCrossoverScale; field_simp; rfl
  have hlog2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  constructor
  · intro hle
    have h1 : -(ε * Real.log p) ≥ (1 - δ) * u := by
      have := mul_le_mul_of_nonneg_left hle hε0.le
      nlinarith
    have h2 : (p : ℝ) ^ (-ε) > 4 * ρ := by
      rw [hpow]
      calc Real.exp (-(ε * Real.log p)) ≥ Real.exp ((1 - δ) * u) := Real.exp_le_exp.mpr h1
        _ = Real.exp u * Real.exp (-(δ * u)) := by rw [← Real.exp_add]; ring_nf
        _ > Real.exp u * Real.exp (Real.log 2) := by
            apply mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (by linarith)) (Real.exp_pos _)
        _ = 4 * ρ := by rw [hexpu, hlog2]; ring
    linarith
  · intro hge
    have h1 : -(ε * Real.log p) ≤ (1 + δ) * u := by
      have := mul_le_mul_of_nonneg_left hge hε0.le
      nlinarith
    have h2 : (p : ℝ) ^ (-ε) < ρ := by
      rw [hpow]
      calc Real.exp (-(ε * Real.log p)) ≤ Real.exp ((1 + δ) * u) := Real.exp_le_exp.mpr h1
        _ = Real.exp u * Real.exp (δ * u) := by rw [← Real.exp_add]; ring_nf
        _ < Real.exp u * Real.exp (-Real.log 2) := by
            apply mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hδu) (Real.exp_pos _)
        _ = ρ := by
            rw [hexpu, Real.exp_neg, hlog2]; ring
    linarith

/-- **The crossover scale.** `ε Λ(ε) = log(1/(2ε)) + o(1)` as `ε → 0⁺`. -/
theorem tendsto_mul_dampedCrossoverScale_sub_log :
    Tendsto (fun ε : ℝ => ε * dampedCrossoverScale ε - Real.log (1 / (2 * ε))) (𝓝[>] 0)
      (𝓝 0) := by
  have h := (Real.continuousAt_log one_ne_zero).tendsto.comp
    tendsto_pmPowerDampedDivisorDensity_re_div_parameter
  rw [Real.log_one] at h
  have h' := h.neg
  rw [neg_zero] at h'
  refine h'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : 0 < ε := hε
  have hρ : 0 < (pmPowerDampedDivisorDensity ε).re := RHTower.pmPowerDampedDivisorDensity_re_pos hε0
  simp only [Function.comp]
  unfold dampedCrossoverScale
  rw [mul_div_cancel₀ _ hε0.ne', Real.log_div hρ.ne' hε0.ne', Real.log_mul two_ne_zero hρ.ne',
    one_div, Real.log_inv, Real.log_mul two_ne_zero hε0.ne']
  ring

/-! ### Energy steps follow the slope -/

theorem pmPowerDamped_prime_step_pos_of_slope {p : ℕ} (hp : p.Prime) {ε : ℝ} (hε : 0 ≤ ε)
    {M : ℕ} (h : 2 * ((p : ℝ) - 1) < ((M / p : ℕ) : ℝ) * dampedPrimeSlope ε p) :
    sieveL2PrefixEnergy (p - 1) M (pmPowerDampedRealWeight ε) <
      sieveL2PrefixEnergy p M (pmPowerDampedRealWeight ε) := by
  obtain ⟨N, rfl⟩ : ∃ N, p = N + 1 := ⟨p - 1, by have := hp.one_le; omega⟩
  rw [show N + 1 - 1 = N by omega]
  have hlaw := (abs_le.mp (abs_pmPowerDamped_prime_step_sub_slope_le hp hε M)).1
  have hr0 : 0 < ((N + 1 : ℕ) : ℝ) ^ (-ε) := Real.rpow_pos_of_pos (by positivity) _
  have hN : ((N + 1 : ℕ) : ℝ) - 1 = N := by push_cast; ring
  rw [hN] at h
  nlinarith [mul_lt_mul_of_pos_left h hr0]

theorem pmPowerDamped_prime_step_neg_of_slope {p : ℕ} (hp : p.Prime) {ε : ℝ} (hε : 0 ≤ ε)
    {M : ℕ} (h : 2 * ((p : ℝ) - 1) < -(((M / p : ℕ) : ℝ) * dampedPrimeSlope ε p)) :
    sieveL2PrefixEnergy p M (pmPowerDampedRealWeight ε) <
      sieveL2PrefixEnergy (p - 1) M (pmPowerDampedRealWeight ε) := by
  obtain ⟨N, rfl⟩ : ∃ N, p = N + 1 := ⟨p - 1, by have := hp.one_le; omega⟩
  rw [show N + 1 - 1 = N by omega]
  have hlaw := (abs_le.mp (abs_pmPowerDamped_prime_step_sub_slope_le hp hε M)).2
  have hr0 : 0 < ((N + 1 : ℕ) : ℝ) ^ (-ε) := Real.rpow_pos_of_pos (by positivity) _
  have hN : ((N + 1 : ℕ) : ℝ) - 1 = N := by push_cast; ring
  rw [hN] at h
  nlinarith [mul_lt_mul_of_pos_left h hr0]

/-- **Crossover of the energy steps.** For every `δ > 0` there is an absolute `P₀` such that for
all small `ε > 0` and primes `p ≥ P₀`: below `(1-δ)Λ(ε)` the horizon `p` raises, and above
`(1+δ)Λ(ε)` it lowers, the damped prefix energy at all large prefixes. -/
theorem pmPowerDamped_prime_step_crossover {δ : ℝ} (hδ : 0 < δ) :
    ∃ P₀ : ℕ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p : ℕ, P₀ ≤ p → p.Prime →
      (Real.log p ≤ (1 - δ) * dampedCrossoverScale ε → ∀ᶠ M in atTop,
        sieveL2PrefixEnergy (p - 1) M (pmPowerDampedRealWeight ε) <
          sieveL2PrefixEnergy p M (pmPowerDampedRealWeight ε)) ∧
      ((1 + δ) * dampedCrossoverScale ε ≤ Real.log p → ∀ᶠ M in atTop,
        sieveL2PrefixEnergy p M (pmPowerDampedRealWeight ε) <
          sieveL2PrefixEnergy (p - 1) M (pmPowerDampedRealWeight ε)) := by
  obtain ⟨P₀, hP₀⟩ := dampedPrimeSlope_crossover hδ
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

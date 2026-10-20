import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedVarianceAndDissipationSecondOrderLaw
import GaloisForLFunctions.BezoutValuationIncidence.MultiLagCovarianceConeFiniteGeneration

/-!
# The damped autocorrelation sees the Hardy–Littlewood singular series

The lag-`h` period covariance of the damped sieve response converges to the damped
autocorrelation `A_ε(h) = Σ_{e ≥ 2} c_e(h) w_ε(e)²`, where `w_ε(e) = ρ_ε μ(e)/D_ε(e)` and
`D_ε(e) = Π_{p ∣ e} (p^{1+ε} - 1)`. Hence, exactly,

`A_ε(h) = ρ_ε² (S_ε(h) - 1)`,  `S_ε(h) = Σ_e μ(e)² c_e(h)/D_ε(e)²`.

As `ε → 0⁺`, `D_ε(e) → φ(e)` on squarefree moduli with the domination `|c_e(h)| ≤ σ(h)`,
`D_ε(e) ≥ φ(e)`, so `S_ε(h)` tends to the **Hardy–Littlewood pair singular series**

`𝔖(h) = Σ_e μ(e)² c_e(h)/φ(e)²`,

and with `ρ_ε/ε → 1`,

`A_ε(h)/ε² → 𝔖(h) - 1`  for every lag `h ≥ 1`.

So at second order in the damping the damped divisor function correlates like the primes:
`E[τ_ε(n) τ_ε(n+h)] = ε² 𝔖(h) + o(ε²)`, as `τ_ε(p) = 1 - p^{-ε} ≈ ε log p` on primes while
products of two or more prime factors are `O(ε²)`. The parity of the lag is decisive: pairing the
odd moduli `e` with `2e` gives `𝔖(h) = (1 + c_2(h)) Σ_{e odd} μ(e)² c_e(h)/φ(e)²`, so `𝔖(h) = 0` and
`A_ε(h)/ε² → -1` at every odd lag (one of `n`, `n + h` is even), extending the lag-one law.
Multiplicativity of `e ↦ μ(e)² c_e(h)/φ(e)²` gives the Hardy–Littlewood Euler product
`𝔖(h) = Π_p (1 + c_p(h)/(p-1)²)`; at even lags every local factor is at least `3/4` and the
logarithms are summable, so `𝔖(h) > 0`: even lags are strictly less anti-correlated.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The singular series -/

/-- The Hardy–Littlewood pair singular series `𝔖(h) = Σ_e μ(e)² c_e(h)/φ(e)²`. -/
def pairSingularSeries (h : ℕ) : ℝ :=
  ∑' e : ℕ, moebiusReal e ^ 2 * ramanujanLagWeight h e / (Nat.totient e : ℝ) ^ 2

/-- The damped singular sum `S_ε(h) = Σ_e μ(e)² c_e(h)/D_ε(e)²`. -/
def dampedSingularSum (ε : ℝ) (h : ℕ) : ℝ :=
  ∑' e : ℕ, moebiusReal e ^ 2 * ramanujanLagWeight h e /
    RHTower.pmPowerDampedRamanujanDenominator ε e ^ 2

private theorem moebiusReal_sq_of_squarefree {e : ℕ} (hsq : Squarefree e) : moebiusReal e ^ 2 = 1 := by
  unfold moebiusReal
  have h1 : |(μ e : ℝ)| = 1 := by exact_mod_cast abs_moebius_eq_one_of_squarefree hsq
  rw [← sq_abs, h1]; norm_num

/-- `φ(e) = Π_{p ∣ e} (p - 1)` on squarefree moduli. -/
private theorem totient_eq_prod_of_squarefree {e : ℕ} (hsq : Squarefree e) :
    (Nat.totient e : ℝ) = ∏ p ∈ e.primeFactors, ((p : ℝ) - 1) := by
  have hφ := Nat.totient_mul_prod_primeFactors e
  rw [Nat.prod_primeFactors_of_squarefree hsq] at hφ
  have he0 : 0 < e := Nat.pos_of_ne_zero hsq.ne_zero
  have hφ' : Nat.totient e = ∏ p ∈ e.primeFactors, (p - 1) := by
    rw [mul_comm] at hφ; exact Nat.eq_of_mul_eq_mul_left he0 hφ
  rw [hφ', Nat.cast_prod]
  exact prod_congr rfl fun p hp => by
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.cast_one]

/-- `φ(e) ≤ D_ε(e)` on squarefree moduli, for `ε ≥ 0`. -/
private theorem totient_le_denominator {ε : ℝ} (hε : 0 ≤ ε) {e : ℕ} (hsq : Squarefree e) :
    (Nat.totient e : ℝ) ≤ RHTower.pmPowerDampedRamanujanDenominator ε e := by
  rw [totient_eq_prod_of_squarefree hsq, RHTower.pmPowerDampedRamanujanDenominator]
  refine prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
  · have : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
    linarith
  · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
    have : (p : ℝ) ^ (1 : ℝ) ≤ (p : ℝ) ^ (1 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    rw [Real.rpow_one] at this
    linarith

/-- `D_ε(e) > 0` for `ε ≥ 0`. -/
private theorem denominator_pos {ε : ℝ} (hε : 0 ≤ ε) (e : ℕ) :
    0 < RHTower.pmPowerDampedRamanujanDenominator ε e := by
  refine prod_pos fun p hp => ?_
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have : (p : ℝ) ^ (1 : ℝ) ≤ (p : ℝ) ^ (1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  rw [Real.rpow_one] at this
  linarith

/-- The common majorant `σ(h) μ(e)²/φ(e)²` of the damped and limiting terms. -/
private theorem abs_singular_term_le {ε : ℝ} (hε : 0 ≤ ε) {h : ℕ} (hh : 1 ≤ h) (e : ℕ) :
    |moebiusReal e ^ 2 * ramanujanLagWeight h e / RHTower.pmPowerDampedRamanujanDenominator ε e ^ 2| ≤
      (∑ d ∈ h.divisors, (d : ℝ)) *
        (RHTower.Sieve.sqfreeTotientInv e / (Nat.totient e : ℝ)) := by
  have hσ0 : 0 ≤ ∑ d ∈ h.divisors, (d : ℝ) := sum_nonneg fun d _ => Nat.cast_nonneg d
  by_cases hsq : Squarefree e
  · have hφ : (0 : ℝ) < Nat.totient e := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hsq.ne_zero)
    have hD := totient_le_denominator hε hsq
    rw [moebiusReal_sq_of_squarefree hsq, one_mul, RHTower.Sieve.sqfreeTotientInv_apply, if_pos hsq,
      abs_div, abs_of_pos (pow_pos (denominator_pos hε e) 2)]
    have hc := abs_ramanujanLagWeight_le_sigma hh e
    calc |ramanujanLagWeight h e| / RHTower.pmPowerDampedRamanujanDenominator ε e ^ 2
        ≤ (∑ d ∈ h.divisors, (d : ℝ)) / (Nat.totient e : ℝ) ^ 2 :=
          div_le_div₀ hσ0 hc (by positivity) (pow_le_pow_left₀ hφ.le hD 2)
      _ = _ := by field_simp
  · rw [moebiusReal_eq_zero_of_not_squarefree e hsq]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, zero_div,
      abs_zero]
    exact mul_nonneg hσ0 (div_nonneg (RHTower.Sieve.sqfreeTotientInv_nonneg e) (Nat.cast_nonneg _))

private theorem summable_singular_majorant (h : ℕ) :
    Summable fun e : ℕ => (∑ d ∈ h.divisors, (d : ℝ)) *
      (RHTower.Sieve.sqfreeTotientInv e / (Nat.totient e : ℝ)) :=
  (summable_sqfreeTotientInv_div_totient.1).mul_left _

private theorem summable_dampedSingular_term {ε : ℝ} (hε : 0 ≤ ε) {h : ℕ} (hh : 1 ≤ h) :
    Summable fun e : ℕ => moebiusReal e ^ 2 * ramanujanLagWeight h e /
      RHTower.pmPowerDampedRamanujanDenominator ε e ^ 2 :=
  Summable.of_norm_bounded (summable_singular_majorant h) fun e => by
    rw [Real.norm_eq_abs]; exact abs_singular_term_le hε hh e

/-- At `ε = 0` the damped term is the singular-series term. -/
private theorem singular_term_zero (h e : ℕ) :
    moebiusReal e ^ 2 * ramanujanLagWeight h e / RHTower.pmPowerDampedRamanujanDenominator 0 e ^ 2 =
      moebiusReal e ^ 2 * ramanujanLagWeight h e / (Nat.totient e : ℝ) ^ 2 := by
  by_cases hsq : Squarefree e
  · rw [totient_eq_prod_of_squarefree hsq, RHTower.pmPowerDampedRamanujanDenominator]
    congr 2
    exact prod_congr rfl fun p _ => by rw [add_zero, Real.rpow_one]
  · simp [moebiusReal_eq_zero_of_not_squarefree e hsq]

/-- The singular series converges absolutely for every lag `h ≥ 1`. -/
theorem summable_pairSingularSeries_term {h : ℕ} (hh : 1 ≤ h) :
    Summable fun e : ℕ => moebiusReal e ^ 2 * ramanujanLagWeight h e / (Nat.totient e : ℝ) ^ 2 := by
  have := summable_dampedSingular_term (ε := 0) le_rfl hh
  simpa only [singular_term_zero] using this

/-- **Convergence of the damped singular sum.** `S_ε(h) → 𝔖(h)` as `ε → 0⁺`. -/
theorem tendsto_dampedSingularSum {h : ℕ} (hh : 1 ≤ h) :
    Tendsto (fun ε : ℝ => dampedSingularSum ε h) (𝓝[>] 0) (𝓝 (pairSingularSeries h)) := by
  unfold dampedSingularSum pairSingularSeries
  refine tendsto_tsum_of_dominated_convergence (summable_singular_majorant h) (fun e => ?_) ?_
  · rw [← singular_term_zero]
    refine Tendsto.div tendsto_const_nhds (Tendsto.pow ?_ 2) ?_
    · unfold RHTower.pmPowerDampedRamanujanDenominator
      refine tendsto_finsetProd _ fun p hp => ?_
      have hp0 : (p : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
      have hc : Continuous (fun ε : ℝ => (p : ℝ) ^ (1 + ε) - 1) :=
        ((Real.continuous_const_rpow hp0).comp (continuous_const.add continuous_id)).sub
          continuous_const
      exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · exact pow_ne_zero 2 (denominator_pos le_rfl e).ne'
  · filter_upwards [self_mem_nhdsWithin] with ε hε e
    rw [Real.norm_eq_abs]
    exact abs_singular_term_le (le_of_lt hε) hh e

/-! ### The autocorrelation is the singular sum -/

/-- `w_ε(e) = ρ_ε μ(e)/D_ε(e)`. -/
private theorem dampedRamanujanCoeff_eq {ε : ℝ} (hε : 0 < ε) (e : ℕ) :
    dampedRamanujanCoeff ε e = (RHTower.pmPowerDampedDivisorDensity ε).re * moebiusReal e /
      RHTower.pmPowerDampedRamanujanDenominator ε e := by
  unfold dampedRamanujanCoeff
  rw [RHTower.pmPowerDampedRamanujanWeight_eq_ofReal hε, Complex.ofReal_re]
  rfl

/-- **Exact form.** `A_ε(h) = ρ_ε² (S_ε(h) - 1)` for every lag `h ≥ 1`. -/
theorem dampedAutocorrelation_eq_singularSum {ε : ℝ} (hε : 0 < ε) {h : ℕ} (hh : 1 ≤ h) :
    dampedAutocorrelation ε h =
      (RHTower.pmPowerDampedDivisorDensity ε).re ^ 2 * (dampedSingularSum ε h - 1) := by
  set ρ := (RHTower.pmPowerDampedDivisorDensity ε).re
  set t : ℕ → ℝ := fun e => moebiusReal e ^ 2 * ramanujanLagWeight h e /
    RHTower.pmPowerDampedRamanujanDenominator ε e ^ 2
  have hterm : ∀ e, ramanujanLagWeight h e * dampedRamanujanCoeff ε e ^ 2 = ρ ^ 2 * t e := fun e => by
    have hD := (RHTower.pmPowerDampedRamanujanDenominator_pos hε e).ne'
    rw [dampedRamanujanCoeff_eq hε]
    simp only [t, ρ]
    field_simp
  have ht : Summable t := summable_dampedSingular_term hε.le hh
  have hg : Summable fun e => ρ ^ 2 * t e := ht.mul_left _
  have h1 : ρ ^ 2 * dampedSingularSum ε h = ρ ^ 2 * t 1 + ∑' i, ρ ^ 2 * t (i + 2) := by
    rw [dampedSingularSum, ← tsum_mul_left, ← hg.sum_add_tsum_nat_add 2]
    simp [Finset.sum_range_succ, t, moebiusReal]
  have ht1 : t 1 = 1 := by
    simp [t, moebiusReal, RHTower.pmPowerDampedRamanujanDenominator, ramanujanLagWeight_of_dvd]
  have hgA : Summable fun e : ℕ => if 2 ≤ e then ramanujanLagWeight h e *
      dampedRamanujanCoeff ε e ^ 2 else 0 := by
    refine Summable.of_norm_bounded hg.norm fun e => ?_
    split_ifs
    · rw [hterm]
    · rw [norm_zero]; exact norm_nonneg _
  have h2 : dampedAutocorrelation ε h = ∑' i, ρ ^ 2 * t (i + 2) := by
    unfold dampedAutocorrelation
    rw [← hgA.sum_add_tsum_nat_add 2]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, show ¬ 2 ≤ 0 by omega,
      show ¬ 2 ≤ 1 by omega, if_false, zero_add, show ∀ i : ℕ, 2 ≤ i + 2 from fun i => by omega,
      if_true, hterm]
  rw [h2, mul_sub, h1, ht1]
  ring

/-- **The singular series law.** For every lag `h ≥ 1`, `A_ε(h)/ε² → 𝔖(h) - 1` as `ε → 0⁺`. -/
theorem tendsto_dampedAutocorrelation_div_sq {h : ℕ} (hh : 1 ≤ h) :
    Tendsto (fun ε : ℝ => dampedAutocorrelation ε h / ε ^ 2) (𝓝[>] 0)
      (𝓝 (pairSingularSeries h - 1)) := by
  have h := (RHTower.tendsto_pmPowerDampedDivisorDensity_re_div_parameter.pow 2).mul
    ((tendsto_dampedSingularSum hh).sub_const 1)
  rw [one_pow, one_mul] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : (0 : ℝ) < ε := hε
  rw [dampedAutocorrelation_eq_singularSum hε0 hh]
  field_simp

/-! ### Parity -/

/-- **Parity factorisation.** `𝔖(h) = (1 + c_2(h)) Σ_{e odd} μ(e)² c_e(h)/φ(e)²`. -/
theorem pairSingularSeries_eq_parity {h : ℕ} (hh : 1 ≤ h) :
    pairSingularSeries h = (1 + ramanujanLagWeight h 2) *
      ∑' j : ℕ, moebiusReal (2 * j + 1) ^ 2 * ramanujanLagWeight h (2 * j + 1) /
        (Nat.totient (2 * j + 1) : ℝ) ^ 2 := by
  set f : ℕ → ℝ := fun e => moebiusReal e ^ 2 * ramanujanLagWeight h e / (Nat.totient e : ℝ) ^ 2
  have hf : Summable f := summable_pairSingularSeries_term hh
  have hinj2 : Function.Injective (fun k : ℕ => 2 * k) := mul_right_injective₀ two_ne_zero
  have hinj1 : Function.Injective (fun k : ℕ => 2 * k + 1) :=
    fun a b (hab : 2 * a + 1 = 2 * b + 1) => by omega
  have h2 : Summable fun k => f (2 * k) := hf.comp_injective hinj2
  have h1 : Summable fun k => f (2 * k + 1) := hf.comp_injective hinj1
  have h4 : Summable fun j => f (2 * (2 * j)) := h2.comp_injective hinj2
  have h3 : Summable fun j => f (2 * (2 * j + 1)) := h2.comp_injective hinj1
  have hodd : ∀ j, f (2 * (2 * j + 1)) = ramanujanLagWeight h 2 * f (2 * j + 1) := fun j => by
    have hm : ¬ 2 ∣ 2 * j + 1 := by omega
    have hcop : Nat.Coprime 2 (2 * j + 1) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm
    simp only [f]
    rw [moebiusReal_two_mul_odd hm, ramanujanLagWeight_mul_of_coprime h hcop,
      Nat.totient_mul hcop, Nat.totient_two, one_mul]
    ring
  have heven : ∀ j, f (2 * (2 * j)) = 0 := fun j => by
    simp only [f]; rw [moebiusReal_four_mul]; simp
  have hsplit := tsum_even_add_odd (f := fun k => f (2 * k)) h4 h3
  unfold pairSingularSeries
  rw [← tsum_even_add_odd h2 h1, ← hsplit]
  simp only [heven, tsum_zero, zero_add, hodd, tsum_mul_left]
  ring

/-- **Odd lags.** `𝔖(h) = 0` for odd `h`. -/
theorem pairSingularSeries_of_odd {h : ℕ} (hh : ¬ 2 ∣ h) : pairSingularSeries h = 0 := by
  have h1 : 1 ≤ h := Nat.pos_of_ne_zero (by rintro rfl; simp at hh)
  rw [pairSingularSeries_eq_parity h1, ramanujanLagWeight_prime Nat.prime_two, if_neg hh]
  ring

/-- **Odd-lag anti-correlation.** For every odd lag `h`, `A_ε(h) = -ε² + o(ε²)`. -/
theorem tendsto_dampedAutocorrelation_odd_lag {h : ℕ} (hh : ¬ 2 ∣ h) :
    Tendsto (fun ε : ℝ => dampedAutocorrelation ε h / ε ^ 2) (𝓝[>] 0) (𝓝 (-1)) := by
  have h1 : 1 ≤ h := Nat.pos_of_ne_zero (by rintro rfl; simp at hh)
  have := tendsto_dampedAutocorrelation_div_sq h1
  rwa [pairSingularSeries_of_odd hh, zero_sub] at this

/-- **Even lags.** `𝔖(h) = 2 Σ_{e odd} μ(e)² c_e(h)/φ(e)²` for even `h ≥ 2`. -/
theorem pairSingularSeries_of_even {h : ℕ} (hh : 2 ∣ h) (h1 : 1 ≤ h) :
    pairSingularSeries h = 2 * ∑' j : ℕ, moebiusReal (2 * j + 1) ^ 2 *
      ramanujanLagWeight h (2 * j + 1) / (Nat.totient (2 * j + 1) : ℝ) ^ 2 := by
  rw [pairSingularSeries_eq_parity h1, ramanujanLagWeight_prime Nat.prime_two, if_pos hh]
  norm_num


/-! ### The Euler product and positivity at even lags -/

/-- The singular-series term `μ(e)² c_e(h)/φ(e)²`. -/
private def singularTerm (h e : ℕ) : ℝ :=
  moebiusReal e ^ 2 * ramanujanLagWeight h e / (Nat.totient e : ℝ) ^ 2

private theorem moebiusReal_mul_of_coprime {m n : ℕ} (hmn : m.Coprime n) :
    moebiusReal (m * n) = moebiusReal m * moebiusReal n := by
  unfold moebiusReal
  rw [isMultiplicative_moebius.map_mul_of_coprime hmn]
  push_cast; ring

private theorem singularTerm_mul (h : ℕ) {m n : ℕ} (hmn : m.Coprime n) :
    singularTerm h (m * n) = singularTerm h m * singularTerm h n := by
  simp only [singularTerm]
  rw [moebiusReal_mul_of_coprime hmn, ramanujanLagWeight_mul_of_coprime h hmn,
    Nat.totient_mul hmn, Nat.cast_mul]
  ring

private theorem singularTerm_one (h : ℕ) : singularTerm h 1 = 1 := by
  simp [singularTerm, moebiusReal, ramanujanLagWeight_of_dvd (one_dvd h)]

/-- The local factor at a prime is `1 + c_p(h)/(p-1)²`: higher prime powers are not squarefree. -/
private theorem tsum_singularTerm_prime_pow (h : ℕ) (p : Nat.Primes) :
    ∑' k : ℕ, singularTerm h ((p : ℕ) ^ k) =
      1 + ramanujanLagWeight h p / (((p : ℕ) : ℝ) - 1) ^ 2 := by
  rw [tsum_eq_sum (s := {0, 1}) (fun k hk => ?_)]
  · rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1), pow_zero, pow_one, singularTerm_one]
    congr 1
    simp only [singularTerm]
    have hμ : moebiusReal (p : ℕ) ^ 2 = 1 := by
      unfold moebiusReal; rw [moebius_apply_prime p.property]; norm_num
    rw [hμ, one_mul, Nat.totient_prime p.property, Nat.cast_sub p.property.one_lt.le, Nat.cast_one]
  · have hk0 : k ≠ 0 := fun h' => hk (by simp [h'])
    have hk1 : k ≠ 1 := fun h' => hk (by simp [h'])
    have hμ : moebiusReal ((p : ℕ) ^ k) = 0 := by
      unfold moebiusReal
      rw [moebius_apply_prime_pow p.property hk0, if_neg hk1]
      simp
    simp [singularTerm, hμ]

/-- **Hardy–Littlewood Euler product.** `𝔖(h) = Π_p (1 + c_p(h)/(p-1)²)` for every lag `h ≥ 1`. -/
theorem hasProd_pairSingularSeries {h : ℕ} (hh : 1 ≤ h) :
    HasProd (fun p : Nat.Primes => 1 + ramanujanLagWeight h p / (((p : ℕ) : ℝ) - 1) ^ 2)
      (pairSingularSeries h) := by
  have hp := EulerProduct.eulerProduct_hasProd (f := singularTerm h) (singularTerm_one h)
    (fun {_ _} hmn => singularTerm_mul h hmn) (summable_pairSingularSeries_term hh).norm
    (by simp [singularTerm, moebiusReal])
  have hfun : (fun p : Nat.Primes => ∑' k : ℕ, singularTerm h ((p : ℕ) ^ k)) =
      fun p : Nat.Primes => 1 + ramanujanLagWeight h p / (((p : ℕ) : ℝ) - 1) ^ 2 :=
    by funext p; exact tsum_singularTerm_prime_pow h p
  rw [hfun] at hp
  exact hp

/-- Each local factor at an even lag is at least `3/4` and within `4h/p²` of one. -/
private theorem singular_factor_bounds {h : ℕ} (hh : 2 ∣ h) (h1 : 1 ≤ h) (p : Nat.Primes) :
    3 / 4 ≤ 1 + ramanujanLagWeight h p / (((p : ℕ) : ℝ) - 1) ^ 2 ∧
      |ramanujanLagWeight h p / (((p : ℕ) : ℝ) - 1) ^ 2| ≤ 4 * h / ((p : ℕ) : ℝ) ^ 2 := by
  have hP2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.property.two_le
  have hP1 : (0 : ℝ) < ((p : ℕ) : ℝ) - 1 := by linarith
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast h1
  rw [ramanujanLagWeight_prime p.property]
  split_ifs with hph
  · have hPh : ((p : ℕ) : ℝ) ≤ h := by exact_mod_cast Nat.le_of_dvd (by omega) hph
    have he : (((p : ℕ) : ℝ) - 1) / (((p : ℕ) : ℝ) - 1) ^ 2 = 1 / (((p : ℕ) : ℝ) - 1) := by
      field_simp
    rw [he, abs_of_pos (by positivity)]
    constructor
    · have : 0 < 1 / (((p : ℕ) : ℝ) - 1) := by positivity
      linarith
    · rw [div_le_div_iff₀ hP1 (by positivity)]
      nlinarith
  · have hp3 : (3 : ℝ) ≤ (p : ℕ) := by
      have hp2 : (p : ℕ) ≠ 2 := fun h2 => hph (h2 ▸ hh)
      have := p.property.two_le
      exact_mod_cast (show 3 ≤ (p : ℕ) by omega)
    rw [abs_div, abs_neg, abs_one, abs_of_pos (by positivity)]
    constructor
    · have hq : 1 / (((p : ℕ) : ℝ) - 1) ^ 2 ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      rw [neg_div]; linarith
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith

/-- `|log a| ≤ (4/3)|a - 1|` for `a ≥ 3/4`. -/
private theorem abs_log_le_of_ge {a : ℝ} (ha : 3 / 4 ≤ a) : |Real.log a| ≤ 4 / 3 * |a - 1| := by
  have ha0 : 0 < a := by linarith
  have hup := Real.log_le_sub_one_of_pos ha0
  have hlo := Real.one_sub_inv_le_log_of_pos ha0
  have hinv : a⁻¹ ≤ 4 / 3 := by
    rw [inv_le_comm₀ ha0 (by norm_num)]; norm_num; linarith
  have hid : 1 - a⁻¹ = (a - 1) * a⁻¹ := by field_simp
  rw [hid] at hlo
  rcases le_or_gt 1 a with h1 | h1
  · rw [abs_of_nonneg (by linarith : 0 ≤ a - 1)]
    have : 0 ≤ (a - 1) * a⁻¹ := mul_nonneg (by linarith) (inv_nonneg.mpr ha0.le)
    rw [abs_le]; constructor <;> linarith
  · rw [abs_of_neg (by linarith : a - 1 < 0)]
    have : (a - 1) * (4 / 3) ≤ (a - 1) * a⁻¹ := mul_le_mul_of_nonpos_left hinv (by linarith)
    rw [abs_le]; constructor <;> linarith

/-- **Even lags are positively seen.** `𝔖(h) > 0` for every even `h ≥ 2`: all local factors are
positive and their logarithms are summable. -/
theorem pairSingularSeries_pos_of_even {h : ℕ} (hh : 2 ∣ h) (h1 : 1 ≤ h) :
    0 < pairSingularSeries h := by
  set a : Nat.Primes → ℝ := fun p => 1 + ramanujanLagWeight h p / (((p : ℕ) : ℝ) - 1) ^ 2
  have hmaj : Summable fun p : Nat.Primes => 4 / 3 * (4 * h / ((p : ℕ) : ℝ) ^ 2) := by
    have hs : Summable fun p : Nat.Primes => 1 / ((p : ℕ) : ℝ) ^ 2 :=
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective
        Subtype.val_injective
    refine (hs.mul_left (4 / 3 * (4 * (h : ℝ)))).congr fun p => ?_
    ring
  have hlog : Summable fun p : Nat.Primes => Real.log (a p) := by
    refine Summable.of_norm_bounded hmaj fun p => ?_
    obtain ⟨hlo, hx⟩ := singular_factor_bounds hh h1 p
    rw [Real.norm_eq_abs]
    refine (abs_log_le_of_ge hlo).trans ?_
    simp only [add_sub_cancel_left]
    exact mul_le_mul_of_nonneg_left hx (by norm_num)
  have hexp := hlog.hasSum.rexp
  have heq : (Real.exp ∘ fun p : Nat.Primes => Real.log (a p)) = a :=
    funext fun p => Real.exp_log (by linarith [(singular_factor_bounds hh h1 p).1])
  rw [heq] at hexp
  rw [(hasProd_pairSingularSeries h1).unique hexp]
  exact Real.exp_pos _

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics

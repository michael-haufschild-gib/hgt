import GaloisForLFunctions.TransHorizonIncidenceMechanics.ReceiverRowParsevalSpectrumAndHorizonUniformVariance
import GaloisForLFunctions.RHTower.Sieve.LevinsonGcdFormBound

/-!
# The damped autocorrelation, small-damping whiteness, and clock invisibility

**Clock invisibility.** A squarefree-supported weight has vanishing Selberg coordinates at every
non-squarefree mode, and at a squarefree mode `e` the Ramanujan lag weight `c_e(h)` depends on the
lag only through `gcd(e, h)`, which is determined by the primes of `h`. Hence for every
squarefree-supported weight and every horizon, the complete-period covariance at lag `h` depends only
on the set of primes dividing `h`: the visibility clock `h / rad(h)` is invisible.

**The damped autocorrelation.** For `c_ε` the Selberg coordinates converge to the Ramanujan
coefficients `w_ε(e) = E[τ_ε] μ(e)/D_ε(e)`, `D_ε(e) = ∏_{p|e}(p^{1+ε} - 1) ≥ φ(e)`, and at a fixed lag
`h ≥ 1` the multipliers are bounded by `σ(h)`; so

`Cov_N(h; c_ε) → A_ε(h) = Σ_{e ≥ 2} c_e(h) w_ε(e)²`,   `|A_ε(h)| ≤ 16 σ(h) E[τ_ε]²`,

the receiver row has `Cov_{Q+1}(h; c_Q) = Σ_{2 ≤ e ≤ Q+1} c_e(h) w_ε(e)²` with the same bound at
every cutoff, and since `E[τ_ε] ~ ε` while `V(ε) ~ ε/2`,

`A_ε(h)/V(ε) → 0` as `ε → 0`:

at small damping the damped and receiver responses become white. Together with the non-commuting
variance limits, the correlation structure commutes with the damping limit while the variance does
not.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Clock invisibility -/

/-- For squarefree-supported weights the Selberg coordinate of a non-squarefree mode vanishes. -/
theorem selbergMultiplesCoord_eq_zero_of_not_squarefree (N : ℕ) {c : ℕ → ℝ}
    (hc : ∀ d, ¬ Squarefree d → c d = 0) {e : ℕ} (he : ¬ Squarefree e) :
    selbergMultiplesCoord N c e = 0 :=
  sum_eq_zero fun d hd => by
    obtain ⟨k, rfl⟩ := (mem_filter.mp hd).2
    rw [hc _ fun h => he h.of_mul_left, zero_div]

/-- At a squarefree mode, lags with the same primes have the same gcd. -/
private theorem gcd_eq_of_primeFactors_eq {e h h' : ℕ} (he : Squarefree e) (hh : h ≠ 0)
    (hh' : h' ≠ 0) (hp : h.primeFactors = h'.primeFactors) : Nat.gcd e h = Nat.gcd e h' := by
  have he0 : e ≠ 0 := he.ne_zero
  refine (Nat.Squarefree.ext_iff (he.squarefree_of_dvd (Nat.gcd_dvd_left e h))
    (he.squarefree_of_dvd (Nat.gcd_dvd_left e h'))).mpr fun p hpp => ?_
  have key : p ∣ h ↔ p ∣ h' := by
    constructor
    · intro hph
      exact (Nat.mem_primeFactors.mp (hp ▸ Nat.mem_primeFactors.mpr ⟨hpp, hph, hh⟩)).2.1
    · intro hph
      exact (Nat.mem_primeFactors.mp (hp.symm ▸ Nat.mem_primeFactors.mpr ⟨hpp, hph, hh'⟩)).2.1
  rw [Nat.dvd_gcd_iff, Nat.dvd_gcd_iff, key]

/-- **Clock invisibility.** For every squarefree-supported weight and horizon, lags with the same
prime factors have the same complete-period covariance. -/
theorem periodCovariance_eq_of_primeFactors_eq (N : ℕ) {c : ℕ → ℝ}
    (hc : ∀ d, ¬ Squarefree d → c d = 0) {h h' : ℕ} (hh : h ≠ 0) (hh' : h' ≠ 0)
    (hp : h.primeFactors = h'.primeFactors) :
    TwoLagSieve.periodCovariance N c h = TwoLagSieve.periodCovariance N c h' := by
  rw [periodCovariance_eq_ramanujanLagWeight_diagonal, periodCovariance_eq_ramanujanLagWeight_diagonal]
  refine sum_congr rfl fun e _ => ?_
  by_cases he : Squarefree e
  · rw [ramanujanLagWeight_eq_of_gcd_eq (gcd_eq_of_primeFactors_eq he hh hh' hp)]
  · rw [selbergMultiplesCoord_eq_zero_of_not_squarefree N hc he]; ring

/-! ### Bounds on the Ramanujan coefficients -/

/-- `φ(e) = ∏_{p | e} (p - 1)` for squarefree `e`. -/
private theorem totient_eq_prod_of_squarefree {e : ℕ} (he : Squarefree e) :
    (Nat.totient e : ℝ) = ∏ p ∈ e.primeFactors, ((p : ℝ) - 1) := by
  have h := Nat.totient_mul_prod_primeFactors e
  rw [Nat.prod_primeFactors_of_squarefree he] at h
  have he0 : 0 < e := Nat.pos_of_ne_zero he.ne_zero
  have h' : Nat.totient e = ∏ p ∈ e.primeFactors, (p - 1) := by
    rw [mul_comm] at h; exact Nat.eq_of_mul_eq_mul_left he0 h
  rw [h', Nat.cast_prod]
  exact prod_congr rfl fun p hp => by
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.cast_one]

/-- `w_ε(e)² ≤ E[τ_ε]² μ²(e)/φ(e)²`. -/
theorem dampedRamanujanCoeff_sq_le {ε : ℝ} (hε : 0 < ε) (e : ℕ) :
    dampedRamanujanCoeff ε e ^ 2 ≤
      (RHTower.pmPowerDampedDivisorDensity ε).re ^ 2 *
        (RHTower.Sieve.sqfreeTotientInv e / (Nat.totient e : ℝ)) := by
  set ρ := (RHTower.pmPowerDampedDivisorDensity ε).re
  have hw : dampedRamanujanCoeff ε e =
      ρ * (moebius e : ℝ) / RHTower.pmPowerDampedRamanujanDenominator ε e := by
    rw [dampedRamanujanCoeff, RHTower.pmPowerDampedRamanujanWeight_eq_ofReal hε, Complex.ofReal_re]
  have hD := RHTower.pmPowerDampedRamanujanDenominator_pos hε e
  by_cases hsq : Squarefree e
  · have hφD : (Nat.totient e : ℝ) ≤ RHTower.pmPowerDampedRamanujanDenominator ε e := by
      rw [totient_eq_prod_of_squarefree hsq, RHTower.pmPowerDampedRamanujanDenominator]
      refine prod_le_prod (fun p hp => ?_) fun p hp => ?_
      · have h1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
        linarith
      · have h1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
        linarith [Real.self_le_rpow_of_one_le h1 (by linarith : (1 : ℝ) ≤ 1 + ε)]
    have hφ0 : 0 < Nat.totient e := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hsq.ne_zero)
    have hφ : (0 : ℝ) < Nat.totient e := by exact_mod_cast hφ0
    have hμ : (moebius e : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    have hsti : RHTower.Sieve.sqfreeTotientInv e / (Nat.totient e : ℝ) =
        1 / (Nat.totient e : ℝ) ^ 2 := by
      rw [RHTower.Sieve.sqfreeTotientInv_apply, if_pos hsq]; field_simp
    rw [hw, hsti, div_pow, mul_pow, hμ, mul_one, mul_one_div]
    exact div_le_div_of_nonneg_left (sq_nonneg ρ) (by positivity)
      (pow_le_pow_left₀ hφ.le hφD 2)
  · have h0 : (moebius e : ℝ) = 0 := by
      rw [moebius_eq_zero_of_not_squarefree hsq]; simp
    rw [hw, h0, mul_zero, zero_div, sq, zero_mul]
    exact mul_nonneg (sq_nonneg _) (div_nonneg (RHTower.Sieve.sqfreeTotientInv_nonneg e)
      (Nat.cast_nonneg _))

/-- `Σ_e μ²(e)/φ(e)²` converges, with sum at most `16`. -/
theorem summable_sqfreeTotientInv_div_totient :
    Summable (fun e : ℕ => RHTower.Sieve.sqfreeTotientInv e / (Nat.totient e : ℝ)) ∧
      ∑' e : ℕ, RHTower.Sieve.sqfreeTotientInv e / (Nat.totient e : ℝ) ≤ 16 := by
  have hnn : ∀ e : ℕ, 0 ≤ RHTower.Sieve.sqfreeTotientInv e / (Nat.totient e : ℝ) := fun e =>
    div_nonneg (RHTower.Sieve.sqfreeTotientInv_nonneg e) (Nat.cast_nonneg _)
  have hrange : ∀ n, ∑ e ∈ range n, RHTower.Sieve.sqfreeTotientInv e / (Nat.totient e : ℝ) ≤ 16 := by
    intro n
    calc ∑ e ∈ range n, RHTower.Sieve.sqfreeTotientInv e / (Nat.totient e : ℝ)
        ≤ ∑ e ∈ Icc 1 n, RHTower.Sieve.sqfreeTotientInv e / (Nat.totient e : ℝ) := by
          rw [← sum_filter_add_sum_filter_not (range n) (· = 0)]
          have h0 : ∑ e ∈ (range n).filter (· = 0),
              RHTower.Sieve.sqfreeTotientInv e / (Nat.totient e : ℝ) = 0 :=
            sum_eq_zero fun e he => by rw [(mem_filter.mp he).2]; simp
          rw [h0, zero_add]
          refine sum_le_sum_of_subset_of_nonneg (fun e he => ?_) fun e _ _ => hnn e
          simp only [mem_filter, mem_range] at he; simp only [mem_Icc]; omega
      _ ≤ 16 := RHTower.Sieve.sum_sqfreeTotientInv_div_totient_le n
  have hs := summable_of_sum_range_le hnn hrange
  exact ⟨hs, hs.tsum_le_of_sum_range_le hrange⟩

/-! ### The damped autocorrelation -/

/-- The limiting lag-`h` autocorrelation `A_ε(h) = Σ_{e ≥ 2} c_e(h) w_ε(e)²`. -/
def dampedAutocorrelation (ε : ℝ) (h : ℕ) : ℝ :=
  ∑' e : ℕ, if 2 ≤ e then ramanujanLagWeight h e * dampedRamanujanCoeff ε e ^ 2 else 0

private theorem abs_lag_term_le {ε : ℝ} (hε : 0 < ε) {h : ℕ} (hh : 1 ≤ h) (e : ℕ) :
    |(if 2 ≤ e then ramanujanLagWeight h e * dampedRamanujanCoeff ε e ^ 2 else 0)| ≤
      (∑ d ∈ h.divisors, (d : ℝ)) * ((RHTower.pmPowerDampedDivisorDensity ε).re ^ 2 *
        (RHTower.Sieve.sqfreeTotientInv e / (Nat.totient e : ℝ))) := by
  split_ifs
  · rw [abs_mul, abs_of_nonneg (sq_nonneg (dampedRamanujanCoeff ε e))]
    exact mul_le_mul (abs_ramanujanLagWeight_le_sigma hh e) (dampedRamanujanCoeff_sq_le hε e)
      (sq_nonneg _) (sum_nonneg fun d _ => Nat.cast_nonneg d)
  · rw [abs_zero]
    exact mul_nonneg (sum_nonneg fun d _ => Nat.cast_nonneg d)
      (mul_nonneg (sq_nonneg _) (div_nonneg (RHTower.Sieve.sqfreeTotientInv_nonneg e)
        (Nat.cast_nonneg _)))

/-- **Small autocorrelation.** `|A_ε(h)| ≤ 16 σ(h) E[τ_ε]²` for every lag `h ≥ 1`. -/
theorem abs_dampedAutocorrelation_le {ε : ℝ} (hε : 0 < ε) {h : ℕ} (hh : 1 ≤ h) :
    |dampedAutocorrelation ε h| ≤
      16 * (∑ d ∈ h.divisors, (d : ℝ)) * (RHTower.pmPowerDampedDivisorDensity ε).re ^ 2 := by
  obtain ⟨hs, hle⟩ := summable_sqfreeTotientInv_div_totient
  set σ := ∑ d ∈ h.divisors, (d : ℝ)
  set ρ := (RHTower.pmPowerDampedDivisorDensity ε).re
  set f : ℕ → ℝ := fun e =>
    if 2 ≤ e then ramanujanLagWeight h e * dampedRamanujanCoeff ε e ^ 2 else 0
  set g : ℕ → ℝ := fun e =>
    σ * (ρ ^ 2 * (RHTower.Sieve.sqfreeTotientInv e / (Nat.totient e : ℝ)))
  have hfg : ∀ e, ‖f e‖ ≤ g e := fun e => by
    rw [Real.norm_eq_abs]; exact abs_lag_term_le hε hh e
  have hg : Summable g := (hs.mul_left _).mul_left _
  have hfs : Summable f := Summable.of_norm_bounded hg hfg
  have hσ : 0 ≤ σ := sum_nonneg fun d _ => Nat.cast_nonneg d
  calc |dampedAutocorrelation ε h| = ‖∑' e, f e‖ := rfl
    _ ≤ ∑' e, ‖f e‖ := norm_tsum_le_tsum_norm hfs.norm
    _ ≤ ∑' e, g e := Summable.tsum_le_tsum hfg hfs.norm hg
    _ = σ * (ρ ^ 2 * ∑' e, RHTower.Sieve.sqfreeTotientInv e / (Nat.totient e : ℝ)) := by
        simp only [g]; rw [tsum_mul_left, tsum_mul_left]
    _ ≤ σ * (ρ ^ 2 * 16) := by gcongr
    _ = 16 * σ * ρ ^ 2 := by ring

/-- **Lag convergence.** `Cov_N(h; c_ε) → A_ε(h)` at every lag `h ≥ 1`. -/
theorem tendsto_periodCovariance_pmPowerDamped_lag {ε : ℝ} (hε : 0 < ε) {h : ℕ} (hh : 1 ≤ h) :
    Tendsto (fun N : ℕ => TwoLagSieve.periodCovariance N (pmPowerDampedRealWeight ε) h) atTop
      (𝓝 (dampedAutocorrelation ε h)) := by
  set Z := ∑' m : ℕ, (m : ℝ) ^ (-1 - ε)
  set σ := ∑ d ∈ h.divisors, (d : ℝ)
  have hσ : 0 ≤ σ := sum_nonneg fun d _ => Nat.cast_nonneg d
  set G : ℕ → ℕ → ℝ := fun N e =>
    if e ∈ Icc 2 N then ramanujanLagWeight h e *
      selbergMultiplesCoord N (pmPowerDampedRealWeight ε) e ^ 2 else 0
  have hfin : ∀ N, TwoLagSieve.periodCovariance N (pmPowerDampedRealWeight ε) h = ∑' e, G N e := by
    intro N
    rw [tsum_eq_sum (s := Icc 2 N) (fun e he => by simp only [G]; rw [if_neg he]),
      periodCovariance_eq_ramanujanLagWeight_diagonal]
    exact sum_congr rfl fun e he => by simp only [G]; rw [if_pos he]
  simp_rw [hfin]
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun e => σ * (Z ^ 2 * (e : ℝ) ^ (-2 - 2 * ε)))
    (((Real.summable_nat_rpow.mpr (by linarith)).mul_left _).mul_left _) (fun e => ?_) ?_
  · by_cases he : 2 ≤ e
    · refine ((tendsto_selbergMultiplesCoord_pmPowerDamped hε (e := e) (by omega)).pow 2
        |>.const_mul (ramanujanLagWeight h e)).congr' ?_ |>.trans (by rw [if_pos he])
      filter_upwards [eventually_ge_atTop e] with N hN
      simp only [G, mem_Icc, he, hN, and_self, if_true]
    · simp only [G, mem_Icc, he, false_and, if_false]
      exact tendsto_const_nhds
  · filter_upwards with N e
    simp only [G]
    split_ifs with he
    · have he0 : 0 < e := by have := (mem_Icc.mp he).1; omega
      have heR : (0 : ℝ) < e := by exact_mod_cast he0
      have hY : |selbergMultiplesCoord N (pmPowerDampedRealWeight ε) e| ≤ (e : ℝ) ^ (-1 - ε) * Z :=
        (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun d _ =>
          abs_pmPowerDampedRealWeight_div_le d).trans (sum_multiples_rpow_le hε N e he0))
      have hpow : ((e : ℝ) ^ (-1 - ε)) ^ 2 = (e : ℝ) ^ (-2 - 2 * ε) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul heR.le]; push_cast; ring_nf
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      calc |ramanujanLagWeight h e| * |selbergMultiplesCoord N (pmPowerDampedRealWeight ε) e| ^ 2
          ≤ σ * ((e : ℝ) ^ (-1 - ε) * Z) ^ 2 :=
            mul_le_mul (abs_ramanujanLagWeight_le_sigma hh e)
              (pow_le_pow_left₀ (abs_nonneg _) hY 2) (sq_nonneg _) hσ
        _ = σ * (Z ^ 2 * (e : ℝ) ^ (-2 - 2 * ε)) := by rw [mul_pow, hpow]; ring
    · rw [norm_zero]
      exact mul_nonneg hσ (mul_nonneg (sq_nonneg Z) (Real.rpow_nonneg (Nat.cast_nonneg e) _))

/-- **Receiver-row autocorrelation.** `Cov_{Q+1}(h; c_Q) = Σ_{2 ≤ e ≤ Q+1} c_e(h) w_ε(e)²`. -/
theorem periodCovariance_cofactor_lag_eq (ε : ℝ) (Q h : ℕ) :
    TwoLagSieve.periodCovariance (Q + 1) (pmCofactorDivisorWeight ε Q) h =
      ∑ e ∈ Icc 2 (Q + 1), ramanujanLagWeight h e * dampedRamanujanCoeff ε e ^ 2 := by
  rw [periodCovariance_eq_ramanujanLagWeight_diagonal]
  refine sum_congr rfl fun e he => ?_
  have he' : e ∈ Icc 1 (Q + 1) := by simp only [mem_Icc] at he ⊢; omega
  rw [selbergMultiplesCoord_pmCofactorDivisorWeight_of_mem ε he', dampedRamanujanCoeff]

/-- The receiver-row autocorrelation obeys the same bound at **every** cutoff. -/
theorem abs_periodCovariance_cofactor_lag_le {ε : ℝ} (hε : 0 < ε) (Q : ℕ) {h : ℕ} (hh : 1 ≤ h) :
    |TwoLagSieve.periodCovariance (Q + 1) (pmCofactorDivisorWeight ε Q) h| ≤
      16 * (∑ d ∈ h.divisors, (d : ℝ)) * (RHTower.pmPowerDampedDivisorDensity ε).re ^ 2 := by
  obtain ⟨hs, hle⟩ := summable_sqfreeTotientInv_div_totient
  rw [periodCovariance_cofactor_lag_eq]
  have hσ : 0 ≤ ∑ d ∈ h.divisors, (d : ℝ) := sum_nonneg fun d _ => Nat.cast_nonneg d
  calc |∑ e ∈ Icc 2 (Q + 1), ramanujanLagWeight h e * dampedRamanujanCoeff ε e ^ 2|
      ≤ ∑ e ∈ Icc 2 (Q + 1), (∑ d ∈ h.divisors, (d : ℝ)) *
          ((RHTower.pmPowerDampedDivisorDensity ε).re ^ 2 *
            (RHTower.Sieve.sqfreeTotientInv e / (Nat.totient e : ℝ))) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun e he => ?_)
        have := abs_lag_term_le hε hh e
        rwa [if_pos (mem_Icc.mp he).1] at this
    _ = (∑ d ∈ h.divisors, (d : ℝ)) * (RHTower.pmPowerDampedDivisorDensity ε).re ^ 2 *
          ∑ e ∈ Icc 2 (Q + 1), RHTower.Sieve.sqfreeTotientInv e / (Nat.totient e : ℝ) := by
        rw [mul_sum]; exact sum_congr rfl fun e _ => by ring
    _ ≤ (∑ d ∈ h.divisors, (d : ℝ)) * (RHTower.pmPowerDampedDivisorDensity ε).re ^ 2 * 16 := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hσ (sq_nonneg _))
        exact (hs.sum_le_tsum _ fun e _ => div_nonneg (RHTower.Sieve.sqfreeTotientInv_nonneg e)
          (Nat.cast_nonneg _)).trans hle
    _ = _ := by ring

/-- **Small-damping whiteness.** At every lag `h ≥ 1`, `A_ε(h)/V(ε) → 0` as `ε → 0⁺`; uniformly in
the cutoff, the receiver row's normalized correlation `Cov_{Q+1}(h; c_Q)/V(ε)` is bounded by a
quantity tending to zero. -/
theorem tendsto_correlationBound_div_variance {h : ℕ} :
    Tendsto (fun ε : ℝ => 16 * (∑ d ∈ h.divisors, (d : ℝ)) *
        (RHTower.pmPowerDampedDivisorDensity ε).re ^ 2 / RHTower.pmPowerDampedDivisorVariance ε)
      (𝓝[>] 0) (𝓝 0) := by
  have hρ := RHTower.tendsto_pmPowerDampedDivisorDensity_re_div_parameter
  have hV := RHTower.tendsto_pmPowerDampedDivisorVariance_div_parameter
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h1 := (((hρ.pow 2).mul he).div hV (by norm_num)).const_mul (16 * ∑ d ∈ h.divisors, (d : ℝ))
  simp only [one_pow, zero_div, mul_zero] at h1
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε ≠ 0 := ne_of_gt hε
  simp only [Pi.div_apply]
  field_simp

theorem tendsto_dampedAutocorrelation_div_variance {h : ℕ} (hh : 1 ≤ h) :
    Tendsto (fun ε : ℝ => dampedAutocorrelation ε h / RHTower.pmPowerDampedDivisorVariance ε)
      (𝓝[>] 0) (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (tendsto_correlationBound_div_variance (h := h))
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hV : 0 < RHTower.pmPowerDampedDivisorVariance ε := RHTower.pmPowerDampedDivisorVariance_pos hε
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hV]
  exact div_le_div_of_nonneg_right (abs_dampedAutocorrelation_le hε hh) hV.le

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics

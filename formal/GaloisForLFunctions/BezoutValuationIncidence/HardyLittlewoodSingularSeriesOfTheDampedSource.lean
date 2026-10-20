import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedAutocorrelationAndClockInvisibility
import GaloisForLFunctions.BezoutValuationIncidence.UniformLagWindowCovarianceAtQuadraticOrder
import GaloisForLFunctions.BezoutValuationIncidence.MultiLagCovarianceConeFiniteGeneration

/-!
# The damped source carries the Hardy–Littlewood singular series

The limiting lag-`h` covariance of the power-damped source is `A_ε(h) = Σ_{e ≥ 2} c_e(h) w_ε(e)²`
with `w_ε(e) = ρ_ε μ(e)/D_ε(e)`, `ρ_ε = 1/ζ(1+ε)` and `D_ε(e) = ∏_{p ∣ e}(p^{1+ε} - 1)`. Dividing by
`ρ_ε²` removes the density. As `ε → 0` we have `D_ε(e) → φ(e)` for squarefree `e`, dominated by
`σ(h) μ²(e)/φ(e)²`. Hence

`(ρ_ε² + A_ε(h))/ρ_ε² → 𝔖(h) = Σ_{q ≥ 1} μ²(q) c_q(h)/φ(q)²`,

the Hardy–Littlewood singular series of prime pairs at gap `h`. The same limit holds jointly in
`(ε, Q)` for the lag covariances of the receiver rows. The series factors over primes:

`𝔖(h) = ∏_p (1 + c_p(h)/(p-1)²)`, with `c_p(h) = p - 1` if `p ∣ h` and `-1` otherwise.

So `𝔖(h) = 0` for odd `h`, because the factor at `2` is `1 - 1 = 0`, and `𝔖(h) > 0` for even `h`.

Relative to the variance `V(ε) ~ ε/2` the damped source is white at small damping (`A_ε(h)/V → 0`).
Relative to its squared density `ρ_ε² ~ ε²`, its lag correlations are those predicted for
`Λ(n)Λ(n+h)`; this is consistent with `τ_ε(n)/ε → Λ(n)`. The limits are taken in the order
period first, then damping. This says nothing about the actual prime-pair correlations.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-! ## §1. The singular series -/

/-- The term `c_q(h) μ²(q)/φ(q)²`. -/
def singularSeriesTerm (h q : ℕ) : ℝ :=
  ramanujanLagWeight h q * (RHTower.Sieve.sqfreeTotientInv q / (Nat.totient q : ℝ))

/-- The Hardy–Littlewood singular series `𝔖(h) = Σ_q μ²(q) c_q(h)/φ(q)²`. -/
def hardyLittlewoodSingularSeries (h : ℕ) : ℝ := ∑' q, singularSeriesTerm h q

theorem sqfreeTotientInv_div_totient_nonneg (q : ℕ) :
    0 ≤ RHTower.Sieve.sqfreeTotientInv q / (Nat.totient q : ℝ) :=
  div_nonneg (RHTower.Sieve.sqfreeTotientInv_nonneg q) (Nat.cast_nonneg _)

theorem abs_singularSeriesTerm_le {h : ℕ} (hh : 1 ≤ h) (q : ℕ) :
    |singularSeriesTerm h q| ≤
      (∑ d ∈ h.divisors, (d : ℝ)) * (RHTower.Sieve.sqfreeTotientInv q / (Nat.totient q : ℝ)) := by
  rw [singularSeriesTerm, abs_mul, abs_of_nonneg (sqfreeTotientInv_div_totient_nonneg q)]
  exact mul_le_mul_of_nonneg_right (abs_ramanujanLagWeight_le_sigma hh q)
    (sqfreeTotientInv_div_totient_nonneg q)

theorem summable_singularSeriesTerm {h : ℕ} (hh : 1 ≤ h) :
    Summable fun q => ‖singularSeriesTerm h q‖ :=
  Summable.of_nonneg_of_le (fun q => norm_nonneg _)
    (fun q => (Real.norm_eq_abs _).trans_le (abs_singularSeriesTerm_le hh q))
    (summable_sqfreeTotientInv_div_totient.1.mul_left _)

theorem singularSeriesTerm_zero (h : ℕ) : singularSeriesTerm h 0 = 0 := by
  simp [singularSeriesTerm, RHTower.Sieve.sqfreeTotientInv_apply]

theorem ramanujanLagWeight_one (h : ℕ) : ramanujanLagWeight h 1 = 1 := by
  rw [ramanujanLagWeight_eq_ramanujanLagCoefficient, ramanujanLagCoefficient]
  simp [moebiusReal]

theorem singularSeriesTerm_one (h : ℕ) : singularSeriesTerm h 1 = 1 := by
  simp [singularSeriesTerm, ramanujanLagWeight_one, RHTower.Sieve.sqfreeTotientInv_apply]

/-- `𝔖(h) - 1` is the series over moduli `q ≥ 2`. -/
theorem hasSum_singularSeriesTerm_ge_two {h : ℕ} (hh : 1 ≤ h) :
    HasSum (fun q => if 2 ≤ q then singularSeriesTerm h q else 0)
      (hardyLittlewoodSingularSeries h - 1) := by
  have hS := (summable_singularSeriesTerm hh).of_norm.hasSum
  have hlow : HasSum (fun q => if q < 2 then singularSeriesTerm h q else 0) 1 := by
    have h : HasSum (fun q => if q < 2 then singularSeriesTerm h q else 0)
        (∑ q ∈ range 2, if q < 2 then singularSeriesTerm h q else 0) :=
      hasSum_sum_of_ne_finset_zero fun q hq => by rw [if_neg (by simpa using hq)]
    simpa [sum_range_succ, singularSeriesTerm_zero, singularSeriesTerm_one] using h
  refine (hS.sub hlow).congr_fun fun q => ?_
  by_cases hq : 2 ≤ q
  · simp [hq, not_lt.mpr hq]
  · simp [hq, lt_of_not_ge hq]

/-! ## §2. The zero-damping limit of the normalized Ramanujan coefficients -/

theorem totient_eq_prod_sub_one_of_squarefree {e : ℕ} (he : Squarefree e) :
    (Nat.totient e : ℝ) = ∏ p ∈ e.primeFactors, ((p : ℝ) - 1) := by
  have h := Nat.totient_mul_prod_primeFactors e
  rw [Nat.prod_primeFactors_of_squarefree he] at h
  have he0 : 0 < e := Nat.pos_of_ne_zero he.ne_zero
  have h' : Nat.totient e = ∏ p ∈ e.primeFactors, (p - 1) := by
    rw [mul_comm] at h
    exact Nat.eq_of_mul_eq_mul_left he0 h
  rw [h', Nat.cast_prod]
  exact prod_congr rfl fun p hp => by
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.cast_one]

/-- The normalized coefficient `w_ε(e)/ρ_ε = μ(e)/D_ε(e)`. -/
theorem dampedRamanujanCoeff_div_density {ε : ℝ} (hε : 0 < ε) (e : ℕ) :
    dampedRamanujanCoeff ε e / (RHTower.pmPowerDampedDivisorDensity ε).re =
      (moebius e : ℝ) / RHTower.pmPowerDampedRamanujanDenominator ε e := by
  have hρ := RHTower.pmPowerDampedDivisorDensity_re_pos hε
  rw [dampedRamanujanCoeff, RHTower.pmPowerDampedRamanujanWeight_eq_ofReal hε, Complex.ofReal_re]
  field_simp

theorem continuous_pmPowerDampedRamanujanDenominator (e : ℕ) :
    Continuous fun ε => RHTower.pmPowerDampedRamanujanDenominator ε e := by
  unfold RHTower.pmPowerDampedRamanujanDenominator
  refine continuous_finsetProd _ fun p hp => ?_
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  exact (continuous_const.rpow (continuous_const.add continuous_id)
    fun _ => Or.inl hp0.ne').sub continuous_const

/-- `(μ(e)/D_ε(e))² → μ²(e)/φ(e)²` as `ε → 0`. -/
theorem tendsto_moebius_div_denominator_sq (e : ℕ) :
    Tendsto (fun ε => ((moebius e : ℝ) / RHTower.pmPowerDampedRamanujanDenominator ε e) ^ 2)
      (𝓝[>] 0) (𝓝 (RHTower.Sieve.sqfreeTotientInv e / (Nat.totient e : ℝ))) := by
  have hD0 : RHTower.pmPowerDampedRamanujanDenominator 0 e =
      ∏ p ∈ e.primeFactors, ((p : ℝ) - 1) := by
    unfold RHTower.pmPowerDampedRamanujanDenominator
    exact prod_congr rfl fun p _ => by rw [add_zero, Real.rpow_one]
  have hpos : 0 < RHTower.pmPowerDampedRamanujanDenominator 0 e := by
    rw [hD0]
    exact prod_pos fun p hp => by
      have : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
      linarith
  have hD : Tendsto (fun ε => RHTower.pmPowerDampedRamanujanDenominator ε e) (𝓝 0)
      (𝓝 (RHTower.pmPowerDampedRamanujanDenominator 0 e)) :=
    (continuous_pmPowerDampedRamanujanDenominator e).continuousAt.tendsto
  have h := ((tendsto_const_nhds (x := (moebius e : ℝ))).div hD hpos.ne').pow 2
  refine (h.mono_left nhdsWithin_le_nhds).trans_eq ?_
  by_cases he : Squarefree e
  · rw [hD0, ← totient_eq_prod_sub_one_of_squarefree he, RHTower.Sieve.sqfreeTotientInv_apply,
      if_pos he, div_pow,
      show (moebius e : ℝ) ^ 2 = 1 by exact_mod_cast moebius_sq_eq_one_of_squarefree he]
    field_simp
  · rw [moebius_eq_zero_of_not_squarefree he, RHTower.Sieve.sqfreeTotientInv_apply, if_neg he]
    simp

/-- `(μ(e)/D_ε(e))² ≤ μ²(e)/φ(e)²` for `ε > 0`. -/
theorem moebius_div_denominator_sq_le {ε : ℝ} (hε : 0 < ε) (e : ℕ) :
    ((moebius e : ℝ) / RHTower.pmPowerDampedRamanujanDenominator ε e) ^ 2 ≤
      RHTower.Sieve.sqfreeTotientInv e / (Nat.totient e : ℝ) := by
  have hρ := RHTower.pmPowerDampedDivisorDensity_re_pos hε
  have h1 := dampedRamanujanCoeff_sq_le hε e
  rw [← dampedRamanujanCoeff_div_density hε, div_pow, div_le_iff₀ (pow_pos hρ 2)]
  linarith

/-! ## §3. The damped source and the receiver rows -/

/-- **The damped source carries the singular series.** `A_ε(h)/ρ_ε² → 𝔖(h) - 1` as `ε → 0`. -/
theorem tendsto_dampedAutocorrelation_div_density_sq {h : ℕ} (hh : 1 ≤ h) :
    Tendsto (fun ε => dampedAutocorrelation ε h / (RHTower.pmPowerDampedDivisorDensity ε).re ^ 2)
      (𝓝[>] 0) (𝓝 (hardyLittlewoodSingularSeries h - 1)) := by
  set σ := ∑ d ∈ h.divisors, (d : ℝ)
  have hσ : 0 ≤ σ := sum_nonneg fun d _ => Nat.cast_nonneg d
  set F : ℝ → ℕ → ℝ := fun ε e => if 2 ≤ e then ramanujanLagWeight h e *
      ((moebius e : ℝ) / RHTower.pmPowerDampedRamanujanDenominator ε e) ^ 2 else 0
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ)) (f := F)
    (g := fun e => if 2 ≤ e then singularSeriesTerm h e else 0)
    (bound := fun e => σ * (RHTower.Sieve.sqfreeTotientInv e / (Nat.totient e : ℝ)))
    (summable_sqfreeTotientInv_div_totient.1.mul_left σ) (fun e => ?_) ?_
  · rw [(hasSum_singularSeriesTerm_ge_two hh).tsum_eq] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [dampedAutocorrelation, ← tsum_div_const]
    refine tsum_congr fun e => ?_
    simp only [F]
    split_ifs
    · rw [← dampedRamanujanCoeff_div_density hε, div_pow, mul_div_assoc]
    · rw [zero_div]
  · simp only [F]
    split_ifs
    · exact (tendsto_moebius_div_denominator_sq e).const_mul _
    · exact tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε e
    simp only [F]
    split_ifs
    · rw [Real.norm_eq_abs, abs_mul, abs_sq]
      exact mul_le_mul (abs_ramanujanLagWeight_le_sigma hh e) (moebius_div_denominator_sq_le hε e)
        (sq_nonneg _) hσ
    · rw [norm_zero]
      exact mul_nonneg hσ (sqfreeTotientInv_div_totient_nonneg e)

/-- **Uncentred form.** The lag-`h` product mean over the squared density tends to `𝔖(h)`. -/
theorem tendsto_lagProductMean_div_density_sq {h : ℕ} (hh : 1 ≤ h) :
    Tendsto (fun ε => ((RHTower.pmPowerDampedDivisorDensity ε).re ^ 2 + dampedAutocorrelation ε h) /
        (RHTower.pmPowerDampedDivisorDensity ε).re ^ 2)
      (𝓝[>] 0) (𝓝 (hardyLittlewoodSingularSeries h)) := by
  have h1 := (tendsto_dampedAutocorrelation_div_density_sq hh).const_add 1
  rw [add_sub_cancel] at h1
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hρ := RHTower.pmPowerDampedDivisorDensity_re_pos hε
  field_simp

/-- **The receiver rows carry the singular series**, jointly in the damping and the cutoff:
`Cov_{Q+1}(h; c_Q)/ρ_ε² → 𝔖(h) - 1` as `ε → 0` and `Q → ∞`. -/
theorem tendsto_periodCovariance_cofactor_div_density_sq {h : ℕ} (hh : 1 ≤ h) :
    Tendsto (fun x : ℝ × ℕ => TwoLagSieve.periodCovariance (x.2 + 1)
        (pmCofactorDivisorWeight x.1 x.2) h / (RHTower.pmPowerDampedDivisorDensity x.1).re ^ 2)
      ((𝓝[>] 0) ×ˢ atTop) (𝓝 (hardyLittlewoodSingularSeries h - 1)) := by
  set σ := ∑ d ∈ h.divisors, (d : ℝ)
  have hσ : 0 ≤ σ := sum_nonneg fun d _ => Nat.cast_nonneg d
  set F : ℝ × ℕ → ℕ → ℝ := fun x e => if e ∈ Icc 2 (x.2 + 1) then ramanujanLagWeight h e *
      ((moebius e : ℝ) / RHTower.pmPowerDampedRamanujanDenominator x.1 e) ^ 2 else 0
  have hpos : ∀ᶠ x : ℝ × ℕ in (𝓝[>] 0) ×ˢ atTop, 0 < x.1 :=
    Filter.Eventually.prod_inl (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ))) _
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := (𝓝[>] (0 : ℝ)) ×ˢ atTop) (f := F)
    (g := fun e => if 2 ≤ e then singularSeriesTerm h e else 0)
    (bound := fun e => σ * (RHTower.Sieve.sqfreeTotientInv e / (Nat.totient e : ℝ)))
    (summable_sqfreeTotientInv_div_totient.1.mul_left σ) (fun e => ?_) ?_
  · rw [(hasSum_singularSeriesTerm_ge_two hh).tsum_eq] at hlim
    refine hlim.congr' ?_
    filter_upwards [hpos] with x hx
    rw [periodCovariance_cofactor_lag_eq, sum_div,
      tsum_eq_sum (s := Icc 2 (x.2 + 1)) fun e he => by simp only [F]; rw [if_neg he]]
    refine sum_congr rfl fun e he => ?_
    simp only [F]
    rw [if_pos he, ← dampedRamanujanCoeff_div_density hx, div_pow, mul_div_assoc]
  · by_cases he : 2 ≤ e
    · simp only [he, if_true]
      have hconv : Tendsto (fun x : ℝ × ℕ => ramanujanLagWeight h e *
          ((moebius e : ℝ) / RHTower.pmPowerDampedRamanujanDenominator x.1 e) ^ 2)
          ((𝓝[>] 0) ×ˢ atTop) (𝓝 (singularSeriesTerm h e)) :=
        ((tendsto_moebius_div_denominator_sq e).comp tendsto_fst).const_mul _
      refine hconv.congr' ?_
      filter_upwards [Filter.Eventually.prod_inr (eventually_ge_atTop e) (𝓝[>] (0 : ℝ))] with x hx
      simp only [F, Function.comp_apply]
      rw [if_pos (mem_Icc.mpr ⟨he, by omega⟩)]
    · simp only [he, if_false]
      refine tendsto_const_nhds.congr fun x => ?_
      simp only [F]
      rw [if_neg (fun hm => he (mem_Icc.mp hm).1)]
  · filter_upwards [hpos] with x hx e
    simp only [F]
    split_ifs
    · rw [Real.norm_eq_abs, abs_mul, abs_sq]
      exact mul_le_mul (abs_ramanujanLagWeight_le_sigma hh e) (moebius_div_denominator_sq_le hx e)
        (sq_nonneg _) hσ
    · rw [norm_zero]
      exact mul_nonneg hσ (sqfreeTotientInv_div_totient_nonneg e)

/-! ## §4. The Euler product -/

theorem ramanujanLagWeight_prime {p : ℕ} (hp : p.Prime) (h : ℕ) :
    ramanujanLagWeight h p = (if p ∣ h then (p : ℝ) else 0) - 1 := by
  rw [ramanujanLagWeight_eq_ramanujanLagCoefficient, ramanujanLagCoefficient, hp.divisors,
    sum_insert (by simp [hp.one_lt.ne]), sum_singleton]
  simp [moebiusReal, Nat.div_self hp.pos, moebius_apply_prime hp]
  ring

theorem singularSeriesTerm_mul_of_coprime (h : ℕ) {m n : ℕ} (hmn : m.Coprime n) :
    singularSeriesTerm h (m * n) = singularSeriesTerm h m * singularSeriesTerm h n := by
  unfold singularSeriesTerm
  rw [ramanujanLagWeight_mul_of_coprime h hmn,
    RHTower.Sieve.isMultiplicative_sqfreeTotientInv.map_mul_of_coprime hmn, Nat.totient_mul hmn]
  push_cast
  ring

/-- The local factor at `p` is `1 + c_p(h)/(p-1)²`. -/
theorem singularSeriesTerm_prime_pow_eq_zero {p : ℕ} (hp : p.Prime) (h : ℕ) {e : ℕ}
    (he : 2 ≤ e) : singularSeriesTerm h (p ^ e) = 0 := by
  rw [singularSeriesTerm, RHTower.Sieve.sqfreeTotientInv_apply,
    if_neg (fun hsq => by
      rw [Nat.squarefree_pow_iff hp.ne_one (by omega)] at hsq
      omega)]
  simp

theorem tsum_singularSeriesTerm_prime_pow {p : ℕ} (hp : p.Prime) (h : ℕ) :
    ∑' e, singularSeriesTerm h (p ^ e) = 1 + ramanujanLagWeight h p / ((p : ℝ) - 1) ^ 2 := by
  rw [tsum_eq_sum (s := range 2) fun e he =>
    singularSeriesTerm_prime_pow_eq_zero hp h (by simp at he; omega)]
  · have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    simp only [sum_range_succ, range_zero, sum_empty, zero_add, pow_zero, pow_one,
      singularSeriesTerm_one]
    rw [singularSeriesTerm, RHTower.Sieve.sqfreeTotientInv_apply, if_pos hp.squarefree,
      Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
    field_simp

/-- **The Euler product.** `𝔖(h) = ∏_p (1 + c_p(h)/(p-1)²)`. -/
theorem hasProd_hardyLittlewoodSingularSeries {h : ℕ} (hh : 1 ≤ h) :
    HasProd (fun p : Nat.Primes => 1 + ramanujanLagWeight h p / ((p : ℝ) - 1) ^ 2)
      (hardyLittlewoodSingularSeries h) := by
  have hE := EulerProduct.eulerProduct_hasProd (f := singularSeriesTerm h) (singularSeriesTerm_one h)
    (fun hmn => singularSeriesTerm_mul_of_coprime h hmn) (summable_singularSeriesTerm hh)
    (singularSeriesTerm_zero h)
  have hf : (fun p : Nat.Primes => ∑' e, singularSeriesTerm h ((p : ℕ) ^ e)) =
      fun p : Nat.Primes => 1 + ramanujanLagWeight h p / ((p : ℝ) - 1) ^ 2 :=
    funext fun p => tsum_singularSeriesTerm_prime_pow p.prop h
  rw [hf] at hE
  exact hE

/-- **Odd gaps.** `𝔖(h) = 0` for odd `h`: the factor at `2` vanishes. -/
theorem hardyLittlewoodSingularSeries_eq_zero_of_odd {h : ℕ} (hh : 1 ≤ h) (hodd : ¬ 2 ∣ h) :
    hardyLittlewoodSingularSeries h = 0 := by
  refine (hasProd_hardyLittlewoodSingularSeries hh).unique
    (hasProd_zero_of_exists_eq_zero ⟨⟨2, Nat.prime_two⟩, ?_⟩)
  simp [ramanujanLagWeight_prime Nat.prime_two, hodd]
  norm_num

/-- **Even gaps.** `𝔖(h) > 0` for even `h`. -/
theorem hardyLittlewoodSingularSeries_pos_of_even {h : ℕ} (hh : 1 ≤ h) (heven : 2 ∣ h) :
    0 < hardyLittlewoodSingularSeries h := by
  set a : Nat.Primes → ℝ := fun p => ramanujanLagWeight h p / ((p : ℝ) - 1) ^ 2
  have hfac : ∀ p : Nat.Primes, 0 < 1 + a p := by
    intro p
    have hp := p.prop
    have hp1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast hp.one_lt
    have hsq : 0 < ((p : ℕ) - 1 : ℝ) ^ 2 := by positivity
    simp only [a, ramanujanLagWeight_prime hp]
    by_cases hdiv : (p : ℕ) ∣ h
    · rw [if_pos hdiv]
      have : 0 ≤ ((p : ℕ) - 1 : ℝ) / ((p : ℕ) - 1 : ℝ) ^ 2 := by positivity
      linarith
    · rw [if_neg hdiv, zero_sub]
      have hp3 : (3 : ℝ) ≤ (p : ℕ) := by
        have h2 : (p : ℕ) ≠ 2 := fun h2 => hdiv (h2 ▸ heven)
        have := hp.two_le
        exact_mod_cast (show 3 ≤ (p : ℕ) by omega)
      have hb : ((p : ℕ) - 1 : ℝ) ^ 2 ≥ 4 := by nlinarith
      rw [neg_div]
      have : 1 / ((p : ℕ) - 1 : ℝ) ^ 2 ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hb
      linarith
  have hsum : Summable a := by
    set σ := ∑ d ∈ h.divisors, (d : ℝ)
    have hs : Summable fun p : Nat.Primes => 4 * σ * (1 / ((p : ℕ) : ℝ) ^ 2) :=
      ((Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective
        Subtype.val_injective).mul_left _
    refine Summable.of_norm_bounded hs fun p => ?_
    have hp := p.prop
    have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast hp.two_le
    have hc := abs_ramanujanLagWeight_le_sigma hh (p : ℕ)
    have hden : ((p : ℕ) : ℝ) ^ 2 ≤ 4 * ((p : ℕ) - 1 : ℝ) ^ 2 := by nlinarith
    have hpos : 0 < ((p : ℕ) - 1 : ℝ) ^ 2 := by nlinarith
    simp only [a, Real.norm_eq_abs, abs_div, abs_of_pos hpos, Function.comp_apply]
    rw [div_le_iff₀ hpos]
    calc |ramanujanLagWeight h p| ≤ σ := hc
      _ = 4 * σ * (1 / ((p : ℕ) : ℝ) ^ 2) * (((p : ℕ) : ℝ) ^ 2 / 4) := by field_simp
      _ ≤ 4 * σ * (1 / ((p : ℕ) : ℝ) ^ 2) * ((p : ℕ) - 1 : ℝ) ^ 2 := by
          have hσ : 0 ≤ σ := sum_nonneg fun d _ => Nat.cast_nonneg d
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
  have hprod := hasProd_hardyLittlewoodSingularSeries hh
  rw [← hprod.tprod_eq, ← Real.rexp_tsum_eq_tprod hfac
    (Real.summable_log_one_add_of_summable hsum)]
  exact Real.exp_pos _

end

end GaloisForLFunctions.BezoutValuationIncidence

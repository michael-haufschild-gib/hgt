import GaloisForLFunctions.BezoutValuationIncidence.HardyLittlewoodSingularSeriesOfTheDampedSource
import GaloisForLFunctions.BezoutValuationIncidence.MobiusVasyuninFormulaForThePronicGramAtAllModuli

/-!
# The exact damped singular series and Gallagher's sum as a prefix discrepancy

For every damping `ε > 0`, the normalized lag product mean of the damped source is an Euler product:

`(ρ_ε² + A_ε(h))/ρ_ε² = 𝔖_ε(h) = Σ_q c_q(h) μ²(q)/D_ε(q)² = ∏_p (1 + c_p(h)/(p^{1+ε} - 1)²)`,

with `D_ε(q) = ∏_{p ∣ q}(p^{1+ε} - 1)`. The damped singular series `𝔖_ε(h)` tends to `𝔖(h)` as
`ε → 0`. Its local factor at `2` is `1 - 1/(2^{1+ε} - 1)²` for odd `h`. That factor is positive for
`ε > 0` and vanishes only in the limit, so odd gaps are suppressed continuously.

Summing over lags turns Ramanujan sums into Ramanujan primitives. Hence

`Σ_{h ≤ H} A_ε(h) = Σ_{e ≥ 2} w_ε(e)² R_e(H)`.

This is the prefix discrepancy at `H` of the row whose Selberg coordinates are the squares
`w_ε(e)²` of the source's own coordinates. At zero damping,

`Σ_{h ≤ H} (𝔖(h) - 1) = Σ_{q ≥ 2} (μ²(q)/φ(q)²) R_q(H)`.

So Gallagher's singular-series sum, whose size governs the variance of primes in short intervals,
is the prefix discrepancy of the row with Selberg coordinates `μ²(q)/φ(q)²`.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-! ## §1. The damped singular series -/

/-- The term `c_q(h) μ²(q)/D_ε(q)²`. -/
def dampedSingularSeriesTerm (ε : ℝ) (h q : ℕ) : ℝ :=
  ramanujanLagWeight h q * ((moebius q : ℝ) / RHTower.pmPowerDampedRamanujanDenominator ε q) ^ 2

/-- The damped singular series `𝔖_ε(h) = Σ_q c_q(h) μ²(q)/D_ε(q)²`. -/
def dampedSingularSeries (ε : ℝ) (h : ℕ) : ℝ := ∑' q, dampedSingularSeriesTerm ε h q

theorem dampedSingularSeriesTerm_zero (ε : ℝ) (h : ℕ) : dampedSingularSeriesTerm ε h 0 = 0 := by
  simp [dampedSingularSeriesTerm]

theorem dampedSingularSeriesTerm_one (ε : ℝ) (h : ℕ) : dampedSingularSeriesTerm ε h 1 = 1 := by
  simp [dampedSingularSeriesTerm, RHTower.pmPowerDampedRamanujanDenominator]

theorem abs_dampedSingularSeriesTerm_le {ε : ℝ} (hε : 0 < ε) {h : ℕ} (hh : 1 ≤ h) (q : ℕ) :
    |dampedSingularSeriesTerm ε h q| ≤
      (∑ d ∈ h.divisors, (d : ℝ)) * (RHTower.Sieve.sqfreeTotientInv q / (Nat.totient q : ℝ)) := by
  rw [dampedSingularSeriesTerm, abs_mul, abs_sq]
  exact mul_le_mul (abs_ramanujanLagWeight_le_sigma hh q) (moebius_div_denominator_sq_le hε q)
    (sq_nonneg _) (sum_nonneg fun d _ => Nat.cast_nonneg d)

theorem summable_dampedSingularSeriesTerm {ε : ℝ} (hε : 0 < ε) {h : ℕ} (hh : 1 ≤ h) :
    Summable fun q => ‖dampedSingularSeriesTerm ε h q‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun q => (Real.norm_eq_abs _).trans_le (abs_dampedSingularSeriesTerm_le hε hh q))
    (summable_sqfreeTotientInv_div_totient.1.mul_left _)

theorem pmPowerDampedRamanujanDenominator_mul_of_coprime (ε : ℝ) {m n : ℕ} (hmn : m.Coprime n) :
    RHTower.pmPowerDampedRamanujanDenominator ε (m * n) =
      RHTower.pmPowerDampedRamanujanDenominator ε m * RHTower.pmPowerDampedRamanujanDenominator ε n := by
  unfold RHTower.pmPowerDampedRamanujanDenominator
  rw [Nat.Coprime.primeFactors_mul hmn, prod_union hmn.disjoint_primeFactors]

theorem dampedSingularSeriesTerm_mul_of_coprime (ε : ℝ) (h : ℕ) {m n : ℕ} (hmn : m.Coprime n) :
    dampedSingularSeriesTerm ε h (m * n) =
      dampedSingularSeriesTerm ε h m * dampedSingularSeriesTerm ε h n := by
  unfold dampedSingularSeriesTerm
  rw [ramanujanLagWeight_mul_of_coprime h hmn, pmPowerDampedRamanujanDenominator_mul_of_coprime ε hmn,
    isMultiplicative_moebius.map_mul_of_coprime hmn]
  push_cast
  ring

/-- The local factor at `p` is `1 + c_p(h)/(p^{1+ε} - 1)²`. -/
theorem tsum_dampedSingularSeriesTerm_prime_pow (ε : ℝ) {p : ℕ} (hp : p.Prime) (h : ℕ) :
    ∑' e, dampedSingularSeriesTerm ε h (p ^ e) =
      1 + ramanujanLagWeight h p / ((p : ℝ) ^ (1 + ε) - 1) ^ 2 := by
  rw [tsum_eq_sum (s := range 2) fun e he => by
    have he2 : 2 ≤ e := by simp at he; omega
    rw [dampedSingularSeriesTerm, moebius_eq_zero_of_not_squarefree (fun hsq => by
      rw [Nat.squarefree_pow_iff hp.ne_one (by omega)] at hsq
      omega)]
    simp]
  rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, dampedSingularSeriesTerm_one,
    dampedSingularSeriesTerm, moebius_apply_prime hp, RHTower.pmPowerDampedRamanujanDenominator,
    hp.primeFactors, prod_singleton]
  push_cast
  rw [neg_div, neg_sq, div_pow, one_pow, mul_one_div]

/-- **The damped Euler product.** `𝔖_ε(h) = ∏_p (1 + c_p(h)/(p^{1+ε} - 1)²)` for `ε > 0`. -/
theorem hasProd_dampedSingularSeries {ε : ℝ} (hε : 0 < ε) {h : ℕ} (hh : 1 ≤ h) :
    HasProd (fun p : Nat.Primes => 1 + ramanujanLagWeight h p / (((p : ℕ) : ℝ) ^ (1 + ε) - 1) ^ 2)
      (dampedSingularSeries ε h) := by
  have hE := EulerProduct.eulerProduct_hasProd (f := dampedSingularSeriesTerm ε h)
    (dampedSingularSeriesTerm_one ε h) (fun hmn => dampedSingularSeriesTerm_mul_of_coprime ε h hmn)
    (summable_dampedSingularSeriesTerm hε hh) (dampedSingularSeriesTerm_zero ε h)
  have hf : (fun p : Nat.Primes => ∑' e, dampedSingularSeriesTerm ε h ((p : ℕ) ^ e)) =
      fun p : Nat.Primes => 1 + ramanujanLagWeight h p / (((p : ℕ) : ℝ) ^ (1 + ε) - 1) ^ 2 :=
    funext fun p => tsum_dampedSingularSeriesTerm_prime_pow ε p.prop h
  rw [hf] at hE
  exact hE

/-! ## §2. The damped source realizes the damped singular series -/

theorem dampedAutocorrelation_div_density_sq_eq {ε : ℝ} (hε : 0 < ε) (h : ℕ) :
    dampedAutocorrelation ε h / (RHTower.pmPowerDampedDivisorDensity ε).re ^ 2 =
      ∑' e, if 2 ≤ e then dampedSingularSeriesTerm ε h e else 0 := by
  rw [dampedAutocorrelation, ← tsum_div_const]
  refine tsum_congr fun e => ?_
  split_ifs
  · rw [dampedSingularSeriesTerm, ← dampedRamanujanCoeff_div_density hε, div_pow, mul_div_assoc]
  · rw [zero_div]

/-- **Exact damped law.** `(ρ_ε² + A_ε(h))/ρ_ε² = 𝔖_ε(h)` for every `ε > 0`. -/
theorem lagProductMean_div_density_sq_eq {ε : ℝ} (hε : 0 < ε) {h : ℕ} (hh : 1 ≤ h) :
    ((RHTower.pmPowerDampedDivisorDensity ε).re ^ 2 + dampedAutocorrelation ε h) /
        (RHTower.pmPowerDampedDivisorDensity ε).re ^ 2 = dampedSingularSeries ε h := by
  have hρ := RHTower.pmPowerDampedDivisorDensity_re_pos hε
  have hS := (summable_dampedSingularSeriesTerm hε hh).of_norm.hasSum
  have hlow : HasSum (fun q => if q < 2 then dampedSingularSeriesTerm ε h q else 0) 1 := by
    have h1 : HasSum (fun q => if q < 2 then dampedSingularSeriesTerm ε h q else 0)
        (∑ q ∈ range 2, if q < 2 then dampedSingularSeriesTerm ε h q else 0) :=
      hasSum_sum_of_ne_finset_zero fun q hq => by rw [if_neg (by simpa using hq)]
    rw [Finset.sum_range_succ, Finset.sum_range_one, if_pos (by norm_num), if_pos (by norm_num),
      dampedSingularSeriesTerm_zero, dampedSingularSeriesTerm_one, zero_add] at h1
    exact h1
  have hhigh : HasSum (fun q => if 2 ≤ q then dampedSingularSeriesTerm ε h q else 0)
      (dampedSingularSeries ε h - 1) := by
    refine (hS.sub hlow).congr_fun fun q => ?_
    by_cases hq : 2 ≤ q
    · simp [hq, not_lt.mpr hq]
    · simp [hq, lt_of_not_ge hq]
  rw [add_div, div_self (pow_pos hρ 2).ne', dampedAutocorrelation_div_density_sq_eq hε,
    hhigh.tsum_eq]
  ring

/-- `𝔖_ε(h) → 𝔖(h)` as `ε → 0`. -/
theorem tendsto_dampedSingularSeries {h : ℕ} (hh : 1 ≤ h) :
    Tendsto (fun ε => dampedSingularSeries ε h) (𝓝[>] 0) (𝓝 (hardyLittlewoodSingularSeries h)) := by
  refine (tendsto_lagProductMean_div_density_sq hh).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact lagProductMean_div_density_sq_eq hε hh

/-! ## §3. Lag sums as prefix discrepancies -/

theorem sum_Icc_ramanujanLagWeight {e : ℕ} (he : 0 < e) (H : ℕ) :
    ∑ h ∈ Icc 1 H, ramanujanLagWeight h e = (RHTower.pmRamanujanPrimitive e H).re := by
  rw [pmRamanujanPrimitive_re_eq_sum e H he]
  exact sum_congr rfl fun h _ => ramanujanLagWeight_eq_ramanujanLagCoefficient h e

/-- **The lag-summed autocorrelation is a prefix discrepancy.**
`Σ_{h ≤ H} A_ε(h) = Σ_{e ≥ 2} w_ε(e)² R_e(H)`. -/
theorem sum_Icc_dampedAutocorrelation {ε : ℝ} (hε : 0 < ε) (H : ℕ) :
    ∑ h ∈ Icc 1 H, dampedAutocorrelation ε h =
      ∑' e, if 2 ≤ e then dampedRamanujanCoeff ε e ^ 2 * (RHTower.pmRamanujanPrimitive e H).re
        else 0 := by
  have hsum : ∀ h ∈ Icc 1 H, Summable fun e : ℕ =>
      if 2 ≤ e then ramanujanLagWeight h e * dampedRamanujanCoeff ε e ^ 2 else 0 := by
    intro h hh
    have hh1 : 1 ≤ h := (mem_Icc.mp hh).1
    refine Summable.of_norm_bounded ((summable_sqfreeTotientInv_div_totient.1.mul_left
      ((RHTower.pmPowerDampedDivisorDensity ε).re ^ 2)).mul_left (∑ d ∈ h.divisors, (d : ℝ)))
      fun e => ?_
    rw [Real.norm_eq_abs]
    split_ifs
    · rw [abs_mul, abs_sq]
      exact mul_le_mul (abs_ramanujanLagWeight_le_sigma hh1 e) (dampedRamanujanCoeff_sq_le hε e)
        (sq_nonneg _) (sum_nonneg fun d _ => Nat.cast_nonneg d)
    · rw [abs_zero]
      exact mul_nonneg (sum_nonneg fun d _ => Nat.cast_nonneg d)
        (mul_nonneg (sq_nonneg _) (sqfreeTotientInv_div_totient_nonneg e))
  simp only [dampedAutocorrelation]
  rw [← Summable.tsum_finsetSum hsum]
  refine tsum_congr fun e => ?_
  split_ifs with he
  · rw [← sum_mul, sum_Icc_ramanujanLagWeight (by omega), mul_comm]
  · simp

/-- **Gallagher's sum as a prefix discrepancy.**
`Σ_{h ≤ H} (𝔖(h) - 1) = Σ_{q ≥ 2} (μ²(q)/φ(q)²) R_q(H)`. -/
theorem hasSum_gallagher_prefixDiscrepancy (H : ℕ) :
    HasSum (fun q => if 2 ≤ q then
        RHTower.Sieve.sqfreeTotientInv q / (Nat.totient q : ℝ) * (RHTower.pmRamanujanPrimitive q H).re
        else 0)
      (∑ h ∈ Icc 1 H, (hardyLittlewoodSingularSeries h - 1)) := by
  have hS := hasSum_sum (s := Icc 1 H) fun h hh =>
    hasSum_singularSeriesTerm_ge_two (h := h) (mem_Icc.mp hh).1
  refine hS.congr_fun fun q => ?_
  split_ifs with hq
  · simp only [singularSeriesTerm]
    rw [← sum_mul, sum_Icc_ramanujanLagWeight (by omega), mul_comm]
  · simp

end

end GaloisForLFunctions.BezoutValuationIncidence

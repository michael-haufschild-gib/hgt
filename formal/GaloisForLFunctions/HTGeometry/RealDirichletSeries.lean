import GaloisForLFunctions.HTGeometry.LogClockLaw
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Real Dirichlet series and the arithmetic clocks

An `L`-series with real coefficients, evaluated at a real abscissa, is the real Dirichlet sum of
those coefficients.  This identifies the weights of an arithmetic clock with the values of the
corresponding `L`-series, so the Laplace transform of the clock is an `L`-series at a shifted
abscissa and its mean is the negative logarithmic derivative.

Specialized to the von Mangoldt weight this gives the Euler clock of the fixed-current layer.
-/

open MeasureTheory Set Filter Topology ArithmeticFunction

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The `L`-series term of a real coefficient at a real abscissa is the real Dirichlet term. -/
theorem lseriesTerm_ofReal {f : ℕ → ℝ} (hf0 : f 0 = 0) (σ : ℝ) (n : ℕ) :
    LSeries.term (fun m => (f m : ℂ)) (σ : ℂ) n = ((f n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  by_cases hn : n = 0
  · subst hn
    simp [LSeries.term, hf0]
  · rw [LSeries.term_of_ne_zero hn]
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [Real.rpow_neg hnn]
    push_cast
    rw [Complex.ofReal_cpow hnn]
    push_cast
    rw [div_eq_mul_inv]

/-- Summability of a real Dirichlet series from summability of its `L`-series. -/
theorem summable_real_of_lseriesSummable {f : ℕ → ℝ} (hf0 : f 0 = 0) {σ : ℝ}
    (h : LSeriesSummable (fun m => (f m : ℂ)) (σ : ℂ)) :
    Summable fun n => f n * (n : ℝ) ^ (-σ) := by
  rw [Complex.summable_ofReal.symm]
  exact h.congr fun n => lseriesTerm_ofReal hf0 σ n

/-- **A real `L`-series at a real abscissa is the real Dirichlet sum.** -/
theorem ofReal_tsum_eq_lseries {f : ℕ → ℝ} (hf0 : f 0 = 0) {σ : ℝ} :
    ((∑' n, f n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) = LSeries (fun m => (f m : ℂ)) (σ : ℂ) := by
  rw [LSeries, Complex.ofReal_tsum]
  exact tsum_congr fun n => (lseriesTerm_ofReal hf0 σ n).symm

/-- The real von Mangoldt Dirichlet series is summable past the abscissa one. -/
theorem summable_vonMangoldt_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => Λ n * (n : ℝ) ^ (-σ) := by
  refine summable_real_of_lseriesSummable ?_ (LSeriesSummable_vonMangoldt (s := (σ : ℂ)) ?_)
  · simp
  · simpa using hσ

/-- **The real von Mangoldt Dirichlet sum is the von Mangoldt current.**  This identifies the Euler
clock weights of the transport layer with the fixed current of the source multiplier. -/
theorem ofReal_tsum_vonMangoldt_eq {σ : ℝ} (hσ : 1 < σ) :
    ((∑' n : ℕ, Λ n * (n : ℝ) ^ (-σ) : ℝ) : ℂ)
      = -deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) := by
  have hre : (1 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  rw [ofReal_tsum_eq_lseries (f := fun n => Λ n) (by simp)]
  exact LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre

/-- The real von Mangoldt Dirichlet sum is positive past the abscissa one. -/
theorem tsum_vonMangoldt_rpow_pos {σ : ℝ} (hσ : 1 < σ) :
    0 < ∑' n : ℕ, Λ n * (n : ℝ) ^ (-σ) := by
  have hsummable := summable_vonMangoldt_rpow hσ
  have hnonneg : ∀ n : ℕ, 0 ≤ Λ n * (n : ℝ) ^ (-σ) := fun n =>
    mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  refine lt_of_lt_of_le ?_ (hsummable.le_tsum 2 fun n _ => hnonneg n)
  have hlam : 0 < Λ 2 := by
    rw [vonMangoldt_apply_prime Nat.prime_two]
    exact Real.log_pos (by norm_num)
  exact mul_pos hlam (Real.rpow_pos_of_pos (by norm_num) _)

/-- The critical Euler clock weight: the normalized von Mangoldt Dirichlet coefficients. -/
def eulerClockWeight (σ : ℝ) (n : ℕ) : ℝ :=
  Λ n * (n : ℝ) ^ (-σ) / ∑' m : ℕ, Λ m * (m : ℝ) ^ (-σ)

theorem eulerClockWeight_nonneg {σ : ℝ} (hσ : 1 < σ) (n : ℕ) : 0 ≤ eulerClockWeight σ n :=
  div_nonneg (mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    (tsum_vonMangoldt_rpow_pos hσ).le

@[simp] theorem eulerClockWeight_zero (σ : ℝ) : eulerClockWeight σ 0 = 0 := by
  simp [eulerClockWeight]

/-- **The Euler clock is a law.** -/
theorem tsum_eulerClockWeight {σ : ℝ} (hσ : 1 < σ) : ∑' n : ℕ, eulerClockWeight σ n = 1 := by
  have hpos := tsum_vonMangoldt_rpow_pos hσ
  simp only [eulerClockWeight]
  rw [tsum_div_const]
  exact div_self (ne_of_gt hpos)

/-- The critical Euler clock: the law of the normalized von Mangoldt weight at logarithmic
points. -/
def eulerClockLaw (σ : ℝ) : Measure ℝ := logClockLaw (eulerClockWeight σ)

theorem isProbabilityMeasure_eulerClockLaw {σ : ℝ} (hσ : 1 < σ) :
    IsProbabilityMeasure (eulerClockLaw σ) :=
  isProbabilityMeasure_logClockLaw (eulerClockWeight_nonneg hσ) (tsum_eulerClockWeight hσ)

theorem eulerClockLaw_Iio_zero (σ : ℝ) : eulerClockLaw σ (Iio 0) = 0 :=
  logClockLaw_Iio_zero _

/-- **The Laplace transform of the Euler clock is the ratio of von Mangoldt currents.** -/
theorem integral_exp_neg_eulerClockLaw {σ : ℝ} (hσ : 1 < σ) {u : ℝ} (hu : 0 ≤ u) :
    (∫ y, Real.exp (-(u * y)) ∂(eulerClockLaw σ))
      = (∑' n : ℕ, Λ n * (n : ℝ) ^ (-(σ + u)))
        / ∑' n : ℕ, Λ n * (n : ℝ) ^ (-σ) := by
  rw [eulerClockLaw, integral_exp_neg_logClockLaw (eulerClockWeight_nonneg hσ)
    (eulerClockWeight_zero σ) (tsum_eulerClockWeight hσ) hu]
  rw [← tsum_div_const]
  refine tsum_congr fun n => ?_
  rw [eulerClockWeight, div_mul_eq_mul_div]
  by_cases hn : n = 0
  · subst hn
    simp
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [show -(σ + u) = -σ + -u by ring, Real.rpow_add hnpos]
    ring

/-- The logarithmically weighted von Mangoldt Dirichlet series is summable past abscissa one. -/
theorem summable_vonMangoldt_logMul_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => (Real.log n * Λ n) * (n : ℝ) ^ (-σ) := by
  have habs : LSeries.abscissaOfAbsConv (fun n => (Λ n : ℂ)) < ((σ : ℂ)).re := by
    have hmid : (1 : ℝ) < (1 + σ) / 2 := by linarith
    have hsummable : LSeriesSummable (fun n => (Λ n : ℂ)) (((1 + σ) / 2 : ℝ) : ℂ) :=
      LSeriesSummable_vonMangoldt (by simpa using hmid)
    refine lt_of_le_of_lt hsummable.abscissaOfAbsConv_le ?_
    simp only [Complex.ofReal_re]
    exact_mod_cast by linarith
  have hlog := LSeriesSummable_logMul_of_lt_re habs
  have hcoef : (LSeries.logMul fun n => (Λ n : ℂ))
      = fun n : ℕ => ((Real.log n * Λ n : ℝ) : ℂ) := by
    funext n
    have hlogn : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (Nat.cast_nonneg n)]
    simp only [LSeries.logMul, hlogn, ← Complex.ofReal_mul]
  rw [hcoef] at hlog
  exact summable_real_of_lseriesSummable (by simp) hlog

/-- **The logarithmically weighted von Mangoldt sum is the negative derivative of the current.** -/
theorem ofReal_tsum_vonMangoldt_logMul_eq {σ : ℝ} (hσ : 1 < σ) :
    ((∑' n : ℕ, (Real.log n * Λ n) * (n : ℝ) ^ (-σ) : ℝ) : ℂ)
      = -deriv (LSeries fun n => (Λ n : ℂ)) (σ : ℂ) := by
  have habs : LSeries.abscissaOfAbsConv (fun n => (Λ n : ℂ)) < ((σ : ℂ)).re := by
    have hmid : (1 : ℝ) < (1 + σ) / 2 := by linarith
    have hsummable : LSeriesSummable (fun n => (Λ n : ℂ)) (((1 + σ) / 2 : ℝ) : ℂ) :=
      LSeriesSummable_vonMangoldt (by simpa using hmid)
    refine lt_of_le_of_lt hsummable.abscissaOfAbsConv_le ?_
    simp only [Complex.ofReal_re]
    exact_mod_cast by linarith
  rw [LSeries_deriv habs, neg_neg,
    ofReal_tsum_eq_lseries (f := fun n => Real.log n * Λ n) (by simp)]
  refine congrArg (fun g => LSeries g (σ : ℂ)) ?_
  funext n
  have hlogn : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  simp only [LSeries.logMul, hlogn]
  push_cast
  ring

/-- The Euler clock has a finite mean. -/
theorem integrable_id_eulerClockLaw {σ : ℝ} (hσ : 1 < σ) :
    Integrable (id : ℝ → ℝ) (eulerClockLaw σ) := by
  refine integrable_weightedPointLaw _ _ (fun n => ENNReal.ofReal_ne_top) ?_
  have hsummable := summable_vonMangoldt_logMul_rpow hσ
  have hpos := tsum_vonMangoldt_rpow_pos hσ
  refine ((hsummable.div_const (∑' m : ℕ, Λ m * (m : ℝ) ^ (-σ))).congr fun n => ?_)
  rw [ENNReal.toReal_ofReal (eulerClockWeight_nonneg hσ n)]
  simp only [eulerClockWeight, id_eq, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_natCast_nonneg n)]
  ring

/-- **The mean of the Euler clock is the ratio of the logarithmic and plain von Mangoldt sums.** -/
theorem integral_id_eulerClockLaw {σ : ℝ} (hσ : 1 < σ) :
    (∫ y, y ∂(eulerClockLaw σ))
      = (∑' n : ℕ, (Real.log n * Λ n) * (n : ℝ) ^ (-σ))
        / ∑' n : ℕ, Λ n * (n : ℝ) ^ (-σ) := by
  rw [eulerClockLaw, integral_id_logClockLaw (eulerClockWeight_nonneg hσ)
    (integrable_id_eulerClockLaw hσ)]
  rw [← tsum_div_const]
  refine tsum_congr fun n => ?_
  simp only [eulerClockWeight]
  ring

/-- The constant arithmetic weight, vanishing at zero. -/
def oneWeight (n : ℕ) : ℝ := if n = 0 then 0 else 1

@[simp] theorem oneWeight_zero : oneWeight 0 = 0 := by simp [oneWeight]

/-- **The constant weight has the zeta Dirichlet series.** -/
theorem ofReal_tsum_oneWeight_eq {σ : ℝ} (hσ : 1 < σ) :
    ((∑' n : ℕ, oneWeight n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) = riemannZeta (σ : ℂ) := by
  have hre : (1 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  rw [ofReal_tsum_eq_lseries (f := oneWeight) (by simp)]
  have hterm : LSeries (fun n => ((oneWeight n : ℝ) : ℂ)) (σ : ℂ)
      = LSeries (1 : ℕ → ℂ) (σ : ℂ) := by
    refine tsum_congr fun n => ?_
    by_cases hn : n = 0
    · simp [hn, LSeries.term]
    · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
      simp [oneWeight, hn]
  rw [hterm, LSeries_one_eq_riemannZeta hre]

/-- **The Möbius weight has the reciprocal zeta Dirichlet series.** -/
theorem ofReal_tsum_moebius_eq {σ : ℝ} (hσ : 1 < σ) :
    ((∑' n : ℕ, (moebius n : ℝ) * (n : ℝ) ^ (-σ) : ℝ) : ℂ)
      = 1 / riemannZeta (σ : ℂ) := by
  have hre : (1 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  have hzeta : LSeries (fun n => ((ArithmeticFunction.zeta n : ℕ) : ℂ)) (σ : ℂ)
      = riemannZeta (σ : ℂ) := LSeries_zeta_eq_riemannZeta hre
  have hprod := LSeries_zeta_mul_Lseries_moebius hre
  rw [hzeta] at hprod
  have hzne : riemannZeta (σ : ℂ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hprod
    exact absurd hprod (by norm_num)
  rw [ofReal_tsum_eq_lseries (f := fun n => (moebius n : ℝ)) (by simp)]
  have hcoef : (fun n : ℕ => (((moebius n : ℝ) : ℝ) : ℂ))
      = fun n : ℕ => ((moebius n : ℤ) : ℂ) := by
    funext n
    push_cast
    ring
  rw [hcoef]
  field_simp at hprod ⊢
  linear_combination hprod

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.RHTower.PrimeLaplaceGramStrict
import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Far-right orientation of the normalized Euler trace-Hankel block

The resolved von Mangoldt Laplace Gram is strictly positive, but the factorial
normalization used by the central trace-Hankel moments does not preserve that
orientation.  This file proves the distinction for the actual infinite Euler
source rather than for a finite frequency model.

For the logarithmically weighted von Mangoldt Dirichlet series, the first
nonzero coefficient is the `n = 2` coefficient.  After scaling by `2^x`, its
far-right limit is therefore the corresponding power of `log 2`.  It follows
that the first normalized Hankel determinant has the scaled limit

`-7 * (log 2)^(8 : ℕ) / 360`,

and hence is strictly negative for all sufficiently large real `x`.
-/

open Complex Filter Topology LSeries

namespace RHTower

noncomputable section

/-- The `m`-fold logarithmic derivative coefficient of the von Mangoldt source. -/
def vonMangoldtLogCoeff (m : ℕ) : ℕ → ℂ :=
  logMul^[m] (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))

theorem vonMangoldtLogCoeff_apply (m n : ℕ) :
    vonMangoldtLogCoeff m n =
      (Complex.log n) ^ m * (ArithmeticFunction.vonMangoldt n : ℂ) := by
  induction m with
  | zero => simp [vonMangoldtLogCoeff]
  | succ m ih =>
      rw [vonMangoldtLogCoeff, Function.iterate_succ_apply', logMul]
      change Complex.log n * vonMangoldtLogCoeff m n = _
      rw [ih]
      ring

theorem vonMangoldtLogCoeff_zero (m : ℕ) :
    vonMangoldtLogCoeff m 0 = 0 := by
  rw [vonMangoldtLogCoeff_apply]
  simp

theorem vonMangoldtLogCoeff_one (m : ℕ) :
    vonMangoldtLogCoeff m 1 = 0 := by
  rw [vonMangoldtLogCoeff_apply]
  simp [ArithmeticFunction.vonMangoldt_apply_one]

theorem vonMangoldtLogCoeff_two (m : ℕ) :
    vonMangoldtLogCoeff m 2 = (Real.log 2 : ℂ) ^ (m + 1) := by
  rw [vonMangoldtLogCoeff_apply,
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
  rw [← Complex.natCast_log]
  norm_num
  ring

private theorem vonMangoldtCoeff_abscissa_lt_top :
    abscissaOfAbsConv (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) < ⊤ := by
  have hs := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (2 : ℂ)) (by norm_num)
  exact hs.abscissaOfAbsConv_le.trans_lt (by simp)

theorem vonMangoldtLogCoeff_abscissa_lt_top (m : ℕ) :
    abscissaOfAbsConv (vonMangoldtLogCoeff m) < ⊤ := by
  rw [vonMangoldtLogCoeff, LSeries.absicssaOfAbsConv_logPowMul]
  exact vonMangoldtCoeff_abscissa_lt_top

/-- The first prime power controls every logarithmic moment on the far right. -/
theorem tendsto_vonMangoldtLogCoeff_firstPrime (m : ℕ) :
    Tendsto
      (fun x : ℝ =>
        (2 : ℂ) ^ (x : ℂ) * LSeries (vonMangoldtLogCoeff m) (x : ℂ))
      atTop (nhds ((Real.log 2 : ℂ) ^ (m + 1))) := by
  have h := LSeries.tendsto_cpow_mul_atTop
    (f := vonMangoldtLogCoeff m) (n := 1)
    (fun n hn => by
      interval_cases n <;>
        simp [vonMangoldtLogCoeff_zero, vonMangoldtLogCoeff_one])
    (vonMangoldtLogCoeff_abscissa_lt_top m)
  norm_num at h
  simpa [vonMangoldtLogCoeff_two] using h

/-- Real logarithmic moment of the von Mangoldt Dirichlet source. -/
def vonMangoldtLogMoment (m : ℕ) (x : ℝ) : ℝ :=
  (LSeries (vonMangoldtLogCoeff m) (x : ℂ)).re

theorem tendsto_scaled_vonMangoldtLogMoment (m : ℕ) :
    Tendsto (fun x : ℝ => (2 : ℝ) ^ x * vonMangoldtLogMoment m x)
      atTop (nhds ((Real.log 2) ^ (m + 1))) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_vonMangoldtLogCoeff_firstPrime m)
  convert h using 1
  · funext x
    simp only [Function.comp_apply, vonMangoldtLogMoment]
    have hpow : (2 : ℂ) ^ (x : ℂ) = ((2 : ℝ) ^ x : ℝ) := by
      rw [Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [hpow]
    simp
  · congr 1
    rw [← Complex.ofReal_pow (Real.log 2) (m + 1)]
    rfl

/-- The first factorial-normalized Hankel determinant of the Euler trace moments. -/
def vonMangoldtNormalizedFirstHankelDet (x : ℝ) : ℝ :=
  vonMangoldtLogMoment 1 x * (vonMangoldtLogMoment 5 x / 120) -
    (vonMangoldtLogMoment 3 x / 6) ^ (2 : ℕ)

/-- Exact projective limit of the first normalized Euler trace-Hankel determinant. -/
theorem tendsto_scaled_vonMangoldtNormalizedFirstHankelDet :
    Tendsto
      (fun x : ℝ =>
        ((2 : ℝ) ^ x) ^ (2 : ℕ) * vonMangoldtNormalizedFirstHankelDet x)
      atTop (nhds (-7 * (Real.log 2) ^ (8 : ℕ) / 360)) := by
  have h1 := tendsto_scaled_vonMangoldtLogMoment 1
  have h3 := tendsto_scaled_vonMangoldtLogMoment 3
  have h5 := tendsto_scaled_vonMangoldtLogMoment 5
  have h := h1.mul (h5.div_const 120) |>.sub ((h3.div_const 6).pow 2)
  convert h using 1
  · funext x
    rw [vonMangoldtNormalizedFirstHankelDet]
    ring
  · ring_nf

/-- The actual Euler source eventually lies in the negative normalized Hankel chamber. -/
theorem vonMangoldtNormalizedFirstHankelDet_eventually_neg :
    ∀ᶠ x : ℝ in atTop, vonMangoldtNormalizedFirstHankelDet x < 0 := by
  have hlimneg : -7 * (Real.log 2) ^ (8 : ℕ) / 360 < 0 := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hpos : 0 < 7 * (Real.log 2) ^ (8 : ℕ) / 360 := by positivity
    linarith
  have hev := tendsto_scaled_vonMangoldtNormalizedFirstHankelDet.eventually
    (Iio_mem_nhds hlimneg)
  filter_upwards [hev] with x hx
  have hscale : 0 < ((2 : ℝ) ^ x) ^ (2 : ℕ) := by positivity
  nlinarith

end

end RHTower

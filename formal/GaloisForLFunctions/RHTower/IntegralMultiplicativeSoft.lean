/-
# Integer-valued multiplicative Dirichlet data without a functional equation is soft

A carrier lies in the **integral multiplicative** class when it is the `L`-series of an
integer-valued multiplicative arithmetic function.  No functional equation and no completion is
imposed — only integrality of the coefficients and multiplicativity across coprime products.

The two-term Dirichlet polynomial `wit s = 1 − 2·3^{−s}` is such an `L`-series: it is the series of
the arithmetic function `witCoeff` supported on `{1, 3}` with `witCoeff 1 = 1` and `witCoeff 3 = −2`,
which is multiplicative (it vanishes off the prime power `3` and is `1` at `1`) and integer-valued.
Because the support is finite the series converges to `wit s` at *every* `s`, with no half-plane
restriction.

The multiplier `s ↦ 1 − 2·3^{−s}` vanishes to first order at
`ρwit = (log 2 / log 3) + (2π / log 3)·i`, where `3^{−ρwit} = exp(−log 2 − 2π i) = 1/2`, so
`1 − 2·(1/2) = 0`, while its derivative there is `log 3 ≠ 0`.  The real part `log 2 / log 3` lies
strictly between `1/2` and `1` (it equals `1/2` only if `4 = 3`), and the imaginary part
`2π / log 3` is nonzero: `ρwit` is an off-line, off-real point inside the open critical strip.

Hence the class **carries off-line charge**: its member `wit` has a simple (odd) zero at `ρwit`, so
its base-level deck charge there is `(−1)¹ = −1 ≠ 1`.  By the trichotomy identity
`ForcesRHParity ↔ IsCategorical` (parity-forcing is exactly the charge-free cell), the class
**cannot force RH-grade parity**.  In the Goldilocks conjunction (functional equation ∧ full
multiplicativity ∧ integrality) the functional equation is therefore load-bearing: integrality and
multiplicativity alone impose no divisor constraint off the critical line.
-/
import GaloisForLFunctions.RHTower.GoldilocksTrichotomy
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.LSeries.Basic

noncomputable section

namespace RHTower

open Complex

/-! ### §1 The two-term integral multiplicative witness -/

/-- The Dirichlet polynomial `wit s = 1 − 2·3^{−s}`. -/
def wit : ℂ → ℂ := fun s => 1 - 2 * (3 : ℂ) ^ (-s)

/-- The integer-valued arithmetic function supported on `{1, 3}` with values `1` at `1` and `−2` at
`3`.  Its `L`-series is `wit`. -/
def witCoeff : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 1 then 1 else if n = 3 then -2 else 0, by simp⟩

private theorem witCoeff_apply (n : ℕ) :
    witCoeff n = if n = 1 then 1 else if n = 3 then -2 else 0 := rfl

/-- **`witCoeff` is multiplicative.**  It is `1` at `1`, and across coprime `m, n` both sides vanish
unless the product is `1` or `3`; the only coprime factorisations landing in `{1, 3}` are `1·1` and
`1·3` (and `3·1`), on which the values match, while `3·3` is excluded by coprimality. -/
theorem witCoeff_multiplicative : ArithmeticFunction.IsMultiplicative witCoeff := by
  constructor
  · rw [witCoeff_apply]; norm_num
  · intro m n hcop
    have hval : ∀ k : ℕ, witCoeff k ≠ 0 → k = 1 ∨ k = 3 := by
      intro k hk
      rw [witCoeff_apply] at hk
      by_contra hc
      push Not at hc
      rw [if_neg hc.1, if_neg hc.2] at hk
      exact hk rfl
    rcases eq_or_ne (m * n) 1 with h1 | h1
    · obtain ⟨hm, hn⟩ := mul_eq_one.mp h1
      subst hm; subst hn; simp [witCoeff_apply]
    rcases eq_or_ne (m * n) 3 with h3 | h3
    · have hm3 : m ∣ 3 := ⟨n, h3.symm⟩
      have hmle : m ≤ 3 := Nat.le_of_dvd (by norm_num) hm3
      have hcase : m = 1 ∧ n = 3 ∨ m = 3 ∧ n = 1 := by interval_cases m <;> omega
      rcases hcase with ⟨hm, hn⟩ | ⟨hm, hn⟩
      · subst hm; subst hn; simp [witCoeff_apply]
      · subst hm; subst hn; simp [witCoeff_apply]
    · rw [show witCoeff (m * n) = 0 by rw [witCoeff_apply, if_neg h1, if_neg h3]]
      by_cases hm : witCoeff m = 0
      · rw [hm]; ring
      by_cases hn : witCoeff n = 0
      · rw [hn]; ring
      exfalso
      rcases hval m hm with hm1 | hm3' <;> rcases hval n hn with hn1 | hn3'
      · subst hm1; subst hn1; exact h1 (by norm_num)
      · subst hm1; subst hn3'; exact h3 (by norm_num)
      · subst hm3'; subst hn1; exact h3 (by norm_num)
      · subst hm3'; subst hn3'; simp [Nat.coprime_self] at hcop

/-- **`witCoeff` is integer-valued.**  Every value is `1`, `−2`, or `0`. -/
theorem witCoeff_integral (n : ℕ) : ∃ k : ℤ, witCoeff n = (k : ℂ) := by
  rw [witCoeff_apply]
  rcases eq_or_ne n 1 with h1 | h1
  · exact ⟨1, by rw [if_pos h1]; norm_num⟩
  rcases eq_or_ne n 3 with h3 | h3
  · exact ⟨-2, by rw [if_neg h1, if_pos h3]; norm_num⟩
  · exact ⟨0, by rw [if_neg h1, if_neg h3]; norm_num⟩

/-- **The `L`-series of `witCoeff` is `wit`.**  The support is `{1, 3}`, so the series is the finite
sum of the `n = 1` term (`1`) and the `n = 3` term (`−2·3^{−s}`), valid at every `s`. -/
theorem LSeries_witCoeff (s : ℂ) : LSeries (fun n => witCoeff n) s = wit s := by
  have hsupp : ∀ n ∉ ({1, 3} : Finset ℕ), LSeries.term (fun n => witCoeff n) s n = 0 := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hpos.ne' _ s]
      have h1 : n ≠ 1 := by rintro rfl; exact hn (by decide)
      have h3 : n ≠ 3 := by rintro rfl; exact hn (by decide)
      rw [witCoeff_apply, if_neg h1, if_neg h3]; simp
  have hHS := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) hsupp
  rw [show LSeries (fun n => witCoeff n) s
        = ∑' n, LSeries.term (fun n => witCoeff n) s n from rfl,
    hHS.tsum_eq, Finset.sum_pair (by decide : (1 : ℕ) ≠ 3),
    LSeries.term_of_ne_zero (by norm_num) _ s, LSeries.term_of_ne_zero (by norm_num) _ s,
    witCoeff_apply, witCoeff_apply]
  norm_num [wit, Complex.cpow_neg]
  rw [div_eq_mul_inv]; ring

/-! ### §2 The off-line witness point and the simple zero -/

/-- The witness point `ρwit = (log 2 / log 3) + (2π / log 3)·i`, where `3^{−ρwit} = 1/2`. -/
def ρwit : ℂ :=
  ((Real.log 2 / Real.log 3 : ℝ) : ℂ) + ((2 * Real.pi / Real.log 3 : ℝ) : ℂ) * Complex.I

/-- `wit` in exponential form: `1 − 2·3^{−s} = 1 − 2·exp(−(log 3)·s)`. -/
theorem wit_eq_exp :
    wit = fun s => 1 - 2 * Complex.exp (-(((Real.log 3 : ℝ) : ℂ) * s)) := by
  have hlog : Complex.log 3 = ((Real.log 3 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
  funext s
  simp only [wit]
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (3 : ℂ) ≠ 0), hlog, mul_neg]

/-- At `ρwit` the exponential factor equals `1/2`: `−(log 3)·ρwit = −log 2 − 2π i`, and
`exp(−log 2)·exp(−2π i) = (1/2)·1`. -/
theorem three_cexp_half : Complex.exp (-(((Real.log 3 : ℝ) : ℂ) * ρwit)) = 1 / 2 := by
  have hlog3neC : ((Real.log 3 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))
  have hkey : ((Real.log 3 : ℝ) : ℂ) * ρwit
      = ((Real.log 2 : ℝ) : ℂ) + ((2 * Real.pi : ℝ) : ℂ) * I := by
    simp only [ρwit]
    rw [show ((Real.log 2 / Real.log 3 : ℝ) : ℂ)
          = ((Real.log 2 : ℝ) : ℂ) / ((Real.log 3 : ℝ) : ℂ) by push_cast; ring,
      show ((2 * Real.pi / Real.log 3 : ℝ) : ℂ)
          = ((2 * Real.pi : ℝ) : ℂ) / ((Real.log 3 : ℝ) : ℂ) by push_cast; ring,
      mul_add, mul_div_cancel₀ _ hlog3neC,
      show ((Real.log 3 : ℝ) : ℂ) * (((2 * Real.pi : ℝ) : ℂ) / ((Real.log 3 : ℝ) : ℂ) * I)
          = (((Real.log 3 : ℝ) : ℂ) * (((2 * Real.pi : ℝ) : ℂ) / ((Real.log 3 : ℝ) : ℂ))) * I by
        ring,
      mul_div_cancel₀ _ hlog3neC]
  rw [hkey, neg_add, Complex.exp_add]
  have hA : Complex.exp (-((Real.log 2 : ℝ) : ℂ)) = 1 / 2 := by
    rw [show -((Real.log 2 : ℝ) : ℂ) = ((-Real.log 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log (by norm_num)]
    push_cast; norm_num
  have hB : Complex.exp (-(((2 * Real.pi : ℝ) : ℂ) * I)) = 1 := by
    have h := Complex.exp_int_mul_two_pi_mul_I (-1)
    rw [show ((-1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) = -(((2 * Real.pi : ℝ) : ℂ) * I) by
      push_cast; ring] at h
    exact h
  rw [hA, hB]; ring

/-- **`wit` vanishes at `ρwit`.**  `1 − 2·(1/2) = 0`. -/
theorem wit_ρwit_eq_zero : wit ρwit = 0 := by
  rw [wit_eq_exp]
  show 1 - 2 * Complex.exp (-(((Real.log 3 : ℝ) : ℂ) * ρwit)) = 0
  rw [three_cexp_half]; ring

/-- **The zero is simple.**  `wit` is entire, vanishes at `ρwit`, and its derivative there is
`log 3 ≠ 0`, so the analytic order is `1`. -/
theorem wit_order_one : analyticOrderAt wit ρwit = 1 := by
  rw [wit_eq_exp]
  have hLcne : ((Real.log 3 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))
  have han : AnalyticAt ℂ (fun s => 1 - 2 * Complex.exp (-(((Real.log 3 : ℝ) : ℂ) * s))) ρwit := by
    have hdiff :
        Differentiable ℂ (fun s => 1 - 2 * Complex.exp (-(((Real.log 3 : ℝ) : ℂ) * s))) :=
      (((differentiable_id.const_mul ((Real.log 3 : ℝ) : ℂ)).neg.cexp).const_mul 2).const_sub 1
    exact (hdiff.differentiableOn.analyticOnNhd isOpen_univ) ρwit (Set.mem_univ ρwit)
  have hzero : (fun s => 1 - 2 * Complex.exp (-(((Real.log 3 : ℝ) : ℂ) * s))) ρwit = 0 := by
    show 1 - 2 * Complex.exp (-(((Real.log 3 : ℝ) : ℂ) * ρwit)) = 0
    rw [three_cexp_half]; ring
  have hd : HasDerivAt (fun s => 1 - 2 * Complex.exp (-(((Real.log 3 : ℝ) : ℂ) * s)))
      (-(2 * (Complex.exp (-(((Real.log 3 : ℝ) : ℂ) * ρwit)) * (-((Real.log 3 : ℝ) : ℂ))))) ρwit := by
    have h1 : HasDerivAt (fun s : ℂ => -(((Real.log 3 : ℝ) : ℂ) * s)) (-((Real.log 3 : ℝ) : ℂ))
        ρwit := by
      simpa using ((hasDerivAt_id ρwit).const_mul ((Real.log 3 : ℝ) : ℂ)).neg
    exact ((h1.cexp).const_mul 2).const_sub 1
  have hderiv : deriv (fun s => 1 - 2 * Complex.exp (-(((Real.log 3 : ℝ) : ℂ) * s))) ρwit
      = ((Real.log 3 : ℝ) : ℂ) := by
    rw [hd.deriv, three_cexp_half]; ring
  refine han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero ?_
  rw [hderiv]; exact hLcne

/-! ### §3 `ρwit` is off-line and inside the open strip -/

theorem ρwit_re : ρwit.re = Real.log 2 / Real.log 3 := by
  simp only [ρwit, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]; ring

/-- `Re ρwit = log 2 / log 3 ≠ 1/2`: equality would force `4 = 3`. -/
theorem ρwit_re_ne_half : ρwit.re ≠ 1 / 2 := by
  rw [ρwit_re]
  intro h
  have hlog3pos := Real.log_pos (show (1 : ℝ) < 3 by norm_num)
  rw [div_eq_iff (ne_of_gt hlog3pos)] at h
  have h4 : Real.log 4 = Real.log 3 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; linarith
  have hbad := Real.log_injOn_pos (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 4))
    (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 3)) h4
  norm_num at hbad

/-- `0 < Re ρwit`: `log 2, log 3 > 0`. -/
theorem ρwit_re_pos : 0 < ρwit.re := by
  rw [ρwit_re]; exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))

/-- `Re ρwit < 1`: `log 2 < log 3`. -/
theorem ρwit_re_lt_one : ρwit.re < 1 := by
  rw [ρwit_re]
  exact (div_lt_one (Real.log_pos (by norm_num))).mpr (Real.log_lt_log (by norm_num) (by norm_num))

/-- `Im ρwit = 2π / log 3 ≠ 0`. -/
theorem ρwit_im_ne_zero : ρwit.im ≠ 0 := by
  have h : ρwit.im = 2 * Real.pi / Real.log 3 := by
    simp only [ρwit, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im]; ring
  rw [h]
  exact ne_of_gt (div_pos (by positivity) (Real.log_pos (by norm_num)))

/-! ### §4 The class carries off-line charge, hence no RH-grade parity -/

/-- The **integral multiplicative** class: carriers that are the `L`-series of an integer-valued
multiplicative arithmetic function.  No functional equation and no completion — only integrality and
multiplicativity of the coefficients. -/
def IntegralMultiplicativeClass (f : ℂ → ℂ) : Prop :=
  ∃ a : ArithmeticFunction ℂ, ArithmeticFunction.IsMultiplicative a ∧
    (∀ n, ∃ k : ℤ, a n = (k : ℂ)) ∧ (∀ s, f s = LSeries (fun n => a n) s)

/-- **`wit` lies in the class**, witnessed by `witCoeff`. -/
theorem wit_mem_integralMultiplicativeClass : IntegralMultiplicativeClass wit :=
  ⟨witCoeff, witCoeff_multiplicative, witCoeff_integral, fun s => (LSeries_witCoeff s).symm⟩

/-- **The class carries nontrivial charge at `ρwit`.**  `wit` is in the class and has a simple (odd)
zero there, so its base-level deck charge is `(−1)¹ = −1 ≠ 1`. -/
theorem carriesChargeAt_integralMultiplicativeClass :
    CarriesChargeAt IntegralMultiplicativeClass ρwit := by
  refine ⟨wit, wit_mem_integralMultiplicativeClass, ?_⟩
  rw [carrierCharge_one_eq_neg_one_pow, wit_order_one, ENat.toNat_one]; norm_num

/-- **The class carries off-line charge.**  The witness `ρwit` has `Re ρwit = log 2 / log 3 ≠ 1/2`
(and, by the strip lemmas, lies strictly inside the open critical strip, off the real axis). -/
theorem integralMultiplicativeClass_carriesOffLineCharge :
    CarriesOffLineCharge IntegralMultiplicativeClass :=
  ⟨ρwit, ρwit_re_ne_half, carriesChargeAt_integralMultiplicativeClass⟩

/-- **Integrality and multiplicativity alone cannot force RH-grade parity.**  Parity-forcing by
charge is exactly the charge-free (categorical) cell (`forcesRHParity_iff_categorical`); this class
carries off-line charge, so it is not categorical.  In the Goldilocks conjunction the functional
equation is load-bearing: without it, integer-valued multiplicative Dirichlet data is blind to
off-line parity. -/
theorem integralMultiplicativeClass_not_forcesRHParity :
    ¬ ForcesRHParity IntegralMultiplicativeClass := by
  rw [forcesRHParity_iff_categorical]
  exact fun hcat => hcat integralMultiplicativeClass_carriesOffLineCharge

end RHTower

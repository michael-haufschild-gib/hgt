import GaloisForLFunctions.RHTower.Sieve.TwoRangeLimits
import GaloisForLFunctions.RHTower.Sieve.PolyDecayLimits

/-!
# The monomials of the two-range budget

Once the schedule is substituted, every group of the two-range budget is a finite sum of monomials

```text
   (log x)^e · (log log x)^k · f(x) ,     f ∈ { 1 , 1/h , 1/√x , h/√x , e^{−(log x)^s} } ,
```

where `h = exp((log x)^β)` is the window length.  Each such monomial vanishes, and the proof is
always the same: a power of `log log` is at most `log x` in the limit, so the `log log` factor is
absorbed into the exponent and the corpus's own decay lemmas apply.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- **A power of `log log` is at most any positive power of `log`.** -/
theorem eventually_logLogPow_le_rpow (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, (Real.log (Real.log x)) ^ k ≤ (Real.log x) ^ ε := by
  have hlim := tendsto_logRpow_mul_logLogPow (e := -ε) (by linarith) k
  filter_upwards [Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) hlim,
    Filter.eventually_gt_atTop (1 : ℝ)] with x hsm hx1
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hpow : (0 : ℝ) < (Real.log x) ^ ε := Real.rpow_pos_of_pos hlogx ε
  have hid : (Real.log x) ^ ε * (Real.log x) ^ (-ε) = 1 := by
    rw [← Real.rpow_add hlogx]
    simp
  have := mul_le_mul_of_nonneg_left hsm hpow.le
  rw [mul_one, ← mul_assoc, hid, one_mul] at this
  exact this

/-- Nonnegativity of a monomial. -/
theorem logMonomial_nonneg {e : ℝ} (k : ℕ) {x : ℝ} (hx : Real.exp 1 ≤ x) :
    0 ≤ (Real.log x) ^ e * (Real.log (Real.log x)) ^ k := by
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hx
    rwa [Real.log_exp] at this
  have hlogx : (0 : ℝ) < Real.log x := by linarith
  have h1 : (0 : ℝ) ≤ (Real.log x) ^ e := Real.rpow_nonneg hlogx.le e
  have h2 : (0 : ℝ) ≤ (Real.log (Real.log x)) ^ k := pow_nonneg (Real.log_nonneg hlog1) k
  exact mul_nonneg h1 h2

/-- A monomial vanishes against a negative power of the logarithm. -/
theorem tendsto_logMonomial {e : ℝ} (he : e < 0) (k : ℕ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ e * (Real.log (Real.log x)) ^ k) atTop (𝓝 0) :=
  tendsto_logRpow_mul_logLogPow he k

/-- A monomial vanishes against the window length. -/
theorem tendsto_logMonomial_div_cardLength {β : ℝ} (hβ : 0 < β) (e : ℝ) (k : ℕ) :
    Tendsto (fun x : ℝ =>
      (Real.log x) ^ e * (Real.log (Real.log x)) ^ k / cardLength β x) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ (tendsto_rpow_log_div_cardLength (β := β) hβ (e + 1))
  · filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with x hxe
    exact div_nonneg (logMonomial_nonneg k hxe) (cardLength_pos β x).le
  · filter_upwards [eventually_logLogPow_le_rpow k (ε := (1 : ℝ)) (by norm_num),
      Filter.eventually_ge_atTop (Real.exp 1), Filter.eventually_gt_atTop (1 : ℝ)]
      with x hll hxe hx1
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hlog1 : (1 : ℝ) ≤ Real.log x := by
      have := Real.log_le_log (Real.exp_pos 1) hxe
      rwa [Real.log_exp] at this
    have hpe : (0 : ℝ) ≤ (Real.log x) ^ e := Real.rpow_nonneg hlogx.le e
    have hnum : (Real.log x) ^ e * (Real.log (Real.log x)) ^ k ≤ (Real.log x) ^ (e + 1) := by
      calc (Real.log x) ^ e * (Real.log (Real.log x)) ^ k
          ≤ (Real.log x) ^ e * (Real.log x) ^ (1 : ℝ) := mul_le_mul_of_nonneg_left hll hpe
        _ = (Real.log x) ^ (e + 1) := by rw [← Real.rpow_add hlogx]
    exact div_le_div_of_nonneg_right hnum (cardLength_pos β x).le

/-- A monomial vanishes against the square root of the outer scale. -/
theorem tendsto_logMonomial_div_sqrt (e : ℝ) (k : ℕ) :
    Tendsto (fun x : ℝ =>
      (Real.log x) ^ e * (Real.log (Real.log x)) ^ k / Real.sqrt x) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ (tendsto_rpow_log_div_sqrt (e + 1))
  · filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with x hxe
    exact div_nonneg (logMonomial_nonneg k hxe) (Real.sqrt_nonneg x)
  · filter_upwards [eventually_logLogPow_le_rpow k (ε := (1 : ℝ)) (by norm_num),
      Filter.eventually_ge_atTop (Real.exp 1), Filter.eventually_gt_atTop (1 : ℝ),
      Filter.eventually_ge_atTop (16 : ℝ)] with x hll hxe hx1 hx16
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hpe : (0 : ℝ) ≤ (Real.log x) ^ e := Real.rpow_nonneg hlogx.le e
    have hsq : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hnum : (Real.log x) ^ e * (Real.log (Real.log x)) ^ k ≤ (Real.log x) ^ (e + 1) := by
      calc (Real.log x) ^ e * (Real.log (Real.log x)) ^ k
          ≤ (Real.log x) ^ e * (Real.log x) ^ (1 : ℝ) := mul_le_mul_of_nonneg_left hll hpe
        _ = (Real.log x) ^ (e + 1) := by rw [← Real.rpow_add hlogx]
    exact div_le_div_of_nonneg_right hnum hsq.le

/-- A monomial vanishes against the window length over the square root of the outer scale. -/
theorem tendsto_logMonomial_mul_cardLength_div_sqrt {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (e : ℝ) (k : ℕ) :
    Tendsto (fun x : ℝ =>
      (Real.log x) ^ e * (Real.log (Real.log x)) ^ k * (cardLength β x / Real.sqrt x))
      atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_
    (tendsto_rpow_log_mul_cardLength_div_sqrt (β := β) hβ0 hβ1 (e + 1))
  · filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with x hxe
    exact mul_nonneg (logMonomial_nonneg k hxe)
      (div_nonneg (cardLength_pos β x).le (Real.sqrt_nonneg x))
  · filter_upwards [eventually_logLogPow_le_rpow k (ε := (1 : ℝ)) (by norm_num),
      Filter.eventually_ge_atTop (Real.exp 1), Filter.eventually_gt_atTop (1 : ℝ)]
      with x hll hxe hx1
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hpe : (0 : ℝ) ≤ (Real.log x) ^ e := Real.rpow_nonneg hlogx.le e
    have hnum : (Real.log x) ^ e * (Real.log (Real.log x)) ^ k ≤ (Real.log x) ^ (e + 1) := by
      calc (Real.log x) ^ e * (Real.log (Real.log x)) ^ k
          ≤ (Real.log x) ^ e * (Real.log x) ^ (1 : ℝ) := mul_le_mul_of_nonneg_left hll hpe
        _ = (Real.log x) ^ (e + 1) := by rw [← Real.rpow_add hlogx]
    exact mul_le_mul_of_nonneg_right hnum
      (div_nonneg (cardLength_pos β x).le (Real.sqrt_nonneg x))

/-- A monomial vanishes against a zero-free-region saving. -/
theorem tendsto_logMonomial_mul_expNeg {s : ℝ} (hs : 0 < s) (e : ℝ) (k : ℕ) :
    Tendsto (fun x : ℝ =>
        (Real.log x) ^ e * (Real.log (Real.log x)) ^ k * Real.exp (-((Real.log x) ^ s)))
      atTop (𝓝 0) :=
  tendsto_logLogPow_mul_expNeg hs k e

end

end RHTower.Sieve

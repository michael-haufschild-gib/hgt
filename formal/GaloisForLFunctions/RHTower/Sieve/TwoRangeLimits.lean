import GaloisForLFunctions.RHTower.Sieve.LogPowerLimits
import GaloisForLFunctions.RHTower.Sieve.PolyDecayLimits

/-!
# The limits the two-range substitution needs

Every group of the two-range budget, once the schedule is substituted, is a product of factors of
four kinds: a power of `log x`, a power of `log log x`, the window `h/√x`, and a zero-free-region
saving `exp(−(log x)^s)`.  The mixed limits are collected here; a power of `log log x` is absorbed
into an arbitrarily small power of `log x` by `Real.log_le_rpow_div`.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- **A power of `log log` is absorbed by any negative power of `log`.** -/
theorem tendsto_logRpow_mul_logLogPow {e : ℝ} (he : e < 0) (k : ℕ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ e * (Real.log (Real.log x)) ^ k) atTop (𝓝 0) := by
  set ε : ℝ := (-e) / (2 * ((k : ℝ) + 1)) with hε
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hε0 : 0 < ε := by
    rw [hε]
    have : (0 : ℝ) < -e := by linarith
    positivity
  have hexp : e + (k : ℝ) * ε < 0 := by
    rw [hε]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    have hne : (0 : ℝ) < -e := by linarith
    have hfrac : (k : ℝ) / (2 * ((k : ℝ) + 1)) ≤ 1 / 2 := by
      have h2 : (0 : ℝ) < 2 * ((k : ℝ) + 1) := by positivity
      rw [div_le_iff₀ h2]
      linarith [hk0]
    have hkey : (k : ℝ) * ((-e) / (2 * ((k : ℝ) + 1))) ≤ (-e) / 2 := by
      have hid : (k : ℝ) * ((-e) / (2 * ((k : ℝ) + 1)))
          = (-e) * ((k : ℝ) / (2 * ((k : ℝ) + 1))) := by ring
      rw [hid]
      have := mul_le_mul_of_nonneg_left hfrac hne.le
      linarith
    linarith
  have hmaj : Tendsto (fun x : ℝ => (1 / ε ^ k) * (Real.log x) ^ (e + (k : ℝ) * ε))
      atTop (𝓝 0) := by
    have h := tendsto_log_rpow_neg (δ := -(e + (k : ℝ) * ε)) (by linarith)
    have h' : Tendsto (fun x : ℝ => (Real.log x) ^ (e + (k : ℝ) * ε)) atTop (𝓝 0) := by
      refine h.congr fun x => ?_
      rw [neg_neg]
    have := h'.const_mul (1 / ε ^ k)
    simpa using this
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1)] with x hx1 hxe
    have hlog : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hll : (0 : ℝ) ≤ Real.log (Real.log x) := by
      refine Real.log_nonneg ?_
      have : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      linarith
    have : (0 : ℝ) ≤ (Real.log x) ^ e := Real.rpow_nonneg hlog.le e
    positivity
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1)] with x hx1 hxe
    have hlog : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hll0 : (0 : ℝ) ≤ Real.log (Real.log x) := by
      refine Real.log_nonneg ?_
      have : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      linarith
    have hbd : Real.log (Real.log x) ≤ (Real.log x) ^ ε / ε :=
      Real.log_le_rpow_div hlog.le hε0
    have hpowk : (Real.log (Real.log x)) ^ k ≤ ((Real.log x) ^ ε / ε) ^ k :=
      pow_le_pow_left₀ hll0 hbd k
    have hfac : ((Real.log x) ^ ε / ε) ^ k = (1 / ε ^ k) * ((Real.log x) ^ ε) ^ k := by
      rw [div_pow]
      ring
    have hcomb : ((Real.log x) ^ ε) ^ k = (Real.log x) ^ ((k : ℝ) * ε) := by
      rw [← Real.rpow_natCast ((Real.log x) ^ ε) k, ← Real.rpow_mul hlog.le]
      congr 1
      ring
    have he0 : (0 : ℝ) ≤ (Real.log x) ^ e := Real.rpow_nonneg hlog.le e
    calc (Real.log x) ^ e * (Real.log (Real.log x)) ^ k
        ≤ (Real.log x) ^ e * ((Real.log x) ^ ε / ε) ^ k :=
          mul_le_mul_of_nonneg_left hpowk he0
      _ = (1 / ε ^ k) * ((Real.log x) ^ e * (Real.log x) ^ ((k : ℝ) * ε)) := by
          rw [hfac, hcomb]; ring
      _ = (1 / ε ^ k) * (Real.log x) ^ (e + (k : ℝ) * ε) := by
          rw [Real.rpow_add hlog]

/-- **A power of `log log` is beaten by a zero-free-region saving.** -/
theorem tendsto_logLogPow_mul_expNeg {s : ℝ} (hs : 0 < s) (k : ℕ) (e : ℝ) :
    Tendsto (fun x : ℝ =>
        (Real.log x) ^ e * (Real.log (Real.log x)) ^ k * Real.exp (-((Real.log x) ^ s)))
      atTop (𝓝 0) := by
  have hmaj := tendsto_rpow_log_mul_exp_neg (c := e + (k : ℝ) + 1) (a := s) hs
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1)] with x hx1 hxe
    have hlog : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hll : (0 : ℝ) ≤ Real.log (Real.log x) := by
      refine Real.log_nonneg ?_
      have : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      linarith
    have : (0 : ℝ) ≤ (Real.log x) ^ e := Real.rpow_nonneg hlog.le e
    positivity
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1)] with x hx1 hxe
    have hlog : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hlog1 : (1 : ℝ) ≤ Real.log x := by
      have : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      linarith
    have hll0 : (0 : ℝ) ≤ Real.log (Real.log x) := Real.log_nonneg hlog1
    have hbd : Real.log (Real.log x) ≤ Real.log x := by
      have := Real.log_le_sub_one_of_pos hlog
      linarith
    have hpowk : (Real.log (Real.log x)) ^ k ≤ (Real.log x) ^ k :=
      pow_le_pow_left₀ hll0 hbd k
    have hcast : ((Real.log x) ^ k : ℝ) = (Real.log x) ^ ((k : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
    have he0 : (0 : ℝ) ≤ (Real.log x) ^ e := Real.rpow_nonneg hlog.le e
    have hexp0 : (0 : ℝ) < Real.exp (-((Real.log x) ^ s)) := Real.exp_pos _
    have hstep : (Real.log x) ^ e * (Real.log (Real.log x)) ^ k
        ≤ (Real.log x) ^ (e + (k : ℝ) + 1) := by
      calc (Real.log x) ^ e * (Real.log (Real.log x)) ^ k
          ≤ (Real.log x) ^ e * (Real.log x) ^ k := mul_le_mul_of_nonneg_left hpowk he0
        _ = (Real.log x) ^ (e + (k : ℝ)) := by
            rw [hcast, ← Real.rpow_add hlog]
        _ ≤ (Real.log x) ^ (e + (k : ℝ) + 1) :=
            Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
    have := mul_le_mul_of_nonneg_right hstep hexp0.le
    linarith [this]

end

end RHTower.Sieve

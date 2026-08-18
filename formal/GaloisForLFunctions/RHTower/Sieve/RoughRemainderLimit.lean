import GaloisForLFunctions.RHTower.Sieve.SiftingDepth
import GaloisForLFunctions.RHTower.Sieve.SiftingRangeRatio

/-!
# The Selberg remainder is negligible against the outer scale

At level `z = x^{1/4}` the whole Selberg remainder of the pair sieve is `2 z · 6^{log z / log P₁}`.
Since `log P₁ → ∞`, the exponent is `o(log x)` and the remainder is `x^{1/4 + o(1)}`, hence
negligible against `√x`.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- **The start of the sifting range has a logarithm of the expected size.** -/
theorem log_siftStart_ge (c x : ℝ) :
    (Real.log x) ^ c ≤ Real.log ((siftStart c x : ℕ) : ℝ) := by
  have hge : Real.exp ((Real.log x) ^ c) ≤ ((siftStart c x : ℕ) : ℝ) := by
    rw [siftStart]
    exact Nat.le_ceil _
  calc (Real.log x) ^ c = Real.log (Real.exp ((Real.log x) ^ c)) := (Real.log_exp _).symm
    _ ≤ Real.log ((siftStart c x : ℕ) : ℝ) := Real.log_le_log (Real.exp_pos _) hge

/-- **The Selberg remainder of the chosen sieve is negligible against `√x`.** -/
theorem tendsto_selbergRemainder_div_sqrt {a β : ℝ} (hβ : 0 < β) (ha0 : 0 < a) :
    Tendsto (fun x : ℝ =>
        (2 * siftLevel x
            * (6 : ℝ) ^ (Real.log (siftLevel x) / Real.log ((siftStart (a * β) x : ℕ) : ℝ)))
          / Real.sqrt x) atTop (𝓝 0) := by
  have hab : (0 : ℝ) < a * β := mul_pos ha0 hβ
  have hpowA : Tendsto (fun x : ℝ => (Real.log x) ^ (a * β)) atTop atTop :=
    (tendsto_rpow_atTop hab).comp Real.tendsto_log_atTop
  have hmaj : Tendsto (fun x : ℝ => 2 * Real.exp (-(Real.log x / 8))) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun x : ℝ => Real.log x / 8) atTop atTop :=
      Real.tendsto_log_atTop.atTop_div_const (by norm_num)
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hdiv).const_mul (2 : ℝ)
    simpa using this
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
    have hx0 : (0 : ℝ) < x := by linarith
    have hs : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
    have hL : (0 : ℝ) < siftLevel x := by
      rw [siftLevel]
      exact Real.sqrt_pos.2 hs
    have hp : (0 : ℝ) < (6 : ℝ) ^ (Real.log (siftLevel x)
        / Real.log ((siftStart (a * β) x : ℕ) : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  · filter_upwards [hpowA.eventually_ge_atTop (2 * Real.log 6),
      Filter.eventually_gt_atTop (1 : ℝ)] with x hbig hx1
    have hx0 : (0 : ℝ) < x := by linarith
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hs : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
    have hL : (0 : ℝ) < siftLevel x := by
      rw [siftLevel]
      exact Real.sqrt_pos.2 hs
    have hl6 : (0 : ℝ) < Real.log 6 := Real.log_pos (by norm_num)
    have hP : 2 * Real.log 6 ≤ Real.log ((siftStart (a * β) x : ℕ) : ℝ) :=
      le_trans hbig (log_siftStart_ge (a * β) x)
    have hP0 : (0 : ℝ) < Real.log ((siftStart (a * β) x : ℕ) : ℝ) := by linarith
    -- the three logarithms
    have hlogLevel : Real.log (siftLevel x) = Real.log x / 4 := log_siftLevel hx0
    have hLexp : siftLevel x = Real.exp (Real.log x / 4) := by
      rw [← hlogLevel, Real.exp_log hL]
    have hsexp : Real.sqrt x = Real.exp (Real.log x / 2) := by
      have : Real.log (Real.sqrt x) = Real.log x / 2 := by
        rw [Real.log_sqrt hx0.le]
      rw [← this, Real.exp_log hs]
    have hpow : (6 : ℝ) ^ (Real.log (siftLevel x)
        / Real.log ((siftStart (a * β) x : ℕ) : ℝ))
        = Real.exp ((Real.log x / 4) / Real.log ((siftStart (a * β) x : ℕ) : ℝ)
            * Real.log 6) := by
      rw [Real.rpow_def_of_pos (by norm_num), hlogLevel]
      ring_nf
    -- the exponent
    have hexpbd : (Real.log x / 4) / Real.log ((siftStart (a * β) x : ℕ) : ℝ) * Real.log 6
        ≤ Real.log x / 8 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hP0 (by norm_num : (0:ℝ) < 8)]
      nlinarith [hP, hlogx, hl6]
    rw [hpow, hLexp, hsexp]
    have hle : Real.log x / 4
        + (Real.log x / 4) / Real.log ((siftStart (a * β) x : ℕ) : ℝ) * Real.log 6
        - Real.log x / 2 ≤ -(Real.log x / 8) := by linarith
    have hstep := Real.exp_le_exp.2 hle
    have hdiv : 2 * Real.exp (Real.log x / 4
        + (Real.log x / 4) / Real.log ((siftStart (a * β) x : ℕ) : ℝ) * Real.log 6
        - Real.log x / 2) ≤ 2 * Real.exp (-(Real.log x / 8)) := by linarith
    calc 2 * Real.exp (Real.log x / 4) * Real.exp ((Real.log x / 4)
            / Real.log ((siftStart (a * β) x : ℕ) : ℝ) * Real.log 6)
              / Real.exp (Real.log x / 2)
        = 2 * Real.exp (Real.log x / 4
            + (Real.log x / 4) / Real.log ((siftStart (a * β) x : ℕ) : ℝ) * Real.log 6
            - Real.log x / 2) := by
          rw [Real.exp_sub, Real.exp_add]
          ring
      _ ≤ 2 * Real.exp (-(Real.log x / 8)) := hdiv

end

end RHTower.Sieve

import GaloisForLFunctions.RHTower.ProlateIndexedAmplitudeRatio
import GaloisForLFunctions.RHTower.ProlatePhaseSeparation
import GaloisForLFunctions.RHTower.ProlateLeakageRatioBounds

/-!
# The amplitude ratio of two rungs vanishes

The three factors of `eventually_prolateBand_sq_ratio_le` are each elementary:

```text
C_n(a)                      ≤ 1 + leakageBarrierConst                (barrierFactor_le)
Λ_n(y₀)                     ≤ log c - log(x₀²/2) - log(1-α²)        (scale log at y₀² = x₀²/c)
2c (Ξ_{s_n}(y₀) - Ξ_{s_m}(y₀)) ≤ -c(s_n - s_m)·((log c)/2 - log x₀)  (bandEndpointPhase_sub_ge)
-12(log(1-α) - log(1-y₀))   ≤ -12 log(1-α)
```

and `c(s_n - s_m) → 4(n-m) ≥ 4`, so the exponent is at most `-(log c)/2 + K` for an absolute `K`.
Hence the ratio is `O(c^{-1/2})`, and in particular vanishes.
-/

set_option maxHeartbeats 2400000

noncomputable section

open Set Filter Topology

namespace RHTower

open GaloisForLFunctions.RHTower

theorem sqrt_eq_exp_half_log {c : ℝ} (hc : 0 < c) :
    Real.sqrt c = Real.exp (Real.log c / 2) := by
  have h2 : Real.exp (Real.log c / 2) ^ (2 : ℕ) = c := by
    rw [sq, ← Real.exp_add]
    have hsum : Real.log c / 2 + Real.log c / 2 = Real.log c := by ring
    rw [hsum, Real.exp_log hc]
  have h := congrArg Real.sqrt h2
  rw [Real.sqrt_sq (Real.exp_nonneg _)] at h
  exact h.symm

/-- The three-quarter power of the bandwidth, elementarily. -/
def prolateRatioScale (a : ℝ) : ℝ :=
  Real.sqrt (signedModeRadialBandwidth a)
    * Real.sqrt (Real.sqrt (signedModeRadialBandwidth a))

theorem prolateRatioScale_pos {a : ℝ} (hc : 0 < signedModeRadialBandwidth a) :
    0 < prolateRatioScale a := by
  have h1 : 0 < Real.sqrt (signedModeRadialBandwidth a) := Real.sqrt_pos.2 hc
  rw [prolateRatioScale]
  exact mul_pos h1 (Real.sqrt_pos.2 h1)

theorem prolateRatioScale_eq_exp {a : ℝ} (hc : 0 < signedModeRadialBandwidth a) :
    prolateRatioScale a = Real.exp (3 * Real.log (signedModeRadialBandwidth a) / 4) := by
  have h1 : 0 < Real.sqrt (signedModeRadialBandwidth a) := Real.sqrt_pos.2 hc
  have e1 : Real.sqrt (signedModeRadialBandwidth a)
      = Real.exp (Real.log (signedModeRadialBandwidth a) / 2) := sqrt_eq_exp_half_log hc
  have e2 : Real.sqrt (Real.sqrt (signedModeRadialBandwidth a))
      = Real.exp (Real.log (signedModeRadialBandwidth a) / 4) := by
    rw [sqrt_eq_exp_half_log h1, Real.log_sqrt hc.le]
    congr 1
    ring
  rw [prolateRatioScale, e2, e1, ← Real.exp_add]
  congr 1
  ring

theorem exp_neg_three_quarter_log_eq {a : ℝ} (hc : 0 < signedModeRadialBandwidth a) :
    Real.exp (-(3 * Real.log (signedModeRadialBandwidth a) / 4)) = 1 / prolateRatioScale a := by
  rw [prolateRatioScale_eq_exp hc, Real.exp_neg, one_div]

/-- The constant of the vanishing ratio. -/
def ratioLimitConst (m n : ℕ) : ℝ :=
  324 * Real.sqrt 2 * Real.pi ^ (3 : ℕ) * (1 + leakageBarrierConst)
    * Real.exp (7 / 2 * Real.log (prolatePairAnchor m n)
        - Real.log (prolatePairAnchor m n ^ (2 : ℕ) / 2)
        - Real.log (1 - prolateLeakageCollar ^ (2 : ℕ))
        - 12 * Real.log (1 - prolateLeakageCollar))

theorem ratioLimitConst_nonneg (m n : ℕ) : 0 ≤ ratioLimitConst m n := by
  have h := leakageBarrierConst_nonneg
  have hπ := Real.pi_pos
  rw [ratioLimitConst]
  positivity

/-- **The squared amplitude of the higher rung is `O(c^{-1/2})` times that of the lower one.** -/
theorem eventually_prolateBand_sq_ratio_le_div_sqrt (m n : ℕ) (hmn : m < n) :
    ∀ᶠ a : ℝ in atTop,
      (signedModeRadialData a n).R (pairAnchorPoint m n a) ^ (2 : ℕ)
        ≤ ratioLimitConst m n / prolateRatioScale a
          * (signedModeRadialData a m).R (pairAnchorPoint m n a) ^ (2 : ℕ) := by
  have hn : 1 ≤ n := lt_of_le_of_lt (Nat.zero_le m) hmn
  set x₀ : ℝ := prolatePairAnchor m n with hx₀def
  have hx₀ : 0 < x₀ := prolatePairAnchor_pos m n
  have hxn : 4 * (4 * (n : ℝ) + 1) < x₀ ^ (2 : ℕ) := prolatePairAnchor_sq_gt m n n (Or.inr rfl)
  have hα1 : prolateLeakageCollar < 1 := prolateLeakageCollar_lt_one
  have hαh : (1 : ℝ) / 2 < prolateLeakageCollar := prolateLeakageCollar_gt_half
  have hα0 : (0 : ℝ) < 1 - prolateLeakageCollar := by linarith
  have hαsq : (0 : ℝ) < 1 - prolateLeakageCollar ^ (2 : ℕ) := by nlinarith
  have hcTop := tendsto_signedModeRadialBandwidth_atTop
  have hsn := tendsto_signedModeRadialBandwidth_mul_s_atTop n
  have hsm := tendsto_signedModeRadialBandwidth_mul_s_atTop m
  have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hmn
  -- eventual data
  have hc8 : ∀ᶠ a : ℝ in atTop, (8 : ℝ) ≤ signedModeRadialBandwidth a :=
    hcTop.eventually_ge_atTop 8
  have hclog : ∀ᶠ a : ℝ in atTop, 2 * x₀ ^ (2 : ℕ) ≤ signedModeRadialBandwidth a :=
    hcTop.eventually_ge_atTop _
  have hgap : ∀ᶠ a : ℝ in atTop,
      7 / 2 < signedModeRadialBandwidth a * (signedModeRadialData a n).s
        - signedModeRadialBandwidth a * (signedModeRadialData a m).s := by
    have := hsn.sub hsm
    refine this.eventually (eventually_gt_nhds ?_)
    linarith
  have hhalf : ∀ᶠ a : ℝ in atTop,
      signedModeRadialBandwidth a * (signedModeRadialData a n).s < x₀ ^ (2 : ℕ) / 2 := by
    refine hsn.eventually (eventually_lt_nhds ?_)
    linarith
  have hs64 : ∀ᶠ a : ℝ in atTop, (signedModeRadialData a n).s ≤ 1 / 64 :=
    eventually_signedModeRadialData_s_le n (by norm_num)
  filter_upwards [eventually_prolateBand_sq_ratio_le m n hn, hc8, hclog, hgap, hhalf, hs64,
    eventually_signedModeRadialData_s_pos n, eventually_signedModeRadialData_s_nonneg m,
    eventually_gt_atTop (0 : ℝ)]
    with a hratio hc8a hcloga hgapa hhalfa hs64a hsn0 hsm0 hapos
  set c : ℝ := signedModeRadialBandwidth a with hcdef
  have hc0 : (0 : ℝ) < c := by linarith
  set y₀ : ℝ := pairAnchorPoint m n a with hy₀def
  have hy₀0 : 0 < y₀ := pairAnchorPoint_pos hc0
  have hy₀sq : y₀ ^ (2 : ℕ) = x₀ ^ (2 : ℕ) / c := pairAnchorPoint_sq hc0
  have hsy0n : (signedModeRadialData a n).s < y₀ ^ (2 : ℕ) := by
    rw [hy₀sq, lt_div_iff₀ hc0]
    nlinarith [hhalfa, sq_nonneg x₀]
  have hy₀half : y₀ ^ (2 : ℕ) ≤ 1 / 2 := by
    rw [hy₀sq, div_le_iff₀ hc0]
    nlinarith [hcloga, hx₀]
  have hy₀1 : y₀ < 1 := by nlinarith [hy₀half, hy₀0]
  -- the logarithm of the anchor
  have hlogy : Real.log y₀ = Real.log x₀ - Real.log c / 2 := by
    rw [hy₀def, pairAnchorPoint, Real.log_div hx₀.ne' (Real.sqrt_pos.2 hc0).ne',
      Real.log_sqrt hc0.le]
  have hloghalf : 0 ≤ Real.log c / 2 - Real.log x₀ := by
    have h1 : Real.log (x₀ ^ (2 : ℕ)) ≤ Real.log c :=
      Real.log_le_log (by positivity) (by nlinarith [hcloga, hx₀])
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  -- the phase separation
  have hsmn : (signedModeRadialData a m).s ≤ (signedModeRadialData a n).s := by
    by_contra hcon
    rw [not_le] at hcon
    nlinarith [hgapa, hc0, hcon]
  have hsy0m : (signedModeRadialData a m).s < y₀ ^ (2 : ℕ) := lt_of_le_of_lt hsmn hsy0n
  have hphase := bandEndpointPhase_sub_ge (sm := (signedModeRadialData a m).s)
    (sn := (signedModeRadialData a n).s) (y := y₀) hsm0 hsmn hsy0n hy₀0 hy₀1
  have hlog1y : Real.log (1 / y₀) = Real.log c / 2 - Real.log x₀ := by
    rw [Real.log_div one_ne_zero hy₀0.ne', Real.log_one, hlogy]
    ring
  rw [hlog1y] at hphase
  -- the exponent
  have hExpBound : 2 * c
        * (bandEndpointPhase (signedModeRadialData a n).s y₀
          - bandEndpointPhase (signedModeRadialData a m).s y₀)
      + prolateScaleLog (signedModeRadialData a n).s y₀ prolateLeakageCollar
      - 12 * (Real.log (1 - prolateLeakageCollar) - Real.log (1 - y₀))
      ≤ (7 / 2 * Real.log x₀ - Real.log (x₀ ^ (2 : ℕ) / 2)
          - Real.log (1 - prolateLeakageCollar ^ (2 : ℕ))
          - 12 * Real.log (1 - prolateLeakageCollar)) - 3 * Real.log c / 4 := by
    -- the phase term
    have hphase' : 2 * c
        * (bandEndpointPhase (signedModeRadialData a n).s y₀
          - bandEndpointPhase (signedModeRadialData a m).s y₀)
        ≤ -(7 / 2 * (Real.log c / 2 - Real.log x₀)) := by
      have hmul := mul_le_mul_of_nonneg_left hphase (by positivity : (0 : ℝ) ≤ 2 * c)
      have hgapmul : 7 / 2 * (Real.log c / 2 - Real.log x₀)
          ≤ (c * (signedModeRadialData a n).s - c * (signedModeRadialData a m).s)
            * (Real.log c / 2 - Real.log x₀) :=
        mul_le_mul_of_nonneg_right (by linarith [hgapa]) hloghalf
      nlinarith [hmul, hgapmul]
    -- the scale logarithm
    have hscale : prolateScaleLog (signedModeRadialData a n).s y₀ prolateLeakageCollar
        ≤ Real.log c - Real.log (x₀ ^ (2 : ℕ) / 2) - Real.log (1 - prolateLeakageCollar ^ (2 : ℕ)) := by
      rw [prolateScaleLog]
      have h1 : Real.log (prolateLeakageCollar ^ (2 : ℕ) - (signedModeRadialData a n).s) ≤ 0 := by
        refine Real.log_nonpos (by nlinarith [hsn0]) ?_
        nlinarith [hsn0]
      have h2 : Real.log (x₀ ^ (2 : ℕ) / 2) - Real.log c
          ≤ Real.log (y₀ ^ (2 : ℕ) - (signedModeRadialData a n).s) := by
        have heq : Real.log (x₀ ^ (2 : ℕ) / 2) - Real.log c = Real.log (x₀ ^ (2 : ℕ) / 2 / c) := by
          rw [Real.log_div (by positivity) hc0.ne']
        have hstep : x₀ ^ (2 : ℕ) / 2 / c ≤ x₀ ^ (2 : ℕ) / c - (signedModeRadialData a n).s := by
          have hid : x₀ ^ (2 : ℕ) / c - (signedModeRadialData a n).s - x₀ ^ (2 : ℕ) / 2 / c
              = (x₀ ^ (2 : ℕ) / 2 - c * (signedModeRadialData a n).s) / c := by
            field_simp
            ring
          have hnn : 0 ≤ (x₀ ^ (2 : ℕ) / 2 - c * (signedModeRadialData a n).s) / c := by
            refine div_nonneg ?_ hc0.le
            linarith [hhalfa]
          linarith [hid, hnn]
        rw [heq, hy₀sq]
        exact Real.log_le_log (by positivity) hstep
      have h3 : Real.log (1 - y₀ ^ (2 : ℕ)) ≤ 0 :=
        Real.log_nonpos (by nlinarith [hy₀0, hy₀1]) (by nlinarith [hy₀0])
      linarith [h1, h2, h3]
    -- the collar logarithm
    have hcol : -12 * (Real.log (1 - prolateLeakageCollar) - Real.log (1 - y₀))
        ≤ -12 * Real.log (1 - prolateLeakageCollar) := by
      have : Real.log (1 - y₀) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
      linarith
    linarith [hphase', hscale, hcol]
  -- the barrier factor
  have hbar := barrierFactor_le (c := c) (s := (signedModeRadialData a n).s) hc8a hsn0 hs64a
  -- assemble
  set Kexp : ℝ := 7 / 2 * Real.log x₀ - Real.log (x₀ ^ (2 : ℕ) / 2)
      - Real.log (1 - prolateLeakageCollar ^ (2 : ℕ))
      - 12 * Real.log (1 - prolateLeakageCollar) with hKexp
  have hexple : Real.exp (2 * c
        * (bandEndpointPhase (signedModeRadialData a n).s y₀
          - bandEndpointPhase (signedModeRadialData a m).s y₀)
      + prolateScaleLog (signedModeRadialData a n).s y₀ prolateLeakageCollar
      - 12 * (Real.log (1 - prolateLeakageCollar) - Real.log (1 - y₀)))
      ≤ Real.exp Kexp / prolateRatioScale a := by
    have h := Real.exp_le_exp.2 hExpBound
    rw [show Kexp - 3 * Real.log c / 4 = Kexp + -(3 * Real.log c / 4) by ring, Real.exp_add,
      exp_neg_three_quarter_log_eq (by rw [← hcdef]; exact hc0)] at h
    calc _ ≤ Real.exp Kexp * (1 / prolateRatioScale a) := h
      _ = Real.exp Kexp / prolateRatioScale a := by ring
  have hCle : 1 + (1 - prolateLeakageCollar ^ (2 : ℕ))
      * (prolateRadialBarrier c (signedModeRadialData a n).s prolateLeakageCollar
        + 6 / (1 - prolateLeakageCollar)) ^ (2 : ℕ)
      / (c ^ (2 : ℕ) * (prolateLeakageCollar ^ (2 : ℕ) - (signedModeRadialData a n).s))
      ≤ 1 + leakageBarrierConst := by linarith [hbar]
  have hCnn : (0 : ℝ) ≤ 1 + (1 - prolateLeakageCollar ^ (2 : ℕ))
      * (prolateRadialBarrier c (signedModeRadialData a n).s prolateLeakageCollar
        + 6 / (1 - prolateLeakageCollar)) ^ (2 : ℕ)
      / (c ^ (2 : ℕ) * (prolateLeakageCollar ^ (2 : ℕ) - (signedModeRadialData a n).s)) := by
    have h1 : (0 : ℝ) < prolateLeakageCollar ^ (2 : ℕ) - (signedModeRadialData a n).s := by
      nlinarith [hsn0, hs64a]
    positivity
  have hRm : (0 : ℝ) ≤ (signedModeRadialData a m).R y₀ ^ (2 : ℕ) := sq_nonneg _
  have hexpnn : (0 : ℝ) ≤ Real.exp (2 * c
        * (bandEndpointPhase (signedModeRadialData a n).s y₀
          - bandEndpointPhase (signedModeRadialData a m).s y₀)
      + prolateScaleLog (signedModeRadialData a n).s y₀ prolateLeakageCollar
      - 12 * (Real.log (1 - prolateLeakageCollar) - Real.log (1 - y₀))) := (Real.exp_pos _).le
  have hbase : (0 : ℝ) ≤ 324 * Real.sqrt 2 * Real.pi ^ (3 : ℕ) := by
    have := Real.pi_pos
    positivity
  refine le_trans hratio ?_
  have hstep : 324 * Real.sqrt 2 * Real.pi ^ (3 : ℕ)
      * (1 + (1 - prolateLeakageCollar ^ (2 : ℕ))
        * (prolateRadialBarrier c (signedModeRadialData a n).s prolateLeakageCollar
          + 6 / (1 - prolateLeakageCollar)) ^ (2 : ℕ)
        / (c ^ (2 : ℕ) * (prolateLeakageCollar ^ (2 : ℕ) - (signedModeRadialData a n).s)))
      * Real.exp (2 * c
          * (bandEndpointPhase (signedModeRadialData a n).s y₀
            - bandEndpointPhase (signedModeRadialData a m).s y₀)
        + prolateScaleLog (signedModeRadialData a n).s y₀ prolateLeakageCollar
        - 12 * (Real.log (1 - prolateLeakageCollar) - Real.log (1 - y₀)))
      ≤ ratioLimitConst m n / prolateRatioScale a := by
    have h1 : 324 * Real.sqrt 2 * Real.pi ^ (3 : ℕ)
        * (1 + (1 - prolateLeakageCollar ^ (2 : ℕ))
          * (prolateRadialBarrier c (signedModeRadialData a n).s prolateLeakageCollar
            + 6 / (1 - prolateLeakageCollar)) ^ (2 : ℕ)
          / (c ^ (2 : ℕ) * (prolateLeakageCollar ^ (2 : ℕ) - (signedModeRadialData a n).s)))
        ≤ 324 * Real.sqrt 2 * Real.pi ^ (3 : ℕ) * (1 + leakageBarrierConst) :=
      mul_le_mul_of_nonneg_left hCle hbase
    have h2 := mul_le_mul h1 hexple hexpnn
      (by
        have := leakageBarrierConst_nonneg
        have := Real.pi_pos
        positivity)
    calc _ ≤ 324 * Real.sqrt 2 * Real.pi ^ (3 : ℕ) * (1 + leakageBarrierConst)
        * (Real.exp Kexp / prolateRatioScale a) := h2
      _ = ratioLimitConst m n / prolateRatioScale a := by
          rw [ratioLimitConst, ← hx₀def, hKexp]
          ring
  exact mul_le_mul_of_nonneg_right hstep hRm

end RHTower

end

import GaloisForLFunctions.RHTower.ProlateIndexedSharpRatio
import GaloisForLFunctions.RHTower.ProlateOscillatorLawAssembly

/-!
# The sharp exponent is `−2(n−m) log c` up to a bounded remainder

`prolateBand_sharp_exponent_le` bounds the sharp transport exponent by

```text
−c(s_n − s_m)·log(1/y₀)  +  (log(y₀² − s_m) − log(y₀² − s_n))/2  +  ∫err_n + ∫err_m .
```

At the pair anchor `y₀ = x₀/√c` one has `log(1/y₀) = ½ log c − log x₀`, and the two-sided oscillator
law gives `c(s_n − s_m) ≥ 4(n−m) − K c^{-1/4}`.  Writing `c = r⁸` with `r = c^{1/8}` turns every
logarithm into `log r ≤ r`, so the correction the law leaves is `4K/r`, which is eventually below
one.  The leading term is then exactly `−2(n−m) log c`.
-/

noncomputable section

open Set Filter Topology

namespace RHTower

open GaloisForLFunctions.RHTower

/-- The eighth root of the bandwidth. -/
def bandwidthEighthRoot (a : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (Real.sqrt (signedModeRadialBandwidth a)))

theorem bandwidthEighthRoot_pos {a : ℝ} (hc : 0 < signedModeRadialBandwidth a) :
    0 < bandwidthEighthRoot a :=
  Real.sqrt_pos.2 (Real.sqrt_pos.2 (Real.sqrt_pos.2 hc))

theorem bandwidthEighthRoot_pow {a : ℝ} (hc : 0 < signedModeRadialBandwidth a) :
    bandwidthEighthRoot a ^ 8 = signedModeRadialBandwidth a := by
  have hs : 0 < Real.sqrt (signedModeRadialBandwidth a) := Real.sqrt_pos.2 hc
  have hss : 0 < Real.sqrt (Real.sqrt (signedModeRadialBandwidth a)) := Real.sqrt_pos.2 hs
  have h1 : bandwidthEighthRoot a ^ 2 = Real.sqrt (Real.sqrt (signedModeRadialBandwidth a)) :=
    Real.sq_sqrt hss.le
  have h2 : Real.sqrt (Real.sqrt (signedModeRadialBandwidth a)) ^ 2
      = Real.sqrt (signedModeRadialBandwidth a) := Real.sq_sqrt hs.le
  have h3 : Real.sqrt (signedModeRadialBandwidth a) ^ 2 = signedModeRadialBandwidth a :=
    Real.sq_sqrt hc.le
  calc bandwidthEighthRoot a ^ 8 = ((bandwidthEighthRoot a ^ 2) ^ 2) ^ 2 := by ring
    _ = signedModeRadialBandwidth a := by rw [h1, h2, h3]

theorem bandwidthEighthRoot_sq {a : ℝ} (hc : 0 < signedModeRadialBandwidth a) :
    bandwidthEighthRoot a ^ 2 = Real.sqrt (Real.sqrt (signedModeRadialBandwidth a)) :=
  Real.sq_sqrt (Real.sqrt_pos.2 (Real.sqrt_pos.2 hc)).le

theorem tendsto_bandwidthEighthRoot_atTop :
    Tendsto bandwidthEighthRoot atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp
    (Real.tendsto_sqrt_atTop.comp tendsto_signedModeRadialBandwidth_atTop))

/-- The logarithm of the reciprocal pair-anchor point. -/
theorem log_inv_pairAnchorPoint {m n : ℕ} {a : ℝ} (hc : 0 < signedModeRadialBandwidth a) :
    Real.log (1 / pairAnchorPoint m n a)
      = 1 / 2 * Real.log (signedModeRadialBandwidth a) - Real.log (prolatePairAnchor m n) := by
  have hx₀ : 0 < prolatePairAnchor m n := prolatePairAnchor_pos m n
  have hsc : 0 < Real.sqrt (signedModeRadialBandwidth a) := Real.sqrt_pos.2 hc
  have hval : pairAnchorPoint m n a
      = prolatePairAnchor m n / Real.sqrt (signedModeRadialBandwidth a) := rfl
  rw [hval, one_div_div, Real.log_div hsc.ne' hx₀.ne', Real.log_sqrt hc.le]
  ring

/-- **The phase term of the sharp exponent.**  Eventually it is below `−2(n−m) log c` plus an
explicit constant. -/
theorem eventually_sharpPhase_le (m n : ℕ) (hmn : m < n) :
    ∀ᶠ a : ℝ in atTop,
      -(signedModeRadialBandwidth a
          * ((signedModeRadialData a n).s - (signedModeRadialData a m).s)
          * Real.log (1 / pairAnchorPoint m n a))
        ≤ -(2 * ((n : ℝ) - (m : ℝ)) * Real.log (signedModeRadialBandwidth a))
          + (4 * ((n : ℝ) - (m : ℝ)) * Real.log (prolatePairAnchor m n) + 1) := by
  obtain ⟨Kn, hKn0, hKn⟩ := exists_rate_abs_signedModeRadialBandwidth_mul_s_sub_rung n
  obtain ⟨Km, hKm0, hKm⟩ := exists_rate_abs_signedModeRadialBandwidth_mul_s_sub_rung m
  have hx₀2 : 2 ≤ prolatePairAnchor m n := prolatePairAnchor_ge_two m n
  have hx₀ : 0 < prolatePairAnchor m n := by linarith
  set L : ℝ := Real.log (prolatePairAnchor m n) with hLdef
  have hL0 : 0 ≤ L := by
    rw [hLdef]
    have : Real.log 1 ≤ Real.log (prolatePairAnchor m n) :=
      Real.log_le_log (by norm_num) (by linarith)
    simpa using this
  have hnm : (0 : ℝ) < (n : ℝ) - (m : ℝ) := by
    have : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
    linarith
  have hcollar : (0 : ℝ) < 1 - prolateLeakageCollar := by
    rw [prolateLeakageCollar]; norm_num
  have hαh : (1 : ℝ) / 2 < prolateLeakageCollar := prolateLeakageCollar_gt_half
  have hcTop := tendsto_signedModeRadialBandwidth_atTop
  filter_upwards [hKn, hKm, eventually_gt_atTop (0 : ℝ),
    hcTop.eventually_gt_atTop (0 : ℝ),
    hcTop.eventually_ge_atTop (prolatePairAnchor m n ^ 2 / prolateLeakageCollar ^ 2),
    tendsto_bandwidthEighthRoot_atTop.eventually_ge_atTop (max 1 (4 * (Kn + Km)))]
    with a hKna hKma hapos hc0 hclarge hr
  set c : ℝ := signedModeRadialBandwidth a with hcdef
  set r : ℝ := bandwidthEighthRoot a with hrdef
  have hr1 : (1 : ℝ) ≤ r := le_trans (le_max_left _ _) hr
  have hrK : 4 * (Kn + Km) ≤ r := le_trans (le_max_right _ _) hr
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  have hr8 : r ^ 8 = c := bandwidthEighthRoot_pow hc0
  have hr2 : r ^ 2 = Real.sqrt (Real.sqrt c) := bandwidthEighthRoot_sq hc0
  -- the anchor sits inside the collar
  set y₀ : ℝ := pairAnchorPoint m n a with hy₀def
  have hy₀0 : 0 < y₀ := pairAnchorPoint_pos hc0
  have hy₀sq : y₀ ^ 2 = prolatePairAnchor m n ^ 2 / c := pairAnchorPoint_sq hc0
  have hy₀α : y₀ ≤ prolateLeakageCollar := by
    have hsq : y₀ ^ 2 ≤ prolateLeakageCollar ^ 2 := by
      rw [hy₀sq, div_le_iff₀ hc0]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < prolateLeakageCollar ^ 2)] at hclarge
      linarith [hclarge]
    nlinarith [hy₀0, hαh]
  have hy₀1 : y₀ < 1 := lt_of_le_of_lt hy₀α prolateLeakageCollar_lt_one
  -- the logarithm at the anchor
  have hlogc : Real.log c = 8 * Real.log r := by
    rw [← hr8, Real.log_pow]
    push_cast
    ring
  have hlogeq : Real.log (1 / y₀) = 4 * Real.log r - L := by
    rw [hy₀def, log_inv_pairAnchorPoint hc0, ← hcdef, hlogc, ← hLdef]
    ring
  have hlogr : Real.log r ≤ r := by
    have := Real.log_le_sub_one_of_pos hr0
    linarith
  have hlog0 : 0 ≤ Real.log (1 / y₀) := by
    rw [Real.log_nonneg_iff (by positivity)]
    rw [le_div_iff₀ hy₀0]
    linarith [hy₀1]
  -- the separation lower bound from the oscillator law
  have hsep : 4 * ((n : ℝ) - (m : ℝ)) - (Kn + Km) / r ^ 2
      ≤ c * ((signedModeRadialData a n).s - (signedModeRadialData a m).s) := by
    rw [← hr2] at hKna hKma
    have h1 := abs_le.1 hKna
    have h2 := abs_le.1 hKma
    have hexp : c * ((signedModeRadialData a n).s - (signedModeRadialData a m).s)
        = c * (signedModeRadialData a n).s - c * (signedModeRadialData a m).s := by ring
    rw [hexp]
    have hsplit : (Kn + Km) / r ^ 2 = Kn / r ^ 2 + Km / r ^ 2 := by ring
    rw [hsplit]
    linarith [h1.1, h2.2]
  -- assemble
  have hprod : -(c * ((signedModeRadialData a n).s - (signedModeRadialData a m).s)
      * Real.log (1 / y₀))
      ≤ -((4 * ((n : ℝ) - (m : ℝ)) - (Kn + Km) / r ^ 2) * Real.log (1 / y₀)) := by
    have := mul_le_mul_of_nonneg_right hsep hlog0
    linarith
  have hsmall : (Kn + Km) / r ^ 2 * (4 * Real.log r - L) ≤ 1 := by
    have hbound : 4 * Real.log r - L ≤ 4 * r := by
      linarith [hlogr, hL0]
    have hKsum : 0 ≤ Kn + Km := by linarith
    have hstep : (Kn + Km) / r ^ 2 * (4 * Real.log r - L) ≤ (Kn + Km) / r ^ 2 * (4 * r) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    have hid : (Kn + Km) / r ^ 2 * (4 * r) = 4 * (Kn + Km) / r := by
      field_simp
    rw [hid] at hstep
    have hfin : 4 * (Kn + Km) / r ≤ 1 := by
      rw [div_le_one hr0]
      exact hrK
    linarith
  have hmain : -((4 * ((n : ℝ) - (m : ℝ)) - (Kn + Km) / r ^ 2) * Real.log (1 / y₀))
      ≤ -(2 * ((n : ℝ) - (m : ℝ)) * Real.log c)
        + (4 * ((n : ℝ) - (m : ℝ)) * L + 1) := by
    have hexpand : -((4 * ((n : ℝ) - (m : ℝ)) - (Kn + Km) / r ^ 2) * Real.log (1 / y₀))
        = -(4 * ((n : ℝ) - (m : ℝ)) * Real.log (1 / y₀))
          + (Kn + Km) / r ^ 2 * Real.log (1 / y₀) := by ring
    rw [hexpand, hlogeq, hlogc]
    linarith [hsmall]
  linarith [hprod, hmain]

end RHTower

end

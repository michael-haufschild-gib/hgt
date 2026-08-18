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

set_option maxHeartbeats 3200000

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


/-- **The scale-logarithm difference is eventually bounded.**  Each scale logarithm separately grows
like `log c`; the growth cancels between the two rungs. -/
theorem exists_bound_eventually_scaleLogDiff (m n : ℕ) :
    ∃ S : ℝ, ∀ᶠ a : ℝ in atTop,
      (Real.log (pairAnchorPoint m n a ^ 2 - (signedModeRadialData a m).s)
        - Real.log (pairAnchorPoint m n a ^ 2 - (signedModeRadialData a n).s)) / 2 ≤ S := by
  set Λ : ℝ := Real.log (prolatePairAnchor m n ^ 2 - (4 * (m : ℝ) + 1))
    - Real.log (prolatePairAnchor m n ^ 2 - (4 * (n : ℝ) + 1)) with hΛ
  refine ⟨Λ / 2 + 1, ?_⟩
  have h := (tendsto_pairAnchor_scaleLog m n).eventually
    (eventually_lt_nhds (by linarith : Λ < Λ + 2))
  filter_upwards [h] with a ha
  linarith


/-- **The transport error integral is eventually bounded.**  At the pair anchor every piece of
`integral_prolateBandErrorMajorant_le` is `O(c)`, and the prefactor is `1/c`. -/
theorem exists_bound_eventually_integral_errorMajorant (m n k : ℕ) (hk : k = m ∨ k = n) :
    ∃ E : ℝ, ∀ᶠ a : ℝ in atTop,
      (∫ t in pairAnchorPoint m n a..prolateLeakageCollar,
        prolateBandErrorMajorant (signedModeRadialBandwidth a) (signedModeRadialData a k).s
          (pairAnchorPoint m n a) prolateLeakageCollar t) ≤ E := by
  set x₀ : ℝ := prolatePairAnchor m n with hx₀def
  have hx₀2 : 2 ≤ x₀ := prolatePairAnchor_ge_two m n
  have hx₀0 : 0 < x₀ := by linarith
  set α : ℝ := prolateLeakageCollar with hαdef
  have hα1 : α < 1 := prolateLeakageCollar_lt_one
  have hαh : (1 : ℝ) / 2 < α := prolateLeakageCollar_gt_half
  have hα0 : 0 < 1 - α := by linarith
  have hαsq : (0 : ℝ) < 1 - α ^ 2 := by nlinarith [hα1, hαh]
  set M : ℝ := 9 / (1 - α) with hMdef
  have hM0 : 0 < M := by rw [hMdef]; positivity
  refine ⟨2 + 6 * (1 + M) * prolatePairAnchor m n
    + (4 * M + 3 / (1 - α ^ 2) + 2 * M ^ 2 + 3 * M / (1 - α ^ 2)), ?_⟩
  have hcTop := tendsto_signedModeRadialBandwidth_atTop
  have hulo : ∀ᶠ a : ℝ in atTop,
      (1 : ℝ) / 2 ≤ signedModeRadialBandwidth a * (signedModeRadialData a k).s := by
    have h := (tendsto_signedModeRadialBandwidth_mul_s_atTop k).eventually
      (eventually_gt_nhds (by
        have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith : (1 : ℝ) / 2 < 4 * (k : ℝ) + 1))
    exact h.mono fun a ha => ha.le
  filter_upwards [eventually_gt_atTop (0 : ℝ), hcTop.eventually_gt_atTop (0 : ℝ),
    hcTop.eventually_ge_atTop (1 : ℝ),
    hcTop.eventually_ge_atTop (x₀ ^ 2 / α ^ 2),
    eventually_signedModeRadialData_s_pos k, hulo,
    eventually_two_mul_s_le_pairAnchorPoint_sq m n k hk] with a hapos hc0 hc1 hclarge hs0 hulo2 h2s
  set c : ℝ := signedModeRadialBandwidth a with hcdef
  set s : ℝ := (signedModeRadialData a k).s with hsdef
  set y₀ : ℝ := pairAnchorPoint m n a with hy₀def
  have hy₀0 : 0 < y₀ := pairAnchorPoint_pos hc0
  have hy₀sq : y₀ ^ 2 = x₀ ^ 2 / c := pairAnchorPoint_sq hc0
  have hy₀val : y₀ = x₀ / Real.sqrt c := rfl
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc0
  have hsc1 : (1 : ℝ) ≤ Real.sqrt c := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt c := Real.sqrt_le_sqrt hc1
  have hsc2 : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc0.le
  have hy₀α : y₀ ≤ α := by
    have hsq : y₀ ^ 2 ≤ α ^ 2 := by
      rw [hy₀sq, div_le_iff₀ hc0]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < α ^ 2)] at hclarge
      linarith [hclarge]
    nlinarith [hy₀0, hαh]
  have hsy0 : s < y₀ ^ 2 := by nlinarith [h2s, hs0]
  -- the two crude lower bounds
  have hslo : 1 / (2 * c) ≤ s := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hulo2]
  have hgap : x₀ ^ 2 / (2 * c) ≤ y₀ ^ 2 - s := by
    have hhalf : y₀ ^ 2 / 2 ≤ y₀ ^ 2 - s := by linarith [h2s]
    have hid : x₀ ^ 2 / (2 * c) = y₀ ^ 2 / 2 := by
      rw [hy₀sq]
      ring
    rw [hid]
    exact hhalf
  have hsqrtgap : x₀ / (2 * Real.sqrt c) ≤ Real.sqrt (y₀ ^ 2 - s) := by
    rw [show (x₀ / (2 * Real.sqrt c)) = Real.sqrt ((x₀ / (2 * Real.sqrt c)) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt ?_
    have hval : (x₀ / (2 * Real.sqrt c)) ^ 2 = x₀ ^ 2 / (4 * c) := by
      rw [div_pow, mul_pow, hsc2]
      ring
    rw [hval]
    refine le_trans ?_ hgap
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hx₀0, hc0]
  have hsqrtpos : 0 < Real.sqrt (y₀ ^ 2 - s) := Real.sqrt_pos.2 (by linarith [hsy0])
  -- reciprocal bounds
  have hinvy : 1 / y₀ ≤ Real.sqrt c := by
    rw [hy₀val, one_div_div, div_le_iff₀ hx₀0]
    nlinarith [hsc, hx₀2]
  have hinvs : 1 / s ≤ 2 * c := by
    rw [div_le_iff₀ hs0]
    nlinarith [hulo2]
  have hinvg : 1 / Real.sqrt (y₀ ^ 2 - s) ≤ Real.sqrt c := by
    rw [div_le_iff₀ hsqrtpos]
    have h := mul_le_mul_of_nonneg_left hsqrtgap hsc.le
    have hid : Real.sqrt c * (x₀ / (2 * Real.sqrt c)) = x₀ / 2 := by
      field_simp
    rw [hid] at h
    linarith [hx₀2, h]
  have hy₀le : y₀ ≤ x₀ / Real.sqrt c := le_of_eq hy₀val
  set Q : ℝ := 4 * M + 3 / (1 - α ^ 2) + 2 * M ^ 2 + 3 * M / (1 - α ^ 2) with hQdef
  have hQ0 : 0 < Q := by rw [hQdef]; positivity
  refine le_trans (integral_prolateBandErrorMajorant_le hc0 hs0 hy₀0 hsy0 hy₀α hα1) ?_
  have hAle : 2 * (1 / y₀ ^ 2) ≤ 2 * c := by
    have hid : (1 : ℝ) / y₀ ^ 2 = (1 / y₀) ^ 2 := by
      rw [div_pow]
      norm_num
    rw [hid]
    have hsq : (1 / y₀) ^ 2 ≤ Real.sqrt c ^ 2 :=
      pow_le_pow_left₀ (by positivity) hinvy 2
    rw [hsc2] at hsq
    linarith
  have hBle : 3 * (1 + 9 / (1 - α)) * (y₀ / (s * Real.sqrt (y₀ ^ 2 - s)))
      ≤ 6 * (1 + M) * x₀ * c := by
    have hid : y₀ / (s * Real.sqrt (y₀ ^ 2 - s))
        = y₀ * (1 / s) * (1 / Real.sqrt (y₀ ^ 2 - s)) := by
      field_simp
    rw [hid, ← hMdef]
    have hstep : y₀ * (1 / s) * (1 / Real.sqrt (y₀ ^ 2 - s))
        ≤ x₀ / Real.sqrt c * (2 * c) * Real.sqrt c := by
      refine mul_le_mul (mul_le_mul hy₀le hinvs (by positivity) (by positivity)) hinvg
        (by positivity) (by positivity)
    have hval : x₀ / Real.sqrt c * (2 * c) * Real.sqrt c = 2 * x₀ * c := by
      field_simp
    rw [hval] at hstep
    nlinarith [hstep, hM0, hx₀0, hc0]
  have hCle : (4 * (9 / (1 - α)) / y₀ + 2 * (9 / (1 - α)) ^ 2
        + 3 * (1 / y₀ + 9 / (1 - α)) / (1 - α ^ 2))
      * ((α - y₀) / Real.sqrt (y₀ ^ 2 - s)) ≤ Q * c := by
    rw [← hMdef]
    have hbracket : 4 * M / y₀ + 2 * M ^ 2 + 3 * (1 / y₀ + M) / (1 - α ^ 2)
        ≤ Q * Real.sqrt c := by
      have h1 : 4 * M / y₀ = 4 * M * (1 / y₀) := by ring
      have h2 : 3 * (1 / y₀ + M) / (1 - α ^ 2)
          = 3 / (1 - α ^ 2) * (1 / y₀) + 3 * M / (1 - α ^ 2) := by
        field_simp
      rw [h1, h2, hQdef]
      have hM4 : 4 * M * (1 / y₀) ≤ 4 * M * Real.sqrt c :=
        mul_le_mul_of_nonneg_left hinvy (by positivity)
      have hM3 : 3 / (1 - α ^ 2) * (1 / y₀) ≤ 3 / (1 - α ^ 2) * Real.sqrt c :=
        mul_le_mul_of_nonneg_left hinvy (by positivity)
      have hM2 : 2 * M ^ 2 ≤ 2 * M ^ 2 * Real.sqrt c := by nlinarith [hsc1, hM0]
      have hM1 : 3 * M / (1 - α ^ 2) ≤ 3 * M / (1 - α ^ 2) * Real.sqrt c := by
        have hpos : (0 : ℝ) ≤ 3 * M / (1 - α ^ 2) := by positivity
        nlinarith [hsc1, hpos]
      nlinarith [hM4, hM3, hM2, hM1]
    have hratio : (α - y₀) / Real.sqrt (y₀ ^ 2 - s) ≤ Real.sqrt c := by
      have hid : (α - y₀) / Real.sqrt (y₀ ^ 2 - s)
          = (α - y₀) * (1 / Real.sqrt (y₀ ^ 2 - s)) := by ring
      rw [hid]
      have hnum : α - y₀ ≤ 1 := by linarith [hy₀0, hα1]
      have hnum0 : (0 : ℝ) ≤ α - y₀ := by linarith [hy₀α]
      have hstep : (α - y₀) * (1 / Real.sqrt (y₀ ^ 2 - s)) ≤ 1 * Real.sqrt c :=
        mul_le_mul hnum hinvg (by positivity) (by norm_num)
      linarith [hstep]
    have hb0 : (0 : ℝ) ≤ 4 * M / y₀ + 2 * M ^ 2 + 3 * (1 / y₀ + M) / (1 - α ^ 2) := by
      have hy : (0 : ℝ) < 1 / y₀ := by positivity
      positivity
    have hr0 : (0 : ℝ) ≤ (α - y₀) / Real.sqrt (y₀ ^ 2 - s) := by
      have hnn : (0 : ℝ) ≤ α - y₀ := by linarith [hy₀α]
      positivity
    calc (4 * M / y₀ + 2 * M ^ 2 + 3 * (1 / y₀ + M) / (1 - α ^ 2))
          * ((α - y₀) / Real.sqrt (y₀ ^ 2 - s))
        ≤ Q * Real.sqrt c * Real.sqrt c := mul_le_mul hbracket hratio hr0 (by positivity)
      _ = Q * c := by
          have hmm : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc0.le
          calc Q * Real.sqrt c * Real.sqrt c = Q * (Real.sqrt c * Real.sqrt c) := by ring
            _ = Q * c := by rw [hmm]
  have hfinal : 2 * (1 / y₀ ^ 2)
      + 3 * (1 + 9 / (1 - α)) * (y₀ / (s * Real.sqrt (y₀ ^ 2 - s)))
      + (4 * (9 / (1 - α)) / y₀ + 2 * (9 / (1 - α)) ^ 2
          + 3 * (1 / y₀ + 9 / (1 - α)) / (1 - α ^ 2))
        * ((α - y₀) / Real.sqrt (y₀ ^ 2 - s))
      ≤ c * (2 + 6 * (1 + M) * x₀ + Q) := by
    have hexp : c * (2 + 6 * (1 + M) * x₀ + Q)
        = 2 * c + 6 * (1 + M) * x₀ * c + Q * c := by ring
    rw [hexp]
    linarith [hAle, hBle, hCle]
  calc 1 / c * (2 * (1 / y₀ ^ 2)
        + 3 * (1 + 9 / (1 - α)) * (y₀ / (s * Real.sqrt (y₀ ^ 2 - s)))
        + (4 * (9 / (1 - α)) / y₀ + 2 * (9 / (1 - α)) ^ 2
            + 3 * (1 / y₀ + 9 / (1 - α)) / (1 - α ^ 2))
          * ((α - y₀) / Real.sqrt (y₀ ^ 2 - s)))
      ≤ 1 / c * (c * (2 + 6 * (1 + M) * x₀ + Q)) :=
        mul_le_mul_of_nonneg_left hfinal (by positivity)
    _ = 2 + 6 * (1 + M) * x₀ + Q := by field_simp


/-- **The sharp exponent is `−2(n−m) log c` up to a bounded remainder.** -/
theorem exists_bound_sharpExponent (m n : ℕ) (hmn : m < n) :
    ∃ E : ℝ, ∀ᶠ a : ℝ in atTop,
      2 * sharpCollarPhase n a - 2 * sharpCollarPhase m a
        + sharpTransportUpper m n n a - sharpTransportLower m n m a
        ≤ -(2 * ((n : ℝ) - (m : ℝ)) * Real.log (signedModeRadialBandwidth a)) + E := by
  obtain ⟨S, hS⟩ := exists_bound_eventually_scaleLogDiff m n
  obtain ⟨En, hEn⟩ := exists_bound_eventually_integral_errorMajorant m n n (Or.inr rfl)
  obtain ⟨Em, hEm⟩ := exists_bound_eventually_integral_errorMajorant m n m (Or.inl rfl)
  refine ⟨(4 * ((n : ℝ) - (m : ℝ)) * Real.log (prolatePairAnchor m n) + 1) + S + En + Em, ?_⟩
  have hx₀2 : 2 ≤ prolatePairAnchor m n := prolatePairAnchor_ge_two m n
  have hx₀0 : (0 : ℝ) < prolatePairAnchor m n := by linarith
  have hα1 : prolateLeakageCollar < 1 := prolateLeakageCollar_lt_one
  have hαh : (1 : ℝ) / 2 < prolateLeakageCollar := prolateLeakageCollar_gt_half
  have hcTop := tendsto_signedModeRadialBandwidth_atTop
  filter_upwards [eventually_sharpPhase_le m n hmn, hS, hEn, hEm,
    eventually_gt_atTop (0 : ℝ), hcTop.eventually_gt_atTop (0 : ℝ),
    hcTop.eventually_ge_atTop (prolatePairAnchor m n ^ 2 / prolateLeakageCollar ^ 2),
    eventually_signedModeRadialData_s_nonneg m,
    eventually_two_mul_s_le_pairAnchorPoint_sq m n n (Or.inr rfl)]
    with a hphase hSa hEna hEma hapos hc0 hclarge hsm0 h2sn
  set c : ℝ := signedModeRadialBandwidth a with hcdef
  set y₀ : ℝ := pairAnchorPoint m n a with hy₀def
  have hy₀0 : 0 < y₀ := pairAnchorPoint_pos hc0
  have hy₀sq : y₀ ^ 2 = prolatePairAnchor m n ^ 2 / c := pairAnchorPoint_sq hc0
  have hy₀α : y₀ ≤ prolateLeakageCollar := by
    have hsq : y₀ ^ 2 ≤ prolateLeakageCollar ^ 2 := by
      rw [hy₀sq, div_le_iff₀ hc0]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < prolateLeakageCollar ^ 2)] at hclarge
      linarith [hclarge]
    nlinarith [hy₀0, hαh]
  have hy₀1 : y₀ < 1 := lt_of_le_of_lt hy₀α hα1
  have hsn0 : 0 < (signedModeRadialData a n).s := by
    have h := signedModeRadialData_s_strictMono hapos hmn
    linarith [hsm0]
  have hsy0n : (signedModeRadialData a n).s < y₀ ^ 2 := by nlinarith [h2sn, hsn0]
  have hsmn : (signedModeRadialData a m).s ≤ (signedModeRadialData a n).s :=
    (signedModeRadialData_s_strictMono hapos hmn).le
  have hbase := prolateBand_sharp_exponent_le (c := c)
    (sn := (signedModeRadialData a n).s) (sm := (signedModeRadialData a m).s)
    (a := y₀) (α := prolateLeakageCollar) hc0 hy₀0 hsm0 hsmn hsy0n hy₀α hα1 hy₀1
  refine le_trans hbase ?_
  linarith [hphase, hSa, hEna, hEma]


/-- **The amplitude ratio at the pair anchor is an explicit inverse power of the bandwidth.**
This is the sharp form of the crude `c^{-3/4}` ratio: the exponent is exactly `2(n−m)`. -/
theorem exists_bound_prolateBand_sq_ratio_power (m n : ℕ) (hmn : m < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ a : ℝ in atTop,
      (signedModeRadialData a n).R (pairAnchorPoint m n a) ^ 2
        ≤ C / signedModeRadialBandwidth a ^ (2 * (n - m))
          * (signedModeRadialData a m).R (pairAnchorPoint m n a) ^ 2 := by
  obtain ⟨E, hE⟩ := exists_bound_sharpExponent m n hmn
  have hα1 : prolateLeakageCollar < 1 := prolateLeakageCollar_lt_one
  have hαh : (1 : ℝ) / 2 < prolateLeakageCollar := prolateLeakageCollar_gt_half
  have hα0 : (0 : ℝ) < prolateLeakageCollar := by linarith
  refine ⟨4050 * Real.pi ^ 3 * (2 * Real.sqrt 2) * Real.exp E, by positivity, ?_⟩
  have hcTop := tendsto_signedModeRadialBandwidth_atTop
  filter_upwards [eventually_prolateBand_sq_ratio_sharp m n, hE,
    eventually_gt_atTop (0 : ℝ), hcTop.eventually_gt_atTop (0 : ℝ),
    eventually_signedModeRadialData_s_nonneg m,
    eventually_signedModeRadialData_s_le n (by norm_num : (0 : ℝ) < 1 / 8)]
    with a hratio hexp hapos hc0 hsm0 hsn8
  set c : ℝ := signedModeRadialBandwidth a with hcdef
  have hsnα : (signedModeRadialData a n).s < prolateLeakageCollar ^ 2 := by nlinarith [hsn8, hαh]
  have hΞn : 0 < bandEndpointPhase (signedModeRadialData a n).s prolateLeakageCollar :=
    bandEndpointPhase_pos hα1 hsnα hα0
  have hΞm : bandEndpointPhase (signedModeRadialData a m).s prolateLeakageCollar
      ≤ 2 * Real.sqrt 2 * bandEndpointPhase (signedModeRadialData a n).s prolateLeakageCollar :=
    bandEndpointPhase_le_two_sqrt_two_mul hsm0 hαh (le_of_lt hα1) hsn8
  -- the collar-phase ratio is bounded
  have hphaseratio : sharpCollarPhase m a / sharpCollarPhase n a ≤ 2 * Real.sqrt 2 := by
    have hn0 : 0 < sharpCollarPhase n a := by
      rw [sharpCollarPhase]
      exact mul_pos hc0 hΞn
    rw [div_le_iff₀ hn0, sharpCollarPhase, sharpCollarPhase]
    nlinarith [hΞm, hc0, hΞn]
  have hphase0 : 0 ≤ sharpCollarPhase m a / sharpCollarPhase n a := by
    have hm0 : 0 ≤ sharpCollarPhase m a := by
      rw [sharpCollarPhase]
      exact mul_nonneg hc0.le (bandEndpointPhase_nonneg _ _)
    have hn0 : 0 < sharpCollarPhase n a := by
      rw [sharpCollarPhase]
      exact mul_pos hc0 hΞn
    positivity
  -- the exponential is the inverse power
  set N : ℕ := 2 * (n - m) with hNdef
  have hNcast : (N : ℝ) = 2 * ((n : ℝ) - (m : ℝ)) := by
    rw [hNdef]
    push_cast [Nat.cast_sub hmn.le]
    ring
  have hexppow : Real.exp (2 * sharpCollarPhase n a - 2 * sharpCollarPhase m a
      + sharpTransportUpper m n n a - sharpTransportLower m n m a)
      ≤ Real.exp E / c ^ N := by
    have hmono := Real.exp_le_exp.2 hexp
    refine le_trans hmono ?_
    have hid : Real.exp (-(2 * ((n : ℝ) - (m : ℝ)) * Real.log c) + E)
        = Real.exp E / c ^ N := by
      rw [Real.exp_add, ← hNcast]
      have hcpow : Real.exp ((N : ℝ) * Real.log c) = c ^ N := by
        rw [Real.exp_nat_mul, Real.exp_log hc0]
      rw [Real.exp_neg, hcpow]
      field_simp
    rw [hid]
  -- assemble
  have hRm : (0 : ℝ) ≤ (signedModeRadialData a m).R (pairAnchorPoint m n a) ^ 2 := sq_nonneg _
  have hpi : (0 : ℝ) < 4050 * Real.pi ^ 3 := by positivity
  have hcN : (0 : ℝ) < c ^ N := by positivity
  refine le_trans hratio ?_
  have hstep : 4050 * Real.pi ^ 3 * (sharpCollarPhase m a / sharpCollarPhase n a)
      * Real.exp (2 * sharpCollarPhase n a - 2 * sharpCollarPhase m a
        + sharpTransportUpper m n n a - sharpTransportLower m n m a)
      ≤ 4050 * Real.pi ^ 3 * (2 * Real.sqrt 2) * Real.exp E / c ^ N := by
    have h1 : 4050 * Real.pi ^ 3 * (sharpCollarPhase m a / sharpCollarPhase n a)
        ≤ 4050 * Real.pi ^ 3 * (2 * Real.sqrt 2) :=
      mul_le_mul_of_nonneg_left hphaseratio hpi.le
    have h2 : (0 : ℝ) ≤ Real.exp (2 * sharpCollarPhase n a - 2 * sharpCollarPhase m a
        + sharpTransportUpper m n n a - sharpTransportLower m n m a) := (Real.exp_pos _).le
    have h3 : (0 : ℝ) ≤ 4050 * Real.pi ^ 3 * (2 * Real.sqrt 2) := by positivity
    calc 4050 * Real.pi ^ 3 * (sharpCollarPhase m a / sharpCollarPhase n a)
          * Real.exp (2 * sharpCollarPhase n a - 2 * sharpCollarPhase m a
            + sharpTransportUpper m n n a - sharpTransportLower m n m a)
        ≤ 4050 * Real.pi ^ 3 * (2 * Real.sqrt 2)
            * Real.exp (2 * sharpCollarPhase n a - 2 * sharpCollarPhase m a
              + sharpTransportUpper m n n a - sharpTransportLower m n m a) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ ≤ 4050 * Real.pi ^ 3 * (2 * Real.sqrt 2) * (Real.exp E / c ^ N) :=
          mul_le_mul_of_nonneg_left hexppow h3
      _ = 4050 * Real.pi ^ 3 * (2 * Real.sqrt 2) * Real.exp E / c ^ N := by ring
  exact mul_le_mul_of_nonneg_right hstep hRm

end RHTower

end

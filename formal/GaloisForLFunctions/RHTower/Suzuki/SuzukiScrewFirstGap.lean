import GaloisForLFunctions.RHTower.Suzuki.SuzukiExplicitScrewZeroSeries
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewFunctionCriterion
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewSmoothTestCriterion
import GaloisForLFunctions.RHTower.DigammaQuarter

/-!
# Suzuki's first prime gap: exact derivative and normalization correction

On `0 < t < log 2` the prime-power hinge sum in Suzuki's explicit screw function is empty.  This
file records the resulting exact derivative of the literal source function `suzukiPsi`.

The calculation also exposes a normalization error in the displayed derivative in the proof of
Suzuki (2022), Theorem 4.1.  Since the linear coefficient in equation (1.1) is

```text
digamma(1/4) - log pi = -(3 log 2 + EulerGamma + pi/2 + log pi),
```

the derivative constant contains `-(log pi)/2`.  That term is absent from the printed formula.
The theorem below is an exact symbolic identity; no zero finder or numerical approximation is
used.
-/

open Filter Set Topology
open GaloisForLFunctions.RHTower

noncomputable section

namespace RHTower

/-- Exact evaluation of the linear coefficient in Suzuki's displayed prime--Lerch formula. -/
theorem screwLinearCoeff_eq :
    screwLinearCoeff =
      -(3 * Real.log 2 + Real.eulerMascheroniConstant + Real.pi / 2 + Real.log Real.pi) := by
  have hreal : (Complex.digamma (1 / 4 : ℂ)).re =
      -(3 * Real.log 2 + Real.eulerMascheroniConstant + Real.pi / 2) := by
    have h := congrArg Complex.re GaloisForLFunctions.RHTower.digamma_quarter
    simpa only [Complex.neg_re, Complex.ofReal_re] using h
  rw [screwLinearCoeff, hreal]
  ring

/-- Before the first prime-power atom, Suzuki's hinge sum is literally empty. -/
theorem screwPrimeSum_eq_zero_of_lt_log_two {t : ℝ} (ht : t < Real.log 2) :
    screwPrimeSum t = 0 := by
  have hexp : Real.exp t < (2 : ℝ) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_lt_exp.mpr ht
  have hfloor : ⌊Real.exp t⌋₊ < 2 := (Nat.floor_lt (Real.exp_pos t).le).mpr hexp
  rw [screwPrimeSum, Finset.Icc_eq_empty_of_lt hfloor]
  simp

/-- Exact first-gap derivative of Suzuki's literal `Psi`.  In particular, substitution of
`screwLinearCoeff_eq` shows the missing `-(log pi)/2` in the printed proof of Theorem 4.1. -/
theorem hasDerivAt_suzukiPsi_firstGap {t : ℝ} (ht : 0 < t) (ht2 : t < Real.log 2) :
    HasDerivAt suzukiPsi
      (2 * Real.exp (t / 2) - 2 * Real.exp (-(t / 2)) + screwLinearCoeff / 2
        - screwLerchTail₁ t) t := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let δ : ℝ := min (t / 2) ((Real.log 2 - t) / 2)
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min (by linarith) (by linarith)
  have hδt : δ ≤ t / 2 := by exact min_le_left _ _
  have haff : ∀ r ∈ Ioo (t - δ) (t + δ), screwPrimeSum r = (0 : ℝ) * r - 0 := by
    intro r hr
    have hδlog : δ ≤ (Real.log 2 - t) / 2 := min_le_right _ _
    have hrlog : r < Real.log 2 := by linarith [hr.2]
    simpa using screwPrimeSum_eq_zero_of_lt_log_two hrlog
  have htmem : t ∈ Ioo (t - δ) (t + δ) := ⟨by linarith, by linarith⟩
  have hscrew := hasDerivAt_screwFn_of_affine screwLinearCoeff screwLerchConst 0 0
    ht hδt haff htmem
  have hneg : HasDerivAt (fun r : ℝ => -screwFn screwLinearCoeff screwLerchConst r)
      (2 * Real.exp (t / 2) - 2 * Real.exp (-(t / 2)) + screwLinearCoeff / 2
        - screwLerchTail₁ t) t := by
    have h := hscrew.fun_neg
    have hcoeff :
        -(-2 * Real.exp (t / 2) + 2 * Real.exp (-(t / 2)) + 0
            - screwLinearCoeff / 2 + screwLerchTail₁ t) =
          2 * Real.exp (t / 2) - 2 * Real.exp (-(t / 2)) + screwLinearCoeff / 2
            - screwLerchTail₁ t := by ring
    rw [hcoeff] at h
    simpa only [Pi.neg_apply] using h
  have heq : suzukiPsi =ᶠ[𝓝 t]
      (fun r : ℝ => -screwFn screwLinearCoeff screwLerchConst r) :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) fun r hr => by
      have hrpos : 0 < r := hr
      rw [suzukiPsi, abs_of_pos hrpos]
  exact hneg.congr_of_eventuallyEq heq

/-- The exact corrected first-gap derivative with every archimedean constant expanded. -/
theorem hasDerivAt_suzukiPsi_firstGap_expanded {t : ℝ} (ht : 0 < t)
    (ht2 : t < Real.log 2) :
    HasDerivAt suzukiPsi
      (2 * Real.exp (t / 2) - 2 * Real.exp (-(t / 2))
        - (3 * Real.log 2 + Real.eulerMascheroniConstant + Real.pi / 2
            + Real.log Real.pi) / 2
        - screwLerchTail₁ t) t := by
  convert hasDerivAt_suzukiPsi_firstGap ht ht2 using 1
  rw [screwLinearCoeff_eq]
  ring

/-! ## A symbolic local-positivity certificate -/

/-- A small rational upper bound for Euler's constant.  This is Euler's decreasing harmonic
sequence at `25`, together with the standard rigorous lower bound for `log 5`. -/
theorem eulerMascheroniConstant_lt_three_fifths :
    Real.eulerMascheroniConstant < (3 : ℝ) / 5 := by
  refine (Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 25).trans ?_
  rw [Real.eulerMascheroniSeq']
  norm_num only [if_false, Nat.reduceEqDiff, Nat.cast_ofNat]
  rw [show (25 : ℝ) = 5 ^ (2 : ℕ) by norm_num, Real.log_pow]
  norm_num [harmonic] at *
  nlinarith [Real.log_five_gt_d9]

/-- A rational upper bound for `log pi`, proved from a sixth-order exponential minorant and the
rigorous mathlib upper bound `pi < 3.1416`. -/
theorem log_pi_lt_twoHundredTwentyNine_over_twoHundred :
    Real.log Real.pi < (229 : ℝ) / 200 := by
  rw [Real.log_lt_iff_lt_exp Real.pi_pos]
  refine Real.pi_lt_d4.trans_le ?_
  refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 229 / 200) 7)
  norm_num [Finset.sum_range_succ]

/-- The exact linear term in the first-gap derivative is larger than `-2.7`. -/
theorem neg_twentySeven_tenths_lt_screwLinearCoeff_half :
    -(27 : ℝ) / 10 < screwLinearCoeff / 2 := by
  rw [screwLinearCoeff_eq]
  have hlog2 : Real.log 2 < (347 : ℝ) / 500 := by
    nlinarith [Real.log_two_lt_d9]
  have hgamma := eulerMascheroniConstant_lt_three_fifths
  have hpi : Real.pi / 2 < (1571 : ℝ) / 1000 := by
    nlinarith [Real.pi_lt_d4]
  have hlogpi := log_pi_lt_twoHundredTwentyNine_over_twoHundred
  nlinarith

/-- The first seven reciprocal Lerch exponents, evaluated exactly. -/
theorem sum_range_seven_one_div_lerchExp :
    ∑ k ∈ Finset.range 7, (1 : ℝ) / lerchExp k = 1068226 / 348075 := by
  norm_num [lerchExp, Finset.sum_range_succ]

/-- Negating the differentiated Lerch tail produces its positive term series. -/
theorem neg_screwLerchTail₁_eq_tsum (t : ℝ) :
    -screwLerchTail₁ t = ∑' k : ℕ, Real.exp (-(lerchExp k * t)) / lerchExp k := by
  rw [screwLerchTail₁, ← tsum_neg]
  apply tsum_congr
  intro k
  ring

/-- Seven positive Lerch terms give a quantitative lower bound for the singular first derivative.
The estimate is purely analytic: `exp (-x) ≥ 1-x`. -/
theorem seven_term_le_neg_screwLerchTail₁ {t : ℝ} (ht : 0 < t) :
    1068226 / 348075 - 7 * t ≤ -screwLerchTail₁ t := by
  have hterm : ∀ k : ℕ, (1 : ℝ) / lerchExp k - t ≤
      Real.exp (-(lerchExp k * t)) / lerchExp k := by
    intro k
    have hbase := Real.one_sub_le_exp_neg (lerchExp k * t)
    calc
      (1 : ℝ) / lerchExp k - t = (1 - lerchExp k * t) / lerchExp k := by
        field_simp [lerchExp_ne_zero]
      _ ≤ Real.exp (-(lerchExp k * t)) / lerchExp k :=
        div_le_div_of_nonneg_right hbase (lerchExp_pos k).le
  have hsum :
      (∑ k ∈ Finset.range 7, ((1 : ℝ) / lerchExp k - t)) ≤
        ∑ k ∈ Finset.range 7, Real.exp (-(lerchExp k * t)) / lerchExp k := by
    exact Finset.sum_le_sum fun k _ => hterm k
  have hsummable : Summable (fun k : ℕ =>
      Real.exp (-(lerchExp k * t)) / lerchExp k) := by
    simpa only [summable_neg_iff] using (summable_screwLerchTerm₁ ht)
  have hfinite :
      (∑ k ∈ Finset.range 7, Real.exp (-(lerchExp k * t)) / lerchExp k) ≤
        ∑' k : ℕ, Real.exp (-(lerchExp k * t)) / lerchExp k :=
    hsummable.sum_le_tsum (Finset.range 7) fun k _ =>
      div_nonneg (Real.exp_nonneg _) (lerchExp_pos k).le
  rw [← neg_screwLerchTail₁_eq_tsum] at hfinite
  calc
    1068226 / 348075 - 7 * t =
        ∑ k ∈ Finset.range 7, ((1 : ℝ) / lerchExp k - t) := by
          rw [Finset.sum_sub_distrib, sum_range_seven_one_div_lerchExp]
          norm_num
    _ ≤ _ := hsum
    _ ≤ _ := hfinite

/-- Suzuki's derivative is strictly positive throughout the explicit interval `(0, 1/20)`.
This replaces the source's computer root-finding near the singular endpoint. -/
theorem deriv_suzukiPsi_pos_of_lt_one_twentieth {t : ℝ} (ht : 0 < t)
    (ht20 : t < 1 / 20) : 0 < deriv suzukiPsi t := by
  have hlog2 : t < Real.log 2 :=
    ht20.trans (by nlinarith [Real.log_two_gt_d9])
  rw [(hasDerivAt_suzukiPsi_firstGap ht hlog2).deriv]
  have hexp : 0 ≤ 2 * Real.exp (t / 2) - 2 * Real.exp (-(t / 2)) := by
    have := Real.exp_le_exp.mpr (by linarith : -(t / 2) ≤ t / 2)
    linarith
  have hlinear := neg_twentySeven_tenths_lt_screwLinearCoeff_half
  have htail := seven_term_le_neg_screwLerchTail₁ ht
  nlinarith

/-- **Suzuki 2022, Theorem 4.1 (analytic weak form used in the proof of Theorem 1.4).**
The literal source function is positive on the unconditional interval `(0, 1/20)`. -/
theorem suzuki_theorem_four_one_weak :
    ∀ t : ℝ, 0 < t → t < 1 / 20 → 0 < suzukiPsi t := by
  have hmono : StrictMonoOn suzukiPsi (Icc (0 : ℝ) (1 / 20)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) (1 / 20))
      continuous_suzukiPsi.continuousOn ?_
    intro t ht
    rw [interior_Icc] at ht
    exact deriv_suzukiPsi_pos_of_lt_one_twentieth ht.1 ht.2
  intro t ht ht20
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) (1 / 20) := by norm_num
  have htmem : t ∈ Icc (0 : ℝ) (1 / 20) := ⟨ht.le, ht20.le⟩
  simpa only [suzukiPsi_zero] using hmono hzero htmem ht

end RHTower

end

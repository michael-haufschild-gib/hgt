/-
Analytic bridge from the rescaling product to the cumulant polynomial.

`SpurCumulant` packages the formal `e_p(j)` carrier.  This file connects that
carrier back to the actual multiplier `φ_d(j) = ∏_{i<j} (1 - i/d)` by rewriting the
all-orders log estimate from `SpurRescale` in polynomial form and exponentiating it on
the negative half-line.
-/
import GaloisForLFunctions.RHTower.SpurCumulant
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace RHTower

open Polynomial

noncomputable section

/-- On the negative half-line, `exp` is `1`-Lipschitz, in ordered form. -/
theorem exp_lipschitz_on_nonpos_ordered {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 0) :
    |Real.exp a - Real.exp b| ≤ |a - b| := by
  have hdiff_nonpos : a - b ≤ 0 := by linarith
  have h_exp_le_one : Real.exp b ≤ 1 := by
    simpa using (Real.exp_le_exp.mpr hb)
  have h_one_sub : 1 - Real.exp (a - b) ≤ b - a := by
    have h := Real.add_one_le_exp (a - b)
    linarith
  have hsub_nonneg : 0 ≤ Real.exp b - Real.exp a := by
    exact sub_nonneg.mpr (Real.exp_le_exp.mpr hab)
  have habsleft : |Real.exp a - Real.exp b| = Real.exp b - Real.exp a := by
    rw [abs_sub_comm, abs_of_nonneg hsub_nonneg]
  rw [habsleft]
  have hfactor : Real.exp b - Real.exp a = Real.exp b * (1 - Real.exp (a - b)) := by
    calc
      Real.exp b - Real.exp a = Real.exp b - Real.exp (b + (a - b)) := by ring_nf
      _ = Real.exp b - Real.exp b * Real.exp (a - b) := by rw [Real.exp_add]
      _ = Real.exp b * (1 - Real.exp (a - b)) := by ring
  rw [hfactor]
  have hsub_nonneg' : 0 ≤ 1 - Real.exp (a - b) := by
    exact sub_nonneg.mpr (by simpa using (Real.exp_le_exp.mpr hdiff_nonpos))
  have hmul : Real.exp b * (1 - Real.exp (a - b)) ≤ 1 * (b - a) := by
    exact mul_le_mul h_exp_le_one h_one_sub hsub_nonneg' zero_le_one
  have habs : |a - b| = b - a := by
    rw [abs_of_nonpos hdiff_nonpos]
    ring
  linarith

/-- On the negative half-line, `exp` is `1`-Lipschitz. -/
theorem exp_lipschitz_on_nonpos {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    |Real.exp a - Real.exp b| ≤ |a - b| := by
  by_cases hab : a ≤ b
  · exact exp_lipschitz_on_nonpos_ordered hab hb
  · have hba : b ≤ a := le_of_not_ge hab
    have h := exp_lipschitz_on_nonpos_ordered hba ha
    rwa [abs_sub_comm (Real.exp b) (Real.exp a), abs_sub_comm b a] at h

/-- Evaluate the cumulant polynomial at `T = 1/d` in the power-sum denominator form used
by `SpurRescale`. -/
theorem eval_cumulantLogPoly_inv_nat {d : ℕ} (hd : 0 < d) (n j : ℕ) :
    (cumulantLogPoly n j).eval ((d : ℝ)⁻¹) =
      ∑ l ∈ Finset.range n,
        rescalePowerSum (l + 1) j / ((l + 1 : ℝ) * (d : ℝ) ^ (l + 1)) := by
  rw [eval_cumulantLogPoly]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hl0 : (l + 1 : ℝ) ≠ 0 := by positivity
  rw [inv_pow]
  field_simp [hd0, pow_ne_zero _ hd0, hl0]

/-- Power sums over nonnegative integer powers are nonnegative. -/
theorem rescalePowerSum_nonneg (ell j : ℕ) : 0 ≤ rescalePowerSum ell j := by
  rw [rescalePowerSum]
  exact Finset.sum_nonneg (fun i _ => by positivity)

/-- The positive cumulant polynomial is nonnegative at every nonnegative input. -/
theorem cumulantLogPoly_eval_nonneg (n j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (cumulantLogPoly n j).eval t := by
  rw [eval_cumulantLogPoly]
  exact Finset.sum_nonneg (fun l _ => by
    exact mul_nonneg (div_nonneg (rescalePowerSum_nonneg (l + 1) j) (by positivity))
      (pow_nonneg ht (l + 1)))

/-- In the live range `j ≤ d`, the rescaling product is at most `1`. -/
theorem phi_product_le_one_of_le {j d : ℕ} (hd : 0 < d) (hjd : j ≤ d) :
    ∏ i ∈ Finset.range j, (1 - (i : ℝ) / d) ≤ 1 := by
  calc
    ∏ i ∈ Finset.range j, (1 - (i : ℝ) / d) ≤ ∏ _i ∈ Finset.range j, (1 : ℝ) := by
      refine Finset.prod_le_prod (fun i hi => ?_) (fun i hi => ?_)
      · have hi_lt : i < j := Finset.mem_range.mp hi
        have hdp : (0 : ℝ) < d := by exact_mod_cast hd
        have hid : (i : ℝ) ≤ d := by exact_mod_cast le_trans (Nat.le_of_lt hi_lt) hjd
        have hdiv : (i : ℝ) / d ≤ 1 := by rwa [div_le_one hdp]
        linarith
      · have hdiv0 : 0 ≤ (i : ℝ) / d := by positivity
        linarith
    _ = 1 := by simp

/-- The log of the live-range multiplier is nonpositive. -/
theorem log_phi_product_nonpos_of_le {j d : ℕ} (hd : 0 < d) (hjd : j ≤ d) :
    Real.log (∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) ≤ 0 := by
  exact Real.log_nonpos (le_of_lt (phi_product_pos_of_le hd hjd))
    (phi_product_le_one_of_le hd hjd)

/-- R1's log-cumulant bound, rewritten in terms of the formal cumulant polynomial. -/
theorem log_phi_cumulant_poly_abs_bound (n : ℕ) {j d : ℕ} (hd : 0 < d) (hjd : j ≤ d) :
    |Real.log (∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) +
        (cumulantLogPoly n j).eval ((d : ℝ)⁻¹)| ≤
      ∑ i ∈ Finset.range j, (((i : ℝ) / d) ^ (n + 1) / (1 - (i : ℝ) / d)) := by
  rw [eval_cumulantLogPoly_inv_nat hd]
  exact log_phi_cumulant_powerSum_abs_bound n hd hjd

/-- Product-to-cumulant-exponential form of R1.

The product itself is within the logarithmic tail of the exponentiated finite cumulant
polynomial.  This is the bridge that lets the finite `exp(-cumulant)` truncation control
the actual Jensen multiplier. -/
theorem phi_product_exp_neg_cumulant_abs_bound (n : ℕ) {j d : ℕ} (hd : 0 < d)
    (hjd : j ≤ d) :
    |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
        Real.exp (-(cumulantLogPoly n j).eval ((d : ℝ)⁻¹))| ≤
      ∑ i ∈ Finset.range j, (((i : ℝ) / d) ^ (n + 1) / (1 - (i : ℝ) / d)) := by
  have hprod_pos := phi_product_pos_of_le hd hjd
  have hlog_nonpos := log_phi_product_nonpos_of_le hd hjd
  have hc_nonneg : 0 ≤ (cumulantLogPoly n j).eval ((d : ℝ)⁻¹) := by
    exact cumulantLogPoly_eval_nonneg n j (by positivity)
  have hneg_nonpos : -(cumulantLogPoly n j).eval ((d : ℝ)⁻¹) ≤ 0 := by linarith
  calc
    |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
        Real.exp (-(cumulantLogPoly n j).eval ((d : ℝ)⁻¹))|
        = |Real.exp (Real.log (∏ i ∈ Finset.range j, (1 - (i : ℝ) / d))) -
            Real.exp (-(cumulantLogPoly n j).eval ((d : ℝ)⁻¹))| := by
          rw [Real.exp_log hprod_pos]
    _ ≤ |Real.log (∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
            (-(cumulantLogPoly n j).eval ((d : ℝ)⁻¹))| :=
          exp_lipschitz_on_nonpos hlog_nonpos hneg_nonpos
    _ = |Real.log (∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) +
            (cumulantLogPoly n j).eval ((d : ℝ)⁻¹)| := by
          congr 1
          ring
    _ ≤ ∑ i ∈ Finset.range j, (((i : ℝ) / d) ^ (n + 1) / (1 - (i : ℝ) / d)) :=
          log_phi_cumulant_poly_abs_bound n hd hjd

/-- The logarithmic cumulant tail from R1. -/
def logCumulantTail (n j d : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, (((i : ℝ) / d) ^ (n + 1) / (1 - (i : ℝ) / d))

/-- The remaining scalar truncation error after replacing `exp(-x)` by its finite
polynomial truncation. -/
def expNegTruncError (P : ℕ) (x : ℝ) : ℝ :=
  |Real.exp (-x) - (expNegTruncPoly P).eval x|

/-- Product-to-cumulant-exponential bound with the tail packaged as a named term. -/
theorem phi_product_exp_neg_cumulant_abs_bound_tail (n : ℕ) {j d : ℕ} (hd : 0 < d)
    (hjd : j ≤ d) :
    |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
        Real.exp (-(cumulantLogPoly n j).eval ((d : ℝ)⁻¹))| ≤ logCumulantTail n j d := by
  simpa [logCumulantTail] using phi_product_exp_neg_cumulant_abs_bound n hd hjd

/-- Unfold the named exponential truncation error. -/
theorem expNegTruncError_eq (P : ℕ) (x : ℝ) :
    expNegTruncError P x = |Real.exp (-x) - (expNegTruncPoly P).eval x| := rfl

/-- Iterated derivatives of `x ↦ exp(-x)`. -/
theorem iteratedDeriv_exp_neg (k : ℕ) :
    iteratedDeriv k (fun y : ℝ => Real.exp (-y)) = fun y => (-1 : ℝ) ^ k * Real.exp (-y) := by
  have h := iteratedDeriv_exp_const_mul k (-1)
  simpa [neg_mul] using h

/-- Smoothness of `x ↦ exp(-x)`. -/
theorem contDiff_exp_neg {n : WithTop ℕ∞} : ContDiff ℝ n (fun y : ℝ => Real.exp (-y)) := by
  simpa using ((contDiff_id.neg).exp : ContDiff ℝ n (fun y : ℝ => Real.exp (-y)))

/-- The Taylor polynomial of `exp(-x)` is exactly `expNegTruncPoly`. -/
theorem taylorWithinEval_exp_neg_eq_expNegTruncPoly {x : ℝ} (hx : 0 < x) (P : ℕ) :
    taylorWithinEval (fun y : ℝ => Real.exp (-y)) P (Set.uIcc 0 x) 0 x =
      (expNegTruncPoly (P + 1)).eval x := by
  rw [taylor_within_apply, eval_expNegTruncPoly]
  refine Finset.sum_congr rfl (fun k _hk => ?_)
  have hmem0 : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) x := Set.left_mem_uIcc
  have hu : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) x) := by
    simpa [Set.uIcc_of_le hx.le] using (uniqueDiffOn_Icc hx)
  have hwithin : iteratedDerivWithin k (fun y : ℝ => Real.exp (-y)) (Set.uIcc 0 x) 0 =
      iteratedDeriv k (fun y : ℝ => Real.exp (-y)) 0 := by
    exact iteratedDerivWithin_eq_iteratedDeriv hu contDiff_exp_neg.contDiffAt hmem0
  rw [hwithin]
  rw [iteratedDeriv_exp_neg]
  simp only [neg_zero, Real.exp_zero, mul_one, sub_zero, smul_eq_mul]
  ring

/-- Scalar exponential truncation bound used in R1:
`|exp(-x) - Σ_{p<P} (-x)^p/p!| ≤ x^P/P!` for `x ≥ 0`. -/
theorem expNegTruncError_le_pow_div_factorial (P : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    expNegTruncError P x ≤ x ^ P / (P.factorial : ℝ) := by
  rcases P with _ | Q
  · rw [expNegTruncError]
    have hexp_nonneg : 0 ≤ Real.exp (-x) := Real.exp_nonneg _
    have hexp_le_one : Real.exp (-x) ≤ 1 := by
      simpa using (Real.exp_le_exp.mpr (by linarith : -x ≤ 0))
    simpa [expNegTruncPoly, abs_of_nonneg hexp_nonneg] using hexp_le_one
  · by_cases hxzero : x = 0
    · subst x
      rw [expNegTruncError, eval_expNegTruncPoly]
      have hsum : (∑ p ∈ Finset.range (Q + 1),
          ((-1 : ℝ) ^ p) / (p.factorial : ℝ) * (0 : ℝ) ^ p) = 1 := by
        rw [Finset.sum_eq_single 0]
        · norm_num
        · intro p _hp hp0
          rw [zero_pow hp0]
          ring
        · intro hnot
          exact False.elim (hnot (Finset.mem_range.mpr (Nat.succ_pos Q)))
      rw [hsum]
      simp
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
      obtain ⟨x', hx', hrem⟩ :=
        taylor_mean_remainder_lagrange_iteratedDeriv
          (f := fun y : ℝ => Real.exp (-y)) (x := x) (x₀ := 0) (n := Q)
          (ne_of_lt hxpos) (contDiff_exp_neg.contDiffOn)
      rw [taylorWithinEval_exp_neg_eq_expNegTruncPoly hxpos Q] at hrem
      have hx'u : x' ∈ Set.Ioo (0 : ℝ) x := by
        simpa [Set.uIoo_of_le hxpos.le] using hx'
      have hderiv_abs_le : |iteratedDeriv (Q + 1) (fun y : ℝ => Real.exp (-y)) x'| ≤ 1 := by
        rw [iteratedDeriv_exp_neg]
        have h_exp_le_one : Real.exp (-x') ≤ 1 := by
          simpa using (Real.exp_le_exp.mpr (by linarith [hx'u.1] : -x' ≤ 0))
        have h_exp_nonneg : 0 ≤ Real.exp (-x') := Real.exp_nonneg _
        calc
          |(-1 : ℝ) ^ (Q + 1) * Real.exp (-x')|
              = Real.exp (-x') := by
                rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
                  abs_of_nonneg h_exp_nonneg]
          _ ≤ 1 := h_exp_le_one
      have hscale_nonneg : 0 ≤ x ^ (Q + 1) / ((Q + 1).factorial : ℝ) := by positivity
      calc
        expNegTruncError (Q + 1) x
            = |iteratedDeriv (Q + 1) (fun y : ℝ => Real.exp (-y)) x' *
                x ^ (Q + 1) / ((Q + 1).factorial : ℝ)| := by
              rw [expNegTruncError, hrem]
              simp only [sub_zero]
        _ = |iteratedDeriv (Q + 1) (fun y : ℝ => Real.exp (-y)) x'| *
              (x ^ (Q + 1) / ((Q + 1).factorial : ℝ)) := by
              rw [abs_div, abs_mul]
              have hpow_nonneg : 0 ≤ x ^ (Q + 1) := pow_nonneg hx (Q + 1)
              have hfac_nonneg : 0 ≤ (((Q + 1).factorial : ℕ) : ℝ) := by positivity
              rw [abs_of_nonneg hpow_nonneg, abs_of_nonneg hfac_nonneg]
              ring
        _ ≤ 1 * (x ^ (Q + 1) / ((Q + 1).factorial : ℝ)) := by
              exact mul_le_mul_of_nonneg_right hderiv_abs_le hscale_nonneg
        _ = x ^ (Q + 1) / ((Q + 1).factorial : ℝ) := by ring

/-- R1 bridge from the actual product to the finite multiplier polynomial.

The remaining analytic work is now isolated in `expNegTruncError`; all product/log/cumulant
bookkeeping has been discharged. -/
theorem phi_product_multiplierTruncPoly_abs_bound (P n : ℕ) {j d : ℕ} (hd : 0 < d)
    (hjd : j ≤ d) :
    |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
        (multiplierTruncPoly P n j).eval ((d : ℝ)⁻¹)| ≤
      logCumulantTail n j d +
        expNegTruncError P ((cumulantLogPoly n j).eval ((d : ℝ)⁻¹)) := by
  set C : ℝ := (cumulantLogPoly n j).eval ((d : ℝ)⁻¹)
  set φ : ℝ := ∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)
  have hprod := phi_product_exp_neg_cumulant_abs_bound_tail n hd hjd
  have htri : |φ - (multiplierTruncPoly P n j).eval ((d : ℝ)⁻¹)| ≤
      |φ - Real.exp (-C)| +
        |Real.exp (-C) - (multiplierTruncPoly P n j).eval ((d : ℝ)⁻¹)| := by
    calc
      |φ - (multiplierTruncPoly P n j).eval ((d : ℝ)⁻¹)|
          = |(φ - Real.exp (-C)) +
              (Real.exp (-C) - (multiplierTruncPoly P n j).eval ((d : ℝ)⁻¹))| := by
            congr 1
            ring
      _ ≤ |φ - Real.exp (-C)| +
          |Real.exp (-C) - (multiplierTruncPoly P n j).eval ((d : ℝ)⁻¹)| := abs_add_le _ _
  have hprodC : |φ - Real.exp (-C)| ≤ logCumulantTail n j d := by
    simpa [φ, C] using hprod
  have htrunc : |Real.exp (-C) - (multiplierTruncPoly P n j).eval ((d : ℝ)⁻¹)| =
      expNegTruncError P C := by
    rw [expNegTruncError, eval_multiplierTruncPoly]
  nlinarith [htri, hprodC]

/-- Fully explicit R1 bridge from the actual product to the finite multiplier polynomial. -/
theorem phi_product_multiplierTruncPoly_abs_bound_explicit (P n : ℕ) {j d : ℕ}
    (hd : 0 < d) (hjd : j ≤ d) :
    |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
        (multiplierTruncPoly P n j).eval ((d : ℝ)⁻¹)| ≤
      logCumulantTail n j d +
        ((cumulantLogPoly n j).eval ((d : ℝ)⁻¹)) ^ P / (P.factorial : ℝ) := by
  have hbase := phi_product_multiplierTruncPoly_abs_bound P n hd hjd
  have hc_nonneg : 0 ≤ (cumulantLogPoly n j).eval ((d : ℝ)⁻¹) := by
    exact cumulantLogPoly_eval_nonneg n j (by positivity)
  have htrunc := expNegTruncError_le_pow_div_factorial P hc_nonneg
  linarith

/-- Coarse live-range bound for the finite cumulant evaluated at `T = 1/d`.

This is deliberately lossy: it packages all lower cumulants under the single scale `j^(2 : ℕ)/d`,
which is the scale needed by the final R1 polynomial envelope. -/
theorem cumulantLogPoly_eval_inv_le_linear (n : ℕ) {j d : ℕ} (hd : 0 < d) (hjd : j ≤ d) :
    (cumulantLogPoly n j).eval ((d : ℝ)⁻¹) ≤ (n : ℝ) * ((j : ℝ) ^ (2 : ℕ) / d) := by
  rw [eval_cumulantLogPoly_inv_nat hd]
  calc
    (∑ l ∈ Finset.range n,
        rescalePowerSum (l + 1) j / ((l + 1 : ℝ) * (d : ℝ) ^ (l + 1)))
        ≤ ∑ _l ∈ Finset.range n, ((j : ℝ) ^ (2 : ℕ) / d) := by
          apply Finset.sum_le_sum
          intro l _hl
          have hpow_sum := sum_range_pow_cast_le_pow_succ (l + 1) j
          have hdR : (0 : ℝ) < d := by exact_mod_cast hd
          have hd0 : (d : ℝ) ≠ 0 := ne_of_gt hdR
          have hdl0 : (d : ℝ) ^ l ≠ 0 := pow_ne_zero _ hd0
          have hdl1pos : 0 < (d : ℝ) ^ (l + 1) := pow_pos hdR _
          have hdenpos : 0 < (l + 1 : ℝ) * (d : ℝ) ^ (l + 1) := by positivity
          have hden_ge : (d : ℝ) ^ (l + 1) ≤ (l + 1 : ℝ) * (d : ℝ) ^ (l + 1) := by
            have hl1 : (1 : ℝ) ≤ (l + 1 : ℝ) := by exact_mod_cast Nat.succ_pos l
            nlinarith [hdl1pos]
          have hterm1 :
              rescalePowerSum (l + 1) j / ((l + 1 : ℝ) * (d : ℝ) ^ (l + 1)) ≤
                (j : ℝ) ^ (l + 2) / ((l + 1 : ℝ) * (d : ℝ) ^ (l + 1)) := by
            exact div_le_div_of_nonneg_right hpow_sum (le_of_lt hdenpos)
          have hterm2 :
              (j : ℝ) ^ (l + 2) / ((l + 1 : ℝ) * (d : ℝ) ^ (l + 1)) ≤
                (j : ℝ) ^ (l + 2) / ((d : ℝ) ^ (l + 1)) := by
            exact div_le_div_of_nonneg_left (by positivity) hdl1pos hden_ge
          have hjdR : (j : ℝ) ≤ d := by exact_mod_cast hjd
          have hpow_le : (j : ℝ) ^ l ≤ (d : ℝ) ^ l :=
            pow_le_pow_left₀ (by positivity) hjdR l
          have hratio_le : (j : ℝ) ^ l / (d : ℝ) ^ l ≤ 1 := by
            rw [div_le_one (by positivity : (0 : ℝ) < (d : ℝ) ^ l)]
            exact hpow_le
          have hterm3 : (j : ℝ) ^ (l + 2) / ((d : ℝ) ^ (l + 1)) ≤
              (j : ℝ) ^ (2 : ℕ) / d := by
            calc
              (j : ℝ) ^ (l + 2) / ((d : ℝ) ^ (l + 1))
                  = (j : ℝ) ^ (2 : ℕ) / d * ((j : ℝ) ^ l / (d : ℝ) ^ l) := by
                    field_simp [hd0, hdl0]
                    ring
              _ ≤ (j : ℝ) ^ (2 : ℕ) / d * 1 := by
                    exact mul_le_mul_of_nonneg_left hratio_le (by positivity)
              _ = (j : ℝ) ^ (2 : ℕ) / d := by ring
          exact le_trans hterm1 (le_trans hterm2 hterm3)
    _ = (n : ℝ) * ((j : ℝ) ^ (2 : ℕ) / d) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Half-range version of the logarithmic cumulant tail bound.

When `2*j ≤ d`, every factor lies in the radius where the geometric tail denominator is
absorbed by `2`. -/
theorem logCumulantTail_half_power (n : ℕ) {j d : ℕ} (hd : 0 < d) (hhalf : 2 * j ≤ d) :
    logCumulantTail n j d ≤ 2 * (j : ℝ) ^ (n + 2) / (d : ℝ) ^ (n + 1) := by
  rw [logCumulantTail]
  have htail :
      (∑ i ∈ Finset.range j, (((i : ℝ) / d) ^ (n + 1) / (1 - (i : ℝ) / d))) ≤
        2 * ∑ i ∈ Finset.range j, ((i : ℝ) / d) ^ (n + 1) := by
    calc
      (∑ i ∈ Finset.range j, (((i : ℝ) / d) ^ (n + 1) / (1 - (i : ℝ) / d)))
          ≤ ∑ i ∈ Finset.range j, (2 * ((i : ℝ) / d) ^ (n + 1)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi_lt : i < j := Finset.mem_range.mp hi
        have hdp : (0 : ℝ) < d := by exact_mod_cast hd
        have hu0 : 0 ≤ (i : ℝ) / d := by positivity
        have hnorm : (i : ℝ) / d ≤ (1 : ℝ) / 2 := by
          rw [div_le_iff₀ hdp]
          have hi2 : 2 * i ≤ d := by omega
          have hi2r : (2 : ℝ) * i ≤ d := by exact_mod_cast hi2
          nlinarith
        exact log_tail_pow_div_one_sub_le_two_pow hu0 hnorm (n + 1)
      _ = 2 * ∑ i ∈ Finset.range j, ((i : ℝ) / d) ^ (n + 1) := by
        rw [Finset.mul_sum]
  have hsum_div : (∑ i ∈ Finset.range j, ((i : ℝ) / d) ^ (n + 1)) =
      (∑ i ∈ Finset.range j, (i : ℝ) ^ (n + 1)) / (d : ℝ) ^ (n + 1) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [div_pow]
  have hpow_sum := sum_range_pow_cast_le_pow_succ (n + 1) j
  calc
    (∑ i ∈ Finset.range j, (((i : ℝ) / d) ^ (n + 1) / (1 - (i : ℝ) / d)))
        ≤ 2 * ∑ i ∈ Finset.range j, ((i : ℝ) / d) ^ (n + 1) := htail
    _ = 2 * ((∑ i ∈ Finset.range j, (i : ℝ) ^ (n + 1)) / (d : ℝ) ^ (n + 1)) := by
      rw [hsum_div]
    _ ≤ 2 * ((j : ℝ) ^ (n + 2) / (d : ℝ) ^ (n + 1)) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hpow_sum (by positivity)) (by norm_num)
    _ = 2 * (j : ℝ) ^ (n + 2) / (d : ℝ) ^ (n + 1) := by ring

/-- Half-range coarse envelope for the R1 product-to-polynomial approximation.

This combines the half-range logarithmic tail and the scalar Taylor remainder into one
reusable estimate. -/
theorem phi_product_multiplierTruncPoly_abs_bound_half_envelope (P n : ℕ) {j d : ℕ}
    (hd : 0 < d) (hhalf : 2 * j ≤ d) :
    |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
        (multiplierTruncPoly P n j).eval ((d : ℝ)⁻¹)| ≤
      2 * (j : ℝ) ^ (n + 2) / (d : ℝ) ^ (n + 1) +
        ((n : ℝ) * ((j : ℝ) ^ (2 : ℕ) / d)) ^ P / (P.factorial : ℝ) := by
  have hjd : j ≤ d := by omega
  have hbase := phi_product_multiplierTruncPoly_abs_bound_explicit P n hd hjd
  have htail := logCumulantTail_half_power n hd hhalf
  have hc_nonneg : 0 ≤ (cumulantLogPoly n j).eval ((d : ℝ)⁻¹) := by
    exact cumulantLogPoly_eval_nonneg n j (by positivity)
  have hc_le := cumulantLogPoly_eval_inv_le_linear n hd hjd
  have hpow : ((cumulantLogPoly n j).eval ((d : ℝ)⁻¹)) ^ P ≤
      ((n : ℝ) * ((j : ℝ) ^ (2 : ℕ) / d)) ^ P := by
    exact pow_le_pow_left₀ hc_nonneg hc_le P
  have hfac : ((cumulantLogPoly n j).eval ((d : ℝ)⁻¹)) ^ P / (P.factorial : ℝ) ≤
      ((n : ℝ) * ((j : ℝ) ^ (2 : ℕ) / d)) ^ P / (P.factorial : ℝ) := by
    exact div_le_div_of_nonneg_right hpow (by positivity)
  linarith

end

end RHTower

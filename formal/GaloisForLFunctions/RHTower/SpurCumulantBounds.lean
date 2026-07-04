/-
Analytic bridge from the rescaling product to the cumulant polynomial.

`SpurCumulant` packages the formal `e_p(j)` carrier.  This file connects that
carrier back to the actual multiplier `φ_d(j) = ∏_{i<j} (1 - i/d)` by rewriting the
all-orders log estimate from `SpurRescale` in polynomial form and exponentiating it on
the negative half-line.
-/
import GaloisForLFunctions.RHTower.SpurCumulant

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

end

end RHTower

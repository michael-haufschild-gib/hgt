import GaloisForLFunctions.HTGeometry.MaximumTermCentralIndex
import GaloisForLFunctions.HTGeometry.DiscreteJensenExp
import GaloisForLFunctions.HTGeometry.MaximumTermLogarithmicDerivative

/-!
# The mean index against the central index

The central index is the *mode* of the weighting `n ↦ ‖a n‖ rⁿ`; the mean of the same weighting is
`Λ(r) = r S'(r) / S(r)`.  Jensen's inequality gives `Λ` the lower growth law that `ν` satisfies for
the maximum term, so `Λ` is squeezed between adjacent difference quotients of `log S` exactly as `ν`
is squeezed between those of `log μ`.  Since the two functions differ by at most a factor linear in
the central index, the two squeezes overlap and the mean and the mode are separated only by the width
of the central-index window plus two logarithmic corrections.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

variable {a : ℕ → ℂ} {r s : ℝ}

/-! ## The mean index

The mean index is the average of `n` against the weights `||a_n|| r^n`; the central index is the mode
of the same weighting.  Jensen's inequality gives the mean index the same lower growth law that the
modal index satisfies for the maximum term. -/

/-- The mean index `Lambda(r) = r S'(r) / S(r)`. -/
noncomputable def meanIndex (a : ℕ → ℂ) (r : ℝ) : ℝ :=
  (∑' n : ℕ, (n : ℝ) * (‖a n‖ * r ^ n)) / coeffSum a r

/-- **Growth law for the mean index.**  By Jensen, the majorant grows at least like `(s/r)` to the
mean index. -/
theorem meanIndex_mul_log_le_log_coeffSum_sub
    (ha : EntireCoeffs a) (hr : 0 < r) (hs : 0 < s) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    meanIndex a r * Real.log (s / r)
      ≤ Real.log (coeffSum a s) - Real.log (coeffSum a r) := by
  obtain ⟨-, -, hμr⟩ := exists_maxTerm_eq ha hr hn₀
  obtain ⟨-, -, hμs⟩ := exists_maxTerm_eq ha hs hn₀
  have hSr : 0 < coeffSum a r := lt_of_lt_of_le hμr (maxTerm_le_coeffSum ha hr hn₀)
  have hSs : 0 < coeffSum a s := lt_of_lt_of_le hμs (maxTerm_le_coeffSum ha hs hn₀)
  have hq : (0 : ℝ) < s / r := div_pos hs hr
  set L : ℝ := Real.log (s / r) with hL
  set p : ℕ → ℝ := fun n => (‖a n‖ * r ^ n) / coeffSum a r with hp
  set x : ℕ → ℝ := fun n => (n : ℝ) * L with hx
  have hpnn : ∀ n, 0 ≤ p n := fun n => div_nonneg (term_nonneg a hr n) hSr.le
  have hpsum : Summable p := (summable_term ha hr).div_const _
  have hp1 : ∑' n : ℕ, p n = 1 := by
    rw [hp, tsum_div_const, ← coeffSum]
    exact div_self (ne_of_gt hSr)
  have hidx : Summable fun n : ℕ => (n : ℝ) * (‖a n‖ * r ^ n) := by
    refine (summable_term (entireCoeffs_mul_index ha) hr).congr fun n => ?_
    rw [norm_mul, Complex.norm_natCast, mul_assoc]
  have hpx : Summable fun n : ℕ => p n * x n := by
    refine (hidx.div_const (coeffSum a r) |>.mul_right L).congr fun n => ?_
    show (n : ℝ) * (‖a n‖ * r ^ n) / coeffSum a r * L = p n * x n
    rw [hp, hx]
    field_simp
  have hexpx : ∀ n : ℕ, Real.exp (x n) = (s / r) ^ n := by
    intro n
    show Real.exp ((n : ℝ) * L) = (s / r) ^ n
    rw [Real.exp_nat_mul, hL, Real.exp_log hq]
  have hpe0 : ∀ n : ℕ, p n * Real.exp (x n) = (‖a n‖ * s ^ n) / coeffSum a r := by
    intro n
    rw [hexpx n]
    show ‖a n‖ * r ^ n / coeffSum a r * (s / r) ^ n = ‖a n‖ * s ^ n / coeffSum a r
    rw [div_pow]
    field_simp
  have hpe : Summable fun n : ℕ => p n * Real.exp (x n) := by
    refine ((summable_term ha hs).div_const (coeffSum a r)).congr fun n => (hpe0 n).symm
  have hjensen := exp_tsum_mul_le_tsum_mul_exp p x hpnn hpsum hp1 hpx hpe
  have hmean : ∑' n : ℕ, p n * x n = meanIndex a r * L := by
    rw [meanIndex, div_mul_eq_mul_div, ← tsum_mul_right, ← tsum_div_const]
    refine tsum_congr fun n => ?_
    show p n * x n = (n : ℝ) * (‖a n‖ * r ^ n) * L / coeffSum a r
    rw [hp, hx]
    field_simp
  have hratio : ∑' n : ℕ, p n * Real.exp (x n) = coeffSum a s / coeffSum a r := by
    rw [tsum_congr hpe0, tsum_div_const, ← coeffSum]
  rw [hmean, hratio] at hjensen
  have hlog := Real.log_le_log (Real.exp_pos _) hjensen
  rw [Real.log_exp, Real.log_div (ne_of_gt hSs) (ne_of_gt hSr)] at hlog
  exact hlog


/-- **The mean index is below the forward difference quotient of `log S`.** -/
theorem meanIndex_le_slope (ha : EntireCoeffs a) (hr : 0 < r) (hrs : r < s)
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    meanIndex a r
      ≤ (Real.log (coeffSum a s) - Real.log (coeffSum a r)) / Real.log (s / r) := by
  have hs : 0 < s := lt_trans hr hrs
  have hL : 0 < Real.log (s / r) := Real.log_pos (by rw [lt_div_iff₀ hr]; linarith)
  rw [le_div_iff₀ hL]
  exact meanIndex_mul_log_le_log_coeffSum_sub ha hr hs hn₀

/-- **The mean index is above the backward difference quotient of `log S`.** -/
theorem slope_le_meanIndex (ha : EntireCoeffs a) (ht : 0 < t) (htr : t < r)
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    (Real.log (coeffSum a r) - Real.log (coeffSum a t)) / Real.log (r / t)
      ≤ meanIndex a r := by
  have hr : 0 < r := lt_trans ht htr
  have hL : 0 < Real.log (r / t) := Real.log_pos (by rw [lt_div_iff₀ ht]; linarith)
  have hneg : Real.log (t / r) = -Real.log (r / t) := by
    rw [← Real.log_inv]
    congr 1
    rw [inv_div]
  have h := meanIndex_mul_log_le_log_coeffSum_sub ha hr ht hn₀
  rw [hneg] at h
  rw [div_le_iff₀ hL]
  linarith


/-- **The mean index is not far above the central index.**  The only cost is the logarithm of the
majorant-to-maximum-term ratio, divided by the logarithmic spacing of the radii. -/
theorem meanIndex_le_centralIndex_add
    (ha : EntireCoeffs a) (hr : 0 < r) (hrs : r < s) {s' : ℝ} (hss' : s < s')
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    meanIndex a r
      ≤ (centralIndex a s : ℝ)
        + Real.log (((centralIndex a s' : ℝ) + 1) + (s / s') / (1 - s / s'))
            / Real.log (s / r) := by
  have hs : 0 < s := lt_trans hr hrs
  have hL : 0 < Real.log (s / r) := Real.log_pos (by rw [lt_div_iff₀ hr]; linarith)
  obtain ⟨-, -, hμr⟩ := exists_maxTerm_eq ha hr hn₀
  obtain ⟨-, -, hμs⟩ := exists_maxTerm_eq ha hs hn₀
  have hSr : 0 < coeffSum a r := lt_of_lt_of_le hμr (maxTerm_le_coeffSum ha hr hn₀)
  have hSs : 0 < coeffSum a s := lt_of_lt_of_le hμs (maxTerm_le_coeffSum ha hs hn₀)
  set B : ℝ := ((centralIndex a s' : ℝ) + 1) + (s / s') / (1 - s / s') with hB
  have hs'pos : 0 < s' := lt_trans hs hss'
  have hq1 : s / s' < 1 := by rw [div_lt_one hs'pos]; exact hss'
  have hq0 : 0 < s / s' := div_pos hs hs'pos
  have hBpos : 0 < B := by
    rw [hB]
    have : 0 < (s / s') / (1 - s / s') := div_pos hq0 (by linarith)
    have : (0 : ℝ) ≤ (centralIndex a s' : ℝ) := Nat.cast_nonneg _
    positivity
  have hSbound := coeffSum_le_maxTerm_mul_centralIndex ha hs hss' hn₀
  rw [← hB] at hSbound
  have hlogS : Real.log (coeffSum a s) ≤ Real.log (maxTerm a s) + Real.log B := by
    have h := Real.log_le_log hSs hSbound
    rwa [Real.log_mul (ne_of_gt hμs) (ne_of_gt hBpos)] at h
  have hlogr : Real.log (maxTerm a r) ≤ Real.log (coeffSum a r) :=
    Real.log_le_log hμr (maxTerm_le_coeffSum ha hr hn₀)
  have hgrow := log_maxTerm_sub_le_centralIndex_mul_log ha hr hrs.le hn₀
  have hslope := meanIndex_le_slope ha hr hrs hn₀
  refine le_trans hslope ?_
  rw [div_le_iff₀ hL]
  have hexpand : ((centralIndex a s : ℝ) + Real.log B / Real.log (s / r)) * Real.log (s / r)
      = (centralIndex a s : ℝ) * Real.log (s / r) + Real.log B := by
    field_simp
  rw [hexpand]
  linarith

/-- **The mean index is not far below the central index.** -/
theorem centralIndex_sub_le_meanIndex
    (ha : EntireCoeffs a) (ht : 0 < t) (htr : t < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    (centralIndex a t : ℝ)
        - Real.log (((centralIndex a r : ℝ) + 1) + (t / r) / (1 - t / r))
            / Real.log (r / t)
      ≤ meanIndex a r := by
  have hr : 0 < r := lt_trans ht htr
  have hL : 0 < Real.log (r / t) := Real.log_pos (by rw [lt_div_iff₀ ht]; linarith)
  obtain ⟨-, -, hμr⟩ := exists_maxTerm_eq ha hr hn₀
  obtain ⟨-, -, hμt⟩ := exists_maxTerm_eq ha ht hn₀
  have hSr : 0 < coeffSum a r := lt_of_lt_of_le hμr (maxTerm_le_coeffSum ha hr hn₀)
  have hSt : 0 < coeffSum a t := lt_of_lt_of_le hμt (maxTerm_le_coeffSum ha ht hn₀)
  set B : ℝ := ((centralIndex a r : ℝ) + 1) + (t / r) / (1 - t / r) with hB
  have hq1 : t / r < 1 := by rw [div_lt_one hr]; exact htr
  have hq0 : 0 < t / r := div_pos ht hr
  have hBpos : 0 < B := by
    rw [hB]
    have : 0 < (t / r) / (1 - t / r) := div_pos hq0 (by linarith)
    have : (0 : ℝ) ≤ (centralIndex a r : ℝ) := Nat.cast_nonneg _
    positivity
  have hSbound := coeffSum_le_maxTerm_mul_centralIndex ha ht htr hn₀
  rw [← hB] at hSbound
  have hlogS : Real.log (coeffSum a t) ≤ Real.log (maxTerm a t) + Real.log B := by
    have h := Real.log_le_log hSt hSbound
    rwa [Real.log_mul (ne_of_gt hμt) (ne_of_gt hBpos)] at h
  have hlogr : Real.log (maxTerm a r) ≤ Real.log (coeffSum a r) :=
    Real.log_le_log hμr (maxTerm_le_coeffSum ha hr hn₀)
  have hgrow := centralIndex_mul_log_le_log_maxTerm_sub ha ht htr.le hn₀
  have hslope := slope_le_meanIndex ha ht htr hn₀
  refine le_trans ?_ hslope
  rw [le_div_iff₀ hL]
  have hexpand : ((centralIndex a t : ℝ) - Real.log B / Real.log (r / t)) * Real.log (r / t)
      = (centralIndex a t : ℝ) * Real.log (r / t) - Real.log B := by
    field_simp
  rw [hexpand]
  linarith


/-- **Mean and mode are close.**  The mean index differs from the central index by at most the width
of the central-index window plus two logarithmic corrections. -/
theorem abs_meanIndex_sub_centralIndex_le
    (ha : EntireCoeffs a) (ht : 0 < t) (htr : t < r) (hrs : r < s) {s' : ℝ} (hss' : s < s')
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    |meanIndex a r - (centralIndex a r : ℝ)|
      ≤ ((centralIndex a s : ℝ) - (centralIndex a t : ℝ))
        + Real.log (((centralIndex a s' : ℝ) + 1) + (s / s') / (1 - s / s'))
            / Real.log (s / r)
        + Real.log (((centralIndex a r : ℝ) + 1) + (t / r) / (1 - t / r))
            / Real.log (r / t) := by
  have hr : 0 < r := lt_trans ht htr
  have hs : 0 < s := lt_trans hr hrs
  have hs' : 0 < s' := lt_trans hs hss'
  have hLs : 0 < Real.log (s / r) := Real.log_pos (by rw [lt_div_iff₀ hr]; linarith)
  have hLt : 0 < Real.log (r / t) := Real.log_pos (by rw [lt_div_iff₀ ht]; linarith)
  have hA : 0 ≤ Real.log (((centralIndex a s' : ℝ) + 1) + (s / s') / (1 - s / s'))
      / Real.log (s / r) := by
    refine div_nonneg (Real.log_nonneg ?_) hLs.le
    have h1 : (0 : ℝ) ≤ (centralIndex a s' : ℝ) := Nat.cast_nonneg _
    have h2 : 0 < (s / s') / (1 - s / s') :=
      div_pos (div_pos hs hs') (by
        have : s / s' < 1 := by rw [div_lt_one hs']; exact hss'
        linarith)
    linarith
  have hB : 0 ≤ Real.log (((centralIndex a r : ℝ) + 1) + (t / r) / (1 - t / r))
      / Real.log (r / t) := by
    refine div_nonneg (Real.log_nonneg ?_) hLt.le
    have h1 : (0 : ℝ) ≤ (centralIndex a r : ℝ) := Nat.cast_nonneg _
    have h2 : 0 < (t / r) / (1 - t / r) :=
      div_pos (div_pos ht hr) (by
        have : t / r < 1 := by rw [div_lt_one hr]; exact htr
        linarith)
    linarith
  have hνtr : (centralIndex a t : ℝ) ≤ (centralIndex a r : ℝ) := by
    exact_mod_cast centralIndex_mono ha ht htr.le hn₀
  have hνrs : (centralIndex a r : ℝ) ≤ (centralIndex a s : ℝ) := by
    exact_mod_cast centralIndex_mono ha hr hrs.le hn₀
  have hup := meanIndex_le_centralIndex_add ha hr hrs hss' hn₀
  have hlow := centralIndex_sub_le_meanIndex ha ht htr hn₀
  exact abs_le.mpr ⟨by linarith, by linarith⟩


/-- **The first moment of the normalised profile.**  Weighting the index deviation by the moduli of
the normalised coefficients gives the mean-minus-mode gap, scaled by the majorant-to-maximum-term
ratio. -/
theorem tsum_index_sub_centralIndex_mul_normalised_norm
    (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    ∑' n : ℕ, ((n : ℝ) - (centralIndex a r : ℝ)) * ((‖a n‖ * r ^ n) / maxTerm a r)
      = (coeffSum a r / maxTerm a r) * (meanIndex a r - (centralIndex a r : ℝ)) := by
  obtain ⟨-, -, hμ⟩ := exists_maxTerm_eq ha hr hn₀
  have hS : 0 < coeffSum a r := lt_of_lt_of_le hμ (maxTerm_le_coeffSum ha hr hn₀)
  have hsplit : ∀ n : ℕ,
      ((n : ℝ) - (centralIndex a r : ℝ)) * ((‖a n‖ * r ^ n) / maxTerm a r)
        = (((n : ℝ) - (centralIndex a r : ℝ)) * (‖a n‖ * r ^ n)) / maxTerm a r := by
    intro n
    ring
  rw [tsum_congr hsplit, tsum_div_const,
    tsum_index_sub_mul_term ha hr (centralIndex a r), meanIndex]
  field_simp


/-! ## Splitting the weighted projection

The weighted sum of the projections of the normalised coefficients onto the direction of the value
splits into the mean-minus-mode gap and a weighted misalignment.  Both pieces are absolutely
convergent, because the misalignment of a term never exceeds twice its modulus. -/

/-- The weighted deviation series of the moduli converges absolutely. -/
theorem summable_index_deviation_normalised
    (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {z : ℂ} (hz : ‖z‖ = r) (k : ℕ) :
    Summable fun n : ℕ => |(n : ℝ) - (k : ℝ)| * ‖normalisedCoeff a r z n‖ := by
  have hzpos : 0 < ‖z‖ := by rw [hz]; exact hr
  have hbase := summable_index_deviation ha hzpos k
  have hCn : ‖a (centralIndex a r) * z ^ centralIndex a r‖ = maxTerm a r := by
    rw [norm_mul, norm_pow, hz]
    exact term_centralIndex_eq ha hr hn₀
  refine (hbase.div_const (maxTerm a r)).congr fun n => ?_
  rw [normalisedCoeff_def, norm_div, hCn, norm_mul, norm_pow, hz]
  ring

set_option maxHeartbeats 400000 in
/-- **Splitting the weighted projection.**  With `u` any unit, the weighted sum of the projections is
the mean-minus-mode gap minus the weighted misalignment. -/
theorem tsum_index_weighted_re_eq
    (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {z : ℂ} (hz : ‖z‖ = r)
    {u : ℂ} (hu : ‖u‖ = 1) :
    ∑' n : ℕ, ((n : ℝ) - (centralIndex a r : ℝ))
        * ((starRingEnd ℂ) u * normalisedCoeff a r z n).re
      = (coeffSum a r / maxTerm a r) * (meanIndex a r - (centralIndex a r : ℝ))
        - ∑' n : ℕ, ((n : ℝ) - (centralIndex a r : ℝ))
            * (‖normalisedCoeff a r z n‖
              - ((starRingEnd ℂ) u * normalisedCoeff a r z n).re) := by
  set k := centralIndex a r with hk
  set c : ℕ → ℂ := normalisedCoeff a r z with hc
  set w : ℕ → ℝ := fun n => (n : ℝ) - (k : ℝ) with hw
  have habs := summable_index_deviation_normalised ha hr hn₀ hz k
  have hA : Summable fun n : ℕ => w n * ‖c n‖ := by
    refine Summable.of_abs (habs.congr fun n => ?_)
    rw [abs_mul, abs_of_nonneg (norm_nonneg (c n))]
  have hB : Summable fun n : ℕ => w n * (‖c n‖ - ((starRingEnd ℂ) u * c n).re) := by
    refine Summable.of_abs ((habs.mul_left 2).of_nonneg_of_le (fun n => abs_nonneg _)
      (fun n => ?_))
    have hnn : 0 ≤ ‖c n‖ - ((starRingEnd ℂ) u * c n).re := alignment_defect_nonneg (c n) hu
    have hle : ‖c n‖ - ((starRingEnd ℂ) u * c n).re ≤ 2 * ‖c n‖ := by
      have := re_conj_mul_le_norm (-(c n)) hu
      simp only [Complex.neg_re, norm_neg, mul_neg] at this
      linarith
    calc |w n * (‖c n‖ - ((starRingEnd ℂ) u * c n).re)|
        = |w n| * (‖c n‖ - ((starRingEnd ℂ) u * c n).re) := by
          rw [abs_mul, abs_of_nonneg hnn]
      _ ≤ 2 * (|w n| * ‖c n‖) := by nlinarith [abs_nonneg (w n), norm_nonneg (c n)]
  have hmoment : ∑' n : ℕ, w n * ‖c n‖
      = (coeffSum a r / maxTerm a r) * (meanIndex a r - (k : ℝ)) := by
    rw [← tsum_index_sub_centralIndex_mul_normalised_norm ha hr hn₀, ← hk]
    refine tsum_congr fun n => ?_
    rw [hc, normalisedCoeff_def, norm_div, norm_mul, norm_pow, hz, hw]
    have hCn : ‖a (centralIndex a r) * z ^ centralIndex a r‖ = maxTerm a r := by
      rw [norm_mul, norm_pow, hz]
      exact term_centralIndex_eq ha hr hn₀
    rw [hCn]
  rw [← hmoment, ← Summable.tsum_sub hA hB]
  exact tsum_congr fun n => by ring


set_option maxHeartbeats 400000 in
/-- **The deviation reduced to a real weighted projection.**  At a point where the logarithmic
derivative is real -- a maximum of the modulus along the circle -- the deviation from the central
index is the weighted sum of the projections of the normalised coefficients, divided by the norm of
their sum. -/
theorem norm_mul_logDeriv_sub_centralIndex_eq
    (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {z : ℂ} (hz : ‖z‖ = r)
    (hfz : coeffFun a z ≠ 0)
    (hcrit : (z * deriv (coeffFun a) z / coeffFun a z).im = 0)
    {u : ℂ} (hu : ‖u‖ = 1)
    (hWdir : ∑' n : ℕ, normalisedCoeff a r z n
      = ((‖∑' n : ℕ, normalisedCoeff a r z n‖ : ℝ) : ℂ) * u) :
    ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a r : ℂ)‖
      = |∑' n : ℕ, ((n : ℝ) - (centralIndex a r : ℝ))
            * ((starRingEnd ℂ) u * normalisedCoeff a r z n).re|
        / ‖∑' n : ℕ, normalisedCoeff a r z n‖ := by
  set k := centralIndex a r with hk
  set c : ℕ → ℂ := normalisedCoeff a r z with hc
  set W : ℂ := ∑' n : ℕ, c n with hW
  set V : ℂ := ∑' n : ℕ, ((n : ℂ) - (k : ℂ)) * c n with hV
  -- the denominator is nonzero
  have hCne : a k * z ^ k ≠ 0 := central_term_ne_zero ha hr hn₀ hz
  have hfac : coeffFun a z = (a k * z ^ k) * W := coeffFun_eq_central_term_mul_tsum ha hr hn₀ hz
  have hWne : W ≠ 0 := by
    intro h
    rw [h, mul_zero] at hfac
    exact hfz hfac
  have hWpos : 0 < ‖W‖ := norm_pos_iff.mpr hWne
  -- the deviation is the ratio, then conjugated
  have hratio : z * deriv (coeffFun a) z / coeffFun a z - (k : ℂ) = V / W :=
    mul_logDeriv_sub_centralIndex_eq_div ha hr hn₀ hz hfz
  have hconj : V / W = ((starRingEnd ℂ) u * V) / ((‖W‖ : ℝ) : ℂ) := by
    conv_lhs => rw [hWdir]
    exact div_ofReal_mul_unit V hu hWpos
  -- criticality makes it real
  have him : (z * deriv (coeffFun a) z / coeffFun a z - (k : ℂ)).im = 0 := by
    simp [Complex.sub_im, hcrit]
  rw [norm_eq_abs_re_of_im_eq_zero him, hratio, hconj]
  -- the real part of the projection
  have hre : (((starRingEnd ℂ) u * V) / ((‖W‖ : ℝ) : ℂ)).re
      = ((starRingEnd ℂ) u * V).re / ‖W‖ := by
    rw [div_eq_mul_inv, ← Complex.ofReal_inv, mul_comm, Complex.re_ofReal_mul]
    ring
  -- interchange the real part with the sum
  have hsum : Summable fun n : ℕ => (starRingEnd ℂ) u * (((n : ℂ) - (k : ℂ)) * c n) := by
    refine Summable.mul_left _ (Summable.of_norm ?_)
    refine (summable_index_deviation_normalised ha hr hn₀ hz k).congr fun n => ?_
    rw [norm_mul]
    congr 1
    rw [show ((n : ℂ) - (k : ℂ)) = (((n : ℝ) - (k : ℝ) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  have hmul : (starRingEnd ℂ) u * V
      = ∑' n : ℕ, (starRingEnd ℂ) u * (((n : ℂ) - (k : ℂ)) * c n) := by
    rw [hV, tsum_mul_left]
  have hreSum : (∑' n : ℕ, (starRingEnd ℂ) u * (((n : ℂ) - (k : ℂ)) * c n)).re
      = ∑' n : ℕ, ((starRingEnd ℂ) u * (((n : ℂ) - (k : ℂ)) * c n)).re :=
    Complex.reCLM.map_tsum hsum
  have hkey : ((starRingEnd ℂ) u * V).re
      = ∑' n : ℕ, ((n : ℝ) - (k : ℝ)) * ((starRingEnd ℂ) u * c n).re := by
    rw [hmul, hreSum]
    refine tsum_congr fun n => ?_
    rw [show ((n : ℂ) - (k : ℂ)) = (((n : ℝ) - (k : ℝ) : ℝ) : ℂ) by push_cast; ring]
    rw [show (starRingEnd ℂ) u * ((((n : ℝ) - (k : ℝ) : ℝ) : ℂ) * c n)
        = ((((n : ℝ) - (k : ℝ) : ℝ) : ℂ)) * ((starRingEnd ℂ) u * c n) by ring,
      Complex.re_ofReal_mul]
  rw [hre, hkey, abs_div, abs_of_pos hWpos]


/-- The normalised misalignment, summed, is the gap between the majorant and the norm of the
normalised sum. -/
theorem tsum_normalised_defect_eq
    (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {z : ℂ} (hz : ‖z‖ = r)
    {u : ℂ} (hu : ‖u‖ = 1)
    (hWdir : ∑' n : ℕ, normalisedCoeff a r z n
      = ((‖∑' n : ℕ, normalisedCoeff a r z n‖ : ℝ) : ℂ) * u) :
    ∑' n : ℕ, (‖normalisedCoeff a r z n‖
        - ((starRingEnd ℂ) u * normalisedCoeff a r z n).re)
      = coeffSum a r / maxTerm a r - ‖∑' n : ℕ, normalisedCoeff a r z n‖ := by
  set c : ℕ → ℂ := normalisedCoeff a r z with hc
  have hCnorm : ‖a (centralIndex a r) * z ^ centralIndex a r‖ = maxTerm a r := by
    rw [norm_mul, norm_pow, hz]
    exact term_centralIndex_eq ha hr hn₀
  have hcnorm : ∀ n, ‖c n‖ = (‖a n‖ * r ^ n) / maxTerm a r := by
    intro n
    rw [hc, normalisedCoeff_def, norm_div, hCnorm, norm_mul, norm_pow, hz]
  have hnsum : Summable fun n => ‖c n‖ := by
    refine ((summable_term ha hr).div_const (maxTerm a r)).congr fun n => (hcnorm n).symm
  have hcsum : Summable c := Summable.of_norm hnsum
  have htsum : ∑' n : ℕ, ‖c n‖ = coeffSum a r / maxTerm a r := by
    rw [coeffSum, ← tsum_div_const]
    exact tsum_congr hcnorm
  rw [tsum_alignment_defect c hcsum hnsum hu hWdir, htsum]

/-- **The numerator bound.**  The weighted projection is at most the scaled mean-minus-mode gap plus
the weighted misalignment. -/
theorem abs_tsum_index_weighted_re_le
    (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {z : ℂ} (hz : ‖z‖ = r)
    {u : ℂ} (hu : ‖u‖ = 1) {E : ℝ}
    (hE : ∑' n : ℕ, |(n : ℝ) - (centralIndex a r : ℝ)|
        * (‖normalisedCoeff a r z n‖
          - ((starRingEnd ℂ) u * normalisedCoeff a r z n).re) ≤ E) :
    |∑' n : ℕ, ((n : ℝ) - (centralIndex a r : ℝ))
        * ((starRingEnd ℂ) u * normalisedCoeff a r z n).re|
      ≤ (coeffSum a r / maxTerm a r) * |meanIndex a r - (centralIndex a r : ℝ)| + E := by
  set k := centralIndex a r with hk
  set c : ℕ → ℂ := normalisedCoeff a r z with hc
  set d : ℕ → ℝ := fun n => ‖c n‖ - ((starRingEnd ℂ) u * c n).re with hd
  set w : ℕ → ℝ := fun n => (n : ℝ) - (k : ℝ) with hw
  have hdnn : ∀ n, 0 ≤ d n := fun n => alignment_defect_nonneg (c n) hu
  have habs := summable_index_deviation_normalised ha hr hn₀ hz k
  have hdsum : Summable fun n : ℕ => |w n| * d n := by
    refine (habs.mul_left 2).of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (hdnn n))
      (fun n => ?_)
    have h := re_conj_mul_le_norm (-(c n)) hu
    simp only [Complex.neg_re, norm_neg, mul_neg] at h
    have hle : d n ≤ 2 * ‖c n‖ := by
      simp only [hd]
      linarith
    nlinarith [abs_nonneg (w n), norm_nonneg (c n), hdnn n]
  have hswsum : Summable fun n : ℕ => w n * d n :=
    Summable.of_abs (hdsum.congr fun n => by rw [abs_mul, abs_of_nonneg (hdnn n)])
  have hSnn : (0 : ℝ) ≤ coeffSum a r / maxTerm a r := by
    obtain ⟨-, -, hμpos⟩ := exists_maxTerm_eq ha hr hn₀
    have : 0 ≤ coeffSum a r := le_trans hμpos.le (maxTerm_le_coeffSum ha hr hn₀)
    positivity
  have hbound : |∑' n : ℕ, w n * d n| ≤ E := by
    refine le_trans ?_ hE
    have hnormsum : Summable fun n : ℕ => ‖w n * d n‖ :=
      hdsum.congr fun n => by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hdnn n)]
    calc |∑' n : ℕ, w n * d n| ≤ ∑' n : ℕ, ‖w n * d n‖ := by
          simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnormsum
      _ = ∑' n : ℕ, |w n| * d n := by
          refine tsum_congr fun n => ?_
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hdnn n)]
  rw [tsum_index_weighted_re_eq ha hr hn₀ hz hu]
  calc |(coeffSum a r / maxTerm a r) * (meanIndex a r - (k : ℝ)) - ∑' n : ℕ, w n * d n|
      ≤ |(coeffSum a r / maxTerm a r) * (meanIndex a r - (k : ℝ))|
        + |∑' n : ℕ, w n * d n| := abs_sub _ _
    _ ≤ (coeffSum a r / maxTerm a r) * |meanIndex a r - (k : ℝ)| + E := by
        rw [abs_mul, abs_of_nonneg hSnn]
        linarith


set_option maxHeartbeats 400000 in
/-- **The Wiman--Valiron logarithmic-derivative estimate.**  At a point of the circle where the
function is at least the maximum term and the modulus is critical along the circle, the logarithmic
derivative differs from `nu(r)/z` by at most the mean-minus-mode gap inflated by the total
misalignment, plus the weighted misalignment. -/
theorem norm_mul_logDeriv_sub_centralIndex_le_meanIndex
    (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {z : ℂ} (hz : ‖z‖ = r)
    (hfz : maxTerm a r ≤ ‖coeffFun a z‖)
    (hcrit : (z * deriv (coeffFun a) z / coeffFun a z).im = 0)
    {u : ℂ} (hu : ‖u‖ = 1)
    (hWdir : ∑' n : ℕ, normalisedCoeff a r z n
      = ((‖∑' n : ℕ, normalisedCoeff a r z n‖ : ℝ) : ℂ) * u)
    {D E : ℝ}
    (hD : ∑' n : ℕ, (‖normalisedCoeff a r z n‖
        - ((starRingEnd ℂ) u * normalisedCoeff a r z n).re) ≤ D)
    (hE : ∑' n : ℕ, |(n : ℝ) - (centralIndex a r : ℝ)|
        * (‖normalisedCoeff a r z n‖
          - ((starRingEnd ℂ) u * normalisedCoeff a r z n).re) ≤ E) :
    ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a r : ℂ)‖
      ≤ (1 + D) * |meanIndex a r - (centralIndex a r : ℝ)| + E := by
  obtain ⟨-, -, hμpos⟩ := exists_maxTerm_eq ha hr hn₀
  have hfpos : 0 < ‖coeffFun a z‖ := lt_of_lt_of_le hμpos hfz
  have hfne : coeffFun a z ≠ 0 := norm_pos_iff.mp hfpos
  have hCnorm : ‖a (centralIndex a r) * z ^ centralIndex a r‖ = maxTerm a r := by
    rw [norm_mul, norm_pow, hz]
    exact term_centralIndex_eq ha hr hn₀
  have hfac : coeffFun a z
      = (a (centralIndex a r) * z ^ centralIndex a r)
        * ∑' n : ℕ, normalisedCoeff a r z n :=
    coeffFun_eq_central_term_mul_tsum ha hr hn₀ hz
  have hWnorm : ‖∑' n : ℕ, normalisedCoeff a r z n‖ = ‖coeffFun a z‖ / maxTerm a r := by
    rw [hfac, norm_mul, hCnorm]
    field_simp
  have hWpos : 0 < ‖∑' n : ℕ, normalisedCoeff a r z n‖ := by
    rw [hWnorm]
    positivity
  have hdefect := tsum_normalised_defect_eq ha hr hn₀ hz hu hWdir
  have hSb : coeffSum a r ≤ (1 + D) * ‖coeffFun a z‖ := by
    refine coeffSum_le_one_add_defect_mul_norm ha hr hn₀ hz hfz ?_ hD
    rw [hdefect, hWnorm, sub_div]
  have hE0 : 0 ≤ E := by
    refine le_trans (tsum_nonneg fun n => ?_) hE
    exact mul_nonneg (abs_nonneg _) (alignment_defect_nonneg _ hu)
  rw [norm_mul_logDeriv_sub_centralIndex_eq ha hr hn₀ hz hfne hcrit hu hWdir,
    div_le_iff₀ hWpos, hWnorm]
  refine le_trans (abs_tsum_index_weighted_re_le ha hr hn₀ hz hu hE) ?_
  have hratio : 1 ≤ ‖coeffFun a z‖ / maxTerm a r := by
    rw [le_div_iff₀ hμpos]
    linarith
  have hS : coeffSum a r / maxTerm a r ≤ (1 + D) * (‖coeffFun a z‖ / maxTerm a r) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hSb hμpos.le
  nlinarith [hS, hratio, hE0, abs_nonneg (meanIndex a r - (centralIndex a r : ℝ))]


set_option maxHeartbeats 400000 in
/-- **The weighted misalignment is bounded by twice the coefficient deviation.**  Each misalignment
is at most twice the modulus of its term, so the weighted misalignment inherits the coefficient-free
bound proved for the deviation series. -/
theorem tsum_index_weighted_defect_le
    (ha : EntireCoeffs a) (ht : 0 < t) (htr : t < r) (hrs : r < s)
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {z : ℂ} (hz : ‖z‖ = r) {u : ℂ} (hu : ‖u‖ = 1) :
    ∑' n : ℕ, |(n : ℝ) - (centralIndex a r : ℝ)|
        * (‖normalisedCoeff a r z n‖
          - ((starRingEnd ℂ) u * normalisedCoeff a r z n).re)
      ≤ 2 * (((centralIndex a s : ℝ) - (centralIndex a t : ℝ))
            * ((centralIndex a s + 1 - centralIndex a t : ℕ) : ℝ)
          + (centralIndex a r : ℝ) * ((t / r) / (1 - t / r))
          + ((centralIndex a s : ℝ) + 1)
              * ∑' j : ℕ, ((1 : ℝ) + j) * (r / s) ^ (j + 1)) := by
  have hr : 0 < r := lt_trans ht htr
  obtain ⟨-, -, hμpos⟩ := exists_maxTerm_eq ha hr hn₀
  set k := centralIndex a r with hk
  set c : ℕ → ℂ := normalisedCoeff a r z with hc
  set d : ℕ → ℝ := fun n => ‖c n‖ - ((starRingEnd ℂ) u * c n).re with hd
  have hdnn : ∀ n, 0 ≤ d n := fun n => alignment_defect_nonneg (c n) hu
  have habs := summable_index_deviation_normalised ha hr hn₀ hz k
  have hle : ∀ n : ℕ, |(n : ℝ) - (k : ℝ)| * d n ≤ 2 * (|(n : ℝ) - (k : ℝ)| * ‖c n‖) := by
    intro n
    have h := re_conj_mul_le_norm (-(c n)) hu
    simp only [Complex.neg_re, norm_neg, mul_neg] at h
    have hle2 : d n ≤ 2 * ‖c n‖ := by
      simp only [hd]
      linarith
    nlinarith [abs_nonneg ((n : ℝ) - (k : ℝ)), hdnn n]
  have hsumL : Summable fun n : ℕ => |(n : ℝ) - (k : ℝ)| * d n :=
    (habs.mul_left 2).of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (hdnn n)) hle
  have hcnorm : ∀ n, ‖c n‖ = (‖a n‖ * r ^ n) / maxTerm a r := by
    intro n
    have hCnorm : ‖a k * z ^ k‖ = maxTerm a r := by
      rw [norm_mul, norm_pow, hz]
      exact term_centralIndex_eq ha hr hn₀
    rw [hc, normalisedCoeff_def, norm_div, ← hk, hCnorm, norm_mul, norm_pow, hz]
  have hmoment : ∑' n : ℕ, |(n : ℝ) - (k : ℝ)| * ‖c n‖
      ≤ ((centralIndex a s : ℝ) - (centralIndex a t : ℝ))
            * ((centralIndex a s + 1 - centralIndex a t : ℕ) : ℝ)
          + (centralIndex a r : ℝ) * ((t / r) / (1 - t / r))
          + ((centralIndex a s : ℝ) + 1)
              * ∑' j : ℕ, ((1 : ℝ) + j) * (r / s) ^ (j + 1) := by
    have hrw : ∑' n : ℕ, |(n : ℝ) - (k : ℝ)| * ‖c n‖
        = (∑' n : ℕ, |(n : ℝ) - (k : ℝ)| * (‖a n‖ * r ^ n)) / maxTerm a r := by
      rw [← tsum_div_const]
      refine tsum_congr fun n => ?_
      rw [hcnorm n]
      ring
    rw [hrw, div_le_iff₀ hμpos]
    have h := tsum_index_deviation_le_maxTerm ha ht htr hrs hn₀
    rw [← hk] at h
    calc ∑' n : ℕ, |(n : ℝ) - (k : ℝ)| * (‖a n‖ * r ^ n) ≤ maxTerm a r * _ := h
      _ = _ * maxTerm a r := by ring
  calc ∑' n : ℕ, |(n : ℝ) - (k : ℝ)| * d n
      ≤ ∑' n : ℕ, 2 * (|(n : ℝ) - (k : ℝ)| * ‖c n‖) :=
        Summable.tsum_le_tsum hle hsumL (habs.mul_left 2)
    _ = 2 * ∑' n : ℕ, |(n : ℝ) - (k : ℝ)| * ‖c n‖ := tsum_mul_left
    _ ≤ 2 * _ := by
        refine mul_le_mul_of_nonneg_left hmoment (by norm_num)


/-- The total misalignment at a point reaching the maximum term, for the direction of the value. -/
theorem tsum_normalised_defect_le_centralIndex
    (ha : EntireCoeffs a) (hr : 0 < r) (hrs : r < s) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {z : ℂ} (hz : ‖z‖ = r) (hfz : maxTerm a r ≤ ‖coeffFun a z‖)
    {u : ℂ} (hu : ‖u‖ = 1)
    (hWdir : ∑' n : ℕ, normalisedCoeff a r z n
      = ((‖∑' n : ℕ, normalisedCoeff a r z n‖ : ℝ) : ℂ) * u) :
    ∑' n : ℕ, (‖normalisedCoeff a r z n‖
        - ((starRingEnd ℂ) u * normalisedCoeff a r z n).re)
      ≤ (centralIndex a s : ℝ) + (r / s) / (1 - r / s) := by
  obtain ⟨-, -, hμpos⟩ := exists_maxTerm_eq ha hr hn₀
  have hfac : coeffFun a z
      = (a (centralIndex a r) * z ^ centralIndex a r)
        * ∑' n : ℕ, normalisedCoeff a r z n :=
    coeffFun_eq_central_term_mul_tsum ha hr hn₀ hz
  have hCnorm : ‖a (centralIndex a r) * z ^ centralIndex a r‖ = maxTerm a r := by
    rw [norm_mul, norm_pow, hz]
    exact term_centralIndex_eq ha hr hn₀
  have hWnorm : ‖∑' n : ℕ, normalisedCoeff a r z n‖ = ‖coeffFun a z‖ / maxTerm a r := by
    rw [hfac, norm_mul, hCnorm]
    field_simp
  have hW1 : (1 : ℝ) ≤ ‖∑' n : ℕ, normalisedCoeff a r z n‖ := by
    rw [hWnorm, le_div_iff₀ hμpos]
    linarith
  have hS := coeffSum_le_maxTerm_mul_centralIndex ha hr hrs hn₀
  have hSμ : coeffSum a r / maxTerm a r
      ≤ ((centralIndex a s : ℝ) + 1) + (r / s) / (1 - r / s) := by
    rw [div_le_iff₀ hμpos]
    calc coeffSum a r ≤ maxTerm a r * (((centralIndex a s : ℝ) + 1) + (r / s) / (1 - r / s)) := hS
      _ = (((centralIndex a s : ℝ) + 1) + (r / s) / (1 - r / s)) * maxTerm a r := by ring
  rw [tsum_normalised_defect_eq ha hr hn₀ hz hu hWdir]
  linarith

set_option maxHeartbeats 400000 in
/-- **The Wiman--Valiron estimate with coefficient-free remainders.**  Both misalignment terms are
replaced by expressions in the central indices and the radius ratios. -/
theorem norm_mul_logDeriv_sub_centralIndex_le_explicit
    (ha : EntireCoeffs a) (ht : 0 < t) (htr : t < r) (hrs : r < s)
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {z : ℂ} (hz : ‖z‖ = r)
    (hfz : maxTerm a r ≤ ‖coeffFun a z‖)
    (hcrit : (z * deriv (coeffFun a) z / coeffFun a z).im = 0)
    {u : ℂ} (hu : ‖u‖ = 1)
    (hWdir : ∑' n : ℕ, normalisedCoeff a r z n
      = ((‖∑' n : ℕ, normalisedCoeff a r z n‖ : ℝ) : ℂ) * u) :
    ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a r : ℂ)‖
      ≤ (1 + ((centralIndex a s : ℝ) + (r / s) / (1 - r / s)))
          * |meanIndex a r - (centralIndex a r : ℝ)|
        + 2 * (((centralIndex a s : ℝ) - (centralIndex a t : ℝ))
            * ((centralIndex a s + 1 - centralIndex a t : ℕ) : ℝ)
          + (centralIndex a r : ℝ) * ((t / r) / (1 - t / r))
          + ((centralIndex a s : ℝ) + 1)
              * ∑' j : ℕ, ((1 : ℝ) + j) * (r / s) ^ (j + 1)) := by
  have hr : 0 < r := lt_trans ht htr
  exact norm_mul_logDeriv_sub_centralIndex_le_meanIndex ha hr hn₀ hz hfz hcrit hu hWdir
    (tsum_normalised_defect_le_centralIndex ha hr hrs hn₀ hz hfz hu hWdir)
    (tsum_index_weighted_defect_le ha ht htr hrs hn₀ hz hu)


end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.MaximumTermCentralIndex
import GaloisForLFunctions.HTGeometry.DiscreteJensenExp

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


end GaloisForLFunctions.HTGeometry

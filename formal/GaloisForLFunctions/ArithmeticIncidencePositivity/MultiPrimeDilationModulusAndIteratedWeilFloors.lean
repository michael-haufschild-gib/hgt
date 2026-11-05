import GaloisForLFunctions.ArithmeticIncidencePositivity.AWeilFloorSurvivesAnotherDilation

/-!
# Multi-prime dilation modulus on arbitrary compact windows and an infinite tower of Weil-floor apertures

`GammaDilationControlsTheArchimedeanForm` and `LinearKreinSmoothingAndInverseLinearGridTail`
already hold on all of `C²_c(ℝ)` without support-width restrictions. Extending the polar
Lipschitz modulus and the prime-sum correlation modulus from `[-1/2, 1/2]` to arbitrary half-width
`R > 0` yields:

1. **Arbitrary-radius polar mass and dilation bounds** (`abs_realPoleForm_le_of_radius`,
   `realPoleForm_dilation_bound_of_radius`): on `[-R, R]`, `|realPoleForm f| ≤ 4 R e^R ∫ f²` and
   `|r · realPoleForm(f(r ·)) - realPoleForm f| ≤ 4 R (R + 1) e^R (r - 1) ∫ f²` for all `r ≥ 1`.
2. **Multi-prime truncation and low-energy Lévy bound** (`primeSum_eq_finsetSum_of_radius`,
   `biScaleLevyEnergy_le_of_fullZeroForm_le_mass_of_radius`): on `[-R, R]`, `primeSum f` truncates
   to `2 ≤ n ≤ ⌊e^{2R}⌋₊` (capturing `{2, 3, 4}` across `(log 4)/2 ≤ R < (log 5)/2` and arbitrary
   finite prime sets at larger `R`), and `fullZeroForm f ≤ ∫ f²` forces an explicit `L²` bound on
   `biScaleLevyEnergy f`.
3. **Derivative-free multi-prime dilation modulus** (`fullZeroForm_dilation_bound_of_radius`):
   for `1 < r` with `(r - 1) max 1 (2R) < 1`, `|r · fullZeroForm(f(r ·)) - fullZeroForm f|` is
   bounded in `∫ f²` with logarithmic rate `1 / (-log((r - 1) max 1 (2R)))`.
4. **Quantitative openness across arbitrary prime-power thresholds**
   (`fullZeroForm_ge_of_dilated_radius`): any floor `δ ∈ (0, 1]` on `[-R, R]` (`R > 0`) propagates
   unconditionally to `δ / 2` on `[-(R * (1 + multiPrimeApertureStep R δ)), R * (1 + multiPrimeApertureStep R δ)]`,
   even when new prime powers enter `(2R, 2R(1 + d)]`.
5. **Infinite strictly increasing tower of unconditional Weil-floor apertures**
   (`weilFloorApertureTower`, `fullZeroForm_ge_of_support_le_weilFloorApertureTower`,
   `zetaZeroConfig_re_W_ge_of_aperture_le_weilFloorApertureTower`): starting from
   `successorWeilFloorAperture > enlargedWeilFloorAperture`, every `k : ℕ` yields an explicit
   aperture `weilFloorApertureTower k < weilFloorApertureTower (k + 1)` with unconditional real and
   complex Weil floor `(1 / 20000) / 2 ^ k`.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.ArchimedeanExactForm
open ArithmeticCriticalityTheory RenormalizedArithmeticPotentialTheory BiScaleUncertainty
open SelectivePositivityAndThresholdLaws

/-! ### 1. Arbitrary-radius polar mass and dilation bounds -/

private theorem abs_exp_parameter_sub_le_of_radius {R q q' u : ℝ}
    (hq : |q| ≤ 1 / 2) (hq' : |q'| ≤ 1 / 2) (hu : |u| ≤ R) :
    |Real.exp (q * u) - Real.exp (q' * u)| ≤ R * Real.exp (R / 2) * |q - q'| := by
  have hd (a : ℝ) : HasDerivAt (fun a => Real.exp (a * u)) (Real.exp (a * u) * u) a := by
    convert! (Real.hasDerivAt_exp (a * u)).comp a ((hasDerivAt_id a).mul_const u) using 1
    simp only [one_mul]
  have hb (a : ℝ) (ha : a ∈ Icc (-(1 / 2)) (1 / 2)) :
      ‖deriv (fun a => Real.exp (a * u)) a‖ ≤ R * Real.exp (R / 2) := by
    rw [(hd a).deriv, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (a * u) ≤ Real.exp (R / 2) := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul (abs_le.mpr ha) hu (abs_nonneg u) (by norm_num)
      have hle := le_abs_self (a * u)
      rw [abs_mul] at hle
      linarith only [hmul, hle]
    exact (mul_le_mul hexp hu (abs_nonneg _) (Real.exp_pos _).le).trans_eq (by ring)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Icc (-(1 / 2 : ℝ)) (1 / 2)) (fun a _ => (hd a).differentiableAt)
    hb (convex_Icc _ _) (abs_le.mp hq') (abs_le.mp hq)
  simpa only [Real.norm_eq_abs] using h

/-- Exponential moments with `|q| ≤ 1/2` on `[-R, R]` are bounded by `e^{R/2} ∫ |f|`. -/
theorem abs_exponentialMoment_le_of_radius {R : ℝ} {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hs : ∀ u, R < |u| → f u = 0) {q : ℝ} (hq : |q| ≤ 1 / 2) :
    |atomExponentialMoment f q| ≤ Real.exp (R / 2) * ∫ u, |f u| := by
  have hi : Integrable (fun u => |f u|) := hf.abs.integrable_of_hasCompactSupport hfc.abs
  have hm : Integrable (fun u => f u * Real.exp (q * u)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  unfold atomExponentialMoment
  rw [← integral_const_mul]
  refine abs_integral_le_integral_abs.trans (integral_mono hm.abs (hi.const_mul _) ?_)
  intro u
  change |f u * Real.exp (q * u)| ≤ Real.exp (R / 2) * |f u|
  by_cases hfu : f u = 0
  · simp only [hfu, zero_mul, abs_zero, mul_zero, le_refl]
  have hu : |u| ≤ R := le_of_not_gt fun hu => hfu (hs u hu)
  rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_comm (|f u|)]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul hq hu (abs_nonneg u) (by norm_num)
  have hle := le_abs_self (q * u)
  rw [abs_mul] at hle
  linarith only [hmul, hle]

/-- Exponential moments on `[-R, R]` are uniformly `R e^{R/2}`-Lipschitz in `q ∈ [-1/2, 1/2]`. -/
theorem abs_exponentialMoment_sub_le_of_radius {R : ℝ} {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hs : ∀ u, R < |u| → f u = 0) {q q' : ℝ}
    (hq : |q| ≤ 1 / 2) (hq' : |q'| ≤ 1 / 2) :
    |atomExponentialMoment f q - atomExponentialMoment f q'| ≤
      R * Real.exp (R / 2) * |q - q'| * ∫ u, |f u| := by
  have hi : Integrable (fun u => |f u|) := hf.abs.integrable_of_hasCompactSupport hfc.abs
  have hm (a : ℝ) : Integrable (fun u => f u * Real.exp (a * u)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  rw [atomExponentialMoment, atomExponentialMoment, ← integral_sub (hm q) (hm q'),
    ← integral_const_mul]
  refine abs_integral_le_integral_abs.trans
    (integral_mono ((hm q).sub (hm q')).abs (hi.const_mul _) ?_)
  intro u
  change |f u * Real.exp (q * u) - f u * Real.exp (q' * u)| ≤
    R * Real.exp (R / 2) * |q - q'| * |f u|
  by_cases hfu : f u = 0
  · simp only [hfu, zero_mul, sub_zero, abs_zero, mul_zero, le_refl]
  have hu : |u| ≤ R := le_of_not_gt fun hu => hfu (hs u hu)
  rw [← mul_sub, abs_mul, mul_comm (|f u|)]
  exact mul_le_mul_of_nonneg_right (abs_exp_parameter_sub_le_of_radius hq hq' hu) (abs_nonneg _)

/-- On `[-R, R]` (`R > 0`), `|realPoleForm f| ≤ 4 R e^R ∫ f²`. -/
theorem abs_realPoleForm_le_of_radius {R : ℝ} (hR : 0 < R) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hs : ∀ u, R < |u| → f u = 0) :
    |realPoleForm f| ≤ 4 * R * Real.exp R * ∫ u, f u ^ 2 := by
  have hp := abs_exponentialMoment_le_of_radius hf.continuous hfc hs
    (q := 1 / 2) (by norm_num)
  have hm := abs_exponentialMoment_le_of_radius hf.continuous hfc hs
    (q := -(1 / 2)) (by norm_num)
  have hs' : ∀ u, (2 * R) / 2 < |u| → f u = 0 := by
    intro u hu; exact hs u (by linarith only [hu])
  have hmass := _root_.RHTower.SeparatedBump.sq_integral_abs_le hf hs' (by positivity : 0 < 2 * R)
  have he : Real.exp (R / 2) * Real.exp (R / 2) = Real.exp R := by
    rw [← Real.exp_add]; ring_nf
  rw [realPoleForm, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2 * (Real.exp (R / 2) * ∫ u, |f u|) * (Real.exp (R / 2) * ∫ u, |f u|) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp (by norm_num)) hm
        (abs_nonneg _) (by positivity)
    _ = 2 * Real.exp R * (∫ u, |f u|) ^ 2 := by
      have : 2 * (Real.exp (R / 2) * ∫ u, |f u|) * (Real.exp (R / 2) * ∫ u, |f u|) =
          2 * (Real.exp (R / 2) * Real.exp (R / 2)) * (∫ u, |f u|) ^ 2 := by ring
      rw [this, he]
    _ ≤ 2 * Real.exp R * ((2 * R) * ∫ u, f u ^ 2) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = 4 * R * Real.exp R * ∫ u, f u ^ 2 := by ring

/-- Arbitrary-radius linear dilation bound for `realPoleForm` on `[-R, R]`. -/
theorem realPoleForm_dilation_bound_of_radius {R : ℝ} (hR : 0 < R) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hs : ∀ u, R < |u| → f u = 0) {r : ℝ} (hr : 1 ≤ r) :
    |r * realPoleForm (fun u => f (r * u)) - realPoleForm f| ≤
      4 * R * (R + 1) * Real.exp R * (r - 1) * ∫ u, f u ^ 2 := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  let C := Real.exp (R / 2)
  let A := ∫ u, |f u|
  let q : ℝ := (1 / 2) / r
  let p := atomExponentialMoment f q
  let m := atomExponentialMoment f (-q)
  let p₀ := atomExponentialMoment f (1 / 2)
  let m₀ := atomExponentialMoment f (-(1 / 2))
  have hA : 0 ≤ A := integral_nonneg fun u => abs_nonneg _
  have hC : 0 < C := Real.exp_pos _
  have hq0 : 0 ≤ q := div_nonneg (by norm_num) hr0.le
  have hq : q ≤ 1 / 2 := (div_le_iff₀ hr0).mpr (by linarith only [hr])
  have hqabs : |q| ≤ 1 / 2 := by rw [abs_of_nonneg hq0]; exact hq
  have hqd : |q - 1 / 2| ≤ (r - 1) / 2 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hq)]
    have hqr : q * r = 1 / 2 := div_mul_cancel₀ _ hr0.ne'
    apply le_of_not_gt fun hbad => ?_
    have hmul := mul_lt_mul_of_pos_right hbad hr0
    nlinarith only [sq_nonneg (r - 1), hqr, hmul]
  have hp : |p| ≤ C * A := abs_exponentialMoment_le_of_radius hf.continuous hfc hs hqabs
  have hm : |m| ≤ C * A := abs_exponentialMoment_le_of_radius hf.continuous hfc hs
    (by simpa only [abs_neg] using hqabs)
  have hp₀ : |p₀| ≤ C * A :=
    abs_exponentialMoment_le_of_radius hf.continuous hfc hs (by norm_num)
  have hm₀ : |m₀| ≤ C * A :=
    abs_exponentialMoment_le_of_radius hf.continuous hfc hs (by norm_num)
  have hdp : |p - p₀| ≤ (R * C / 2) * (r - 1) * A := by
    have h := abs_exponentialMoment_sub_le_of_radius hf.continuous hfc hs hqabs
      (by norm_num : |(1 / 2 : ℝ)| ≤ 1 / 2)
    exact h.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hqd (by positivity)) hA).trans_eq (by ring))
  have hdm : |m - m₀| ≤ (R * C / 2) * (r - 1) * A := by
    have h := abs_exponentialMoment_sub_le_of_radius hf.continuous hfc hs
      (q := -q) (q' := -(1 / 2)) (by simpa only [abs_neg] using hqabs) (by norm_num)
    rw [neg_sub_neg, abs_sub_comm (1 / 2 : ℝ) q] at h
    exact h.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hqd (by positivity)) hA).trans_eq (by ring))
  have hprod : |p * m - p₀ * m₀| ≤ R * C ^ 2 * (r - 1) * A ^ 2 := by
    rw [show p * m - p₀ * m₀ = (p - p₀) * m + p₀ * (m - m₀) by ring]
    calc
      _ ≤ |p - p₀| * |m| + |p₀| * |m - m₀| := by
        simpa only [abs_mul] using abs_add_le ((p - p₀) * m) (p₀ * (m - m₀))
      _ ≤ ((R * C / 2) * (r - 1) * A) * (C * A) +
          (C * A) * ((R * C / 2) * (r - 1) * A) := add_le_add
        (mul_le_mul hdp hm (abs_nonneg _) (by positivity))
        (mul_le_mul hp₀ hdm (abs_nonneg _) (by positivity))
      _ = _ := by ring
  have hprod₀ : |p₀ * m₀| ≤ C ^ 2 * A ^ 2 := by
    rw [abs_mul]
    exact (mul_le_mul hp₀ hm₀ (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hinv0 : 0 ≤ 2 / r := div_nonneg (by norm_num) hr0.le
  have hinv2 : 2 / r ≤ 2 := (div_le_iff₀ hr0).mpr (by linarith only [hr])
  have hcoef : |2 / r - 2| ≤ 2 * (r - 1) := by
    rw [abs_of_nonpos (by linarith only [hinv2])]
    have hqr : (2 / r) * r = 2 := div_mul_cancel₀ _ hr0.ne'
    apply le_of_not_gt fun hbad => ?_
    have hmul := mul_lt_mul_of_pos_right hbad hr0
    nlinarith only [sq_nonneg (r - 1), hqr, hmul]
  have hscale : r * realPoleForm (fun u => f (r * u)) = 2 / r * p * m := by
    rw [realPoleForm, exponentialMoment_comp_mul f hr0, exponentialMoment_comp_mul f hr0]
    change r * (2 * (r⁻¹ * p) * (r⁻¹ * atomExponentialMoment f (-(1 / 2) / r))) = _
    rw [neg_div]
    change r * (2 * (r⁻¹ * p) * (r⁻¹ * m)) = _
    field_simp
  rw [hscale]
  change |2 / r * p * m - 2 * p₀ * m₀| ≤ _
  have hwhole : |2 / r * p * m - 2 * p₀ * m₀| ≤ 2 * (R + 1) * C ^ 2 * (r - 1) * A ^ 2 := by
    rw [show 2 / r * p * m - 2 * p₀ * m₀ =
      (2 / r) * (p * m - p₀ * m₀) + (2 / r - 2) * (p₀ * m₀) by ring]
    calc
      _ ≤ |2 / r| * |p * m - p₀ * m₀| + |2 / r - 2| * |p₀ * m₀| := by
        simpa only [abs_mul] using abs_add_le ((2 / r) * (p * m - p₀ * m₀))
          ((2 / r - 2) * (p₀ * m₀))
      _ ≤ 2 * (R * C ^ 2 * (r - 1) * A ^ 2) + (2 * (r - 1)) * (C ^ 2 * A ^ 2) := add_le_add
        (mul_le_mul (by rw [abs_of_nonneg hinv0]; exact hinv2) hprod (abs_nonneg _) (by norm_num))
        (mul_le_mul hcoef hprod₀ (abs_nonneg _) (by positivity))
      _ = _ := by ring
  have hs' : ∀ u, (2 * R) / 2 < |u| → f u = 0 := fun u hu => hs u (by linarith only [hu])
  have hmass : A ^ 2 ≤ (2 * R) * ∫ u, f u ^ 2 :=
    _root_.RHTower.SeparatedBump.sq_integral_abs_le hf hs' (by positivity : 0 < 2 * R)
  have hC2 : C ^ 2 = Real.exp R := by
    dsimp only [C]; rw [sq, ← Real.exp_add]; ring_nf
  rw [hC2] at hwhole
  exact hwhole.trans ((mul_le_mul_of_nonneg_left hmass
    (by have := sub_nonneg.mpr hr; positivity)).trans_eq (by ring))

/-! ### 2. Multi-prime truncation and low-energy Lévy bound on `[-R, R]` -/

/-- Autocorrelation vanishes beyond `2R` whenever `f` vanishes outside `[-R, R]`. -/
theorem autocorr_zero_of_radius {R : ℝ} {f : ℝ → ℝ}
    (hs : ∀ u, R < |u| → f u = 0) {t : ℝ} (ht : 2 * R < |t|) :
    autocorr f t = 0 := by
  change (∫ u, f u * f (u + t)) = 0
  have hzero (u : ℝ) : f u * f (u + t) = 0 := by
    by_cases hu : R < |u|
    · rw [hs u hu, zero_mul]
    · have hsu := abs_sub_abs_le_abs_sub t (-u)
      rw [abs_neg, sub_neg_eq_add, add_comm] at hsu
      rw [hs (u + t) (by linarith only [ht, hsu, le_of_not_gt hu]), mul_zero]
  simp only [hzero, integral_zero]

/-- Support in `[-R, R]` is preserved by contraction `u ↦ f(r * u)` for `r ≥ 1`. -/
theorem support_radius_comp_mul {R : ℝ} {f : ℝ → ℝ}
    (hs : ∀ u, R < |u| → f u = 0) {r : ℝ} (hr : 1 ≤ r) :
    ∀ u, R < |u| → f (r * u) = 0 := by
  intro u hu
  apply hs
  rw [abs_mul, abs_of_pos (lt_of_lt_of_le zero_lt_one hr)]
  have h := mul_le_mul_of_nonneg_right hr (abs_nonneg u)
  linarith only [hu, h]

/-- On `[-R, R]`, `primeSum f` truncates to the finite prime-power window `2 ≤ n ≤ ⌊e^{2R}⌋₊`. -/
theorem primeSum_eq_finsetSum_of_radius {R : ℝ} {f : ℝ → ℝ}
    (hs : ∀ u, R < |u| → f u = 0) :
    primeSum f = ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * R)⌋₊,
      2 * vonMangoldtAtom n * autocorr f (Real.log n) := by
  have hterm (n : ℕ) :
      vonMangoldtAtom n * ((∫ u, f u * f (u - Real.log n)) + (∫ u, f u * f (u + Real.log n))) =
        2 * vonMangoldtAtom n * autocorr f (Real.log n) := by
    change vonMangoldtAtom n * (autocorr f (-Real.log n) + autocorr f (Real.log n)) = _
    rw [autocorr_neg]; ring
  unfold primeSum
  simp_rw [hterm]
  refine tsum_eq_sum fun n hn => ?_
  simp only [Finset.mem_Icc, not_and_or, not_le] at hn
  rcases hn with hn2 | hgt
  · rw [vonMangoldtAtom, if_neg (by omega : ¬ 2 ≤ n), mul_zero, zero_mul]
  · have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hexp_lt : Real.exp (2 * R) < n :=
      (Nat.floor_lt (Real.exp_pos (2 * R)).le).mp hgt
    have hlog : 2 * R < Real.log n := (Real.lt_log_iff_exp_lt hn_pos).mpr hexp_lt
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hlog_nn : 0 ≤ Real.log n := Real.log_nonneg hn1
    rw [autocorr_zero_of_radius hs (by rwa [abs_of_nonneg hlog_nn]), mul_zero]

/-- Total symmetric prime-power weight acting on `[-R, R]`. -/
def multiPrimeWeightSum (R : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * R)⌋₊, 2 * vonMangoldtAtom n

theorem multiPrimeWeightSum_nonneg (R : ℝ) : 0 ≤ multiPrimeWeightSum R :=
  Finset.sum_nonneg fun n _ => mul_nonneg (by norm_num) (vonMangoldtAtom_nonneg n)

/-- Explicit upper-bound constant for `biScaleLevyEnergy f` on the low-energy cone `fullZeroForm f ≤ ∫ f²`. -/
def multiPrimeLowEnergyConstant (R : ℝ) : ℝ :=
  1 + 2 * |gammaHardyPhaseRate 0| + multiPrimeWeightSum R + 4 * R * Real.exp R

theorem multiPrimeLowEnergyConstant_pos {R : ℝ} (hR : 0 < R) :
    0 < multiPrimeLowEnergyConstant R := by
  have hw := multiPrimeWeightSum_nonneg R
  unfold multiPrimeLowEnergyConstant
  positivity

/-- Bounded full energy `fullZeroForm f ≤ ∫ f²` on `[-R, R]` forces an explicit `L²` bound on
`biScaleLevyEnergy f`. -/
theorem biScaleLevyEnergy_le_of_fullZeroForm_le_mass_of_radius {R : ℝ} (hR : 0 < R) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hs : ∀ u, R < |u| → f u = 0)
    (hQ : fullZeroForm f ≤ ∫ u, f u ^ 2) :
    biScaleLevyEnergy f ≤ multiPrimeLowEnergyConstant R * ∫ u, f u ^ 2 := by
  have hmass0 : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hmass : autocorr f 0 = ∫ u, f u ^ 2 := by
    unfold autocorr; simp only [add_zero, ← sq]
  have hprime : primeSum f ≤ multiPrimeWeightSum R * ∫ u, f u ^ 2 := by
    rw [primeSum_eq_finsetSum_of_radius hs, multiPrimeWeightSum, Finset.sum_mul]
    refine Finset.sum_le_sum fun n _ => ?_
    have hp := abs_autocorr_le_zero hfc hf.continuous (Real.log n)
    rw [hmass] at hp
    have hw : 0 ≤ 2 * vonMangoldtAtom n := mul_nonneg (by norm_num) (vonMangoldtAtom_nonneg n)
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans hp) hw
  have hpolar := neg_abs_le (realPoleForm f)
  have hb := abs_realPoleForm_le_of_radius hR hf hfc hs
  have hgamma := mul_le_mul_of_nonneg_right (neg_abs_le (gammaHardyPhaseRate 0)) hmass0
  rw [fullZeroForm_eq_arch_prime_pole hf hfc, archForm_eq_levyEnergy hf hfc,
    levyEnergy_eq_biScaleLevyEnergy hf.continuous hfc] at hQ
  unfold multiPrimeLowEnergyConstant
  nlinarith only [hQ, hprime, hpolar, hb, hgamma]

/-! ### 3. Derivative-free multi-prime dilation modulus on `[-R, R]` -/

/-- Numerator of the logarithmic prime-sum dilation modulus on `[-R, R]`. -/
def multiPrimeDilationCoeff (R : ℝ) : ℝ :=
  multiPrimeWeightSum R * (32 * Real.exp (1 / 2) * multiPrimeLowEnergyConstant R + 2)

theorem multiPrimeDilationCoeff_nonneg {R : ℝ} (hR : 0 < R) :
    0 ≤ multiPrimeDilationCoeff R := by
  unfold multiPrimeDilationCoeff
  have hw := multiPrimeWeightSum_nonneg R
  have hL := multiPrimeLowEnergyConstant_pos hR
  positivity

/-- Normalized dilation shifts every acting prime-power lag simultaneously. -/
theorem primeSum_normalized_dilation_of_radius {R : ℝ} {f : ℝ → ℝ}
    (hs : ∀ u, R < |u| → f u = 0) {r : ℝ} (hr : 1 ≤ r) :
    r * primeSum (fun u => f (r * u)) - primeSum f =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * R)⌋₊,
        2 * vonMangoldtAtom n * (autocorr f (r * Real.log n) - autocorr f (Real.log n)) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [primeSum_eq_finsetSum_of_radius (support_radius_comp_mul hs hr),
    primeSum_eq_finsetSum_of_radius hs, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hc : autocorr (fun u => f (r * u)) (Real.log n) =
      r⁻¹ * autocorr f (r * Real.log n) := by
    unfold autocorr
    have heq : (∫ u, f (r * u) * f (r * (u + Real.log n))) =
        ∫ u, (fun v => f v * f (v + r * Real.log n)) (r * u) :=
      integral_congr_ae (Filter.Eventually.of_forall fun u => by
        change f (r * u) * f (r * (u + Real.log n)) = f (r * u) * f (r * u + r * Real.log n)
        rw [mul_add])
    rw [heq, Measure.integral_comp_mul_left (fun v => f v * f (v + r * Real.log n)) r,
      abs_of_pos (inv_pos.mpr hr0), smul_eq_mul]
  rw [hc]
  field_simp

/-- Multi-prime correlation dilation bound on `[-R, R]`. -/
theorem primeSum_dilation_bound_of_radius {R : ℝ} (hR : 0 < R) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hs : ∀ u, R < |u| → f u = 0)
    (hQ : fullZeroForm f ≤ ∫ u, f u ^ 2) {r : ℝ}
    (hr : 1 < r) (hsmall : (r - 1) * max 1 (2 * R) < 1) :
    |r * primeSum (fun u => f (r * u)) - primeSum f| ≤
      (multiPrimeDilationCoeff R / (-Real.log ((r - 1) * max 1 (2 * R)))) * ∫ u, f u ^ 2 := by
  have hmax1 : (1 : ℝ) ≤ max 1 (2 * R) := le_max_left 1 (2 * R)
  have hdmax0 : 0 < (r - 1) * max 1 (2 * R) := mul_pos (sub_pos.mpr hr) (by positivity)
  have hden : 0 < -Real.log ((r - 1) * max 1 (2 * R)) :=
    neg_pos.mpr (Real.log_neg hdmax0 hsmall)
  have hmass : autocorr f 0 = ∫ u, f u ^ 2 := by
    unfold autocorr; simp only [add_zero, ← sq]
  have hlevy := biScaleLevyEnergy_le_of_fullZeroForm_le_mass_of_radius hR hf hfc hs hQ
  have hmul := mul_le_mul_of_nonneg_left hlevy (show 0 ≤ 32 * Real.exp (1 / 2) by positivity)
  rw [primeSum_normalized_dilation_of_radius hs hr.le]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ n ∈ Finset.Icc 2 ⌊Real.exp (2 * R)⌋₊,
      |2 * vonMangoldtAtom n * (autocorr f (r * Real.log n) - autocorr f (Real.log n))| ≤
        2 * vonMangoldtAtom n *
          (((32 * Real.exp (1 / 2) * multiPrimeLowEnergyConstant R + 2) * ∫ u, f u ^ 2) /
            (-Real.log ((r - 1) * max 1 (2 * R)))) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have hn_gt1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hlog_pos : 0 < Real.log n := Real.log_pos hn_gt1
    have hn_le_exp : (n : ℝ) ≤ Real.exp (2 * R) :=
      Nat.le_floor_iff (Real.exp_pos (2 * R)).le |>.mp hn.2
    have hlog_le : Real.log n ≤ 2 * R :=
      (Real.log_le_iff_le_exp (by positivity)).mpr hn_le_exp
    have hlog_le_max : Real.log n ≤ max 1 (2 * R) := hlog_le.trans (le_max_right 1 (2 * R))
    have hdn0 : 0 < (r - 1) * Real.log n := mul_pos (sub_pos.mpr hr) hlog_pos
    have hdn_le : (r - 1) * Real.log n ≤ (r - 1) * max 1 (2 * R) :=
      mul_le_mul_of_nonneg_left hlog_le_max (sub_pos.mpr hr).le
    have hdn_lt1 : (r - 1) * Real.log n < 1 := hdn_le.trans_lt hsmall
    have hdist : |r * Real.log n - Real.log n| = (r - 1) * Real.log n := by
      rw [show r * Real.log n - Real.log n = (r - 1) * Real.log n by ring, abs_of_pos hdn0]
    have hmod := neg_log_mul_abs_autocorr_sub_le hf hfc
      (x := r * Real.log n) (y := Real.log n) (by rwa [hdist]) (by rwa [hdist])
    rw [hdist, hmass] at hmod
    have hlog_mono : -Real.log ((r - 1) * max 1 (2 * R)) ≤ -Real.log ((r - 1) * Real.log n) :=
      neg_le_neg (Real.log_le_log hdn0 hdn_le)
    have hcorr : |autocorr f (r * Real.log n) - autocorr f (Real.log n)| ≤
        ((32 * Real.exp (1 / 2) * multiPrimeLowEnergyConstant R + 2) * ∫ u, f u ^ 2) /
          (-Real.log ((r - 1) * max 1 (2 * R))) := by
      rw [le_div_iff₀ hden]
      have hmono : (-Real.log ((r - 1) * max 1 (2 * R))) *
          |autocorr f (r * Real.log n) - autocorr f (Real.log n)| ≤
          (-Real.log ((r - 1) * Real.log n)) *
            |autocorr f (r * Real.log n) - autocorr f (Real.log n)| :=
        mul_le_mul_of_nonneg_right hlog_mono (abs_nonneg _)
      nlinarith only [hmono, hmod, hmul]
    have hw : 0 ≤ 2 * vonMangoldtAtom n := mul_nonneg (by norm_num) (vonMangoldtAtom_nonneg n)
    rw [abs_mul, abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_left hcorr hw
  refine (Finset.sum_le_sum hterm).trans_eq ?_
  rw [← Finset.sum_mul, ← multiPrimeWeightSum]
  unfold multiPrimeDilationCoeff
  ring

/-- **Full multi-prime dilation modulus on `[-R, R]`.** On the low-energy cone `fullZeroForm f ≤ ∫ f²`,
contracting `f` by `r > 1` (`(r - 1) max 1 (2R) < 1`) moves `fullZeroForm` by an explicit logarithmic
modulus in `∫ f²` with zero derivative assumptions on `f`. -/
theorem fullZeroForm_dilation_bound_of_radius {R : ℝ} (hR : 0 < R) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hs : ∀ u, R < |u| → f u = 0)
    (hQ : fullZeroForm f ≤ ∫ u, f u ^ 2) {r : ℝ}
    (hr : 1 < r) (hsmall : (r - 1) * max 1 (2 * R) < 1) :
    |r * fullZeroForm (fun u => f (r * u)) - fullZeroForm f| ≤
      (10 * Real.log r + 4 * R * (R + 1) * Real.exp R * (r - 1) +
        multiPrimeDilationCoeff R / (-Real.log ((r - 1) * max 1 (2 * R)))) * ∫ u, f u ^ 2 := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hg : ContDiff ℝ 2 (fun u => f (r * u)) :=
    hf.comp (contDiff_const.mul contDiff_id)
  have hgs := support_radius_comp_mul hs hr.le
  have hgc : HasCompactSupport (fun u => f (r * u)) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -R) (b := R))
      fun u hu => abs_le.mp (le_of_not_gt fun h => hu (hgs u h))
  have harch := archForm_logarithmic_dilation_bound f hf hfc hr0
  rw [abs_of_nonneg (Real.log_nonneg hr.le)] at harch
  have hprime := primeSum_dilation_bound_of_radius hR hf hfc hs hQ hr hsmall
  have hpole := realPoleForm_dilation_bound_of_radius hR hf hfc hs hr.le
  rw [fullZeroForm_eq_arch_prime_pole hg hgc, fullZeroForm_eq_arch_prime_pole hf hfc]
  rw [show r * (archForm (fun u => f (r * u)) - primeSum (fun u => f (r * u)) +
        realPoleForm (fun u => f (r * u))) - (archForm f - primeSum f + realPoleForm f) =
      (r * archForm (fun u => f (r * u)) - archForm f) -
        (r * primeSum (fun u => f (r * u)) - primeSum f) +
        (r * realPoleForm (fun u => f (r * u)) - realPoleForm f) by ring]
  exact ((abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans
    ((add_le_add (add_le_add harch hprime) hpole).trans_eq (by ring))

/-! ### 4. Quantitative openness across arbitrary prime-power thresholds -/

/-- Closed-form dilation step propagating a floor `δ ∈ (0, 1]` on `[-R, R]` to `δ / 2` on
`[-(R * (1 + d)), R * (1 + d)]`, using the upper-envelope radius `(11 / 10) R` so that prime
powers newly entering `(2R, 2R(1 + d)]` are automatically accounted for. -/
def multiPrimeApertureStep (R δ : ℝ) : ℝ :=
  let R₁ := (11 / 10) * R
  min (1 / 10) (min (δ / (4 * (11 + 4 * R₁ * (R₁ + 1) * Real.exp R₁)))
    (Real.exp (-1 - 4 * multiPrimeDilationCoeff R₁ / δ) / max 1 (2 * R₁)))

theorem multiPrimeApertureStep_pos {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    0 < multiPrimeApertureStep R δ := by
  unfold multiPrimeApertureStep
  dsimp only
  have hR₁ : 0 < (11 / 10) * R := by positivity
  apply lt_min (by norm_num)
  refine lt_min (by positivity) (div_pos (Real.exp_pos _) ?_)
  exact lt_of_lt_of_le zero_lt_one (le_max_left 1 (2 * ((11 / 10) * R)))

theorem multiPrimeApertureStep_le_tenth (R δ : ℝ) :
    multiPrimeApertureStep R δ ≤ 1 / 10 := min_le_left _ _

private theorem multiPrimeApertureStep_allowance {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    let R₁ := (11 / 10) * R
    let d := multiPrimeApertureStep R δ
    d * max 1 (2 * R₁) < 1 ∧
      10 * Real.log (1 + d) + 4 * R₁ * (R₁ + 1) * Real.exp R₁ * d +
        multiPrimeDilationCoeff R₁ / (-Real.log (d * max 1 (2 * R₁))) ≤ δ / 2 := by
  dsimp only
  set R₁ := (11 / 10) * R
  set d := multiPrimeApertureStep R δ
  have hR₁ : 0 < R₁ := by dsimp only [R₁]; positivity
  have hd : 0 < d := multiPrimeApertureStep_pos hR hδ
  have hM : 0 < max 1 (2 * R₁) := lt_of_lt_of_le zero_lt_one (le_max_left 1 (2 * R₁))
  have hdM0 : 0 < d * max 1 (2 * R₁) := mul_pos hd hM
  have hlinBound : d ≤ δ / (4 * (11 + 4 * R₁ * (R₁ + 1) * Real.exp R₁)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hprimeBound : d ≤ Real.exp (-1 - 4 * multiPrimeDilationCoeff R₁ / δ) / max 1 (2 * R₁) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hdelta := (le_div_iff₀ hM).mp hprimeBound
  have hcoeff_nn := multiPrimeDilationCoeff_nonneg hR₁
  have hdiv_nn : 0 ≤ 4 * multiPrimeDilationCoeff R₁ / δ := by positivity
  have hsmall : d * max 1 (2 * R₁) < 1 :=
    hdelta.trans_lt (Real.exp_lt_one_iff.mpr (by linarith only [hdiv_nn]))
  refine ⟨hsmall, ?_⟩
  have hB : 0 < 11 + 4 * R₁ * (R₁ + 1) * Real.exp R₁ := by positivity
  have hpay : (11 + 4 * R₁ * (R₁ + 1) * Real.exp R₁) * d ≤ δ / 4 := by
    have := mul_le_mul_of_nonneg_left hlinBound hB.le
    refine this.trans_eq ?_
    field_simp [hB.ne']
  have hlogr := Real.log_le_sub_one_of_pos (show 0 < 1 + d by positivity)
  have hlinear : 10 * Real.log (1 + d) + 4 * R₁ * (R₁ + 1) * Real.exp R₁ * d ≤ δ / 4 := by
    nlinarith only [hlogr, hpay, hd]
  have hlogd := Real.log_le_log hdM0 hdelta
  rw [Real.log_exp] at hlogd
  have hden : 0 < -Real.log (d * max 1 (2 * R₁)) := neg_pos.mpr (Real.log_neg hdM0 hsmall)
  have hprime : multiPrimeDilationCoeff R₁ / (-Real.log (d * max 1 (2 * R₁))) ≤ δ / 4 := by
    rw [div_le_iff₀ hden]
    have h1 : 4 * multiPrimeDilationCoeff R₁ / δ ≤ -Real.log (d * max 1 (2 * R₁)) := by
      linarith only [hlogd]
    have h2 := mul_le_mul_of_nonneg_right h1 hδ.le
    have h3 : (4 * multiPrimeDilationCoeff R₁ / δ) * δ = 4 * multiPrimeDilationCoeff R₁ :=
      div_mul_cancel₀ _ hδ.ne'
    rw [h3] at h2
    linarith only [h2]
  linarith only [hlinear, hprime]

/-- **Quantitative openness across arbitrary prime-power thresholds.** Any positive Weil floor
`δ ∈ (0, 1]` on `[-R, R]` (`R > 0`) propagates to `δ / 2` on `[-(R * (1 + multiPrimeApertureStep R δ)),
R * (1 + multiPrimeApertureStep R δ)]`. -/
theorem fullZeroForm_ge_of_dilated_radius {R δ : ℝ} (hR : 0 < R) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hbase_floor : ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      (∀ u, R < |u| → g u = 0) → δ * (∫ u, g u ^ 2) ≤ fullZeroForm g)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hs : ∀ u, R * (1 + multiPrimeApertureStep R δ) < |u| → f u = 0) :
    (δ / 2) * (∫ u, f u ^ 2) ≤ fullZeroForm f := by
  by_contra hfloor
  have hlt : fullZeroForm f < (δ / 2) * ∫ u, f u ^ 2 := lt_of_not_ge hfloor
  have hE : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hQ : fullZeroForm f ≤ ∫ u, f u ^ 2 := by nlinarith only [hlt, hE, hδ1]
  set d := multiPrimeApertureStep R δ
  set r : ℝ := 1 + d
  set R₁ : ℝ := (11 / 10) * R
  have hd0 : 0 < d := multiPrimeApertureStep_pos hR hδ0
  have hd10 : d ≤ 1 / 10 := multiPrimeApertureStep_le_tenth R δ
  have hr : 1 < r := by dsimp only [r]; linarith only [hd0]
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hR₁ : 0 < R₁ := by dsimp only [R₁]; positivity
  have hsR₁ : ∀ u, R₁ < |u| → f u = 0 := fun u hu => by
    apply hs
    have : R * r ≤ R₁ := by dsimp only [r, R₁]; nlinarith only [hR, hd10]
    exact this.trans_lt hu
  have hg : ContDiff ℝ 2 (fun u => f (r * u)) :=
    hf.comp (contDiff_const.mul contDiff_id)
  have hgs : ∀ u, R < |u| → f (r * u) = 0 := fun u hu => by
    apply hs
    rw [abs_mul, abs_of_pos hr0]
    have := mul_lt_mul_of_pos_left hu hr0
    linarith only [this]
  have hgc : HasCompactSupport (fun u => f (r * u)) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -R) (b := R))
      fun u hu => abs_le.mp (le_of_not_gt fun h => hu (hgs u h))
  have hbase := hbase_floor _ hg hgc hgs
  have hmass : (∫ u, f (r * u) ^ 2) = r⁻¹ * ∫ u, f u ^ 2 := by
    rw [Measure.integral_comp_mul_left (fun u => f u ^ 2) r,
      abs_of_pos (inv_pos.mpr hr0), smul_eq_mul]
  rw [hmass] at hbase
  have hbaseR := mul_le_mul_of_nonneg_left hbase hr0.le
  have hbase_eq : r * (δ * (r⁻¹ * ∫ u, f u ^ 2)) = δ * ∫ u, f u ^ 2 := by field_simp [hr0.ne']
  rw [hbase_eq] at hbaseR
  obtain ⟨hgap, hcost⟩ := multiPrimeApertureStep_allowance hR hδ0
  have hmod := fullZeroForm_dilation_bound_of_radius hR₁ hf hfc hsR₁ hQ hr
    (by simpa only [r, add_sub_cancel_left] using hgap)
  have hmod' : |r * fullZeroForm (fun u => f (r * u)) - fullZeroForm f| ≤
      (δ / 2) * ∫ u, f u ^ 2 := by
    refine hmod.trans (mul_le_mul_of_nonneg_right ?_ hE)
    simpa only [r, add_sub_cancel_left] using hcost
  have hupper := (le_abs_self (r * fullZeroForm (fun u => f (r * u)) - fullZeroForm f)).trans hmod'
  linarith only [hbaseR, hupper, hlt]

/-! ### 5. Infinite strictly increasing tower of unconditional Weil-floor apertures -/

/-- Explicit positive floor `(1 / 20000) / 2 ^ k` at stage `k` of the unconditional aperture tower. -/
def weilFloorTowerConst (k : ℕ) : ℝ :=
  (1 / 20000) / (2 : ℝ) ^ k

theorem weilFloorTowerConst_pos (k : ℕ) : 0 < weilFloorTowerConst k := by
  unfold weilFloorTowerConst; positivity

theorem weilFloorTowerConst_le_one (k : ℕ) : weilFloorTowerConst k ≤ 1 := by
  unfold weilFloorTowerConst
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hdiv : (1 / 20000 : ℝ) / (2 : ℝ) ^ k ≤ (1 / 20000 : ℝ) / 1 :=
    div_le_div_of_nonneg_left (by norm_num) zero_lt_one hpow
  linarith only [hdiv]

theorem weilFloorTowerConst_succ (k : ℕ) :
    weilFloorTowerConst (k + 1) = weilFloorTowerConst k / 2 := by
  unfold weilFloorTowerConst
  rw [pow_succ]
  ring

/-- Infinite strictly increasing tower of explicit positive Weil-floor apertures starting at
`successorWeilFloorAperture` (`k = 0`). -/
def weilFloorApertureTower : ℕ → ℝ
  | 0 => successorWeilFloorAperture
  | k + 1 => weilFloorApertureTower k *
      (1 + multiPrimeApertureStep (weilFloorApertureTower k) (weilFloorTowerConst k))

theorem weilFloorApertureTower_zero :
    weilFloorApertureTower 0 = successorWeilFloorAperture := rfl

theorem weilFloorApertureTower_pos (k : ℕ) : 0 < weilFloorApertureTower k := by
  induction k with
  | zero =>
    exact lt_trans (by norm_num : (0 : ℝ) < 181 / 500)
      (enlargedWeilFloorAperture_bounds.1.trans successorWeilFloorAperture_bounds.1)
  | succ k ih =>
    simp only [weilFloorApertureTower]
    have hd := multiPrimeApertureStep_pos ih (weilFloorTowerConst_pos k)
    exact mul_pos ih (by linarith only [hd])

theorem weilFloorApertureTower_lt_succ (k : ℕ) :
    weilFloorApertureTower k < weilFloorApertureTower (k + 1) := by
  simp only [weilFloorApertureTower]
  have hR := weilFloorApertureTower_pos k
  have hd := multiPrimeApertureStep_pos hR (weilFloorTowerConst_pos k)
  nlinarith only [mul_pos hR hd]

theorem weilFloorApertureTower_strictMono : StrictMono weilFloorApertureTower :=
  strictMono_nat_of_lt_succ weilFloorApertureTower_lt_succ

theorem enlargedWeilFloorAperture_lt_weilFloorApertureTower (k : ℕ) :
    enlargedWeilFloorAperture < weilFloorApertureTower k := by
  rcases k with _ | k
  · exact successorWeilFloorAperture_bounds.1
  · exact successorWeilFloorAperture_bounds.1.trans
      (weilFloorApertureTower_strictMono (Nat.zero_lt_succ k))

/-- **Unconditional Weil floor across the infinite aperture tower.** For every `k : ℕ`, every
real `f ∈ C²_c(ℝ)` supported in `[-weilFloorApertureTower k, weilFloorApertureTower k]` satisfies
`weilFloorTowerConst k * ∫ f² ≤ fullZeroForm f`. -/
theorem fullZeroForm_ge_of_support_le_weilFloorApertureTower (k : ℕ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hs : ∀ u, weilFloorApertureTower k < |u| → f u = 0) :
    weilFloorTowerConst k * (∫ u, f u ^ 2) ≤ fullZeroForm f := by
  induction k generalizing f with
  | zero =>
    simpa only [weilFloorTowerConst, pow_zero, div_one] using
      fullZeroForm_ge_of_support_le_successorWeilFloorAperture hf hfc hs
  | succ k ih =>
    rw [weilFloorTowerConst_succ]
    exact fullZeroForm_ge_of_dilated_radius
      (weilFloorApertureTower_pos k) (weilFloorTowerConst_pos k) (weilFloorTowerConst_le_one k)
      (fun _ hg hgc hgs => ih hg hgc hgs) hf hfc hs

/-- Complex-test counterpart of `fullZeroForm_ge_of_support_le_weilFloorApertureTower` for every `k : ℕ`. -/
theorem zetaZeroConfig_re_W_ge_of_aperture_le_weilFloorApertureTower (k : ℕ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-weilFloorApertureTower k) (weilFloorApertureTower k)) :
    weilFloorTowerConst k * (∫ u, ‖f u‖ ^ 2) ≤ (Zeta23.zetaZeroConfig.W f f).re :=
  SquareRootThreshold.zetaZeroConfig_re_W_ge_of_window
    (fun _ hF hFc hs => fullZeroForm_ge_of_support_le_weilFloorApertureTower k hF hFc hs)
    hf hfs

end GaloisForLFunctions.ArithmeticIncidencePositivity

#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.fullZeroForm_dilation_bound_of_radius
#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.fullZeroForm_ge_of_dilated_radius
#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.weilFloorApertureTower_strictMono
#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.fullZeroForm_ge_of_support_le_weilFloorApertureTower
#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.zetaZeroConfig_re_W_ge_of_aperture_le_weilFloorApertureTower

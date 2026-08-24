import GaloisForLFunctions.RHTower.ThetaCuspFinitePrimeScreenIntegrable
import GaloisForLFunctions.RHTower.HedenmalmThetaAllShiftedTails
import GaloisForLFunctions.RHTower.GaussianMomentFourier
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments

/-!
# Weighted convergence of positive finite-prime theta screens

The source-defined cofinal screens converge to the completed theta source in every fixed
exponentially weighted `L¹` norm.  A single integrable majorant combines the uniform positive-ray
finite-prime tail, the completed source, and the Gaussian diagonal-selection error.
-/

open Filter Topology Set MeasureTheory

noncomputable section

namespace RHTower

/-- Exponentially weighted pointwise error of the selected even screen. -/
def finitePrimeThetaCuspWeightedScreenError (A : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  Real.exp (A * |x|) *
    |finitePrimeThetaCuspEvenScreen j x - thetaCuspFullSource x|

/-- One integrable majorant for all selected screens at a fixed exponential weight. -/
def finitePrimeThetaCuspWeightedScreenMajor (A : ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  finitePrimeThetaCuspWeightedDerivativeConstant 0 q *
      Real.exp (-(((q + 1 : ℕ) : ℝ) - |A|) * |x|) +
    2 * (Real.exp (|A| * |x|) * thetaCuspFullSource x) +
    Real.exp (|A| ^ 2 + 1) * Real.exp (-(1 / 4 : ℝ) * x ^ 2)

theorem integrable_finitePrimeThetaCuspWeightedScreenMajor
    (A : ℝ) (q : ℕ) (hA : |A| < (q + 1 : ℕ)) :
    Integrable (finitePrimeThetaCuspWeightedScreenMajor A q) := by
  have hc : 0 < ((q + 1 : ℕ) : ℝ) - |A| := sub_pos.mpr hA
  have htail : Integrable (fun x : ℝ ↦
      finitePrimeThetaCuspWeightedDerivativeConstant 0 q *
        Real.exp (-(((q + 1 : ℕ) : ℝ) - |A|) * |x|)) := by
    have h := (HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 hc).const_mul
      (finitePrimeThetaCuspWeightedDerivativeConstant 0 q)
    simpa only [pow_zero, one_mul] using h
  have hsource : Integrable (fun x : ℝ ↦
      2 * (Real.exp (|A| * |x|) * thetaCuspFullSource x)) :=
    (HedenmalmThetaSource.integrable_exp_abs_mul_thetaCuspFullSource |A|).const_mul 2
  have hgauss : Integrable (fun x : ℝ ↦
      Real.exp (|A| ^ 2 + 1) * Real.exp (-(1 / 4 : ℝ) * x ^ 2)) := by
    simpa only [pow_zero, one_mul] using
      (integrable_abs_pow_mul_exp_neg_mul_sq
        (by norm_num : (0 : ℝ) < 1 / 4) 0).const_mul (Real.exp (|A| ^ 2 + 1))
  change Integrable (fun x : ℝ ↦
    finitePrimeThetaCuspWeightedDerivativeConstant 0 q *
        Real.exp (-(((q + 1 : ℕ) : ℝ) - |A|) * |x|) +
      2 * (Real.exp (|A| * |x|) * thetaCuspFullSource x) +
      Real.exp (|A| ^ 2 + 1) * Real.exp (-(1 / 4 : ℝ) * x ^ 2))
  exact (htail.add hsource).add hgauss

/-- The diagonal accuracy error, while its transition screen is active, has a fixed Gaussian
majorant independent of the screen index. -/
theorem exp_screenAccuracy_le_gaussianMajor
    (A : ℝ) (j : ℕ) {x : ℝ} (hx : 0 ≤ x)
    (hxj : x ≤ ((j + 1 : ℕ) : ℝ)) :
    Real.exp (|A| * x) * Real.exp (-((j : ℝ) ^ 2)) ≤
      Real.exp (|A| ^ 2 + 1) * Real.exp (-(1 / 4 : ℝ) * x ^ 2) := by
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have hxj' : x ≤ (j : ℝ) + 1 := by
    push_cast at hxj
    exact hxj
  have hsq : x ^ 2 ≤ ((j : ℝ) + 1) ^ 2 :=
    (sq_le_sq₀ hx (by positivity)).2 hxj'
  have hjquad : ((j : ℝ) + 1) ^ 2 ≤ 2 * (j : ℝ) ^ 2 + 2 := by
    nlinarith [sq_nonneg ((j : ℝ) - 1)]
  have hyoung : |A| * x ≤ x ^ 2 / 4 + |A| ^ 2 := by
    nlinarith [sq_nonneg (x - 2 * |A|)]
  have hexp : |A| * x - (j : ℝ) ^ 2 ≤
      |A| ^ 2 + 1 - (1 / 4 : ℝ) * x ^ 2 := by
    nlinarith
  rw [← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

theorem finitePrimeThetaCuspWeightedScreenError_le_major_of_nonneg
    (A : ℝ) (q j : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    finitePrimeThetaCuspWeightedScreenError A j x ≤
      finitePrimeThetaCuspWeightedScreenMajor A q x := by
  let N := finitePrimeThetaCuspPositiveScreenIndex j
  let B := |A|
  let C := finitePrimeThetaCuspWeightedDerivativeConstant 0 q
  let c := ((q + 1 : ℕ) : ℝ) - B
  have hAB : A ≤ B := le_abs_self A
  have hweight : Real.exp (A * x) ≤ Real.exp (B * x) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hAB hx)
  have hsourcePos : 0 < finitePrimeThetaCuspSource N x :=
    finitePrimeThetaCuspSource_pos_of_nonneg N hx
  have hrightEq : finitePrimeThetaCuspRightScreen j x =
      finitePrimeThetaCuspSource N x := by
    rw [finitePrimeThetaCuspRightScreen,
      finitePrimeThetaCuspScreenCutoff_eq_one j (by
        have hj : (0 : ℝ) ≤ (j : ℕ) := by positivity
        linarith), one_mul]
  have hrightTail : Real.exp (B * x) * finitePrimeThetaCuspRightScreen j x ≤
      C * Real.exp (-(c * x)) := by
    have h := exp_mul_abs_finitePrimeThetaCuspDerivative_le 0 q N B hx
    have hzero : finitePrimeThetaCuspDerivative 0 N =
        finitePrimeThetaCuspSource N := by
      rw [← iteratedDeriv_finitePrimeThetaCuspSource]
      simp only [iteratedDeriv_zero]
    rw [hzero, abs_of_pos hsourcePos] at h
    rw [hrightEq]
    simpa only [C, c, neg_mul] using h
  have href : Real.exp (B * x) * finitePrimeThetaCuspRightScreen j (-x) ≤
      Real.exp (B * x) * thetaCuspFullSource x +
        Real.exp (B ^ 2 + 1) * Real.exp (-(1 / 4 : ℝ) * x ^ 2) := by
    by_cases hxj : ((j + 1 : ℕ) : ℝ) ≤ x
    · rw [finitePrimeThetaCuspRightScreen_neg_eq_zero_of_ge j hxj,
        mul_zero]
      exact add_nonneg
        (mul_nonneg (Real.exp_pos _).le
          (HedenmalmThetaSource.thetaCuspFullSource_pos x).le)
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    · have hxj' : x < ((j + 1 : ℕ) : ℝ) := lt_of_not_ge hxj
      have hleftPos : 0 < finitePrimeThetaCuspSource N (-x) :=
        finitePrimeThetaCuspPositiveScreenIndex_pos j (-x) (by linarith)
      have hacc := finitePrimeThetaCuspPositiveScreenIndex_accuracy j
        0 (Nat.zero_le j) (-x)
        (show -((j + 1 : ℕ) : ℝ) ≤ -x ∧
            -x ≤ ((j + 1 : ℕ) : ℝ) by constructor <;> linarith)
      simp only [iteratedDeriv_zero, thetaCuspFullSource_neg] at hacc
      have hleftUpper : finitePrimeThetaCuspSource N (-x) <
          thetaCuspFullSource x + Real.exp (-((j : ℝ) ^ 2)) := by
        have hsub : finitePrimeThetaCuspSource N (-x) - thetaCuspFullSource x <
            Real.exp (-((j : ℝ) ^ 2)) :=
          (le_abs_self _).trans_lt hacc
        linarith
      have hcutNonneg : 0 ≤ finitePrimeThetaCuspScreenCutoff j (-x) :=
        ccmSmoothHalflineCutoff_nonneg _
      have hcutLe : finitePrimeThetaCuspScreenCutoff j (-x) ≤ 1 :=
        ccmSmoothHalflineCutoff_le_one _
      have hrefUpper : finitePrimeThetaCuspRightScreen j (-x) ≤
          thetaCuspFullSource x + Real.exp (-((j : ℝ) ^ 2)) := by
        calc
          finitePrimeThetaCuspRightScreen j (-x) =
              finitePrimeThetaCuspScreenCutoff j (-x) *
                finitePrimeThetaCuspSource N (-x) := rfl
          _ ≤ finitePrimeThetaCuspSource N (-x) :=
            mul_le_of_le_one_left hleftPos.le hcutLe
          _ ≤ thetaCuspFullSource x + Real.exp (-((j : ℝ) ^ 2)) := hleftUpper.le
      have hgauss := exp_screenAccuracy_le_gaussianMajor A j hx hxj'.le
      calc
        Real.exp (B * x) * finitePrimeThetaCuspRightScreen j (-x) ≤
            Real.exp (B * x) *
              (thetaCuspFullSource x + Real.exp (-((j : ℝ) ^ 2))) :=
          mul_le_mul_of_nonneg_left hrefUpper (Real.exp_pos _).le
        _ = Real.exp (B * x) * thetaCuspFullSource x +
              Real.exp (B * x) * Real.exp (-((j : ℝ) ^ 2)) := by ring
        _ ≤ Real.exp (B * x) * thetaCuspFullSource x +
              Real.exp (B ^ 2 + 1) * Real.exp (-(1 / 4 : ℝ) * x ^ 2) := by
          gcongr
  have hscreenNonneg : 0 ≤ finitePrimeThetaCuspEvenScreen j x :=
    (finitePrimeThetaCuspEvenScreen_pos j x).le
  have hfullNonneg : 0 ≤ thetaCuspFullSource x :=
    (HedenmalmThetaSource.thetaCuspFullSource_pos x).le
  have hscreenSum : finitePrimeThetaCuspEvenScreen j x ≤
      finitePrimeThetaCuspRightScreen j x +
        finitePrimeThetaCuspRightScreen j (-x) := by
    unfold finitePrimeThetaCuspEvenScreen
    have hr := finitePrimeThetaCuspRightScreen_nonneg j x
    have hl := finitePrimeThetaCuspRightScreen_nonneg j (-x)
    nlinarith
  have herr : |finitePrimeThetaCuspEvenScreen j x - thetaCuspFullSource x| ≤
      finitePrimeThetaCuspRightScreen j x +
        finitePrimeThetaCuspRightScreen j (-x) + thetaCuspFullSource x := by
    calc
      |finitePrimeThetaCuspEvenScreen j x - thetaCuspFullSource x| =
          |finitePrimeThetaCuspEvenScreen j x + (-thetaCuspFullSource x)| := by ring
      _ ≤ |finitePrimeThetaCuspEvenScreen j x| + |-thetaCuspFullSource x| :=
        abs_add_le _ _
      _ = |finitePrimeThetaCuspEvenScreen j x| + |thetaCuspFullSource x| := by
        rw [abs_neg]
      _ = finitePrimeThetaCuspEvenScreen j x + thetaCuspFullSource x := by
        rw [abs_of_nonneg hscreenNonneg, abs_of_nonneg hfullNonneg]
      _ ≤ finitePrimeThetaCuspRightScreen j x +
          finitePrimeThetaCuspRightScreen j (-x) + thetaCuspFullSource x := by
        linarith
  rw [finitePrimeThetaCuspWeightedScreenError, abs_of_nonneg hx]
  calc
    Real.exp (A * x) *
        |finitePrimeThetaCuspEvenScreen j x - thetaCuspFullSource x| ≤
      Real.exp (B * x) *
        |finitePrimeThetaCuspEvenScreen j x - thetaCuspFullSource x| :=
      mul_le_mul_of_nonneg_right hweight (abs_nonneg _)
    _ ≤ Real.exp (B * x) *
        (finitePrimeThetaCuspRightScreen j x +
          finitePrimeThetaCuspRightScreen j (-x) + thetaCuspFullSource x) :=
      mul_le_mul_of_nonneg_left herr (Real.exp_pos _).le
    _ = Real.exp (B * x) * finitePrimeThetaCuspRightScreen j x +
        Real.exp (B * x) * finitePrimeThetaCuspRightScreen j (-x) +
        Real.exp (B * x) * thetaCuspFullSource x := by ring
    _ ≤ C * Real.exp (-(c * x)) +
        (Real.exp (B * x) * thetaCuspFullSource x +
          Real.exp (B ^ 2 + 1) * Real.exp (-(1 / 4 : ℝ) * x ^ 2)) +
        Real.exp (B * x) * thetaCuspFullSource x := by gcongr
    _ = finitePrimeThetaCuspWeightedScreenMajor A q x := by
      simp only [finitePrimeThetaCuspWeightedScreenMajor, abs_of_nonneg hx, B, C, c]
      ring

theorem finitePrimeThetaCuspWeightedScreenError_le_major
    (A : ℝ) (q j : ℕ) (x : ℝ) :
    finitePrimeThetaCuspWeightedScreenError A j x ≤
      finitePrimeThetaCuspWeightedScreenMajor A q x := by
  rcases le_total 0 x with hx | hx
  · exact finitePrimeThetaCuspWeightedScreenError_le_major_of_nonneg A q j hx
  · have h := finitePrimeThetaCuspWeightedScreenError_le_major_of_nonneg
      A q j (neg_nonneg.mpr hx)
    simpa only [finitePrimeThetaCuspWeightedScreenError,
      finitePrimeThetaCuspWeightedScreenMajor, abs_neg,
      finitePrimeThetaCuspEvenScreen_neg, thetaCuspFullSource_neg,
      neg_sq] using h

theorem tendsto_exp_neg_natCast_sq_zero :
    Tendsto (fun j : ℕ ↦ Real.exp (-((j : ℝ) ^ 2))) atTop (𝓝 0) := by
  have hreal := tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero 0
    (by norm_num : (0 : ℝ) < 1)
  have hnat := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def, pow_zero, one_mul] using hnat

theorem finitePrimeThetaCuspEvenScreen_sub_full_abs_lt_accuracy
    (j : ℕ) {x : ℝ} (hx : |x| ≤ (j : ℝ)) :
    |finitePrimeThetaCuspEvenScreen j x - thetaCuspFullSource x| <
      Real.exp (-((j : ℝ) ^ 2)) := by
  let N := finitePrimeThetaCuspPositiveScreenIndex j
  have hxlo : -((j : ℕ) : ℝ) ≤ x := by linarith [neg_abs_le x]
  have hxhi : x ≤ ((j : ℕ) : ℝ) := (le_abs_self x).trans hx
  have hcutx : finitePrimeThetaCuspScreenCutoff j x = 1 :=
    finitePrimeThetaCuspScreenCutoff_eq_one j hxlo
  have hcutneg : finitePrimeThetaCuspScreenCutoff j (-x) = 1 :=
    finitePrimeThetaCuspScreenCutoff_eq_one j (by linarith)
  have hmemx : x ∈ Icc (-((j + 1 : ℕ) : ℝ)) ((j + 1 : ℕ) : ℝ) := by
    constructor <;> push_cast <;> linarith
  have hmemneg : -x ∈ Icc (-((j + 1 : ℕ) : ℝ)) ((j + 1 : ℕ) : ℝ) := by
    constructor <;> push_cast <;> linarith
  have haccx := finitePrimeThetaCuspPositiveScreenIndex_accuracy j
    0 (Nat.zero_le j) x hmemx
  have haccneg := finitePrimeThetaCuspPositiveScreenIndex_accuracy j
    0 (Nat.zero_le j) (-x) hmemneg
  simp only [iteratedDeriv_zero, thetaCuspFullSource_neg] at haccx haccneg
  have hid : finitePrimeThetaCuspEvenScreen j x - thetaCuspFullSource x =
      ((finitePrimeThetaCuspSource N x - thetaCuspFullSource x) +
        (finitePrimeThetaCuspSource N (-x) - thetaCuspFullSource x)) / 2 := by
    rw [finitePrimeThetaCuspEvenScreen, finitePrimeThetaCuspRightScreen,
      finitePrimeThetaCuspRightScreen, hcutx, hcutneg]
    ring
  rw [hid]
  calc
    |((finitePrimeThetaCuspSource N x - thetaCuspFullSource x) +
        (finitePrimeThetaCuspSource N (-x) - thetaCuspFullSource x)) / 2| ≤
      (|finitePrimeThetaCuspSource N x - thetaCuspFullSource x| +
        |finitePrimeThetaCuspSource N (-x) - thetaCuspFullSource x|) / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      gcongr
      exact abs_add_le _ _
    _ < Real.exp (-((j : ℝ) ^ 2)) := by linarith

theorem tendsto_finitePrimeThetaCuspWeightedScreenError_pointwise
    (A x : ℝ) :
    Tendsto (fun j : ℕ ↦ finitePrimeThetaCuspWeightedScreenError A j x)
      atTop (𝓝 0) := by
  have hnat : ∀ᶠ j : ℕ in atTop, |x| ≤ (j : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)) (eventually_ge_atTop |x|)
  have hnonneg : ∀ j : ℕ, 0 ≤ finitePrimeThetaCuspWeightedScreenError A j x :=
    fun j ↦ mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  have hupper : ∀ᶠ j : ℕ in atTop,
      finitePrimeThetaCuspWeightedScreenError A j x ≤
        Real.exp (A * |x|) * Real.exp (-((j : ℝ) ^ 2)) := by
    filter_upwards [hnat] with j hj
    unfold finitePrimeThetaCuspWeightedScreenError
    exact mul_le_mul_of_nonneg_left
      (finitePrimeThetaCuspEvenScreen_sub_full_abs_lt_accuracy j hj).le
      (Real.exp_pos _).le
  have henv : Tendsto
      (fun j : ℕ ↦ Real.exp (A * |x|) * Real.exp (-((j : ℝ) ^ 2)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_exp_neg_natCast_sq_zero.const_mul
      (Real.exp (A * |x|))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds henv (Eventually.of_forall hnonneg) hupper

/-- Every exponential-weighted `L¹` error of the selected positive even screens tends to zero. -/
theorem tendsto_integral_finitePrimeThetaCuspWeightedScreenError (A : ℝ) :
    Tendsto (fun j : ℕ ↦ ∫ x : ℝ,
      finitePrimeThetaCuspWeightedScreenError A j x) atTop (𝓝 0) := by
  obtain ⟨q : ℕ, hq⟩ := exists_nat_gt |A|
  have hq' : |A| < (q + 1 : ℕ) :=
    lt_trans hq (by exact_mod_cast Nat.lt_succ_self q)
  have hmeas : ∀ᶠ j : ℕ in atTop,
      AEStronglyMeasurable (finitePrimeThetaCuspWeightedScreenError A j) := by
    filter_upwards with j
    exact (((Real.continuous_exp.comp
      (continuous_const.mul continuous_abs))).mul
        ((continuous_finitePrimeThetaCuspEvenScreen j).sub
          contDiff_thetaCuspFullSource.continuous).abs).aestronglyMeasurable
  have hbound : ∀ᶠ j : ℕ in atTop, ∀ᵐ x : ℝ,
      ‖finitePrimeThetaCuspWeightedScreenError A j x‖ ≤
        finitePrimeThetaCuspWeightedScreenMajor A q x := by
    filter_upwards with j
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      exact mul_nonneg (Real.exp_pos _).le (abs_nonneg _))]
    exact finitePrimeThetaCuspWeightedScreenError_le_major A q j x
  have hlim : ∀ᵐ x : ℝ,
      Tendsto (fun j : ℕ ↦ finitePrimeThetaCuspWeightedScreenError A j x)
        atTop (𝓝 (0 : ℝ)) :=
    Eventually.of_forall (tendsto_finitePrimeThetaCuspWeightedScreenError_pointwise A)
  have h := tendsto_integral_filter_of_dominated_convergence
    (finitePrimeThetaCuspWeightedScreenMajor A q) hmeas hbound
    (integrable_finitePrimeThetaCuspWeightedScreenMajor A q hq') hlim
  simpa using h

end RHTower

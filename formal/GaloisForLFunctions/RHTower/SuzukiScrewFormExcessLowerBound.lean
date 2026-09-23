import GaloisForLFunctions.RHTower.SuzukiScrewTestRayEnergy

/-!
# The screw form is bounded below by the top excess, in the `L¹` normalisation

For a smooth zero-mean test `φ` supported in `[−a, a]`, every ray coefficient satisfies
`‖c_q‖ ≤ (e^{Θ|a|} + 1) ‖φ‖₁` as soon as every spectral point has `|Im z_q| ≤ Θ`, and the screw
form is `Σ'_q c̄_q c_q / z_q²`.  Since `Σ'_q ‖z_q‖⁻²` converges, the real part of the screw form is
at least `−(e^{Θ|a|} + 1)² ‖φ‖₁² Σ'_q ‖z_q‖⁻²`.  With `Θ` the top excess `⨆_q |Im z_q|` this is
unconditional: in the `L¹` normalisation the negative part of the screw form grows at most like
`e^{2 Θ_sup |a|}`, the upper half of the rate identity, whose lower half is the corpus's attained-top
negativity `≤ −c e^{2Θa}` for tests of polynomial `L¹` norm.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- `Σ'_q ‖z_q‖⁻²` over all Xi zero copies. -/
def xiSpectralInvSqSum : ℝ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)

/-- The top horizontal excess of the Xi zeros, `⨆_q |Im z_q| = ⨆_ρ |Re ρ − 1/2|`. -/
def xiTopExcess : ℝ := ⨆ q : XiZeroCopy, |(xiSpectralPoint q).im|

theorem abs_im_xiSpectralPoint_le_xiTopExcess (q : XiZeroCopy) :
    |(xiSpectralPoint q).im| ≤ xiTopExcess := by
  unfold xiTopExcess
  have hb : BddAbove (Set.range fun q : XiZeroCopy => |(xiSpectralPoint q).im|) :=
    ⟨1 / 2, by
      rintro _ ⟨q, rfl⟩
      exact (abs_xiSpectralPoint_im_lt_half q).le⟩
  exact le_ciSup hb q

theorem xiTopExcess_le_half : xiTopExcess ≤ 1 / 2 :=
  Real.iSup_le (fun q => (abs_xiSpectralPoint_im_lt_half q).le) (by norm_num)

theorem xiTopExcess_nonneg : 0 ≤ xiTopExcess :=
  Real.iSup_nonneg fun _ => abs_nonneg _

/-- Points of the support of a test satisfy `|u| ≤ |a|`. -/
theorem abs_le_abs_of_mem_support {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) {u : ℝ}
    (hu : (φ : ℝ → ℂ) u ≠ 0) : |u| ≤ |a| := by
  have hmem : u ∈ Icc (-a) a := φ.support_subset (by simpa [Function.mem_support] using hu)
  rw [mem_Icc] at hmem
  rw [abs_le]
  constructor <;> linarith [le_abs_self a, neg_abs_le a]

/-- Pointwise bound on the exponential slope with a general excess bound. -/
theorem norm_expSlope_test_le_of_im_le {a Θ : ℝ} (hΘ : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ)
    (φ : SuzukiSmoothZeroMeanTest a) (q : XiZeroCopy) (u : ℝ) :
    ‖(Complex.exp (-(I * xiSpectralPoint q * (u : ℂ))) - 1) * (φ : ℝ → ℂ) u‖
      ≤ (Real.exp (Θ * |a|) + 1) * ‖(φ : ℝ → ℂ) u‖ := by
  rcases eq_or_ne ((φ : ℝ → ℂ) u) 0 with h0 | h0
  · simp [h0]
  have hu := abs_le_abs_of_mem_support φ h0
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_one, Complex.norm_exp]
  have hre : (-(I * xiSpectralPoint q * (u : ℂ))).re = (xiSpectralPoint q).im * u := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  have hΘ0 : 0 ≤ Θ := le_trans (abs_nonneg _) (hΘ q)
  have : (xiSpectralPoint q).im * u ≤ Θ * |a| := by
    calc (xiSpectralPoint q).im * u ≤ |(xiSpectralPoint q).im * u| := le_abs_self _
      _ = |(xiSpectralPoint q).im| * |u| := abs_mul _ _
      _ ≤ Θ * |a| := mul_le_mul (hΘ q) hu (abs_nonneg _) hΘ0
  linarith [Real.exp_le_exp.mpr this]

/-- Pointwise bound on the reflected exponential slope with a general excess bound. -/
theorem norm_expSlopeBar_test_le_of_im_le {a Θ : ℝ}
    (hΘ : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ)
    (φ : SuzukiSmoothZeroMeanTest a) (q : XiZeroCopy) (t : ℝ) :
    ‖(Complex.exp (I * xiSpectralPoint q * (t : ℂ)) - 1) * (starRingEnd ℂ) ((φ : ℝ → ℂ) t)‖
      ≤ (Real.exp (Θ * |a|) + 1) * ‖(φ : ℝ → ℂ) t‖ := by
  rcases eq_or_ne ((φ : ℝ → ℂ) t) 0 with h0 | h0
  · simp [h0]
  have ht := abs_le_abs_of_mem_support φ h0
  rw [norm_mul, Complex.norm_conj]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_one, Complex.norm_exp]
  have hre : (I * xiSpectralPoint q * (t : ℂ)).re = -((xiSpectralPoint q).im * t) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  have hΘ0 : 0 ≤ Θ := le_trans (abs_nonneg _) (hΘ q)
  have : -((xiSpectralPoint q).im * t) ≤ Θ * |a| := by
    calc -((xiSpectralPoint q).im * t) ≤ |(xiSpectralPoint q).im * t| := neg_le_abs _
      _ = |(xiSpectralPoint q).im| * |t| := abs_mul _ _
      _ ≤ Θ * |a| := mul_le_mul (hΘ q) ht (abs_nonneg _) hΘ0
  linarith [Real.exp_le_exp.mpr this]

/-- `‖c_q‖ ≤ (e^{Θ|a|} + 1) ‖φ‖₁`. -/
theorem norm_suzukiTestRayCoef_le_of_im_le {a Θ : ℝ}
    (hΘ : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ)
    (φ : SuzukiSmoothZeroMeanTest a) (q : XiZeroCopy) :
    ‖suzukiTestRayCoef φ q‖ ≤ (Real.exp (Θ * |a|) + 1) * ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖ := by
  unfold suzukiTestRayCoef
  refine le_trans (norm_integral_le_integral_norm _) ?_
  rw [← integral_const_mul]
  refine integral_mono (integrable_expSlope_test φ q).norm
    ((integrable_suzukiSmoothZeroMeanTest φ).norm.const_mul _) ?_
  intro u
  exact norm_expSlope_test_le_of_im_le hΘ φ q u

/-- `‖c̄_q‖ ≤ (e^{Θ|a|} + 1) ‖φ‖₁`. -/
theorem norm_suzukiTestRayCoefBar_le_of_im_le {a Θ : ℝ}
    (hΘ : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ)
    (φ : SuzukiSmoothZeroMeanTest a) (q : XiZeroCopy) :
    ‖suzukiTestRayCoefBar φ q‖ ≤ (Real.exp (Θ * |a|) + 1) * ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖ := by
  unfold suzukiTestRayCoefBar
  refine le_trans (norm_integral_le_integral_norm _) ?_
  rw [← integral_const_mul]
  refine integral_mono (integrable_expSlopeBar_test φ q).norm
    ((integrable_suzukiSmoothZeroMeanTest φ).norm.const_mul _) ?_
  intro t
  exact norm_expSlopeBar_test_le_of_im_le hΘ φ q t

/-- Norm bound for one ray term of the screw form. -/
theorem norm_screwRayTerm_le_of_im_le {a Θ : ℝ}
    (hΘ : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ)
    (φ : SuzukiSmoothZeroMeanTest a) (q : XiZeroCopy) :
    ‖suzukiTestRayCoefBar φ q * suzukiTestRayCoef φ q / xiSpectralPoint q ^ (2 : ℕ)‖
      ≤ ((Real.exp (Θ * |a|) + 1) * ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖) ^ (2 : ℕ) *
          (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
  rw [norm_div, norm_mul, norm_pow]
  have h1 := norm_suzukiTestRayCoefBar_le_of_im_le hΘ φ q
  have h2 := norm_suzukiTestRayCoef_le_of_im_le hΘ φ q
  have hz : 0 < ‖xiSpectralPoint q‖ ^ (2 : ℕ) :=
    pow_pos (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)) 2
  rw [div_le_iff₀ hz]
  have hM0 : 0 ≤ (Real.exp (Θ * |a|) + 1) * ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖ := by
    have : 0 ≤ ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖ := integral_nonneg fun u => norm_nonneg _
    positivity
  calc ‖suzukiTestRayCoefBar φ q‖ * ‖suzukiTestRayCoef φ q‖
      ≤ ((Real.exp (Θ * |a|) + 1) * ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖) *
          ((Real.exp (Θ * |a|) + 1) * ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖) :=
        mul_le_mul h1 h2 (norm_nonneg _) hM0
    _ = ((Real.exp (Θ * |a|) + 1) * ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖) ^ (2 : ℕ) := by ring
    _ = ((Real.exp (Θ * |a|) + 1) * ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖) ^ (2 : ℕ) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) *
          ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
        rw [mul_assoc, one_div, inv_mul_cancel₀ hz.ne', mul_one]

/-- **Lower bound for the screw form by an excess bound.**  If every spectral point has
`|Im z_q| ≤ Θ`, then `Re Q(φ) ≥ −(e^{Θ|a|} + 1)² ‖φ‖₁² Σ'_q ‖z_q‖⁻²`. -/
theorem re_suzukiScrewSmoothForm_ge_of_im_le {a Θ : ℝ}
    (hΘ : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ) (φ : SuzukiSmoothZeroMeanTest a) :
    -(((Real.exp (Θ * |a|) + 1) * ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖) ^ (2 : ℕ) * xiSpectralInvSqSum)
      ≤ (suzukiScrewSmoothForm φ φ).re := by
  rw [suzukiScrewSmoothForm_eq_tsum]
  set M : ℝ := (Real.exp (Θ * |a|) + 1) * ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖ with hM
  set term : XiZeroCopy → ℂ := fun q =>
    suzukiTestRayCoefBar φ q * suzukiTestRayCoef φ q / xiSpectralPoint q ^ (2 : ℕ) with hterm
  have hbound : ∀ q, ‖term q‖ ≤ M ^ (2 : ℕ) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := fun q =>
    norm_screwRayTerm_le_of_im_le hΘ φ q
  have hg : Summable fun q : XiZeroCopy => M ^ (2 : ℕ) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) :=
    xiSpectralPoint_inv_sq_summable.mul_left _
  have hsum : Summable term := Summable.of_norm_bounded hg hbound
  rw [Complex.re_tsum hsum]
  have hre : Summable fun q => (term q).re :=
    (hsum.hasSum.mapL Complex.reCLM).summable
  have hle : ∀ q, -(M ^ (2 : ℕ) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))) ≤ (term q).re := by
    intro q
    have h1 := Complex.abs_re_le_norm (term q)
    have h2 := (abs_le.mp h1).1
    linarith [hbound q]
  have := Summable.tsum_le_tsum hle hg.neg hre
  rw [tsum_neg, tsum_mul_left] at this
  exact this

/-- **Unconditional lower bound with the top excess.**  For every smooth zero-mean test at aperture
`a`, `Re Q(φ) ≥ −(e^{Θ_sup |a|} + 1)² ‖φ‖₁² Σ'_q ‖z_q‖⁻²`: in the `L¹` normalisation the negative
part of the screw form grows at most at exponential rate `2 Θ_sup`. -/
theorem re_suzukiScrewSmoothForm_ge_topExcess {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) :
    -(((Real.exp (xiTopExcess * |a|) + 1) * ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖) ^ (2 : ℕ) * xiSpectralInvSqSum)
      ≤ (suzukiScrewSmoothForm φ φ).re :=
  re_suzukiScrewSmoothForm_ge_of_im_le abs_im_xiSpectralPoint_le_xiTopExcess φ

/-- The trivial rate: with `Θ = 1/2`, `Re Q(φ) ≥ −(e^{|a|/2} + 1)² ‖φ‖₁² Σ'_q ‖z_q‖⁻²`. -/
theorem re_suzukiScrewSmoothForm_ge_half {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) :
    -(((Real.exp (|a| / 2) + 1) * ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖) ^ (2 : ℕ) * xiSpectralInvSqSum)
      ≤ (suzukiScrewSmoothForm φ φ).re := by
  have := re_suzukiScrewSmoothForm_ge_of_im_le (Θ := 1 / 2)
    (fun q => (abs_xiSpectralPoint_im_lt_half q).le) φ
  rwa [show (1 / 2 : ℝ) * |a| = |a| / 2 by ring] at this

end

end RHTower

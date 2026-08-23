import GaloisForLFunctions.RHTower.SuzukiScrewLine
import GaloisForLFunctions.RHTower.SuzukiScrewSmoothTestCriterion

/-!
# The screw form of a smooth test as a ray energy

Suzuki's Hermitian form `⟨φ₁, φ₂⟩_{G_g} = ∫∫ G_g(t,u) φ₁(u) conj(φ₂(t))` is evaluated here on the
diagonal for a smooth compactly supported test of zero mean.  Feeding in the exponential zero
series for `G_g` and interchanging twice — once in `u`, once in `t` — turns the double integral
into the ray energy

```text
⟨φ, φ⟩_{G_g} = ∑_γ (∫ (e^{iγt} - 1) conj(φ(t)) dt) (∫ (e^{-iγu} - 1) φ(u) du) / γ².
```

The interchanges are justified by the strip bound `|Im γ| < 1/2`, which makes each exponential
factor bounded on the support of `φ`, together with inverse-square summability of the divisor.
Everything here is unconditional; the Riemann hypothesis enters only later, when the two ray
integrals are recognized as conjugates of one another.
-/

open Complex Filter Topology MeasureTheory Set

namespace RHTower
noncomputable section

/-- The `q`-th ray coefficient of a smooth zero-mean test against the screw kernel. -/
def suzukiTestRayCoef {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (q : XiZeroCopy) : ℂ :=
  ∫ u : ℝ, (Complex.exp (-(I * xiSpectralPoint q * (u : ℂ))) - 1) * φ u

/-- The reflected ray coefficient, paired with the conjugated test. -/
def suzukiTestRayCoefBar {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (q : XiZeroCopy) : ℂ :=
  ∫ t : ℝ, (Complex.exp (I * xiSpectralPoint q * (t : ℂ)) - 1) * (starRingEnd ℂ) (φ t)

theorem integrable_suzukiSmoothZeroMeanTest {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) :
    Integrable (fun u : ℝ => (φ : ℝ → ℂ) u) :=
  φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport

theorem norm_expSlope_test_le {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (q : XiZeroCopy)
    (u : ℝ) :
    ‖(Complex.exp (-(I * xiSpectralPoint q * (u : ℂ))) - 1) * (φ : ℝ → ℂ) u‖
      ≤ (Real.exp (|a| / 2) + 1) * ‖(φ : ℝ → ℂ) u‖ := by
  rcases eq_or_ne ((φ : ℝ → ℂ) u) 0 with h0 | h0
  · rw [h0]
    simp
  · have hmem : u ∈ Icc (-a) a := φ.support_subset (by simpa [Function.mem_support] using h0)
    have hu : |u| ≤ |a| := by
      rcases abs_le.mp (abs_le.mpr ⟨hmem.1, hmem.2⟩) with ⟨_, _⟩
      exact le_trans (abs_le.mpr ⟨hmem.1, hmem.2⟩) (le_abs_self a)
    have hneg : -(I * xiSpectralPoint q * (u : ℂ)) = I * xiSpectralPoint q * ((-u : ℝ) : ℂ) := by
      push_cast; ring
    have hb : ‖Complex.exp (-(I * xiSpectralPoint q * (u : ℂ)))‖ ≤ Real.exp (|a| / 2) := by
      rw [hneg]
      refine le_trans (norm_exp_I_xiSpectralPoint_mul_le (-u) q) ?_
      rw [abs_neg]
      exact Real.exp_le_exp.mpr (by linarith)
    rw [norm_mul]
    gcongr
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_one]
    linarith

theorem aestronglyMeasurable_expSlope_test {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a)
    (q : XiZeroCopy) :
    AEStronglyMeasurable
      (fun u : ℝ => (Complex.exp (-(I * xiSpectralPoint q * (u : ℂ))) - 1)
        * (φ : ℝ → ℂ) u) volume := by
  refine AEStronglyMeasurable.mul ?_ φ.continuous.aestronglyMeasurable
  refine Continuous.aestronglyMeasurable ?_
  exact (Complex.continuous_exp.comp
    (by continuity)).sub continuous_const

theorem integrable_expSlope_test {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (q : XiZeroCopy) :
    Integrable (fun u : ℝ => (Complex.exp (-(I * xiSpectralPoint q * (u : ℂ))) - 1)
      * (φ : ℝ → ℂ) u) :=
  Integrable.mono'
    ((integrable_suzukiSmoothZeroMeanTest φ).norm.const_mul (Real.exp (|a| / 2) + 1))
    (aestronglyMeasurable_expSlope_test φ q)
    (Filter.Eventually.of_forall (norm_expSlope_test_le φ q))

theorem norm_suzukiTestRayCoef_le {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (q : XiZeroCopy) :
    ‖suzukiTestRayCoef φ q‖
      ≤ (Real.exp (|a| / 2) + 1) * ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖ := by
  refine le_trans (norm_integral_le_integral_norm _) ?_
  refine le_trans (MeasureTheory.integral_mono (integrable_expSlope_test φ q).norm
    ((integrable_suzukiSmoothZeroMeanTest φ).norm.const_mul _)
    (norm_expSlope_test_le φ q)) ?_
  rw [MeasureTheory.integral_const_mul]

/-! ## The conjugated side -/

theorem norm_expSlopeBar_test_le {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (q : XiZeroCopy)
    (t : ℝ) :
    ‖(Complex.exp (I * xiSpectralPoint q * (t : ℂ)) - 1) * (starRingEnd ℂ) ((φ : ℝ → ℂ) t)‖
      ≤ (Real.exp (|a| / 2) + 1) * ‖(φ : ℝ → ℂ) t‖ := by
  rcases eq_or_ne ((φ : ℝ → ℂ) t) 0 with h0 | h0
  · rw [h0]
    simp
  · have hmem : t ∈ Icc (-a) a := φ.support_subset (by simpa [Function.mem_support] using h0)
    have ht : |t| ≤ |a| := le_trans (abs_le.mpr ⟨hmem.1, hmem.2⟩) (le_abs_self a)
    have hb : ‖Complex.exp (I * xiSpectralPoint q * (t : ℂ))‖ ≤ Real.exp (|a| / 2) :=
      le_trans (norm_exp_I_xiSpectralPoint_mul_le t q) (Real.exp_le_exp.mpr (by linarith))
    rw [norm_mul, RCLike.norm_conj]
    gcongr
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_one]
    linarith

theorem integrable_expSlopeBar_test {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (q : XiZeroCopy) :
    Integrable (fun t : ℝ => (Complex.exp (I * xiSpectralPoint q * (t : ℂ)) - 1)
      * (starRingEnd ℂ) ((φ : ℝ → ℂ) t)) := by
  refine Integrable.mono'
    ((integrable_suzukiSmoothZeroMeanTest φ).norm.const_mul (Real.exp (|a| / 2) + 1)) ?_
    (Filter.Eventually.of_forall (norm_expSlopeBar_test_le φ q))
  refine AEStronglyMeasurable.mul ?_ (Complex.continuous_conj.comp φ.continuous).aestronglyMeasurable
  exact ((Complex.continuous_exp.comp (by continuity)).sub continuous_const).aestronglyMeasurable

theorem norm_suzukiTestRayCoefBar_le {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (q : XiZeroCopy) :
    ‖suzukiTestRayCoefBar φ q‖
      ≤ (Real.exp (|a| / 2) + 1) * ∫ t : ℝ, ‖(φ : ℝ → ℂ) t‖ := by
  refine le_trans (norm_integral_le_integral_norm _) ?_
  refine le_trans (MeasureTheory.integral_mono (integrable_expSlopeBar_test φ q).norm
    ((integrable_suzukiSmoothZeroMeanTest φ).norm.const_mul _)
    (norm_expSlopeBar_test_le φ q)) ?_
  rw [MeasureTheory.integral_const_mul]

/-! ## The two Fubini steps -/

theorem integral_screwKernel_test {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (t : ℝ) :
    (∫ u : ℝ, suzukiScrewKernel t u * (φ : ℝ → ℂ) u)
      = ∑' q : XiZeroCopy,
        (Complex.exp (I * xiSpectralPoint q * (t : ℂ)) - 1) / xiSpectralPoint q ^ 2
          * suzukiTestRayCoef φ q := by
  have hsplit : ∀ (u : ℝ) (q : XiZeroCopy), suzukiScrewExpTerm t u q * (φ : ℝ → ℂ) u
      = ((Complex.exp (I * xiSpectralPoint q * (t : ℂ)) - 1) / xiSpectralPoint q ^ 2)
        * ((Complex.exp (-(I * xiSpectralPoint q * (u : ℂ))) - 1) * (φ : ℝ → ℂ) u) := by
    intro u q
    rw [suzukiScrewExpTerm]
    ring
  have hpt : ∀ u : ℝ, suzukiScrewKernel t u * (φ : ℝ → ℂ) u
      = ∑' q : XiZeroCopy, suzukiScrewExpTerm t u q * (φ : ℝ → ℂ) u := by
    intro u
    rw [suzukiScrewKernel_eq_tsum t u, tsum_mul_right]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have hint : ∀ q : XiZeroCopy,
      Integrable (fun u : ℝ => suzukiScrewExpTerm t u q * (φ : ℝ → ℂ) u) := by
    intro q
    refine ((integrable_expSlope_test φ q).const_mul
      ((Complex.exp (I * xiSpectralPoint q * (t : ℂ)) - 1) / xiSpectralPoint q ^ 2)).congr ?_
    filter_upwards with u
    exact (hsplit u q).symm
  have hbound : ∀ q : XiZeroCopy,
      (∫ u : ℝ, ‖suzukiScrewExpTerm t u q * (φ : ℝ → ℂ) u‖)
        ≤ ‖(Complex.exp (I * xiSpectralPoint q * (t : ℂ)) - 1) / xiSpectralPoint q ^ 2‖
          * ((Real.exp (|a| / 2) + 1) * ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖) := by
    intro q
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
      (fun u => by rw [hsplit u q]))]
    simp only [norm_mul]
    rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hmono : ∀ u : ℝ,
        ‖Complex.exp (-(I * xiSpectralPoint q * (u : ℂ))) - 1‖ * ‖(φ : ℝ → ℂ) u‖
          ≤ (Real.exp (|a| / 2) + 1) * ‖(φ : ℝ → ℂ) u‖ := by
      intro u
      have h := norm_expSlope_test_le φ q u
      rwa [norm_mul] at h
    refine le_trans (MeasureTheory.integral_mono ?_ ?_ hmono) ?_
    · refine (integrable_expSlope_test φ q).norm.congr (Filter.Eventually.of_forall fun u => ?_)
      exact norm_mul _ _
    · exact (integrable_suzukiSmoothZeroMeanTest φ).norm.const_mul _
    · rw [MeasureTheory.integral_const_mul]
  have hsum : Summable fun q : XiZeroCopy =>
      ∫ u : ℝ, ‖suzukiScrewExpTerm t u q * (φ : ℝ → ℂ) u‖ := by
    refine Summable.of_nonneg_of_le (fun q => MeasureTheory.integral_nonneg fun u => norm_nonneg _)
      hbound ?_
    refine Summable.mul_right _ ?_
    refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
      (xiSpectralPoint_inv_sq_summable.mul_left (Real.exp (|t| / 2) + 1))
    have hnum : ‖Complex.exp (I * xiSpectralPoint q * (t : ℂ)) - 1‖
        ≤ Real.exp (|t| / 2) + 1 := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [norm_one]
      linarith [norm_exp_I_xiSpectralPoint_mul_le t q]
    have hden : (0 : ℝ) < ‖xiSpectralPoint q‖ ^ 2 :=
      pow_pos (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)) 2
    rw [norm_div, norm_pow, mul_one_div]
    gcongr
  rw [← MeasureTheory.integral_tsum_of_summable_integral_norm hint hsum]
  refine tsum_congr fun q => ?_
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => hsplit u q)),
    MeasureTheory.integral_const_mul, suzukiTestRayCoef]


/-- **The screw form of a smooth zero-mean test is its ray energy.**  Unconditional. -/
theorem suzukiScrewSmoothForm_eq_tsum {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) :
    suzukiScrewSmoothForm φ φ
      = ∑' q : XiZeroCopy,
        suzukiTestRayCoefBar φ q * suzukiTestRayCoef φ q / xiSpectralPoint q ^ 2 := by
  rw [suzukiScrewSmoothForm]
  have hinner : ∀ t : ℝ,
      (∫ u : ℝ, suzukiScrewKernel t u * (φ : ℝ → ℂ) u * (starRingEnd ℂ) ((φ : ℝ → ℂ) t))
        = ∑' q : XiZeroCopy,
          (Complex.exp (I * xiSpectralPoint q * (t : ℂ)) - 1) * (starRingEnd ℂ) ((φ : ℝ → ℂ) t)
            * (suzukiTestRayCoef φ q / xiSpectralPoint q ^ 2) := by
    intro t
    rw [MeasureTheory.integral_mul_const, integral_screwKernel_test φ t, ← tsum_mul_right]
    refine tsum_congr fun q => ?_
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hinner)]
  have hint : ∀ q : XiZeroCopy, Integrable (fun t : ℝ =>
      (Complex.exp (I * xiSpectralPoint q * (t : ℂ)) - 1) * (starRingEnd ℂ) ((φ : ℝ → ℂ) t)
        * (suzukiTestRayCoef φ q / xiSpectralPoint q ^ 2)) :=
    fun q => (integrable_expSlopeBar_test φ q).mul_const _
  have hsum : Summable fun q : XiZeroCopy => ∫ t : ℝ,
      ‖(Complex.exp (I * xiSpectralPoint q * (t : ℂ)) - 1) * (starRingEnd ℂ) ((φ : ℝ → ℂ) t)
        * (suzukiTestRayCoef φ q / xiSpectralPoint q ^ 2)‖ := by
    set Mφ : ℝ := (Real.exp (|a| / 2) + 1) * ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖ with hM
    have hMnn : 0 ≤ Mφ := by
      refine mul_nonneg (by positivity) (MeasureTheory.integral_nonneg fun u => norm_nonneg _)
    refine Summable.of_nonneg_of_le
      (fun q => MeasureTheory.integral_nonneg fun t => norm_nonneg _) (fun q => ?_)
      ((xiSpectralPoint_inv_sq_summable.mul_left (Mφ * Mφ)))
    have hbnd : ∀ t : ℝ,
        ‖(Complex.exp (I * xiSpectralPoint q * (t : ℂ)) - 1) * (starRingEnd ℂ) ((φ : ℝ → ℂ) t)
          * (suzukiTestRayCoef φ q / xiSpectralPoint q ^ 2)‖
          ≤ ((Real.exp (|a| / 2) + 1) * ‖(φ : ℝ → ℂ) t‖)
            * (Mφ * (1 / ‖xiSpectralPoint q‖ ^ 2)) := by
      intro t
      rw [norm_mul, norm_div, norm_pow, mul_one_div]
      gcongr
      · exact norm_expSlopeBar_test_le φ q t
      · exact norm_suzukiTestRayCoef_le φ q
    refine le_trans (MeasureTheory.integral_mono (hint q).norm ?_ hbnd) ?_
    · exact (((integrable_suzukiSmoothZeroMeanTest φ).norm.const_mul
        (Real.exp (|a| / 2) + 1)).mul_const _)
    · refine le_of_eq ?_
      rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul, hM]
      ring
  rw [← MeasureTheory.integral_tsum_of_summable_integral_norm hint hsum]
  refine tsum_congr fun q => ?_
  rw [MeasureTheory.integral_mul_const, suzukiTestRayCoefBar]
  ring


end
end RHTower

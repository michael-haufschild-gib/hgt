import GaloisForLFunctions.RHTower.PaperThetaUniformCutControl

/-! # A common spatial control for an entire native spectral strip

The real part of the spectral parameter costs only a scalar factor. The same
bounded monotone spatial function controls all cut modes in a horizontal
strip. This permits summation before native BV and arithmetic admission.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex

namespace RHTower.PaperThetaEndpoint
open ThetaFiniteTransport HedenmalmQuantile

def stripTailControl (B x : ℝ) : ℝ :=
  ∫ h in Ioi (0 : ℝ), sourceRatio h x * Real.exp (B*h)

theorem stripTailControl_nonneg (B x : ℝ) : 0 ≤ stripTailControl B x :=
  integral_nonneg fun h => mul_nonneg (sourceRatio_pos h x).le (Real.exp_pos _).le

theorem stripTailControl_antitone (B : ℝ) : Antitone (stripTailControl B) := by
  intro x y hxy
  apply setIntegral_mono_on (integrable_sourceRatio_tilt B y).integrableOn
    (integrable_sourceRatio_tilt B x).integrableOn measurableSet_Ioi
  intro h hh
  exact mul_le_mul_of_nonneg_right (sourceRatio_antitone_all ⟨h, hh.le⟩ hxy)
    (Real.exp_pos _).le

theorem stripTailControl_mono {b B : ℝ} (hb : b ≤ B) (x : ℝ) :
    stripTailControl b x ≤ stripTailControl B x := by
  apply setIntegral_mono_on (integrable_sourceRatio_tilt b x).integrableOn
    (integrable_sourceRatio_tilt B x).integrableOn measurableSet_Ioi
  intro h hh
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hb hh.le)) (sourceRatio_pos h x).le

theorem stripTailControl_difference_mono {b B x y : ℝ} (hb : b ≤ B) (hxy : x ≤ y) :
    stripTailControl b x-stripTailControl b y ≤
      stripTailControl B x-stripTailControl B y := by
  unfold stripTailControl
  rw [← integral_sub (integrable_sourceRatio_tilt b x).integrableOn
    (integrable_sourceRatio_tilt b y).integrableOn,
    ← integral_sub (integrable_sourceRatio_tilt B x).integrableOn
      (integrable_sourceRatio_tilt B y).integrableOn]
  apply setIntegral_mono_on
    ((integrable_sourceRatio_tilt b x).sub (integrable_sourceRatio_tilt b y)).integrableOn
    ((integrable_sourceRatio_tilt B x).sub (integrable_sourceRatio_tilt B y)).integrableOn
    measurableSet_Ioi
  intro h hh
  simp only [Pi.sub_apply]
  rw [← sub_mul, ← sub_mul]
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hb hh.le))
    (sub_nonneg.mpr (sourceRatio_antitone_all ⟨h, hh.le⟩ hxy))

theorem flatQuotient_add_one_strip {z : ℂ} {B : ℝ} (hz : -z.im ≤ B) (x : ℝ) :
    ‖flatQuotient z x+1‖ ≤ ‖z‖ * stripTailControl B x := by
  rw [flatQuotient_eq_sourceRatio_integral, norm_mul, norm_neg, norm_mul, norm_I, one_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
  calc
    _ ≤ ∫ h in Ioi (0 : ℝ), ‖(sourceRatio h x : ℂ)*sourceChar z h‖ :=
      norm_integral_le_integral_norm _
    _ = stripTailControl (-z.im) x := by
      simp only [norm_sourceRatio_character, stripTailControl]
    _ ≤ stripTailControl B x := stripTailControl_mono hz x

theorem flatQuotient_increment_strip {z : ℂ} {B x y : ℝ}
    (hz : -z.im ≤ B) (hxy : x ≤ y) :
    ‖flatQuotient z y-flatQuotient z x‖ ≤
      ‖z‖ * (stripTailControl B x-stripTailControl B y) := by
  have h := flatQuotient_increment_budget z x y
  rw [abs_of_nonpos (sub_nonpos.mpr (quotientVariationBudget_antitone z hxy)), neg_sub] at h
  calc
    _ ≤ quotientVariationBudget z x-quotientVariationBudget z y := h
    _ = ‖z‖ * (stripTailControl (-z.im) x-stripTailControl (-z.im) y) := by
      simp only [quotientVariationBudget, stripTailControl, mul_sub]
    _ ≤ _ := mul_le_mul_of_nonneg_left (stripTailControl_difference_mono hz hxy) (norm_nonneg z)

def stripCutControl (B x : ℝ) : ℝ :=
  if x < 0 then stripTailControl B (-x)
  else 4*stripTailControl B 0-stripTailControl B x

theorem stripCutControl_bounds (B x : ℝ) :
    0 ≤ stripCutControl B x ∧ stripCutControl B x ≤ 4*stripTailControl B 0 := by
  have h0 := stripTailControl_nonneg B 0
  have hx := stripTailControl_nonneg B x
  have hn := stripTailControl_nonneg B (-x)
  unfold stripCutControl
  split_ifs with h
  · have hm := stripTailControl_antitone B (show 0 ≤ -x by linarith)
    constructor <;> linarith
  · have hm := stripTailControl_antitone B (le_of_not_gt h)
    constructor <;> linarith

theorem monotone_stripCutControl (B : ℝ) : Monotone (stripCutControl B) := by
  intro x y hxy
  by_cases hy : y < 0
  · have hx := lt_of_le_of_lt hxy hy
    simp only [stripCutControl, if_pos hx, if_pos hy]
    exact stripTailControl_antitone B (neg_le_neg hxy)
  by_cases hx : x < 0
  · have hl := stripTailControl_antitone B (show 0 ≤ -x by linarith)
    have hr := stripTailControl_antitone B (le_of_not_gt hy)
    have h0 := stripTailControl_nonneg B 0
    simp only [stripCutControl, if_pos hx, if_neg hy]
    linarith
  · simp only [stripCutControl, if_neg hx, if_neg hy]
    exact sub_le_sub_left (stripTailControl_antitone B hxy) _

theorem boundedVariationOn_stripCutControl (B : ℝ) :
    BoundedVariationOn (stripCutControl B) univ := by
  apply ((monotone_stripCutControl B).monotoneOn univ).boundedVariationOn
  intro x _
  rw [abs_of_nonneg (stripCutControl_bounds B x).1]
  exact (stripCutControl_bounds B x).2

theorem cutQuotient_add_one_strip {z : ℂ} {B : ℝ} (hz : |z.im| ≤ B) (x : ℝ) :
    ‖cutQuotient z 0 x+1‖ ≤ ‖z‖*stripTailControl B 0 := by
  have hp : -z.im ≤ B := (neg_le_abs z.im).trans hz
  have hn : -(-z).im ≤ B := by simpa using (le_abs_self z.im).trans hz
  by_cases hx : x < 0
  · rw [cutQuotient_left z hx, leftQuotient]
    exact (flatQuotient_add_one_strip hn (-x)).trans (by
      rw [norm_neg]
      exact mul_le_mul_of_nonneg_left
        (stripTailControl_antitone B (show 0 ≤ -x by linarith)) (norm_nonneg z))
  · rw [cutQuotient_right z (le_of_not_gt hx)]
    exact (flatQuotient_add_one_strip hp x).trans
      (mul_le_mul_of_nonneg_left (stripTailControl_antitone B (le_of_not_gt hx)) (norm_nonneg z))

theorem cutQuotient_increment_strip {z : ℂ} {B x y : ℝ}
    (hz : |z.im| ≤ B) (hxy : x ≤ y) :
    ‖cutQuotient z 0 y-cutQuotient z 0 x‖ ≤
      ‖z‖*(stripCutControl B y-stripCutControl B x) := by
  have hp : -z.im ≤ B := (neg_le_abs z.im).trans hz
  have hn : -(-z).im ≤ B := by simpa using (le_abs_self z.im).trans hz
  by_cases hy : y < 0
  · have hx := lt_of_le_of_lt hxy hy
    simpa only [cutQuotient, leftQuotient, stripCutControl, if_pos hx, if_pos hy,
      norm_neg, norm_sub_rev] using flatQuotient_increment_strip hn (neg_le_neg hxy)
  by_cases hx : x < 0
  · have hl := flatQuotient_add_one_strip hn (-x)
    rw [norm_neg] at hl
    have hr := flatQuotient_add_one_strip hp y
    have hla := mul_le_mul_of_nonneg_left
      (stripTailControl_antitone B (show 0 ≤ -x by linarith)) (norm_nonneg z)
    have hra := mul_le_mul_of_nonneg_left
      (stripTailControl_antitone B (le_of_not_gt hy)) (norm_nonneg z)
    have ht := norm_sub_le (flatQuotient z y+1) (flatQuotient (-z) (-x)+1)
    rw [add_sub_add_right_eq_sub] at ht
    simp only [cutQuotient, leftQuotient, stripCutControl, if_pos hx, if_neg hy]
    nlinarith
  · have h := flatQuotient_increment_strip hp hxy
    simp only [cutQuotient, stripCutControl, if_neg hx, if_neg hy]
    convert h using 1
    ring

theorem cutQuotient_difference_strip {z : ℂ} {B : ℝ}
    (hz : |z.im| ≤ B) (x y : ℝ) :
    ‖cutQuotient z 0 y-cutQuotient z 0 x‖ ≤
      ‖z‖*|stripCutControl B y-stripCutControl B x| := by
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonneg (sub_nonneg.mpr (monotone_stripCutControl B hxy))]
    exact cutQuotient_increment_strip hz hxy
  · rw [norm_sub_rev, abs_of_nonpos (sub_nonpos.mpr (monotone_stripCutControl B hyx)), neg_sub]
    exact cutQuotient_increment_strip hz hyx

end RHTower.PaperThetaEndpoint

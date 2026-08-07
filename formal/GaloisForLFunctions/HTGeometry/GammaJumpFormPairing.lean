import GaloisForLFunctions.HTGeometry.GammaTransportKernel
import GaloisForLFunctions.HTGeometry.MonotoneTranslationModulus

/-!
# The jump-form pairing of the Gamma transport operator

Tested against a weight, the transport operator becomes the symmetric bilinear form

`E(F,w) = ½ ∫∫ k(|L−M|) [F(L) − F(M)] [w(L) − w(M)] dM dL`.

Sliced by the shift `s = M − L`, the inner integral is controlled by the `L¹` modulus of `w`, and
the outer integral by the first moment of the kernel.  Both inputs are already available: the
modulus is `MonotoneTranslationModulus.integral_abs_translate_sub_le_variation` and the moment is
`integrableOn_id_mul_gammaTransportKernel_Ioi_zero`.  Together they make the pairing absolutely
convergent for a bounded profile against a monotone weight, with no regularity on either beyond
boundedness and monotonicity.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- The integrand of the jump form at shift `s`. -/
noncomputable def jumpFormIntegrand (F w : ℝ → ℝ) (s L : ℝ) : ℝ :=
  (F L - F (L + s)) * (w L - w (L + s))

/-- **The profile factor is bounded.**  A bounded profile contributes at most `2M` to each slice. -/
theorem abs_jumpFormIntegrand_le {F w : ℝ → ℝ} {MF : ℝ} (hF : ∀ x, |F x| ≤ MF) (s L : ℝ) :
    |jumpFormIntegrand F w s L| ≤ 2 * MF * |w (L + s) - w L| := by
  unfold jumpFormIntegrand
  rw [abs_mul]
  have h1 : |F L - F (L + s)| ≤ 2 * MF := by
    have ha := abs_le.mp (hF L)
    have hb := abs_le.mp (hF (L + s))
    rw [abs_le]
    constructor <;> linarith
  rw [abs_sub_comm (w L) (w (L + s))]
  exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)

/-- The slice integrand is interval integrable, by domination against the weight's increment. -/
theorem intervalIntegrable_abs_jumpFormIntegrand {F w : ℝ → ℝ} {MF : ℝ}
    (hFc : Continuous F) (hw : Monotone w) (hF : ∀ x, |F x| ≤ MF) (s a b : ℝ) :
    IntervalIntegrable (fun L => |jumpFormIntegrand F w s L|) volume a b := by
  have hdw : IntervalIntegrable (fun L => |w (L + s) - w L|) volume a b :=
    (MonotoneTranslation.intervalIntegrable_translate_sub hw s a b).abs
  have hmeas : Measurable fun L => |jumpFormIntegrand F w s L| := by
    unfold jumpFormIntegrand
    exact (((hFc.measurable).sub
      ((hFc.comp (continuous_id.add continuous_const)).measurable)).mul
      (hw.measurable.sub ((monotone_comp_add_right hw s).measurable))).abs
  refine IntervalIntegrable.mono_fun (hdw.const_mul (2 * MF)) hmeas.aestronglyMeasurable ?_
  filter_upwards with L
  have hpt := abs_jumpFormIntegrand_le (w := w) hF s L
  have hnn : 0 ≤ 2 * MF * |w (L + s) - w L| := le_trans (abs_nonneg _) hpt
  simp only [Real.norm_eq_abs, abs_abs, abs_of_nonneg hnn]
  exact hpt

/-- **The slice bound.**  For a bounded profile against a monotone weight, the jump-form slice at
shift `s` is bounded by `2M · V · s`: linear in the shift, which is what the kernel's finite first
moment consumes. -/
theorem integral_abs_jumpFormIntegrand_le {F w : ℝ → ℝ} {MF V a b s : ℝ}
    (hFc : Continuous F) (hw : Monotone w) (hF : ∀ x, |F x| ≤ MF) (hMF : 0 ≤ MF)
    (hs : 0 ≤ s) (hV : w (b + s) - w a ≤ V) (hab : a ≤ b) :
    (∫ L in a..b, |jumpFormIntegrand F w s L|) ≤ 2 * MF * (V * s) := by
  have hdw : IntervalIntegrable (fun L => |w (L + s) - w L|) volume a b :=
    (MonotoneTranslation.intervalIntegrable_translate_sub hw s a b).abs
  have hmono : (∫ L in a..b, |jumpFormIntegrand F w s L|)
      ≤ ∫ L in a..b, 2 * MF * |w (L + s) - w L| :=
    intervalIntegral.integral_mono_on hab
      (intervalIntegrable_abs_jumpFormIntegrand hFc hw hF s a b)
      (hdw.const_mul (2 * MF)) fun L _ => abs_jumpFormIntegrand_le (w := w) hF s L
  have hval : (∫ L in a..b, 2 * MF * |w (L + s) - w L|)
      = 2 * MF * ∫ L in a..b, |w (L + s) - w L| := intervalIntegral.integral_const_mul _ _
  have hL1 : (∫ L in a..b, |w (L + s) - w L|) ≤ V * s :=
    integral_abs_translate_sub_le_variation hw (a := a) (b := b) hs hV
  rw [hval] at hmono
  nlinarith [hmono, hL1, hMF]

/-- **The outer integral converges.**  Pairing the slice bound with the kernel's finite first
moment shows the whole jump form is absolutely convergent: the dominating function
`s ↦ 2M·V·s·k(s)` is integrable on the positive ray. -/
theorem integrableOn_jumpFormDominant (MF V : ℝ) :
    IntegrableOn (fun s => 2 * MF * V * (s * gammaTransportKernel s)) (Ioi 0) :=
  integrableOn_id_mul_gammaTransportKernel_Ioi_zero.const_mul (2 * MF * V)

/-! ## Weights of bounded variation

The truncated weights `w_M(L) = 1_{[L₀,M]}(L) L^{−3/2}` that test the source equation are not
monotone — an indicator times a decreasing power is a *difference* of two monotone pieces.  The
linear `L¹` modulus survives the splitting, with the two variations adding.
-/

/-- **A difference of monotone weights keeps a linear `L¹` modulus.**  This is what lets the
truncated test weights be used: they are differences of monotone pieces, not monotone. -/
theorem integral_abs_translate_sub_le_variation_sub {w₁ w₂ : ℝ → ℝ}
    (h1 : Monotone w₁) (h2 : Monotone w₂) {a b s V₁ V₂ : ℝ}
    (hs : 0 ≤ s) (hV1 : w₁ (b + s) - w₁ a ≤ V₁) (hV2 : w₂ (b + s) - w₂ a ≤ V₂) (hab : a ≤ b) :
    (∫ L in a..b, |(w₁ (L + s) - w₂ (L + s)) - (w₁ L - w₂ L)|) ≤ (V₁ + V₂) * s := by
  have hi1 : IntervalIntegrable (fun L => |w₁ (L + s) - w₁ L|) volume a b :=
    (MonotoneTranslation.intervalIntegrable_translate_sub h1 s a b).abs
  have hi2 : IntervalIntegrable (fun L => |w₂ (L + s) - w₂ L|) volume a b :=
    (MonotoneTranslation.intervalIntegrable_translate_sub h2 s a b).abs
  have hpt : ∀ L : ℝ, |(w₁ (L + s) - w₂ (L + s)) - (w₁ L - w₂ L)|
      ≤ |w₁ (L + s) - w₁ L| + |w₂ (L + s) - w₂ L| := by
    intro L
    have hrw : (w₁ (L + s) - w₂ (L + s)) - (w₁ L - w₂ L)
        = (w₁ (L + s) - w₁ L) + (-(w₂ (L + s) - w₂ L)) := by ring
    rw [hrw]
    calc |(w₁ (L + s) - w₁ L) + (-(w₂ (L + s) - w₂ L))|
        ≤ |w₁ (L + s) - w₁ L| + |-(w₂ (L + s) - w₂ L)| := abs_add_le _ _
      _ = |w₁ (L + s) - w₁ L| + |w₂ (L + s) - w₂ L| := by rw [abs_neg]
  have hmeas : Measurable fun L => |(w₁ (L + s) - w₂ (L + s)) - (w₁ L - w₂ L)| :=
    ((((monotone_comp_add_right h1 s).measurable).sub
      ((monotone_comp_add_right h2 s).measurable)).sub
      (h1.measurable.sub h2.measurable)).abs
  have hlhs : IntervalIntegrable
      (fun L => |(w₁ (L + s) - w₂ (L + s)) - (w₁ L - w₂ L)|) volume a b := by
    refine IntervalIntegrable.mono_fun (hi1.add hi2) hmeas.aestronglyMeasurable ?_
    filter_upwards with L
    have hnn : 0 ≤ |w₁ (L + s) - w₁ L| + |w₂ (L + s) - w₂ L| := by positivity
    simp only [Real.norm_eq_abs, abs_abs, abs_of_nonneg hnn]
    exact hpt L
  have hmono : (∫ L in a..b, |(w₁ (L + s) - w₂ (L + s)) - (w₁ L - w₂ L)|)
      ≤ ∫ L in a..b, (|w₁ (L + s) - w₁ L| + |w₂ (L + s) - w₂ L|) :=
    intervalIntegral.integral_mono_on hab hlhs (hi1.add hi2) fun L _ => hpt L
  have hsplit : (∫ L in a..b, (|w₁ (L + s) - w₁ L| + |w₂ (L + s) - w₂ L|))
      = (∫ L in a..b, |w₁ (L + s) - w₁ L|) + ∫ L in a..b, |w₂ (L + s) - w₂ L| :=
    intervalIntegral.integral_add hi1 hi2
  have hb1 : (∫ L in a..b, |w₁ (L + s) - w₁ L|) ≤ V₁ * s :=
    integral_abs_translate_sub_le_variation h1 (a := a) (b := b) hs hV1
  have hb2 : (∫ L in a..b, |w₂ (L + s) - w₂ L|) ≤ V₂ * s :=
    integral_abs_translate_sub_le_variation h2 (a := a) (b := b) hs hV2
  rw [hsplit] at hmono
  nlinarith [hmono, hb1, hb2]

/-- **The slice bound for a bounded-variation weight.**  The jump form pairs a bounded profile
against a difference of monotone weights with a modulus still linear in the shift, the two
variations adding.  This is the form the truncated test weights of `(10)` require. -/
theorem integral_abs_jumpFormIntegrand_le_bv {F w₁ w₂ : ℝ → ℝ} {MF V₁ V₂ a b s : ℝ}
    (hFc : Continuous F) (h1 : Monotone w₁) (h2 : Monotone w₂)
    (hF : ∀ x, |F x| ≤ MF) (hMF : 0 ≤ MF) (hs : 0 ≤ s)
    (hV1 : w₁ (b + s) - w₁ a ≤ V₁) (hV2 : w₂ (b + s) - w₂ a ≤ V₂) (hab : a ≤ b) :
    (∫ L in a..b, |jumpFormIntegrand F (fun x => w₁ x - w₂ x) s L|)
      ≤ 2 * MF * ((V₁ + V₂) * s) := by
  set w : ℝ → ℝ := fun x => w₁ x - w₂ x with hwdef
  have hmeasw : Measurable fun L => |w (L + s) - w L| :=
    ((((monotone_comp_add_right h1 s).measurable).sub
      ((monotone_comp_add_right h2 s).measurable)).sub
      (h1.measurable.sub h2.measurable)).abs
  have hi1 : IntervalIntegrable (fun L => |w₁ (L + s) - w₁ L|) volume a b :=
    (MonotoneTranslation.intervalIntegrable_translate_sub h1 s a b).abs
  have hi2 : IntervalIntegrable (fun L => |w₂ (L + s) - w₂ L|) volume a b :=
    (MonotoneTranslation.intervalIntegrable_translate_sub h2 s a b).abs
  have hptw : ∀ L : ℝ, |w (L + s) - w L|
      ≤ |w₁ (L + s) - w₁ L| + |w₂ (L + s) - w₂ L| := by
    intro L
    have hrw : w (L + s) - w L
        = (w₁ (L + s) - w₁ L) + (-(w₂ (L + s) - w₂ L)) := by
      simp only [hwdef]; ring
    rw [hrw]
    calc |(w₁ (L + s) - w₁ L) + (-(w₂ (L + s) - w₂ L))|
        ≤ |w₁ (L + s) - w₁ L| + |-(w₂ (L + s) - w₂ L)| := abs_add_le _ _
      _ = |w₁ (L + s) - w₁ L| + |w₂ (L + s) - w₂ L| := by rw [abs_neg]
  have hiw : IntervalIntegrable (fun L => |w (L + s) - w L|) volume a b := by
    refine IntervalIntegrable.mono_fun (hi1.add hi2) hmeasw.aestronglyMeasurable ?_
    filter_upwards with L
    have hnn : 0 ≤ |w₁ (L + s) - w₁ L| + |w₂ (L + s) - w₂ L| := by positivity
    simp only [Real.norm_eq_abs, abs_abs, abs_of_nonneg hnn]
    exact hptw L
  have hmeas : Measurable fun L => |jumpFormIntegrand F w s L| := by
    unfold jumpFormIntegrand
    exact (((hFc.measurable).sub
      ((hFc.comp (continuous_id.add continuous_const)).measurable)).mul
      (((h1.measurable.sub h2.measurable)).sub
        (((monotone_comp_add_right h1 s).measurable).sub
          ((monotone_comp_add_right h2 s).measurable)))).abs
  have hlhs : IntervalIntegrable (fun L => |jumpFormIntegrand F w s L|) volume a b := by
    refine IntervalIntegrable.mono_fun (hiw.const_mul (2 * MF))
      hmeas.aestronglyMeasurable ?_
    filter_upwards with L
    have hpt := abs_jumpFormIntegrand_le (w := w) hF s L
    have hnn : 0 ≤ 2 * MF * |w (L + s) - w L| := le_trans (abs_nonneg _) hpt
    simp only [Real.norm_eq_abs, abs_abs, abs_of_nonneg hnn]
    exact hpt
  have hmono : (∫ L in a..b, |jumpFormIntegrand F w s L|)
      ≤ ∫ L in a..b, 2 * MF * |w (L + s) - w L| :=
    intervalIntegral.integral_mono_on hab hlhs (hiw.const_mul (2 * MF))
      fun L _ => abs_jumpFormIntegrand_le (w := w) hF s L
  have hval : (∫ L in a..b, 2 * MF * |w (L + s) - w L|)
      = 2 * MF * ∫ L in a..b, |w (L + s) - w L| := intervalIntegral.integral_const_mul _ _
  have hbv : (∫ L in a..b, |w (L + s) - w L|) ≤ (V₁ + V₂) * s :=
    integral_abs_translate_sub_le_variation_sub h1 h2 hs hV1 hV2 hab
  rw [hval] at hmono
  nlinarith [hmono, hbv, hMF]

end GaloisForLFunctions.HTGeometry

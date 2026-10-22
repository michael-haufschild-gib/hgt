import GaloisForLFunctions.RHTower.XiGuinandWeilSpectralRectangle
import GaloisForLFunctions.RHTower.CCM.CCMRectangularAutocorrelation
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Sharp rectangular Fourier evaluation of the Guinand--Weil prime edge

This module proves Fourier inversion directly for the half-open two-edge rectangular profile.
The required convolution theorem is established under `L1` hypotheses, so no artificial
continuity or smoothing assumption is imposed on the sharp rectangles.  The final theorem
identifies the Euler-line von Mangoldt integral with the existing finite critical-weight
autocorrelation sum.
-/

open MeasureTheory Convolution
open scoped Convolution RealInnerProductSpace

noncomputable section

namespace Real

open FourierTransform ContinuousLinearMap

theorem fourier_bilin_convolution_eq_integral_L1
    {F₁ F₂ F₃ : Type*}
    [NormedAddCommGroup F₁] [NormedAddCommGroup F₂] [NormedAddCommGroup F₃]
    [NormedSpace ℂ F₁] [NormedSpace ℂ F₂] [NormedSpace ℂ F₃]
    (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃) {f₁ : ℝ → F₁} {f₂ : ℝ → F₂}
    (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) (ξ : ℝ) :
    𝓕 (f₁ ⋆[B] f₂) ξ =
      ∫ y, ∫ x, 𝐞 (-inner ℝ (y + x) ξ) • B (f₁ x) (f₂ y) := by
  calc
    _ = 𝓕 (f₂ ⋆[B.flip] f₁) ξ := by
      rw [convolution_flip]
    _ = ∫ x, 𝐞 (-inner ℝ x ξ) • ∫ y, B (f₁ (x - y)) (f₂ y) := by rfl
    _ = ∫ x, ∫ y, 𝐞 (-inner ℝ x ξ) • B (f₁ (x - y)) (f₂ y) := by
      congr
      ext x
      simp_rw [Circle.smul_def, integral_smul]
    _ = ∫ y, ∫ x, 𝐞 (-inner ℝ x ξ) • B (f₁ (x - y)) (f₂ y) := by
      refine integral_integral_swap ?_
      have hconv : Integrable
          (fun p : ℝ × ℝ => B (f₁ (p.1 - p.2)) (f₂ p.2)) := by
        simpa only [flip_apply] using!
          hf₂.convolution_integrand B.flip hf₁
      have hchar : AEStronglyMeasurable
          (fun p : ℝ × ℝ => ((𝐞 (-inner ℝ p.1 ξ) : Circle) : ℂ)) := by
        fun_prop
      have hbound : ∀ᵐ p : ℝ × ℝ,
          ‖((𝐞 (-inner ℝ p.1 ξ) : Circle) : ℂ)‖ ≤ 1 := by
        filter_upwards with p
        simp
      simpa only [Pi.smul_apply, Circle.smul_def] using!
        hconv.bdd_smul 1 hchar hbound
    _ = ∫ y, ∫ x, 𝐞 (-inner ℝ (y + x) ξ) • B (f₁ x) (f₂ y) := by
      congr
      ext y
      convert! integral_sub_right_eq_self _ y (μ := volume)
      congr
      simp

theorem fourier_bilin_convolution_eq_L1
    {F₁ F₂ F₃ : Type*}
    [NormedAddCommGroup F₁] [NormedAddCommGroup F₂] [NormedAddCommGroup F₃]
    [NormedSpace ℂ F₁] [NormedSpace ℂ F₂] [NormedSpace ℂ F₃]
    [CompleteSpace F₁] [CompleteSpace F₂] [CompleteSpace F₃]
    (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃) {f₁ : ℝ → F₁} {f₂ : ℝ → F₂}
    (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) (ξ : ℝ) :
    𝓕 (f₁ ⋆[B] f₂) ξ = B (𝓕 f₁ ξ) (𝓕 f₂ ξ) := calc
  _ = ∫ y, ∫ x, 𝐞 (-inner ℝ (y + x) ξ) • B (f₁ x) (f₂ y) :=
    fourier_bilin_convolution_eq_integral_L1 B hf₁ hf₂ _
  _ = ∫ y, ∫ x, 𝐞 (-inner ℝ y ξ) • 𝐞 (-inner ℝ x ξ) • B (f₁ x) (f₂ y) := by
    congr
    ext y
    congr
    ext x
    rw [smul_smul, ← AddChar.map_add_eq_mul, inner_add_left]
    congr
    grind
  _ = ∫ y, (∫ x, B (𝐞 (-inner ℝ x ξ) • f₁ x)) (𝐞 (-inner ℝ y ξ) • f₂ y) := by
    congr
    ext y
    simp_rw [Circle.smul_def, map_smul, MeasureTheory.integral_smul]
    congr
    rw [integral_apply ?_ (f₂ y)]
    · simp
    simpa only [Circle.smul_def, map_smul] using
      B.integrable_comp ((Real.fourierIntegral_convergent_iff ξ).2 hf₁)
  _ = B (∫ x, 𝐞 (-inner ℝ x ξ) • f₁ x)
      (∫ y, 𝐞 (-inner ℝ y ξ) • f₂ y) := by
    rw [← integral_comp_comm _ ((Real.fourierIntegral_convergent_iff ξ).2 hf₂),
      ← integral_comp_comm _ ((Real.fourierIntegral_convergent_iff ξ).2 hf₁)]

theorem fourier_mul_convolution_eq_L1
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    𝓕 (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) ξ = (𝓕 f ξ) * (𝓕 g ξ) :=
  fourier_bilin_convolution_eq_L1 (ContinuousLinearMap.mul ℂ ℂ) hf hg ξ

end Real

namespace RHTower

open Complex
open FourierTransform

/-- The sharp two-edge profile tilted to the Euler line `Re s = 3/2`. -/
def rectangularEulerTilt (L a : ℝ) (x : ℝ) : ℂ :=
  (rectangularTwoEdgeProfile L a x : ℂ) * Complex.exp x

/-- The reflected sharp profile with the same Euler-line tilt. -/
def rectangularEulerReflectedTilt (L a : ℝ) (x : ℝ) : ℂ :=
  (rectangularTwoEdgeProfile L a (-x) : ℂ) * Complex.exp x

theorem integrable_rectangularTwoEdgeProfile_mul_exp
    (L a : ℝ) (w : ℂ) :
    Integrable (fun x : ℝ =>
      (rectangularTwoEdgeProfile L a x : ℂ) * Complex.exp (w * x)) := by
  have hr := integrable_rectangularIntervalIndicator_mul_exp (a - L) L w
  have hl := integrable_rectangularIntervalIndicator_mul_exp (-a) L w
  rw [show (fun x : ℝ =>
      (rectangularTwoEdgeProfile L a x : ℂ) * Complex.exp (w * x)) =
      (fun x : ℝ => (rectangularIntervalIndicator (a - L) L x : ℂ) *
        Complex.exp (w * x)) +
      (fun x : ℝ => (rectangularIntervalIndicator (-a) L x : ℂ) *
        Complex.exp (w * x)) by
    funext x
    simp only [rectangularTwoEdgeProfile]
    push_cast
    simp only [Pi.add_apply]
    ring]
  exact hr.add hl

theorem integrable_rectangularEulerTilt (L a : ℝ) :
    Integrable (rectangularEulerTilt L a) := by
  simpa only [rectangularEulerTilt, one_mul, ofReal_one] using!
    integrable_rectangularTwoEdgeProfile_mul_exp L a 1

theorem integrable_rectangularEulerReflectedTilt (L a : ℝ) :
    Integrable (rectangularEulerReflectedTilt L a) := by
  have h := (integrable_rectangularTwoEdgeProfile_mul_exp L a (-1)).comp_neg
  simpa only [rectangularEulerReflectedTilt, Function.comp_apply, ofReal_neg,
    ofReal_one, neg_mul, one_mul, neg_neg] using! h

theorem fourier_rectangularEulerTilt
    {L : ℝ} (hL : 0 ≤ L) (a ξ : ℝ) :
    𝓕 (rectangularEulerTilt L a) ξ =
      rectangularTwoEdgeTransform L a
        (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) := by
  rw [Real.fourier_eq']
  rw [show (fun x : ℝ =>
      Complex.exp ((↑(-2 * Real.pi * @inner ℝ ℝ _ x ξ) * I)) •
        rectangularEulerTilt L a x) =
      fun x : ℝ => (rectangularTwoEdgeProfile L a x : ℂ) *
        Complex.exp ((1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) * x) by
    funext x
    rw [rectangularEulerTilt, smul_eq_mul]
    calc
      Complex.exp ((↑(-2 * Real.pi * @inner ℝ ℝ _ x ξ) * I)) *
          ((rectangularTwoEdgeProfile L a x : ℂ) * Complex.exp x) =
          (rectangularTwoEdgeProfile L a x : ℂ) *
            (Complex.exp ((↑(-2 * Real.pi * @inner ℝ ℝ _ x ξ) * I)) *
              Complex.exp x) := by ring
      _ = (rectangularTwoEdgeProfile L a x : ℂ) *
          Complex.exp
            ((↑(-2 * Real.pi * @inner ℝ ℝ _ x ξ) * I) + x) := by
        rw [Complex.exp_add]
      _ = _ := by
        congr 2
        rw [Real.inner_apply]
        push_cast
        ring]
  exact rectangularTwoEdgeLaplaceIntegral_eq_transform hL a _

theorem fourier_rectangularEulerReflectedTilt
    {L : ℝ} (hL : 0 ≤ L) (a ξ : ℝ) :
    𝓕 (rectangularEulerReflectedTilt L a) ξ =
      rectangularTwoEdgeTransform L a
        (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) := by
  rw [Real.fourier_eq']
  rw [show (fun x : ℝ =>
      Complex.exp ((↑(-2 * Real.pi * @inner ℝ ℝ _ x ξ) * I)) •
        rectangularEulerReflectedTilt L a x) =
      fun x : ℝ =>
        ((rectangularTwoEdgeProfile L a · : ℝ → ℂ) *
          fun y : ℝ => Complex.exp
            ((-1 + ((2 * Real.pi * ξ : ℝ) : ℂ) * I) * y)) (-x) by
    funext x
    rw [rectangularEulerReflectedTilt, smul_eq_mul]
    simp only [Pi.mul_apply]
    calc
      Complex.exp ((↑(-2 * Real.pi * @inner ℝ ℝ _ x ξ) * I)) *
          ((rectangularTwoEdgeProfile L a (-x) : ℂ) * Complex.exp x) =
          (rectangularTwoEdgeProfile L a (-x) : ℂ) *
            (Complex.exp ((↑(-2 * Real.pi * @inner ℝ ℝ _ x ξ) * I)) *
              Complex.exp x) := by ring
      _ = (rectangularTwoEdgeProfile L a (-x) : ℂ) *
          Complex.exp
            ((↑(-2 * Real.pi * @inner ℝ ℝ _ x ξ) * I) + x) := by
        rw [Complex.exp_add]
      _ = _ := by
        congr 2
        rw [Real.inner_apply]
        push_cast
        ring]
  rw [MeasureTheory.integral_neg_eq_self]
  change rectangularTwoEdgeLaplaceIntegral L a
      (-1 + ((2 * Real.pi * ξ : ℝ) : ℂ) * I) = _
  have htransform := rectangularTwoEdgeLaplaceIntegral_eq_transform hL a
    (-1 + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)
  rw [htransform]
  have hneg : -1 + ((2 * Real.pi * ξ : ℝ) : ℂ) * I =
      -(1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) := by ring
  rw [hneg]
  exact rectangularTwoEdgeTransform_even L a
    (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I)

/-- The exponentially tilted autocorrelation on the Euler edge. -/
def rectangularEulerAutocorrelation (L a : ℝ) (h : ℝ) : ℂ :=
  (rectangularTwoEdgeAutocorrelation L a h : ℂ) * Complex.exp h

theorem rectangularEulerAutocorrelation_eq_convolution
    (L a h : ℝ) :
    rectangularEulerAutocorrelation L a h =
      (rectangularEulerReflectedTilt L a ⋆[ContinuousLinearMap.mul ℂ ℂ]
        rectangularEulerTilt L a) h := by
  rw [rectangularEulerAutocorrelation, rectangularTwoEdgeAutocorrelation]
  symm
  change (∫ t : ℝ, rectangularEulerReflectedTilt L a t *
      rectangularEulerTilt L a (h - t)) = _
  rw [← MeasureTheory.integral_neg_eq_self]
  simp only [rectangularEulerReflectedTilt, rectangularEulerTilt, neg_neg,
    sub_neg_eq_add]
  calc
    _ =
        ∫ t : ℝ,
          (((rectangularTwoEdgeProfile L a (t + h) *
            rectangularTwoEdgeProfile L a t : ℝ) : ℂ) * Complex.exp h) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [add_comm h t]
      push_cast
      have hexp : Complex.exp (-t) * Complex.exp (t + h) =
          Complex.exp h := by
        rw [← Complex.exp_add]
        congr 1
        ring
      calc
        (rectangularTwoEdgeProfile L a t : ℂ) * Complex.exp (-t) *
            ((rectangularTwoEdgeProfile L a (t + h) : ℂ) *
              Complex.exp (t + h)) =
            (rectangularTwoEdgeProfile L a (t + h) : ℂ) *
              (rectangularTwoEdgeProfile L a t : ℂ) *
                (Complex.exp (-t) * Complex.exp (t + h)) := by ring
        _ = _ := by rw [hexp]
    _ = _ := by rw [integral_mul_const, integral_complex_ofReal]

/-- The Fourier transform of the tilted sharp autocorrelation is the exact square of the
rectangular bilateral transform on `Re w = 1`. -/
theorem fourier_rectangularEulerAutocorrelation
    {L : ℝ} (hL : 0 ≤ L) (a ξ : ℝ) :
    𝓕 (rectangularEulerAutocorrelation L a) ξ =
      rectangularTwoEdgeTransform L a
          (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2 := by
  rw [funext (rectangularEulerAutocorrelation_eq_convolution L a)]
  rw [Real.fourier_mul_convolution_eq_L1
    (integrable_rectangularEulerReflectedTilt L a)
    (integrable_rectangularEulerTilt L a) ξ]
  rw [fourier_rectangularEulerReflectedTilt hL,
    fourier_rectangularEulerTilt hL]
  ring

/-- A fixed majorant for the squared Euler-line transform. -/
def rectangularEulerFourierMajorant (L a : ℝ) : ℝ :=
  (2 * Real.exp |a| * (1 + Real.exp |L|)) ^ 2

theorem norm_rectangularTwoEdgeTransform_eulerLine_sq_le
    (L a ξ : ℝ) :
    ‖rectangularTwoEdgeTransform L a
        (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2‖ ≤
      rectangularEulerFourierMajorant L a * (1 + ξ ^ 2)⁻¹ := by
  let w : ℂ := 1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I
  let B : ℝ := 1 + Real.exp |L|
  let C : ℝ := 2 * Real.exp |a| * B
  have hwre : w.re = 1 := by
    dsimp only [w]
    simp [Complex.mul_re]
  have hwim : w.im = -(2 * Real.pi * ξ) := by
    dsimp only [w]
    simp [Complex.mul_im]
  have hw : w ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hwre] at this
    norm_num at this
  have hwNormSq : ‖w‖ ^ 2 = 1 + (2 * Real.pi * ξ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hwre, hwim]
    ring
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hAw : ‖rectangularWindowAmplitude L w‖ ≤ B / ‖w‖ := by
    rw [rectangularWindowAmplitude_eq_div hw, norm_div]
    gcongr
    calc
      ‖1 - Complex.exp (-(L : ℂ) * w)‖ ≤
          1 + ‖Complex.exp (-(L : ℂ) * w)‖ := by
        simpa only [norm_one] using norm_sub_le (1 : ℂ)
          (Complex.exp (-(L : ℂ) * w))
      _ = 1 + Real.exp (-L) := by
        rw [Complex.norm_exp]
        congr 2
        simp [Complex.mul_re, hwre]
      _ ≤ B := by
        dsimp only [B]
        gcongr
        exact neg_le_abs L
  have hAnw : ‖rectangularWindowAmplitude L (-w)‖ ≤ B / ‖w‖ := by
    rw [rectangularWindowAmplitude_eq_div (neg_ne_zero.mpr hw), norm_div,
      norm_neg]
    gcongr
    calc
      ‖1 - Complex.exp (-(L : ℂ) * -w)‖ ≤
          1 + ‖Complex.exp (-(L : ℂ) * -w)‖ := by
        simpa only [norm_one] using norm_sub_le (1 : ℂ)
          (Complex.exp (-(L : ℂ) * -w))
      _ = 1 + Real.exp L := by
        rw [Complex.norm_exp]
        congr 2
        simp [Complex.mul_re, hwre]
      _ ≤ B := by
        dsimp only [B]
        gcongr
        exact le_abs_self L
  have hepos : ‖Complex.exp ((a : ℂ) * w)‖ ≤ Real.exp |a| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp [Complex.mul_re, hwre]
    exact le_abs_self a
  have heneg : ‖Complex.exp (-(a : ℂ) * w)‖ ≤ Real.exp |a| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp [Complex.mul_re, hwre]
    exact neg_le_abs a
  have hF : ‖rectangularTwoEdgeTransform L a w‖ ≤ C / ‖w‖ := by
    rw [rectangularTwoEdgeTransform]
    calc
      ‖Complex.exp ((a : ℂ) * w) * rectangularWindowAmplitude L w +
          Complex.exp (-(a : ℂ) * w) * rectangularWindowAmplitude L (-w)‖ ≤
          ‖Complex.exp ((a : ℂ) * w)‖ * ‖rectangularWindowAmplitude L w‖ +
            ‖Complex.exp (-(a : ℂ) * w)‖ *
              ‖rectangularWindowAmplitude L (-w)‖ := by
        simpa only [norm_mul] using norm_add_le
          (Complex.exp ((a : ℂ) * w) * rectangularWindowAmplitude L w)
          (Complex.exp (-(a : ℂ) * w) * rectangularWindowAmplitude L (-w))
      _ ≤ Real.exp |a| * (B / ‖w‖) +
          Real.exp |a| * (B / ‖w‖) := by gcongr
      _ = C / ‖w‖ := by
        dsimp only [C]
        ring
  have hF2 : ‖rectangularTwoEdgeTransform L a w‖ ^ 2 ≤
      (C / ‖w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hF 2
  have hden : 1 + ξ ^ 2 ≤ 1 + (2 * Real.pi * ξ) ^ 2 := by
    have hp : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    nlinarith [sq_nonneg ξ, mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1) hp]
  change ‖rectangularTwoEdgeTransform L a w ^ 2‖ ≤ _
  rw [norm_pow]
  calc
    ‖rectangularTwoEdgeTransform L a w‖ ^ 2 ≤ (C / ‖w‖) ^ 2 := hF2
    _ = C ^ 2 / (1 + (2 * Real.pi * ξ) ^ 2) := by
      rw [div_pow, hwNormSq]
    _ ≤ C ^ 2 / (1 + ξ ^ 2) := by
      exact div_le_div_of_nonneg_left (sq_nonneg C) (by positivity) hden
    _ = rectangularEulerFourierMajorant L a * (1 + ξ ^ 2)⁻¹ := by
      rw [div_eq_mul_inv]
      rfl

theorem integrable_rectangularTwoEdgeTransform_eulerLine_sq (L a : ℝ) :
    Integrable (fun ξ : ℝ =>
      rectangularTwoEdgeTransform L a
        (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2) := by
  let M : ℝ := rectangularEulerFourierMajorant L a
  have hmajor : Integrable (fun ξ : ℝ => M * (1 + ξ ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul M
  refine hmajor.mono' ?_ ?_
  · have hc : Continuous (fun ξ : ℝ =>
        rectangularTwoEdgeTransform L a
          (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I)) :=
      (rectangularTwoEdgeTransform_differentiable L a).continuous.comp (by fun_prop)
    exact (hc.pow 2).aestronglyMeasurable
  · filter_upwards with ξ
    dsimp only [M]
    exact norm_rectangularTwoEdgeTransform_eulerLine_sq_le L a ξ

theorem continuous_rectangularTwoEdgeAutocorrelation (L a : ℝ) :
    Continuous (rectangularTwoEdgeAutocorrelation L a) := by
  rw [show rectangularTwoEdgeAutocorrelation L a = fun h : ℝ =>
      2 * max 0 (L - |h|) +
        max 0 (L - |h - (2 * a - L)|) +
        max 0 (L - |h + (2 * a - L)|) by
    funext h
    exact rectangularTwoEdgeAutocorrelation_eq_four_tents L a h]
  fun_prop

theorem continuous_rectangularEulerAutocorrelation (L a : ℝ) :
    Continuous (rectangularEulerAutocorrelation L a) := by
  unfold rectangularEulerAutocorrelation
  exact (Complex.continuous_ofReal.comp
    (continuous_rectangularTwoEdgeAutocorrelation L a)).mul
      (Complex.continuous_exp.comp Complex.continuous_ofReal)

theorem integrable_rectangularEulerAutocorrelation (L a : ℝ) :
    Integrable (rectangularEulerAutocorrelation L a) := by
  rw [show rectangularEulerAutocorrelation L a =
      rectangularEulerReflectedTilt L a ⋆[ContinuousLinearMap.mul ℂ ℂ]
        rectangularEulerTilt L a by
    funext h
    exact rectangularEulerAutocorrelation_eq_convolution L a h]
  exact (integrable_rectangularEulerReflectedTilt L a).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (integrable_rectangularEulerTilt L a)

theorem integrable_fourier_rectangularEulerAutocorrelation
    {L : ℝ} (hL : 0 ≤ L) (a : ℝ) :
    Integrable (𝓕 (rectangularEulerAutocorrelation L a)) := by
  rw [show 𝓕 (rectangularEulerAutocorrelation L a) = fun ξ : ℝ =>
      rectangularTwoEdgeTransform L a
        (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2 by
    funext ξ
    exact fourier_rectangularEulerAutocorrelation hL a ξ]
  exact integrable_rectangularTwoEdgeTransform_eulerLine_sq L a

/-- **Sharp rectangular Fourier inversion.**  The exact squared bilateral transform on the
Euler line recovers the exponentially tilted piecewise-linear autocorrelation, with no smoothing
or regularity hypothesis. -/
theorem integral_rectangularEulerFourierKernel
    {L : ℝ} (hL : 0 ≤ L) (a t : ℝ) :
    (∫ ξ : ℝ,
        Complex.exp ((((2 * Real.pi * ξ * t : ℝ) : ℂ)) * I) *
          rectangularTwoEdgeTransform L a
            (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2) =
      (rectangularTwoEdgeAutocorrelation L a t : ℂ) * Complex.exp t := by
  have hinv := (integrable_rectangularEulerAutocorrelation L a).fourierInv_fourier_eq
    (integrable_fourier_rectangularEulerAutocorrelation hL a)
    (v := t)
    (continuous_rectangularEulerAutocorrelation L a).continuousAt
  rw [Real.fourierInv_eq'] at hinv
  rw [show 𝓕 (rectangularEulerAutocorrelation L a) = fun ξ : ℝ =>
      rectangularTwoEdgeTransform L a
        (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2 by
    funext ξ
    exact fourier_rectangularEulerAutocorrelation hL a ξ] at hinv
  simpa only [smul_eq_mul, rectangularEulerAutocorrelation, Real.inner_apply,
    ofReal_mul, mul_assoc] using hinv

theorem natCast_cpow_neg_eulerFourier
    (n : ℕ) (hn : 1 ≤ n) (ξ : ℝ) :
    (n : ℂ) ^
        (-(3 / 2 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I)) =
      (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp ((((2 * Real.pi * ξ * Real.log n : ℝ) : ℂ)) * I) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Complex.cpow_def_of_ne_zero hn0]
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hnpos.le]
  rw [hlog]
  have hexpand : ((Real.log n : ℝ) : ℂ) *
      (-(3 / 2 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I)) =
      (((Real.log n * (-(3 / 2 : ℝ)) : ℝ) : ℂ)) +
        (((2 * Real.pi * ξ * Real.log n : ℝ) : ℂ) * I) := by
    push_cast
    ring
  rw [hexpand, Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_exp, ← Real.rpow_def_of_pos hnpos]

theorem eulerFourier_vonMangoldt_term
    (n : ℕ) (hn : 1 ≤ n) (ξ : ℝ) :
    LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
        (3 / 2 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) n =
      (((ArithmeticFunction.vonMangoldt n : ℝ) *
          (n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp ((((2 * Real.pi * ξ * Real.log n : ℝ) : ℂ)) * I) := by
  have hn0 : n ≠ 0 := by omega
  rw [LSeries.term_of_ne_zero hn0, div_eq_mul_inv, ← Complex.cpow_neg,
    natCast_cpow_neg_eulerFourier n hn ξ]
  push_cast
  ring

/-- One Euler-line von Mangoldt monomial is read by the sharp Fourier square as exactly its
critical-weight autocorrelation coefficient. -/
theorem integral_rectangularEulerFourierKernel_mul_vonMangoldtTerm
    {L : ℝ} (hL : 0 ≤ L) (a : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (∫ ξ : ℝ,
        rectangularTwoEdgeTransform L a
            (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2 *
          LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
            (3 / 2 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) n) =
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        rectangularTwoEdgeAutocorrelation L a (Real.log n) : ℝ) : ℂ) := by
  rw [show (fun ξ : ℝ =>
      rectangularTwoEdgeTransform L a
          (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2 *
        LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
          (3 / 2 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) n) =
      fun ξ : ℝ =>
        (((ArithmeticFunction.vonMangoldt n : ℝ) *
            (n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
          (Complex.exp
              ((((2 * Real.pi * ξ * Real.log n : ℝ) : ℂ)) * I) *
            rectangularTwoEdgeTransform L a
              (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2) by
    funext ξ
    rw [eulerFourier_vonMangoldt_term n hn ξ]
    ring]
  rw [integral_const_mul, integral_rectangularEulerFourierKernel hL]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsqrt : Real.sqrt n = (n : ℝ) ^ (1 / 2 : ℝ) :=
    Real.sqrt_eq_rpow n
  have hweight : (n : ℝ) ^ (-(3 / 2 : ℝ)) * n =
      1 / Real.sqrt n := by
    rw [hsqrt, one_div, ← Real.rpow_neg hnpos.le]
    calc
      (n : ℝ) ^ (-(3 / 2 : ℝ)) * n =
          (n : ℝ) ^ (-(3 / 2 : ℝ)) * (n : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (n : ℝ) ^ (-(3 / 2 : ℝ) + 1) := by
        rw [Real.rpow_add hnpos]
      _ = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by norm_num
  push_cast
  rw [Complex.exp_log (by exact_mod_cast (show n ≠ 0 by omega))]
  norm_cast
  calc
    ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(3 / 2 : ℝ)) *
          (rectangularTwoEdgeAutocorrelation L a (Real.log n) * n) =
        ArithmeticFunction.vonMangoldt n *
          ((n : ℝ) ^ (-(3 / 2 : ℝ)) * n) *
            rectangularTwoEdgeAutocorrelation L a (Real.log n) := by ring
    _ = _ := by rw [hweight]; ring

private theorem norm_eulerFourier_vonMangoldt_term
    (n : ℕ) (ξ : ℝ) :
    ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
        (3 / 2 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) n‖ =
      ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
        (3 / 2 : ℂ) n‖ := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [LSeries.term_zero]
  · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0,
      norm_div, norm_div]
    congr 1
    rw [Complex.norm_natCast_cpow_of_pos hn,
      Complex.norm_natCast_cpow_of_pos hn]
    norm_num

private theorem integrable_rectangularEulerFourierKernel_mul_vonMangoldtTerm
    (L a : ℝ) (n : ℕ) :
    Integrable (fun ξ : ℝ =>
      rectangularTwoEdgeTransform L a
          (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2 *
        LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
          (3 / 2 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) n) := by
  let K : ℝ → ℂ := fun ξ =>
    rectangularTwoEdgeTransform L a
      (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2
  let T : ℝ → ℂ := fun ξ =>
    LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
      (3 / 2 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) n
  have hK : Integrable K := integrable_rectangularTwoEdgeTransform_eulerLine_sq L a
  have hTmeas : AEStronglyMeasurable T := by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp only [T, LSeries.term_zero]
      fun_prop
    · rw [show T = fun ξ : ℝ =>
        (((ArithmeticFunction.vonMangoldt n : ℝ) *
            (n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
          Complex.exp ((((2 * Real.pi * ξ * Real.log n : ℝ) : ℂ)) * I) by
        funext ξ
        exact eulerFourier_vonMangoldt_term n hn ξ]
      fun_prop
  have hTbound : ∀ᵐ ξ : ℝ,
      ‖T ξ‖ ≤ ‖LSeries.term
        (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (3 / 2 : ℂ) n‖ := by
    filter_upwards with ξ
    exact le_of_eq (norm_eulerFourier_vonMangoldt_term n ξ)
  exact hK.mul_bdd hTmeas hTbound

/-- **Prime edge evaluation.**  The Fourier-normalized Euler edge pairs the honest von Mangoldt
L-series with the squared sharp rectangular transform and returns the exact critical-weight
autocorrelation sum. -/
theorem integral_rectangularEulerFourierKernel_mul_vonMangoldtLSeries
    {L : ℝ} (hL : 0 ≤ L) (a : ℝ) :
    (∫ ξ : ℝ,
        rectangularTwoEdgeTransform L a
            (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2 *
          LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
            (3 / 2 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I)) =
      ∑' n : ℕ,
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt n *
          rectangularTwoEdgeAutocorrelation L a (Real.log n) : ℝ) : ℂ) := by
  let F : ℕ → ℝ → ℂ := fun n ξ =>
    rectangularTwoEdgeTransform L a
        (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2 *
      LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
        (3 / 2 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) n
  have hFint : ∀ n, Integrable (F n) := fun n =>
    integrable_rectangularEulerFourierKernel_mul_vonMangoldtTerm L a n
  let J : ℝ := ∫ ξ : ℝ,
    ‖rectangularTwoEdgeTransform L a
      (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2‖
  have hvm : LSeriesSummable
      (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (3 / 2 : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have hnormIntegral : ∀ n : ℕ,
      (∫ ξ : ℝ, ‖F n ξ‖) =
        ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
            (3 / 2 : ℂ) n‖ * J := by
    intro n
    rw [show (fun ξ : ℝ => ‖F n ξ‖) = fun ξ : ℝ =>
        ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
            (3 / 2 : ℂ) n‖ *
          ‖rectangularTwoEdgeTransform L a
            (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2‖ by
      funext ξ
      dsimp only [F]
      rw [norm_mul, norm_eulerFourier_vonMangoldt_term n ξ]
      ring]
    rw [integral_const_mul]
  have hFsum : Summable (fun n => ∫ ξ : ℝ, ‖F n ξ‖) := by
    rw [show (fun n => ∫ ξ : ℝ, ‖F n ξ‖) = fun n =>
        ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
          (3 / 2 : ℂ) n‖ * J by
      funext n
      exact hnormIntegral n]
    exact hvm.norm.mul_right J
  have hinterchange := integral_tsum_of_summable_integral_norm hFint hFsum
  rw [show (fun ξ : ℝ => ∑' n, F n ξ) = fun ξ : ℝ =>
      rectangularTwoEdgeTransform L a
          (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2 *
        LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
          (3 / 2 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) by
    funext ξ
    have hsum : LSeriesSummable
        (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
          (3 / 2 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
    dsimp only [F]
    rw [LSeries, ← tsum_mul_left]] at hinterchange
  rw [show (fun n : ℕ => ∫ ξ : ℝ, F n ξ) = fun n : ℕ =>
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        rectangularTwoEdgeAutocorrelation L a (Real.log n) : ℝ) : ℂ) by
    funext n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [F]
    · exact integral_rectangularEulerFourierKernel_mul_vonMangoldtTerm
        hL a n hn] at hinterchange
  exact hinterchange.symm

theorem tsum_rectangularPrimeAutocorrelation_eq_finite
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    (∑' n : ℕ,
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt n *
          rectangularTwoEdgeAutocorrelation L a (Real.log n) : ℝ) : ℂ)) =
      (rectangularPrimeAutocorrelationSum L a : ℂ) := by
  rw [tsum_eq_sum (s := Finset.Icc 2 (Nat.floor (Real.exp (2 * a))))]
  · rw [rectangularPrimeAutocorrelationSum, ofReal_sum]
  · intro n hnmem
    by_cases hn2 : 2 ≤ n
    · have hnupper : Nat.floor (Real.exp (2 * a)) < n := by
        by_contra hnot
        apply hnmem
        exact Finset.mem_Icc.mpr ⟨hn2, by omega⟩
      have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hexp : Real.exp (2 * a) < (n : ℝ) :=
        (Nat.floor_lt (Real.exp_pos (2 * a)).le).mp hnupper
      have hlog : 2 * a < Real.log n :=
        (Real.lt_log_iff_exp_lt hnreal).mpr hexp
      rw [rectangularTwoEdgeAutocorrelation_eq_zero_of_two_mul_a_lt
        hL ha hlog, mul_zero, ofReal_zero]
    · interval_cases n <;> simp [ArithmeticFunction.vonMangoldt]

/-- Finite arithmetic form of the sharp Euler edge. -/
theorem integral_rectangularEulerFourierKernel_mul_vonMangoldtLSeries_eq_primeSum
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    (∫ ξ : ℝ,
        rectangularTwoEdgeTransform L a
            (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2 *
          LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
            (3 / 2 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I)) =
      (rectangularPrimeAutocorrelationSum L a : ℂ) := by
  rw [integral_rectangularEulerFourierKernel_mul_vonMangoldtLSeries hL,
    tsum_rectangularPrimeAutocorrelation_eq_finite hL ha]

/-- The same prime-edge law in the literal centered-Xi contour coordinate.  The real dilation
`x = -2πξ` supplies exactly the Fourier normalization. -/
theorem invTwoPi_smul_rectangularBottomPrimeIntegral_eq_primeSum
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    (2 * Real.pi)⁻¹ •
        (∫ x : ℝ,
          xiRectangularTwoEdgeTransform L a ((x : ℂ) - I) ^ 2 *
            LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
              (3 / 2 + x * I)) =
      (rectangularPrimeAutocorrelationSum L a : ℂ) := by
  let g : ℝ → ℂ := fun x =>
    xiRectangularTwoEdgeTransform L a ((x : ℂ) - I) ^ 2 *
      LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
        (3 / 2 + x * I)
  have hscale := MeasureTheory.Measure.integral_comp_mul_left g (-2 * Real.pi)
  have hfactor : |(-2 * Real.pi)⁻¹| = (2 * Real.pi)⁻¹ := by
    rw [abs_inv]
    have hneg : -2 * Real.pi < 0 :=
      mul_neg_of_neg_of_pos (by norm_num) Real.pi_pos
    rw [abs_of_neg hneg]
    congr 1
    ring
  rw [hfactor] at hscale
  rw [← hscale]
  rw [show (fun ξ : ℝ => g ((-2 * Real.pi) * ξ)) = fun ξ : ℝ =>
      rectangularTwoEdgeTransform L a
          (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2 *
        LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
          (3 / 2 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) by
    funext ξ
    dsimp only [g]
    congr 1
    · rw [xiRectangularTwoEdgeTransform]
      congr 2
      push_cast
      rw [mul_sub, Complex.I_mul_I]
      ring
    · congr 1
      push_cast
      ring]
  exact integral_rectangularEulerFourierKernel_mul_vonMangoldtLSeries_eq_primeSum
    hL ha

/-- After the symmetric Xi contour is divided by `2πi`, its complete bottom-edge von Mangoldt
contribution is exactly `-2` times the finite rectangular prime autocorrelation value.  This is
the prime term, with its final explicit-formula sign and normalization already resolved. -/
theorem normalized_rectangularBottomPrimeContribution_eq_neg_two_primeSum
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    (2 * Real.pi * I)⁻¹ *
        (2 * ∫ x : ℝ,
          -I *
            (xiRectangularTwoEdgeTransform L a ((x : ℂ) - I) ^ 2 *
              LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
                (3 / 2 + x * I))) =
      -2 * (rectangularPrimeAutocorrelationSum L a : ℂ) := by
  have hprime := invTwoPi_smul_rectangularBottomPrimeIntegral_eq_primeSum hL ha
  change (((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
      (∫ x : ℝ,
        xiRectangularTwoEdgeTransform L a ((x : ℂ) - I) ^ 2 *
          LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
            (3 / 2 + x * I)) =
        (rectangularPrimeAutocorrelationSum L a : ℂ) at hprime
  have htwoPi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
  have hj :
      (∫ x : ℝ,
        xiRectangularTwoEdgeTransform L a ((x : ℂ) - I) ^ 2 *
          LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
            (3 / 2 + x * I)) =
        (2 * Real.pi : ℂ) * (rectangularPrimeAutocorrelationSum L a : ℂ) := by
    rw [ofReal_inv] at hprime
    apply (inv_mul_eq_iff_eq_mul₀ htwoPi).mp
    simpa using hprime
  rw [MeasureTheory.integral_const_mul, hj]
  field_simp

end RHTower

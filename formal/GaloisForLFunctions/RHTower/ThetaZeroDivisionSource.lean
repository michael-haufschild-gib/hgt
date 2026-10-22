import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceSpectrumExact
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaKernelEnergy
import GaloisForLFunctions.RHTower.ThetaTiltLogDensity
import GaloisForLFunctions.RHTower.WeightedLaplaceShift
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspSchwartzFourierXi
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspComplexStrip
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspReflectedSourceOddStationary
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullDerivativeExponentialMoments
import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.HTGeometry.GammaVerticalPolynomialDecay
import GaloisForLFunctions.HTGeometry.WaveTracePoleTransform

/-!
# One-sided zero division of even sources

For a complex parameter `α` and an even continuous source `f` with every exponential moment, the
outward sine Green operator `(T_α f)(x) = α ∫₀^∞ sin(αt) f(x+t) dt` and its even extension
`g = T_α f(|·|)` satisfy the exact Fourier division law

`(α² - z²) ĝ(z) = α² (f̂(z) - f̂(α))`,     `f̂(z) = ∫ e^{-izx} f(x) dx`.

On the whole line `T_α f = α (cos(αx) S(x) - sin(αx) C(x))` with the sine and cosine tails
`S, C`; when `f̂(α) = 0` this Green solution is even, so the even extension is smooth and solves
`g'' + α² g = α² f` everywhere.  The class of continuous even sources with every exponential
moment is closed under zero division.

For the completed theta source `k` (with `k̂ = XiC`), every complex zero division is bounded by
`C e^{-2|x|} k(x)`.  At a positive real zero `γ` of `XiC`, the real division `g_γ` is strictly
positive (integration by parts against `1 - cos(γt)` and `k' < 0` on `(0,∞)`), has the same
mass, and `ĝ_γ(z) (1 - z²/γ²) = XiC(z)`.  The positive flow `(1-ε) k + ε g_γ` moves the selected
pair to `±γ/√(1-ε)`, keeps every other zero with at least its multiplicity, and at `ε = 1`
removes exactly one copy of `±γ`.
-/
open MeasureTheory Set Filter Topology Complex

noncomputable section

namespace RHTower

/-! ## Exponential bounds for the complex sine and cosine -/

theorem abs_im_mul_ofReal (α : ℂ) (t : ℝ) : |(α * (t : ℂ)).im| = |α.im| * |t| := by
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, abs_mul]

theorem norm_csin_mul_ofReal_le (α : ℂ) (t : ℝ) :
    ‖Complex.sin (α * t)‖ ≤ Real.exp (|α.im| * |t|) := by
  simpa only [abs_im_mul_ofReal] using GaloisForLFunctions.HTGeometry.norm_csin_le_exp_abs_im (α * t)

theorem norm_ccos_mul_ofReal_le (α : ℂ) (t : ℝ) :
    ‖Complex.cos (α * t)‖ ≤ Real.exp (|α.im| * |t|) := by
  simpa only [abs_im_mul_ofReal] using GaloisForLFunctions.HTGeometry.norm_ccos_le_exp_abs_im (α * t)

/-! ## Sources with every exponential moment -/

/-- A continuous source with finite exponential moments of every order. -/
structure ExpMomentSource (f : ℝ → ℂ) : Prop where
  continuous : Continuous f
  moment : ∀ c : ℝ, Integrable (fun x => Real.exp (c * |x|) * ‖f x‖)

namespace ExpMomentSource

variable {f : ℝ → ℂ}

theorem integrable_mul (hf : ExpMomentSource f) {w : ℝ → ℂ} (hw : Continuous w) {c : ℝ}
    (hwb : ∀ x, ‖w x‖ ≤ Real.exp (c * |x|)) : Integrable (fun x => w x * f x) := by
  refine (hf.moment c).mono' (hw.mul hf.continuous).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hwb x) (norm_nonneg _)

theorem integrable_mul_shift (hf : ExpMomentSource f) {w : ℝ → ℂ} (hw : Continuous w) {c : ℝ}
    (hwb : ∀ t, ‖w t‖ ≤ Real.exp (c * |t|)) (x : ℝ) :
    Integrable (fun t => w t * f (x + t)) := by
  have hI := ((hf.moment |c|).comp_add_left x).const_mul (Real.exp (|c| * |x|))
  refine hI.mono' (hw.mul (hf.continuous.comp (continuous_const.add continuous_id))).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [norm_mul]
  have htri : |t| ≤ |x| + |x + t| := by
    calc |t| = |-x + (x + t)| := by ring_nf
      _ ≤ |-x| + |x + t| := abs_add_le _ _
      _ = |x| + |x + t| := by rw [abs_neg]
  have hct : c * |t| ≤ |c| * |x| + |c| * |x + t| := by
    calc c * |t| ≤ |c| * |t| := mul_le_mul_of_nonneg_right (le_abs_self c) (abs_nonneg t)
      _ ≤ |c| * (|x| + |x + t|) := mul_le_mul_of_nonneg_left htri (abs_nonneg c)
      _ = _ := by ring
  have hexp : Real.exp (c * |t|) ≤ Real.exp (|c| * |x|) * Real.exp (|c| * |x + t|) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr hct
  calc ‖w t‖ * ‖f (x + t)‖ ≤ Real.exp (c * |t|) * ‖f (x + t)‖ :=
        mul_le_mul_of_nonneg_right (hwb t) (norm_nonneg _)
    _ ≤ (Real.exp (|c| * |x|) * Real.exp (|c| * |x + t|)) * ‖f (x + t)‖ :=
        mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
    _ = Real.exp (|c| * |x|) * (Real.exp (|c| * |x + t|) * ‖f (x + t)‖) := by ring

theorem integrable (hf : ExpMomentSource f) : Integrable f := by
  refine (hf.moment 0).mono' hf.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  simp

theorem integrable_sin (hf : ExpMomentSource f) (α : ℂ) :
    Integrable (fun t : ℝ => Complex.sin (α * t) * f t) :=
  hf.integrable_mul (by fun_prop) (norm_csin_mul_ofReal_le α)

theorem integrable_cos (hf : ExpMomentSource f) (α : ℂ) :
    Integrable (fun t : ℝ => Complex.cos (α * t) * f t) :=
  hf.integrable_mul (by fun_prop) (norm_ccos_mul_ofReal_le α)

theorem integrable_sin_shift (hf : ExpMomentSource f) (α : ℂ) (x : ℝ) :
    Integrable (fun t : ℝ => Complex.sin (α * t) * f (x + t)) :=
  hf.integrable_mul_shift (by fun_prop) (norm_csin_mul_ofReal_le α) x

theorem integrable_cexp (hf : ExpMomentSource f) (z : ℂ) :
    Integrable (fun x : ℝ => Complex.exp (-I * z * x) * f x) := by
  refine hf.integrable_mul (by fun_prop) (c := |z.im|) fun x => ?_
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have : (-I * z * (x : ℂ)).re = z.im * x := by simp [Complex.mul_re]
  rw [this, ← abs_mul]
  exact le_abs_self _

end ExpMomentSource

/-! ## The outward sine Green operator -/

/-- Outward sine Green operator `(T_α f)(x) = α ∫₀^∞ sin(αt) f(x+t) dt`. -/
def outwardSine (α : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  α * ∫ t in Ioi (0 : ℝ), Complex.sin (α * t) * f (x + t)

/-- One-sided zero division: the even extension `x ↦ (T_α f)(|x|)`. -/
def zeroDivision (α : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ := outwardSine α f |x|

/-- Sine tail `S(x) = ∫_x^∞ sin(αt) f(t) dt`. -/
def sineTail (α : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ := ∫ t in Ioi x, Complex.sin (α * t) * f t

/-- Cosine tail `C(x) = ∫_x^∞ cos(αt) f(t) dt`. -/
def cosineTail (α : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ := ∫ t in Ioi x, Complex.cos (α * t) * f t

/-- The globally defined Green solution `α (cos(αx) S(x) - sin(αx) C(x))`. -/
def joinedDivision (α : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  α * (Complex.cos (α * x) * sineTail α f x - Complex.sin (α * x) * cosineTail α f x)

/-- Its derivative `-α² (sin(αx) S(x) + cos(αx) C(x))`. -/
def joinedDivisionDeriv (α : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  -(α ^ 2 * (Complex.sin (α * x) * sineTail α f x + Complex.cos (α * x) * cosineTail α f x))

/-- The Fourier transform `F_f(z) = ∫ e^{-izx} f(x) dx`. -/
def sourceTransform (f : ℝ → ℂ) (z : ℂ) : ℂ := ∫ x : ℝ, Complex.exp (-I * z * x) * f x

theorem outwardSine_eq_integral_Ioi (α : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    outwardSine α f x = α * ∫ t in Ioi x, Complex.sin (α * (t - x)) * f t := by
  unfold outwardSine
  congr 1
  have h := GaloisForLFunctions.RHTower.setIntegral_Ioi_comp_add_right
    (fun t : ℝ => Complex.sin (α * ((t : ℂ) - x)) * f t) x x
  rw [sub_self] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [Complex.ofReal_add, add_sub_cancel_right, add_comm x t]

theorem outwardSine_eq_joinedDivision {f : ℝ → ℂ} (hf : ExpMomentSource f) (α : ℂ) (x : ℝ) :
    outwardSine α f x = joinedDivision α f x := by
  rw [outwardSine_eq_integral_Ioi, joinedDivision, sineTail, cosineTail]
  congr 1
  rw [← integral_const_mul, ← integral_const_mul, ← integral_sub]
  · refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [mul_sub, Complex.sin_sub]
    ring
  · exact ((hf.integrable_sin α).const_mul _).integrableOn
  · exact ((hf.integrable_cos α).const_mul _).integrableOn

theorem zeroDivision_eq_joinedDivision_abs {f : ℝ → ℂ} (hf : ExpMomentSource f) (α : ℂ)
    (x : ℝ) : zeroDivision α f x = joinedDivision α f |x| :=
  outwardSine_eq_joinedDivision hf α |x|

theorem zeroDivision_neg (α : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    zeroDivision α f (-x) = zeroDivision α f x := by
  simp only [zeroDivision, abs_neg]

/-! ## Tail calculus -/

theorem setIntegral_Ioi_eq_sub {g : ℝ → ℂ} (hg : Integrable g) (x : ℝ) :
    (∫ t in Ioi x, g t) = (∫ t in Ioi (0 : ℝ), g t) - ∫ t in (0 : ℝ)..x, g t := by
  rw [← intervalIntegral.integral_Ioi_sub_Ioi' hg.integrableOn hg.integrableOn]
  ring

theorem hasDerivAt_setIntegral_Ioi {g : ℝ → ℂ} (hg : Integrable g) (hc : Continuous g) (x : ℝ) :
    HasDerivAt (fun y => ∫ t in Ioi y, g t) (-g x) x := by
  have h := (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hfun : (fun y => ∫ t in Ioi y, g t) =
      fun y => (∫ t in Ioi (0 : ℝ), g t) - ∫ t in (0 : ℝ)..y, g t :=
    funext (setIntegral_Ioi_eq_sub hg)
  rw [hfun]
  simpa using h.const_sub (∫ t in Ioi (0 : ℝ), g t)

theorem hasDerivAt_sineTail {f : ℝ → ℂ} (hf : ExpMomentSource f) (α : ℂ) (x : ℝ) :
    HasDerivAt (sineTail α f) (-(Complex.sin (α * x) * f x)) x :=
  hasDerivAt_setIntegral_Ioi (hf.integrable_sin α) (by have := hf.continuous; fun_prop) x

theorem hasDerivAt_cosineTail {f : ℝ → ℂ} (hf : ExpMomentSource f) (α : ℂ) (x : ℝ) :
    HasDerivAt (cosineTail α f) (-(Complex.cos (α * x) * f x)) x :=
  hasDerivAt_setIntegral_Ioi (hf.integrable_cos α) (by have := hf.continuous; fun_prop) x

theorem hasDerivAt_csin_mul (α : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.sin (α * y)) (α * Complex.cos (α * x)) x := by
  have h := ((Complex.hasDerivAt_sin (α * x)).comp (x : ℂ)
    ((hasDerivAt_id (x : ℂ)).const_mul α)).comp_ofReal
  exact h.congr_deriv (by simp only [mul_one]; ring)

theorem hasDerivAt_ccos_mul (α : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.cos (α * y)) (-(α * Complex.sin (α * x))) x := by
  have h := ((Complex.hasDerivAt_cos (α * x)).comp (x : ℂ)
    ((hasDerivAt_id (x : ℂ)).const_mul α)).comp_ofReal
  exact h.congr_deriv (by simp only [mul_one]; ring)

theorem hasDerivAt_joinedDivision {f : ℝ → ℂ} (hf : ExpMomentSource f) (α : ℂ) (x : ℝ) :
    HasDerivAt (joinedDivision α f) (joinedDivisionDeriv α f x) x := by
  have hS := hasDerivAt_sineTail hf α x
  have hC := hasDerivAt_cosineTail hf α x
  have hc := hasDerivAt_ccos_mul α x
  have hs := hasDerivAt_csin_mul α x
  have h := ((hc.mul hS).sub (hs.mul hC)).const_mul α
  refine h.congr_deriv ?_
  simp only [joinedDivisionDeriv]
  ring

theorem hasDerivAt_joinedDivisionDeriv {f : ℝ → ℂ} (hf : ExpMomentSource f) (α : ℂ) (x : ℝ) :
    HasDerivAt (joinedDivisionDeriv α f) (α ^ 2 * (f x - joinedDivision α f x)) x := by
  have hS := hasDerivAt_sineTail hf α x
  have hC := hasDerivAt_cosineTail hf α x
  have hc := hasDerivAt_ccos_mul α x
  have hs := hasDerivAt_csin_mul α x
  have h := (((hs.mul hS).add (hc.mul hC)).const_mul (α ^ 2)).neg
  refine h.congr_deriv ?_
  simp only [joinedDivision]
  have hsc := Complex.sin_sq_add_cos_sq (α * x)
  linear_combination (α ^ 2 * f x) * hsc

theorem continuous_joinedDivision {f : ℝ → ℂ} (hf : ExpMomentSource f) (α : ℂ) :
    Continuous (joinedDivision α f) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_joinedDivision hf α x).continuousAt

theorem continuous_zeroDivision {f : ℝ → ℂ} (hf : ExpMomentSource f) (α : ℂ) :
    Continuous (zeroDivision α f) := by
  have : zeroDivision α f = fun x => joinedDivision α f |x| :=
    funext (zeroDivision_eq_joinedDivision_abs hf α)
  rw [this]
  exact (continuous_joinedDivision hf α).comp continuous_abs

/-! ## Even sources and the smooth join -/

theorem ExpMomentSource.sourceTransform_eq_integral_cos {f : ℝ → ℂ} (hf : ExpMomentSource f)
    (heven : ∀ x, f (-x) = f x) (z : ℂ) :
    sourceTransform f z = 2 * ∫ t in Ioi (0 : ℝ), Complex.cos (z * t) * f t := by
  unfold sourceTransform
  rw [integral_eq_integral_Ioi_add_reflect (hf.integrable_cexp z), ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [heven, Complex.ofReal_neg]
  have hcos : Complex.cos (z * t) =
      (Complex.exp (z * t * I) + Complex.exp (-(z * t) * I)) / 2 := rfl
  rw [hcos]
  have e1 : -I * z * (t : ℂ) = -(z * t) * I := by ring
  have e2 : -I * z * -(t : ℂ) = z * t * I := by ring
  rw [e1, e2]
  ring

theorem cosineTail_neg_add {f : ℝ → ℂ} (hf : ExpMomentSource f) (heven : ∀ x, f (-x) = f x)
    (α : ℂ) (x : ℝ) :
    cosineTail α f (-x) + cosineTail α f x = sourceTransform f α := by
  rw [hf.sourceTransform_eq_integral_cos heven α]
  unfold cosineTail
  have hi := hf.integrable_cos α
  rw [setIntegral_Ioi_eq_sub hi (-x), setIntegral_Ioi_eq_sub hi x]
  have hsym : (∫ t in (0 : ℝ)..-x, Complex.cos (α * t) * f t) =
      -∫ t in (0 : ℝ)..x, Complex.cos (α * t) * f t := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := x)
      (fun t : ℝ => Complex.cos (α * t) * f t)
    simp only [neg_zero, Complex.ofReal_neg, mul_neg, Complex.cos_neg, heven] at h
    rw [intervalIntegral.integral_symm (-x) 0, ← h]
  rw [hsym]
  ring

theorem sineTail_neg {f : ℝ → ℂ} (hf : ExpMomentSource f) (heven : ∀ x, f (-x) = f x)
    (α : ℂ) (x : ℝ) : sineTail α f (-x) = sineTail α f x := by
  unfold sineTail
  have hi := hf.integrable_sin α
  rw [setIntegral_Ioi_eq_sub hi (-x), setIntegral_Ioi_eq_sub hi x]
  have hsym : (∫ t in (0 : ℝ)..-x, Complex.sin (α * t) * f t) =
      ∫ t in (0 : ℝ)..x, Complex.sin (α * t) * f t := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := x)
      (fun t : ℝ => Complex.sin (α * t) * f t)
    simp only [neg_zero, Complex.ofReal_neg, mul_neg, Complex.sin_neg, heven, neg_mul,
      intervalIntegral.integral_neg] at h
    rw [intervalIntegral.integral_symm (-x) 0, ← h, neg_neg]
  rw [hsym]

/-- At a zero of the transform, the Green solution is even. -/
theorem joinedDivision_neg {f : ℝ → ℂ} (hf : ExpMomentSource f) (heven : ∀ x, f (-x) = f x)
    {α : ℂ} (hα : sourceTransform f α = 0) (x : ℝ) :
    joinedDivision α f (-x) = joinedDivision α f x := by
  have hC := cosineTail_neg_add hf heven α x
  rw [hα] at hC
  have hC' : cosineTail α f (-x) = -cosineTail α f x := by linear_combination hC
  simp only [joinedDivision, Complex.ofReal_neg, mul_neg, Complex.cos_neg, Complex.sin_neg,
    sineTail_neg hf heven, hC']
  ring

/-- At a zero of the transform, one-sided zero division is the globally smooth Green solution. -/
theorem zeroDivision_eq_joinedDivision {f : ℝ → ℂ} (hf : ExpMomentSource f)
    (heven : ∀ x, f (-x) = f x) {α : ℂ} (hα : sourceTransform f α = 0) :
    zeroDivision α f = joinedDivision α f := by
  funext x
  rw [zeroDivision_eq_joinedDivision_abs hf]
  rcases abs_choice x with h | h <;> rw [h]
  exact joinedDivision_neg hf heven hα x

/-! ## Decay and the closed class of sources -/

theorem ExpMomentSource.norm_outwardSine_le {f : ℝ → ℂ} (hf : ExpMomentSource f) (α : ℂ)
    {B : ℝ} (hB : 0 ≤ B) {x : ℝ} (hx : 0 ≤ x) :
    ‖outwardSine α f x‖ ≤
      ‖α‖ * ((∫ s, Real.exp ((B + |α.im|) * |s|) * ‖f s‖) * Real.exp (-(B * x))) := by
  set A := B + |α.im|
  have hmom := hf.moment A
  have hshift : Integrable (fun t => Real.exp (A * |x + t|) * ‖f (x + t)‖) :=
    hmom.comp_add_left x
  have hbound : ∀ t ∈ Ioi (0 : ℝ), ‖Complex.sin (α * t) * f (x + t)‖ ≤
      Real.exp (-(B * x)) * (Real.exp (A * |x + t|) * ‖f (x + t)‖) := by
    intro t ht
    have ht0 : 0 < t := ht
    rw [norm_mul, ← mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_right ((norm_csin_mul_ofReal_le α t).trans
      (Real.exp_le_exp.mpr ?_)) (norm_nonneg _)
    rw [abs_of_pos ht0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x + t)]
    have := abs_nonneg α.im
    nlinarith
  unfold outwardSine
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖∫ t in Ioi (0 : ℝ), Complex.sin (α * t) * f (x + t)‖
      ≤ ∫ t in Ioi (0 : ℝ), ‖Complex.sin (α * t) * f (x + t)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-(B * x)) * (Real.exp (A * |x + t|) * ‖f (x + t)‖) :=
        setIntegral_mono_on (hf.integrable_sin_shift α x).integrableOn.norm
          (hshift.const_mul _).integrableOn measurableSet_Ioi hbound
    _ ≤ ∫ t, Real.exp (-(B * x)) * (Real.exp (A * |x + t|) * ‖f (x + t)‖) :=
        setIntegral_le_integral (hshift.const_mul _)
          (Eventually.of_forall fun t => by positivity)
    _ = (∫ s, Real.exp (A * |s|) * ‖f s‖) * Real.exp (-(B * x)) := by
        rw [integral_const_mul, integral_add_left_eq_self
          (fun s => Real.exp (A * |s|) * ‖f s‖) x, mul_comm]

theorem ExpMomentSource.norm_zeroDivision_le {f : ℝ → ℂ} (hf : ExpMomentSource f) (α : ℂ)
    {B : ℝ} (hB : 0 ≤ B) (x : ℝ) :
    ‖zeroDivision α f x‖ ≤
      ‖α‖ * ((∫ s, Real.exp ((B + |α.im|) * |s|) * ‖f s‖) * Real.exp (-(B * |x|))) :=
  hf.norm_outwardSine_le α hB (abs_nonneg x)

/-- One-sided zero division preserves continuity and every exponential moment. -/
theorem expMomentSource_zeroDivision {f : ℝ → ℂ} (hf : ExpMomentSource f) (α : ℂ) :
    ExpMomentSource (zeroDivision α f) := by
  refine ⟨continuous_zeroDivision hf α, fun c => ?_⟩
  set B := |c| + 1
  have hB : 0 ≤ B := by positivity
  set M := ∫ s, Real.exp ((B + |α.im|) * |s|) * ‖f s‖
  have hM : 0 ≤ M := integral_nonneg fun s => by positivity
  refine (integrable_exp_neg_abs_line.const_mul (‖α‖ * M)).mono'
    ((by fun_prop : Continuous fun x : ℝ => Real.exp (c * |x|)).mul
      (continuous_zeroDivision hf α).norm).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  have hbd := hf.norm_zeroDivision_le α hB x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hexp : Real.exp (c * |x|) * Real.exp (-(B * |x|)) ≤ Real.exp (-|x|) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have := abs_nonneg x
    have := le_abs_self c
    dsimp only [B]
    nlinarith
  calc Real.exp (c * |x|) * ‖zeroDivision α f x‖
      ≤ Real.exp (c * |x|) * (‖α‖ * (M * Real.exp (-(B * |x|)))) :=
        mul_le_mul_of_nonneg_left hbd (Real.exp_pos _).le
    _ = ‖α‖ * M * (Real.exp (c * |x|) * Real.exp (-(B * |x|))) := by ring
    _ ≤ ‖α‖ * M * Real.exp (-|x|) := mul_le_mul_of_nonneg_left hexp (by positivity)

/-! ## Smoothness and the Green equation -/

theorem deriv_sineTail {f : ℝ → ℂ} (hf : ExpMomentSource f) (α : ℂ) :
    deriv (sineTail α f) = fun x : ℝ => -(Complex.sin (α * x) * f x) :=
  funext fun x => (hasDerivAt_sineTail hf α x).deriv

theorem deriv_cosineTail {f : ℝ → ℂ} (hf : ExpMomentSource f) (α : ℂ) :
    deriv (cosineTail α f) = fun x : ℝ => -(Complex.cos (α * x) * f x) :=
  funext fun x => (hasDerivAt_cosineTail hf α x).deriv

theorem contDiff_csin_mul (α : ℂ) : ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ => Complex.sin (α * x) :=
  Complex.contDiff_sin.restrict_scalars ℝ |>.comp
    (contDiff_const.mul Complex.ofRealCLM.contDiff)

theorem contDiff_ccos_mul (α : ℂ) : ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ => Complex.cos (α * x) :=
  Complex.contDiff_cos.restrict_scalars ℝ |>.comp
    (contDiff_const.mul Complex.ofRealCLM.contDiff)

theorem contDiff_sineTail {f : ℝ → ℂ} (hf : ExpMomentSource f)
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (α : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (sineTail α f) := by
  refine contDiff_infty_iff_deriv.mpr ⟨fun x => (hasDerivAt_sineTail hf α x).differentiableAt, ?_⟩
  rw [deriv_sineTail hf]
  exact ((contDiff_csin_mul α).mul hs).neg

theorem contDiff_cosineTail {f : ℝ → ℂ} (hf : ExpMomentSource f)
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (α : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (cosineTail α f) := by
  refine contDiff_infty_iff_deriv.mpr ⟨fun x => (hasDerivAt_cosineTail hf α x).differentiableAt, ?_⟩
  rw [deriv_cosineTail hf]
  exact ((contDiff_ccos_mul α).mul hs).neg

theorem contDiff_joinedDivision {f : ℝ → ℂ} (hf : ExpMomentSource f)
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (α : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (joinedDivision α f) :=
  contDiff_const.mul (((contDiff_ccos_mul α).mul (contDiff_sineTail hf hs α)).sub
    ((contDiff_csin_mul α).mul (contDiff_cosineTail hf hs α)))

/-- The Green equation `g'' + α² g = α² f` for the globally defined solution. -/
theorem iteratedDeriv_two_joinedDivision {f : ℝ → ℂ} (hf : ExpMomentSource f) (α : ℂ) (x : ℝ) :
    iteratedDeriv 2 (joinedDivision α f) x + α ^ 2 * joinedDivision α f x = α ^ 2 * f x := by
  have h1 : deriv (joinedDivision α f) = joinedDivisionDeriv α f :=
    funext fun y => (hasDerivAt_joinedDivision hf α y).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1, (hasDerivAt_joinedDivisionDeriv hf α x).deriv]
  ring

/-- At a zero of the transform, the zero-division source is smooth and solves the Green equation
on the whole line. -/
theorem zeroDivision_smooth_green {f : ℝ → ℂ} (hf : ExpMomentSource f)
    (heven : ∀ x, f (-x) = f x) (hs : ContDiff ℝ (⊤ : ℕ∞) f) {α : ℂ}
    (hα : sourceTransform f α = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (zeroDivision α f) ∧
      ∀ x, iteratedDeriv 2 (zeroDivision α f) x + α ^ 2 * zeroDivision α f x = α ^ 2 * f x := by
  rw [zeroDivision_eq_joinedDivision hf heven hα]
  exact ⟨contDiff_joinedDivision hf hs α, iteratedDeriv_two_joinedDivision hf α⟩

/-! ## Fourier division -/

theorem hasDerivAt_ccos_mul_sub (α : ℂ) (t x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.cos (α * ((t : ℂ) - y)))
      (α * Complex.sin (α * ((t : ℂ) - x))) x := by
  have hin : HasDerivAt (fun y : ℂ => α * ((t : ℂ) - y)) (-α) (x : ℂ) := by
    simpa using ((hasDerivAt_id (x : ℂ)).const_sub (t : ℂ)).const_mul α
  exact ((Complex.hasDerivAt_cos _).comp (x : ℂ) hin).comp_ofReal.congr_deriv (by ring)

theorem hasDerivAt_csin_mul_sub (α : ℂ) (t x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.sin (α * ((t : ℂ) - y)))
      (-(α * Complex.cos (α * ((t : ℂ) - x)))) x := by
  have hin : HasDerivAt (fun y : ℂ => α * ((t : ℂ) - y)) (-α) (x : ℂ) := by
    simpa using ((hasDerivAt_id (x : ℂ)).const_sub (t : ℂ)).const_mul α
  exact ((Complex.hasDerivAt_sin _).comp (x : ℂ) hin).comp_ofReal.congr_deriv (by ring)

/-- The elementary kernel identity behind Fourier division. -/
theorem integral_cos_mul_sin_sub (z α : ℂ) (t : ℝ) :
    (α ^ 2 - z ^ 2) * ∫ x in (0 : ℝ)..t, Complex.cos (z * x) * Complex.sin (α * ((t : ℂ) - x)) =
      α * (Complex.cos (z * t) - Complex.cos (α * t)) := by
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) t, HasDerivAt
      (fun y : ℝ => α * Complex.cos (z * y) * Complex.cos (α * ((t : ℂ) - y)) -
        z * Complex.sin (z * y) * Complex.sin (α * ((t : ℂ) - y)))
      ((α ^ 2 - z ^ 2) * (Complex.cos (z * x) * Complex.sin (α * ((t : ℂ) - x)))) x := by
    intro x _
    have h := (((hasDerivAt_ccos_mul z x).const_mul α).mul (hasDerivAt_ccos_mul_sub α t x)).sub
      (((hasDerivAt_csin_mul z x).const_mul z).mul (hasDerivAt_csin_mul_sub α t x))
    exact h.congr_deriv (by ring)
  have hcont : Continuous fun x : ℝ =>
      (α ^ 2 - z ^ 2) * (Complex.cos (z * x) * Complex.sin (α * ((t : ℂ) - x))) := by fun_prop
  rw [← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.cos_zero, Complex.sin_zero, sub_zero, mul_one,
    sub_self, zero_mul]
  ring

/-- Fubini on the triangle `0 < x < t` for the cosine transform of the outward Green solution. -/
theorem ExpMomentSource.integral_cos_mul_outwardSine {f : ℝ → ℂ} (hf : ExpMomentSource f)
    (z α : ℂ) :
    (∫ x in Ioi (0 : ℝ), Complex.cos (z * x) * outwardSine α f x) =
      α * ∫ t in Ioi (0 : ℝ),
        (∫ x in (0 : ℝ)..t, Complex.cos (z * x) * Complex.sin (α * ((t : ℂ) - x))) * f t := by
  classical
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let K : ℝ → ℝ → ℂ := fun x t =>
    if x < t then Complex.cos (z * x) * Complex.sin (α * ((t : ℂ) - x)) * f t else 0
  set A := |z.im| + |α.im|
  have hG1 : Integrable (fun x : ℝ => Real.exp (-1 * x)) μ :=
    integrableOn_exp_mul_Ioi (by norm_num) 0
  have hG2 : Integrable (fun t : ℝ => Real.exp ((A + 1) * t) * ‖f t‖) μ :=
    (hf.moment (A + 1)).integrableOn.congr_fun
      (fun t ht => by simp only [abs_of_pos (show (0 : ℝ) < t from ht)]) measurableSet_Ioi
  have hG := hG1.mul_prod hG2
  have hmeas : Measurable (Function.uncurry K) := by
    refine Measurable.ite (measurableSet_lt measurable_fst measurable_snd) ?_ measurable_const
    have := hf.continuous
    exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
      Complex.cos (z * p.1) * Complex.sin (α * ((p.2 : ℂ) - p.1)) * f p.2).measurable
  have hKint : Integrable (Function.uncurry K) (μ.prod μ) := by
    refine hG.mono' hmeas.aestronglyMeasurable ?_
    rw [Measure.prod_restrict]
    refine (ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioi)).mpr
      (Eventually.of_forall fun p hp => ?_)
    obtain ⟨hx, ht⟩ := hp
    have hx0 : (0 : ℝ) < p.1 := hx
    have ht0 : (0 : ℝ) < p.2 := ht
    simp only [Function.uncurry, K]
    split_ifs with hlt
    · rw [norm_mul, norm_mul]
      have hc := norm_ccos_mul_ofReal_le z p.1
      have hs : ‖Complex.sin (α * ((p.2 : ℂ) - p.1))‖ ≤ Real.exp (|α.im| * |p.2 - p.1|) := by
        have := norm_csin_mul_ofReal_le α (p.2 - p.1)
        simpa only [Complex.ofReal_sub] using this
      rw [abs_of_pos hx0] at hc
      rw [abs_of_pos (sub_pos.mpr hlt)] at hs
      have hexp : Real.exp (|z.im| * p.1) * Real.exp (|α.im| * (p.2 - p.1)) ≤
          Real.exp (-1 * p.1) * Real.exp ((A + 1) * p.2) := by
        rw [← Real.exp_add, ← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have := abs_nonneg z.im
        have := abs_nonneg α.im
        dsimp only [A]
        nlinarith
      calc ‖Complex.cos (z * p.1)‖ * ‖Complex.sin (α * ((p.2 : ℂ) - p.1))‖ * ‖f p.2‖
          ≤ Real.exp (|z.im| * p.1) * Real.exp (|α.im| * (p.2 - p.1)) * ‖f p.2‖ := by
            gcongr
        _ ≤ Real.exp (-1 * p.1) * Real.exp ((A + 1) * p.2) * ‖f p.2‖ := by gcongr
        _ = Real.exp (-1 * p.1) * (Real.exp ((A + 1) * p.2) * ‖f p.2‖) := by ring
    · rw [norm_zero]
      positivity
  have hL : ∀ x ∈ Ioi (0 : ℝ), Complex.cos (z * x) * outwardSine α f x =
      α * ∫ t in Ioi (0 : ℝ), K x t := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [outwardSine_eq_integral_Ioi]
    have hind : (fun t => K x t) = (Ioi x).indicator
        (fun t => Complex.cos (z * x) * Complex.sin (α * ((t : ℂ) - x)) * f t) := by
      funext t
      simp only [K, Set.indicator, mem_Ioi]
    rw [hind, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_right.mpr hx0.le,
      ← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  have hR : ∀ t ∈ Ioi (0 : ℝ), (∫ x in Ioi (0 : ℝ), K x t) =
      (∫ x in (0 : ℝ)..t, Complex.cos (z * x) * Complex.sin (α * ((t : ℂ) - x))) * f t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hind : (fun x => K x t) = (Iio t).indicator
        (fun x => Complex.cos (z * x) * Complex.sin (α * ((t : ℂ) - x)) * f t) := by
      funext x
      simp only [K, Set.indicator, mem_Iio]
    rw [hind, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio,
      intervalIntegral.integral_of_le ht0.le, integral_Ioc_eq_integral_Ioo, ← integral_mul_const]
  calc (∫ x in Ioi (0 : ℝ), Complex.cos (z * x) * outwardSine α f x)
      = ∫ x in Ioi (0 : ℝ), α * ∫ t in Ioi (0 : ℝ), K x t := setIntegral_congr_fun
        measurableSet_Ioi hL
    _ = α * ∫ x, ∫ t, K x t ∂μ ∂μ := integral_const_mul _ _
    _ = α * ∫ t, ∫ x, K x t ∂μ ∂μ := by rw [integral_integral_swap hKint]
    _ = α * ∫ t in Ioi (0 : ℝ),
          (∫ x in (0 : ℝ)..t, Complex.cos (z * x) * Complex.sin (α * ((t : ℂ) - x))) * f t := by
        rw [setIntegral_congr_fun measurableSet_Ioi hR]

/-- **Fourier division.**  For an even source with every exponential moment and any complex `α`,
`(α² - z²) Ĝ(z) = α² (F(z) - F(α))`, where `G` is the one-sided zero division at `α`. -/
theorem ExpMomentSource.sourceTransform_zeroDivision {f : ℝ → ℂ} (hf : ExpMomentSource f)
    (heven : ∀ x, f (-x) = f x) (α z : ℂ) :
    (α ^ 2 - z ^ 2) * sourceTransform (zeroDivision α f) z =
      α ^ 2 * (sourceTransform f z - sourceTransform f α) := by
  have hg := expMomentSource_zeroDivision hf α
  rw [hg.sourceTransform_eq_integral_cos (zeroDivision_neg α f) z,
    hf.sourceTransform_eq_integral_cos heven z, hf.sourceTransform_eq_integral_cos heven α]
  have hcongr : (∫ x in Ioi (0 : ℝ), Complex.cos (z * x) * zeroDivision α f x) =
      ∫ x in Ioi (0 : ℝ), Complex.cos (z * x) * outwardSine α f x :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx => by
      simp only [zeroDivision, abs_of_pos (show (0 : ℝ) < x from hx)]
  rw [hcongr, hf.integral_cos_mul_outwardSine z α]
  have hker : (∫ t in Ioi (0 : ℝ), (α ^ 2 - z ^ 2) *
      ((∫ x in (0 : ℝ)..t, Complex.cos (z * x) * Complex.sin (α * ((t : ℂ) - x))) * f t)) =
      ∫ t in Ioi (0 : ℝ), α * (Complex.cos (z * t) * f t - Complex.cos (α * t) * f t) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by
      rw [← mul_assoc, integral_cos_mul_sin_sub]
      ring
  rw [integral_const_mul] at hker
  rw [integral_const_mul, integral_sub (hf.integrable_cos z).integrableOn
    (hf.integrable_cos α).integrableOn] at hker
  linear_combination 2 * α * hker

/-! ## The transform is entire -/

theorem ExpMomentSource.hasDerivAt_sourceTransform {f : ℝ → ℂ} (hf : ExpMomentSource f)
    (w₀ : ℂ) :
    HasDerivAt (sourceTransform f)
      (∫ x : ℝ, (-I * x) * Complex.exp (-I * w₀ * x) * f x) w₀ := by
  set B := |w₀.im| + 1
  have hbound : Integrable (fun x : ℝ => Real.exp ((B + 1) * |x|) * ‖f x‖) := hf.moment _
  have hmeas : ∀ w : ℂ, AEStronglyMeasurable (fun x : ℝ => Complex.exp (-I * w * x) * f x) :=
    fun w => by have := hf.continuous; exact (by fun_prop : Continuous fun x : ℝ =>
      Complex.exp (-I * w * x) * f x).aestronglyMeasurable
  have hdom : ∀ᵐ x : ℝ, ∀ w ∈ Metric.ball w₀ 1,
      ‖(-I * x) * Complex.exp (-I * w * x) * f x‖ ≤ Real.exp ((B + 1) * |x|) * ‖f x‖ := by
    refine Eventually.of_forall fun x w hw => ?_
    have hdist : ‖w - w₀‖ < 1 := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hw
    have him : |w.im| ≤ B := by
      have h1 : |w.im - w₀.im| ≤ ‖w - w₀‖ := by
        simpa only [Complex.sub_im] using Complex.abs_im_le_norm (w - w₀)
      have h2 := abs_sub_abs_le_abs_sub w.im w₀.im
      dsimp only [B]; linarith
    rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_exp]
    have hre : (-I * w * (x : ℂ)).re = w.im * x := by simp [Complex.mul_re]
    rw [hre]
    have hx : |x| ≤ Real.exp |x| := by
      have := Real.add_one_le_exp |x|; linarith
    have hwx : w.im * x ≤ B * |x| := by
      calc w.im * x ≤ |w.im * x| := le_abs_self _
        _ = |w.im| * |x| := abs_mul _ _
        _ ≤ B * |x| := mul_le_mul_of_nonneg_right him (abs_nonneg x)
    have : |x| * Real.exp (w.im * x) ≤ Real.exp ((B + 1) * |x|) := by
      calc |x| * Real.exp (w.im * x) ≤ Real.exp |x| * Real.exp (B * |x|) :=
            mul_le_mul hx (Real.exp_le_exp.mpr hwx) (Real.exp_pos _).le (Real.exp_pos _).le
        _ = Real.exp ((B + 1) * |x|) := by rw [← Real.exp_add]; ring_nf
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have hderiv : ∀ᵐ x : ℝ, ∀ w ∈ Metric.ball w₀ 1, HasDerivAt
      (fun w : ℂ => Complex.exp (-I * w * x) * f x) ((-I * x) * Complex.exp (-I * w * x) * f x)
      w := by
    refine Eventually.of_forall fun x w _ => ?_
    have hlin : HasDerivAt (fun w : ℂ => -I * w * x) (-I * x) w := by
      simpa using ((hasDerivAt_id w).const_mul (-I)).mul_const (x : ℂ)
    exact ((Complex.hasDerivAt_exp _).comp w hlin).mul_const (f x) |>.congr_deriv (by ring)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds w₀ one_pos)
    (Eventually.of_forall hmeas) (hf.integrable_cexp w₀)
    (by have := hf.continuous; exact (by fun_prop : Continuous fun x : ℝ =>
      (-I * x) * Complex.exp (-I * w₀ * x) * f x).aestronglyMeasurable) hdom hbound hderiv).2

theorem ExpMomentSource.differentiable_sourceTransform {f : ℝ → ℂ} (hf : ExpMomentSource f) :
    Differentiable ℂ (sourceTransform f) :=
  fun w => (hf.hasDerivAt_sourceTransform w).differentiableAt

theorem sourceTransform_add {f g : ℝ → ℂ} (hf : ExpMomentSource f) (hg : ExpMomentSource g)
    (z : ℂ) : sourceTransform (fun x => f x + g x) z = sourceTransform f z + sourceTransform g z := by
  unfold sourceTransform
  rw [← integral_add (hf.integrable_cexp z) (hg.integrable_cexp z)]
  exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)

theorem sourceTransform_const_mul (c : ℂ) (f : ℝ → ℂ) (z : ℂ) :
    sourceTransform (fun x => c * f x) z = c * sourceTransform f z := by
  unfold sourceTransform
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)

/-! ## The completed theta source -/

/-- The completed theta source `k` as a complex-valued function. -/
def thetaSourceC (x : ℝ) : ℂ := (thetaCuspFullSource x : ℂ)

theorem expMomentSource_thetaSourceC : ExpMomentSource thetaSourceC := by
  refine ⟨Complex.continuous_ofReal.comp contDiff_thetaCuspFullSource.continuous, fun c => ?_⟩
  refine (HedenmalmThetaSource.integrable_exp_abs_mul_thetaCuspFullSource c).congr
    (Eventually.of_forall fun x => ?_)
  simp only [thetaSourceC, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (thetaCuspFullSource_pos x)]

theorem thetaSourceC_neg (x : ℝ) : thetaSourceC (-x) = thetaSourceC x := by
  simp only [thetaSourceC, thetaCuspFullSource_neg]

theorem contDiff_thetaSourceC : ContDiff ℝ (⊤ : ℕ∞) thetaSourceC :=
  Complex.ofRealCLM.contDiff.comp contDiff_thetaCuspFullSource

/-- The transform of the completed theta source is `XiC` on the whole plane. -/
theorem sourceTransform_thetaSourceC (z : ℂ) : sourceTransform thetaSourceC z = XiC z :=
  HedenmalmThetaSource.thetaCuspFourierLaplace_eq_XiC_all z

/-! ## Real zero division of the theta source -/

/-- The real one-sided zero division `g_γ(x) = γ ∫₀^∞ sin(γt) k(|x|+t) dt`. -/
def thetaZeroDivision (γ x : ℝ) : ℝ :=
  γ * ∫ t in Ioi (0 : ℝ), Real.sin (γ * t) * thetaCuspFullSource (|x| + t)

theorem zeroDivision_thetaSourceC_ofReal (γ x : ℝ) :
    zeroDivision (γ : ℂ) thetaSourceC x = (thetaZeroDivision γ x : ℂ) := by
  unfold zeroDivision outwardSine thetaZeroDivision
  rw [Complex.ofReal_mul, ← integral_complex_ofReal]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [thetaSourceC, Complex.ofReal_mul, Complex.ofReal_sin]

theorem thetaZeroDivision_neg (γ x : ℝ) : thetaZeroDivision γ (-x) = thetaZeroDivision γ x := by
  simp only [thetaZeroDivision, abs_neg]

theorem deriv_thetaCuspFullSource_neg_of_pos {s : ℝ} (hs : 0 < s) :
    deriv thetaCuspFullSource s < 0 := by
  have h := deriv_thetaCuspLogSource_neg_of_pos hs
  rw [deriv_thetaCuspLogSource_eq, iteratedDeriv_one] at h
  exact (div_neg_iff.mp h).resolve_left (fun h' => absurd h'.2 (not_lt.mpr
    (thetaCuspFullSource_pos s).le)) |>.1

theorem integrable_deriv_thetaCuspFullSource : Integrable (deriv thetaCuspFullSource) := by
  refine (integrable_exp_abs_mul_abs_iteratedDeriv_thetaCuspFullSource 1 0).mono'
    (contDiff_thetaCuspFullSource.continuous_deriv (by simp)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  simp [iteratedDeriv_one]

/-- Integration by parts against the nonnegative primitive `1 - cos(γt)`. -/
theorem thetaSineIntegral_eq_integral_one_sub_cos (γ y : ℝ) :
    γ * ∫ t in Ioi (0 : ℝ), Real.sin (γ * t) * thetaCuspFullSource (y + t) =
      ∫ t in Ioi (0 : ℝ), (1 - Real.cos (γ * t)) * -deriv thetaCuspFullSource (y + t) := by
  have hk : Integrable thetaCuspFullSource :=
    (HedenmalmThetaSource.integrable_exp_abs_mul_thetaCuspFullSource 0).congr
      (Eventually.of_forall fun x => by simp)
  have hkd : Differentiable ℝ thetaCuspFullSource :=
    contDiff_thetaCuspFullSource.differentiable (by simp)
  have hu : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t => 1 - Real.cos (γ * t))
      (γ * Real.sin (γ * t)) t := by
    intro t _
    have h := ((Real.hasDerivAt_cos (γ * t)).comp t ((hasDerivAt_id t).const_mul γ)).const_sub 1
    exact h.congr_deriv (by simp only [mul_one]; ring)
  have hv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t => thetaCuspFullSource (y + t))
      (deriv thetaCuspFullSource (y + t)) t := by
    intro t _
    have h := (hkd (y + t)).hasDerivAt.comp t ((hasDerivAt_id t).const_add y)
    exact h.congr_deriv (by simp)
  have hvd : Integrable (fun t => deriv thetaCuspFullSource (y + t)) :=
    integrable_deriv_thetaCuspFullSource.comp_add_left y
  have hvi : Integrable (fun t => thetaCuspFullSource (y + t)) := hk.comp_add_left y
  have huv' : IntegrableOn ((fun t => 1 - Real.cos (γ * t)) *
      fun t => deriv thetaCuspFullSource (y + t)) (Ioi 0) := by
    refine (hvd.norm.const_mul 2).integrableOn.mono'
      ((by fun_prop : Continuous fun t : ℝ => 1 - Real.cos (γ * t)).aestronglyMeasurable.mul
        hvd.aestronglyMeasurable).restrict (Eventually.of_forall fun t => ?_)
    simp only [Pi.mul_apply, norm_mul, Real.norm_eq_abs]
    have : |1 - Real.cos (γ * t)| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith [Real.neg_one_le_cos (γ * t), Real.cos_le_one (γ * t)]
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have hu'v : IntegrableOn ((fun t => γ * Real.sin (γ * t)) *
      fun t => thetaCuspFullSource (y + t)) (Ioi 0) := by
    refine (hvi.const_mul |γ|).integrableOn.mono'
      ((by fun_prop : Continuous fun t : ℝ => γ * Real.sin (γ * t)).aestronglyMeasurable.mul
        hvi.aestronglyMeasurable).restrict (Eventually.of_forall fun t => ?_)
    simp only [Pi.mul_apply, norm_mul, Real.norm_eq_abs]
    have := Real.abs_sin_le_one (γ * t)
    have hk0 := (thetaCuspFullSource_pos (y + t)).le
    rw [abs_of_nonneg hk0]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (abs_nonneg γ) this) hk0
  have hcont : Continuous ((fun t => 1 - Real.cos (γ * t)) * fun t => thetaCuspFullSource (y + t)) :=
    (by fun_prop : Continuous fun t : ℝ => 1 - Real.cos (γ * t)).mul
      (contDiff_thetaCuspFullSource.continuous.comp (continuous_const.add continuous_id))
  have hzero : Tendsto ((fun t => 1 - Real.cos (γ * t)) * fun t => thetaCuspFullSource (y + t))
      (𝓝[>] 0) (𝓝 0) := by
    have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have hinf : Tendsto ((fun t => 1 - Real.cos (γ * t)) * fun t => thetaCuspFullSource (y + t))
      atTop (𝓝 0) := by
    have hk0 : Tendsto (fun t => thetaCuspFullSource (y + t)) atTop (𝓝 0) :=
      tendsto_thetaCuspFullSource_atTop_zero.comp (tendsto_atTop_add_const_left _ y tendsto_id)
    refine squeeze_zero_norm (fun t => ?_) (by simpa using hk0.const_mul 2)
    simp only [Pi.mul_apply, norm_mul, Real.norm_eq_abs]
    have : |1 - Real.cos (γ * t)| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith [Real.neg_one_le_cos (γ * t), Real.cos_le_one (γ * t)]
    rw [abs_of_pos (thetaCuspFullSource_pos (y + t))]
    exact mul_le_mul_of_nonneg_right this (thetaCuspFullSource_pos _).le
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v hzero hinf
  simp only [sub_zero, zero_sub] at h
  rw [← integral_const_mul]
  have e1 : (∫ t in Ioi (0 : ℝ), (1 - Real.cos (γ * t)) * -deriv thetaCuspFullSource (y + t)) =
      -∫ t in Ioi (0 : ℝ), (1 - Real.cos (γ * t)) * deriv thetaCuspFullSource (y + t) := by
    rw [← integral_neg]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
  rw [e1, h, neg_neg]
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring

/-- **Positivity of real zero division.**  For `γ > 0`, `g_γ > 0` everywhere. -/
theorem thetaZeroDivision_pos {γ : ℝ} (hγ : 0 < γ) (x : ℝ) : 0 < thetaZeroDivision γ x := by
  unfold thetaZeroDivision
  rw [thetaSineIntegral_eq_integral_one_sub_cos]
  set y := |x|
  have hy : 0 ≤ y := abs_nonneg x
  set φ : ℝ → ℝ := fun t => (1 - Real.cos (γ * t)) * -deriv thetaCuspFullSource (y + t)
  have hφnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ φ t := fun t ht =>
    mul_nonneg (by linarith [Real.cos_le_one (γ * t)])
      (neg_nonneg.mpr (deriv_thetaCuspFullSource_neg_of_pos
        (by have : (0 : ℝ) < t := ht; linarith)).le)
  have hφint : IntegrableOn φ (Ioi 0) := by
    refine (integrable_deriv_thetaCuspFullSource.comp_add_left y |>.norm.const_mul 2).integrableOn.mono'
      ((by fun_prop : Continuous fun t : ℝ => 1 - Real.cos (γ * t)).aestronglyMeasurable.mul
        (integrable_deriv_thetaCuspFullSource.comp_add_left y).aestronglyMeasurable.neg).restrict
      (Eventually.of_forall fun t => ?_)
    simp only [φ, norm_mul, norm_neg, Real.norm_eq_abs]
    have : |1 - Real.cos (γ * t)| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith [Real.neg_one_le_cos (γ * t), Real.cos_le_one (γ * t)]
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  refine (setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hφnn)) hφint).mpr ?_
  have hsub : Ioo 0 (2 * Real.pi / γ) ⊆ Function.support φ ∩ Ioi 0 := by
    intro t ⟨ht0, ht1⟩
    refine ⟨?_, ht0⟩
    have hγt : γ * t < 2 * Real.pi := by
      have := (lt_div_iff₀ hγ).mp ht1; linarith
    have hγt0 : 0 < γ * t := mul_pos hγ ht0
    have hcos : Real.cos (γ * t) ≠ 1 := fun h =>
      hγt0.ne' ((Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos]) hγt).mp h)
    have hcos' : Real.cos (γ * t) < 1 := lt_of_le_of_ne (Real.cos_le_one _) hcos
    have hd := deriv_thetaCuspFullSource_neg_of_pos (by linarith : 0 < y + t)
    exact mul_ne_zero (by linarith) (by linarith)
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo]
  simp only [sub_zero, ENNReal.ofReal_pos]
  positivity

/-! ## Relative tail bound against the theta source -/

open HedenmalmThetaSource in
theorem norm_outwardSine_thetaSourceC_le_tail (α : ℂ) {y : ℝ} (hy1 : 1 ≤ y)
    (hyα : |α.im| ≤ y) :
    ‖outwardSine α thetaSourceC y‖ ≤
      (2 * ‖α‖ * thetaEnvelopeUpper / (Real.pi * thetaEnvelopeLower)) *
        Real.exp (-(2 * y)) * thetaCuspFullSource y := by
  set r := Real.pi * Real.exp (2 * y)
  set a := |α.im| - r
  have hr2 : 2 * |α.im| ≤ r := by
    have h1 := Real.add_one_le_exp (2 * y)
    have := Real.pi_gt_three
    have : 0 ≤ Real.exp (2 * y) := (Real.exp_pos _).le
    dsimp only [r]; nlinarith [abs_nonneg α.im]
  have hrpos : 0 < r := by positivity
  have ha : a < 0 := by dsimp only [a]; have := abs_nonneg α.im; linarith
  have hU := thetaEnvelopeUpper_pos
  have hL := thetaEnvelopeLower_pos
  have hE := thetaEnvelope_pos y
  have hbound : ∀ t ∈ Ioi (0 : ℝ), ‖Complex.sin (α * t) * thetaSourceC (y + t)‖ ≤
      thetaEnvelopeUpper * thetaEnvelope y * Real.exp (a * t) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [norm_mul]
    have hs := norm_csin_mul_ofReal_le α t
    rw [abs_of_pos ht0] at hs
    have hk := thetaCuspFullSource_le_shift hy1 (by linarith : y ≤ y + t)
    rw [show y + t - y = t by ring] at hk
    have hkn : ‖thetaSourceC (y + t)‖ = thetaCuspFullSource (y + t) := by
      simp only [thetaSourceC, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (thetaCuspFullSource_pos _)]
    rw [hkn]
    calc ‖Complex.sin (α * t)‖ * thetaCuspFullSource (y + t)
        ≤ Real.exp (|α.im| * t) *
            (thetaEnvelopeUpper * thetaEnvelope y * Real.exp (-r * t)) :=
          mul_le_mul hs hk (thetaCuspFullSource_pos _).le (Real.exp_pos _).le
      _ = thetaEnvelopeUpper * thetaEnvelope y * Real.exp (a * t) := by
          rw [mul_comm, mul_assoc, ← Real.exp_add]; dsimp only [a]; ring_nf
  have hint : IntegrableOn (fun t : ℝ => thetaEnvelopeUpper * thetaEnvelope y * Real.exp (a * t))
      (Ioi 0) := (integrableOn_exp_mul_Ioi ha 0).const_mul _
  have hval : (∫ t in Ioi (0 : ℝ), thetaEnvelopeUpper * thetaEnvelope y * Real.exp (a * t)) =
      thetaEnvelopeUpper * thetaEnvelope y / (r - |α.im|) := by
    rw [integral_const_mul, integral_exp_mul_Ioi ha 0]
    simp only [mul_zero, Real.exp_zero]
    rw [show a = -(r - |α.im|) by dsimp only [a]; ring, neg_div_neg_eq]
    ring
  have hEk := thetaCuspFullSource_ge_envelope (by linarith : (0 : ℝ) < y)
  unfold outwardSine
  rw [norm_mul]
  have hI : ‖∫ t in Ioi (0 : ℝ), Complex.sin (α * t) * thetaSourceC (y + t)‖ ≤
      thetaEnvelopeUpper * thetaEnvelope y / (r - |α.im|) := by
    rw [← hval]
    exact (norm_integral_le_integral_norm _).trans (setIntegral_mono_on
      (expMomentSource_thetaSourceC.integrable_sin_shift α y).integrableOn.norm hint
      measurableSet_Ioi hbound)
  have hden : r / 2 ≤ r - |α.im| := by linarith
  have hexp : Real.exp (-(2 * y)) * Real.exp (2 * y) = 1 := by
    rw [← Real.exp_add]; simp
  have hEle : thetaEnvelope y ≤ thetaCuspFullSource y / thetaEnvelopeLower := by
    rw [le_div_iff₀ hL]; linarith
  calc ‖α‖ * ‖∫ t in Ioi (0 : ℝ), Complex.sin (α * t) * thetaSourceC (y + t)‖
      ≤ ‖α‖ * (thetaEnvelopeUpper * thetaEnvelope y / (r - |α.im|)) :=
        mul_le_mul_of_nonneg_left hI (norm_nonneg _)
    _ ≤ ‖α‖ * (thetaEnvelopeUpper * (thetaCuspFullSource y / thetaEnvelopeLower) / (r / 2)) := by
        refine mul_le_mul_of_nonneg_left (div_le_div₀ (mul_nonneg hU.le
          (div_nonneg (thetaCuspFullSource_pos y).le hL.le)) (mul_le_mul_of_nonneg_left hEle hU.le)
          (by positivity) hden) (norm_nonneg _)
    _ = (2 * ‖α‖ * thetaEnvelopeUpper / (Real.pi * thetaEnvelopeLower)) *
          (1 / Real.exp (2 * y)) * thetaCuspFullSource y := by
        dsimp only [r]; field_simp
    _ = (2 * ‖α‖ * thetaEnvelopeUpper / (Real.pi * thetaEnvelopeLower)) *
          Real.exp (-(2 * y)) * thetaCuspFullSource y := by
        rw [Real.exp_neg, one_div]

/-- **Relative bound.**  Every complex zero division of the theta source is bounded by
`C e^{-2|x|} k(x)`. -/
theorem exists_norm_zeroDivision_thetaSourceC_le (α : ℂ) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖zeroDivision α thetaSourceC x‖ ≤
      C * Real.exp (-(2 * |x|)) * thetaCuspFullSource x := by
  set x₁ := max 1 |α.im|
  set C₁ := 2 * ‖α‖ * HedenmalmThetaSource.thetaEnvelopeUpper /
    (Real.pi * HedenmalmThetaSource.thetaEnvelopeLower)
  have hC₁ : 0 ≤ C₁ := by
    have := HedenmalmThetaSource.thetaEnvelopeUpper_pos
    have := HedenmalmThetaSource.thetaEnvelopeLower_pos
    positivity
  have hcont : ContinuousOn (fun x => ‖zeroDivision α thetaSourceC x‖ /
      (Real.exp (-(2 * |x|)) * thetaCuspFullSource x)) (Icc (-x₁) x₁) := by
    refine Continuous.continuousOn ?_
    refine (continuous_zeroDivision expMomentSource_thetaSourceC α).norm.div
      ((by fun_prop : Continuous fun x : ℝ => Real.exp (-(2 * |x|))).mul
        contDiff_thetaCuspFullSource.continuous) fun x => ?_
    exact (mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos x)).ne'
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C₁ M, le_max_of_le_left hC₁, fun x => ?_⟩
  have hpos : 0 < Real.exp (-(2 * |x|)) * thetaCuspFullSource x :=
    mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos x)
  by_cases hx : |x| ≤ x₁
  · have hmem : x ∈ Icc (-x₁) x₁ := abs_le.mp hx
    have h := hM x hmem
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) hpos.le),
      div_le_iff₀ hpos] at h
    calc ‖zeroDivision α thetaSourceC x‖ ≤ M * (Real.exp (-(2 * |x|)) * thetaCuspFullSource x) := h
      _ ≤ max C₁ M * (Real.exp (-(2 * |x|)) * thetaCuspFullSource x) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hpos.le
      _ = _ := by ring
  · replace hx := not_le.mp hx
    have h1 : 1 ≤ |x| := le_trans (le_max_left _ _) hx.le
    have h2 : |α.im| ≤ |x| := le_trans (le_max_right _ _) hx.le
    have h := norm_outwardSine_thetaSourceC_le_tail α h1 h2
    have hk : thetaCuspFullSource |x| = thetaCuspFullSource x := by
      rcases abs_choice x with h' | h' <;> rw [h']
      exact thetaCuspFullSource_neg x
    rw [hk] at h
    calc ‖zeroDivision α thetaSourceC x‖ ≤ C₁ * Real.exp (-(2 * |x|)) * thetaCuspFullSource x := h
      _ ≤ max C₁ M * Real.exp (-(2 * |x|)) * thetaCuspFullSource x := by
          have := hpos.le
          have h3 : C₁ ≤ max C₁ M := le_max_left _ _
          nlinarith [mul_le_mul_of_nonneg_right h3 hpos.le]

/-- The ratio of a zero division to the theta source tends to zero at both ends. -/
theorem tendsto_zeroDivision_div_thetaCuspFullSource (α : ℂ) :
    Tendsto (fun x => ‖zeroDivision α thetaSourceC x‖ / thetaCuspFullSource x)
      (cocompact ℝ) (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_zeroDivision_thetaSourceC_le α
  have hlim : Tendsto (fun x : ℝ => C * Real.exp (-(2 * |x|))) (cocompact ℝ) (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => |x|) (cocompact ℝ) atTop :=
      (tendsto_norm_cocompact_atTop (E := ℝ)).congr fun x => Real.norm_eq_abs x
    have h2 : Tendsto (fun x : ℝ => Real.exp (-(2 * |x|))) (cocompact ℝ) (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop' (by norm_num : (0 : ℝ) < 2) |>.comp h)
    simpa using h2.const_mul C
  refine squeeze_zero (fun x => div_nonneg (norm_nonneg _) (thetaCuspFullSource_pos x).le)
    (fun x => ?_) hlim
  rw [div_le_iff₀ (thetaCuspFullSource_pos x)]
  exact hb x

/-! ## Positive flow removing one real zero pair -/

section RealZeroDivision

variable {γ : ℝ}

theorem thetaZeroDivision_eq_re (γ : ℝ) :
    thetaZeroDivision γ = fun x => (zeroDivision (γ : ℂ) thetaSourceC x).re := by
  funext x
  rw [zeroDivision_thetaSourceC_ofReal, Complex.ofReal_re]

theorem contDiff_thetaZeroDivision (hγ : XiC (γ : ℂ) = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (thetaZeroDivision γ) := by
  have h := (zeroDivision_smooth_green expMomentSource_thetaSourceC thetaSourceC_neg
    contDiff_thetaSourceC (by rw [sourceTransform_thetaSourceC]; exact hγ)).1
  rw [thetaZeroDivision_eq_re]
  exact Complex.reCLM.contDiff.comp h

/-- The real Green equation `g_γ'' + γ² g_γ = γ² k` on the whole line. -/
theorem thetaZeroDivision_green (hγ : XiC (γ : ℂ) = 0) (x : ℝ) :
    iteratedDeriv 2 (thetaZeroDivision γ) x + γ ^ 2 * thetaZeroDivision γ x =
      γ ^ 2 * thetaCuspFullSource x := by
  have h := (zeroDivision_smooth_green expMomentSource_thetaSourceC thetaSourceC_neg
    contDiff_thetaSourceC (by rw [sourceTransform_thetaSourceC]; exact hγ)).2 x
  have hfun : zeroDivision (γ : ℂ) thetaSourceC = fun u => ((thetaZeroDivision γ u : ℝ) : ℂ) :=
    funext (zeroDivision_thetaSourceC_ofReal γ)
  rw [hfun, GaloisForLFunctions.iteratedDeriv_ofReal_comp
    (contDiff_thetaZeroDivision hγ)] at h
  simp only [thetaSourceC] at h
  exact_mod_cast h

/-- Every exponential moment of `g_γ` is finite. -/
theorem integrable_exp_abs_mul_thetaZeroDivision {γ : ℝ} (hγ : 0 < γ) (c : ℝ) :
    Integrable (fun x => Real.exp (c * |x|) * thetaZeroDivision γ x) := by
  refine ((expMomentSource_zeroDivision expMomentSource_thetaSourceC (γ : ℂ)).moment c).congr
    (Eventually.of_forall fun x => ?_)
  simp only [zeroDivision_thetaSourceC_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (thetaZeroDivision_pos hγ x)]

theorem exists_thetaZeroDivision_le (γ : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x, |thetaZeroDivision γ x| ≤ C * Real.exp (-(2 * |x|)) * thetaCuspFullSource x := by
  obtain ⟨C, hC, h⟩ := exists_norm_zeroDivision_thetaSourceC_le (γ : ℂ)
  refine ⟨C, hC, fun x => ?_⟩
  have := h x
  rwa [zeroDivision_thetaSourceC_ofReal, Complex.norm_real, Real.norm_eq_abs] at this

theorem tendsto_thetaZeroDivision_div (γ : ℝ) :
    Tendsto (fun x => thetaZeroDivision γ x / thetaCuspFullSource x) (cocompact ℝ) (𝓝 0) := by
  have h := tendsto_zeroDivision_div_thetaCuspFullSource (γ : ℂ)
  simp only [zeroDivision_thetaSourceC_ofReal, Complex.norm_real, Real.norm_eq_abs] at h
  refine (tendsto_zero_iff_abs_tendsto_zero _).mpr ?_
  refine h.congr fun x => ?_
  simp only [Function.comp_apply, abs_div, abs_of_pos (thetaCuspFullSource_pos x)]

/-- The transform of the real zero division. -/
def thetaZeroDivisionTransform (γ : ℝ) (z : ℂ) : ℂ :=
  sourceTransform (zeroDivision (γ : ℂ) thetaSourceC) z

theorem differentiable_thetaZeroDivisionTransform (γ : ℝ) :
    Differentiable ℂ (thetaZeroDivisionTransform γ) :=
  (expMomentSource_zeroDivision expMomentSource_thetaSourceC (γ : ℂ)).differentiable_sourceTransform

/-- **Fourier division by one real zero pair.** `G_γ(z) (1 - z²/γ²) = XiC(z)`. -/
theorem thetaZeroDivisionTransform_mul (hγ0 : γ ≠ 0) (hγ : XiC (γ : ℂ) = 0) (z : ℂ) :
    thetaZeroDivisionTransform γ z * (1 - z ^ 2 / (γ : ℂ) ^ 2) = XiC z := by
  have h := expMomentSource_thetaSourceC.sourceTransform_zeroDivision thetaSourceC_neg (γ : ℂ) z
  rw [sourceTransform_thetaSourceC, sourceTransform_thetaSourceC, hγ, sub_zero] at h
  have hγc : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ0
  unfold thetaZeroDivisionTransform
  field_simp
  linear_combination h

theorem thetaZeroDivisionTransform_eq_div (hγ0 : γ ≠ 0) (hγ : XiC (γ : ℂ) = 0) {z : ℂ}
    (hz : z ^ 2 ≠ (γ : ℂ) ^ 2) :
    thetaZeroDivisionTransform γ z = XiC z / (1 - z ^ 2 / (γ : ℂ) ^ 2) := by
  have hγc : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ0
  have hne : (1 - z ^ 2 / (γ : ℂ) ^ 2) ≠ 0 := by
    intro h
    apply hz
    field_simp at h
    linear_combination -h
  rw [eq_div_iff hne, thetaZeroDivisionTransform_mul hγ0 hγ]

theorem thetaZeroDivisionTransform_ofReal_integral (γ : ℝ) :
    thetaZeroDivisionTransform γ 0 = ((∫ x, thetaZeroDivision γ x : ℝ) : ℂ) := by
  unfold thetaZeroDivisionTransform sourceTransform
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [zeroDivision_thetaSourceC_ofReal]

theorem XiC_zero_eq_integral : XiC 0 = ((∫ x, thetaCuspFullSource x : ℝ) : ℂ) := by
  rw [← sourceTransform_thetaSourceC]
  unfold sourceTransform
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [thetaSourceC]

/-- The zero division preserves the total mass. -/
theorem integral_thetaZeroDivision (hγ0 : γ ≠ 0) (hγ : XiC (γ : ℂ) = 0) :
    (∫ x, thetaZeroDivision γ x) = ∫ x, thetaCuspFullSource x := by
  have h := thetaZeroDivisionTransform_mul hγ0 hγ 0
  rw [thetaZeroDivisionTransform_ofReal_integral, XiC_zero_eq_integral] at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_zero,
    mul_one] at h
  exact_mod_cast h

/-- The positive source flow `k_{ε,γ} = (1-ε) k + ε g_γ`. -/
def thetaZeroDivisionFlow (γ ε x : ℝ) : ℝ :=
  (1 - ε) * thetaCuspFullSource x + ε * thetaZeroDivision γ x

theorem thetaZeroDivisionFlow_pos (hγ : 0 < γ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (x : ℝ) :
    0 < thetaZeroDivisionFlow γ ε x := by
  unfold thetaZeroDivisionFlow
  have hk := thetaCuspFullSource_pos x
  have hg := thetaZeroDivision_pos hγ x
  rcases eq_or_lt_of_le hε1 with h | h
  · subst h; simpa using hg
  · have : 0 < 1 - ε := by linarith
    positivity

theorem thetaZeroDivisionFlow_neg (γ ε x : ℝ) :
    thetaZeroDivisionFlow γ ε (-x) = thetaZeroDivisionFlow γ ε x := by
  simp only [thetaZeroDivisionFlow, thetaCuspFullSource_neg, thetaZeroDivision_neg]

theorem contDiff_thetaZeroDivisionFlow (hγ : XiC (γ : ℂ) = 0) (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (thetaZeroDivisionFlow γ ε) :=
  (contDiff_const.mul contDiff_thetaCuspFullSource).add
    (contDiff_const.mul (contDiff_thetaZeroDivision hγ))

theorem integrable_exp_abs_mul_thetaZeroDivisionFlow (hγ : 0 < γ) (ε c : ℝ) :
    Integrable (fun x => Real.exp (c * |x|) * thetaZeroDivisionFlow γ ε x) := by
  have h1 := (HedenmalmThetaSource.integrable_exp_abs_mul_thetaCuspFullSource c).const_mul (1 - ε)
  have h2 := (integrable_exp_abs_mul_thetaZeroDivision hγ c).const_mul ε
  refine (h1.add h2).congr (Eventually.of_forall fun x => ?_)
  simp only [thetaZeroDivisionFlow, Pi.add_apply]
  ring

/-- The transform of the flow. -/
def thetaZeroDivisionFlowTransform (γ ε : ℝ) (z : ℂ) : ℂ :=
  sourceTransform (fun x => ((thetaZeroDivisionFlow γ ε x : ℝ) : ℂ)) z

/-- **Exact flow factorization.** `F_{ε,γ}(z) = G_γ(z) (1 - (1-ε) z²/γ²)`. -/
theorem thetaZeroDivisionFlowTransform_eq (hγ0 : γ ≠ 0) (hγ : XiC (γ : ℂ) = 0) (ε : ℝ) (z : ℂ) :
    thetaZeroDivisionFlowTransform γ ε z =
      thetaZeroDivisionTransform γ z * (1 - (1 - ε) * z ^ 2 / (γ : ℂ) ^ 2) := by
  have hk := expMomentSource_thetaSourceC
  have hg := expMomentSource_zeroDivision hk (γ : ℂ)
  have hfun : (fun x => ((thetaZeroDivisionFlow γ ε x : ℝ) : ℂ)) =
      fun x => ((1 - ε : ℝ) : ℂ) * thetaSourceC x + (ε : ℂ) * zeroDivision (γ : ℂ) thetaSourceC x := by
    funext x
    simp only [thetaZeroDivisionFlow, zeroDivision_thetaSourceC_ofReal, thetaSourceC]
    push_cast; ring
  have hk' : ExpMomentSource fun x => ((1 - ε : ℝ) : ℂ) * thetaSourceC x :=
    ⟨continuous_const.mul hk.continuous, fun c => ((hk.moment c).const_mul ‖((1 - ε : ℝ) : ℂ)‖).congr
      (Eventually.of_forall fun x => by simp only [norm_mul]; ring)⟩
  have hg' : ExpMomentSource fun x => (ε : ℂ) * zeroDivision (γ : ℂ) thetaSourceC x :=
    ⟨continuous_const.mul hg.continuous, fun c => ((hg.moment c).const_mul ‖(ε : ℂ)‖).congr
      (Eventually.of_forall fun x => by simp only [norm_mul]; ring)⟩
  unfold thetaZeroDivisionFlowTransform
  rw [hfun, sourceTransform_add hk' hg', sourceTransform_const_mul, sourceTransform_const_mul,
    sourceTransform_thetaSourceC, ← thetaZeroDivisionTransform_mul hγ0 hγ z]
  unfold thetaZeroDivisionTransform
  push_cast
  ring

/-- The selected pair moves to `±γ/√(1-ε)`. -/
theorem thetaZeroDivisionFlowTransform_moving_zero (hγ0 : γ ≠ 0) (hγ : XiC (γ : ℂ) = 0) {ε : ℝ}
    (hε1 : ε < 1) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    thetaZeroDivisionFlowTransform γ ε ((s * γ / Real.sqrt (1 - ε) : ℝ) : ℂ) = 0 := by
  rw [thetaZeroDivisionFlowTransform_eq hγ0 hγ]
  have h1 : 0 < 1 - ε := by linarith
  have hsq : Real.sqrt (1 - ε) ^ 2 = 1 - ε := Real.sq_sqrt h1.le
  have hsq0 : Real.sqrt (1 - ε) ≠ 0 := (Real.sqrt_pos.mpr h1).ne'
  have hs2 : s ^ 2 = 1 := by rcases hs with h | h <;> simp [h]
  have : (1 - (1 - ε) * ((s * γ / Real.sqrt (1 - ε) : ℝ) : ℂ) ^ 2 / (γ : ℂ) ^ 2) = 0 := by
    have hr : ((s * γ / Real.sqrt (1 - ε) : ℝ) : ℂ) ^ 2 = ((γ ^ 2 / (1 - ε) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow]
      congr 1
      rw [div_pow, mul_pow, hs2, hsq, one_mul]
    rw [hr]
    have hreal : (1 : ℝ) - (1 - ε) * (γ ^ 2 / (1 - ε)) / γ ^ 2 = 0 := by
      field_simp
      ring
    have hc := congrArg (fun r : ℝ => (r : ℂ)) hreal
    push_cast at hc ⊢
    exact hc
  rw [this, mul_zero]

/-- The flow preserves the total mass. -/
theorem thetaZeroDivisionFlowTransform_zero (hγ0 : γ ≠ 0) (hγ : XiC (γ : ℂ) = 0) (ε : ℝ) :
    thetaZeroDivisionFlowTransform γ ε 0 = XiC 0 := by
  rw [thetaZeroDivisionFlowTransform_eq hγ0 hγ, ← thetaZeroDivisionTransform_mul hγ0 hγ 0]
  simp

theorem integral_thetaZeroDivisionFlow (hγ0 : γ ≠ 0) (hγ : XiC (γ : ℂ) = 0) (ε : ℝ) :
    (∫ x, thetaZeroDivisionFlow γ ε x) = ∫ x, thetaCuspFullSource x := by
  have h := thetaZeroDivisionFlowTransform_zero hγ0 hγ ε
  rw [XiC_zero_eq_integral] at h
  unfold thetaZeroDivisionFlowTransform sourceTransform at h
  rw [← integral_complex_ofReal] at h
  have : (∫ x : ℝ, Complex.exp (-I * 0 * x) * ((thetaZeroDivisionFlow γ ε x : ℝ) : ℂ)) =
      ((∫ x, thetaZeroDivisionFlow γ ε x : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp)
  rw [this] at h
  exact_mod_cast h

/-! ### Multiplicity bookkeeping -/

theorem analyticAt_thetaZeroDivisionTransform (γ : ℝ) (z : ℂ) :
    AnalyticAt ℂ (thetaZeroDivisionTransform γ) z :=
  (differentiable_thetaZeroDivisionTransform γ).analyticAt z

theorem analyticAt_divisionFactor (c : ℂ) (γ : ℝ) (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => 1 - c * w ^ 2 / (γ : ℂ) ^ 2) z :=
  (by fun_prop : Differentiable ℂ fun w : ℂ => 1 - c * w ^ 2 / (γ : ℂ) ^ 2).analyticAt z

/-- Away from `±γ`, every zero of `XiC` persists along the flow with at least its multiplicity. -/
theorem analyticOrderAt_XiC_le_flow (hγ0 : γ ≠ 0) (hγ : XiC (γ : ℂ) = 0) (ε : ℝ) {w : ℂ}
    (hw : w ^ 2 ≠ (γ : ℂ) ^ 2) :
    analyticOrderAt XiC w ≤ analyticOrderAt (thetaZeroDivisionFlowTransform γ ε) w := by
  have hγc : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ0
  have hXi : XiC = thetaZeroDivisionTransform γ * fun w : ℂ => 1 - 1 * w ^ 2 / (γ : ℂ) ^ 2 := by
    funext z; simp only [Pi.mul_apply, one_mul]; exact (thetaZeroDivisionTransform_mul hγ0 hγ z).symm
  have hF : thetaZeroDivisionFlowTransform γ ε =
      thetaZeroDivisionTransform γ * fun w : ℂ => 1 - ((1 - ε : ℝ) : ℂ) * w ^ 2 / (γ : ℂ) ^ 2 := by
    funext z; simp only [Pi.mul_apply]; rw [thetaZeroDivisionFlowTransform_eq hγ0 hγ]; push_cast; ring
  have hp0 : analyticOrderAt (fun w : ℂ => 1 - 1 * w ^ 2 / (γ : ℂ) ^ 2) w = 0 := by
    refine analyticOrderAt_eq_zero.mpr (Or.inr ?_)
    intro h
    apply hw
    field_simp at h
    linear_combination -h
  rw [hXi, hF, analyticOrderAt_mul (analyticAt_thetaZeroDivisionTransform γ w)
    (analyticAt_divisionFactor 1 γ w), analyticOrderAt_mul (analyticAt_thetaZeroDivisionTransform γ w)
    (analyticAt_divisionFactor _ γ w), hp0, add_zero]
  exact le_self_add

/-- At `±γ` exactly one copy of the zero is removed: `ord G + 1 = ord XiC`. -/
theorem analyticOrderAt_thetaZeroDivisionTransform_add_one (hγ0 : γ ≠ 0)
    (hγ : XiC (γ : ℂ) = 0) {w : ℂ} (hw : w = γ ∨ w = -γ) :
    analyticOrderAt (thetaZeroDivisionTransform γ) w + 1 = analyticOrderAt XiC w := by
  have hγc : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ0
  have hXi : XiC = thetaZeroDivisionTransform γ * fun w : ℂ => 1 - 1 * w ^ 2 / (γ : ℂ) ^ 2 := by
    funext z; simp only [Pi.mul_apply, one_mul]; exact (thetaZeroDivisionTransform_mul hγ0 hγ z).symm
  have hw2 : w ^ 2 = (γ : ℂ) ^ 2 := by rcases hw with h | h <;> rw [h]; ring
  have hwne : w ≠ 0 := by rcases hw with h | h <;> rw [h] <;> simpa using hγc
  have hderiv : HasDerivAt (fun w : ℂ => 1 - 1 * w ^ 2 / (γ : ℂ) ^ 2)
      (-(2 * w / (γ : ℂ) ^ 2)) w := by
    have := ((hasDerivAt_pow 2 w).const_mul (1 : ℂ)).div_const ((γ : ℂ) ^ 2) |>.const_sub 1
    exact this.congr_deriv (by push_cast; ring)
  have hp : analyticOrderAt (fun w : ℂ => 1 - 1 * w ^ 2 / (γ : ℂ) ^ 2) w = 1 := by
    refine (analyticAt_divisionFactor 1 γ w).analyticOrderAt_eq_one_of_zero_deriv_ne_zero ?_ ?_
    · simp only [one_mul, hw2]; field_simp; ring
    · rw [hderiv.deriv]
      simp only [ne_eq, neg_eq_zero, div_eq_zero_iff, mul_eq_zero, OfNat.ofNat_ne_zero,
        false_or, not_or]
      exact ⟨hwne, by simpa using hγc⟩
  rw [hXi, analyticOrderAt_mul (analyticAt_thetaZeroDivisionTransform γ w)
    (analyticAt_divisionFactor 1 γ w), hp]

/-- A simple selected zero is deleted completely at `ε = 1`. -/
theorem thetaZeroDivisionTransform_ne_zero_of_simple (hγ0 : γ ≠ 0) (hγ : XiC (γ : ℂ) = 0)
    {w : ℂ} (hw : w = γ ∨ w = -γ) (hsimple : analyticOrderAt XiC w = 1) :
    thetaZeroDivisionTransform γ w ≠ 0 := by
  have h := analyticOrderAt_thetaZeroDivisionTransform_add_one hγ0 hγ hw
  rw [hsimple] at h
  have h0 : analyticOrderAt (thetaZeroDivisionTransform γ) w = 0 := by
    generalize analyticOrderAt (thetaZeroDivisionTransform γ) w = r at h ⊢
    induction r using ENat.recTopCoe with
    | top => simp at h
    | coe n =>
      norm_cast at h ⊢
      omega
  exact (analyticOrderAt_eq_zero.mp h0).resolve_left
    (not_not.mpr (analyticAt_thetaZeroDivisionTransform γ w))

end RealZeroDivision

/-- **Unconditional instances.**  There is a positive real zero `γ` of `XiC`; its zero division is
a strictly positive source with the same mass. -/
theorem exists_positive_thetaZeroDivision :
    ∃ γ : ℝ, 0 < γ ∧ XiC (γ : ℂ) = 0 ∧ (∀ x, 0 < thetaZeroDivision γ x) ∧
      (∫ x, thetaZeroDivision γ x) = ∫ x, thetaCuspFullSource x := by
  obtain ⟨a, _, ha, _, _, hza, _⟩ := exists_two_distinct_positive_real_XiC_zeros
  exact ⟨a, ha, hza, thetaZeroDivision_pos ha, integral_thetaZeroDivision ha.ne' hza⟩

/-- Every other zero of `XiC` stays a zero of the flow transform. -/
theorem thetaZeroDivisionFlowTransform_eq_zero {γ : ℝ} (hγ0 : γ ≠ 0) (hγ : XiC (γ : ℂ) = 0)
    (ε : ℝ) {w : ℂ} (hw : XiC w = 0) (hw2 : w ^ 2 ≠ (γ : ℂ) ^ 2) :
    thetaZeroDivisionFlowTransform γ ε w = 0 := by
  rw [thetaZeroDivisionFlowTransform_eq hγ0 hγ, thetaZeroDivisionTransform_eq_div hγ0 hγ hw2, hw,
    zero_div, zero_mul]

/-- The moving pair travels strictly outward along the real axis. -/
theorem strictMonoOn_movingZero {γ : ℝ} (hγ : 0 < γ) :
    StrictMonoOn (fun ε : ℝ => γ / Real.sqrt (1 - ε)) (Iio 1) := by
  intro a ha b hb hab
  have ha' : 0 < 1 - a := by have : a < 1 := ha; linarith
  have hb' : 0 < 1 - b := by have : b < 1 := hb; linarith
  exact div_lt_div_of_pos_left hγ (Real.sqrt_pos.mpr hb')
    (Real.sqrt_lt_sqrt hb'.le (by linarith))

/-- The moving pair escapes to infinity as `ε ↑ 1`. -/
theorem tendsto_movingZero {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun ε : ℝ => γ / Real.sqrt (1 - ε)) (𝓝[<] 1) atTop := by
  have h0 : Tendsto (fun ε : ℝ => Real.sqrt (1 - ε)) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun ε : ℝ => Real.sqrt (1 - ε)) (𝓝 1) (𝓝 (Real.sqrt (1 - 1))) :=
        ((continuous_const.sub continuous_id).sqrt).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact Real.sqrt_pos.mpr (by have : ε < 1 := hε; linarith)
  exact (h0.inv_tendsto_nhdsGT_zero.const_mul_atTop hγ).congr fun ε => by
    simp only [Pi.inv_apply, div_eq_mul_inv]

end RHTower

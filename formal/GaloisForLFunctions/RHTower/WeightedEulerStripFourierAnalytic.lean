import GaloisForLFunctions.RHTower.WeightedEulerTwoRayPhragmenLindelof
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Strip Fourier transform of a two-ray decaying entire function

For an entire function `g`
satisfying the two-ray Phragmén–Lindelöf bound
`‖g z‖ ≤ K e^{-ε|Re z| + τ|Im z|}` (as produced by
`norm_le_exp_of_two_ray_exponential_decay`), the complexified Fourier
transform

`Φ(w) = ∫_ℝ g(x)·e^{-iwx} dx`

is well defined and analytic on the horizontal strip `|Im w| < ε`.

The follow-up module shifts the integration contour to prove `Φ(w) = 0` for
`|w| > τ`, and concludes `Φ ≡ 0` by the identity theorem, then `g ≡ 0` by
Fourier inversion — the vanishing form of the classical indicator inequality
that drives the carrier separation.  Everything here is unconditional.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Set

/-- Two-sided exponential decay is integrable on the line. -/
theorem integrable_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    Integrable fun x : ℝ => Real.exp (-(c * |x|)) := by
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
  have hIoi : IntegrableOn (fun x : ℝ => Real.exp (-c * x)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hc
  apply IntegrableOn.union
  · have hIci : IntegrableOn (fun x : ℝ => Real.exp (-c * x)) (Ici (-(0:ℝ))) := by
      rw [neg_zero, integrableOn_Ici_iff_integrableOn_Ioi]
      exact hIoi
    have hIic := hIci.comp_neg_Iic
    apply hIic.congr_fun _ measurableSet_Iic
    intro x hx
    rw [mem_Iic] at hx
    simp only [abs_of_nonpos hx]
    congr 1
    ring
  · apply hIoi.congr_fun _ measurableSet_Ioi
    intro x hx
    rw [mem_Ioi] at hx
    simp only [abs_of_pos hx]
    congr 1
    ring

/-- The linear weight is absorbed by halving the exponential rate. -/
theorem integrable_abs_mul_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    Integrable fun x : ℝ => |x| * Real.exp (-(c * |x|)) := by
  have hhalf : (0:ℝ) < c / 2 := by positivity
  apply Integrable.mono' ((integrable_exp_neg_mul_abs hhalf).const_mul (2 / c))
  · exact (continuous_abs.mul
      ((continuous_const.mul continuous_abs).neg.rexp)).aestronglyMeasurable
  · refine ae_of_all _ fun x => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg x) (Real.exp_nonneg _))]
    have hxle : |x| ≤ 2 / c * Real.exp (c / 2 * |x|) := by
      have h1 : c / 2 * |x| ≤ Real.exp (c / 2 * |x|) := by
        linarith [Real.add_one_le_exp (c / 2 * |x|)]
      calc |x| = 2 / c * (c / 2 * |x|) := by field_simp
        _ ≤ 2 / c * Real.exp (c / 2 * |x|) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
    calc |x| * Real.exp (-(c * |x|))
        ≤ (2 / c * Real.exp (c / 2 * |x|)) * Real.exp (-(c * |x|)) :=
          mul_le_mul_of_nonneg_right hxle (Real.exp_nonneg _)
      _ = 2 / c * Real.exp (-(c / 2 * |x|)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring

/-- Real part of the Fourier phase along the real axis. -/
theorem re_neg_I_mul_mul_ofReal (w : ℂ) (x : ℝ) :
    (-(I * w * (x : ℂ))).re = w.im * x := by
  simp [Complex.mul_re, Complex.mul_im]

/-- The strip Fourier kernel of a two-ray-bounded function is integrable for
frequencies in the open strip `|Im w| < ε`. -/
theorem integrable_stripFourier_kernel {g : ℂ → ℂ} (hgc : Continuous g)
    {K ε τ : ℝ}
    (hbound : ∀ z : ℂ, ‖g z‖ ≤ K * Real.exp (-(ε * |z.re|) + τ * |z.im|))
    {w : ℂ} (hw : |w.im| < ε) :
    Integrable fun x : ℝ => g x * Complex.exp (-(I * w * x)) := by
  have hc : 0 < ε - |w.im| := by linarith
  apply Integrable.mono' ((integrable_exp_neg_mul_abs hc).const_mul K)
  · apply Continuous.aestronglyMeasurable
    exact (hgc.comp Complex.continuous_ofReal).mul
      (Complex.continuous_exp.comp (by fun_prop))
  · refine ae_of_all _ fun x => ?_
    rw [norm_mul, Complex.norm_exp, re_neg_I_mul_mul_ofReal]
    have hb := hbound (x : ℂ)
    rw [Complex.ofReal_re, Complex.ofReal_im, abs_zero, mul_zero, add_zero] at hb
    calc ‖g (x : ℂ)‖ * Real.exp (w.im * x)
        ≤ (K * Real.exp (-(ε * |x|))) * Real.exp (w.im * x) :=
          mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
      _ = K * Real.exp (-(ε * |x|) + w.im * x) := by
          rw [mul_assoc, ← Real.exp_add]
      _ ≤ K * Real.exp (-((ε - |w.im|) * |x|)) := by
          have hK0 : 0 ≤ K :=
            le_trans (norm_nonneg (g 0)) (by simpa using hbound 0)
          apply mul_le_mul_of_nonneg_left _ hK0
          apply Real.exp_le_exp.2
          have h2 : w.im * x ≤ |w.im| * |x| := by
            calc w.im * x ≤ |w.im * x| := le_abs_self _
              _ = |w.im| * |x| := abs_mul _ _
          nlinarith [abs_nonneg x]

/-- The strip Fourier transform. -/
def stripFourier (g : ℂ → ℂ) (w : ℂ) : ℂ :=
  ∫ x : ℝ, g x * Complex.exp (-(I * w * x))

/-- **Analyticity of the strip Fourier transform**: at every frequency in the
open strip `|Im w| < ε` the transform has a complex derivative, given by
differentiation under the integral. -/
theorem hasDerivAt_stripFourier {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {K ε τ : ℝ}
    (hbound : ∀ z : ℂ, ‖g z‖ ≤ K * Real.exp (-(ε * |z.re|) + τ * |z.im|))
    {w₀ : ℂ} (hw : |w₀.im| < ε) :
    HasDerivAt (stripFourier g)
      (∫ x : ℝ, g x * (-(I * x)) * Complex.exp (-(I * w₀ * x))) w₀ := by
  have hgc : Continuous g := hg.continuous
  have hK0 : 0 ≤ K := le_trans (norm_nonneg (g 0)) (by simpa using hbound 0)
  set r : ℝ := (ε - |w₀.im|) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (w : ℂ) (x : ℝ) => g x * Complex.exp (-(I * w * x)))
    (F' := fun (w : ℂ) (x : ℝ) =>
      g x * (-(I * x)) * Complex.exp (-(I * w * x)))
    (bound := fun x : ℝ => K * (|x| * Real.exp (-(r * |x|))))
    (Metric.ball_mem_nhds w₀ hr0) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards with w
    exact ((hgc.comp Complex.continuous_ofReal).mul
      (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
  · exact integrable_stripFourier_kernel hgc hbound hw
  · apply Continuous.aestronglyMeasurable
    exact ((hgc.comp Complex.continuous_ofReal).mul (by fun_prop)).mul
      (Complex.continuous_exp.comp (by fun_prop))
  · refine ae_of_all _ fun x w hwball => ?_
    have hwim : |w.im| ≤ |w₀.im| + r := by
      rw [Metric.mem_ball, Complex.dist_eq] at hwball
      have h1 : |w.im - w₀.im| ≤ ‖w - w₀‖ := by
        rw [← Complex.sub_im]
        exact Complex.abs_im_le_norm _
      calc |w.im| = |w₀.im + (w.im - w₀.im)| := by ring_nf
        _ ≤ |w₀.im| + |w.im - w₀.im| := abs_add_le _ _
        _ ≤ |w₀.im| + r := by
            have h2 := le_of_lt hwball
            linarith
    rw [norm_mul, norm_mul, Complex.norm_exp, re_neg_I_mul_mul_ofReal]
    have hb := hbound (x : ℂ)
    rw [Complex.ofReal_re, Complex.ofReal_im, abs_zero, mul_zero, add_zero] at hb
    have hnormIx : ‖-(I * (x : ℂ))‖ = |x| := by
      rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
    rw [hnormIx]
    have hexp : Real.exp (w.im * x) ≤ Real.exp ((|w₀.im| + r) * |x|) := by
      apply Real.exp_le_exp.2
      calc w.im * x ≤ |w.im * x| := le_abs_self _
        _ = |w.im| * |x| := abs_mul _ _
        _ ≤ (|w₀.im| + r) * |x| :=
            mul_le_mul_of_nonneg_right hwim (abs_nonneg x)
    calc ‖g (x : ℂ)‖ * |x| * Real.exp (w.im * x)
        ≤ (K * Real.exp (-(ε * |x|))) * |x| * Real.exp ((|w₀.im| + r) * |x|) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hb (abs_nonneg x)) hexp
            (Real.exp_nonneg _)
          positivity
      _ = K * (|x| * Real.exp (-(ε * |x|) + (|w₀.im| + r) * |x|)) := by
          rw [show K * Real.exp (-(ε * |x|)) * |x| *
              Real.exp ((|w₀.im| + r) * |x|)
              = K * (|x| * (Real.exp (-(ε * |x|)) *
                Real.exp ((|w₀.im| + r) * |x|))) from by ring,
            ← Real.exp_add]
      _ ≤ K * (|x| * Real.exp (-(r * |x|))) := by
          apply mul_le_mul_of_nonneg_left _ hK0
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg x)
          apply Real.exp_le_exp.2
          have hεsplit : ε = |w₀.im| + 2 * r := by rw [hr]; ring
          nlinarith [abs_nonneg x]
  · exact (integrable_abs_mul_exp_neg_mul_abs hr0).const_mul K
  · refine ae_of_all _ fun x w _ => ?_
    have h1 : HasDerivAt (fun w : ℂ => -(I * (x : ℂ)) * w)
        (-(I * (x : ℂ))) w := by
      simpa using (hasDerivAt_id w).const_mul (-(I * (x : ℂ)))
    have h2 : HasDerivAt (fun w : ℂ => Complex.exp (-(I * (x : ℂ)) * w))
        (Complex.exp (-(I * (x : ℂ)) * w) * -(I * (x : ℂ))) w := h1.cexp
    have h3 : HasDerivAt (fun w : ℂ => g x * Complex.exp (-(I * (x : ℂ)) * w))
        (g x * (Complex.exp (-(I * (x : ℂ)) * w) * -(I * (x : ℂ)))) w :=
      h2.const_mul (g x)
    have hfun : (fun w : ℂ => g x * Complex.exp (-(I * (x : ℂ)) * w))
        = fun w : ℂ => g x * Complex.exp (-(I * w * (x : ℂ))) := by
      funext w
      congr 2
      ring
    rw [hfun] at h3
    convert h3 using 1
    ring

/-- The strip Fourier transform is analytic on the open strip. -/
theorem analyticOnNhd_stripFourier {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {K ε τ : ℝ}
    (hbound : ∀ z : ℂ, ‖g z‖ ≤ K * Real.exp (-(ε * |z.re|) + τ * |z.im|)) :
    AnalyticOnNhd ℂ (stripFourier g) {w : ℂ | |w.im| < ε} := by
  have hopen : IsOpen {w : ℂ | |w.im| < ε} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  apply DifferentiableOn.analyticOnNhd _ hopen
  intro w hw
  exact (hasDerivAt_stripFourier hg hbound hw).differentiableAt.differentiableWithinAt

end RHTower

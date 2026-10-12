import GaloisForLFunctions.RHTower.XiGaussianHeatPhysicalRealForm
import GaloisForLFunctions.HTGeometry.HermiteGaussianSmoothingTail

/-!
# Heat smoothing of a compactly supported source

For `a > 0` let `G_a(x) = (2πa)^{-1/2} e^{-x²/(2a)}` (`gaussHeatKernel`) and `u_a = u ⋆ G_a`
(`heatSmooth`).

* **Fourier–Laplace side** (`heatStripTransform_heatSmooth`).  `F_{u_a}(z) = e^{-az²/2} F_u(z)` for every
  complex `z`.  The weight `e^{izx}` factors through the convolution,
  `(u ⋆ G_a)(x) e^{izx} = ((u e^{iz·}) ⋆ (G_a e^{iz·}))(x)`, and `∫ G_a e^{izx} dx = e^{-az²/2}`.
* **Unit scale** (`gaussSmooth_scaled_apply`).  With `s = (2πa)^{1/2}`, `u_a(x)` is the unit-width
  Gaussian smoothing of `τ ↦ u(sτ)` evaluated at `x/s`.  So the Hermite expansion at width `s`
  applies to `u_a`.
-/

open scoped Real SchwartzMap Convolution
open Complex MeasureTheory
open GaloisForLFunctions (gaussSmooth gaussSmooth_apply coherentGauss coherentGauss_apply gaussReal)

namespace RHTower

noncomputable section

/-- The normalized heat kernel `(2πa)^{-1/2} e^{-x²/(2a)}`. -/
def gaussHeatKernel (a x : ℝ) : ℝ := (2 * π * a) ^ (-(1 / 2 : ℝ)) * Real.exp (-(x ^ 2 / (2 * a)))

/-- The heat smoothing `u_a(x) = ∫ u(t) G_a(x − t) dt`. -/
def heatSmooth (a : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t : ℝ, u t * gaussHeatKernel a (x - t)

theorem heatKernel_ofReal_eq {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ((gaussHeatKernel a x : ℝ) : ℂ) = ((2 * π * a : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) *
      gaussDeriv (1 / (2 * a)) 0 x := by
  rw [gaussHeatKernel, gaussDeriv, gaussDerivPoly, Polynomial.eval_one, one_mul, Complex.ofReal_mul,
    Complex.ofReal_cpow (by positivity), Complex.ofReal_exp]
  have e1 : ((-(1 / 2 : ℝ) : ℝ) : ℂ) = -(1 / 2 : ℂ) := by push_cast; ring
  have e2 : (((-(x ^ 2 / (2 * a))) : ℝ) : ℂ) = -(((1 / (2 * a) : ℝ) : ℂ)) * (x : ℂ) ^ 2 := by
    push_cast; ring
  rw [e1, e2]

theorem integrable_heatKernel_mul_cexp {a : ℝ} (ha : 0 < a) (z : ℂ) :
    Integrable (fun x : ℝ => ((gaussHeatKernel a x : ℝ) : ℂ) * Complex.exp (I * z * x)) := by
  have hb : 0 < 1 / (2 * a) := by positivity
  refine ((integrable_gaussDeriv_mul_cexp hb 0 z).const_mul
    (((2 * π * a : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))).congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [heatKernel_ofReal_eq ha]
  ring

/-- `∫ G_a(x) e^{izx} dx = e^{-az²/2}`. -/
theorem heatStripTransform_heatKernel {a : ℝ} (ha : 0 < a) (z : ℂ) :
    heatStripTransform (fun x => ((gaussHeatKernel a x : ℝ) : ℂ)) z = Complex.exp (-(a : ℂ) * z ^ 2 / 2) := by
  have hb : 0 < 1 / (2 * a) := by positivity
  unfold heatStripTransform
  have hfun : (fun x : ℝ => ((gaussHeatKernel a x : ℝ) : ℂ) * Complex.exp (I * z * x)) = fun x : ℝ =>
      ((2 * π * a : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) *
        (gaussDeriv (1 / (2 * a)) 0 x * Complex.exp (I * z * x)) := by
    funext x; rw [heatKernel_ofReal_eq ha]; ring
  rw [hfun, integral_const_mul, integral_gaussDeriv_mul_cexp hb 0 z, pow_zero, one_mul]
  have hpi : (π : ℂ) / ((1 / (2 * a) : ℝ) : ℂ) = ((2 * π * a : ℝ) : ℂ) := by
    push_cast; field_simp
  have hA : 0 < 2 * π * a := by positivity
  have hcp : ((2 * π * a : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * ((2 * π * a : ℝ) : ℂ) ^ (1 / 2 : ℂ) = 1 := by
    rw [← Complex.cpow_add _ _ (by exact_mod_cast hA.ne')]
    norm_num
  have hexp : Complex.exp (-z ^ 2 / (4 * ((1 / (2 * a) : ℝ) : ℂ))) =
      Complex.exp (-(a : ℂ) * z ^ 2 / 2) := by
    congr 1; push_cast; field_simp; ring
  rw [hpi, hexp, ← mul_assoc, hcp, one_mul]

/-- **The heat smoothing on the Fourier–Laplace side.**  `F_{u_a}(z) = e^{-az²/2} F_u(z)`. -/
theorem heatStripTransform_heatSmooth {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : Continuous u)
    (hcpt : HasCompactSupport u) (z : ℂ) :
    heatStripTransform (fun x => ((heatSmooth a u x : ℝ) : ℂ)) z =
      Complex.exp (-(a : ℂ) * z ^ 2 / 2) * heatStripTransform (fun x => ((u x : ℝ) : ℂ)) z := by
  set f : ℝ → ℂ := fun t => ((u t : ℝ) : ℂ) * Complex.exp (I * z * t) with hf
  set g : ℝ → ℂ := fun y => ((gaussHeatKernel a y : ℝ) : ℂ) * Complex.exp (I * z * y) with hg
  have hfi : Integrable f := by
    refine ((Complex.continuous_ofReal.comp hu).mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))).integrable_of_hasCompactSupport ?_
    exact (hcpt.comp_left Complex.ofReal_zero).mul_right
  have hgi : Integrable g := integrable_heatKernel_mul_cexp ha z
  have hconv : ∀ x : ℝ, ((heatSmooth a u x : ℝ) : ℂ) * Complex.exp (I * z * x) =
      (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) x := by
    intro x
    rw [convolution_def, heatSmooth, ← integral_complex_ofReal, ← integral_mul_const]
    congr 1
    funext t
    simp only [hf, hg, ContinuousLinearMap.mul_apply']
    have e : Complex.exp (I * z * t) * Complex.exp (I * z * ((x - t : ℝ) : ℂ)) =
        Complex.exp (I * z * x) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [Complex.ofReal_mul, ← e]
    ring
  unfold heatStripTransform
  simp_rw [hconv]
  rw [integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hfi hgi, ContinuousLinearMap.mul_apply',
    mul_comm]
  congr 1
  exact heatStripTransform_heatKernel ha z

/-- **Unit scale.**  `u_a(x)` is the unit-width Gaussian smoothing of `u(s·)` at `x/s`,
`s = (2πa)^{1/2}`. -/
theorem heatSmooth_eq_unitScale {a : ℝ} (ha : 0 < a) (u : ℝ → ℝ) (x : ℝ) :
    heatSmooth a u x = ∫ τ : ℝ, u (Real.sqrt (2 * π * a) * τ) *
      gaussReal (x / Real.sqrt (2 * π * a) - τ) := by
  set s := Real.sqrt (2 * π * a) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = 2 * π * a := Real.sq_sqrt (by positivity)
  have hsub := Measure.integral_comp_mul_left (fun t : ℝ => u t * gaussReal (x / s - t / s)) s
  have e1 : ∀ τ : ℝ, u (s * τ) * gaussReal (x / s - s * τ / s) = u (s * τ) * gaussReal (x / s - τ) :=
    fun τ => by rw [mul_div_cancel_left₀ _ hs0.ne']
  simp_rw [e1] at hsub
  rw [hsub, smul_eq_mul, abs_inv, abs_of_pos hs0, heatSmooth, ← integral_const_mul]
  congr 1
  funext t
  rw [gaussHeatKernel, gaussReal]
  have hpow : (2 * π * a) ^ (-(1 / 2 : ℝ)) = s⁻¹ := by
    rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity)]
  rw [hpow]
  have hex : -(π * (x / s - t / s) ^ 2) = -((x - t) ^ 2 / (2 * a)) := by
    field_simp
    rw [hs2]
    ring
  rw [hex]
  ring

end

end RHTower

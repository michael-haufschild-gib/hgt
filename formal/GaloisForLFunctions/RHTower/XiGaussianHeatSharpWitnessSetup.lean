import GaloisForLFunctions.RHTower.XiGaussianHeatSourceSmoothing
import GaloisForLFunctions.RHTower.XiGaussianHeatTestPolynomialBasis
import GaloisForLFunctions.RHTower.XiGaussianHeatWindowWeilMargin

/-!
# The Hermite truncation of a heat-smoothed source as a heat test

Fix a smooth real source `u` vanishing outside `[−A, A]`, a heat time `a > 0` and `s = (2πa)^{1/2}`.
The unit-scale function `w(y) = u_a(sy)` is the Gaussian smoothing of `τ ↦ u(sτ)`
(`sourceSmooth`).  Its Hermite truncation at degree `< N`, read back at scale `s`, is the real
polynomial–Gaussian `g = Q e^{-x²/(2a)}` (`truncHeatTest`), `Q` even of degree `≤ N − 1`, and it
differs from `u_a` in `L²` by `s ‖w − Π_N w‖²` (`integral_sq_truncHeatTest_sub_le`).  With
`πA²/s² ≤ θN` this is at most `(‖u‖₁²/s) ‖ψ_0‖² (θ e^{1-θ})^N/(1 − θ)`.
-/

open scoped Real SchwartzMap
open Complex MeasureTheory Polynomial
open GaloisForLFunctions (gaussSmooth gaussSmooth_apply coherentGauss coherentGauss_apply gaussReal
  gaussPolyFun hermiteTrunc hermiteTruncPoly hermiteTrunc_apply_of_real hermiteTruncPoly_comp_neg
  natDegree_hermiteTruncPoly_le hermiteCoeff_im_eq_zero_of_real hermiteCoeff_eq_zero_of_even
  norm_sq_sub_hermiteTrunc_gaussSmooth_le polyGaussSchwartz polyGaussSchwartz_apply
  norm_toLp_sq_eq_integral)

namespace RHTower

noncomputable section

/-- The scaled source `τ ↦ u(sτ)` as a Schwartz map. -/
def scaledSource (u : ℝ → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hcpt : HasCompactSupport u) {s : ℝ}
    (hs : s ≠ 0) : 𝓢(ℝ, ℂ) :=
  HasCompactSupport.toSchwartzMap (f := fun τ : ℝ => ((u (s * τ) : ℝ) : ℂ))
    ((hcpt.comp_smul hs).comp_left Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp (hu.comp (contDiff_const.mul contDiff_id)))

@[simp] theorem scaledSource_apply (u : ℝ → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcpt : HasCompactSupport u) {s : ℝ} (hs : s ≠ 0) (τ : ℝ) :
    scaledSource u hu hcpt hs τ = ((u (s * τ) : ℝ) : ℂ) := rfl

/-- The heat scale `s = (2πa)^{1/2}`. -/
def heatHermiteScale (a : ℝ) : ℝ := Real.sqrt (2 * π * a)

theorem heatHermiteScale_pos {a : ℝ} (ha : 0 < a) : 0 < heatHermiteScale a := Real.sqrt_pos.2 (by positivity)

theorem heatHermiteScale_sq {a : ℝ} (ha : 0 < a) : heatHermiteScale a ^ 2 = 2 * π * a :=
  Real.sq_sqrt (by positivity)

/-- The unit-scale smoothed source `w(y) = u_a(sy)`. -/
def sourceSmooth (u : ℝ → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hcpt : HasCompactSupport u) {a : ℝ}
    (ha : 0 < a) : 𝓢(ℝ, ℂ) :=
  gaussSmooth (scaledSource u hu hcpt (heatHermiteScale_pos ha).ne')

theorem sourceSmooth_apply (u : ℝ → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hcpt : HasCompactSupport u)
    {a : ℝ} (ha : 0 < a) (y : ℝ) :
    sourceSmooth u hu hcpt ha y = ((heatSmooth a u (heatHermiteScale a * y) : ℝ) : ℂ) := by
  rw [sourceSmooth, gaussSmooth_apply, heatSmooth_eq_unitScale ha, ← heatHermiteScale,
    mul_div_cancel_left₀ _ (heatHermiteScale_pos ha).ne', ← integral_complex_ofReal]
  congr 1
  funext τ
  rw [scaledSource_apply, coherentGauss_apply]
  push_cast
  ring

theorem heatSmooth_neg {a : ℝ} {u : ℝ → ℝ} (heven : ∀ x, u (-x) = u x) (x : ℝ) :
    heatSmooth a u (-x) = heatSmooth a u x := by
  rw [heatSmooth, heatSmooth, ← integral_neg_eq_self]
  congr 1
  funext t
  rw [heven, gaussHeatKernel, gaussHeatKernel]
  congr 3
  ring

/-- The truncated heat test `g = Q e^{-x²/(2a)}`, `Q(x) = R(x/s)` with `R` the truncation polynomial. -/
def truncHeatPoly (u : ℝ → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hcpt : HasCompactSupport u)
    {a : ℝ} (ha : 0 < a) (N : ℕ) : ℝ[X] :=
  (hermiteTruncPoly (sourceSmooth u hu hcpt ha) N).comp (C (heatHermiteScale a)⁻¹ * X)

theorem sourceSmooth_im (u : ℝ → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hcpt : HasCompactSupport u)
    {a : ℝ} (ha : 0 < a) (y : ℝ) : (sourceSmooth u hu hcpt ha y).im = 0 := by
  rw [sourceSmooth_apply, Complex.ofReal_im]

theorem hermiteTrunc_sourceSmooth_apply (u : ℝ → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcpt : HasCompactSupport u) {a : ℝ} (ha : 0 < a) (N : ℕ) (x : ℝ) :
    hermiteTrunc (sourceSmooth u hu hcpt ha) N (x / heatHermiteScale a) =
      ((gaussPolyFun (truncHeatPoly u hu hcpt ha N) (1 / (2 * a)) x : ℝ) : ℂ) := by
  rw [hermiteTrunc_apply_of_real _ N (hermiteCoeff_im_eq_zero_of_real _
    (sourceSmooth_im u hu hcpt ha)), polyGaussSchwartz_apply]
  have hs := heatHermiteScale_pos ha
  have hs2 := heatHermiteScale_sq ha
  congr 1
  rw [gaussPolyFun, truncHeatPoly, eval_comp, eval_mul, eval_C, eval_X, gaussReal]
  congr 1
  · rw [inv_mul_eq_div]
  · congr 1
    field_simp
    rw [hs2]
    ring

theorem truncHeatPoly_comp_neg (u : ℝ → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcpt : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) {a : ℝ} (ha : 0 < a) (N : ℕ) :
    (truncHeatPoly u hu hcpt ha N).comp (-X) = truncHeatPoly u hu hcpt ha N := by
  have hev : ∀ y, sourceSmooth u hu hcpt ha (-y) = sourceSmooth u hu hcpt ha y := fun y => by
    rw [sourceSmooth_apply, sourceSmooth_apply, mul_neg, heatSmooth_neg heven]
  have hL : (C (heatHermiteScale a)⁻¹ * X : ℝ[X]).comp (-X) = (-X : ℝ[X]).comp (C (heatHermiteScale a)⁻¹ * X) := by
    rw [mul_comp, C_comp, X_comp, neg_comp, X_comp, mul_neg]
  rw [truncHeatPoly, comp_assoc, hL, ← comp_assoc, hermiteTruncPoly_comp_neg _ hev]

theorem natDegree_truncHeatPoly_le (u : ℝ → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcpt : HasCompactSupport u) {a : ℝ} (ha : 0 < a) (N : ℕ) :
    (truncHeatPoly u hu hcpt ha N).natDegree ≤ N - 1 := by
  rw [truncHeatPoly, natDegree_comp]
  have h1 := natDegree_hermiteTruncPoly_le (sourceSmooth u hu hcpt ha) N
  have h2 : (C (heatHermiteScale a)⁻¹ * X : ℝ[X]).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans natDegree_X_le
  nlinarith

/-- **The `L²` error of the truncated heat test.** -/
theorem integral_sq_truncHeatTest_sub_le (u : ℝ → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcpt : HasCompactSupport u) {A : ℝ} (hsupp : ∀ t : ℝ, A < |t| → u t = 0) {a : ℝ} (ha : 0 < a)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {N : ℕ}
    (hN : π * (A / heatHermiteScale a) ^ 2 ≤ θ * N) :
    ∫ x : ℝ, (gaussPolyFun (truncHeatPoly u hu hcpt ha N) (1 / (2 * a)) x - heatSmooth a u x) ^ 2 ≤
      heatHermiteScale a * ((∫ τ : ℝ, ‖scaledSource u hu hcpt (heatHermiteScale_pos ha).ne' τ‖) ^ 2 *
        ‖(coherentGauss 0).toLp 2 (volume : Measure ℝ)‖ ^ 2 *
          ((θ * Real.exp (1 - θ)) ^ N / (1 - θ))) := by
  set sc := heatHermiteScale a with hsc
  have hs := heatHermiteScale_pos ha
  set w := sourceSmooth u hu hcpt ha with hw
  have hpt : ∀ x : ℝ, (gaussPolyFun (truncHeatPoly u hu hcpt ha N) (1 / (2 * a)) x -
      heatSmooth a u x) ^ 2 = ‖(w - hermiteTrunc w N) (sc⁻¹ * x)‖ ^ 2 := fun x => by
    rw [sub_apply, inv_mul_eq_div, hw, hermiteTrunc_sourceSmooth_apply, sourceSmooth_apply,
      mul_div_cancel₀ _ hs.ne', ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  simp_rw [hpt]
  rw [Measure.integral_comp_mul_left (fun y => ‖(w - hermiteTrunc w N) y‖ ^ 2) sc⁻¹, inv_inv,
    abs_of_pos hs, smul_eq_mul, ← norm_toLp_sq_eq_integral]
  gcongr
  exact norm_sq_sub_hermiteTrunc_gaussSmooth_le _ (fun τ hτ => by
    rw [scaledSource_apply, hsupp _ (by
      rw [abs_mul, abs_of_pos hs]
      rwa [div_lt_iff₀ hs, mul_comm] at hτ), Complex.ofReal_zero]) hθ0 hθ1 hN

end

end RHTower

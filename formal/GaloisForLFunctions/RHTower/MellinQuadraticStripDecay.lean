import GaloisForLFunctions.RHTower.DeningerMeyerXiCofinalSynthesisSingularity
import GaloisForLFunctions.RHTower.StripHorizontalShift

/-!
# Uniform quadratic Mellin decay on bounded vertical strips

Two integrations by parts give quadratic decay for the entire logarithmic Mellin transform of an
all-weight smooth source.  The existing all-orders estimate is pointwise in the real part of the
spectral parameter.  Contour shifting needs one majorant valid across a whole bounded strip.

This file supplies that missing uniform form.  It expands the second weighted Euler derivative
exactly and bounds it by one integrable function independent of the strip height.  Consequently,

`‖M_g(σ + iτ)‖ ≤ C(g,c) / (1 + τ²)` for `0 ≤ σ ≤ c`.

Compactly supported smooth functions enter through `DeningerMeyerStrongLogTarget`, so this is the
precise rapid-strip-decay input used in Suzuki's kernel-to-spectral identification.
-/

open Complex Filter Function Set Topology MeasureTheory
open scoped Classical FourierTransform

namespace RHTower

noncomputable section

/-- Exact second derivative of an exponentially weighted logarithmic source. -/
theorem iteratedDeriv_two_deningerMeyerWeightedLogProfile
    (g : DeningerMeyerStrongLogTarget) (sigma t : ℝ) :
    iteratedDeriv 2 (deningerMeyerWeightedLogProfile sigma g) t =
      (Real.exp (sigma * t) : ℂ) *
        ((sigma : ℂ) ^ 2 * (g : ℝ → ℂ) t +
          2 * (sigma : ℂ) * deriv (g : ℝ → ℂ) t +
          iteratedDeriv 2 (g : ℝ → ℂ) t) := by
  rw [iteratedDeriv_deningerMeyerWeightedLogProfile g.property sigma 2]
  simp only [deningerMeyerWeightedLogProfile, deningerMeyerWeightedEulerIterate,
    deningerMeyerWeightedEuler, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hderiv : deriv ((sigma : ℂ) • (g : ℝ → ℂ) + deriv g) t =
      (sigma : ℂ) * deriv g t + iteratedDeriv 2 g t := by
    rw [deriv_add, deriv_const_smul]
    · simp [iteratedDeriv_succ]
    · exact (g.property.smooth.differentiable (by simp)) t
    · exact ((g.property.smooth.differentiable (by simp)).const_smul (sigma : ℂ)) t
    · exact (g.property.smooth.of_le
        (WithTop.coe_le_coe.mpr le_top :
          (2 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))).differentiable_deriv_two t
  rw [hderiv]
  ring

/-- Order-zero uniform majorant on the strip `0 ≤ Re s ≤ c`. -/
def deningerMeyerQuadraticStripMajorant0
    (c : ℝ) (g : ℝ → ℂ) (t : ℝ) : ℝ :=
  Real.exp (c * |t|) * ‖g t‖

/-- Order-two uniform majorant on the strip `0 ≤ Re s ≤ c`. -/
def deningerMeyerQuadraticStripMajorant2
    (c : ℝ) (g : ℝ → ℂ) (t : ℝ) : ℝ :=
  Real.exp (c * |t|) *
    (c ^ 2 * ‖g t‖ + 2 * c * ‖deriv g t‖ + ‖iteratedDeriv 2 g t‖)

theorem integrable_deningerMeyerQuadraticStripMajorant0
    (g : DeningerMeyerStrongLogTarget) (c : ℝ) :
    Integrable (deningerMeyerQuadraticStripMajorant0 c g) := by
  convert integrable_deningerMeyerStrongLogAbsMoment g.property 0 c using 1
  funext t
  simp [deningerMeyerQuadraticStripMajorant0]

theorem integrable_deningerMeyerQuadraticStripMajorant2
    (g : DeningerMeyerStrongLogTarget) (c : ℝ) :
    Integrable (deningerMeyerQuadraticStripMajorant2 c g) := by
  have h0 :=
    (integrable_deningerMeyerStrongLogAbsMoment g.property 0 c).const_mul (c ^ 2)
  have h1 :=
    (integrable_deningerMeyerStrongLogAbsMoment g.property.deriv 0 c).const_mul (2 * c)
  have h2base :=
    integrable_deningerMeyerStrongLogAbsMoment g.property.deriv.deriv 0 c
  have h2 : Integrable (fun t : ℝ =>
      Real.exp (c * |t|) * ‖iteratedDeriv 2 (g : ℝ → ℂ) t‖) := by
    convert h2base using 1
    funext t
    simp [iteratedDeriv_succ]
  apply (h0.add h1 |>.add h2).congr
  filter_upwards with t
  simp only [deningerMeyerQuadraticStripMajorant2, pow_zero, one_mul, Pi.add_apply]
  ring

theorem norm_iteratedDeriv_two_deningerMeyerWeightedLogProfile_le
    (g : DeningerMeyerStrongLogTarget) {c sigma : ℝ}
    (hc : 0 ≤ c) (hsigma0 : 0 ≤ sigma) (hsigmac : sigma ≤ c) (t : ℝ) :
    ‖iteratedDeriv 2 (deningerMeyerWeightedLogProfile sigma g) t‖ ≤
      deningerMeyerQuadraticStripMajorant2 c g t := by
  rw [iteratedDeriv_two_deningerMeyerWeightedLogProfile]
  have hst : sigma * t ≤ c * |t| := by
    calc
      sigma * t ≤ |sigma * t| := le_abs_self _
      _ = sigma * |t| := by rw [abs_mul, abs_of_nonneg hsigma0]
      _ ≤ c * |t| := mul_le_mul_of_nonneg_right hsigmac (abs_nonneg t)
  have hexp : Real.exp (sigma * t) ≤ Real.exp (c * |t|) :=
    Real.exp_le_exp.mpr hst
  have hs2 : sigma ^ 2 ≤ c ^ 2 := (sq_le_sq₀ hsigma0 hc).mpr hsigmac
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  rw [deningerMeyerQuadraticStripMajorant2]
  calc
    Real.exp (sigma * t) *
        ‖(sigma : ℂ) ^ 2 * (g : ℝ → ℂ) t +
          2 * (sigma : ℂ) * deriv (g : ℝ → ℂ) t +
          iteratedDeriv 2 (g : ℝ → ℂ) t‖ ≤
      Real.exp (sigma * t) *
        (sigma ^ 2 * ‖(g : ℝ → ℂ) t‖ +
          2 * sigma * ‖deriv (g : ℝ → ℂ) t‖ +
          ‖iteratedDeriv 2 (g : ℝ → ℂ) t‖) := by
        gcongr
        calc
          ‖(sigma : ℂ) ^ 2 * (g : ℝ → ℂ) t +
              2 * (sigma : ℂ) * deriv (g : ℝ → ℂ) t +
              iteratedDeriv 2 (g : ℝ → ℂ) t‖ ≤
            (‖(sigma : ℂ) ^ 2 * (g : ℝ → ℂ) t‖ +
              ‖2 * (sigma : ℂ) * deriv (g : ℝ → ℂ) t‖ +
              ‖iteratedDeriv 2 (g : ℝ → ℂ) t‖) := by
                calc
                  _ ≤ ‖(sigma : ℂ) ^ 2 * (g : ℝ → ℂ) t +
                        2 * (sigma : ℂ) * deriv (g : ℝ → ℂ) t‖ +
                      ‖iteratedDeriv 2 (g : ℝ → ℂ) t‖ := norm_add_le _ _
                  _ ≤ _ := by
                    gcongr
                    exact norm_add_le _ _
          _ = _ := by
            simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hsigma0, norm_ofNat]
    _ ≤ Real.exp (c * |t|) *
        (c ^ 2 * ‖(g : ℝ → ℂ) t‖ +
          2 * c * ‖deriv (g : ℝ → ℂ) t‖ +
          ‖iteratedDeriv 2 (g : ℝ → ℂ) t‖) := by
      apply mul_le_mul hexp
      · exact add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_right hs2 (norm_nonneg _))
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsigmac (by norm_num)) (norm_nonneg _)))
          le_rfl
      · positivity
      · positivity

/-- Uniform quadratic decay of the entire logarithmic Mellin transform on a bounded vertical
strip.  The constant is explicit as the sum of the order-zero and order-two majorant integrals. -/
theorem norm_deningerMeyerStrongLogMellin_le_inv_one_add_sq
    (g : DeningerMeyerStrongLogTarget) {c sigma : ℝ}
    (hc : 0 ≤ c) (hsigma0 : 0 ≤ sigma) (hsigmac : sigma ≤ c) (tau : ℝ) :
    ‖deningerMeyerStrongLogMellin g
        ((sigma : ℂ) + (tau : ℂ) * Complex.I)‖ ≤
      ((∫ t : ℝ, deningerMeyerQuadraticStripMajorant0 c g t) +
        ∫ t : ℝ, deningerMeyerQuadraticStripMajorant2 c g t) *
          (1 + tau ^ 2)⁻¹ := by
  have h0 :=
    abs_im_pow_mul_norm_deningerMeyerStrongLogMellin_le g 0 sigma tau
  have h2 :=
    abs_im_pow_mul_norm_deningerMeyerStrongLogMellin_le g 2 sigma tau
  have hi0 : (∫ t : ℝ,
      ‖iteratedDeriv 0 (deningerMeyerWeightedLogProfile sigma g) t‖) ≤
      ∫ t : ℝ, deningerMeyerQuadraticStripMajorant0 c g t := by
    apply integral_mono
    · exact integrable_deningerMeyerWeightedLogProfile g.property sigma |>.norm
    · exact integrable_deningerMeyerQuadraticStripMajorant0 g c
    · intro t
      simp only [iteratedDeriv_zero, deningerMeyerWeightedLogProfile, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        deningerMeyerQuadraticStripMajorant0]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      calc
        sigma * t ≤ |sigma * t| := le_abs_self _
        _ = sigma * |t| := by rw [abs_mul, abs_of_nonneg hsigma0]
        _ ≤ c * |t| := mul_le_mul_of_nonneg_right hsigmac (abs_nonneg t)
  have hi2 : (∫ t : ℝ,
      ‖iteratedDeriv 2 (deningerMeyerWeightedLogProfile sigma g) t‖) ≤
      ∫ t : ℝ, deningerMeyerQuadraticStripMajorant2 c g t := by
    apply integral_mono
    · exact
        integrable_iteratedDeriv_deningerMeyerWeightedLogProfile g.property sigma 2 |>.norm
    · exact integrable_deningerMeyerQuadraticStripMajorant2 g c
    · exact
        norm_iteratedDeriv_two_deningerMeyerWeightedLogProfile_le
          g hc hsigma0 hsigmac
  have hsum : (1 + tau ^ 2) *
      ‖deningerMeyerStrongLogMellin g
        ((sigma : ℂ) + (tau : ℂ) * Complex.I)‖ ≤
      (∫ t : ℝ, deningerMeyerQuadraticStripMajorant0 c g t) +
        ∫ t : ℝ, deningerMeyerQuadraticStripMajorant2 c g t := by
    calc
      (1 + tau ^ 2) * ‖deningerMeyerStrongLogMellin g
          ((sigma : ℂ) + (tau : ℂ) * Complex.I)‖ =
        1 * ‖deningerMeyerStrongLogMellin g
          ((sigma : ℂ) + (tau : ℂ) * Complex.I)‖ +
        |tau| ^ 2 * ‖deningerMeyerStrongLogMellin g
          ((sigma : ℂ) + (tau : ℂ) * Complex.I)‖ := by
            rw [sq_abs]
            ring
      _ ≤ (∫ t : ℝ, deningerMeyerQuadraticStripMajorant0 c g t) +
          ∫ t : ℝ, deningerMeyerQuadraticStripMajorant2 c g t :=
        add_le_add (h0.trans hi0) (h2.trans hi2)
  rw [le_mul_inv_iff₀ (by positivity : 0 < 1 + tau ^ 2)]
  simpa [mul_comm] using hsum

end

end RHTower

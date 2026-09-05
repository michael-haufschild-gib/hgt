import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaBreatherPhysicalScaling
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Spatial localization of the Ma breather

Equation (36) is localized in space: at either spatial infinity its rational core tends to `-1`,
so the complex field approaches the plane-wave carrier with background magnitude `1/sqrt 2`.
This module supplies the missing real `cosh` divergence bridge and proves both one-sided limits.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

open Filter

theorem tendsto_cosh_positive_mul_atTop (p : PositiveScale) :
    Tendsto (fun x : ℝ => Real.cosh ((p : ℝ) * x)) atTop atTop := by
  have hexp : Tendsto (fun x : ℝ => Real.exp ((p : ℝ) * x) / 2) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop p.property)).atTop_div_const
      (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ hexp
  filter_upwards with x
  rw [Real.cosh_eq]
  linarith [Real.exp_pos (-((p : ℝ) * x))]

theorem tendsto_positive_cosh_mul_atTop (c p : PositiveScale) :
    Tendsto (fun x : ℝ => (c : ℝ) * Real.cosh ((p : ℝ) * x)) atTop atTop :=
  (tendsto_cosh_positive_mul_atTop p).const_mul_atTop c.property

private theorem tendsto_complex_affine_ratio_div_atTop
    (A : ℝ → ℝ) (hA : Tendsto A atTop atTop) (hApos : ∀ x, 0 < A x)
    (B : ℂ) (y : ℝ) :
    Tendsto (fun x => ((((A x : ℝ) : ℂ) - B) / (((A x - y : ℝ) : ℂ))))
      atTop (nhds 1) := by
  have hinvR : Tendsto (fun x => (A x)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hA
  have hinvC : Tendsto (fun x => (((A x)⁻¹ : ℝ) : ℂ)) atTop (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hinvR
  have hnum : Tendsto (fun x => (1 : ℂ) - B * (((A x)⁻¹ : ℝ) : ℂ))
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hinvC)
  have hden : Tendsto (fun x => (1 : ℂ) - (y : ℂ) * (((A x)⁻¹ : ℝ) : ℂ))
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hinvC)
  have hquot := hnum.div hden (by norm_num : (1 : ℂ) ≠ 0)
  have hquot' : Tendsto
      ((fun x => (1 : ℂ) - B * (((A x)⁻¹ : ℝ) : ℂ)) /
        fun x => (1 : ℂ) - (y : ℂ) * (((A x)⁻¹ : ℝ) : ℂ)) atTop (nhds 1) := by
    simpa using hquot
  apply hquot'.congr'
  filter_upwards with x
  have hne : A x ≠ 0 := ne_of_gt (hApos x)
  change ((1 : ℂ) - B * (((A x)⁻¹ : ℝ) : ℂ)) /
      ((1 : ℂ) - (y : ℂ) * (((A x)⁻¹ : ℝ) : ℂ)) =
    (((A x : ℝ) : ℂ) - B) / (((A x - y : ℝ) : ℂ))
  push_cast
  field_simp [hne]

noncomputable def maLeadingScale (φ : MaAngle) (ξ : ℝ) : ℝ :=
  Real.cosh (φ : ℝ) * Real.cosh (maWaveNumber φ * ξ)

noncomputable def maNumeratorOffset (φ : MaAngle) (τ : ℝ) : ℂ :=
  ((Real.cos (maOmega φ * τ) * Real.cosh (2 * (φ : ℝ)) : ℝ) : ℂ) +
    Complex.I * ((Real.sin (maOmega φ * τ) * Real.sinh (2 * (φ : ℝ)) : ℝ) : ℂ)

theorem maNumerator_as_leading_sub_offset (φ : MaAngle) (ξ τ : ℝ) :
    maNumerator φ ξ τ =
      (maLeadingScale φ ξ : ℂ) - maNumeratorOffset φ τ := by
  rw [maNumerator, maLeadingScale, maNumeratorOffset]
  push_cast
  ring

theorem maDenominator_as_leading_sub_offset (φ : MaAngle) (ξ τ : ℝ) :
    maDenominator φ ξ τ = maLeadingScale φ ξ - Real.cos (maOmega φ * τ) := by
  rfl

theorem maLeadingScale_pos (φ : MaAngle) (ξ : ℝ) : 0 < maLeadingScale φ ξ := by
  exact mul_pos (Real.cosh_pos _) (Real.cosh_pos _)

theorem tendsto_maLeadingScale_atTop (φ : MaAngle) :
    Tendsto (maLeadingScale φ) atTop atTop := by
  let c : PositiveScale := ⟨Real.cosh (φ : ℝ), Real.cosh_pos _⟩
  let p : PositiveScale := ⟨maWaveNumber φ, maWaveNumber_pos φ⟩
  change Tendsto (fun x => Real.cosh (φ : ℝ) * Real.cosh (maWaveNumber φ * x))
    atTop atTop
  exact tendsto_positive_cosh_mul_atTop c p

theorem tendsto_maRatio_atTop (φ : MaAngle) (τ : ℝ) :
    Tendsto (fun ξ => maNumerator φ ξ τ / (maDenominator φ ξ τ : ℂ))
      atTop (nhds 1) := by
  simpa only [maNumerator_as_leading_sub_offset, maDenominator_as_leading_sub_offset] using
    tendsto_complex_affine_ratio_div_atTop (maLeadingScale φ)
      (tendsto_maLeadingScale_atTop φ) (maLeadingScale_pos φ)
      (maNumeratorOffset φ τ) (Real.cos (maOmega φ * τ))

/-- Ma's full complex field approaches the carrier plane wave as `ξ→+∞`. -/
theorem tendsto_maBreather_atTop (φ : MaAngle) (τ : ℝ) :
    Tendsto (fun ξ => maBreather φ ξ τ) atTop
      (nhds (-linearPhase 1 0 τ 0 / (Real.sqrt 2 : ℂ))) := by
  rw [show -linearPhase 1 0 τ 0 / (Real.sqrt 2 : ℂ) =
      -(1 : ℂ) * linearPhase 1 0 τ 0 / (Real.sqrt 2 : ℂ) by ring]
  have h := ((tendsto_maRatio_atTop φ τ).neg.mul_const
    (linearPhase 1 0 τ 0)).div_const (Real.sqrt 2 : ℂ)
  apply h.congr'
  filter_upwards with ξ
  rw [maBreather, maCore]
  have hphase : linearPhase 1 0 τ ξ = linearPhase 1 0 τ 0 := by
    simp [linearPhase, GaloisForLFunctions.HTGeometry.FDNLS.staggerPhase]
  rw [hphase]

/-- Even spatial symmetry gives the identical asymptote at `ξ→-∞`. -/
theorem tendsto_maBreather_atBot (φ : MaAngle) (τ : ℝ) :
    Tendsto (fun ξ => maBreather φ ξ τ) atBot
      (nhds (-linearPhase 1 0 τ 0 / (Real.sqrt 2 : ℂ))) := by
  have h := (tendsto_maBreather_atTop φ τ).comp tendsto_neg_atBot_atTop
  apply h.congr'
  filter_upwards with ξ
  exact maBreather_space_neg φ ξ τ

theorem tendsto_norm_maBreather_atTop (φ : MaAngle) (τ : ℝ) :
    Tendsto (fun ξ => ‖maBreather φ ξ τ‖) atTop (nhds ((Real.sqrt 2)⁻¹)) := by
  have h := (tendsto_maBreather_atTop φ τ).norm
  convert h using 1
  rw [norm_div, norm_neg, norm_linearPhase, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.mpr (by norm_num)), one_div]

theorem tendsto_norm_maBreather_atBot (φ : MaAngle) (τ : ℝ) :
    Tendsto (fun ξ => ‖maBreather φ ξ τ‖) atBot (nhds ((Real.sqrt 2)⁻¹)) := by
  have h := (tendsto_maBreather_atBot φ τ).norm
  convert h using 1
  rw [norm_div, norm_neg, norm_linearPhase, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.mpr (by norm_num)), one_div]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

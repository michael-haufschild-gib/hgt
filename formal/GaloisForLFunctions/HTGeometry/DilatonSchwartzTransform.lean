import GaloisForLFunctions.HTGeometry.SchwartzNeutralModeStability
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Polynomial dilaton weights acting on complex Schwartz fields

Equations (15)--(20) of arXiv:2608.21406v1 give a half-density transformation
removing the radial first derivative. Here every polynomial log-weight acts on
an actual complex Schwartz field. Both derivatives are established directly,
the potential is derived, and the complete charged-wave residual is conjugated.
There are no assumed differential equations, smoothness premises, or boundary
conditions. The weighted norm density and integral are preserved exactly.
-/

noncomputable section
open Polynomial MeasureTheory
open scoped SchwartzMap
namespace GaloisForLFunctions.HTGeometry

def dilatonWeight (H : ℝ[X]) (x : ℝ) : ℝ := Real.exp (H.eval x)

def dilatonGauge (H : ℝ[X]) (x : ℝ) : ℂ := (Real.exp (-H.eval x / 2) : ℝ)

def dilatonUndressed (H : ℝ[X]) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ := dilatonGauge H x * ψ x

def dilatonPotential (H : ℝ[X]) (x : ℝ) : ℝ :=
  H.derivative.derivative.eval x / 2 + (H.derivative.eval x) ^ 2 / 4

def dilatonRadialOperator (H : ℝ[X]) (R : ℝ → ℂ) (x : ℝ) : ℂ :=
  deriv (deriv R) x + ((H.derivative.eval x : ℝ) : ℂ) * deriv R x

theorem dilatonWeight_pos (H : ℝ[X]) (x : ℝ) : 0 < dilatonWeight H x := Real.exp_pos _

theorem dilatonGauge_ne_zero (H : ℝ[X]) (x : ℝ) : dilatonGauge H x ≠ 0 := by
  unfold dilatonGauge
  exact_mod_cast Real.exp_ne_zero (-H.eval x / 2)

theorem dilatonWeight_log (H : ℝ[X]) (x : ℝ) : Real.log (dilatonWeight H x) = H.eval x :=
  Real.log_exp _

theorem dilatonGauge_derivative (H : ℝ[X]) (x : ℝ) :
    HasDerivAt (dilatonGauge H)
      (-((H.derivative.eval x : ℝ) : ℂ) / 2 * dilatonGauge H x) x := by
  have h := (((H.hasDerivAt x).neg.div_const 2).exp).ofReal_comp
  apply h.congr_deriv
  dsimp
  simp only [dilatonGauge, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_ofNat]
  ring

theorem dilatonUndressed_derivative (H : ℝ[X]) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasDerivAt (dilatonUndressed H ψ)
      (dilatonGauge H x * (deriv ψ x - ((H.derivative.eval x : ℝ) : ℂ) / 2 * ψ x)) x := by
  exact ((dilatonGauge_derivative H x).mul (ψ.hasDerivAt x)).congr_deriv (by ring)

theorem dilatonUndressed_second_derivative (H : ℝ[X]) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasDerivAt (deriv (dilatonUndressed H ψ))
      (dilatonGauge H x * (deriv (deriv ψ) x - ((H.derivative.eval x : ℝ) : ℂ) * deriv ψ x +
        (((H.derivative.eval x : ℝ) : ℂ) ^ 2 / 4 - ((H.derivative.derivative.eval x : ℝ) : ℂ) / 2) * ψ x)) x := by
  have hd : HasDerivAt (deriv ψ) (deriv (deriv ψ) x) x :=
    (SchwartzMap.derivCLM ℂ ℂ ψ).hasDerivAt x
  have h := (dilatonGauge_derivative H x).mul
    (hd.sub (((H.derivative.hasDerivAt x).ofReal_comp.div_const 2).mul (ψ.hasDerivAt x)))
  rw [show deriv (dilatonUndressed H ψ) = fun y =>
      dilatonGauge H y * (deriv ψ y - ((H.derivative.eval y : ℝ) : ℂ) / 2 * ψ y) from
    funext (fun y => (dilatonUndressed_derivative H ψ y).deriv)]
  exact h.congr_deriv (by dsimp; ring)

/-- The paper's first-derivative cancellation, with the effective potential derived. -/
theorem dilatonRadialOperator_conjugation (H : ℝ[X]) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    dilatonRadialOperator H (dilatonUndressed H ψ) x =
      dilatonGauge H x * (deriv (deriv ψ) x - (dilatonPotential H x : ℂ) * ψ x) := by
  rw [dilatonRadialOperator, (dilatonUndressed_second_derivative H ψ x).deriv,
    (dilatonUndressed_derivative H ψ x).deriv]
  simp only [dilatonPotential, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_ofNat]
  ring

/-- The weighted norm density is exactly the original Schwartz norm density. -/
theorem dilatonUndressed_weighted_norm (H : ℝ[X]) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    dilatonWeight H x * ‖dilatonUndressed H ψ x‖ ^ 2 = ‖ψ x‖ ^ 2 := by
  rw [dilatonUndressed, norm_mul, mul_pow]
  simp only [dilatonGauge, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), dilatonWeight]
  rw [pow_two, ← Real.exp_add, ← mul_assoc, ← Real.exp_add,
    show H.eval x + (-H.eval x / 2 + -H.eval x / 2) = 0 by ring,
    Real.exp_zero, one_mul]

theorem dilatonUndressed_weighted_integral (H : ℝ[X]) (ψ : 𝓢(ℝ, ℂ)) :
    (∫ x : ℝ, dilatonWeight H x * ‖dilatonUndressed H ψ x‖ ^ 2) =
      ∫ x : ℝ, ‖ψ x‖ ^ 2 := by
  simp only [dilatonUndressed_weighted_norm]

theorem dilatonUndressed_weighted_integrable (H : ℝ[X]) (ψ : 𝓢(ℝ, ℂ)) :
    Integrable (fun x => dilatonWeight H x * ‖dilatonUndressed H ψ x‖ ^ 2) := by
  simp only [dilatonUndressed_weighted_norm]
  have h : Integrable (fun x : ℝ => ‖mulS (SchwartzMap.conjSLM ψ) ψ x‖) :=
    (mulS (SchwartzMap.conjSLM ψ) ψ).integrable.norm
  convert h using 1
  funext x
  simp only [mulS_apply, norm_mul, SchwartzMap.conjSLM_apply, RCLike.norm_conj, pow_two]

/-- The full charged wave residual is conjugated, not assumed to vanish. -/
theorem dilaton_charged_wave_residual (H A U : ℝ[X]) (ψ : 𝓢(ℝ, ℂ)) (ω : ℂ) (e x : ℝ) :
    dilatonRadialOperator H (dilatonUndressed H ψ) x +
      ((ω - (e : ℂ) * ((A.eval x : ℝ) : ℂ)) ^ 2 - ((U.eval x : ℝ) : ℂ)) *
        dilatonUndressed H ψ x =
      dilatonGauge H x * (deriv (deriv ψ) x +
        ((ω - (e : ℂ) * ((A.eval x : ℝ) : ℂ)) ^ 2 -
          ((U.eval x + dilatonPotential H x : ℝ) : ℂ)) * ψ x) := by
  rw [dilatonRadialOperator_conjugation, dilatonUndressed, Complex.ofReal_add]
  ring

/-- Vanishing of the original radial equation is exactly vanishing of its normal form. -/
theorem dilaton_charged_wave_equivalence (H A U : ℝ[X]) (ψ : 𝓢(ℝ, ℂ)) (ω : ℂ) (e x : ℝ) :
    dilatonRadialOperator H (dilatonUndressed H ψ) x +
      ((ω - (e : ℂ) * ((A.eval x : ℝ) : ℂ)) ^ 2 - ((U.eval x : ℝ) : ℂ)) *
        dilatonUndressed H ψ x = 0 ↔
      deriv (deriv ψ) x + ((ω - (e : ℂ) * ((A.eval x : ℝ) : ℂ)) ^ 2 -
        ((U.eval x + dilatonPotential H x : ℝ) : ℂ)) * ψ x = 0 := by
  rw [dilaton_charged_wave_residual, mul_eq_zero]
  exact or_iff_right (dilatonGauge_ne_zero H x)

end GaloisForLFunctions.HTGeometry

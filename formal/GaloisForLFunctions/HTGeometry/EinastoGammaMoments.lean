import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Einasto moments and exact enclosed-mass core

The Einasto profile and enclosed mass from equations (1)--(3) of
arXiv:2608.23600v1. Central density, length scale, and Einasto index are
`exp d`, `exp l`, and `exp a`, so the whole physical parameter range is covered
without hypotheses. Every natural radial moment is evaluated through the Gamma
integral. Integrability, finite total mass, the actual mass derivative, and the
central cubic limit follow from the integral itself.

The rescaled unit-interval integral `einastoCore` gives an exact factorization,
not merely an asymptotic approximation. It supports the derivative and curvature
analysis in `EinastoRadialGravity`.
-/

noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def einastoDensity (d l a r : ℝ) : ℝ :=
  exp d * exp (-((r / exp l) ^ exp (-a)))

def einastoMoment (n : ℕ) (d l a : ℝ) : ℝ :=
  ∫ r in Ioi (0 : ℝ), r ^ n * einastoDensity d l a r

def einastoMass (d l a r : ℝ) : ℝ :=
  4 * Real.pi * ∫ s in 0..r, s ^ 2 * einastoDensity d l a s

def einastoCore (d l a r : ℝ) : ℝ :=
  4 * Real.pi * ∫ u in (0 : ℝ)..1, u ^ 2 * einastoDensity d l a (r * u)

theorem einastoDensity_pos (d l a r : ℝ) : 0 < einastoDensity d l a r := by
  unfold einastoDensity
  positivity

theorem einastoDensity_continuous (d l a : ℝ) : Continuous (einastoDensity d l a) := by
  unfold einastoDensity
  exact continuous_const.mul (Real.continuous_exp.comp (((continuous_rpow_const (exp_pos (-a)).le).comp
    (continuous_id.div_const (exp l))).neg))

theorem einastoDensity_zero (d l a : ℝ) : einastoDensity d l a 0 = exp d := by
  simp [einastoDensity, Real.zero_rpow (Real.exp_ne_zero (-a))]

theorem einastoMoment_eq (n : ℕ) (d l a : ℝ) :
    einastoMoment n d l a =
      exp d * exp l ^ (n + 1) * exp a * Gamma (((n : ℝ) + 1) * exp a) := by
  have hs : exp l ≠ 0 := exp_ne_zero l
  have hscale := integral_comp_mul_left_Ioi
    (fun r : ℝ => r ^ n * exp (-r ^ exp (-a))) 0
    (by positivity : 0 < (exp l)⁻¹)
  simp only [mul_zero, smul_eq_mul, inv_inv] at hscale
  calc
    einastoMoment n d l a = (exp d * exp l ^ n) *
        ∫ r in Ioi (0 : ℝ), ((exp l)⁻¹ * r) ^ n * exp (-((exp l)⁻¹ * r) ^ exp (-a)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r _
      dsimp [einastoMoment, einastoDensity]
      rw [div_eq_mul_inv, mul_comm r (exp l)⁻¹, mul_pow, inv_pow]
      field_simp
    _ = (exp d * exp l ^ n) * (exp l *
        ((1 / exp (-a)) * Gamma (((n : ℝ) + 1) / exp (-a)))) := by
      rw [hscale]
      congr 2
      simpa only [rpow_natCast] using
        integral_rpow_mul_exp_neg_rpow (exp_pos (-a)) (by have := Nat.cast_nonneg (α := ℝ) n; linarith : -1 < (n : ℝ))
    _ = exp d * exp l ^ (n + 1) * exp a * Gamma (((n : ℝ) + 1) * exp a) := by
      simp only [exp_neg, div_inv_eq_mul, one_mul, pow_succ]
      ring

theorem einastoMoment_pos (n : ℕ) (d l a : ℝ) : 0 < einastoMoment n d l a := by
  rw [einastoMoment_eq]
  have hg := Gamma_pos_of_pos (by positivity : 0 < ((n : ℝ) + 1) * exp a)
  positivity

theorem einastoMoment_integrable (n : ℕ) (d l a : ℝ) :
    IntegrableOn (fun r : ℝ => r ^ n * einastoDensity d l a r) (Ioi 0) :=
  Integrable.of_integral_ne_zero (ne_of_gt (einastoMoment_pos n d l a))

theorem einastoMass_total (d l a : ℝ) :
    Tendsto (einastoMass d l a) atTop
      (𝓝 (4 * Real.pi * exp d * exp l ^ 3 * exp a * Gamma (3 * exp a))) := by
  have h := (intervalIntegral_tendsto_integral_Ioi 0
    (einastoMoment_integrable 2 d l a) tendsto_id).const_mul (4 * Real.pi)
  change Tendsto (einastoMass d l a) atTop (𝓝 (4 * Real.pi * einastoMoment 2 d l a)) at h
  have heq : 4 * Real.pi * einastoMoment 2 d l a =
      4 * Real.pi * exp d * exp l ^ 3 * exp a * Gamma (3 * exp a) := by
    rw [einastoMoment_eq]
    norm_num
    ring
  rw [heq] at h
  exact h

theorem einastoCore_continuous (d l a : ℝ) : Continuous (einastoCore d l a) := by
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (continuous_snd.pow 2).mul ((einastoDensity_continuous d l a).comp
    (continuous_fst.mul continuous_snd))

theorem einastoCore_zero (d l a : ℝ) : einastoCore d l a 0 = 4 * Real.pi * exp d / 3 := by
  simp only [einastoCore, zero_mul, einastoDensity_zero]
  rw [intervalIntegral.integral_mul_const, integral_pow]
  norm_num
  ring

theorem einastoMass_core (d l a r : ℝ) : einastoMass d l a r = r ^ 3 * einastoCore d l a r := by
  have h := intervalIntegral.smul_integral_comp_mul_left
    (fun s : ℝ => s ^ 2 * einastoDensity d l a s) r (a := 0) (b := 1)
  simp only [smul_eq_mul, mul_zero, mul_one, mul_pow] at h
  rw [show (fun u : ℝ => r ^ 2 * u ^ 2 * einastoDensity d l a (r * u)) =
    (fun u : ℝ => r ^ 2 * (u ^ 2 * einastoDensity d l a (r * u))) by funext u; ring,
    intervalIntegral.integral_const_mul] at h
  dsimp [einastoMass, einastoCore]
  rw [← h]
  ring

theorem einastoMass_derivative (d l a r : ℝ) :
    HasDerivAt (einastoMass d l a) (4 * Real.pi * r ^ 2 * einastoDensity d l a r) r := by
  have hc : Continuous (fun s : ℝ => s ^ 2 * einastoDensity d l a s) :=
    (continuous_id.pow 2).mul (einastoDensity_continuous d l a)
  have h := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 r)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_mul (4 * Real.pi)
  apply h.congr_deriv
  ring

theorem einastoMass_core_limit (d l a : ℝ) :
    Tendsto (fun t => einastoMass d l a (exp t) / exp t ^ 3) atBot
      (𝓝 (4 * Real.pi * exp d / 3)) := by
  have h := (einastoCore_continuous d l a).continuousAt.tendsto.comp tendsto_exp_atBot
  rw [einastoCore_zero] at h
  simpa only [Function.comp_def, einastoMass_core, mul_div_cancel_left₀ _
    (pow_ne_zero 3 (exp_ne_zero _))] using h

end GaloisForLFunctions.HTGeometry

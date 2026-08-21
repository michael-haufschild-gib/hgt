/-
# Chen--Gupta--Li `h_t`: first reciprocal-parameter Fourier decay

This module proves the `j = 1` instance of the second family in CGL Lemma
4.3.  The verified Mellin--Fourier bridge places the parameter `t` in an
ordinary Fourier frequency.  A compact log-dyadic cutoff profile and the
literal derivative of its additive phase then give

`|t| ‖ĥ_t(ξ)‖ ≤ C_w (1 + |ξ|)`.

The source's all-order reciprocal-parameter family is deliberately not claimed
here; this is its closed first-order base layer.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiMellinFourierBridge
import Mathlib.Analysis.Fourier.FourierTransformDeriv

noncomputable section

namespace RHTower

open MeasureTheory
open scoped FourierTransform

/-- The fixed CGL cutoff in logarithmic coordinates. -/
def cglLogCutoffProfile (w : CGLSmoothBump) (u : ℝ) : ℂ :=
  (Real.exp (-u) : ℂ) * w.value (Real.exp (-u)) * w.value (Real.exp (-u))

theorem cglLogCutoffProfile_eq_logFourierAmplitude_zero (w : CGLSmoothBump) :
    cglLogCutoffProfile w = cglLogFourierAmplitude w 0 := by
  funext u
  simp [cglLogCutoffProfile, cglLogFourierAmplitude, cglFourierAmplitude, mul_assoc]

theorem cglLogCutoffProfile_eq_zero_of_not_mem (w : CGLSmoothBump) (u : ℝ)
    (hu : u ∉ Set.Icc (-Real.log 2) 0) : cglLogCutoffProfile w u = 0 := by
  rw [cglLogCutoffProfile_eq_logFourierAmplitude_zero]
  exact cglLogFourierAmplitude_eq_zero_of_not_mem w 0 u hu

theorem hasCompactSupport_cglLogCutoffProfile (w : CGLSmoothBump) :
    HasCompactSupport (cglLogCutoffProfile w) := by
  rw [cglLogCutoffProfile_eq_logFourierAmplitude_zero]
  exact hasCompactSupport_cglLogFourierAmplitude w 0

theorem contDiff_cglLogCutoffProfile (w : CGLSmoothBump) :
    ContDiff ℝ (⊤ : ℕ∞) (cglLogCutoffProfile w) := by
  rw [cglLogCutoffProfile_eq_logFourierAmplitude_zero]
  exact contDiff_cglLogFourierAmplitude w 0

def cglLogCutoffProfileSchwartz (w : CGLSmoothBump) : SchwartzMap ℝ ℂ :=
  (hasCompactSupport_cglLogCutoffProfile w).toSchwartzMap (contDiff_cglLogCutoffProfile w)

@[simp] theorem cglLogCutoffProfileSchwartz_apply (w : CGLSmoothBump) (u : ℝ) :
    cglLogCutoffProfileSchwartz w u = cglLogCutoffProfile w u := rfl

/-- The additive phase in the verified logarithmic Fourier model. -/
def cglLogAdditivePhase (xi u : ℝ) : ℂ :=
  Complex.exp (((-2 * Real.pi * xi * Real.exp (-u) : ℝ) : ℂ) * Complex.I)

theorem norm_cglLogAdditivePhase (xi u : ℝ) : ‖cglLogAdditivePhase xi u‖ = 1 := by
  rw [cglLogAdditivePhase, Complex.norm_exp]
  have him : ((((-2 * Real.pi * xi * Real.exp (-u) : ℝ) : ℂ) * Complex.I).re) = 0 := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero]
  rw [him, Real.exp_zero]

theorem cglLogFourierAmplitude_eq_cutoff_mul_phase (w : CGLSmoothBump) (xi u : ℝ) :
    cglLogFourierAmplitude w xi u =
      cglLogCutoffProfile w u * cglLogAdditivePhase xi u := by
  simp [cglLogFourierAmplitude, cglLogCutoffProfile, cglFourierAmplitude,
    cglLogAdditivePhase, mul_assoc]

theorem hasDerivAt_cglLogAdditivePhase (xi u : ℝ) :
    HasDerivAt (cglLogAdditivePhase xi)
      (cglLogAdditivePhase xi u *
        ((-2 * Real.pi * xi * -Real.exp (-u) : ℝ) : ℂ) * Complex.I) u := by
  have hexpR : HasDerivAt (fun v : ℝ => Real.exp (-v)) (-Real.exp (-u)) u := by
    simpa only [Function.comp_def, mul_neg, mul_one] using
      (Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)
  have hargR : HasDerivAt (fun v : ℝ => -2 * Real.pi * xi * Real.exp (-v))
      (-2 * Real.pi * xi * -Real.exp (-u)) u := by
    have hraw := hexpR.const_mul (-2 * Real.pi * xi)
    exact hraw
  have hargC : HasDerivAt
      (fun v : ℝ => ((-2 * Real.pi * xi * Real.exp (-v) : ℝ) : ℂ))
      ((-2 * Real.pi * xi * -Real.exp (-u) : ℝ) : ℂ) u :=
    hargR.ofReal_comp
  apply HasDerivAt.of_isLittleO
  simpa [cglLogAdditivePhase, mul_assoc] using (hargC.mul_const Complex.I).cexp.isLittleO

def cglLogCutoffProfileDerivative (w : CGLSmoothBump) : SchwartzMap ℝ ℂ :=
  SchwartzMap.derivCLM ℂ ℂ (cglLogCutoffProfileSchwartz w)

theorem cglLogCutoffProfileDerivative_apply (w : CGLSmoothBump) (u : ℝ) :
    cglLogCutoffProfileDerivative w u = deriv (cglLogCutoffProfile w) u := by
  rw [cglLogCutoffProfileDerivative, SchwartzMap.derivCLM_apply]
  rfl

def cglLogFourierAmplitudeDerivativeValue (w : CGLSmoothBump) (xi u : ℝ) : ℂ :=
  deriv (cglLogCutoffProfile w) u * cglLogAdditivePhase xi u +
    cglLogCutoffProfile w u *
      (cglLogAdditivePhase xi u *
        ((-2 * Real.pi * xi * -Real.exp (-u) : ℝ) : ℂ) * Complex.I)

theorem hasDerivAt_cglLogFourierAmplitude (w : CGLSmoothBump) (xi u : ℝ) :
    HasDerivAt (cglLogFourierAmplitude w xi)
      (cglLogFourierAmplitudeDerivativeValue w xi u) u := by
  have hcut : HasDerivAt (cglLogCutoffProfile w)
      (deriv (cglLogCutoffProfile w) u) u :=
    ((contDiff_cglLogCutoffProfile w).differentiable (by simp)).differentiableAt.hasDerivAt
  have hphase := hasDerivAt_cglLogAdditivePhase xi u
  have hprod := hcut.mul hphase
  apply HasDerivAt.of_isLittleO
  simpa [cglLogFourierAmplitude, cglLogCutoffProfile, cglFourierAmplitude,
    cglLogAdditivePhase, cglLogFourierAmplitudeDerivativeValue, mul_assoc] using hprod.isLittleO

theorem deriv_cglLogFourierAmplitude (w : CGLSmoothBump) (xi u : ℝ) :
    deriv (cglLogFourierAmplitude w xi) u =
      cglLogFourierAmplitudeDerivativeValue w xi u :=
  (hasDerivAt_cglLogFourierAmplitude w xi u).deriv

def cglLogFourierAmplitudeSchwartz (w : CGLSmoothBump) (xi : ℝ) : SchwartzMap ℝ ℂ :=
  (hasCompactSupport_cglLogFourierAmplitude w xi).toSchwartzMap
    (contDiff_cglLogFourierAmplitude w xi)

@[simp] theorem cglLogFourierAmplitudeSchwartz_apply (w : CGLSmoothBump) (xi u : ℝ) :
    cglLogFourierAmplitudeSchwartz w xi u = cglLogFourierAmplitude w xi u := rfl

def cglLogFourierAmplitudeDerivative (w : CGLSmoothBump) (xi : ℝ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.derivCLM ℂ ℂ (cglLogFourierAmplitudeSchwartz w xi)

theorem cglLogFourierAmplitudeDerivative_apply (w : CGLSmoothBump) (xi u : ℝ) :
    cglLogFourierAmplitudeDerivative w xi u =
      cglLogFourierAmplitudeDerivativeValue w xi u := by
  rw [cglLogFourierAmplitudeDerivative, SchwartzMap.derivCLM_apply]
  change deriv (cglLogFourierAmplitude w xi) u = _
  exact deriv_cglLogFourierAmplitude w xi u

theorem cglLogCutoffProfile_tsupport_subset (w : CGLSmoothBump) :
    tsupport (cglLogCutoffProfileSchwartz w) ⊆ Set.Icc (-Real.log 2) 0 := by
  apply closure_minimal
  intro u hu
  by_contra hnot
  change cglLogCutoffProfile w u ≠ 0 at hu
  rw [cglLogCutoffProfile_eq_zero_of_not_mem w u hnot] at hu
  exact hu rfl
  exact isClosed_Icc

theorem cglLogCutoffProfileDerivative_tsupport_subset (w : CGLSmoothBump) :
    tsupport (cglLogCutoffProfileDerivative w) ⊆ Set.Icc (-Real.log 2) 0 := by
  rw [cglLogCutoffProfileDerivative]
  exact (SchwartzMap.tsupport_derivCLM_subset (𝕜 := ℂ)
    (cglLogCutoffProfileSchwartz w)).trans (cglLogCutoffProfile_tsupport_subset w)

theorem norm_cglLogFourierAmplitudeDerivativeValue_le (w : CGLSmoothBump) (xi u : ℝ) :
    ‖cglLogFourierAmplitudeDerivativeValue w xi u‖ ≤
      ‖cglLogCutoffProfileDerivative w u‖ +
        (4 * Real.pi * |xi|) * ‖cglLogCutoffProfileSchwartz w u‖ := by
  rw [cglLogFourierAmplitudeDerivativeValue,
    ← cglLogCutoffProfileDerivative_apply, cglLogCutoffProfileSchwartz_apply]
  calc
    ‖cglLogCutoffProfileDerivative w u * cglLogAdditivePhase xi u +
        cglLogCutoffProfile w u *
          (cglLogAdditivePhase xi u *
            ((-2 * Real.pi * xi * -Real.exp (-u) : ℝ) : ℂ) * Complex.I)‖ ≤
        ‖cglLogCutoffProfileDerivative w u * cglLogAdditivePhase xi u‖ +
          ‖cglLogCutoffProfile w u *
            (cglLogAdditivePhase xi u *
              ((-2 * Real.pi * xi * -Real.exp (-u) : ℝ) : ℂ) * Complex.I)‖ :=
      norm_add_le _ _
    _ = ‖cglLogCutoffProfileDerivative w u‖ +
          ‖cglLogCutoffProfile w u *
            (cglLogAdditivePhase xi u *
              ((-2 * Real.pi * xi * -Real.exp (-u) : ℝ) : ℂ) * Complex.I)‖ := by
      rw [norm_mul, norm_cglLogAdditivePhase, mul_one]
    _ ≤ ‖cglLogCutoffProfileDerivative w u‖ +
          (4 * Real.pi * |xi|) * ‖cglLogCutoffProfile w u‖ := by
      gcongr
      by_cases hzero : cglLogCutoffProfile w u = 0
      · rw [hzero]
        simp
      · have hu : u ∈ Set.Icc (-Real.log 2) 0 := by
          by_contra hnot
          exact hzero (cglLogCutoffProfile_eq_zero_of_not_mem w u hnot)
        have harg : -u ≤ Real.log 2 := by linarith [hu.1]
        have hexp : Real.exp (-u) ≤ 2 := by
          calc
            Real.exp (-u) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr harg
            _ = 2 := Real.exp_log (by norm_num)
        have hcoeff :
            ‖((-2 * Real.pi * xi * -Real.exp (-u) : ℝ) : ℂ)‖ =
              2 * Real.pi * |xi| * Real.exp (-u) := by
          have hident : -2 * Real.pi * xi * -Real.exp (-u) =
              2 * Real.pi * xi * Real.exp (-u) := by ring
          rw [hident, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
            abs_of_pos (mul_pos (by norm_num) Real.pi_pos),
            abs_of_nonneg (Real.exp_nonneg _)]
        calc
          ‖cglLogCutoffProfile w u *
              (cglLogAdditivePhase xi u *
                ((-2 * Real.pi * xi * -Real.exp (-u) : ℝ) : ℂ) * Complex.I)‖ =
              ‖cglLogCutoffProfile w u‖ *
                (2 * Real.pi * |xi| * Real.exp (-u)) := by
            rw [norm_mul, norm_mul, norm_mul, norm_cglLogAdditivePhase, hcoeff,
              Complex.norm_I, mul_one]
            ring
          _ ≤ ‖cglLogCutoffProfile w u‖ * (4 * Real.pi * |xi|) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            calc
              2 * Real.pi * |xi| * Real.exp (-u) ≤
                  2 * Real.pi * |xi| * 2 := by gcongr
              _ = 4 * Real.pi * |xi| := by ring
          _ = (4 * Real.pi * |xi|) * ‖cglLogCutoffProfile w u‖ := by ring

theorem norm_cglLogFourierAmplitudeDerivative_le (w : CGLSmoothBump) (xi u : ℝ) :
    ‖cglLogFourierAmplitudeDerivative w xi u‖ ≤
      ‖cglLogCutoffProfileDerivative w u‖ +
        (4 * Real.pi * |xi|) * ‖cglLogCutoffProfileSchwartz w u‖ := by
  rw [cglLogFourierAmplitudeDerivative_apply]
  exact norm_cglLogFourierAmplitudeDerivativeValue_le w xi u

/-- Cutoff-only `L¹` budget for the first reciprocal-parameter CGL estimate. -/
def cglLogFourierAmplitudeFirstDecayBudget (w : CGLSmoothBump) : ℝ :=
  (∫ u : ℝ, ‖cglLogCutoffProfileDerivative w u‖) +
    4 * Real.pi * (∫ u : ℝ, ‖cglLogCutoffProfileSchwartz w u‖)

theorem integral_norm_cglLogFourierAmplitudeDerivative_le (w : CGLSmoothBump) (xi : ℝ) :
    (∫ u : ℝ, ‖cglLogFourierAmplitudeDerivative w xi u‖) ≤
      cglLogFourierAmplitudeFirstDecayBudget w * (1 + |xi|) := by
  have hderiv : Integrable (fun u : ℝ => ‖cglLogFourierAmplitudeDerivative w xi u‖) :=
    (cglLogFourierAmplitudeDerivative w xi).integrable.norm
  have hcutDeriv : Integrable (fun u : ℝ => ‖cglLogCutoffProfileDerivative w u‖) :=
    (cglLogCutoffProfileDerivative w).integrable.norm
  have hcut : Integrable (fun u : ℝ => ‖cglLogCutoffProfileSchwartz w u‖) :=
    (cglLogCutoffProfileSchwartz w).integrable.norm
  have henv : Integrable (fun u : ℝ =>
      ‖cglLogCutoffProfileDerivative w u‖ +
        (4 * Real.pi * |xi|) * ‖cglLogCutoffProfileSchwartz w u‖) :=
    hcutDeriv.add (hcut.const_mul _)
  calc
    (∫ u : ℝ, ‖cglLogFourierAmplitudeDerivative w xi u‖) ≤
        ∫ u : ℝ, ‖cglLogCutoffProfileDerivative w u‖ +
          (4 * Real.pi * |xi|) * ‖cglLogCutoffProfileSchwartz w u‖ :=
      integral_mono hderiv henv (norm_cglLogFourierAmplitudeDerivative_le w xi)
    _ = (∫ u : ℝ, ‖cglLogCutoffProfileDerivative w u‖) +
        (4 * Real.pi * |xi|) *
          (∫ u : ℝ, ‖cglLogCutoffProfileSchwartz w u‖) := by
      rw [integral_add hcutDeriv (hcut.const_mul _), integral_const_mul]
    _ = (∫ u : ℝ, ‖cglLogCutoffProfileDerivative w u‖) +
        (4 * Real.pi * (∫ u : ℝ, ‖cglLogCutoffProfileSchwartz w u‖)) * |xi| := by
      ring
    _ ≤ cglLogFourierAmplitudeFirstDecayBudget w * (1 + |xi|) := by
      unfold cglLogFourierAmplitudeFirstDecayBudget
      have hA : 0 ≤ ∫ u : ℝ, ‖cglLogCutoffProfileDerivative w u‖ :=
        integral_nonneg fun _ => norm_nonneg _
      have hB : 0 ≤ 4 * Real.pi * (∫ u : ℝ, ‖cglLogCutoffProfileSchwartz w u‖) := by
        positivity
      nlinarith [mul_nonneg hA (abs_nonneg xi), mul_nonneg hB (abs_nonneg xi)]

theorem cglLogFourierAmplitude_fourier_derivative (w : CGLSmoothBump) (xi eta : ℝ) :
    𝓕 (cglLogFourierAmplitudeDerivative w xi : ℝ → ℂ) eta =
      (2 * Real.pi * Complex.I * eta) •
        𝓕 (cglLogFourierAmplitudeSchwartz w xi : ℝ → ℂ) eta := by
  have h := Real.fourier_deriv
    (f := (cglLogFourierAmplitudeSchwartz w xi : ℝ → ℂ))
    (cglLogFourierAmplitudeSchwartz w xi).integrable
    (cglLogFourierAmplitudeSchwartz w xi).differentiable
    (cglLogFourierAmplitudeDerivative w xi).integrable
  exact congrFun h eta

theorem cglLogFourierAmplitude_first_fourier_decay (w : CGLSmoothBump) (xi eta : ℝ) :
    (2 * Real.pi) *
        (|eta| * ‖𝓕 (cglLogFourierAmplitudeSchwartz w xi : ℝ → ℂ) eta‖) ≤
      cglLogFourierAmplitudeFirstDecayBudget w * (1 + |xi|) := by
  have hfour := cglLogFourierAmplitude_fourier_derivative w xi eta
  have hbound :
      ‖𝓕 (cglLogFourierAmplitudeDerivative w xi : ℝ → ℂ) eta‖ ≤
        ∫ u : ℝ, ‖cglLogFourierAmplitudeDerivative w xi u‖ := by
    simpa only [Real.fourier_real_eq, Fourier.fourierIntegral_def] using
      (Fourier.norm_fourierIntegral_le_integral_norm
        Real.fourierChar MeasureTheory.volume
        (cglLogFourierAmplitudeDerivative w xi : ℝ → ℂ) eta)
  calc
    (2 * Real.pi) *
        (|eta| * ‖𝓕 (cglLogFourierAmplitudeSchwartz w xi : ℝ → ℂ) eta‖) =
        ‖𝓕 (cglLogFourierAmplitudeDerivative w xi : ℝ → ℂ) eta‖ := by
      rw [hfour, norm_smul]
      simp only [norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs]
      norm_num
      rw [abs_of_pos Real.pi_pos]
      ring
    _ ≤ ∫ u : ℝ, ‖cglLogFourierAmplitudeDerivative w xi u‖ := hbound
    _ ≤ cglLogFourierAmplitudeFirstDecayBudget w * (1 + |xi|) :=
      integral_norm_cglLogFourierAmplitudeDerivative_le w xi

/-- The `j = 1` reciprocal-parameter family in CGL Lemma 4.3. -/
theorem cglSmoothBumpHt_first_reciprocalParameter_fourier_decay
    (w : CGLSmoothBump) (t xi : ℝ) :
    |t| * ‖𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) xi‖ ≤
      cglLogFourierAmplitudeFirstDecayBudget w * (1 + |xi|) := by
  have h := cglLogFourierAmplitude_first_fourier_decay w xi (t / (2 * Real.pi))
  change (2 * Real.pi) *
      (|t / (2 * Real.pi)| *
        ‖𝓕 (cglLogFourierAmplitude w xi) (t / (2 * Real.pi))‖) ≤ _ at h
  rw [← cglSmoothBumpHt_fourier_eq_logFourier w t xi] at h
  have hscale : (2 * Real.pi) * |t / (2 * Real.pi)| = |t| := by
    rw [abs_div, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    field_simp [Real.pi_ne_zero]
  calc
    |t| * ‖𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) xi‖ =
        ((2 * Real.pi) * |t / (2 * Real.pi)|) *
          ‖𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) xi‖ := by rw [hscale]
    _ = (2 * Real.pi) *
        (|t / (2 * Real.pi)| * ‖𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) xi‖) := by ring
    _ ≤ cglLogFourierAmplitudeFirstDecayBudget w * (1 + |xi|) := h

end RHTower

/-
# Chen--Gupta--Li `h_t`: Mellin--Fourier bridge in the parameter coordinate

The second family in CGL Lemma 4.3 is decay in the Mellin parameter `t`.
This module gives its exact analytic starting point: the literal spatial Fourier
transform of `h_t` is the ordinary Fourier transform, at frequency `t / (2π)`,
of a compactly supported logarithmic profile.  It uses Mathlib's Mellin
change-of-variables theorem, so no informal substitution or analytic premise is
introduced.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiHtAllOrder
import Mathlib.Analysis.MellinInversion

noncomputable section

namespace RHTower

open MeasureTheory
open scoped FourierTransform

/-- CGL's cutoff with the spatial Fourier phase, before Mellin oscillation is applied. -/
def cglFourierAmplitude (w : CGLSmoothBump) (xi x : ℝ) : ℂ :=
  w.value x * w.value x *
    Complex.exp (((-2 * Real.pi * xi * x : ℝ) : ℂ) * Complex.I)

/-- The Mellin power at `1 + it` is CGL's literal phase on the positive axis. -/
theorem cgl_cpow_one_add_it_sub_one (t x : ℝ) (hx : 0 < x) :
    (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I - 1) = cglMellinPhase t x := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  unfold cglMellinPhase
  rw [← Complex.ofReal_log hx.le]
  congr 1
  ring

/-- The spatial Fourier transform of `h_t` is the Mellin transform of its fixed-phase amplitude. -/
theorem cglSmoothBumpHt_fourier_eq_mellin (w : CGLSmoothBump) (t xi : ℝ) :
    𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) xi =
      mellin (cglFourierAmplitude w xi) ((1 : ℂ) + (t : ℂ) * Complex.I) := by
  rw [mellin, Real.fourier_real_eq_integral_exp_smul,
    ← MeasureTheory.integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : 0 < x
  · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hx)]
    rw [cglSmoothBumpHt_apply, cglSmoothBumpHtValue,
      cgl_cpow_one_add_it_sub_one t x hx]
    simp only [smul_eq_mul, cglFourierAmplitude]
    ring_nf
  · rw [Set.indicator_of_notMem (Set.notMem_Ioi.mpr (not_lt.mp hx))]
    have houtside : x ∉ Set.Icc (1 : ℝ) 2 := by
      intro hmem
      linarith [hmem.1]
    rw [cglSmoothBumpHt_apply, cglSmoothBumpHtValue, w.outside_support x houtside]
    simp

/-- Compact logarithmic profile whose Fourier transform carries the `t` oscillation. -/
def cglLogFourierAmplitude (w : CGLSmoothBump) (xi u : ℝ) : ℂ :=
  Real.exp (-u) • cglFourierAmplitude w xi (Real.exp (-u))

/-- Exact CGL Mellin--Fourier bridge for the literal kernel. -/
theorem cglSmoothBumpHt_fourier_eq_logFourier (w : CGLSmoothBump) (t xi : ℝ) :
    𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) xi =
      𝓕 (cglLogFourierAmplitude w xi) (t / (2 * Real.pi)) := by
  rw [cglSmoothBumpHt_fourier_eq_mellin, mellin_eq_fourier]
  have hsource :
      (fun u : ℝ => Real.exp (-(1 + (t : ℂ) * Complex.I).re * u) •
        cglFourierAmplitude w xi (Real.exp (-u))) = cglLogFourierAmplitude w xi := by
    funext u
    simp [cglLogFourierAmplitude]
  rw [hsource]
  simp

/-- Outside `[-log 2, 0]`, the logarithmic CGL amplitude is literally zero. -/
theorem cglLogFourierAmplitude_eq_zero_of_not_mem (w : CGLSmoothBump) (xi u : ℝ)
    (hu : u ∉ Set.Icc (-Real.log 2) 0) :
    cglLogFourierAmplitude w xi u = 0 := by
  have hx : Real.exp (-u) ∉ Set.Icc (1 : ℝ) 2 := by
    intro hmem
    apply hu
    constructor
    · have hright : Real.exp (-u) ≤ Real.exp (Real.log 2) := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        exact hmem.2
      have hbound : -u ≤ Real.log 2 := Real.exp_le_exp.mp hright
      linarith
    · have hleft : Real.exp 0 ≤ Real.exp (-u) := by simpa using hmem.1
      have hbound : 0 ≤ -u := Real.exp_le_exp.mp hleft
      linarith
  rw [cglLogFourierAmplitude, cglFourierAmplitude, w.outside_support _ hx]
  simp

/-- The logarithmic amplitude has support in the fixed compact log-dyadic interval. -/
theorem hasCompactSupport_cglLogFourierAmplitude (w : CGLSmoothBump) (xi : ℝ) :
    HasCompactSupport (cglLogFourierAmplitude w xi) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc :
    IsCompact (Set.Icc (-Real.log 2) 0)) ?_
  intro u hu
  by_contra hnot
  have hzero := cglLogFourierAmplitude_eq_zero_of_not_mem w xi u hnot
  exact hu hzero

/-- The log-dyadic amplitude is globally smooth, including outside its support. -/
theorem contDiff_cglLogFourierAmplitude (w : CGLSmoothBump) (xi : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (cglLogFourierAmplitude w xi) := by
  unfold cglLogFourierAmplitude cglFourierAmplitude
  have hexp : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => Real.exp (-u)) :=
    Real.contDiff_exp.comp contDiff_id.neg
  have hexpC : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => (Real.exp (-u) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hexp
  have hw : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => w.value (Real.exp (-u))) :=
    w.smooth.comp hexp
  have hconst : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => (-2 * Real.pi * xi : ℝ)) :=
    contDiff_const
  have hargR : ContDiff ℝ (⊤ : ℕ∞)
      (fun u : ℝ => (-2 * Real.pi * xi) * Real.exp (-u)) :=
    hconst.mul hexp
  have hargC : ContDiff ℝ (⊤ : ℕ∞)
      (fun u : ℝ => ((-2 * Real.pi * xi * Real.exp (-u) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hargR
  have hI : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => Complex.I) := contDiff_const
  have hphase : ContDiff ℝ (⊤ : ℕ∞)
      (fun u : ℝ => Complex.exp
        (((-2 * Real.pi * xi * Real.exp (-u) : ℝ) : ℂ) * Complex.I)) :=
    (hargC.mul hI).cexp
  simpa only [Pi.smul_apply, Complex.real_smul, mul_assoc] using
    hexpC.mul ((hw.mul hw).mul hphase)

end RHTower

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62Poisson
import GaloisForLFunctions.RHTower.ChenGuptaLiHtReciprocalAllOrder
import GaloisForLFunctions.RHTower.DeningerPoissonMellin

/-!
# Chen--Gupta--Li Lemma 6.2: Mellin kernel on the initial line

The source Mellin transform `H(s)` is the transform of the square of CGL's
compact cutoff.  On its initial line `Re(s)=1`, the already-formalized
Mellin--Fourier bridge identifies it with the zero-frequency value of `h_t`.
This makes the paper's rapid-decay estimate a closed all-order theorem.
-/

open Complex MeasureTheory
open scoped FourierTransform

noncomputable section

namespace RHTower

/-- CGL's Section 6 Mellin kernel `H(s)`. -/
def cglLemma62MellinTransform (w : CGLRealSmoothBump) (s : ℂ) : ℂ :=
  mellin (fun x : ℝ =>
    w.toCGLSmoothBump.value x * w.toCGLSmoothBump.value x) s

/-- The logarithmic Fourier profile for the Mellin kernel on `Re(s)=σ`. -/
def cglLemma62LogMellinProfile (w : CGLRealSmoothBump) (σ u : ℝ) : ℂ :=
  (Real.exp (-σ * u) : ℂ) *
    w.toCGLSmoothBump.value (Real.exp (-u)) *
      w.toCGLSmoothBump.value (Real.exp (-u))

/-- Reexpress the general Mellin-line profile through the fixed compact
logarithmic cutoff profile. -/
theorem cglLemma62LogMellinProfile_eq_logCutoffProfile
    (w : CGLRealSmoothBump) (σ u : ℝ) :
    cglLemma62LogMellinProfile w σ u =
      (Real.exp (-((σ - 1) * u)) : ℂ) * cglLogCutoffProfile w.toCGLSmoothBump u := by
  have hexp : Real.exp (-σ * u) = Real.exp (-((σ - 1) * u)) * Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [cglLemma62LogMellinProfile, cglLogCutoffProfile, hexp]
  push_cast
  ring

/-- Every fixed Mellin-line profile has the same compact logarithmic support. -/
theorem hasCompactSupport_cglLemma62LogMellinProfile
    (w : CGLRealSmoothBump) (σ : ℝ) :
    HasCompactSupport (cglLemma62LogMellinProfile w σ) := by
  rw [show cglLemma62LogMellinProfile w σ =
      fun u : ℝ => (Real.exp (-((σ - 1) * u)) : ℂ) *
        cglLogCutoffProfile w.toCGLSmoothBump u by
      funext u
      exact cglLemma62LogMellinProfile_eq_logCutoffProfile w σ u]
  exact (hasCompactSupport_cglLogCutoffProfile w.toCGLSmoothBump).mul_left

/-- Smoothness of every fixed Mellin-line profile. -/
theorem contDiff_cglLemma62LogMellinProfile
    (w : CGLRealSmoothBump) (σ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (cglLemma62LogMellinProfile w σ) := by
  rw [show cglLemma62LogMellinProfile w σ =
      fun u : ℝ => (Real.exp (-((σ - 1) * u)) : ℂ) *
        cglLogCutoffProfile w.toCGLSmoothBump u by
      funext u
      exact cglLemma62LogMellinProfile_eq_logCutoffProfile w σ u]
  have harg : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => -((σ - 1) * u)) :=
    (contDiff_const.mul contDiff_id).neg
  exact (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp harg)).mul
    (contDiff_cglLogCutoffProfile w.toCGLSmoothBump)

/-- The smooth compact logarithmic Mellin profile as a Schwartz function. -/
def cglLemma62LogMellinProfileSchwartz
    (w : CGLRealSmoothBump) (σ : ℝ) : SchwartzMap ℝ ℂ :=
  (hasCompactSupport_cglLemma62LogMellinProfile w σ).toSchwartzMap
    (contDiff_cglLemma62LogMellinProfile w σ)

@[simp] theorem cglLemma62LogMellinProfileSchwartz_apply
    (w : CGLRealSmoothBump) (σ u : ℝ) :
    cglLemma62LogMellinProfileSchwartz w σ u = cglLemma62LogMellinProfile w σ u := rfl

/-- The Mellin transform on any fixed real line is the Fourier transform of
its compact logarithmic profile. -/
theorem cglLemma62_mellinTransform_eq_fourier_logMellinProfile
    (w : CGLRealSmoothBump) (σ t : ℝ) :
    cglLemma62MellinTransform w ((σ : ℂ) + (t : ℂ) * I) =
      𝓕 (cglLemma62LogMellinProfile w σ) (t / (2 * Real.pi)) := by
  unfold cglLemma62MellinTransform
  rw [mellin_eq_fourier]
  have hre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
  have him : ((σ : ℂ) + (t : ℂ) * I).im = t := by simp
  rw [hre, him]
  have hprofile :
      (fun u : ℝ => Real.exp (-σ * u) •
        (w.toCGLSmoothBump.value (Real.exp (-u)) *
          w.toCGLSmoothBump.value (Real.exp (-u)))) =
        cglLemma62LogMellinProfile w σ := by
    funext u
    rw [cglLemma62LogMellinProfile]
    rw [Complex.real_smul]
    ring
  rw [hprofile]

/-- Explicit all-order budget for the source Mellin kernel on a fixed real
line. -/
def cglLemma62MellinLineDecayBudget
    (w : CGLRealSmoothBump) (σ : ℝ) (n : ℕ) : ℝ :=
  (2 * Real.pi) ^ n *
    cglSchwartzFourierDecayBudget (cglLemma62LogMellinProfileSchwartz w σ) n

/-- **CGL equation (6.2).**  On every fixed vertical Mellin line the compact
source kernel has arbitrary polynomial decay in the imaginary direction. -/
theorem cglLemma62_mellinTransform_vertical_rapidDecay
    (w : CGLRealSmoothBump) (σ : ℝ) (n : ℕ) (t : ℝ) :
    |t| ^ n * ‖cglLemma62MellinTransform w ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      cglLemma62MellinLineDecayBudget w σ n := by
  rw [cglLemma62_mellinTransform_eq_fourier_logMellinProfile]
  have hfourier := cglSchwartz_abs_pow_mul_norm_fourier_le_decayBudget
    (cglLemma62LogMellinProfileSchwartz w σ) n (t / (2 * Real.pi))
  have hprofile : (cglLemma62LogMellinProfileSchwartz w σ : ℝ → ℂ) =
      cglLemma62LogMellinProfile w σ := by
    funext u
    exact cglLemma62LogMellinProfileSchwartz_apply w σ u
  have hfourier' : |t / (2 * Real.pi)| ^ n *
      ‖𝓕 (cglLemma62LogMellinProfile w σ) (t / (2 * Real.pi))‖ ≤
        cglSchwartzFourierDecayBudget (cglLemma62LogMellinProfileSchwartz w σ) n := by
    rw [← hprofile]
    exact hfourier
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hscale : |t| ^ n = (2 * Real.pi) ^ n * |t / (2 * Real.pi)| ^ n := by
    rw [abs_div, abs_of_pos hpi, ← mul_pow]
    field_simp [hpi.ne']
  rw [hscale, cglLemma62MellinLineDecayBudget]
  calc
    (2 * Real.pi) ^ n * |t / (2 * Real.pi)| ^ n *
        ‖𝓕 (cglLemma62LogMellinProfile w σ) (t / (2 * Real.pi))‖ =
      (2 * Real.pi) ^ n * (|t / (2 * Real.pi)| ^ n *
        ‖𝓕 (cglLemma62LogMellinProfile w σ) (t / (2 * Real.pi))‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfourier' (pow_nonneg hpi.le _)

/-- The source Mellin transform is absolutely integrable on every fixed
vertical line.  This is the exact vertical-integrability input for Mellin
inversion and for later contour limits. -/
theorem cglLemma62_mellinTransform_verticalIntegrable
    (w : CGLRealSmoothBump) (σ : ℝ) :
    Complex.VerticalIntegrable (cglLemma62MellinTransform w) σ := by
  have hfun :
      (fun y : ℝ => cglLemma62MellinTransform w ((σ : ℂ) + (y : ℂ) * I)) =
        fun y : ℝ =>
          𝓕 (cglLemma62LogMellinProfileSchwartz w σ : ℝ → ℂ)
            (y / (2 * Real.pi)) := by
    funext y
    rw [cglLemma62_mellinTransform_eq_fourier_logMellinProfile]
    have hprofile : (cglLemma62LogMellinProfileSchwartz w σ : ℝ → ℂ) =
        cglLemma62LogMellinProfile w σ := by
      funext u
      exact cglLemma62LogMellinProfileSchwartz_apply w σ u
    rw [hprofile]
  have hschwartz : Integrable
      (fun z : ℝ => 𝓕 (cglLemma62LogMellinProfileSchwartz w σ : ℝ → ℂ) z) := by
    have hcoe : 𝓕 (cglLemma62LogMellinProfileSchwartz w σ : ℝ → ℂ) =
        ((𝓕 (cglLemma62LogMellinProfileSchwartz w σ) : SchwartzMap ℝ ℂ) : ℝ → ℂ) :=
      (SchwartzMap.fourier_coe _).symm
    rw [hcoe]
    exact (𝓕 (cglLemma62LogMellinProfileSchwartz w σ) : SchwartzMap ℝ ℂ).integrable
  have hscale : Integrable
      (fun y : ℝ => 𝓕 (cglLemma62LogMellinProfileSchwartz w σ : ℝ → ℂ)
        (y / (2 * Real.pi))) := by
    have hne : (2 * Real.pi) ≠ 0 := by positivity
    have hcomp := hschwartz.comp_mul_left' (R := (2 * Real.pi)⁻¹) (inv_ne_zero hne)
    refine hcomp.congr ?_
    filter_upwards with y
    field_simp
  show Integrable (fun y : ℝ => cglLemma62MellinTransform w ((σ : ℂ) + y * I))
  rw [hfun]
  exact hscale

/-- The compact squared source cutoff has a convergent Mellin transform on
the initial CGL inversion line `Re(s)=2`. -/
theorem cglLemma62_mellinTransform_mellinConvergent_two
    (w : CGLRealSmoothBump) :
    MellinConvergent (fun x : ℝ =>
      w.toCGLSmoothBump.value x * w.toCGLSmoothBump.value x) (2 : ℂ) := by
  have h := mellinConvergent_schwartz (cglSmoothBumpSquare w.toCGLSmoothBump)
    (by norm_num : 0 < (2 : ℂ).re)
  have hsq : (cglSmoothBumpSquare w.toCGLSmoothBump : ℝ → ℂ) =
      fun x : ℝ => w.toCGLSmoothBump.value x * w.toCGLSmoothBump.value x := by
    funext x
    exact cglSmoothBumpSquare_apply w.toCGLSmoothBump x
  rw [← hsq]
  exact h

/-- **CGL Mellin inversion.**  The compact squared cutoff is recovered from
its source Mellin transform on the absolute-convergence line `Re(s)=2`. -/
theorem cglLemma62_mellinInv_two_eq_squaredCutoff
    (w : CGLRealSmoothBump) {x : ℝ} (hx : 0 < x) :
    mellinInv 2 (cglLemma62MellinTransform w) x =
      w.toCGLSmoothBump.value x * w.toCGLSmoothBump.value x := by
  unfold cglLemma62MellinTransform
  apply mellinInv_mellin_eq
  · exact hx
  · exact cglLemma62_mellinTransform_mellinConvergent_two w
  · exact cglLemma62_mellinTransform_verticalIntegrable w 2
  · have hsq : (cglSmoothBumpSquare w.toCGLSmoothBump : ℝ → ℂ) =
        fun y : ℝ => w.toCGLSmoothBump.value y * w.toCGLSmoothBump.value y := by
      funext y
      exact cglSmoothBumpSquare_apply w.toCGLSmoothBump y
    rw [← hsq]
    exact (cglSmoothBumpSquare w.toCGLSmoothBump).continuous.continuousAt

/-- On `Re(s)=1`, the CGL Mellin kernel is exactly the zero spatial Fourier
mode of the oscillatory cutoff kernel. -/
theorem cglLemma62_mellinTransform_one_add_it_eq_fourier_zero
    (w : CGLRealSmoothBump) (t : ℝ) :
    cglLemma62MellinTransform w ((1 : ℂ) + (t : ℂ) * I) =
      𝓕 (cglSmoothBumpHt w.toCGLSmoothBump t : ℝ → ℂ) 0 := by
  unfold cglLemma62MellinTransform
  symm
  calc
    𝓕 (cglSmoothBumpHt w.toCGLSmoothBump t : ℝ → ℂ) 0 =
        mellin (cglFourierAmplitude w.toCGLSmoothBump 0) ((1 : ℂ) + (t : ℂ) * I) :=
      cglSmoothBumpHt_fourier_eq_mellin w.toCGLSmoothBump t 0
    _ = mellin (fun x : ℝ =>
        w.toCGLSmoothBump.value x * w.toCGLSmoothBump.value x) ((1 : ℂ) + (t : ℂ) * I) := by
      congr 1
      funext x
      simp [cglFourierAmplitude]

/-- **CGL (6.2) on the initial Mellin line.**  The source Mellin kernel
decays faster than every power of the imaginary parameter, with an explicit
cutoff-dependent budget. -/
theorem cglLemma62_mellinTransform_one_add_it_rapidDecay
    (w : CGLRealSmoothBump) (n : ℕ) (t : ℝ) :
    |t| ^ n * ‖cglLemma62MellinTransform w ((1 : ℂ) + (t : ℂ) * I)‖ ≤
      cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump n := by
  rw [cglLemma62_mellinTransform_one_add_it_eq_fourier_zero]
  simpa using cglSmoothBumpHt_allOrder_reciprocalParameter_fourier_decay
    w.toCGLSmoothBump n t 0

end RHTower

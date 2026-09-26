import GaloisForLFunctions.RHTower.XiPrimeGammaNoetherAction
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Vertical decay of theta sources and escape of the canonical adjoint

Every vertical restriction of the bilateral theta transform is a rescaled
Fourier transform of an integrable exponentially tilted source. The
Riemann--Lebesgue lemma therefore forces decay. On the zero-free arithmetic
Euler line, reciprocal Noether charge one forces the adjoint norm to grow
without bound. This obstruction occurs away from all Xi poles.
-/

open Complex MeasureTheory Filter Topology
open scoped FourierTransform

noncomputable section

namespace RHTower.ThetaSourceWard

/-- Real exponential tilt of the source in physical coordinates. -/
def thetaSourceNoetherTilt (S : ThetaSource) (a x : ℝ) : ℂ :=
  (S.k x : ℂ) * Complex.exp ((a : ℂ) * (x : ℂ))

theorem integrable_thetaSourceNoetherTilt (S : ThetaSource) (a : ℝ) :
    Integrable (thetaSourceNoetherTilt S a) := integrable_bilateralLaplace S a

/-- Exact Fourier normalization of the vertical Laplace source. -/
theorem bilateralLaplace_vertical_eq_fourier (S : ThetaSource) (a t : ℝ) :
    bilateralLaplace S ((a : ℂ) + I * (t : ℂ)) =
      𝓕 (thetaSourceNoetherTilt S a) (-t / (2 * Real.pi)) := by
  rw [bilateralLaplace, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with x
  have hf : -2 * Real.pi * x * (-t / (2 * Real.pi)) = t * x := by
    field_simp
    ring
  rw [hf]
  unfold thetaSourceNoetherTilt
  have he : ((a : ℂ) + I * (t : ℂ)) * (x : ℂ) =
      ((t * x : ℝ) : ℂ) * I + (a : ℂ) * (x : ℂ) := by
    push_cast
    ring
  rw [he, Complex.exp_add]
  ring

/-- Every real tilt has vertical decay, without a zero-location assumption. -/
theorem tendsto_bilateralLaplace_vertical (S : ThetaSource) (a : ℝ) :
    Tendsto (fun t : ℝ => bilateralLaplace S ((a : ℂ) + I * (t : ℂ)))
      atTop (𝓝 0) := by
  have hr := Real.zero_at_infty_fourier (thetaSourceNoetherTilt S a)
  have hb : (atBot : Filter ℝ) ≤ cocompact ℝ := by
    rw [cocompact_eq_atBot_atTop]
    exact le_sup_left
  have ht : Tendsto (fun t : ℝ => -t / (2 * Real.pi)) atTop atBot :=
    (tendsto_div_const_atBot_of_pos (by positivity)).mpr tendsto_neg_atTop_atBot
  simpa only [← bilateralLaplace_vertical_eq_fourier] using (hr.mono_left hb).comp ht

theorem tendsto_xiPrimeGammaNoetherPath_fst :
    Tendsto (fun t => (xiPrimeGammaNoetherPath t).1) atTop (𝓝 (0 : ℂ)) := by
  simpa only [xiPrimeGammaNoetherPath, xiPrimeGammaNoetherCoordinate, Complex.ofReal_one] using
    tendsto_bilateralLaplace_vertical thetaCuspTiltSource 1

/-- Unit arithmetic Noether charge forces reciprocal growth even on the zero-free Euler line. -/
theorem tendsto_norm_xiPrimeGammaNoetherPath_snd :
    Tendsto (fun t => ‖(xiPrimeGammaNoetherPath t).2‖) atTop atTop := by
  have hzero : Tendsto (fun t => ‖(xiPrimeGammaNoetherPath t).1‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using tendsto_xiPrimeGammaNoetherPath_fst.norm
  have hpos : Tendsto (fun t => ‖(xiPrimeGammaNoetherPath t).1‖) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero,
      Eventually.of_forall (fun t => norm_pos_iff.mpr (xiPrimeGammaNoetherPath_fst_ne_zero t))⟩
  simpa only [xiPrimeGammaNoetherPath, norm_inv, Pi.inv_apply] using hpos.inv_tendsto_nhdsGT_zero

theorem xiPrimeGammaNoetherAdjoint_unbounded (C : ℝ) :
    ∃ t : ℝ, C < ‖(xiPrimeGammaNoetherPath t).2‖ :=
  (tendsto_norm_xiPrimeGammaNoetherPath_snd.eventually_gt_atTop C).exists

end RHTower.ThetaSourceWard

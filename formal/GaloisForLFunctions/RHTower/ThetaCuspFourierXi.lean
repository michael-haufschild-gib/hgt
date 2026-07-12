import GaloisForLFunctions.RHTower.ThetaCuspSchwartz
import GaloisForLFunctions.RHTower.XiThetaCriticalTrace
import GaloisForLFunctions.RHTower.XiEntireReal
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Fourier identification of the theta-cusp Schwartz source

This file develops the remaining exact Fourier identity between the actual theta-cusp Schwartz
object and the centered completed function `XiC`.
-/

open Complex Real MeasureTheory Set Filter Topology HurwitzZeta
open scoped FourierTransform SchwartzMap

noncomputable section

namespace RHTower

/-- On the critical line, `XiC` is the elementary quadratic multiplier of the pole-subtracted
completed zeta trace, together with its exact constant term. -/
theorem XiC_ofReal_eq_completedRiemannZeta₀ (t : ℝ) :
    XiC (t : ℂ) =
      (1 / 2 : ℂ) - (((t : ℂ) ^ 2 + 1 / 4) / 2) *
        completedRiemannZeta₀ ((1 : ℂ) / 2 + (t : ℂ) * I) := by
  rw [XiC, xi]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- On the positive logarithmic half-line, the completed theta source at scale `2x` is twice the
raw positive Gaussian tail used by the cusp operator. -/
theorem xiThetaLogSource_two_mul_eq_tail {x : ℝ} (hx : 0 < x) :
    xiThetaLogSource (2 * x) =
      (2 * thetaCuspTailDerivative 0 x : ℝ) := by
  rw [xiThetaLogSource_eq_positiveFormula (by linarith)]
  rw [xiThetaPositiveFormula, thetaCuspTailDerivative_zero_eq_evenKernel]
  norm_cast
  ring

theorem integrableOn_cos_mul_thetaCuspTailDerivative (m : ℕ) (t : ℝ) :
    IntegrableOn (fun x : ℝ => Real.cos (t * x) * thetaCuspTailDerivative m x) (Ioi 0) := by
  apply Integrable.bdd_mul (integrableOn_thetaCuspTailDerivative_Ioi m)
  · exact (by fun_prop : Continuous (fun x : ℝ => Real.cos (t * x))).aestronglyMeasurable.restrict
  · filter_upwards with x
    rw [Real.norm_eq_abs]
    exact abs_cos_le_one _

theorem integrableOn_sin_mul_thetaCuspTailDerivative (m : ℕ) (t : ℝ) :
    IntegrableOn (fun x : ℝ => Real.sin (t * x) * thetaCuspTailDerivative m x) (Ioi 0) := by
  apply Integrable.bdd_mul (integrableOn_thetaCuspTailDerivative_Ioi m)
  · exact (by fun_prop : Continuous (fun x : ℝ => Real.sin (t * x))).aestronglyMeasurable.restrict
  · filter_upwards with x
    rw [Real.norm_eq_abs]
    exact abs_sin_le_one _

theorem cos_mul_thetaCuspTailDerivative_tendsto_atTop_zero (m : ℕ) (t : ℝ) :
    Tendsto (fun x : ℝ => Real.cos (t * x) * thetaCuspTailDerivative m x) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hle : ∀ᶠ x : ℝ in atTop,
      ‖Real.cos (t * x) * thetaCuspTailDerivative m x‖ ≤
        ‖thetaCuspTailDerivative m x‖ := Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (by simpa using abs_cos_le_one (t * x))
  have hmajor := (thetaCuspTailDerivative_tendsto_atTop_zero m).norm
  exact squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) hle (by simpa using hmajor)

theorem sin_mul_thetaCuspTailDerivative_tendsto_atTop_zero (m : ℕ) (t : ℝ) :
    Tendsto (fun x : ℝ => Real.sin (t * x) * thetaCuspTailDerivative m x) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hle : ∀ᶠ x : ℝ in atTop,
      ‖Real.sin (t * x) * thetaCuspTailDerivative m x‖ ≤
        ‖thetaCuspTailDerivative m x‖ := Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (by simpa using abs_sin_le_one (t * x))
  have hmajor := (thetaCuspTailDerivative_tendsto_atTop_zero m).norm
  exact squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) hle (by simpa using hmajor)

/-- Twice integrating the cusp operator by parts on the positive half-line exposes the exact
constant boundary term and the quadratic spectral multiplier. -/
theorem integral_Ioi_thetaCuspFullSource_mul_cos (t : ℝ) :
    ∫ x : ℝ in Ioi 0, thetaCuspFullSource x * Real.cos (t * x) =
      1 / 4 - (t ^ 2 + 1 / 4) *
        ∫ x : ℝ in Ioi 0, thetaCuspTailDerivative 0 x * Real.cos (t * x) := by
  have hsinDeriv (x : ℝ) :
      HasDerivAt (fun y : ℝ => Real.sin (t * y)) (t * Real.cos (t * x)) x := by
    convert (Real.hasDerivAt_sin (t * x)).comp x ((hasDerivAt_id x).const_mul t) using 1
    ring
  have hcosDeriv (x : ℝ) :
      HasDerivAt (fun y : ℝ => Real.cos (t * y)) (-t * Real.sin (t * x)) x := by
    convert (Real.hasDerivAt_cos (t * x)).comp x ((hasDerivAt_id x).const_mul t) using 1
    ring
  have hsinZero : Tendsto
      (fun x : ℝ => Real.sin (t * x) * thetaCuspTailDerivative 0 x)
      (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun x : ℝ =>
        Real.sin (t * x) * thetaCuspTailDerivative 0 x) :=
      (by fun_prop : Continuous (fun x : ℝ => Real.sin (t * x))).mul
        (differentiable_thetaCuspTailDerivative 0).continuous
    simpa using (hc.continuousAt : Tendsto _ (𝓝 (0 : ℝ)) _).mono_left inf_le_left
  have hcosZero : Tendsto
      (fun x : ℝ => Real.cos (t * x) * thetaCuspTailDerivative 1 x)
      (𝓝[>] 0) (𝓝 (-(1 / 4 : ℝ))) := by
    have hc : Continuous (fun x : ℝ =>
        Real.cos (t * x) * thetaCuspTailDerivative 1 x) :=
      (by fun_prop : Continuous (fun x : ℝ => Real.cos (t * x))).mul
        (differentiable_thetaCuspTailDerivative 1).continuous
    simpa [thetaCuspTailDerivative_one_zero] using
      (hc.continuousAt : Tendsto _ (𝓝 (0 : ℝ)) _).mono_left inf_le_left
  have hsinIBP := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ))
    (u := fun x : ℝ => Real.sin (t * x))
    (u' := fun x : ℝ => t * Real.cos (t * x))
    (v := thetaCuspTailDerivative 0)
    (v' := thetaCuspTailDerivative 1)
    (fun x _ => hsinDeriv x)
    (fun x _ => hasDerivAt_thetaCuspTailDerivative 0 x)
    (integrableOn_sin_mul_thetaCuspTailDerivative 1 t)
    (by
      simpa only [Pi.mul_apply, ← mul_assoc] using
        (integrableOn_cos_mul_thetaCuspTailDerivative 0 t).const_mul t)
    hsinZero (sin_mul_thetaCuspTailDerivative_tendsto_atTop_zero 0 t)
  have hsinIdentity :
      (∫ x : ℝ in Ioi 0, Real.sin (t * x) * thetaCuspTailDerivative 1 x) =
        -t * ∫ x : ℝ in Ioi 0,
          Real.cos (t * x) * thetaCuspTailDerivative 0 x := by
    have hshape : (fun x : ℝ => (t * Real.cos (t * x)) *
        thetaCuspTailDerivative 0 x) =
        fun x => t * (Real.cos (t * x) * thetaCuspTailDerivative 0 x) := by
      funext x
      ring
    rw [hshape, integral_const_mul] at hsinIBP
    calc
      _ = -(t * ∫ x : ℝ in Ioi 0,
          Real.cos (t * x) * thetaCuspTailDerivative 0 x) := by
            simpa only [zero_sub, sub_zero] using hsinIBP
      _ = _ := by ring
  have hcosIBP := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ))
    (u := fun x : ℝ => Real.cos (t * x))
    (u' := fun x : ℝ => -t * Real.sin (t * x))
    (v := thetaCuspTailDerivative 1)
    (v' := thetaCuspTailDerivative 2)
    (fun x _ => hcosDeriv x)
    (fun x _ => hasDerivAt_thetaCuspTailDerivative 1 x)
    (integrableOn_cos_mul_thetaCuspTailDerivative 2 t)
    (by
      simpa only [Pi.mul_apply, ← mul_assoc] using
        (integrableOn_sin_mul_thetaCuspTailDerivative 1 t).const_mul (-t))
    hcosZero (cos_mul_thetaCuspTailDerivative_tendsto_atTop_zero 1 t)
  have hcosIdentity :
      (∫ x : ℝ in Ioi 0, Real.cos (t * x) * thetaCuspTailDerivative 2 x) =
        1 / 4 - t ^ 2 * ∫ x : ℝ in Ioi 0,
          Real.cos (t * x) * thetaCuspTailDerivative 0 x := by
    have hshape : (fun x : ℝ => (-t * Real.sin (t * x)) *
        thetaCuspTailDerivative 1 x) =
        fun x => (-t) * (Real.sin (t * x) * thetaCuspTailDerivative 1 x) := by
      funext x
      ring
    rw [hshape, integral_const_mul, hsinIdentity] at hcosIBP
    convert hcosIBP using 1 <;> ring
  rw [show (fun x : ℝ => thetaCuspFullSource x * Real.cos (t * x)) =
      fun x => Real.cos (t * x) * thetaCuspTailDerivative 2 x -
        (1 / 4 : ℝ) * (Real.cos (t * x) * thetaCuspTailDerivative 0 x) by
    funext x
    rw [thetaCuspFullSource_eq_tail_second_sub]
    ring]
  rw [integral_sub (integrableOn_cos_mul_thetaCuspTailDerivative 2 t)
    ((integrableOn_cos_mul_thetaCuspTailDerivative 0 t).const_mul (1 / 4 : ℝ)),
    integral_const_mul, hcosIdentity]
  have hcomm : (∫ x : ℝ in Ioi 0,
      thetaCuspTailDerivative 0 x * Real.cos (t * x)) =
      ∫ x : ℝ in Ioi 0, Real.cos (t * x) * thetaCuspTailDerivative 0 x := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hcomm]
  ring

end RHTower

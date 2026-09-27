import GaloisForLFunctions.RHTower.ThetaGammaPolarCrossingCurrent
import GaloisForLFunctions.RHTower.ThetaPrimeShiftNoetherCurrent
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Exact divergence of the continuous arithmetic current

The singular diagonal term cancels between forward and reflected sources.
The original compensated Gamma integrand supplies a locally uniform derivative
majorant, permitting differentiation of the entire continuous crossing current.
-/

noncomputable section

open MeasureTheory Filter Set Topology

namespace RHTower.ThetaSourceWard

def thetaGammaPolarSourceTerm (x u : ℝ) : ℂ :=
  (gammaSourceTerm x u : ℂ) + polarSourceTerm (1 / 2) x u + polarSourceTerm (-1 / 2) x u

theorem integrable_thetaGammaPolarSourceTerm (x : ℝ) :
    IntegrableOn (thetaGammaPolarSourceTerm x) (Ioi (0 : ℝ)) :=
  ((gammaSourceTerm_integrable x).fun_add
    (polarSourceTerm_integrable (a := 1 / 2) (by norm_num) x)).fun_add
      (polarSourceTerm_integrable (a := -1 / 2) (by norm_num) x)

theorem integral_thetaGammaPolarSourceTerm (x : ℝ) :
    (∫ u in Ioi (0 : ℝ), thetaGammaPolarSourceTerm x u) = thetaArchimedeanShiftSource x := by
  have hgp : IntegrableOn (fun u => (gammaSourceTerm x u : ℂ) + polarSourceTerm (1 / 2) x u)
      (Ioi (0 : ℝ)) := (gammaSourceTerm_integrable x).fun_add
        (polarSourceTerm_integrable (a := 1 / 2) (by norm_num) x)
  unfold thetaGammaPolarSourceTerm thetaArchimedeanShiftSource
  rw [integral_add hgp
      (polarSourceTerm_integrable (a := -1 / 2) (by norm_num) x),
    integral_add (gammaSourceTerm_integrable x)
      (polarSourceTerm_integrable (a := 1 / 2) (by norm_num) x)]
  rfl

theorem norm_thetaGammaPolarSourceTerm_le (x : ℝ) {u : ℝ} (hu : 0 < u) :
    ‖thetaGammaPolarSourceTerm x u‖ ≤ gammaSourceBound u +
      thetaCuspDerivativeExpConstant 0 * Real.exp |x| *
        (Real.exp ((-1 / 2 : ℝ) * u) + Real.exp ((-3 / 2 : ℝ) * u)) := by
  have hg : ‖(gammaSourceTerm x u : ℂ)‖ ≤ gammaSourceBound u := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_gammaSourceTerm_le_bound x hu
  have hp := norm_polarSourceTerm_le (1 / 2) x u
  have hm := norm_polarSourceTerm_le (-1 / 2) x u
  simp only [show (1 / 2 : ℝ) - 1 = -1 / 2 by norm_num] at hp
  simp only [show (-1 / 2 : ℝ) - 1 = -3 / 2 by norm_num] at hm
  calc
    _ ≤ (‖(gammaSourceTerm x u : ℂ)‖ + ‖polarSourceTerm (1 / 2) x u‖) +
        ‖polarSourceTerm (-1 / 2) x u‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (gammaSourceBound u + thetaCuspDerivativeExpConstant 0 * Real.exp |x| *
        Real.exp ((-1 / 2 : ℝ) * u)) + thetaCuspDerivativeExpConstant 0 * Real.exp |x| *
          Real.exp ((-3 / 2 : ℝ) * u) := add_le_add (add_le_add hg hp) hm
    _ = _ := by ring

def thetaGammaPolarCrossingDerivative (x u : ℝ) : ℝ :=
  ((thetaCuspFullSource x : ℂ) * (thetaGammaPolarSourceTerm x u - thetaGammaPolarSourceTerm (-x) u)).re

/-- Cancellation occurs before integration of the singular coefficient. -/
theorem thetaGammaPolarCrossingDerivative_eq (x u : ℝ) :
    thetaGammaPolarCrossingDerivative x u = thetaGammaPolarScalingKernel u *
      thetaCuspFullSource x * (thetaCuspFullSource (x + u) - thetaCuspFullSource (x - u)) := by
  have he : thetaCuspFullSource (-x + u) = thetaCuspFullSource (x - u) := by
    rw [show -x + u = -(x - u) by ring, thetaCuspFullSource_neg]
  unfold thetaGammaPolarCrossingDerivative thetaGammaPolarSourceTerm
  rw [thetaGammaPolarScalingKernel_source_decomposition,
    thetaGammaPolarScalingKernel_source_decomposition, thetaCuspFullSource_neg, he]
  simp only [← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

theorem integrable_thetaGammaPolarCrossingDerivative (x : ℝ) :
    IntegrableOn (thetaGammaPolarCrossingDerivative x) (Ioi (0 : ℝ)) := by
  change Integrable (fun u => ((thetaCuspFullSource x : ℂ) *
    (thetaGammaPolarSourceTerm x u - thetaGammaPolarSourceTerm (-x) u)).re) (volume.restrict (Ioi 0))
  simpa only [RCLike.re_to_complex, Pi.sub_apply] using
    (((integrable_thetaGammaPolarSourceTerm x).sub (integrable_thetaGammaPolarSourceTerm (-x))).const_mul
      (thetaCuspFullSource x : ℂ)).re

theorem integral_thetaGammaPolarCrossingDerivative (x : ℝ) :
    (∫ u in Ioi (0 : ℝ), thetaGammaPolarCrossingDerivative x u) =
      ((thetaCuspFullSource x : ℂ) *
        (thetaArchimedeanShiftSource x - thetaArchimedeanShiftSource (-x))).re := by
  have hi : IntegrableOn (fun u => (thetaCuspFullSource x : ℂ) *
      (thetaGammaPolarSourceTerm x u - thetaGammaPolarSourceTerm (-x) u)) (Ioi (0 : ℝ)) :=
    ((integrable_thetaGammaPolarSourceTerm x).sub
      (integrable_thetaGammaPolarSourceTerm (-x))).const_mul (thetaCuspFullSource x : ℂ)
  have h := integral_re hi
  simp only [RCLike.re_to_complex] at h
  change (∫ u in Ioi (0 : ℝ), ((thetaCuspFullSource x : ℂ) *
    (thetaGammaPolarSourceTerm x u - thetaGammaPolarSourceTerm (-x) u)).re) = _
  rw [h, integral_const_mul,
    integral_sub (integrable_thetaGammaPolarSourceTerm x) (integrable_thetaGammaPolarSourceTerm (-x)),
    integral_thetaGammaPolarSourceTerm, integral_thetaGammaPolarSourceTerm]

def thetaGammaPolarCrossingDerivativeBound (x u : ℝ) : ℝ :=
  2 * thetaCuspDerivativeExpConstant 0 * (gammaSourceBound u +
    thetaCuspDerivativeExpConstant 0 * Real.exp (|x| + 1) *
      (Real.exp ((-1 / 2 : ℝ) * u) + Real.exp ((-3 / 2 : ℝ) * u)))

theorem integrable_thetaGammaPolarCrossingDerivativeBound (x : ℝ) :
    IntegrableOn (thetaGammaPolarCrossingDerivativeBound x) (Ioi (0 : ℝ)) :=
  (gammaSourceBound_integrable.fun_add
    (((integrableOn_exp_mul_Ioi (a := -1 / 2) (by norm_num) 0).fun_add
      (integrableOn_exp_mul_Ioi (a := -3 / 2) (by norm_num) 0)).const_mul
        (thetaCuspDerivativeExpConstant 0 * Real.exp (|x| + 1)))).const_mul
          (2 * thetaCuspDerivativeExpConstant 0)

private theorem derivative_bound (x y : ℝ) (hy : y ∈ Metric.ball x 1) {u : ℝ} (hu : 0 < u) :
    ‖thetaGammaPolarCrossingDerivative y u‖ ≤ thetaGammaPolarCrossingDerivativeBound x u := by
  have hC := thetaCuspDerivativeExpConstant_nonneg 0
  have hy' : |y - x| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hy
  have habs : |y| ≤ |x| + 1 := by
    have h := abs_add_le (y - x) x
    rw [sub_add_cancel] at h
    linarith
  let B := gammaSourceBound u + thetaCuspDerivativeExpConstant 0 * Real.exp (|x| + 1) *
    (Real.exp ((-1 / 2 : ℝ) * u) + Real.exp ((-3 / 2 : ℝ) * u))
  have h₁ : ‖thetaGammaPolarSourceTerm y u‖ ≤ B :=
    (norm_thetaGammaPolarSourceTerm_le y hu).trans (by dsimp [B]; gcongr)
  have h₂ : ‖thetaGammaPolarSourceTerm (-y) u‖ ≤ B := by
    have h := norm_thetaGammaPolarSourceTerm_le (-y) hu
    rw [abs_neg] at h
    exact h.trans (by dsimp [B]; gcongr)
  have hk : ‖(thetaCuspFullSource y : ℂ)‖ ≤ thetaCuspDerivativeExpConstant 0 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_theta_le_const y
  calc
    _ ≤ ‖(thetaCuspFullSource y : ℂ) *
        (thetaGammaPolarSourceTerm y u - thetaGammaPolarSourceTerm (-y) u)‖ :=
      Complex.abs_re_le_norm _
    _ = ‖(thetaCuspFullSource y : ℂ)‖ *
        ‖thetaGammaPolarSourceTerm y u - thetaGammaPolarSourceTerm (-y) u‖ := norm_mul _ _
    _ ≤ thetaCuspDerivativeExpConstant 0 * (B + B) :=
      mul_le_mul hk ((norm_sub_le _ _).trans (add_le_add h₁ h₂)) (norm_nonneg _) hC
    _ = _ := by dsimp [B, thetaGammaPolarCrossingDerivativeBound]; ring

/-- The literal continuous current has precisely the actual Gamma/pole exchange as divergence. -/
theorem hasDerivAt_thetaGammaPolarCrossingCurrent (x : ℝ) :
    HasDerivAt (thetaGammaPolarCrossingCurrent thetaCuspTiltSource)
      (((thetaCuspFullSource x : ℂ) *
        (thetaArchimedeanShiftSource x - thetaArchimedeanShiftSource (-x))).re) x := by
  have hd (y u : ℝ) : HasDerivAt (fun z => thetaGammaPolarCrossingTerm thetaCuspTiltSource z u)
      (thetaGammaPolarCrossingDerivative y u) y := by
    simpa only [thetaGammaPolarCrossingDerivative_eq, thetaCuspTiltSource_k] using
      hasDerivAt_thetaGammaPolarCrossingTerm thetaCuspTiltSource y u
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y u => thetaGammaPolarCrossingTerm thetaCuspTiltSource y u)
    (F' := thetaGammaPolarCrossingDerivative)
    (μ := volume.restrict (Ioi (0 : ℝ))) (bound := thetaGammaPolarCrossingDerivativeBound x)
    (Metric.ball_mem_nhds x one_pos)
    (Eventually.of_forall fun y => (measurable_thetaGammaPolarCrossingTerm thetaCuspTiltSource y).aestronglyMeasurable)
    (integrable_thetaGammaPolarCrossingTerm thetaCuspTiltSource x)
    (integrable_thetaGammaPolarCrossingDerivative x).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact fun y hy => derivative_bound x y hy hu)
    (integrable_thetaGammaPolarCrossingDerivativeBound x)
    (Eventually.of_forall fun u y _ => hd y u)
  rw [integral_thetaGammaPolarCrossingDerivative] at h
  exact h.2

end RHTower.ThetaSourceWard

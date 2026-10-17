import GaloisForLFunctions.BiScaleUncertainty.SobolevTraceEnergy
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Logarithmic transport of rough Sobolev primitives

The monotone Jacobian formula transports arbitrary L2 physical velocities to
locally integrable logarithmic velocities. Absolute continuity and the derivative
formula follow from the integral construction, without applying a pointwise
chain rule at exceptional points. The actual derivative has weighted energy
equal to the physical additive Dirichlet form.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

def logPrimitive (q : Velocity) (x : ℝ) : ℝ := primitive q (Real.exp x)

def logVelocity (q : Velocity) (x : ℝ) : ℝ := Real.exp x * q (Real.exp x)

private theorem exp_substitution_of_le (g : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) :
    (∫ x in a..b, Real.exp x * g (Real.exp x)) = ∫ t in Real.exp a..Real.exp b, g t := by
  rw [intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le (Real.exp_le_exp.mpr hab),
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
  exact integral_Icc_deriv_smul_of_deriv_nonneg Real.continuous_exp.continuousOn
    (fun x _ => Real.hasDerivAt_exp x) (fun x _ => (Real.exp_pos x).le) hab

/-- Substitution does not require continuity of the integrand. -/
theorem exp_substitution (g : ℝ → ℝ) (a b : ℝ) :
    (∫ x in a..b, Real.exp x * g (Real.exp x)) = ∫ t in Real.exp a..Real.exp b, g t := by
  rcases le_total a b with h | h
  · exact exp_substitution_of_le g a b h
  · rw [intervalIntegral.integral_symm b a,
      intervalIntegral.integral_symm (Real.exp b) (Real.exp a), exp_substitution_of_le g b a h]

theorem intervalIntegrable_logVelocity (q : Velocity) (a b : ℝ) :
    IntervalIntegrable (logVelocity q) volume a b := by
  apply IntegrableOn.intervalIntegrable
  change IntegrableOn (logVelocity q) (Icc (min a b) (max a b)) volume
  have h := integrableOn_Icc_deriv_smul_iff_of_deriv_nonneg
    (g := fun t => q t) Real.continuous_exp.continuousOn
    (fun x _ => Real.hasDerivAt_exp x) (fun x _ => (Real.exp_pos x).le) (min_le_max : min a b ≤ max a b)
  apply h.mpr
  exact integrableOn_Lp_of_measure_ne_top q (by norm_num) isCompact_Icc.measure_lt_top.ne

theorem locallyIntegrable_logVelocity (q : Velocity) : LocallyIntegrable (logVelocity q) volume := by
  intro x
  refine ⟨Icc (x-1) (x+1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  exact (integrableOn_Icc_iff_integrableOn_Ioc).mpr (intervalIntegrable_logVelocity q (x-1) (x+1)).1

theorem logPrimitive_sub (q : Velocity) (a b : ℝ) :
    logPrimitive q b-logPrimitive q a = ∫ x in a..b, logVelocity q x := by
  rw [logPrimitive, logPrimitive, primitive_sub]
  exact (exp_substitution (fun t => q t) a b).symm

theorem logPrimitive_eq_integral (q : Velocity) (x : ℝ) :
    logPrimitive q x = primitive q 1 + ∫ t in 0..x, logVelocity q t := by
  have h := logPrimitive_sub q 0 x
  simp only [logPrimitive, Real.exp_zero] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

theorem absolutelyContinuous_logPrimitive (q : Velocity) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (logPrimitive q) a b := by
  have h := (intervalIntegrable_logVelocity q a b).absolutelyContinuousOnInterval_intervalIntegral
    (left_mem_uIcc : a ∈ uIcc a b)
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => logPrimitive q a) a b :=
    (contDiffOn_const : ContDiffOn ℝ 1 (fun _ : ℝ => logPrimitive q a) (uIcc a b)).absolutelyContinuousOnInterval
  have he : logPrimitive q = (fun _ : ℝ => logPrimitive q a) +
      (fun t => ∫ u in a..t, logVelocity q u) := by
    funext t
    have ht := logPrimitive_sub q a t
    simp only [Pi.add_apply]
    linarith
  rw [he]
  exact hc.add h

theorem ae_hasDerivAt_logPrimitive (q : Velocity) :
    ∀ᵐ x, HasDerivAt (logPrimitive q) (logVelocity q x) x := by
  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral
    (locallyIntegrable_logVelocity q)] with x hx
  have h := (hx 0).const_add (primitive q 1)
  simpa only [← logPrimitive_eq_integral] using h

theorem ae_deriv_logPrimitive (q : Velocity) :
    deriv (logPrimitive q) =ᵐ[volume] logVelocity q := by
  filter_upwards [ae_hasDerivAt_logPrimitive q] with x hx
  exact hx.deriv

/-- Finiteness of the actual weighted derivative energy on every logarithmic interval. -/
theorem intervalIntegrable_logDerivativeEnergy (q : Velocity) (a b : ℝ) :
    IntervalIntegrable (fun x => Real.exp (-x)*(deriv (logPrimitive q) x)^2) volume a b := by
  have hi : IntervalIntegrable (fun x => Real.exp x*(q (Real.exp x))^2) volume a b := by
    apply IntegrableOn.intervalIntegrable
    change IntegrableOn (fun x => Real.exp x*(q (Real.exp x))^2)
      (Icc (min a b) (max a b)) volume
    apply (integrableOn_Icc_deriv_smul_iff_of_deriv_nonneg
      (g := fun t => (q t)^2) Real.continuous_exp.continuousOn
      (fun x _ => Real.hasDerivAt_exp x) (fun x _ => (Real.exp_pos x).le)
      (min_le_max : min a b ≤ max a b)).mpr
    exact (integrable_velocity_sq q).integrableOn
  apply hi.congr_ae
  apply ae_restrict_of_ae
  filter_upwards [ae_deriv_logPrimitive q] with x hx
  rw [hx, logVelocity, Real.exp_neg]
  field_simp

/-- The actual a.e. derivative of the rough logarithmic state has the correct energy. -/
theorem log_energy_eq (q : Velocity) (a b : ℝ) :
    (∫ x in a..b, Real.exp (-x)*(deriv (logPrimitive q) x)^2) =
      energy q (Real.exp a) (Real.exp b) := by
  calc
    _ = ∫ x in a..b, Real.exp x*(q (Real.exp x))^2 := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_deriv_logPrimitive q] with x hx
      intro _
      rw [hx, logVelocity, Real.exp_neg]
      field_simp
    _ = _ := exp_substitution (fun t => (q t)^2) a b

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear

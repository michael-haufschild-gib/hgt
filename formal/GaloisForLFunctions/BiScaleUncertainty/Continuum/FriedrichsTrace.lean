import GaloisForLFunctions.BiScaleUncertainty.ContinuumShearDirichlet
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A one-boundary Friedrichs estimate for continuum shear states

Ming–Yu's mixed-boundary estimate (https://arxiv.org/abs/2611.17054, Lemma 3.3)
applies to the corpus's canonical primitives after subtracting their left
boundary value. Cauchy–Schwarz on every prefix, then integration over the
window, gives the factor one half. The velocity is arbitrary and continuous;
no trace or derivative hypothesis is added.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal

namespace GaloisForLFunctions.BiScaleUncertainty.ContinuumShear

/-- Uniform control of an anchored primitive on a physical window. -/
theorem primitive_friedrichs (q : C(ℝ, ℝ)) (a : ℝ) (r : ℝ≥0) :
    (∫ t in a..(a + r), (primitive q t - primitive q a)^2) ≤
      (r : ℝ)^2 / 2 * energy q a (a + r) := by
  have hp : Continuous (primitive q) := continuous_iff_continuousAt.mpr
    fun x => (hasDerivAt_primitive q x).continuousAt
  have hprefix (t : ℝ) (ht : t ∈ Icc a (a + r)) :
      (primitive q t - primitive q a)^2 ≤ (t - a) * energy q a (a + r) := by
    have hi := increment_sq_le_energy q a ⟨t - a, sub_nonneg.mpr ht.1⟩
    change (primitive q (a + (t - a)) - primitive q a)^2 ≤
      (t - a) * energy q a (a + (t - a)) at hi
    rw [show a + (t - a) = t by ring] at hi
    have hadd : energy q a t + energy q t (a + r) = energy q a (a + r) :=
      intervalIntegral.integral_add_adjacent_intervals
        ((q.continuous.pow 2).intervalIntegrable a t)
        ((q.continuous.pow 2).intervalIntegrable t (a + r))
    have hn : 0 ≤ energy q t (a + r) :=
      intervalIntegral.integral_nonneg_of_forall ht.2 (fun x => sq_nonneg (q x))
    have hm : energy q a t ≤ energy q a (a + r) := by linarith only [hadd, hn]
    exact hi.trans (mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr ht.1))
  calc
    _ ≤ ∫ t in a..(a + r), (t - a) * energy q a (a + r) :=
      intervalIntegral.integral_mono_on (le_add_of_nonneg_right r.coe_nonneg)
        (((hp.sub continuous_const).pow 2).intervalIntegrable _ _)
        (((continuous_id.sub continuous_const).mul continuous_const).intervalIntegrable _ _)
        hprefix
    _ = _ := by
      rw [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_sub (f := fun t : ℝ => t) (g := fun _ => a)
          (μ := volume) (continuous_id.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _), integral_id,
        intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring

#print axioms primitive_friedrichs

end GaloisForLFunctions.BiScaleUncertainty.ContinuumShear

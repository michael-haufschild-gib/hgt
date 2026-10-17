import GaloisForLFunctions.BiScaleUncertainty.ContinuumShearDirichlet
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Exact trace energy for Sobolev primitives

Every real L2 velocity gives a canonical locally absolutely continuous primitive.
Its derivative agrees with the velocity almost everywhere. The endpoint trace
inequality and square remainder therefore apply to rough states, including
piecewise affine interpolants, without a smoothness or integrability premise.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators NNReal Topology

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

abbrev Velocity := Lp ℝ 2 (volume : Measure ℝ)

def primitive (q : Velocity) (t : ℝ) : ℝ := ∫ u in 0..t, q u

def energy (q : Velocity) (a b : ℝ) : ℝ := ∫ t in a..b, (q t)^2

theorem intervalIntegrable_velocity (q : Velocity) (a b : ℝ) :
    IntervalIntegrable (fun t => q t) volume a b :=
  (integrableOn_Lp_of_measure_ne_top q (by norm_num)
    (isCompact_uIcc.measure_lt_top.ne)).intervalIntegrable

theorem locallyIntegrable_velocity (q : Velocity) : LocallyIntegrable (fun t => q t) volume :=
  locallyIntegrable_iff.mpr fun _ hs =>
    integrableOn_Lp_of_measure_ne_top q (by norm_num) hs.measure_lt_top.ne

theorem integrable_velocity_sq (q : Velocity) : Integrable (fun t => (q t)^2) :=
  (Lp.memLp q).integrable_sq

theorem primitive_sub (q : Velocity) (a b : ℝ) :
    primitive q b - primitive q a = ∫ t in a..b, q t := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_velocity q 0 a) (intervalIntegrable_velocity q a b)
  dsimp [primitive]
  linarith

theorem absolutelyContinuous_primitive (q : Velocity) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (primitive q) a b := by
  have h := (intervalIntegrable_velocity q a b).absolutelyContinuousOnInterval_intervalIntegral
    (left_mem_uIcc : a ∈ uIcc a b)
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => primitive q a) a b :=
    (contDiffOn_const : ContDiffOn ℝ 1 (fun _ : ℝ => primitive q a) (uIcc a b)).absolutelyContinuousOnInterval
  have he : primitive q = (fun _ : ℝ => primitive q a) + (fun t => ∫ u in a..t, q u) := by
    funext t
    have ht := primitive_sub q a t
    simp only [Pi.add_apply]
    linarith
  rw [he]
  exact hc.add h

theorem ae_hasDerivAt_primitive (q : Velocity) :
    ∀ᵐ t, HasDerivAt (primitive q) (q t) t := by
  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral (locallyIntegrable_velocity q)] with t ht
  exact ht 0

theorem ae_deriv_primitive (q : Velocity) : deriv (primitive q) =ᵐ[volume] fun t => q t := by
  filter_upwards [ae_hasDerivAt_primitive q] with t ht
  exact ht.deriv

theorem energy_eq_integral_deriv (q : Velocity) (a b : ℝ) :
    energy q a b = ∫ t in a..b, (deriv (primitive q) t)^2 := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ae_deriv_primitive q] with t ht
  intro _
  rw [ht]

theorem integral_scaled_deviation_sq (q : Velocity) (a b L c : ℝ) :
    (∫ t in a..b, (L*q t-c)^2) = L^2 * energy q a b -
      2*L*c*(primitive q b-primitive q a) + (b-a)*c^2 := by
  have hq := intervalIntegrable_velocity q a b
  have hs := (integrable_velocity_sq q).intervalIntegrable (a := a) (b := b)
  simp_rw [show ∀ t : ℝ, (L*q t-c)^2 = (L^2*(q t)^2-(2*L*c)*q t)+c^2 by intro t; ring]
  rw [intervalIntegral.integral_add
    (f := fun t => L^2*(q t)^2-(2*L*c)*q t) (g := fun _ => c^2)
    ((hs.const_mul _).sub (hq.const_mul _)) (continuous_const.intervalIntegrable a b)]
  rw [intervalIntegral.integral_sub
    (f := fun t => L^2*(q t)^2) (g := fun t => (2*L*c)*q t)
    (hs.const_mul _) (hq.const_mul _)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    ← primitive_sub, intervalIntegral.integral_const]
  rfl

theorem interval_trace_defect (q : Velocity) (a b : ℝ) :
    (∫ t in a..b, ((b-a)*q t-(primitive q b-primitive q a))^2) =
      (b-a)^2*energy q a b-(b-a)*(primitive q b-primitive q a)^2 := by
  rw [integral_scaled_deviation_sq]
  ring

theorem increment_sq_le_energy (q : Velocity) (a : ℝ) (r : ℝ≥0) :
    (primitive q (a+r)-primitive q a)^2 ≤ (r : ℝ)*energy q a (a+r) := by
  have h := interval_trace_defect q a (a+r)
  have he : a+(r : ℝ)-a = r := by ring
  rw [he] at h
  have hn := intervalIntegral.integral_nonneg_of_forall (a := a) (b := a+r) (μ := volume)
    (le_add_of_nonneg_right r.coe_nonneg)
    (fun t => sq_nonneg ((r : ℝ)*q t-(primitive q (a+r)-primitive q a)))
  by_cases hr : (r : ℝ) = 0
  · simp [hr]
  · have hp : 0 < (r : ℝ) := lt_of_le_of_ne r.coe_nonneg (Ne.symm hr)
    have hm : 0 ≤ (r : ℝ)*((r : ℝ)*energy q a (a+r)-(primitive q (a+r)-primitive q a)^2) := by
      nlinarith [h]
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hp).mp hm)

theorem sum_cell_energy (q : Velocity) (a k : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, energy q (a+k*n) (a+k*(n+1))) = energy q a (a+k*N) := by
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun n : ℕ => a+k*n) (n := N) (μ := volume) (f := fun t => (q t)^2)
    (fun n _ => (integrable_velocity_sq q).intervalIntegrable)
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero, add_zero, energy] using h

/-- The exact orthogonal defect of all unit-cell traces of a Sobolev primitive. -/
theorem unit_trace_energy_decomposition (q : Velocity) (a : ℝ) (N : ℕ) :
    energy q a (a+N) =
      (∑ n ∈ Finset.range N, (primitive q (a+(n+1))-primitive q (a+n))^2) +
      ∑ n ∈ Finset.range N, ∫ t in (a+n)..(a+(n+1)),
        (q t-(primitive q (a+(n+1))-primitive q (a+n)))^2 := by
  have he (n : ℕ) : (∫ t in (a+n)..(a+(n+1)),
        (q t-(primitive q (a+(n+1))-primitive q (a+n)))^2) =
      energy q (a+n) (a+(n+1))-(primitive q (a+(n+1))-primitive q (a+n))^2 := by
    have h := integral_scaled_deviation_sq q (a+n) (a+(n+1)) 1
      (primitive q (a+(n+1))-primitive q (a+n))
    simp only [one_mul, one_pow] at h
    rw [h]
    ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib]
  have hs := sum_cell_energy q a 1 N
  simp only [one_mul] at hs
  rw [hs]
  ring

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear

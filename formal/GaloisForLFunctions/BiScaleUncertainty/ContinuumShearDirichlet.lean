import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Tactic

/-!
# Logarithmic shear and the exact additive Dirichlet trace defect

Primitives of arbitrary continuous velocities supply actual continuously differentiable
states. Their additive Dirichlet energy becomes the weighted logarithmic energy
`∫ exp (-x) * (deriv f x)^2`. On each physical interval the endpoint trace cost
has an exact square remainder. Summing over dilated cells gives the continuum
multiplicative-to-additive energy inequality with its full defect.
-/

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory Set

namespace GaloisForLFunctions.BiScaleUncertainty.ContinuumShear

set_option autoImplicit false

/-- Additive translation by a nonnegative physical distance in logarithmic coordinates. -/
def shear (b : ℝ≥0) (x : ℝ) : ℝ := Real.log (Real.exp x + b)

theorem exp_shear (b : ℝ≥0) (x : ℝ) :
    Real.exp (shear b x) = Real.exp x + b :=
  Real.exp_log (add_pos_of_pos_of_nonneg (Real.exp_pos x) b.coe_nonneg)

theorem shear_zero (x : ℝ) : shear 0 x = x := by
  simp [shear]

theorem shear_add (b c : ℝ≥0) (x : ℝ) :
    shear b (shear c x) = shear (b + c) x := by
  simp only [shear, Real.exp_log (add_pos_of_pos_of_nonneg (Real.exp_pos x) c.coe_nonneg),
    NNReal.coe_add]
  congr 1
  ring

/-- The affine semigroup relation; the shear distance scales with dilation. -/
theorem shear_dilation (b : ℝ≥0) (s x : ℝ) :
    shear (⟨Real.exp s, (Real.exp_pos s).le⟩ * b) (x + s) = shear b x + s := by
  apply Real.exp_injective
  rw [exp_shear, Real.exp_add, Real.exp_add, exp_shear]
  change Real.exp x * Real.exp s + Real.exp s * (b : ℝ) =
    (Real.exp x + b) * Real.exp s
  ring

theorem hasDerivAt_shear (b : ℝ≥0) (x : ℝ) :
    HasDerivAt (shear b) (Real.exp x / (Real.exp x + b)) x := by
  exact ((Real.hasDerivAt_exp x).add_const (b : ℝ)).log
    (ne_of_gt (add_pos_of_pos_of_nonneg (Real.exp_pos x) b.coe_nonneg))

/-- Every positive integer successor is the unit shear of its logarithm. -/
theorem shear_one_log_succ (n : ℕ) :
    shear 1 (Real.log (n + 1 : ℝ)) = Real.log (n + 2 : ℝ) := by
  rw [shear, Real.exp_log (by positivity)]
  congr 1
  simp only [NNReal.coe_one]
  ring

/-- A canonical continuously differentiable physical state. -/
def primitive (q : C(ℝ, ℝ)) (t : ℝ) : ℝ := ∫ u in 0..t, q u

/-- The same state in logarithmic coordinates. -/
def logPrimitive (q : C(ℝ, ℝ)) (x : ℝ) : ℝ := primitive q (Real.exp x)

/-- Physical additive Dirichlet energy, with oriented endpoints. -/
def energy (q : C(ℝ, ℝ)) (a b : ℝ) : ℝ := ∫ t in a..b, (q t)^2

theorem hasDerivAt_primitive (q : C(ℝ, ℝ)) (t : ℝ) :
    HasDerivAt (primitive q) (q t) t := by
  exact intervalIntegral.integral_hasDerivAt_right (q.continuous.intervalIntegrable 0 t)
    q.continuous.stronglyMeasurable.stronglyMeasurableAtFilter q.continuous.continuousAt

theorem hasDerivAt_logPrimitive (q : C(ℝ, ℝ)) (x : ℝ) :
    HasDerivAt (logPrimitive q) (q (Real.exp x) * Real.exp x) x :=
  (hasDerivAt_primitive q (Real.exp x)).comp x (Real.hasDerivAt_exp x)

theorem primitive_sub (q : C(ℝ, ℝ)) (a b : ℝ) :
    primitive q b - primitive q a = ∫ t in a..b, q t := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume) (q.continuous.intervalIntegrable 0 a) (q.continuous.intervalIntegrable a b)
  dsimp [primitive]
  linarith

/-- The logarithmic weight is forced by the physical additive Dirichlet form. -/
theorem log_energy_eq (q : C(ℝ, ℝ)) (u v : ℝ) :
    (∫ x in u..v, Real.exp (-x) * (deriv (logPrimitive q) x)^2) =
      energy q (Real.exp u) (Real.exp v) := by
  calc
    _ = ∫ x in u..v, (q (Real.exp x))^2 * Real.exp x := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [(hasDerivAt_logPrimitive q x).deriv, Real.exp_neg]
      field_simp
    _ = _ := intervalIntegral.integral_comp_mul_deriv
      (fun x _ => Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn
      (q.continuous.pow 2)

/-- Square completion on every oriented interval, without dividing by its length. -/
theorem integral_scaled_deviation_sq (q : C(ℝ, ℝ)) (a b L c : ℝ) :
    (∫ t in a..b, (L * q t - c)^2) =
      L^2 * energy q a b - 2 * L * c * (primitive q b - primitive q a) +
        (b - a) * c^2 := by
  simp_rw [show ∀ t : ℝ, (L * q t - c)^2 =
    (L^2 * (q t)^2 - (2 * L * c) * q t) + c^2 by intro t; ring]
  rw [intervalIntegral.integral_add
    (f := fun t => L^2 * (q t)^2 - (2 * L * c) * q t) (g := fun _ => c^2)
    ((((q.continuous.pow 2).const_mul (L^2)).sub
      (q.continuous.const_mul (2*L*c))).intervalIntegrable a b)
    (continuous_const.intervalIntegrable a b)]
  rw [intervalIntegral.integral_sub
    (f := fun t => L^2 * (q t)^2) (g := fun t => (2*L*c) * q t)
    (((q.continuous.pow 2).const_mul (L^2)).intervalIntegrable a b)
    ((q.continuous.const_mul (2*L*c)).intervalIntegrable a b)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    ← primitive_sub, intervalIntegral.integral_const]
  rfl

/-- Exact continuum defect above the endpoint trace energy. -/
theorem interval_trace_defect (q : C(ℝ, ℝ)) (a b : ℝ) :
    (∫ t in a..b, ((b-a) * q t - (primitive q b - primitive q a))^2) =
      (b-a)^2 * energy q a b - (b-a) * (primitive q b - primitive q a)^2 := by
  rw [integral_scaled_deviation_sq]
  ring

/-- Endpoint increment control for every nonnegative physical step. -/
theorem increment_sq_le_energy (q : C(ℝ, ℝ)) (a : ℝ) (r : ℝ≥0) :
    (primitive q (a + r) - primitive q a)^2 ≤ (r : ℝ) * energy q a (a + r) := by
  have h := interval_trace_defect q a (a + r)
  have hn := intervalIntegral.integral_nonneg_of_forall (a := a) (b := a+r) (μ := volume)
    (le_add_of_nonneg_right r.coe_nonneg)
    (fun t : ℝ => sq_nonneg ((a + (r : ℝ) - a) * q t -
      (primitive q (a + r) - primitive q a)))
  by_cases hr : (r : ℝ) = 0
  · simp [hr]
  · have hp : 0 < (r : ℝ) := lt_of_le_of_ne r.coe_nonneg (Ne.symm hr)
    have he : a + (r : ℝ) - a = r := by ring
    rw [he] at h hn
    have hm : 0 ≤ (r : ℝ) * ((r : ℝ) * energy q a (a + r) -
        (primitive q (a + r) - primitive q a)^2) := by nlinarith [h]
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hp).mp hm)

/-- The additive shear has resistance exactly its physical step, independent of position. -/
theorem shear_increment_sq_le_energy (q : C(ℝ, ℝ)) (x : ℝ) (b : ℝ≥0) :
    (logPrimitive q (shear b x) - logPrimitive q x)^2 ≤
      (b : ℝ) * ∫ y in x..shear b x, Real.exp (-y) * (deriv (logPrimitive q) y)^2 := by
  rw [log_energy_eq]
  simp only [logPrimitive, exp_shear]
  exact increment_sq_le_energy q (Real.exp x) b

/-- Exact partition of continuum energy across equally spaced physical cells. -/
theorem sum_cell_energy (q : C(ℝ, ℝ)) (a k : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, energy q (a+k*n) (a+k*(n+1))) = energy q a (a+k*N) := by
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun n : ℕ => a + k * n) (n := N) (μ := volume)
    (f := fun t => (q t)^2)
    (fun n _ => (q.continuous.pow 2).intervalIntegrable (a+k*n) (a+k*(↑(n+1))))
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero, add_zero, energy] using h

/-- The continuum lift of the multiplicative-to-additive Dirichlet inequality. -/
theorem sum_dilated_increment_sq_le (q : C(ℝ, ℝ)) (a : ℝ) (k : ℝ≥0) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (primitive q (a+k*(n+1)) - primitive q (a+k*n))^2) ≤
        (k : ℝ) * energy q a (a+k*N) := by
  calc
    _ ≤ ∑ n ∈ Finset.range N, (k : ℝ) * energy q (a+k*n) (a+k*(n+1)) := by
      apply Finset.sum_le_sum
      intro n _
      have he : a + (k : ℝ) * n + k = a + (k : ℝ) * (n+1) := by ring
      simpa only [he] using increment_sq_le_energy q (a+(k : ℝ)*n) k
    _ = _ := by rw [← Finset.mul_sum, sum_cell_energy]

/-- Exact defect of the dilated-cell inequality, valid even for oriented cells. -/
theorem sum_dilated_trace_defect (q : C(ℝ, ℝ)) (a k : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, ∫ t in (a+k*n)..(a+k*(n+1)),
      (k * q t - (primitive q (a+k*(n+1)) - primitive q (a+k*n)))^2) =
    k^2 * energy q a (a+k*N) -
      k * ∑ n ∈ Finset.range N,
        (primitive q (a+k*(n+1)) - primitive q (a+k*n))^2 := by
  calc
    _ = ∑ n ∈ Finset.range N,
        (k^2 * energy q (a+k*n) (a+k*(n+1)) -
          k * (primitive q (a+k*(n+1)) - primitive q (a+k*n))^2) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [integral_scaled_deviation_sq]
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_cell_energy]

/-- Unit-cell trace energy and the exact nonnegative interpolation remainder. -/
theorem unit_trace_energy_decomposition (q : C(ℝ, ℝ)) (a : ℝ) (N : ℕ) :
    energy q a (a+N) =
      (∑ n ∈ Finset.range N, (primitive q (a+(n+1)) - primitive q (a+n))^2) +
      ∑ n ∈ Finset.range N, ∫ t in (a+n)..(a+(n+1)),
        (q t - (primitive q (a+(n+1)) - primitive q (a+n)))^2 := by
  have h := sum_dilated_trace_defect q a 1 N
  simp only [one_pow, one_mul] at h
  linarith

theorem primitive_const (c t : ℝ) :
    primitive (ContinuousMap.const ℝ c) t = t*c := by
  simp [primitive]

theorem energy_const (c a b : ℝ) :
    energy (ContinuousMap.const ℝ c) a b = (b-a)*c^2 := by
  simp [energy]

/-- Constant physical velocities attain the endpoint coefficient exactly. -/
theorem increment_sq_eq_energy_const (c a : ℝ) (r : ℝ≥0) :
    (primitive (ContinuousMap.const ℝ c) (a+r) - primitive (ContinuousMap.const ℝ c) a)^2 =
      (r : ℝ) * energy (ContinuousMap.const ℝ c) a (a+r) := by
  rw [primitive_const, primitive_const, energy_const]
  ring

/-- Additive Dirichlet energy for an arbitrary continuous logarithmic velocity.
Unlike `logPrimitive`, this does not impose extension across physical zero. -/
def logarithmicEnergy (v : C(ℝ, ℝ)) (a b : ℝ) : ℝ :=
  ∫ x in a..b, Real.exp (-x) * (v x)^2

theorem logarithmicEnergy_eq_derivative (v : C(ℝ, ℝ)) (a b : ℝ) :
    logarithmicEnergy v a b = ∫ x in a..b, Real.exp (-x) * (deriv (primitive v) x)^2 := by
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [(hasDerivAt_primitive v x).deriv]

/-- Weighted square completion for arbitrary logarithmic velocities. -/
theorem logarithmic_scaled_deviation (v : C(ℝ, ℝ)) (a b L c : ℝ) :
    (∫ x in a..b, Real.exp (-x) * (L*v x - c*Real.exp x)^2) =
      L^2 * logarithmicEnergy v a b - 2*L*c*(primitive v b - primitive v a) +
        c^2 * (Real.exp b - Real.exp a) := by
  have hexp : (∫ x in a..b, Real.exp x) = Real.exp b - Real.exp a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => Real.hasDerivAt_exp x)
      (Real.continuous_exp.intervalIntegrable a b)
  have hw : Continuous (fun x : ℝ => Real.exp (-x) * (v x)^2) :=
    (Real.continuous_exp.comp continuous_neg).mul (v.continuous.pow 2)
  have he (x : ℝ) : Real.exp (-x) * (L*v x - c*Real.exp x)^2 =
      (L^2 * (Real.exp (-x) * (v x)^2) - (2*L*c)*v x) + c^2 * Real.exp x := by
    rw [Real.exp_neg]
    field_simp
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_add
    (f := fun x => L^2 * (Real.exp (-x) * (v x)^2) - (2*L*c)*v x)
    (g := fun x => c^2 * Real.exp x)
    (((hw.const_mul _).sub (v.continuous.const_mul _)).intervalIntegrable a b)
    ((Real.continuous_exp.const_mul _).intervalIntegrable a b)]
  rw [intervalIntegral.integral_sub
    (f := fun x => L^2 * (Real.exp (-x) * (v x)^2)) (g := fun x => (2*L*c)*v x)
    ((hw.const_mul _).intervalIntegrable a b) ((v.continuous.const_mul _).intervalIntegrable a b)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, ← primitive_sub, hexp]
  rfl

/-- Exact endpoint resistance defect, without any physical-origin extension. -/
theorem logarithmic_trace_defect (v : C(ℝ, ℝ)) (a b : ℝ) :
    (∫ x in a..b, Real.exp (-x) *
      ((Real.exp b - Real.exp a)*v x - (primitive v b - primitive v a)*Real.exp x)^2) =
      (Real.exp b - Real.exp a)^2 * logarithmicEnergy v a b -
        (Real.exp b - Real.exp a)*(primitive v b - primitive v a)^2 := by
  rw [logarithmic_scaled_deviation]
  ring

theorem logarithmic_increment_sq_le (v : C(ℝ, ℝ)) (a : ℝ) (r : ℝ≥0) :
    (primitive v (a+r) - primitive v a)^2 ≤
      (Real.exp (a+r) - Real.exp a) * logarithmicEnergy v a (a+r) := by
  have h := logarithmic_trace_defect v a (a+r)
  have hn := intervalIntegral.integral_nonneg_of_forall (a := a) (b := a+r) (μ := volume)
    (le_add_of_nonneg_right r.coe_nonneg)
    (fun x => mul_nonneg (Real.exp_pos (-x)).le
      (sq_nonneg ((Real.exp (a+r) - Real.exp a)*v x -
        (primitive v (a+r) - primitive v a)*Real.exp x)))
  by_cases hr : (r : ℝ) = 0
  · simp [hr]
  · have hp : 0 < Real.exp (a+r) - Real.exp a :=
      sub_pos.mpr (Real.exp_lt_exp.mpr (lt_add_of_pos_right a
        (lt_of_le_of_ne r.coe_nonneg (Ne.symm hr))))
    have hm : 0 ≤ (Real.exp (a+r) - Real.exp a) *
        ((Real.exp (a+r) - Real.exp a)*logarithmicEnergy v a (a+r) -
          (primitive v (a+r) - primitive v a)^2) := by nlinarith [h]
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hp).mp hm)

theorem le_shear (b : ℝ≥0) (x : ℝ) : x ≤ shear b x := by
  apply Real.exp_le_exp.mp
  rw [exp_shear]
  exact le_add_of_nonneg_right b.coe_nonneg

/-- Shear control for arbitrary continuous logarithmic velocities. -/
theorem logarithmic_shear_increment_sq_le (v : C(ℝ, ℝ)) (x : ℝ) (b : ℝ≥0) :
    (primitive v (shear b x) - primitive v x)^2 ≤
      (b : ℝ) * logarithmicEnergy v x (shear b x) := by
  have h := logarithmic_increment_sq_le v x
    ⟨shear b x - x, sub_nonneg.mpr (le_shear b x)⟩
  change (primitive v (x+(shear b x-x)) - primitive v x)^2 ≤
    (Real.exp (x+(shear b x-x)) - Real.exp x) *
      logarithmicEnergy v x (x+(shear b x-x)) at h
  have he : x + (shear b x - x) = shear b x := by ring
  rw [he, exp_shear, add_sub_cancel_left] at h
  exact h

/-- The dilated-cell inequality for arbitrary logarithmic velocities, without
requiring their physical pullbacks to extend to zero. -/
theorem sum_logarithmic_dilated_increment_sq_le (v : C(ℝ, ℝ)) (a : ℝ)
    (k : ℝ≥0) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (primitive v (Real.log (Real.exp a + (k : ℝ)*(n+1))) -
        primitive v (Real.log (Real.exp a + (k : ℝ)*n)))^2) ≤
      (k : ℝ) * logarithmicEnergy v a (Real.log (Real.exp a + (k : ℝ)*N)) := by
  have hs (n : ℕ) : shear k (Real.log (Real.exp a + (k : ℝ)*n)) =
      Real.log (Real.exp a + (k : ℝ)*(n+1)) := by
    rw [shear, Real.exp_log (by positivity)]
    congr 1
    ring
  have hw : Continuous (fun x : ℝ => Real.exp (-x) * (v x)^2) :=
    (Real.continuous_exp.comp continuous_neg).mul (v.continuous.pow 2)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun n : ℕ => Real.log (Real.exp a + (k : ℝ)*n)) (n := N) (μ := volume)
    (f := fun x => Real.exp (-x) * (v x)^2)
    (fun n _ => hw.intervalIntegrable _ _)
  have he : (∑ n ∈ Finset.range N,
      logarithmicEnergy v (Real.log (Real.exp a + (k : ℝ)*n))
        (Real.log (Real.exp a + (k : ℝ)*(n+1)))) =
      logarithmicEnergy v a (Real.log (Real.exp a + (k : ℝ)*N)) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero, add_zero,
      Real.log_exp, logarithmicEnergy] using hsum
  calc
    _ ≤ ∑ n ∈ Finset.range N, (k : ℝ) *
        logarithmicEnergy v (Real.log (Real.exp a + (k : ℝ)*n))
          (Real.log (Real.exp a + (k : ℝ)*(n+1))) := by
      apply Finset.sum_le_sum
      intro n _
      simpa only [hs n] using
        logarithmic_shear_increment_sq_le v (Real.log (Real.exp a + (k : ℝ)*n)) k
    _ = _ := by rw [← Finset.mul_sum, he]

/-- Quantitative affine noncommutativity. The commutator interval has physical
length `(exp s - 1) * b`, independent of the base point. -/
theorem affine_commutator_sq_le (v : C(ℝ, ℝ)) (b s : ℝ≥0) (x : ℝ) :
    (primitive v (shear b x + s) - primitive v (shear b (x+s)))^2 ≤
      ((Real.exp (s : ℝ) - 1) * (b : ℝ)) *
        logarithmicEnergy v (shear b (x+s)) (shear b x+s) := by
  have hs : 0 ≤ Real.exp (s : ℝ) - 1 := by
    have h := Real.exp_le_exp.mpr s.coe_nonneg
    simpa only [Real.exp_zero, sub_nonneg] using h
  have he : Real.exp (shear b x+s) - Real.exp (shear b (x+s)) =
      (Real.exp (s : ℝ) - 1) * (b : ℝ) := by
    simp only [Real.exp_add, exp_shear]
    ring
  have hab : shear b (x+s) ≤ shear b x+s := by
    apply Real.exp_le_exp.mp
    have hn := mul_nonneg hs b.coe_nonneg
    linarith [he]
  have h := logarithmic_increment_sq_le v (shear b (x+s))
    ⟨shear b x+s - shear b (x+s), sub_nonneg.mpr hab⟩
  change (primitive v (shear b (x+s) + (shear b x+s - shear b (x+s))) -
      primitive v (shear b (x+s)))^2 ≤
    (Real.exp (shear b (x+s) + (shear b x+s - shear b (x+s))) - Real.exp (shear b (x+s))) *
      logarithmicEnergy v (shear b (x+s))
        (shear b (x+s) + (shear b x+s - shear b (x+s))) at h
  have hz : shear b (x+s) + (shear b x+s - shear b (x+s)) = shear b x+s := by ring
  rw [hz, he] at h
  exact h

end GaloisForLFunctions.BiScaleUncertainty.ContinuumShear

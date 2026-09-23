import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinEnergy
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Complete undamped spin precession and the failure of energy-only relaxation

The zero-damping boundary of Schaffer–Exl's spin evolution (arXiv:2609.04530)
has exact periodic orbits, constant latitude energy, and constant Euclidean
speed. Every finite-chart orbit converges exactly when its chart coordinate
is zero. Exponentially constructed nonzero coordinates therefore give closed
nonconvergent trajectories with infinite total arclength. Together with the
positive-damping arctangent formula, this identifies an exact geometric boundary.
-/

set_option autoImplicit false
open scoped Matrix RealInnerProductSpace
open Filter
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- With zero damping, half a precession turn negates the complex chart coordinate. -/
theorem spinPlaneFlow_zero_damping_pi (z : ℂ) : spinPlaneFlow 0 z Real.pi = -z := by
  have he : spinPlaneRate 0 * (Real.pi : ℂ) = -((Real.pi : ℂ) * Complex.I) := by
    simp [spinPlaneRate, mul_comm]
  rw [spinPlaneFlow, he, Complex.exp_neg_pi_mul_I, neg_one_mul]

/-- Undamped precession closes exactly after one full turn. -/
theorem spinPlaneFlow_zero_damping_two_pi (z : ℂ) : spinPlaneFlow 0 z (2 * Real.pi) = z := by
  rw [show 2 * Real.pi = Real.pi + Real.pi by ring, spinPlaneFlow_add,
    spinPlaneFlow_zero_damping_pi, spinPlaneFlow_zero_damping_pi, neg_neg]

/-- The actual unit-spin ODE has period two pi at zero damping. -/
theorem spinSphereFlow_zero_damping_periodic (z : ℂ) :
    Function.Periodic (spinSphereFlow 0 z) (2 * Real.pi) := by
  intro t
  simp only [spinSphereFlow, spinPlaneFlow_add, spinPlaneFlow_zero_damping_two_pi]

/-- The undamped spin's latitude energy is constant even on nonstationary orbits. -/
theorem spinSphereFlow_zero_damping_energy (z : ℂ) (t : ℝ) :
    spinSphereFlow 0 z t (2 : Fin 3) = (‖z‖ ^ (2 : ℕ) - 1) / (1 + ‖z‖ ^ (2 : ℕ)) := by
  simp [spinSphereFlow_energy]

/-- Undamped precession has an exact, time-independent Euclidean speed. -/
theorem spinSphereFlow_zero_damping_speed (z : ℂ) (t : ℝ) :
    ‖spinSphereField 0 (spinSphereFlow 0 z t)‖ = 2 * ‖z‖ / (1 + ‖z‖ ^ (2 : ℕ)) := by
  rw [spinSphereFlow_speed, norm_mul, spinPlaneFlow_norm]
  simp [spinPlaneRate]

/-- The undamped speed integral grows linearly with oriented elapsed time. -/
theorem spinSphereFlow_zero_damping_integral_speed (z : ℂ) (s t : ℝ) :
    (∫ v in s..t, ‖spinSphereField 0 (spinSphereFlow 0 z v)‖) =
      (t - s) * (2 * ‖z‖ / (1 + ‖z‖ ^ (2 : ℕ))) := by
  simp only [spinSphereFlow_zero_damping_speed, intervalIntegral.integral_const, smul_eq_mul]

/-- Every exponentially constructed nonzero undamped spin travels infinite total arclength. -/
theorem spinSphereFlow_zero_damping_infinite_arclength (c : ℂ) :
    Tendsto (fun T => ∫ t in (0 : ℝ)..T,
      ‖spinSphereField 0 (spinSphereFlow 0 (Complex.exp c) t)‖) atTop atTop := by
  have hz : 0 < ‖Complex.exp c‖ := norm_pos_iff.mpr (Complex.exp_ne_zero c)
  have hp : 0 < 2 * ‖Complex.exp c‖ / (1 + ‖Complex.exp c‖ ^ (2 : ℕ)) := by positivity
  have h := Filter.Tendsto.const_mul_atTop hp (Filter.tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  simpa only [spinSphereFlow_zero_damping_integral_speed, sub_zero, id_eq, mul_comm] using h

/-- The south pole is the only convergent finite-chart undamped spin, with its exact limit. -/
theorem spinSphereFlow_zero_damping_tendsto_iff (z : ℂ) (m : EuclideanSpace ℝ (Fin 3)) :
    Tendsto (spinSphereFlow 0 z) atTop (nhds m) ↔ z = 0 ∧ m = _root_.Bottcher.stereo 0 := by
  constructor
  · intro h
    have hperiod := spinSphereFlow_zero_damping_periodic z
    have ht : Tendsto (fun n : ℕ => (n : ℝ) * (2 * Real.pi)) atTop atTop := by
      have hpi : 0 < 2 * Real.pi := by positivity
      simpa only [mul_comm] using Filter.Tendsto.const_mul_atTop hpi
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    have hall : ∀ u : ℝ, spinSphereFlow 0 z u = m := by
      intro u
      have hu := h.comp (Filter.tendsto_atTop_add_const_left atTop u ht)
      have heq : (fun n : ℕ => spinSphereFlow 0 z (u + (n : ℝ) * (2 * Real.pi))) =
          (fun _ : ℕ => spinSphereFlow 0 z u) := by
        funext n
        exact hperiod.nat_mul n u
      simp only [Function.comp_def, heq] at hu
      exact tendsto_nhds_unique tendsto_const_nhds hu
    have hzero := hall 0
    rw [spinSphereFlow_zero] at hzero
    have hpi := hall Real.pi
    simp only [spinSphereFlow, spinPlaneFlow_zero_damping_pi] at hpi
    have hz : z = -z := by
      have hh := congrArg _root_.Bottcher.stereoFiniteChart (hzero.trans hpi.symm)
      simpa only [_root_.Bottcher.stereoFiniteChart_stereo] using hh
    have hz0 : z = 0 := by
      have hr := congrArg Complex.re hz
      have hi := congrArg Complex.im hz
      apply Complex.ext <;> simp only [Complex.zero_re, Complex.zero_im]
      · simp only [Complex.neg_re] at hr
        linarith
      · simp only [Complex.neg_im] at hi
        linarith
    exact ⟨hz0, by simpa only [hz0] using hzero.symm⟩
  · rintro ⟨rfl, rfl⟩
    unfold spinSphereFlow spinPlaneFlow
    simpa only [spinSphereFlow, spinPlaneFlow, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => _root_.Bottcher.stereo 0) atTop
        (nhds (_root_.Bottcher.stereo 0)))

/-- Nonzero undamped spins give closed counterexamples to energy-only convergence claims. -/
theorem spinSphereFlow_zero_damping_no_limit (c : ℂ) (m : EuclideanSpace ℝ (Fin 3)) :
    ¬ Tendsto (spinSphereFlow 0 (Complex.exp c)) atTop (nhds m) := by
  rw [spinSphereFlow_zero_damping_tendsto_iff]
  exact fun h => Complex.exp_ne_zero c h.1

end
end GaloisForLFunctions.HTGeometry.SchafferExl

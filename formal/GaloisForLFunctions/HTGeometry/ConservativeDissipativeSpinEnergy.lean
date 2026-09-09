import GaloisForLFunctions.HTGeometry.ConservativeDissipativeProjectiveSpin
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false

/-!
# Exact spin dissipation and projective relaxation

The Schaffer–Exl torque-square law (arXiv:2609.04530) holds along the actual
global homogeneous spin trajectory. Its energy is antitone and its integrated
torque loss equals the exact endpoint energy drop. Exponentially constructed
positive damping drives every finite chart spin to the south pole, while the
north pole and zero spin remain fixed. The existing chordal metric gives an
explicit exponential distance bound, and Marty conformality gives a global
speed bound. Latitude odds are precisely the exponentially damped chart radius.
-/
open scoped Matrix RealInnerProductSpace
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Squared torque of a spin against the fixed north-directed energy gradient. -/
def spinTorqueEnergy (m : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (m.ofLp ⨯₃ (![0, 0, 1] : Fin 3 → ℝ)) ⬝ᵥ (m.ofLp ⨯₃ (![0, 0, 1] : Fin 3 → ℝ))

theorem spinTorqueEnergy_components (m : EuclideanSpace ℝ (Fin 3)) :
    spinTorqueEnergy m = m 0 ^ 2 + m 1 ^ 2 := by
  simp [spinTorqueEnergy, cross_apply, dotProduct, Fin.sum_univ_three]
  ring

theorem spinTorqueEnergy_nonneg (m : EuclideanSpace ℝ (Fin 3)) : 0 ≤ spinTorqueEnergy m := by
  rw [spinTorqueEnergy_components]
  positivity

/-- Every physical coordinate of the globally defined spin evolution has its exact field derivative. -/
theorem hasDerivAt_projectiveSpinFlow_coord (a : ℝ) (N D : ℂ) (t : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => projectiveSpinFlow a N D s i)
      (spinSphereField a (projectiveSpinFlow a N D t) i) t := by
  have h := (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_projectiveSpinFlow a N D t)
  exact (hasDerivAt_pi.mp h) i

/-- Exact torque-square energy derivative along the actual global Landau–Lifshitz solution. -/
theorem hasDerivAt_projectiveSpinFlow_energy (a : ℝ) (N D : ℂ) (t : ℝ) :
    HasDerivAt (fun s => projectiveSpinFlow a N D s (2 : Fin 3))
      (-a ^ 2 * spinTorqueEnergy (projectiveSpinFlow a N D t)) t := by
  apply (hasDerivAt_projectiveSpinFlow_coord a N D t 2).congr_deriv
  rw [spinSphereField_components, spinTorqueEnergy_components]
  simp

/-- The actual global spin energy is antitone for arbitrary raw damping amplitude. -/
theorem projectiveSpinFlow_energy_antitone (a : ℝ) (N D : ℂ) :
    Antitone (fun t => projectiveSpinFlow a N D t (2 : Fin 3)) := by
  apply antitone_of_hasDerivAt_nonpos (fun t => hasDerivAt_projectiveSpinFlow_energy a N D t)
  intro t
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg a)) (spinTorqueEnergy_nonneg _)

/-- The actual torque loss is continuous, including both homogeneous poles and the zero spin. -/
theorem continuous_projectiveSpinFlow_loss (a : ℝ) (N D : ℂ) :
    Continuous (fun t => a ^ 2 * spinTorqueEnergy (projectiveSpinFlow a N D t)) := by
  have h0 : Continuous (fun t => projectiveSpinFlow a N D t (0 : Fin 3)) :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_projectiveSpinFlow_coord a N D t 0).continuousAt)
  have h1 : Continuous (fun t => projectiveSpinFlow a N D t (1 : Fin 3)) :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_projectiveSpinFlow_coord a N D t 1).continuousAt)
  simp only [spinTorqueEnergy_components]
  exact continuous_const.mul ((h0.pow 2).add (h1.pow 2))

/-- Exact integrated energy loss for the actual spin solution, at arbitrary real endpoints. -/
theorem projectiveSpinFlow_integral_loss (a : ℝ) (N D : ℂ) (s t : ℝ) :
    (∫ v in s..t, a ^ 2 * spinTorqueEnergy (projectiveSpinFlow a N D v)) =
      projectiveSpinFlow a N D s (2 : Fin 3) - projectiveSpinFlow a N D t (2 : Fin 3) := by
  have hc : Continuous (fun v => -a ^ 2 * spinTorqueEnergy (projectiveSpinFlow a N D v)) := by
    convert (continuous_projectiveSpinFlow_loss a N D).neg using 1
    funext v
    simp only [Pi.neg_apply, neg_mul]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v _ => hasDerivAt_projectiveSpinFlow_energy a N D v) (hc.intervalIntegrable s t)
  simp only [neg_mul, intervalIntegral.integral_neg] at h
  linarith

/-- Positive damping is constructed exponentially and drives every finite chart point to zero. -/
theorem spinPlaneFlow_positive_tendsto_zero (s : ℝ) (z : ℂ) :
    Filter.Tendsto (spinPlaneFlow (Real.exp s) z) Filter.atTop (nhds 0) := by
  have ht : Filter.Tendsto (fun t : ℝ => -(Real.exp s) ^ 2 * t) Filter.atTop Filter.atBot :=
    Filter.Tendsto.const_mul_atTop_of_neg (r := -(Real.exp s) ^ 2)
      (neg_neg_of_pos (sq_pos_of_pos (Real.exp_pos s))) Filter.tendsto_id
  have he := (Real.tendsto_exp_atBot.comp ht).mul_const ‖z‖
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [spinPlaneFlow_norm, Function.comp_apply, zero_mul] using he

/-- Quantitative spherical convergence follows from the existing chordal metric estimate. -/
theorem spinSphereFlow_south_distance_bound (a : ℝ) (z : ℂ) (t : ℝ) :
    ‖spinSphereFlow a z t - _root_.Bottcher.stereo 0‖ ≤
      2 * Real.exp (-a ^ 2 * t) * ‖z‖ := by
  rw [spinSphereFlow, _root_.Bottcher.norm_stereo_sub]
  have h := _root_.Bottcher.chordalDist_le_norm (spinPlaneFlow a z t) 0
  rw [sub_zero, spinPlaneFlow_norm] at h
  linarith

/-- Every finite stereographic initial spin converges to the south-pole energy minimum. -/
theorem spinSphereFlow_positive_tendsto (s : ℝ) (z : ℂ) :
    Filter.Tendsto (spinSphereFlow (Real.exp s) z) Filter.atTop (nhds (_root_.Bottcher.stereo 0)) :=
  (_root_.Bottcher.continuous_stereo.tendsto 0).comp (spinPlaneFlow_positive_tendsto_zero s z)

/-- Exact projective long-time classification: finite chart points relax, the north pole stays fixed. -/
theorem projectiveSpinFlow_positive_tendsto (s : ℝ) (N D : ℂ) :
    Filter.Tendsto (projectiveSpinFlow (Real.exp s) N D) Filter.atTop
      (nhds (if D = 0 then (if N = 0 then 0 else (!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)))
        else _root_.Bottcher.stereo 0)) := by
  by_cases hD : D = 0
  · subst D
    have h : projectiveSpinFlow (Real.exp s) N 0 = fun _ =>
        (if N = 0 then 0 else (!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3))) := by
      funext t
      exact projectiveSpinFlow_pole (Real.exp s) N t
    rw [h, if_pos rfl]
    exact tendsto_const_nhds
  · have h : projectiveSpinFlow (Real.exp s) N D = spinSphereFlow (Real.exp s) (N / D) := by
      funext t
      rw [projectiveSpinFlow_chart, if_neg hD]
    rw [h, if_neg hD]
    exact spinSphereFlow_positive_tendsto s (N / D)

/-- The latitude odds are exactly the decaying squared chart radius. -/
theorem spinSphereFlow_energy_odds (a : ℝ) (z : ℂ) (t : ℝ) :
    (1 + spinSphereFlow a z t (2 : Fin 3)) / (1 - spinSphereFlow a z t (2 : Fin 3)) =
      Real.exp (-2 * a ^ 2 * t) * ‖z‖ ^ 2 := by
  rw [spinSphereFlow_energy]
  have h : 1 + Real.exp (-2 * a ^ 2 * t) * ‖z‖ ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The speed of every spin orbit is bounded globally, uniformly over its stereographic initial state. -/
theorem spinSphereFlow_speed_bound (a : ℝ) (z : ℂ) (t : ℝ) :
    ‖spinSphereField a (spinSphereFlow a z t)‖ ≤ ‖spinPlaneRate a‖ := by
  rw [spinSphereFlow_speed, norm_mul]
  apply (div_le_iff₀ (by positivity : 0 < 1 + ‖spinPlaneFlow a z t‖ ^ 2)).mpr
  nlinarith [mul_nonneg (norm_nonneg (spinPlaneRate a)) (sq_nonneg (‖spinPlaneFlow a z t‖ - 1))]

end
end GaloisForLFunctions.HTGeometry.SchafferExl

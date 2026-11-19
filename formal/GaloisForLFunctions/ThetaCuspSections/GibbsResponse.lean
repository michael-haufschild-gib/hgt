import GaloisForLFunctions.RHTower.ThetaSourceGlobalStrictLogConvexity

/-!
# Coupling and temperature response of the completed theta source

The pure-scale identity of Peña, Castorene and Vidal-Silva (arXiv:2611.18873,
equation 46) has an exact analogue for the exponential tilt of the theta
density. Log coupling and log temperature enter through their difference.
Their entropy responses are opposite, with magnitude given by real-axis Xi
susceptibility. The change between two tilts is measured by the gap between
the log partition and its tangent line.
-/

open Set Real RHTower

namespace ThetaCuspSections

noncomputable section

/-- Entropy relative to the theta base density, in units with Boltzmann constant one. -/
def tiltEntropy (a : ℝ) : ℝ := thetaTiltLogPartition a - a * thetaTiltMean a

/-- Log-partition tangent gap from tilt `a` to tilt `b`. -/
def tiltGap (a b : ℝ) : ℝ :=
  thetaTiltLogPartition b - thetaTiltLogPartition a - (b-a) * thetaTiltMean a

private theorem partition_deriv (a : ℝ) :
    HasDerivAt thetaTiltLogPartition (thetaTiltMean a) a :=
  (hasDerivAt_thetaTiltMoment_global a 0).log (thetaTiltMoment_zero_pos_global a).ne'

theorem tiltEntropy_hasDerivAt (a : ℝ) :
    HasDerivAt tiltEntropy (-a * thetaTiltVariance a) a := by
  convert (partition_deriv a).sub ((hasDerivAt_id a).mul (hasDerivAt_thetaTiltMean_global a))
    using 1 <;> first | rfl | (dsimp; ring)

theorem tiltEntropy_even (a : ℝ) : tiltEntropy (-a) = tiltEntropy a := by
  simp [tiltEntropy, thetaTiltLogPartition_neg, thetaTiltMean_neg]

/-- Increasing the magnitude of the real tilt strictly decreases the entropy. -/
theorem tiltEntropy_strictAntiOn : StrictAntiOn tiltEntropy (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
    (fun x _ => (tiltEntropy_hasDerivAt x).continuousAt.continuousWithinAt)
  intro x hx
  rw [interior_Ici] at hx
  rw [(tiltEntropy_hasDerivAt x).deriv]
  exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hx) (thetaTiltVariance_pos_global x)

/-- Entropy readings identify the absolute value of the real displacement. -/
theorem tiltEntropy_eq_iff (a b : ℝ) : tiltEntropy a = tiltEntropy b ↔ |a| = |b| := by
  have habs (x : ℝ) : tiltEntropy |x| = tiltEntropy x := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, tiltEntropy_even]
  rw [← habs a, ← habs b]
  exact ⟨tiltEntropy_strictAntiOn.injOn (abs_nonneg a) (abs_nonneg b), congrArg _⟩

/-- Susceptibility sampled at the scale ratio, multiplied by the square of that ratio. -/
def tiltCapacity (u v : ℝ) : ℝ :=
  Real.exp (u-v) ^ 2 * thetaTiltVariance (Real.exp (u-v))

/-- Entropy at log coupling `u` and log temperature `v`. -/
def scaleEntropy (u v : ℝ) : ℝ := tiltEntropy (Real.exp (u-v))

theorem tiltCapacity_pos (u v : ℝ) : 0 < tiltCapacity u v :=
  mul_pos (sq_pos_of_pos (Real.exp_pos _)) (thetaTiltVariance_pos_global _)

/-- The real-axis logarithmic derivative of Xi determines the calorimetric response. -/
theorem tiltCapacity_eq_xi_susceptibility (u v : ℝ) :
    tiltCapacity u v = Real.exp (u-v)^2 * deriv xiRealLogDeriv (Real.exp (u-v)) := by
  rw [← (funext thetaTiltMean_eq_xiRealLogDeriv), (hasDerivAt_thetaTiltMean_global _).deriv]
  rfl

theorem scaleEntropy_coupling (u v : ℝ) :
    HasDerivAt (fun t => scaleEntropy t v) (-tiltCapacity u v) u := by
  have h := ((tiltEntropy_hasDerivAt _).comp u (((hasDerivAt_id u).sub_const v).exp))
  convert h using 1 <;> first | rfl | (dsimp [tiltCapacity]; ring)

theorem scaleEntropy_temperature (u v : ℝ) :
    HasDerivAt (scaleEntropy u) (tiltCapacity u v) v := by
  have h := ((tiltEntropy_hasDerivAt _).comp v (((hasDerivAt_id v).const_sub u).exp))
  convert h using 1 <;> first | rfl | (dsimp [tiltCapacity]; ring)

/-- Isentropes are exactly straight lines of slope one in log-scale coordinates. -/
theorem scaleEntropy_eq_iff (u v w z : ℝ) :
    scaleEntropy u v = scaleEntropy w z ↔ u-v = w-z := by
  unfold scaleEntropy
  rw [tiltEntropy_eq_iff, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _), Real.exp_injective.eq_iff]

/-- Differentiating in the target reads a difference of real Xi logarithmic derivatives. -/
theorem tiltGap_target_deriv (a b : ℝ) :
    HasDerivAt (tiltGap a) (xiRealLogDeriv b - xiRealLogDeriv a) b := by
  rw [← thetaTiltMean_eq_xiRealLogDeriv b, ← thetaTiltMean_eq_xiRealLogDeriv a]
  have hlin : HasDerivAt (fun t : ℝ => (t-a)*thetaTiltMean a) (thetaTiltMean a) b := by
    simpa only [id_eq, one_mul] using (((hasDerivAt_id b).sub_const a).mul_const (thetaTiltMean a))
  change HasDerivAt (fun t : ℝ => thetaTiltLogPartition t - thetaTiltLogPartition a -
    (t-a)*thetaTiltMean a) _ b
  exact ((partition_deriv b).sub_const (thetaTiltLogPartition a)).sub hlin

/-- Differentiating in the source measures its local variance times the signed distance. -/
theorem tiltGap_source_deriv (a b : ℝ) :
    HasDerivAt (fun t => tiltGap t b) ((a-b) * thetaTiltVariance a) a := by
  convert ((partition_deriv a).const_sub (thetaTiltLogPartition b)).sub
    (((hasDerivAt_id a).const_sub b).mul (hasDerivAt_thetaTiltMean_global a)) using 1 <;>
    first | rfl | (dsimp; ring)

private theorem gap_right (a : ℝ) : StrictMonoOn (tiltGap a) (Ici a) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
    (fun x _ => (tiltGap_target_deriv a x).continuousAt.continuousWithinAt)
  intro x hx
  rw [interior_Ici] at hx
  rw [(tiltGap_target_deriv a x).deriv]
  exact sub_pos.mpr (strictMono_xiRealLogDeriv hx)

private theorem gap_left (a : ℝ) : StrictAntiOn (tiltGap a) (Iic a) := by
  apply strictAntiOn_of_deriv_neg (convex_Iic _)
    (fun x _ => (tiltGap_target_deriv a x).continuousAt.continuousWithinAt)
  intro x hx
  rw [interior_Iic] at hx
  rw [(tiltGap_target_deriv a x).deriv]
  exact sub_neg.mpr (strictMono_xiRealLogDeriv hx)

/-- Equality in the log-partition tangent inequality characterizes identical tilts. -/
theorem tiltGap_pos_iff (a b : ℝ) : 0 < tiltGap a b ↔ a ≠ b := by
  have hz : tiltGap a a = 0 := by simp [tiltGap]
  refine ⟨fun h e => by subst b; exact (lt_irrefl 0) (hz ▸ h), fun h => ?_⟩
  rcases lt_or_gt_of_ne h with h | h
  · exact hz ▸ gap_right a (le_refl a) h.le h
  · exact hz ▸ gap_left a h.le (le_refl a) h

theorem tiltGap_nonneg (a b : ℝ) : 0 ≤ tiltGap a b := by
  rcases eq_or_ne a b with rfl | h
  · simp [tiltGap]
  · exact ((tiltGap_pos_iff a b).2 h).le

/-- Symmetrization removes the partition and leaves a two-point Xi response. -/
theorem tiltGap_symmetrized (a b : ℝ) :
    tiltGap a b + tiltGap b a = (b-a) * (xiRealLogDeriv b - xiRealLogDeriv a) := by
  simp only [tiltGap, thetaTiltMean_eq_xiRealLogDeriv]
  ring

/-- Exact correction to additivity on three successive real tilts. -/
theorem tiltGap_three_point (a b c : ℝ) :
    tiltGap a c - tiltGap a b - tiltGap b c =
      (c-b) * (xiRealLogDeriv b - xiRealLogDeriv a) := by
  simp only [tiltGap, thetaTiltMean_eq_xiRealLogDeriv]
  ring

/-- The correction is positive precisely when the intermediate displacement is
strictly between the endpoints, in either order. -/
theorem tiltGap_superadditive_iff (a b c : ℝ) :
    tiltGap a b + tiltGap b c < tiltGap a c ↔ (a < b ∧ b < c) ∨ (c < b ∧ b < a) := by
  rw [show tiltGap a b + tiltGap b c < tiltGap a c ↔
    0 < tiltGap a c - tiltGap a b - tiltGap b c by constructor <;> intro h <;> linarith,
    tiltGap_three_point, mul_pos_iff]
  simp only [sub_pos, sub_neg, strictMono_xiRealLogDeriv.lt_iff_lt]
  tauto

/-- Entropy lost from the symmetric base is exactly the reverse tangent gap. -/
theorem tiltEntropy_loss (a : ℝ) : tiltEntropy 0 - tiltEntropy a = tiltGap a 0 := by
  simp only [tiltEntropy, tiltGap, zero_mul, sub_zero, zero_sub]
  ring

#print axioms scaleEntropy_coupling
#print axioms scaleEntropy_temperature
#print axioms scaleEntropy_eq_iff
#print axioms tiltCapacity_eq_xi_susceptibility
#print axioms tiltGap_pos_iff
#print axioms tiltGap_superadditive_iff
#print axioms tiltGap_source_deriv
#print axioms tiltEntropy_loss

end

end ThetaCuspSections

import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceTimeField

/-!
# PW-B literal source vanishing at physical event faces

The original reduced time source vanishes at the radial wall. On the
negative-radius half-line its onset also annihilates every nonpositive
first-event time. These are the two source facts needed to extend the
physical test across the hard event-set cuts in the ordered null chart.
-/

namespace RHTower.D4BMJointSource

noncomputable section
set_option autoImplicit false

/-- Every retained term of the actual reduced source has a radial factor. -/
theorem timeReducedCoefficient_zero_at_radial_wall (s a : ℂ) (τ : ℝ) :
    timeReducedCoefficient s a τ 0 = 0 := by
  have hu : radialUnit 0 = 0 := by simp [radialUnit]
  simp [timeReducedCoefficient, reducedCoefficient, reducedPolynomial,
    radialLiftFirst, liftFirstPolynomial, liftSecondPolynomial, hu]

/-- The fixed smooth onset removes the original first-event time cut while
the event remains on the physical negative-radius half-line. -/
theorem timeReducedCoefficient_zero_at_nonpositive_time_negative_radius
    (s a : ℂ) (τ t : ℝ) (hτ : τ ≤ 0) (ht : t < 0) :
    timeReducedCoefficient s a τ t = 0 :=
  timeReducedCoefficient_zero_before_onset s a τ t (by linarith)

end
end RHTower.D4BMJointSource

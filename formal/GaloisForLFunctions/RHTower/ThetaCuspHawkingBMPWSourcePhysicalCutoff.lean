import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPWSourceBoundaryNullAdmission
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceVectorDecay

/-!
# Continuous physical-event extension of the literal reduced source

The source itself kills both hard event-set cuts. This permits the original
ordered CTP test to enter continuous mixed-test Goursat transposition in the
direct and reflected-image charts without a discontinuous indicator.
-/

open Set

namespace RHTower.D4BMJointSource

noncomputable section
set_option autoImplicit false

def physicalSourceCutoff (s a : ℂ) : ℝ × ℝ → ℂ :=
  fun p => if p.2 < 0 then timeReducedCoefficient s a p.1 p.2 else 0

theorem physicalSourceCutoff_continuous (s a : ℂ) :
    Continuous (physicalSourceCutoff s a) := by
  classical
  apply Continuous.if
    (p := fun p : ℝ × ℝ => p.2 < 0)
    (fun p hp => ?_)
    (timeReducedCoefficient_joint_continuous s a) continuous_const
  have hfront := (continuous_snd : Continuous (fun p : ℝ × ℝ => p.2)).frontier_preimage_subset
    (Iio (0 : ℝ)) hp
  have hp0 : p.2 = 0 := by
    simpa only [mem_preimage, frontier_Iio, mem_singleton_iff] using hfront
  simp [hp0, timeReducedCoefficient_zero_at_radial_wall]

/-- The zero extension equals the exact original positive-time/negative-radius
event indicator, rather than modifying the source. -/
theorem physicalSourceCutoff_eq_event_indicator (s a : ℂ) :
    physicalSourceCutoff s a =
      (Ioi (0 : ℝ) ×ˢ Iio (0 : ℝ)).indicator
        (fun p : ℝ × ℝ => timeReducedCoefficient s a p.1 p.2) := by
  funext p
  by_cases hx : p.2 < 0
  · by_cases ht : 0 < p.1
    · simp [physicalSourceCutoff, hx, ht, Set.indicator]
    · have hz := timeReducedCoefficient_zero_at_nonpositive_time_negative_radius
        s a p.1 p.2 (le_of_not_gt ht) hx
      simp [physicalSourceCutoff, hx, ht, hz, Set.indicator]
  · simp [physicalSourceCutoff, hx, Set.indicator]

end
end RHTower.D4BMJointSource

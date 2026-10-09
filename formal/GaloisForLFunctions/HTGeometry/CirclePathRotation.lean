import GaloisForLFunctions.HTGeometry.CornerCirclePath
import Mathlib.Algebra.Field.Periodic
import Mathlib.Topology.Homotopy.Path

open Set
open scoped unitInterval
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- One closed positive-circle path contains every real-angle value of its circle map. -/
theorem exists_positiveCircle_parameter (c : ℂ) (r θ : ℝ) :
    ∃ t : I, positiveCirclePath c r t = circleMap c r θ := by
  obtain ⟨θ', hθ', he⟩ := (periodic_circleMap c r).exists_mem_Ico₀ Real.two_pi_pos θ
  let t : I := ⟨θ' / (2 * Real.pi), div_nonneg hθ'.1 Real.two_pi_pos.le,
    (div_le_one Real.two_pi_pos).mpr hθ'.2.le⟩
  refine ⟨t, ?_⟩
  change circleMap c r (2 * Real.pi * (θ' / (2 * Real.pi))) = circleMap c r θ
  have hangle : 2 * Real.pi * (θ' / (2 * Real.pi)) = θ' := by
    field_simp [Real.two_pi_pos.ne']
  rw [hangle]
  exact he.symm

/-- The aligned circle translated to an arbitrary center. -/
def translatedCornerCirclePath (c : ℂ) (r : ℝ) :
    Path (c + circleMap 0 r (-3 * Real.pi / 4)) (c + circleMap 0 r (-3 * Real.pi / 4)) :=
  (cornerCirclePath r).map ((continuous_const : Continuous (fun _ : ℂ => c)).add continuous_id)

/-- Rotate the basepoint continuously while retaining the positive orientation of each loop. -/
def positiveCircleRotation (c : ℂ) (r : ℝ) :
    (positiveCirclePath c r).toContinuousMap.Homotopy
      (translatedCornerCirclePath c r).toContinuousMap where
  toFun x := circleMap c r (2 * Real.pi * (x.2 : ℝ) + (-3 * Real.pi / 4) * (x.1 : ℝ))
  continuous_toFun := by unfold circleMap; fun_prop
  map_zero_left := by
    intro t
    change circleMap c r (2 * Real.pi * (t : ℝ) + (-3 * Real.pi / 4) * (0 : ℝ)) =
      circleMap c r (2 * Real.pi * (t : ℝ))
    rw [mul_zero, add_zero]
  map_one_left := by
    intro t
    change circleMap c r (2 * Real.pi * (t : ℝ) + (-3 * Real.pi / 4) * (1 : ℝ)) =
      c + circleMap 0 r (-3 * Real.pi / 4 + 2 * Real.pi * (t : ℝ))
    rw [mul_one, add_comm (2 * Real.pi * (t : ℝ))]
    simp only [circleMap, zero_add]

/-- Every intermediate path is closed; its common endpoint is the moving basepoint. -/
theorem positiveCircleRotation_closed (c : ℂ) (r : ℝ) (s : I) :
    positiveCircleRotation c r (s, 0) = positiveCircleRotation c r (s, 1) := by
  change circleMap c r (2 * Real.pi * (0 : ℝ) + (-3 * Real.pi / 4) * (s : ℝ)) =
    circleMap c r (2 * Real.pi * (1 : ℝ) + (-3 * Real.pi / 4) * (s : ℝ))
  simpa only [mul_zero, zero_add, mul_one, add_comm] using
    ((periodic_circleMap c r) ((-3 * Real.pi / 4) * (s : ℝ))).symm

/-- Rotating the basepoint preserves avoidance of every set avoided by the original circle. -/
theorem positiveCircleRotation_avoids (c : ℂ) (r : ℝ) {S : Set ℂ}
    (havoid : ∀ t : I, positiveCirclePath c r t ∉ S) (s t : I) :
    positiveCircleRotation c r (s, t) ∉ S := by
  obtain ⟨u, hu⟩ := exists_positiveCircle_parameter c r
    (2 * Real.pi * (t : ℝ) + (-3 * Real.pi / 4) * (s : ℝ))
  change circleMap c r (2 * Real.pi * (t : ℝ) + (-3 * Real.pi / 4) * (s : ℝ)) ∉ S
  rw [← hu]
  exact havoid u

end
end GaloisForLFunctions.HTGeometry

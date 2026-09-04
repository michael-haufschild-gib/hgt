import GaloisForLFunctions.HTGeometry.SpinTorsionChannel
import GaloisForLFunctions.RHTower.SuperPoincareQ8OddClifford

/-!
# Quaternionic realization of the three-plane spin-torsion channel

The odd central sector of the existing Q8 representation supplies three anticommuting complex
structures.  Their three squares give the three negative internal plane contributions in the
spin-torsion channel, so the scalar-plus-three-plane trace is exactly `-2`.
-/

noncomputable section

namespace RHTower

/-- Third quaternionic complex structure on the odd central sector. -/
def q8KOnOdd : Module.End ℚ q8OddSubmodule := q8IOnOdd * q8JOnOdd

/-- Reverse anticommutation relation on the odd sector. -/
theorem q8JOnOdd_mul_q8IOnOdd_eq_neg :
    q8JOnOdd * q8IOnOdd = -(q8IOnOdd * q8JOnOdd) := by
  rw [q8IOnOdd_mul_q8JOnOdd_eq_neg]
  abel

/-- The third quaternionic generator also squares to `-1`. -/
theorem q8KOnOdd_sq : q8KOnOdd * q8KOnOdd = -1 := by
  unfold q8KOnOdd
  calc
    (q8IOnOdd * q8JOnOdd) * (q8IOnOdd * q8JOnOdd) =
        q8IOnOdd * (q8JOnOdd * q8IOnOdd) * q8JOnOdd := by
      simp only [mul_assoc]
    _ = q8IOnOdd * (-(q8IOnOdd * q8JOnOdd)) * q8JOnOdd := by
      rw [q8JOnOdd_mul_q8IOnOdd_eq_neg]
    _ = -((q8IOnOdd * q8IOnOdd) * (q8JOnOdd * q8JOnOdd)) := by
      apply LinearMap.ext
      intro z
      simp [Module.End.mul_apply]
    _ = -1 := by rw [q8IOnOdd_sq, q8JOnOdd_sq]; norm_num

/-- Q8 realization of the paper's scalar-plus-three-Cartan-plane channel factor. -/
theorem q8_threePlane_spinTorsionChannel :
    (1 : Module.End ℚ q8OddSubmodule) +
        q8IOnOdd * q8IOnOdd + q8JOnOdd * q8JOnOdd + q8KOnOdd * q8KOnOdd =
      -(2 : ℚ) • (1 : Module.End ℚ q8OddSubmodule) := by
  rw [q8IOnOdd_sq, q8JOnOdd_sq, q8KOnOdd_sq]
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change x.1 + -x.1 + -x.1 + -x.1 = (-2 : ℚ) • x.1
  norm_num [Algebra.smul_def]
  ring

/-- The concrete Q8 trace agrees with the abstract three-plane channel factor. -/
theorem q8_threePlane_channel_matches_abstract :
    ((1 : Module.End ℚ q8OddSubmodule) +
          q8IOnOdd * q8IOnOdd + q8JOnOdd * q8JOnOdd + q8KOnOdd * q8KOnOdd =
        -(2 : ℚ) • (1 : Module.End ℚ q8OddSubmodule)) ∧
      GaloisForLFunctions.HTGeometry.spinTorsionChannelTrace (1 : ℂ) 3 = -2 := by
  exact ⟨q8_threePlane_spinTorsionChannel,
    by simpa using GaloisForLFunctions.HTGeometry.spinTorsion_threePlaneChannelTrace (1 : ℂ)⟩

end RHTower

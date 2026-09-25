import GaloisForLFunctions.RHTower.FrankensteinSourceTailSoninPhaseWork

/-!
# Hidden grade duality of complete-source/Sonin phase work

The source work factors through a rational profile in the squared horizontal
grade.  That profile is invariant under a nontrivial involution, so the scalar
work alone forgets which side of its maximum generated it.  This is a
pre-divisor algebraic fact; it asserts no additional Xi zero location.
-/

namespace RHTower

noncomputable section

/-- Rational shape of the complete-source/Sonin work in squared grade. -/
def stcWorkShape (s : ℝ) : ℝ := s * (1 - s) / (1 + s) ^ (2 : ℕ)

/-- The second squared grade with the same positive work. -/
def stcWorkDual (s : ℝ) : ℝ := (1 - s) / (1 + 3 * s)

/-- The grade transform is an involution on the nonnegative source range. -/
theorem stcWorkDual_involutive (s : ℝ) (hs : 0 ≤ s) :
    stcWorkDual (stcWorkDual s) = s := by
  have hd : 1 + 3 * s ≠ 0 := by linarith
  simp only [stcWorkDual]
  field_simp [hd]
  ring

/-- The source-work profile is invariant under the grade transform. -/
theorem stcWorkShape_dual (s : ℝ) (hs : 0 ≤ s) :
    stcWorkShape (stcWorkDual s) = stcWorkShape s := by
  have hd : 1 + 3 * s ≠ 0 := by linarith
  have h1s : 1 + s ≠ 0 := by linarith
  have hminus : 1 - stcWorkDual s = 4 * s / (1 + 3 * s) := by
    simp only [stcWorkDual]
    field_simp [hd]
    ring
  have hplus : 1 + stcWorkDual s = 2 * (1 + s) / (1 + 3 * s) := by
    simp only [stcWorkDual]
    field_simp [hd]
    ring
  simp only [stcWorkShape]
  rw [hminus, hplus]
  simp only [stcWorkDual]
  field_simp [hd, h1s]
  ring

/-- The actual complete-source/Sonin work factors through this grade profile. -/
theorem sourceTailSoninPhaseWork_eq_shape (q : XiZeroCopy) :
    sourceTailSoninPhaseWork q =
      ((Real.log 2 ^ (2 : ℕ) / 4 *
        stcWorkShape (primeDepthBVWoldXiCenteredRate q.1 ^ (2 : ℕ)) : ℝ) : ℂ) := by
  rw [sourceTailSoninPhaseWork_closedForm]
  simp only [stcWorkShape]
  push_cast
  ring

end
end RHTower

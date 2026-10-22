import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiClockVolterraBridge

namespace RHTower

noncomputable section

/-- Six powers of log height remove every inverse power in the literal connected
Suzuki third-grade test.  The continuum clock mixture becomes two exponential
endpoint clocks and one unshifted linear jet. -/
theorem ccmSuzukiConnectedThirdGradeWeight_sixthJet
    (ω h : ℝ) :
    h ^ (6 : ℕ) * ccmSuzukiConnectedThirdGradeWeight ω h =
      96 / ω ^ (3 : ℕ) *
        (Real.exp (ω * h) - Real.exp (-(ω * h)) - 2 * ω * h) := by
  by_cases hω : ω = 0
  · subst ω
    simp [ccmSuzukiConnectedThirdGradeWeight,
      ccmGuinandWeilThirdGradeWeight,
      shiftedEulerLogConnectedThirdMultiplier]
  by_cases hh : h = 0
  · subst h
    simp [ccmSuzukiConnectedThirdGradeWeight,
      ccmGuinandWeilThirdGradeWeight]
  rw [ccmSuzukiConnectedThirdGradeWeight,
    ccmGuinandWeilThirdGradeWeight,
    shiftedEulerLogConnectedThirdMultiplier,
    Real.sinh_eq]
  have hωh : ω * h ≠ 0 := mul_ne_zero hω hh
  field_simp [hω, hh, hωh]
  ring

/-- The sixth-jet endpoint reduction holds on the same prime atoms and polar
interval, before either channel is scalarized. -/
theorem ccmSuzukiConnectedThirdGradeWindow_sixthJet
    (b H ω : ℝ) :
    ccmGuinandWeilPrimePolarWeightedWindow b H
      (fun h => h ^ (6 : ℕ) * ccmSuzukiConnectedThirdGradeWeight ω h) =
    ccmGuinandWeilPrimePolarWeightedWindow b H
      (fun h => 96 / ω ^ (3 : ℕ) *
        (Real.exp (ω * h) - Real.exp (-(ω * h)) - 2 * ω * h)) := by
  congr 1
  funext h
  exact ccmSuzukiConnectedThirdGradeWeight_sixthJet ω h

end

end RHTower

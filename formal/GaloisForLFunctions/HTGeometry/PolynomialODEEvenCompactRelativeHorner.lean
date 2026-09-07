import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactRelativeDeterminant
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactHorner0

namespace HTGeometry
noncomputable section

/-- The checked finite Horner recurrence is exactly the coupled-gap substitution. -/
theorem evenCompactRelativeDet_gap_eq_horner (r t v : ℝ) :
    evenCompactRelativeDet r (evenCompactUnitGap r t) v =
      evenCompactHorner0 r t v := by
  simp only [evenCompactRelativeDet, evenCompactHorner0_step,
    evenCompactHorner1_step,
    evenCompactHorner2_step,
    evenCompactHorner3_step,
    evenCompactHorner4_step,
    evenCompactHorner5_step,
    evenCompactHorner6_step,
    evenCompactHorner7_step,
    evenCompactHorner8_step,
    evenCompactHorner9_step,
    evenCompactHorner10_step,
    evenCompactHorner11_step,
    evenCompactHorner12_step,
    evenCompactHorner13_step,
    evenCompactHorner14_step,
    evenCompactHorner15_step,
    evenCompactHorner16_step,
    evenCompactHorner17_step,
    evenCompactHorner18_step,
    evenCompactHorner19_step,
    evenCompactHorner20_step, evenCompactHorner21]

end
end HTGeometry

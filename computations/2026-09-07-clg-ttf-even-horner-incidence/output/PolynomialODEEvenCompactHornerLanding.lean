import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactHorner0
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactUnitReserve
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBlockGrades0
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBlockGrades1
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBlockGrades2
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBlockGrades3
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBlockGrades4
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBlockGrades5
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBlockGrades6
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBlockGrades7
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBlockGrades8
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBlockGrades9
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBlockGrades10
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBlockGrades11

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

/-- Exact landing of drift-degree 0 in the positive polynomial certificate. -/
theorem evenCompactHornerLandingCoeff0 (t v : ℝ) :
    evenCompactHorner0Coeff0 t v = evenCompactUnitBlock0DriftCoeff0 t v := by
  first
  | rfl
  | unfold evenCompactHorner0Coeff0 evenCompactUnitBlock0DriftCoeff0
    ring1

/-- Exact landing of drift-degree 1 in the positive polynomial certificate. -/
theorem evenCompactHornerLandingCoeff1 (t v : ℝ) :
    evenCompactHorner0Coeff1 t v = evenCompactUnitBlock0DriftCoeff1 t v := by
  first
  | rfl
  | unfold evenCompactHorner0Coeff1 evenCompactUnitBlock0DriftCoeff1
    ring1

/-- Exact landing of drift-degree 2 in the positive polynomial certificate. -/
theorem evenCompactHornerLandingCoeff2 (t v : ℝ) :
    evenCompactHorner0Coeff2 t v = evenCompactUnitBlock0DriftCoeff2 t v := by
  first
  | rfl
  | unfold evenCompactHorner0Coeff2 evenCompactUnitBlock0DriftCoeff2
    ring1

/-- Exact landing of drift-degree 3 in the positive polynomial certificate. -/
theorem evenCompactHornerLandingCoeff3 (t v : ℝ) :
    evenCompactHorner0Coeff3 t v = evenCompactUnitBlock0DriftCoeff3 t v := by
  first
  | rfl
  | unfold evenCompactHorner0Coeff3 evenCompactUnitBlock0DriftCoeff3
    ring1

/-- Exact landing of drift-degree 4 in the positive polynomial certificate. -/
theorem evenCompactHornerLandingCoeff4 (t v : ℝ) :
    evenCompactHorner0Coeff4 t v = (evenCompactUnitBlock0DriftCoeff4 t v +
    evenCompactUnitBlock1DriftCoeff4 t v : ℝ) := by
  first
  | rfl
  | unfold evenCompactHorner0Coeff4 evenCompactUnitBlock0DriftCoeff4 evenCompactUnitBlock1DriftCoeff4
    ring1

/-- Exact landing of drift-degree 5 in the positive polynomial certificate. -/
theorem evenCompactHornerLandingCoeff5 (t v : ℝ) :
    evenCompactHorner0Coeff5 t v = evenCompactUnitBlock1DriftCoeff5 t v := by
  first
  | rfl
  | unfold evenCompactHorner0Coeff5 evenCompactUnitBlock1DriftCoeff5
    ring1

/-- Exact landing of drift-degree 6 in the positive polynomial certificate. -/
theorem evenCompactHornerLandingCoeff6 (t v : ℝ) :
    evenCompactHorner0Coeff6 t v = (evenCompactUnitBlock1DriftCoeff6 t v +
    evenCompactUnitBlock2DriftCoeff6 t v : ℝ) := by
  first
  | rfl
  | unfold evenCompactHorner0Coeff6 evenCompactUnitBlock1DriftCoeff6 evenCompactUnitBlock2DriftCoeff6
    ring1

/-- Exact landing of drift-degree 7 in the positive polynomial certificate. -/
theorem evenCompactHornerLandingCoeff7 (t v : ℝ) :
    evenCompactHorner0Coeff7 t v = evenCompactUnitBlock2DriftCoeff7 t v := by
  first
  | rfl
  | unfold evenCompactHorner0Coeff7 evenCompactUnitBlock2DriftCoeff7
    ring1

/-- Exact landing of drift-degree 8 in the positive polynomial certificate. -/
theorem evenCompactHornerLandingCoeff8 (t v : ℝ) :
    evenCompactHorner0Coeff8 t v = (evenCompactUnitBlock2DriftCoeff8 t v +
    evenCompactUnitBlock3DriftCoeff8 t v : ℝ) := by
  first
  | rfl
  | unfold evenCompactHorner0Coeff8 evenCompactUnitBlock2DriftCoeff8 evenCompactUnitBlock3DriftCoeff8
    ring1

/-- Exact landing of drift-degree 9 in the positive polynomial certificate. -/
theorem evenCompactHornerLandingCoeff9 (t v : ℝ) :
    evenCompactHorner0Coeff9 t v = evenCompactUnitBlock3DriftCoeff9 t v := by
  first
  | rfl
  | unfold evenCompactHorner0Coeff9 evenCompactUnitBlock3DriftCoeff9
    ring1

/-- Exact landing of drift-degree 10 in the positive polynomial certificate. -/
theorem evenCompactHornerLandingCoeff10 (t v : ℝ) :
    evenCompactHorner0Coeff10 t v = (evenCompactUnitBlock3DriftCoeff10 t v +
    evenCompactUnitBlock4DriftCoeff10 t v : ℝ) := by
  first
  | rfl
  | unfold evenCompactHorner0Coeff10 evenCompactUnitBlock3DriftCoeff10 evenCompactUnitBlock4DriftCoeff10
    ring1

/-- Exact landing of drift-degree 11 in the positive polynomial certificate. -/
theorem evenCompactHornerLandingCoeff11 (t v : ℝ) :
    evenCompactHorner0Coeff11 t v = (evenCompactUnitBlock4DriftCoeff11 t v +
    evenCompactUnitBlock5DriftCoeff11 t v : ℝ) := by
  first
  | rfl
  | unfold evenCompactHorner0Coeff11 evenCompactUnitBlock4DriftCoeff11 evenCompactUnitBlock5DriftCoeff11
    ring1

/-- Exact landing of drift-degree 12 in the positive polynomial certificate. -/
theorem evenCompactHornerLandingCoeff12 (t v : ℝ) :
    evenCompactHorner0Coeff12 t v = (evenCompactUnitBlock5DriftCoeff12 t v +
    evenCompactUnitBlock6DriftCoeff12 t v : ℝ) := by
  first
  | rfl
  | unfold evenCompactHorner0Coeff12 evenCompactUnitBlock5DriftCoeff12 evenCompactUnitBlock6DriftCoeff12
    ring1

/-- Exact landing of drift-degree 13 in the positive polynomial certificate. -/
theorem evenCompactHornerLandingCoeff13 (t v : ℝ) :
    evenCompactHorner0Coeff13 t v = evenCompactUnitBlock6DriftCoeff13 t v := by
  first
  | rfl
  | unfold evenCompactHorner0Coeff13 evenCompactUnitBlock6DriftCoeff13
    ring1

/-- Exact landing of drift-degree 14 in the positive polynomial certificate. -/
theorem evenCompactHornerLandingCoeff14 (t v : ℝ) :
    evenCompactHorner0Coeff14 t v = (evenCompactUnitBlock6DriftCoeff14 t v +
    evenCompactUnitBlock7DriftCoeff14 t v : ℝ) := by
  first
  | rfl
  | unfold evenCompactHorner0Coeff14 evenCompactUnitBlock6DriftCoeff14 evenCompactUnitBlock7DriftCoeff14
    ring1

/-- Exact landing of drift-degree 15 in the positive polynomial certificate. -/
theorem evenCompactHornerLandingCoeff15 (t v : ℝ) :
    evenCompactHorner0Coeff15 t v = (evenCompactUnitBlock7DriftCoeff15 t v +
    evenCompactUnitBlock8DriftCoeff15 t v : ℝ) := by
  first
  | rfl
  | unfold evenCompactHorner0Coeff15 evenCompactUnitBlock7DriftCoeff15 evenCompactUnitBlock8DriftCoeff15
    ring1

/-- Exact landing of drift-degree 16 in the positive polynomial certificate. -/
theorem evenCompactHornerLandingCoeff16 (t v : ℝ) :
    evenCompactHorner0Coeff16 t v = (evenCompactUnitBlock8DriftCoeff16 t v +
    evenCompactUnitBlock9DriftCoeff16 t v : ℝ) := by
  first
  | rfl
  | unfold evenCompactHorner0Coeff16 evenCompactUnitBlock8DriftCoeff16 evenCompactUnitBlock9DriftCoeff16
    ring1

/-- Exact landing of drift-degree 17 in the positive polynomial certificate. -/
theorem evenCompactHornerLandingCoeff17 (t v : ℝ) :
    evenCompactHorner0Coeff17 t v = evenCompactUnitBlock9DriftCoeff17 t v := by
  first
  | rfl
  | unfold evenCompactHorner0Coeff17 evenCompactUnitBlock9DriftCoeff17
    ring1

/-- Exact landing of drift-degree 18 in the positive polynomial certificate. -/
theorem evenCompactHornerLandingCoeff18 (t v : ℝ) :
    evenCompactHorner0Coeff18 t v = (evenCompactUnitBlock9DriftCoeff18 t v +
    evenCompactUnitBlock10DriftCoeff18 t v : ℝ) := by
  first
  | rfl
  | unfold evenCompactHorner0Coeff18 evenCompactUnitBlock9DriftCoeff18 evenCompactUnitBlock10DriftCoeff18
    ring1

/-- Exact landing of drift-degree 19 in the positive polynomial certificate. -/
theorem evenCompactHornerLandingCoeff19 (t v : ℝ) :
    evenCompactHorner0Coeff19 t v = (evenCompactUnitBlock10DriftCoeff19 t v +
    evenCompactUnitBlock11DriftCoeff19 t v : ℝ) := by
  first
  | rfl
  | unfold evenCompactHorner0Coeff19 evenCompactUnitBlock10DriftCoeff19 evenCompactUnitBlock11DriftCoeff19
    ring1

/-- Exact landing of drift-degree 20 in the positive polynomial certificate. -/
theorem evenCompactHornerLandingCoeff20 (t v : ℝ) :
    evenCompactHorner0Coeff20 t v = evenCompactUnitBlock11DriftCoeff20 t v := by
  first
  | rfl
  | unfold evenCompactHorner0Coeff20 evenCompactUnitBlock11DriftCoeff20
    ring1

/-- All drift coefficients land exactly in the independently proved positive polynomial. -/
theorem evenCompactHorner0_eq_unitPolynomial (r t v : ℝ) :
    evenCompactHorner0 r t v = evenCompactUnitPolynomial r t v := by
  unfold evenCompactHorner0
  rw [evenCompactHornerLandingCoeff0, evenCompactHornerLandingCoeff1, evenCompactHornerLandingCoeff2, evenCompactHornerLandingCoeff3, evenCompactHornerLandingCoeff4, evenCompactHornerLandingCoeff5, evenCompactHornerLandingCoeff6, evenCompactHornerLandingCoeff7, evenCompactHornerLandingCoeff8, evenCompactHornerLandingCoeff9, evenCompactHornerLandingCoeff10, evenCompactHornerLandingCoeff11, evenCompactHornerLandingCoeff12, evenCompactHornerLandingCoeff13, evenCompactHornerLandingCoeff14, evenCompactHornerLandingCoeff15, evenCompactHornerLandingCoeff16, evenCompactHornerLandingCoeff17, evenCompactHornerLandingCoeff18, evenCompactHornerLandingCoeff19, evenCompactHornerLandingCoeff20]
  unfold evenCompactUnitPolynomial
  rw [evenCompactUnitBlock0_drift_eq, evenCompactUnitBlock1_drift_eq, evenCompactUnitBlock2_drift_eq, evenCompactUnitBlock3_drift_eq, evenCompactUnitBlock4_drift_eq, evenCompactUnitBlock5_drift_eq, evenCompactUnitBlock6_drift_eq, evenCompactUnitBlock7_drift_eq, evenCompactUnitBlock8_drift_eq, evenCompactUnitBlock9_drift_eq, evenCompactUnitBlock10_drift_eq, evenCompactUnitBlock11_drift_eq]
  ring1

end
end HTGeometry

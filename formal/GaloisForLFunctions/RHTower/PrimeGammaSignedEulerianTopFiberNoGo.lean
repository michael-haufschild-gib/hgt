import GaloisForLFunctions.RHTower.PrimeGammaSignedEulerianCurvaturePluckerLift

/-!
# Top-fibre collapse no-go for the signed-Eulerian SP-E carrier

The type-B Eulerian top statistic identifies the first two distinct four-label histories
needed by SP-E.  This file closes the resulting closure class: any adjacent-edge kernel that
factors through that statistic has zero four-label curvature, hence its canonical Plücker
pencil is identically singular.  A viable growing-rank signed-Eulerian source must retain
descent-bottom incidence.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Factoring an adjacent-edge kernel through type-B top signatures erases the four-label
curvature of the first signed-Eulerian SP-E collision. -/
theorem signedEulerianFourLabelCurvature_eq_zero_of_descentEdgeWeight_factorsThrough
    (κ : ℕ → ℕ → ℝ)
    (hκ : FactorsThroughTypeBTopSignature (signedWordDescentEdgeWeight κ)) :
    signedEulerianFourLabelCurvature κ = 0 := by
  rw [signedEulerianFourLabelCurvature_eq_curvatureMinor]
  have hcross := crossRelation_of_descentEdgeWeight_factorsThrough κ hκ
  dsimp [curvatureMinor]
  linarith

/-- Therefore the canonical four-label signed-Eulerian Plücker pencil is singular for every
pair of spectral variables. -/
theorem det_signedEulerian_curvaturePencil_eq_zero_of_descentEdgeWeight_factorsThrough
    (κ : ℕ → ℕ → ℝ)
    (hκ : FactorsThroughTypeBTopSignature (signedWordDescentEdgeWeight κ))
    (z w : ℂ) :
    (curvaturePluckerPencil (κ 3 1) (κ 3 2) (κ 4 1) (κ 4 2) z w).det = 0 := by
  rw [det_signedEulerian_curvaturePencil,
    signedEulerianFourLabelCurvature_eq_zero_of_descentEdgeWeight_factorsThrough κ hκ]
  norm_num

end GaloisForLFunctions.HTGeometry

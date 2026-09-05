import GaloisForLFunctions.HTGeometry.PointedFisherConnectionInertia
import GaloisForLFunctions.HTGeometry.ComplexHermitianRealification
import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry

/-!
# Pointed Fisher connection: greedy-bump positivity no-go

Despite its name and positive Hilbert--Schmidt energy, the pointed Fisher connection has mixed
signature on an independent state--tangent pair.  Faithful doubled-real transport preserves that
obstruction, so it cannot be used as a positive template metric in arXiv:2609.03581.  This is a
closed negative control against applying the local-bias package to an indefinite connection.
-/

open Matrix
open scoped ComplexOrder Matrix InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Independent pointed state and tangent, with independence carried as data. -/
structure GreedyBumpIndependentFisherPair
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  state : E
  tangent : E
  independent : LinearIndependent ℂ ![state, tangent]

/-- Doubled-real compression of the pointed Fisher connection. -/
def GreedyBumpIndependentFisherPair.realifiedCompression
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (data : GreedyBumpIndependentFisherPair E) : Matrix (Fin 4) (Fin 4) ℝ :=
  (complexMatrixRealification
    (pointedFisherConnectionCompression data.state data.tangent)).submatrix
      (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin (2 + 2)).symm
      (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin (2 + 2)).symm

/-- Realification cannot turn the mixed-signature Fisher connection into a positive metric. -/
theorem GreedyBumpIndependentFisherPair.realifiedCompression_not_posDef
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (data : GreedyBumpIndependentFisherPair E) :
    ¬ data.realifiedCompression.PosDef := by
  have hmixed := pointedFisherConnectionCompression_exact_mixed_signature data.independent
  have hraw : ¬ (complexMatrixRealification
      (pointedFisherConnectionCompression data.state data.tangent)).PosDef :=
    complexMatrixRealification_not_posDef_of_not_posSemidef hmixed.1 hmixed.2.2.1
  intro hfin
  apply hraw
  have hback := hfin.submatrix
    (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin (2 + 2)).injective
  simpa [GreedyBumpIndependentFisherPair.realifiedCompression,
    Matrix.submatrix_submatrix] using hback

/-- No positive-template bundle can have the Fisher compression as its matrix. -/
theorem GreedyBumpIndependentFisherPair.no_positiveTemplateMetric
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (data : GreedyBumpIndependentFisherPair E) :
    ¬ ∃ G : PositiveTemplateMetric 4, G.matrix = data.realifiedCompression := by
  rintro ⟨G, hG⟩
  apply data.realifiedCompression_not_posDef
  rw [← hG]
  exact G.posDef

end

end GaloisForLFunctions.HTGeometry

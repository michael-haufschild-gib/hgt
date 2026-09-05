import GaloisForLFunctions.HTGeometry.EvaluationMinorGeneralDomain
import GaloisForLFunctions.HTGeometry.ComplexHermitianRealification
import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry

/-!
# Greedy-bump synthesis from independent function dictionaries

Every finite linearly independent complex function family admits distinct sample points with a
strict evaluation Gram.  Choosing such a packet and doubled-realifying it constructs a template
metric for arXiv:2609.03581.  Thus abstract function independence is enough to synthesize a finite
search design with closed optimizer, bias, trials, and localization laws.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped ComplexOrder

noncomputable section

/-- Certified finite independent complex function dictionary on an arbitrary domain. -/
structure GreedyBumpEvaluationFamilyData (alpha : Type*) (N : ℕ) where
  feature : Fin N → alpha → ℂ
  independent : LinearIndependent ℂ feature

/-- Existence certificate for a strict finite evaluation packet. -/
theorem GreedyBumpEvaluationFamilyData.exists_strictPacket {alpha : Type*} {N : ℕ}
    (data : GreedyBumpEvaluationFamilyData alpha N) :
    ∃ points : Fin N → alpha, Function.Injective points ∧
      (finiteEvaluationGram data.feature points).PosDef :=
  exists_injective_finiteEvaluationGram_posDef_of_linearIndependent
    data.feature data.independent

/-- Canonically chosen unisolvent sample packet. -/
def GreedyBumpEvaluationFamilyData.points {alpha : Type*} {N : ℕ}
    (data : GreedyBumpEvaluationFamilyData alpha N) : Fin N → alpha :=
  Classical.choose data.exists_strictPacket

/-- Chosen sample packet has no collisions. -/
theorem GreedyBumpEvaluationFamilyData.points_injective {alpha : Type*} {N : ℕ}
    (data : GreedyBumpEvaluationFamilyData alpha N) :
    Function.Injective data.points :=
  (Classical.choose_spec data.exists_strictPacket).1

/-- Chosen evaluation Gram is strictly positive definite. -/
theorem GreedyBumpEvaluationFamilyData.evaluationGram_posDef
    {alpha : Type*} {N : ℕ} (data : GreedyBumpEvaluationFamilyData alpha N) :
    (finiteEvaluationGram data.feature data.points).PosDef :=
  (Classical.choose_spec data.exists_strictPacket).2

/-- Doubled-real chosen evaluation Gram. -/
def GreedyBumpEvaluationFamilyData.realifiedMatrix {alpha : Type*} {N : ℕ}
    (data : GreedyBumpEvaluationFamilyData alpha N) :
    Matrix (Fin (N + N)) (Fin (N + N)) ℝ :=
  (complexMatrixRealification
      (finiteEvaluationGram data.feature data.points)).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm

/-- Synthesized evaluation packet as a positive template metric. -/
def GreedyBumpEvaluationFamilyData.metric {alpha : Type*} {N : ℕ}
    (data : GreedyBumpEvaluationFamilyData alpha N) : PositiveTemplateMetric (N + N) where
  matrix := data.realifiedMatrix
  posDef := (complexMatrixRealification_posDef
    data.evaluationGram_posDef).submatrix finSumFinEquiv.symm.injective

/-- Every independent function dictionary admits the complete local-search package. -/
theorem GreedyBumpEvaluationFamilyData.laws {alpha : Type*} {N : ℕ}
    (data : GreedyBumpEvaluationFamilyData alpha N) (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q data.metric :=
  greedyBumpMetricLaws_closed Q data.metric

/-- `N` independent complex features contribute exact leading bias `N / Q`. -/
theorem GreedyBumpEvaluationFamilyData.bias {alpha : Type*} {N : ℕ}
    (data : GreedyBumpEvaluationFamilyData alpha N) (Q : PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q data.metric)⁻¹ * data.metric.matrix) =
      (N : ℝ) / (Q : ℝ) := by
  rw [greedyBump_matched_bias]
  push_cast
  field_simp [ne_of_gt Q.property]
  ring

end

end GaloisForLFunctions.HTGeometry

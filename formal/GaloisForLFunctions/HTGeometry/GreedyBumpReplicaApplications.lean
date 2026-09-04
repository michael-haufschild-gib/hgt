import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry
import GaloisForLFunctions.HTGeometry.PureStateReplicaProjectiveGramLaw

/-!
# Greedy-bump replica applications

The pure-state replica Gram law is identified with the matched Hessian
`H_Q = QG` from arXiv:2609.03581. Positivity and normalization are bundled,
so exported bridge theorems carry no propositional hypotheses.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Positive replica count, with nonzero order carried as data. -/
abbrev PositiveReplicaOrder := {r : ℕ // 0 < r}

/-- Normalized finite pure-state model with positive projective Gram. -/
structure PositivePureStateModel (α : Type*) [Fintype α] (v : ℕ) where
  state : α → ℂ
  tangent : Fin v → α → ℂ
  normalized : finiteComplexInner state state = 1
  gram_posDef : (finitePureStateProjectiveGram state tangent).PosDef

/-- Replica order as a positive signal amplitude. -/
def PositiveReplicaOrder.signal (r : PositiveReplicaOrder) : PositiveSignal :=
  ⟨(r : ℕ), by exact_mod_cast r.property⟩

/-- Projective Gram as a bundled positive template metric. -/
def PositivePureStateModel.templateMetric {α : Type*} [Fintype α] {v : ℕ}
    (model : PositivePureStateModel α v) : PositiveTemplateMetric v where
  matrix := finitePureStateProjectiveGram model.state model.tangent
  posDef := model.gram_posDef

/-- Replica projective Gram is exactly the paper's matched Hessian. -/
theorem greedyBump_replicaGram_eq_matchedHessian
    {α : Type*} [Fintype α] {v : ℕ}
    (model : PositivePureStateModel α v) (r : PositiveReplicaOrder) :
    finitePureStateReplicaProjectiveGram r model.state model.tangent =
      greedyBumpHessian r.signal model.templateMetric := by
  rw [finitePureStateReplicaProjectiveGram_eq_smul
    (r : ℕ) model.state model.tangent model.normalized]
  rfl

/-- Replica volume factor is exactly `r^v`, the trials-factor exponent. -/
theorem greedyBump_replicaGram_det_volume
    {α : Type*} [Fintype α] {v : ℕ}
    (model : PositivePureStateModel α v) (r : PositiveReplicaOrder) :
    (finitePureStateReplicaProjectiveGram r model.state model.tangent).det =
      (r : ℕ) ^ v *
        (finitePureStateProjectiveGram model.state model.tangent).det := by
  exact det_finitePureStateReplicaProjectiveGram
    (r : ℕ) model.state model.tangent model.normalized

/-- Replica matched trace penalty is exactly `v/r`. -/
theorem greedyBump_replica_trace_penalty
    {α : Type*} [Fintype α] {v : ℕ}
    (model : PositivePureStateModel α v) (r : PositiveReplicaOrder) :
    Matrix.trace
      ((finitePureStateReplicaProjectiveGram r model.state model.tangent)⁻¹ *
        finitePureStateProjectiveGram model.state model.tangent) =
      (v : ℝ) / (r : ℕ) := by
  rw [greedyBump_replicaGram_eq_matchedHessian]
  exact greedyBumpHessian_trace_inv_mul r.signal model.templateMetric

/-- Replica local profiling bias is exactly `v/(2r)`. -/
theorem greedyBump_replica_local_bias
    {α : Type*} [Fintype α] {v : ℕ}
    (model : PositivePureStateModel α v) (r : PositiveReplicaOrder) :
    (1 / 2 : ℝ) * Matrix.trace
      ((finitePureStateReplicaProjectiveGram r model.state model.tangent)⁻¹ *
        finitePureStateProjectiveGram model.state model.tangent) =
      (v : ℝ) / (2 * (r : ℕ)) := by
  rw [greedyBump_replicaGram_eq_matchedHessian]
  exact greedyBump_matched_bias r.signal model.templateMetric

end

end GaloisForLFunctions.HTGeometry

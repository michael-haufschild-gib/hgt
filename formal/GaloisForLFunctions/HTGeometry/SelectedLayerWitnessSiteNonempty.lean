import GaloisForLFunctions.HTGeometry.LocalInteractionLiftAnalyticRelationLaw
import GaloisForLFunctions.HTGeometry.PolynomialPhaseMomentGap

/-!
# Two membership premises with producers already in reach

The selected-layer relation theorems quantify over points of the witness's analytic site `S`, and
the moment-gap theorems over patterns of the minimal cluster.  Neither membership had a producer
the premise scan could see, although both sets are known to be nonempty — the site by the witness's
own infiniteness field, the cluster by a recorded theorem whose conclusion is stated through
`Finset.Nonempty` rather than an existential.

Both are restated here in the existential form the consumers need.
-/

namespace GaloisForLFunctions

namespace HTGeometry

variable {α ρ : Type*} [Fintype α] [Fintype ρ] [DecidableEq α] [DecidableEq ρ]

/-- The analytic site of a selected-layer witness is nonempty: it is infinite by construction. -/
theorem SelectedLayerAnalyticRelationWitness.site_nonempty
    {energy : α → ℝ} {transition : Matrix α α ℂ} {coefficient : α × ρ → ℂ} {r s : ρ}
    (W : SelectedLayerAnalyticRelationWitness energy transition coefficient r s) :
    W.S.Nonempty :=
  W.infinite.nonempty

/-- Hence the site-membership premise is satisfiable. -/
theorem SelectedLayerAnalyticRelationWitness.exists_mem_site
    {energy : α → ℝ} {transition : Matrix α α ℂ} {coefficient : α × ρ → ℂ} {r s : ρ}
    (W : SelectedLayerAnalyticRelationWitness energy transition coefficient r s) :
    ∃ z : ℂ, z ∈ W.S :=
  W.site_nonempty

end HTGeometry

/-- The minimal pattern cluster has a member: the existential form of the recorded nonemptiness. -/
theorem exists_mem_polynomialPatternMinimalCluster {M D R : ℕ}
    (S : Finset (Fin M → Fin (D + 1))) (hS : S.Nonempty) :
    ∃ p : Fin M → Fin (D + 1), p ∈ polynomialPatternMinimalCluster (R := R) S hS :=
  polynomialPatternMinimalCluster_nonempty (R := R) S hS

end GaloisForLFunctions

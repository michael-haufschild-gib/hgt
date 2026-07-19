import GaloisForLFunctions.HTGeometry.JetIndexReindexGenericity
import GaloisForLFunctions.HTGeometry.WeightedJetControlSurjective

/-!
# Full expanded rank is generic among bounded reweightings

Assembling the genericity chain for the reweighting family.  The jet map of a bounded reweighting is
surjective over a base measure of infinite support carrying a strictly positive integrable density,
and surjectivity of the jet map is the only input the genericity conclusion still needs.

So the reweightings carrying full expanded column rank are open, dense and residual, with no
transversality, differentiability or reachability hypothesis anywhere.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- **Genericity of full expanded rank among bounded reweightings.**  Over a base measure of
infinite support with a strictly positive integrable density, the bounded reweightings whose jets
give the expanded evaluation matrix full column rank are open, dense and residual. -/
theorem exists_nodes_residual_expandedMatrix_weightedJetControl
    {κ ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (q n : ℕ) (exponent : κ → (Fin n →₀ ℕ)) (hexp : Function.Injective exponent)
    (μ : Measure ℝ) (hsupp : μ.support.Infinite)
    (w : ℝ → ℝ) (hw : Integrable w μ) (hwpos : ∀ t, 0 < w t)
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (orders : ι → ℕ)
    (e : ((κ × Fin (q + 1)) × Fin n) ≃ jetIndex orders) :
    ∃ z : κ × Fin (q + 1) → ℂ,
      Function.Injective z ∧
      IsOpen {u : Lp ℝ ⊤ μ | Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent
          (funLeftCLM (e : ((κ × Fin (q + 1)) × Fin n) → jetIndex orders)
            (weightedJetControl μ w hw x (fun i => ne_of_gt (hupper i)) orders u))).mulVec} ∧
      Dense {u : Lp ℝ ⊤ μ | Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent
          (funLeftCLM (e : ((κ × Fin (q + 1)) × Fin n) → jetIndex orders)
            (weightedJetControl μ w hw x (fun i => ne_of_gt (hupper i)) orders u))).mulVec} ∧
      {u : Lp ℝ ⊤ μ | Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent
          (funLeftCLM (e : ((κ × Fin (q + 1)) × Fin n) → jetIndex orders)
            (weightedJetControl μ w hw x (fun i => ne_of_gt (hupper i)) orders u))).mulVec}
        ∈ residual (Lp ℝ ⊤ μ) :=
  exists_nodes_residual_expandedMatrix_of_surjective_jetMap q n exponent hexp
    (weightedJetControl μ w hw x (fun i => ne_of_gt (hupper i)) orders)
    (surjective_weightedJetControl μ hsupp w hw hwpos x hx hupper orders) e

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.IncubationTubeTransport

/-!
# The weak-cut synthesis cap and its time bound

A decoupled Hamiltonian prepares its orbit with the split synthesis cost, and Duhamel's bound says
the coupled orbit stays within `|t|‖V‖` of the decoupled one.  So the coupled orbit inherits the
split cap at every time for which that displacement is below the error budget.

Read backwards, exceeding the split cap forces the elapsed time above the ratio of the remaining
error budget to the coupling norm: a weak bond delays the first full-complexity epoch in exact
proportion to its weakness.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry
open scoped Matrix.Norms.L2Operator

noncomputable section

section WeakCut

variable {d : Type*} [Fintype d] [DecidableEq d] {Γ : Type*}

/-- **`(4)`: the coupled orbit inherits the split synthesis cap.**  While the Duhamel displacement
stays inside the error budget, the coupled orbit is prepared by the decoupled circuits. -/
theorem approxComplexity_le_of_decoupled
    (act : Γ → EuclideanSpace ℂ d → EuclideanSpace ℂ d) (chi : EuclideanSpace ℂ d)
    {H H₀ : Matrix d d ℂ} (hH : IsSelfAdjoint H) (hH₀ : IsSelfAdjoint H₀)
    {ψ : EuclideanSpace ℂ d} (hψ : ‖ψ‖ = 1) {eta eps : ℝ} {S : ℕ}
    (hcert : ∀ s : ℝ, ∃ w : List Γ, w.length ≤ S ∧
      dist (orbitState H₀ ψ s) (wordAct act w chi) ≤ eta)
    {t : ℝ} (ht0 : 0 ≤ t) (hgap : t * ‖H - H₀‖ ≤ eps - eta) :
    approxComplexity act chi eps (orbitState H ψ t) ≤ S :=
  approxComplexity_orbitState_le_of_window act chi hH hH₀ hψ hcert hgap ht0 le_rfl

/-- **`(6)`: exceeding the split cap forces a late time.**  If the coupled orbit is harder than the
split cap, the elapsed time exceeds the error budget divided by the coupling norm. -/
theorem lt_time_of_exceeds_cap
    (act : Γ → EuclideanSpace ℂ d → EuclideanSpace ℂ d) (chi : EuclideanSpace ℂ d)
    {H H₀ : Matrix d d ℂ} (hH : IsSelfAdjoint H) (hH₀ : IsSelfAdjoint H₀)
    {ψ : EuclideanSpace ℂ d} (hψ : ‖ψ‖ = 1) {eta eps : ℝ} {S : ℕ}
    (hcert : ∀ s : ℝ, ∃ w : List Γ, w.length ≤ S ∧
      dist (orbitState H₀ ψ s) (wordAct act w chi) ≤ eta)
    {t : ℝ} (ht0 : 0 ≤ t) (hV : 0 < ‖H - H₀‖)
    (hhard : S < approxComplexity act chi eps (orbitState H ψ t)) :
    (eps - eta) / ‖H - H₀‖ < t := by
  by_contra hcon
  have hle : t ≤ (eps - eta) / ‖H - H₀‖ := le_of_not_gt hcon
  have hgap : t * ‖H - H₀‖ ≤ eps - eta := by
    rw [← le_div_iff₀ hV]
    exact hle
  exact absurd (approxComplexity_le_of_decoupled act chi hH hH₀ hψ hcert ht0 hgap)
    (not_le.mpr hhard)

/-- The cap is monotone in the budget: a larger error budget keeps the same cap. -/
theorem approxComplexity_le_of_decoupled_mono
    (act : Γ → EuclideanSpace ℂ d → EuclideanSpace ℂ d) (chi : EuclideanSpace ℂ d)
    {H H₀ : Matrix d d ℂ} (hH : IsSelfAdjoint H) (hH₀ : IsSelfAdjoint H₀)
    {ψ : EuclideanSpace ℂ d} (hψ : ‖ψ‖ = 1) {eta eps eps' : ℝ} {S : ℕ}
    (hcert : ∀ s : ℝ, ∃ w : List Γ, w.length ≤ S ∧
      dist (orbitState H₀ ψ s) (wordAct act w chi) ≤ eta)
    {t : ℝ} (ht0 : 0 ≤ t) (hgap : t * ‖H - H₀‖ ≤ eps - eta) (hmono : eps ≤ eps') :
    approxComplexity act chi eps' (orbitState H ψ t) ≤ S := by
  refine approxComplexity_le_of_decoupled act chi hH hH₀ hψ hcert ht0 ?_
  linarith

end WeakCut

end

end GaloisForLFunctions.HTGeometry

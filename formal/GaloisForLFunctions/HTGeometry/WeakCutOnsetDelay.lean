import GaloisForLFunctions.HTGeometry.ResolutionTimeNoncommutativity

/-!
# The cut-conductance delay law

A state within one resolution budget of a synthesizable state is itself synthesizable at the total
budget with the same circuit, so an approximate complexity is inherited across every
resolution-sized displacement.

For a Schrödinger orbit the displacement from the decoupled orbit is the elapsed time times the
operator norm of the interaction, by Duhamel.  Hence, up to the time at which that displacement
exhausts the remaining resolution, the orbit's approximate complexity never exceeds the synthesis
cost of the decoupled orbit; equivalently, the first time at which complexity can exceed that cost
is at least the remaining resolution divided by the interaction norm.
-/

open Matrix

open scoped Matrix Matrix.Norms.L2Operator

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry

noncomputable section

section AbstractDelay

variable {X : Type*} [MetricSpace X] {Γ : Type*}

/-- **Approximation transfer.**  A state within `δ₁` of a state synthesizable to `δ₂` by `s` gates
has approximate complexity at most `s` at every resolution above `δ₁ + δ₂`. -/
theorem approxComplexity_le_of_near {act : Γ → X → X} {chi : X} {x y : X} {s : ℕ}
    {δ₁ δ₂ ε : ℝ} (h₁ : dist x y ≤ δ₁)
    (hw : ∃ w : List Γ, w.length ≤ s ∧ dist y (wordAct act w chi) ≤ δ₂)
    (hsum : δ₁ + δ₂ ≤ ε) :
    approxComplexity act chi ε x ≤ s := by
  obtain ⟨w, hlen, hd⟩ := hw
  refine Nat.sInf_le ⟨w, hlen, ?_⟩
  calc dist x (wordAct act w chi) ≤ dist x y + dist y (wordAct act w chi) :=
        dist_triangle _ _ _
    _ ≤ δ₁ + δ₂ := add_le_add h₁ hd
    _ ≤ ε := hsum

end AbstractDelay

section Schroedinger

variable {d : Type*} [Fintype d] [DecidableEq d] {Γ : Type*}

/-- **Equation `(7)`.**  Two Schrödinger orbits of the same unit seed separate at most at the rate
of the generator distance. -/
theorem dist_evolvedState_sub_le {H K : Matrix d d ℂ} (hH : IsSelfAdjoint H)
    (hK : IsSelfAdjoint K) (t : ℝ) {ψ : EuclideanSpace ℂ d} (hψ : ‖ψ‖ = 1) :
    dist (evolvedState H t ψ) (evolvedState K t ψ) ≤ |t| * ‖H - K‖ := by
  rw [dist_eq_norm]
  have h := QuantumAlg.norm_unitaryEvolution_mulVec_sub_le hH hK t ψ
  rw [hψ, mul_one] at h
  exact h

/-- **Cut-conductance delay law, equation `(4)`.**  While the interaction displacement stays within
the remaining resolution, the interacting orbit inherits the synthesis cost of the decoupled
orbit. -/
theorem approxComplexity_evolvedState_le_synthesis
    {act : Γ → EuclideanSpace ℂ d → EuclideanSpace ℂ d}
    {H K : Matrix d d ℂ} (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K)
    {ψ : EuclideanSpace ℂ d} (hψ : ‖ψ‖ = 1) {t : ℝ} {S : ℕ} {η ε : ℝ}
    (hsyn : ∃ w : List Γ, w.length ≤ S ∧
      dist (evolvedState K t ψ) (wordAct act w ψ) ≤ η)
    (ht : |t| * ‖H - K‖ ≤ ε - η) :
    approxComplexity act ψ ε (evolvedState H t ψ) ≤ S := by
  refine approxComplexity_le_of_near (dist_evolvedState_sub_le hH hK t hψ) hsyn ?_
  linarith

/-- **Onset lower bound, equation `(6)`.**  If the interacting orbit ever exceeds the decoupled
synthesis cost, the elapsed time is at least the remaining resolution over the interaction norm. -/
theorem lt_abs_time_of_lt_approxComplexity
    {act : Γ → EuclideanSpace ℂ d → EuclideanSpace ℂ d}
    {H K : Matrix d d ℂ} (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K)
    {ψ : EuclideanSpace ℂ d} (hψ : ‖ψ‖ = 1) {t : ℝ} {S : ℕ} {η ε : ℝ}
    (hV : 0 < ‖H - K‖)
    (hsyn : ∃ w : List Γ, w.length ≤ S ∧
      dist (evolvedState K t ψ) (wordAct act w ψ) ≤ η)
    (hbig : S < approxComplexity act ψ ε (evolvedState H t ψ)) :
    (ε - η) / ‖H - K‖ < |t| := by
  by_contra hcon
  rw [not_lt, le_div_iff₀ hV] at hcon
  have hle := approxComplexity_evolvedState_le_synthesis hH hK hψ hsyn
    (by linarith : |t| * ‖H - K‖ ≤ ε - η)
  omega

end Schroedinger

end

end GaloisForLFunctions.HTGeometry

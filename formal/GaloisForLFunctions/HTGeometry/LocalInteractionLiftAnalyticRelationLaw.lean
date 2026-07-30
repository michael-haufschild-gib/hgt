import GaloisForLFunctions.HTGeometry.LocalSelectedLayerSpectralResponse

/-!
# Analytic relation space of a local interaction lift

For every selected pair of local labels, the exact second-order spectral
response turns a branchwise eigenvalue relation into equality along the
corresponding interaction-lift edges.  This file assembles those pairwise
analytic statements into one global kernel theorem.

The result is not a graph-connectivity theorem.  It identifies the analytic
spectral-relation kernel with component-constant zero-cochains on the
interaction lift.  Connectivity then leaves only the trace direction.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Old-system transitions detected in both orientations by one Hermitian
interaction channel. -/
def transitionSupportGraph
    {α : Type*} (transition : Matrix α α ℂ) :
    SimpleGraph α where
  Adj a b :=
    a ≠ b ∧ transition a b * transition b a ≠ 0
  symm := ⟨by
    intro a b h
    exact ⟨h.1.symm, by simpa [mul_comm] using h.2⟩⟩
  loopless := ⟨by
    intro a h
    exact h.1 rfl⟩

@[simp] theorem transitionSupportGraph_adj
    {α : Type*} (transition : Matrix α α ℂ) (a b : α) :
    (transitionSupportGraph transition).Adj a b ↔
      a ≠ b ∧ transition a b * transition b a ≠ 0 :=
  Iff.rfl

/-- Complete analytic data obtained by restricting a local extension family
to one selected pair of local labels. -/
structure SelectedLayerAnalyticRelationWitness
    {α ρ : Type*} [Fintype α] [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    (energy : α → ℝ)
    (transition : Matrix α α ℂ)
    (coefficient : α × ρ → ℂ)
    (r s : ρ) where
  S : Set ℂ
  infinite : S.Infinite
  shift : ℂ → ρ → ℂ
  pairShift :
    ∀ z ∈ S, shift z r - shift z s = z
  simple :
    ∀ z ∈ S,
      Function.Injective
        (layeredEnergy
          (fun a => (energy a : ℂ)) (shift z))
  branch : ℂ → (α × ρ) → ℂ → ℂ
  analytic :
    ∀ z ∈ S, ∀ i, AnalyticAt ℂ (branch z i) 0
  base :
    ∀ z ∈ S, ∀ i,
      branch z i 0 =
        layeredEnergy
          (fun a => (energy a : ℂ)) (shift z) i
  root :
    ∀ z ∈ S, ∀ i,
      ∀ᶠ g in 𝓝 0,
        matrixCharpolyRelation
          (Matrix.diagonal
              (layeredEnergy
                (fun a => (energy a : ℂ)) (shift z)) +
            g • selectedLayerCoupling transition r s,
            branch z i g) = 0
  relation :
    ∀ z ∈ S,
      ∀ᶠ g in 𝓝 0,
        ∑ i, coefficient i * branch z i g = 0

/-- **Analytic interaction-lift kernel law.** If one coefficient packet is
an analytic eigenvalue relation on every selected-pair restriction of a
local extension family, then it is a component-constant zero-cochain on the
interaction lift of the detected transition graph. -/
theorem selectedLayerAnalyticRelation_mem_componentConstant
    {α ρ : Type*} [Fintype α] [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ] [Nonempty α]
    (energy : α → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (transition : Matrix α α ℂ)
    (coefficient : α × ρ → ℂ)
    (hwitness :
      ∀ r s, r ≠ s →
        SelectedLayerAnalyticRelationWitness
          energy transition coefficient r s) :
    coefficient ∈
      GaloisForLFunctions.componentConstant
        (crossLayerLiftGraph
          (transitionSupportGraph transition) ρ) ℂ := by
  rw [← crossLayerEquality_iff_mem_componentConstant
    (transitionSupportGraph transition)
    (fun a r => coefficient (a, r))]
  intro a b hab r s hrs
  let W := hwitness r s hrs
  exact crossLayer_eq_of_selectedLayerAnalyticBranchRelation
    energy hmax transition coefficient hrs
    W.S W.infinite W.shift W.pairShift W.simple
    W.branch W.analytic W.base W.root W.relation
    a b hab.1 hab.2

/-- A connected interaction lift annihilates every nontrace analytic
relation: every coefficient in the assembled relation packet is equal. -/
theorem selectedLayerAnalyticRelation_constant_of_preconnected
    {α ρ : Type*} [Fintype α] [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ] [Nonempty α]
    (energy : α → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (transition : Matrix α α ℂ)
    (coefficient : α × ρ → ℂ)
    (hwitness :
      ∀ r s, r ≠ s →
        SelectedLayerAnalyticRelationWitness
          energy transition coefficient r s)
    (hlift :
      (crossLayerLiftGraph
        (transitionSupportGraph transition) ρ).Preconnected) :
    ∀ x y, coefficient x = coefficient y := by
  have hcomponent :=
    selectedLayerAnalyticRelation_mem_componentConstant
      energy hmax transition coefficient hwitness
  intro x y
  obtain ⟨walk⟩ := hlift x y
  induction walk with
  | nil => rfl
  | cons hadj walk ih =>
      exact (hcomponent _ _ hadj).trans ih

/-- Every finite local alphabet of size at least three erases all nontrace
analytic relations whenever the old detected transition graph is connected
and has no isolated vertex. -/
theorem selectedLayerAnalyticRelation_constant_of_three_le_card
    {α ρ : Type*} [Fintype α] [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    [Nonempty α] [Nonempty ρ]
    (energy : α → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (transition : Matrix α α ℂ)
    (coefficient : α × ρ → ℂ)
    (hwitness :
      ∀ r s, r ≠ s →
        SelectedLayerAnalyticRelationWitness
          energy transition coefficient r s)
    (hcard : 3 ≤ Fintype.card ρ)
    (hneighbour :
      ∀ a, ∃ b,
        (transitionSupportGraph transition).Adj a b)
    (hconnected :
      (transitionSupportGraph transition).Preconnected) :
    ∀ x y, coefficient x = coefficient y := by
  apply selectedLayerAnalyticRelation_constant_of_preconnected
    energy hmax transition coefficient hwitness
  exact crossLayerLiftGraph_preconnected_of_spareLabel
    (transitionSupportGraph transition)
    (hasSpareLabel_of_three_le_card ρ hcard)
    hneighbour hconnected

/-- For a two-level local factor, one triangle in the connected detected
transition graph removes the parity obstruction and again leaves only the
trace relation. -/
theorem selectedLayerAnalyticRelation_constant_bool_of_triangle
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (energy : α → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (transition : Matrix α α ℂ)
    (coefficient : α × Bool → ℂ)
    (hwitness :
      ∀ r s, r ≠ s →
        SelectedLayerAnalyticRelationWitness
          energy transition coefficient r s)
    (hconnected :
      (transitionSupportGraph transition).Preconnected)
    {a b c : α}
    (hab : (transitionSupportGraph transition).Adj a b)
    (hbc : (transitionSupportGraph transition).Adj b c)
    (hca : (transitionSupportGraph transition).Adj c a) :
    ∀ x y, coefficient x = coefficient y := by
  apply selectedLayerAnalyticRelation_constant_of_preconnected
    energy hmax transition coefficient hwitness
  exact crossLayerLiftGraph_bool_preconnected_of_triangle
    (transitionSupportGraph transition)
    hconnected hab hbc hca

end

end GaloisForLFunctions.HTGeometry

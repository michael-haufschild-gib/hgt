import GaloisForLFunctions.HTGeometry.NonautonomousStableCore

/-!
# A protocol's tails are constant at every phase or at none

Each microscopic injection restricts to an isomorphism of persistent fields, and an intermediate field
isomorphic to the base over the base is the base.  So triviality of the tail at one phase forces it at
the next, and — running the isomorphism backwards — at the previous one as well.

Hence the all-or-nothing dichotomy: either every phase tail is the constants, or none is.  This is the
first half of the scalar dichotomy, and it needs nothing beyond the exact phase transport.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- **An intermediate field isomorphic to the base is the base.** -/
theorem eq_bot_of_algEquiv_base {L : IntermediateField K F} (e : L ≃ₐ[K] K) : L = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  have hcomm : e (algebraMap K L (e ⟨x, hx⟩)) = e ⟨x, hx⟩ := by
    rw [e.commutes]
    simp
  have hx' : algebraMap K L (e ⟨x, hx⟩) = ⟨x, hx⟩ := e.injective hcomm
  rw [IntermediateField.mem_bot]
  exact ⟨e ⟨x, hx⟩, congrArg Subtype.val hx'⟩

/-- The base, as an intermediate field, is isomorphic to the base. -/
def algEquiv_base_of_eq_bot {L : IntermediateField K F} (h : L = ⊥) : L ≃ₐ[K] K :=
  (IntermediateField.equivOfEq h).trans (IntermediateField.botEquiv K F)

/-- **Triviality of the tail transports across one step.** -/
theorem nonautonomousTail_eq_bot_succ_iff (φ : ℕ → F →ₐ[K] F) (i : ℕ) :
    nonautonomousTail φ i = ⊥ ↔ nonautonomousTail φ (i + 1) = ⊥ := by
  constructor
  · intro h
    exact eq_bot_of_algEquiv_base
      ((nonautonomousTailTransitionAlgEquiv φ i).trans (algEquiv_base_of_eq_bot h))
  · intro h
    exact eq_bot_of_algEquiv_base
      ((nonautonomousTailTransitionAlgEquiv φ i).symm.trans (algEquiv_base_of_eq_bot h))

/-- **Triviality at one phase is triviality at every phase.** -/
theorem nonautonomousTail_eq_bot_of_eq_bot (φ : ℕ → F →ₐ[K] F) {i : ℕ}
    (h : nonautonomousTail φ i = ⊥) : ∀ j, nonautonomousTail φ j = ⊥ := by
  have hzero : nonautonomousTail φ 0 = ⊥ := by
    induction i with
    | zero => exact h
    | succ i ih => exact ih ((nonautonomousTail_eq_bot_succ_iff φ i).2 h)
  intro j
  induction j with
  | zero => exact hzero
  | succ j ih => exact (nonautonomousTail_eq_bot_succ_iff φ j).1 ih

/-- **The scalar dichotomy.**  Either every phase tail is the constants, or none is. -/
theorem nonautonomousTail_dichotomy (φ : ℕ → F →ₐ[K] F) :
    (∀ i, nonautonomousTail φ i = ⊥) ∨ ∀ i, nonautonomousTail φ i ≠ ⊥ := by
  by_cases h : ∃ i, nonautonomousTail φ i = ⊥
  · obtain ⟨i, hi⟩ := h
    exact Or.inl (nonautonomousTail_eq_bot_of_eq_bot φ hi)
  · refine Or.inr fun i hi => h ⟨i, hi⟩

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HilbertMetric.CCRFiniteBlockObstruction

/-!
# Exact finite full-CCR interface classification

The unrestricted finite CCR interface is satisfiable only in the two vacuous chambers: no modes,
or no coordinates.  This completes the positive side of the existing trace obstruction while the
invariant-block realization remains the nonvacuous replacement in positive dimension.
-/

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

variable {I n m : Type*} [Fintype I] [DecidableEq I]
  [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- With no modes, every matrix family satisfies the full CCR interface. -/
theorem isFullCCRMatrixTuple_empty_index
    (T : Empty → Matrix (n ⊕ m) (n ⊕ m) ℝ) :
    IsFullCCRMatrixTuple T := by
  intro i
  exact i.elim

omit [Fintype I] in
/-- With no coordinates, every matrix family satisfies the full CCR interface. -/
theorem isFullCCRMatrixTuple_of_empty_coordinates
    [IsEmpty n] [IsEmpty m]
    (T : I → Matrix (n ⊕ m) (n ⊕ m) ℝ) :
    IsFullCCRMatrixTuple T := by
  intro i j
  ext a b
  exact isEmptyElim a

omit [Fintype I] in
/-- **Full finite-CCR classification.** A full tuple exists exactly in the mode-empty or
coordinate-empty chambers. -/
theorem exists_isFullCCRMatrixTuple_iff_isEmpty
    : (∃ T : I → Matrix (n ⊕ m) (n ⊕ m) ℝ, IsFullCCRMatrixTuple T) ↔
        IsEmpty I ∨ (IsEmpty n ∧ IsEmpty m) := by
  constructor
  · rintro ⟨T, hT⟩
    rcases isEmpty_or_nonempty I with hI | hI
    · exact Or.inl hI
    · letI := hI
      exact Or.inr (isEmpty_of_isFullCCRMatrixTuple T hT)
  · rintro (hI | ⟨hn, hm⟩)
    · letI := hI
      refine ⟨fun i => isEmptyElim i, ?_⟩
      intro i
      exact isEmptyElim i
    · letI := hn
      letI := hm
      exact ⟨0, isFullCCRMatrixTuple_of_empty_coordinates 0⟩

end

end GaloisForLFunctions.HilbertMetric

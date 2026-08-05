import GaloisForLFunctions.HTGeometry.ComplexAffineAlgebraicStratification

/-!
# Affine algebraic sets of arbitrary codimension exist

The empty set is affine algebraic — it is the zero locus of the unit ideal — and every polynomial
vanishes on it, so its vanishing ideal is everything and the coordinate ring of the empty set is the
zero ring.  Its Krull dimension is therefore the bottom element, which stays below the ambient
dimension after adding any codimension.  So the stratification laws apply at every codimension.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Every polynomial vanishes on the empty set, so its vanishing ideal is everything. -/
theorem vanishingIdeal_empty {n : ℕ} :
    MvPolynomial.vanishingIdeal ℂ (∅ : Set (Fin n → ℂ)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  intro x hx
  exact absurd hx (Set.notMem_empty x)

/-- **The empty set has every codimension.** -/
theorem isComplexAffineAlgebraicOfCodimAtLeast_empty {n : ℕ} (c : ℕ) :
    IsComplexAffineAlgebraicOfCodimAtLeast (∅ : Set (Fin n → ℂ)) c := by
  refine ⟨isComplexAffineAlgebraic_empty, ?_⟩
  have hsub : Subsingleton ((MvPolynomial (Fin n) ℂ) ⧸
      MvPolynomial.vanishingIdeal ℂ (∅ : Set (Fin n → ℂ))) := by
    rw [vanishingIdeal_empty]
    exact Ideal.Quotient.subsingleton_iff.mpr rfl
  rw [ringKrullDim_eq_bot_of_subsingleton]
  simp

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.DifferentialPolynomialRank

/-!
# Minimal Ritt rank over a coefficient ring

Over a field a nonzero constant is a unit, so a proper ideal contains none and every nonzero
element of it is nonconstant.  Over a coefficient ring that role is played by the contraction of the
ideal: if no nonzero constant lies in the ideal, the same conclusion holds, and the minimal-rank
selection goes through unchanged.

* `Ideal.exists_nonzero_nonconstant_scalarDifferentialPolynomial_of_trivialContraction`;
* `Ideal.exists_minimal_scalarDifferentialPolynomialRank_of_trivialContraction`.
-/

namespace GaloisForLFunctions

noncomputable section

/-- A nonzero ideal whose contraction to the coefficients is zero contains a nonzero nonconstant
differential polynomial. -/
theorem Ideal.exists_nonzero_nonconstant_scalarDifferentialPolynomial_of_trivialContraction
    {R : Type*} [CommRing R]
    {I : Ideal (DifferentialPolynomial Unit R)}
    (hI0 : I ≠ ⊥)
    (hIC : ∀ r : R, (MvPolynomial.C r : DifferentialPolynomial Unit R) ∈ I → r = 0) :
    ∃ P : DifferentialPolynomial Unit R,
      P ∈ I ∧ P ≠ 0 ∧ P.vars.Nonempty := by
  classical
  have hex : ∃ P : DifferentialPolynomial Unit R, P ∈ I ∧ P ≠ 0 := by
    by_contra h
    apply hI0
    ext P
    simp only [Ideal.mem_bot]
    constructor
    · intro hPI
      by_contra hP0
      exact h ⟨P, hPI, hP0⟩
    · intro hP
      subst P
      exact I.zero_mem
  obtain ⟨P, hPI, hP0⟩ := hex
  by_cases hPv : P.vars.Nonempty
  · exact ⟨P, hPI, hP0, hPv⟩
  · have hPvars : P.vars = ∅ := Finset.not_nonempty_iff_eq_empty.mp hPv
    have hPC : P = MvPolynomial.C (P.coeff 0) :=
      MvPolynomial.vars_eq_empty_iff_eq_C.mp hPvars
    have hc : P.coeff 0 = 0 := hIC _ (by rw [← hPC]; exact hPI)
    exact absurd (by rw [hPC, hc]; simp) hP0

/-- A nonzero ideal whose contraction to the coefficients is zero contains an element of minimal
Ritt rank: order, then leader degree, then total degree. -/
theorem Ideal.exists_minimal_scalarDifferentialPolynomialRank_of_trivialContraction
    {R : Type*} [CommRing R]
    {I : Ideal (DifferentialPolynomial Unit R)}
    (hI0 : I ≠ ⊥)
    (hIC : ∀ r : R, (MvPolynomial.C r : DifferentialPolynomial Unit R) ∈ I → r = 0) :
    ∃ P : DifferentialPolynomial Unit R,
      IsMinimalScalarDifferentialPolynomialRank (I : Set _) P :=
  exists_minimalScalarDifferentialPolynomialRank
    (Ideal.exists_nonzero_nonconstant_scalarDifferentialPolynomial_of_trivialContraction
      (I := I) hI0 hIC)

end

end GaloisForLFunctions

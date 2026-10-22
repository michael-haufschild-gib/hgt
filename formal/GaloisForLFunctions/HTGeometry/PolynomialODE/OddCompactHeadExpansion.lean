import GaloisForLFunctions.HTGeometry.PolynomialODE.OddCompactScalarPolynomials

/-!
# Exact scalar odd determinant elimination

The literal reflected entries give the displayed scalar polynomials by ring
identities. These identities impose no trajectory or sign assumptions.
-/

namespace HTGeometry
noncomputable section
set_option maxRecDepth 100000

/-- Real scalar identity for the odd head. -/
theorem oddCompactHeadScalar_identity (u a w : ℝ) :
    ((-oddCompactReflectedScalar2 u a w)*(-oddCompactReflectedScalar6 u a w) - (oddCompactReflectedScalar4 u a w)^(2 : ℕ)) = oddCompactScalarHead u a w := by
  as_aux_lemma =>
    unfold oddCompactReflectedScalar2 oddCompactReflectedScalar4 oddCompactReflectedScalar6 oddCompactScalarHead
      oddCompactScalarHeadPart0 oddCompactScalarHeadPart1 oddCompactScalarHeadPart2 oddCompactScalarHeadPart3 oddCompactScalarHeadPart4 oddCompactScalarHeadPart5
    ring


/-- Exact normalization of the complete odd head. -/
theorem oddCompactHead_eq_scalarPolynomial (u a w : ℝ) :
    oddCompactHead u a w = oddCompactScalarHead u a w := by
  rw [oddCompactHead_eq_reflectedScalars]
  exact oddCompactHeadScalar_identity u a w

end
end HTGeometry

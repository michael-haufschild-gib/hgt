import GaloisForLFunctions.HTGeometry.PolynomialODE.OddCompactReflected10

/-! Exact scalar formation of the normalized odd determinant and leading minor. -/

namespace HTGeometry
noncomputable section

/-- The normalized real determinant is formed from the five exact reflected scalars. -/
theorem oddCompactDet_eq_reflectedScalars (u a w : ℝ) :
    oddCompactDet u a w =
      (-oddCompactReflectedScalar2 u a w)*(-oddCompactReflectedScalar6 u a w)*
        (-oddCompactReflectedScalar10 u a w) -
      (-oddCompactReflectedScalar2 u a w)*(oddCompactReflectedScalar8 u a w)^(2 : ℕ) -
      (oddCompactReflectedScalar4 u a w)^(2 : ℕ)*(-oddCompactReflectedScalar10 u a w) +
      2*oddCompactReflectedScalar4 u a w*(-oddCompactReflectedScalar6 u a w)*
        oddCompactReflectedScalar8 u a w - (-oddCompactReflectedScalar6 u a w)^(3 : ℕ) := by
  unfold oddCompactDet
  rw [eval_oddCompactDetPolynomial]
  dsimp only
  rw [oddCompactReflectedScalar2_eq, oddCompactReflectedScalar4_eq,
    oddCompactReflectedScalar6_eq, oddCompactReflectedScalar8_eq, oddCompactReflectedScalar10_eq]
  simp [← Complex.ofReal_pow, ← Complex.ofReal_neg]

/-- The normalized real leading minor uses the same exact reflected scalars. -/
theorem oddCompactHead_eq_reflectedScalars (u a w : ℝ) :
    oddCompactHead u a w =
      (-oddCompactReflectedScalar2 u a w)*(-oddCompactReflectedScalar6 u a w) -
        (oddCompactReflectedScalar4 u a w)^(2 : ℕ) := by
  unfold oddCompactHead
  rw [eval_oddCompactHeadPolynomial]
  rw [oddCompactReflectedScalar2_eq, oddCompactReflectedScalar4_eq, oddCompactReflectedScalar6_eq]
  simp [← Complex.ofReal_pow, ← Complex.ofReal_neg]

end
end HTGeometry

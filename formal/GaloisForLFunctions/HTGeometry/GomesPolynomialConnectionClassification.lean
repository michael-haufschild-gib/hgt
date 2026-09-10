import GaloisForLFunctions.HTGeometry.GomesPolynomialConnectionConstantRigidity

/-!
# Classification of all scalar polynomial connections up to linear conjugacy

Constant coefficients are individually rigid. Every positive degree is one
nonconstant conjugacy class. These statements classify the full family without
an assumed intertwiner or an unproved analytic realization.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- Complete conjugacy classification: identical coefficients, or a common positive degree. -/
theorem gomesPolynomialConnection_intertwiner_iff (A B : ℝ[X]) :
    Nonempty (GomesPolynomialConnectionIntertwiner A B) ↔
      A = B ∨ (A.derivative ≠ 0 ∧ B.derivative ≠ 0 ∧ A.natDegree = B.natDegree) := by
  constructor
  · rintro ⟨E⟩
    by_cases ha : A.derivative = 0
    · left
      have hca := eq_C_of_derivative_eq_zero ha
      have hb : B = C (A.coeff 0) := by
        apply gomesPolynomialConnectionIntertwiner_constant_source (A.coeff 0) B
        exact hca ▸ E
      exact hca.trans hb.symm
    · by_cases hb : B.derivative = 0
      · left
        have hcb := eq_C_of_derivative_eq_zero hb
        have ha' : A = C (B.coeff 0) := by
          apply (gomesPolynomialConnection_constant_target_intertwiner_iff A (B.coeff 0)).mp
          exact ⟨hcb ▸ E⟩
        exact ha'.trans hcb.symm
      · exact Or.inr ⟨ha, hb, gomesPolynomialConnectionIntertwiner_degree A B E⟩
  · rintro (rfl | ⟨ha, hb, hd⟩)
    · exact ⟨gomesPolynomialConnectionIntertwinerRefl _⟩
    · exact (gomesPolynomialConnection_nonconstant_intertwiner_iff ⟨A, ha⟩ ⟨B, hb⟩).mpr hd

/-- Disjoint constant and nonconstant classes give an alternative complete classification. -/
theorem gomesPolynomialConnection_intertwiner_cases (A B : ℝ[X]) :
    Nonempty (GomesPolynomialConnectionIntertwiner A B) ↔
      (∃ a : ℝ, A = C a ∧ B = C a) ∨
        (A.derivative ≠ 0 ∧ B.derivative ≠ 0 ∧ A.natDegree = B.natDegree) := by
  rw [gomesPolynomialConnection_intertwiner_iff]
  constructor
  · rintro (he | h)
    · subst B
      by_cases ha : A.derivative = 0
      · exact Or.inl ⟨A.coeff 0, eq_C_of_derivative_eq_zero ha, eq_C_of_derivative_eq_zero ha⟩
      · exact Or.inr ⟨ha, ha, rfl⟩
    · exact Or.inr h
  · rintro (⟨a, ha, hb⟩ | h)
    · exact Or.inl (ha.trans hb.symm)
    · exact Or.inr h

/-- Positive-degree conjugacy is measured exactly by the connection cokernel dimension. -/
theorem gomesPolynomialConnection_nonconstant_cokernel_complete
    (A B : GomesNonconstantPolynomialCoefficient) :
    Nonempty (GomesPolynomialConnectionIntertwiner A.val B.val) ↔
      Module.finrank ℝ (GomesPolynomialConnectionCokernel A.val) =
        Module.finrank ℝ (GomesPolynomialConnectionCokernel B.val) := by
  rw [gomesPolynomialConnection_nonconstant_intertwiner_iff,
    gomesPolynomialConnectionCokernel_finrank_all, gomesPolynomialConnectionCokernel_finrank_all]

/-- The exact algebraic connection index also completely classifies the nonconstant sector. -/
theorem gomesPolynomialConnection_nonconstant_index_complete
    (A B : GomesNonconstantPolynomialCoefficient) :
    Nonempty (GomesPolynomialConnectionIntertwiner A.val B.val) ↔
      gomesPolynomialConnectionIndex A.val = gomesPolynomialConnectionIndex B.val := by
  rw [gomesPolynomialConnection_nonconstant_intertwiner_iff,
    gomesPolynomialConnectionIndex_exact, gomesPolynomialConnectionIndex_exact,
    if_neg (gomesNonconstantPolynomialCoefficient_ne_zero A),
    if_neg (gomesNonconstantPolynomialCoefficient_ne_zero B), neg_inj, Int.natCast_inj]

/-- The pure derivative is conjugate only to itself among these coefficient connections. -/
theorem gomesPolynomialConnection_derivative_intertwiner_iff (A : ℝ[X]) :
    Nonempty (GomesPolynomialConnectionIntertwiner 0 A) ↔ A = 0 := by
  simpa only [map_zero] using gomesPolynomialConnection_constant_source_intertwiner_iff 0 A

/-- Point spectrum together with coefficient degree completely recovers the linear conjugacy class. -/
theorem gomesPolynomialConnection_eigenvalues_degree_complete (A B : ℝ[X]) :
    Nonempty (GomesPolynomialConnectionIntertwiner A B) ↔
      gomesPolynomialFirstOrderEigenvalues A = gomesPolynomialFirstOrderEigenvalues B ∧
        A.natDegree = B.natDegree := by
  constructor
  · intro h
    refine ⟨?_, (let ⟨E⟩ := h; gomesPolynomialConnectionIntertwiner_degree A B E)⟩
    rcases (gomesPolynomialConnection_intertwiner_iff A B).mp h with rfl | ⟨ha, hb, _⟩
    · rfl
    · rw [gomesPolynomialFirstOrderEigenvalues_nonconstant ⟨A, ha⟩,
        gomesPolynomialFirstOrderEigenvalues_nonconstant ⟨B, hb⟩]
  · rintro ⟨he, hd⟩
    by_cases ha : A.derivative = 0
    · have hca := eq_C_of_derivative_eq_zero ha
      have hx : -(A.coeff 0) ∈ gomesPolynomialFirstOrderEigenvalues B := by
        rw [← he, hca, gomesPolynomialFirstOrderEigenvalues_constant]
        simpa using Set.mem_singleton (-(A.coeff 0))
      have hz := (gomesPolynomialFirstOrderEigenvalues_mem_iff B (-(A.coeff 0))).mp hx
      have hcb : B = C (A.coeff 0) := by
        simpa only [map_neg, neg_neg] using eq_neg_of_add_eq_zero_left hz
      apply (gomesPolynomialConnection_intertwiner_iff A B).mpr
      exact Or.inl (hca.trans hcb.symm)
    · have hb : B.derivative ≠ 0 := by
        rw [derivative_ne_zero, ← hd]
        exact derivative_ne_zero.mp ha
      exact (gomesPolynomialConnection_nonconstant_intertwiner_iff ⟨A, ha⟩ ⟨B, hb⟩).mpr hd

/-- Polynomial eigenvalues and the number of missing outputs are complete conjugacy invariants. -/
theorem gomesPolynomialConnection_eigenvalues_cokernel_complete (A B : ℝ[X]) :
    Nonempty (GomesPolynomialConnectionIntertwiner A B) ↔
      gomesPolynomialFirstOrderEigenvalues A = gomesPolynomialFirstOrderEigenvalues B ∧
        Module.finrank ℝ (GomesPolynomialConnectionCokernel A) =
          Module.finrank ℝ (GomesPolynomialConnectionCokernel B) := by
  rw [gomesPolynomialConnection_eigenvalues_degree_complete,
    gomesPolynomialConnectionCokernel_finrank_all, gomesPolynomialConnectionCokernel_finrank_all]

end GaloisForLFunctions.HTGeometry

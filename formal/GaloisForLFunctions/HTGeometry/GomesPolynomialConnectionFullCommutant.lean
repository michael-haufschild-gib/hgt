import GaloisForLFunctions.HTGeometry.GomesFormalSeriesOperatorAlgebra
import GaloisForLFunctions.HTGeometry.GomesPolynomialCommutantReconstruction

/-!
# Full symmetry algebras for every polynomial connection

Constant coefficients give the formal power-series algebra of differentiation.
Nonconstant coefficients give polynomial matrix algebras from the orbit chains.
Together these classify the full commutant in every coefficient sector and locate
the exact commutativity boundary at coefficient degree one.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- Every constant-coefficient connection has exactly the differentiation commutant. -/
theorem gomesPolynomialConstantConnection_commutant_algebra (a : ℝ) :
    gomesPolynomialConnectionCommutantAlgebra (C a) =
      gomesPolynomialDerivativeCommutantAlgebra ℝ := by
  have h := gomesPolynomialConnectionCommutant_shift (0 : ℝ[X]) a
  simp only [zero_add] at h
  rw [h]
  have hd : gomesPolynomialFirstOrderLinearMap 0 = (Polynomial.derivative : Module.End ℝ ℝ[X]) := by
    apply LinearMap.ext
    intro P
    simp [gomesPolynomialFirstOrderLinearMap, gomesPolynomialFirstOrderOperator]
  rw [gomesPolynomialConnectionCommutantAlgebra, hd, gomesPolynomialDerivativeCommutantAlgebra]

/-- The full symmetry algebra of any constant-coefficient connection is a formal series algebra. -/
def gomesPolynomialConstantConnectionCommutantEquiv (a : ℝ) :
    GomesPolynomialConnectionCommutant (C a) ≃ₐ[ℝ] PowerSeries ℝ := by
  change ↥(gomesPolynomialConnectionCommutantAlgebra (C a)) ≃ₐ[ℝ] PowerSeries ℝ
  rw [gomesPolynomialConstantConnection_commutant_algebra]
  exact gomesPolynomialDerivativeCommutantEquiv ℝ

/-- Every polynomial connection has a full formal-series or polynomial-matrix symmetry classification. -/
theorem gomesPolynomialConnection_full_commutant_classification (A : ℝ[X]) :
    (A.derivative = 0 ∧ Nonempty (GomesPolynomialConnectionCommutant A ≃ₐ[ℝ] PowerSeries ℝ)) ∨
      (A.derivative ≠ 0 ∧ Nonempty (GomesPolynomialConnectionCommutant A ≃ₐ[ℝ]
        Matrix (Fin A.natDegree) (Fin A.natDegree) ℝ[X])) := by
  by_cases h : A.derivative = 0
  · refine Or.inl ⟨h, ?_⟩
    rw [eq_C_of_derivative_eq_zero h]
    exact ⟨gomesPolynomialConstantConnectionCommutantEquiv (A.coeff 0)⟩
  · exact Or.inr ⟨h, ⟨gomesPolynomialConnectionCommutantMatrixEquiv ⟨A, h⟩⟩⟩

/-- All symmetries of a constant-coefficient connection commute. -/
theorem gomesPolynomialConstantConnectionCommutant_commutative (a : ℝ)
    (E F : GomesPolynomialConnectionCommutant (C a)) : E * F = F * E := by
  apply (gomesPolynomialConstantConnectionCommutantEquiv a).injective
  rw [map_mul, map_mul, mul_comm]

/-- Across all polynomial coefficients, the full commutant is commutative exactly up to degree one. -/
theorem gomesPolynomialConnection_full_commutant_commutative_iff (A : ℝ[X]) :
    (∀ E F : GomesPolynomialConnectionCommutant A, E * F = F * E) ↔ A.natDegree ≤ 1 := by
  by_cases h : A.derivative = 0
  · have hn : A.natDegree = 0 := derivative_eq_zero.mp h
    constructor
    · intro _
      rw [hn]
      exact Nat.zero_le _
    · intro _
      rw [eq_C_of_derivative_eq_zero h]
      exact gomesPolynomialConstantConnectionCommutant_commutative _
  · rw [gomesPolynomialConnectionCommutant_commutative_iff ⟨A, h⟩]
    constructor
    · rintro h1
      exact h1 ▸ le_rfl
    · intro h1
      exact Nat.le_antisymm h1 (gomesNonconstantPolynomialCoefficient_degree_pos ⟨A, h⟩)

/-- Every constant connection has an actual commuting map beyond polynomials in differentiation. -/
theorem gomesPolynomialConstantConnection_nonpolynomial_symmetry (a : ℝ) :
    ∃ E : Module.End ℝ ℝ[X], E ∈ gomesPolynomialConnectionCommutantAlgebra (C a) ∧
      ∀ P : ℝ[X], E ≠ (Polynomial.aeval (Polynomial.derivative : Module.End ℝ ℝ[X])) P := by
  obtain ⟨E, hE, hP⟩ := gomesPolynomialDerivative_nonpolynomial_symmetry ℝ
  refine ⟨E, ?_, hP⟩
  rw [gomesPolynomialConstantConnection_commutant_algebra]
  exact (gomesPolynomialDerivativeCommutant_mem_iff ℝ E).mpr hE

end GaloisForLFunctions.HTGeometry

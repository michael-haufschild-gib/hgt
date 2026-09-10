import GaloisForLFunctions.HTGeometry.GomesPolynomialConnectionCokernel

/-!
# Complete algebraic index of every real polynomial connection

The cokernel degree law extends to all polynomial coefficients, including constants.
Its kernel has dimension one precisely for the zero coefficient. Together these give
an exact algebraic index and a shift-stable obstruction count even when the algebraic
spectrum is the entire real line.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- Every polynomial connection has a finite-dimensional cokernel, including the constant sector. -/
instance gomesPolynomialConnectionCokernel_finite_all (A : ℝ[X]) :
    Module.Finite ℝ (GomesPolynomialConnectionCokernel A) := by
  by_cases ha : A.derivative = 0
  · have hs : LinearMap.range (gomesPolynomialFirstOrderLinearMap A) = ⊤ :=
      LinearMap.range_eq_top.mpr ((gomesPolynomialFirstOrderOperator_surjective_iff A).mpr ha)
    unfold GomesPolynomialConnectionCokernel
    rw [hs]
    infer_instance
  · exact gomesPolynomialConnectionCokernel_finite ⟨A, ha⟩

/-- For every coefficient, the cokernel dimension is exactly its natural polynomial degree. -/
theorem gomesPolynomialConnectionCokernel_finrank_all (A : ℝ[X]) :
    Module.finrank ℝ (GomesPolynomialConnectionCokernel A) = A.natDegree := by
  by_cases ha : A.derivative = 0
  · have hs : LinearMap.range (gomesPolynomialFirstOrderLinearMap A) = ⊤ :=
      LinearMap.range_eq_top.mpr ((gomesPolynomialFirstOrderOperator_surjective_iff A).mpr ha)
    unfold GomesPolynomialConnectionCokernel
    rw [hs, derivative_eq_zero.mp ha]
    exact Module.finrank_zero_of_subsingleton
  · exact gomesPolynomialConnectionCokernel_finrank ⟨A, ha⟩

/-- Adding any constant to the coefficient preserves the exact missing-output count. -/
theorem gomesPolynomialConnectionCokernel_constant_shift_finrank (A : ℝ[X]) (r : ℝ) :
    Module.finrank ℝ (GomesPolynomialConnectionCokernel (A + C r)) = A.natDegree := by
  rw [gomesPolynomialConnectionCokernel_finrank_all, natDegree_add_C]

/-- Every real spectral shift has precisely the same finite cokernel dimension. -/
theorem gomesPolynomialConnectionCokernel_spectral_shift_finrank (A : ℝ[X]) (r : ℝ) :
    Module.finrank ℝ (ℝ[X] ⧸ LinearMap.range
      (algebraMap ℝ (Module.End ℝ ℝ[X]) r - gomesPolynomialFirstOrderLinearMap A)) = A.natDegree := by
  rw [gomesPolynomialFirstOrderLinearMap_spectral_shift, LinearMap.range_neg]
  exact gomesPolynomialConnectionCokernel_constant_shift_finrank A r

/-- Pure differentiation has exactly the degree-below-one polynomials as its kernel. -/
theorem gomesPolynomialFirstOrderLinearMap_zero_ker :
    LinearMap.ker (gomesPolynomialFirstOrderLinearMap 0) = degreeLT ℝ 1 := by
  ext B
  change gomesPolynomialFirstOrderOperator 0 B = 0 ↔ _
  simp only [gomesPolynomialFirstOrderOperator, zero_mul, sub_zero, derivative_eq_zero]
  by_cases hb : B = 0
  · simp [hb]
  · rw [mem_degreeLT, ← natDegree_lt_iff_degree_lt hb, Nat.lt_one_iff]

/-- The kernel dimension is one exactly for zero coefficient and otherwise vanishes. -/
theorem gomesPolynomialFirstOrderLinearMap_kernel_finrank (A : ℝ[X]) :
    Module.finrank ℝ (LinearMap.ker (gomesPolynomialFirstOrderLinearMap A)) =
      if A = 0 then 1 else 0 := by
  by_cases ha : A = 0
  · rw [if_pos ha, ha, gomesPolynomialFirstOrderLinearMap_zero_ker,
      (degreeLTEquiv ℝ 1).finrank_eq, Module.finrank_fin_fun]
  · rw [if_neg ha, LinearMap.ker_eq_bot.mpr
      ((gomesPolynomialFirstOrderOperator_injective_iff A).mpr ha)]
    exact Module.finrank_zero_of_subsingleton

/-- Every polynomial connection also has finite-dimensional kernel. -/
instance gomesPolynomialFirstOrderLinearMap_kernel_finite (A : ℝ[X]) :
    Module.Finite ℝ (LinearMap.ker (gomesPolynomialFirstOrderLinearMap A)) := by
  by_cases ha : A = 0
  · rw [ha, gomesPolynomialFirstOrderLinearMap_zero_ker]
    infer_instance
  · rw [LinearMap.ker_eq_bot.mpr ((gomesPolynomialFirstOrderOperator_injective_iff A).mpr ha)]
    infer_instance

/-- The algebraic index counts kernel freedom minus missing polynomial outputs. -/
def gomesPolynomialConnectionIndex (A : ℝ[X]) : ℤ :=
  (Module.finrank ℝ (LinearMap.ker (gomesPolynomialFirstOrderLinearMap A)) : ℤ) -
    (Module.finrank ℝ (GomesPolynomialConnectionCokernel A) : ℤ)

/-- The full index classification has only the differentiation exception to negative degree. -/
theorem gomesPolynomialConnectionIndex_exact (A : ℝ[X]) :
    gomesPolynomialConnectionIndex A = if A = 0 then 1 else -(A.natDegree : ℤ) := by
  unfold gomesPolynomialConnectionIndex
  rw [gomesPolynomialFirstOrderLinearMap_kernel_finrank, gomesPolynomialConnectionCokernel_finrank_all]
  by_cases ha : A = 0
  · simp [ha]
  · simp [ha]

/-- A nonconstant coefficient has strictly negative algebraic index. -/
theorem gomesPolynomialConnectionIndex_negative (A : GomesNonconstantPolynomialCoefficient) :
    gomesPolynomialConnectionIndex A.val < 0 := by
  have ha : A.val ≠ 0 := by
    intro h
    exact A.property (by rw [h, derivative_zero])
  rw [gomesPolynomialConnectionIndex_exact, if_neg ha, neg_lt_zero]
  exact_mod_cast gomesNonconstantPolynomialCoefficient_degree_pos A

/-- Scalar shifts preserve the algebraic index throughout the nonconstant sector. -/
theorem gomesPolynomialConnectionIndex_constant_shift
    (A : GomesNonconstantPolynomialCoefficient) (r : ℝ) :
    gomesPolynomialConnectionIndex (A.val + C r) = gomesPolynomialConnectionIndex A.val := by
  have ha : A.val ≠ 0 := by
    intro h
    exact A.property (by rw [h, derivative_zero])
  have hs : A.val + C r ≠ 0 := by
    intro h
    have hd := congrArg Polynomial.derivative h
    apply A.property
    simpa only [derivative_add, derivative_C, add_zero, derivative_zero] using hd
  rw [gomesPolynomialConnectionIndex_exact, gomesPolynomialConnectionIndex_exact,
    if_neg hs, if_neg ha, natDegree_add_C]

end GaloisForLFunctions.HTGeometry

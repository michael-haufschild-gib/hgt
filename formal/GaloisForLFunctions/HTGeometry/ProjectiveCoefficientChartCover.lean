import GaloisForLFunctions.HTGeometry.ProjectiveAffineChartFullIncidenceDimension

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

noncomputable section

def projectiveChartHomogenize
    {I : Type} [DecidableEq I] (j : I)
    (x : projectiveChartVar j → ℂ) (i : I) : ℂ :=
  if h : i = j then 1 else x ⟨i, h⟩

def projectiveChartDehomogenize
    {I : Type} (c : I → ℂ) (j : I) : projectiveChartVar j → ℂ :=
  fun i => c i.1 / c j

@[simp] theorem projectiveChartHomogenize_self
    {I : Type} [DecidableEq I] (j : I) (x : projectiveChartVar j → ℂ) :
    projectiveChartHomogenize j x j = 1 := by
  simp [projectiveChartHomogenize]

theorem projectiveChart_reconstruct
    {I : Type} [DecidableEq I] (c : I → ℂ) (j : I) (hj : c j ≠ 0) (i : I) :
    c i = c j * projectiveChartHomogenize j (projectiveChartDehomogenize c j) i := by
  by_cases h : i = j
  · subst i
    simp
  · simp only [projectiveChartHomogenize, projectiveChartDehomogenize, h, dite_false]
    field_simp

/-- The standard affine projective charts cover every nonzero coefficient vector. -/
theorem exists_projectiveChart_reconstruction
    {I : Type} [DecidableEq I] (c : I → ℂ) (hc : c ≠ 0) :
    ∃ j, ∃ x : projectiveChartVar j → ℂ, ∃ scale : ℂ, scale ≠ 0 ∧
      ∀ i, c i = scale * projectiveChartHomogenize j x i := by
  have hex : ∃ j, c j ≠ 0 := by
    by_contra h
    apply hc
    funext i
    exact not_ne_iff.mp (fun hi => h ⟨i, hi⟩)
  obtain ⟨j, hj⟩ := hex
  exact ⟨j, projectiveChartDehomogenize c j, c j, hj,
    projectiveChart_reconstruct c j hj⟩

theorem projectiveChartCoefficient_eval
    {I : Type} [DecidableEq I] (j : I)
    (x : projectiveChartVar j → ℂ) (i : I) :
    MvPolynomial.eval x (projectiveChartCoefficient j i) =
      projectiveChartHomogenize j x i := by
  by_cases h : i = j
  · subst i
    simp
  · simp [projectiveChartCoefficient, projectiveChartHomogenize, h]

/-- Evaluating the universal coefficient chart gives the literal dehomogenized bounded row
coefficient used in the incidence equations. -/
theorem rowCoefficientPolynomialOf_projectiveChart_eval
    {row κ : Type} [Fintype κ] [DecidableEq κ]
    (q : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (x : projectiveChartVar j → ℂ) (b : row) (a : κ) :
    MvPolynomial.eval x
        (rowCoefficientPolynomialOf q z (projectiveChartCoefficient j) b a) =
      ∑ d : Fin (q + 1), z b ^ (d : ℕ) *
        projectiveChartHomogenize j x (a, d) := by
  classical
  rw [rowCoefficientPolynomialOf, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp [projectiveChartCoefficient_eval]

end
end GaloisForLFunctions.HTGeometry

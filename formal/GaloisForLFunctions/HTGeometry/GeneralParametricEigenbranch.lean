/-
# Analytic eigenbranches at a unitarily diagonalisable simple point

The parametric eigenbranch engine is stated at a *diagonal* base point.  A Hermitian matrix with
simple spectrum is unitarily diagonal, and the characteristic relation is invariant under unitary
conjugation, so the engine applies at any such base point after conjugating the family -- and the
branches it returns are branches of the original family, not of the conjugated one.

That removes the last restriction on the parameter space: over any complex Banach parameter space,
an analytic matrix family with simple spectrum at a point has analytic eigenvalue branches there,
hence analytic canonical eigenvectors, hence endpoint visibility is an open condition.

Main results:
* `analyticAt_matrix_of_entries` — entrywise analyticity assembles.
* `matrixCharpolyRelation_unitary_conj` — the characteristic relation is conjugation invariant.
* `exists_analyticBranch_of_unitaryDiagonal` — **analytic eigenvalue branches at a simple point**.
* `analyticAt_generalAdjugateColumn` — the canonical eigenvectors are analytic there.
-/
import GaloisForLFunctions.HTGeometry.ParametricSpectralBranch
import GaloisForLFunctions.HTGeometry.LocalExtensionChartProbeContinuity

open Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {P ι : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Entrywise analyticity assembles into analyticity of a matrix-valued family. -/
theorem analyticAt_matrix_of_entries {H : P → Matrix ι ι ℂ} {p₀ : P}
    (h : ∀ i j, AnalyticAt ℂ (fun p => H p i j) p₀) : AnalyticAt ℂ H p₀ := by
  refine AnalyticAt.pi fun i => ?_
  exact AnalyticAt.pi fun j => h i j

omit [DecidableEq ι] in
/-- Every entry of an analytic matrix family is analytic. -/
theorem analyticAt_matrix_entry {H : P → Matrix ι ι ℂ} {p₀ : P}
    (hH : AnalyticAt ℂ H p₀) (i j : ι) : AnalyticAt ℂ (fun p => H p i j) p₀ := by
  have hentry : AnalyticAt ℂ (fun N : Matrix ι ι ℂ => N i j) (H p₀) := by
    let row : Matrix ι ι ℂ →L[ℂ] (ι → ℂ) := ContinuousLinearMap.proj (R := ℂ) i
    let col : (ι → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj (R := ℂ) j
    exact (col.comp row).analyticAt _
  exact hentry.fun_comp_of_eq hH rfl

/-- **The characteristic relation is invariant under unitary conjugation.** -/
theorem matrixCharpolyRelation_unitary_conj {U M : Matrix ι ι ℂ} (hU1 : Uᴴ * U = 1) (w : ℂ) :
    matrixCharpolyRelation (Uᴴ * M * U, w) = matrixCharpolyRelation (M, w) := by
  have hscal : Uᴴ * (Matrix.scalar ι w) * U = Matrix.scalar ι w := by
    have hsc : (Matrix.scalar ι w : Matrix ι ι ℂ) = w • (1 : Matrix ι ι ℂ) := by
      rw [Matrix.scalar_apply]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    rw [hsc, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU1]
  have hconj : Matrix.scalar ι w - Uᴴ * M * U = Uᴴ * (Matrix.scalar ι w - M) * U := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hscal]
  have hdet : Uᴴ.det * U.det = 1 := by
    rw [← Matrix.det_mul, hU1, Matrix.det_one]
  show (Matrix.scalar ι w - Uᴴ * M * U).det = (Matrix.scalar ι w - M).det
  rw [hconj, Matrix.det_mul, Matrix.det_mul]
  calc Uᴴ.det * (Matrix.scalar ι w - M).det * U.det
      = (Uᴴ.det * U.det) * (Matrix.scalar ι w - M).det := by ring
    _ = (Matrix.scalar ι w - M).det := by rw [hdet, one_mul]

/-- **Analytic eigenvalue branches at a unitarily diagonalisable simple point.** -/
theorem exists_analyticBranch_of_unitaryDiagonal {H : P → Matrix ι ι ℂ} {p₀ : P}
    (hH : AnalyticAt ℂ H p₀) {U : Matrix ι ι ℂ} (hU1 : Uᴴ * U = 1)
    (energy : ι → ℂ) (hinj : Function.Injective energy)
    (hbase : Uᴴ * H p₀ * U = Matrix.diagonal energy) (x : ι) :
    ∃ branch : P → ℂ, AnalyticAt ℂ branch p₀ ∧ branch p₀ = energy x ∧
      ∀ᶠ p in 𝓝 p₀, matrixCharpolyRelation (H p, branch p) = 0 := by
  have hconjAnalytic : AnalyticAt ℂ (fun p => Uᴴ * H p * U) p₀ := by
    refine analyticAt_matrix_of_entries fun i j => ?_
    have hentry : ∀ k l : ι, AnalyticAt ℂ (fun p => H p k l) p₀ :=
      fun k l => analyticAt_matrix_entry hH k l
    have hsum : AnalyticAt ℂ
        (fun p => ∑ k, ∑ l, Uᴴ i k * H p k l * U l j) p₀ := by
      refine Finset.analyticAt_fun_sum _ fun k _ => ?_
      refine Finset.analyticAt_fun_sum _ fun l _ => ?_
      exact (analyticAt_const.mul (hentry k l)).mul analyticAt_const
    have hfun : (fun p => (Uᴴ * H p * U) i j) = fun p => ∑ k, ∑ l, Uᴴ i k * H p k l * U l j := by
      funext p
      rw [Matrix.mul_apply]
      have hrow : ∀ l : ι, (Uᴴ * H p) i l * U l j = ∑ k, Uᴴ i k * H p k l * U l j := by
        intro l
        rw [Matrix.mul_apply, Finset.sum_mul]
      rw [Finset.sum_congr rfl fun l _ => hrow l, Finset.sum_comm]
    rw [hfun]
    exact hsum
  obtain ⟨branch, hban, hb0, hbroot⟩ :=
    analyticMatrixFamily_eigenvalueBranch hconjAnalytic energy hinj hbase x
  refine ⟨branch, hban, hb0, ?_⟩
  filter_upwards [hbroot] with p hp
  rwa [matrixCharpolyRelation_unitary_conj hU1] at hp

/-- **The canonical eigenvectors are analytic at a simple point.** -/
theorem analyticAt_generalAdjugateColumn {H : P → Matrix ι ι ℂ} {branch : P → ℂ} {p₀ : P}
    (hH : AnalyticAt ℂ H p₀) (hbranch : AnalyticAt ℂ branch p₀) (x i : ι) :
    AnalyticAt ℂ (fun p => (Matrix.scalar ι (branch p) - H p).adjugate i x) p₀ := by
  refine analyticAt_matrix_adjugate_apply_finiteParameter (M := fun p => Matrix.scalar ι (branch p) - H p) ?_ i x
  intro k l
  have hent : AnalyticAt ℂ (fun p => H p k l) p₀ := analyticAt_matrix_entry hH k l
  have hfun : (fun p => (Matrix.scalar ι (branch p) - H p) k l)
      = fun p => (if k = l then branch p else 0) - H p k l := by
    funext p
    rw [Matrix.sub_apply, Matrix.scalar_apply]
    by_cases hkl : k = l
    · subst hkl
      rw [Matrix.diagonal_apply_eq, if_pos rfl]
    · rw [Matrix.diagonal_apply_ne _ hkl, if_neg hkl]
  rw [hfun]
  by_cases hkl : k = l
  · subst hkl
    have hif : (fun p => (if k = k then branch p else 0) - H p k k)
        = fun p => branch p - H p k k := by
      funext p
      rw [if_pos rfl]
    rw [hif]
    exact hbranch.sub hent
  · simp only [if_neg hkl]
    exact analyticAt_const.sub hent

end

end GaloisForLFunctions.HTGeometry

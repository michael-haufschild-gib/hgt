import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Instances.Matrix

/-!
# Closed topology of rectangular differential-evaluation rank defects

The full-translation argument uses rectangular evaluation matrices: rows are evaluation bases,
while columns are coefficient-degree/monomial labels.  This module identifies loss of column rank
with vanishing of the Gram determinant `det (Aᴴ * A)`.  The rank-defect locus is therefore closed.

The second half instantiates this topology on the manuscript's expanded differential-monomial
evaluation matrix.  It supplies the literal closed bad set needed by compact-configuration Baire
assembly; no square submatrix is selected and no coefficient vector is enumerated.
-/

namespace GaloisForLFunctions.HTGeometry

open ComplexOrder Matrix

noncomputable section

/-- Rectangular complex matrices which lose column rank, represented by their Gram determinant. -/
def rectangularRankDefect
    {row col : Type*} [Fintype row] [Fintype col] [DecidableEq col] :
    Set (Matrix row col ℂ) :=
  {A | (Aᴴ * A).det = 0}

/-- The Gram-determinant definition is exactly failure of injectivity of the rectangular
matrix's column map. -/
theorem mem_rectangularRankDefect_iff_not_injective
    {row col : Type*} [Fintype row] [Fintype col] [DecidableEq col]
    (A : Matrix row col ℂ) :
    A ∈ rectangularRankDefect ↔ ¬ Function.Injective A.mulVec := by
  have hker := Matrix.ker_mulVecLin_conjTranspose_mul_self A
  have hinj : Function.Injective (Aᴴ * A).mulVec ↔ Function.Injective A.mulVec := by
    change Function.Injective (Aᴴ * A).mulVecLin ↔ Function.Injective A.mulVecLin
    rw [← LinearMap.ker_eq_bot, ← LinearMap.ker_eq_bot, hker]
  rw [rectangularRankDefect, Set.mem_setOf_eq, ← hinj]
  rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  simp

/-- Rectangular column-rank loss is a closed condition. -/
theorem rectangularRankDefect_isClosed
    {row col : Type*} [Fintype row] [Fintype col] [DecidableEq col] :
    IsClosed (rectangularRankDefect : Set (Matrix row col ℂ)) := by
  apply isClosed_singleton.preimage
  exact (continuous_id.matrix_conjTranspose.matrix_mul continuous_id).matrix_det

/-- The expanded evaluation matrix of polynomial coefficient degree at most `q` and a finite
differential-monomial support.  The packet variables of different rows are kept in disjoint
blocks. -/
noncomputable def expandedDifferentialEvaluationMatrix
    {row κ : Type*} (q n : ℕ) (z : row → ℂ)
    (exponent : κ → (Fin n →₀ ℕ)) (y : row × Fin n → ℂ) :
    Matrix row (κ × Fin (q + 1)) ℂ :=
  fun b c => z b ^ c.2.1 *
    MvPolynomial.eval (fun k => y (b, k))
      (MvPolynomial.monomial (exponent c.1) 1)

@[simp]
theorem expandedDifferentialEvaluationMatrix_apply
    {row κ : Type*} (q n : ℕ) (z : row → ℂ)
    (exponent : κ → (Fin n →₀ ℕ)) (y : row × Fin n → ℂ)
    (b : row) (a : κ) (d : Fin (q + 1)) :
    expandedDifferentialEvaluationMatrix q n z exponent y b (a, d) =
      z b ^ d.1 * (exponent a).prod (fun k e => y (b, k) ^ e) := by
  simp [expandedDifferentialEvaluationMatrix, MvPolynomial.eval_monomial]

/-- The expanded evaluation matrix depends continuously on its complete finite row-jet packet. -/
theorem continuous_expandedDifferentialEvaluationMatrix
    {row κ : Type*} (q n : ℕ) (z : row → ℂ)
    (exponent : κ → (Fin n →₀ ℕ)) :
    Continuous (expandedDifferentialEvaluationMatrix q n z exponent) := by
  apply continuous_pi
  intro b
  apply continuous_pi
  intro c
  apply continuous_const.mul
  apply (MvPolynomial.monomial (exponent c.1) 1).continuous_eval.comp
  exact continuous_pi fun k => continuous_apply (b, k)

/-- Row-jet packets whose expanded evaluation matrix loses column rank. -/
def expandedDifferentialEvaluationRankDefect
    {row κ : Type*} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (exponent : κ → (Fin n →₀ ℕ)) :
    Set (row × Fin n → ℂ) :=
  expandedDifferentialEvaluationMatrix q n z exponent ⁻¹' rectangularRankDefect

/-- Membership in the expanded defect is literally failure of coefficient-uniform column rank. -/
theorem mem_expandedDifferentialEvaluationRankDefect_iff
    {row κ : Type*} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (exponent : κ → (Fin n →₀ ℕ))
    (y : row × Fin n → ℂ) :
    y ∈ expandedDifferentialEvaluationRankDefect q n z exponent ↔
      ¬ Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent y).mulVec := by
  exact mem_rectangularRankDefect_iff_not_injective _

/-- The manuscript's literal finite expanded rank-defect locus is closed in row-jet packet
space. -/
theorem expandedDifferentialEvaluationRankDefect_isClosed
    {row κ : Type*} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (exponent : κ → (Fin n →₀ ℕ)) :
    IsClosed (expandedDifferentialEvaluationRankDefect q n z exponent) := by
  exact rectangularRankDefect_isClosed.preimage
    (continuous_expandedDifferentialEvaluationMatrix q n z exponent)

/-- Full coefficient-uniform rank is an open condition on the finite row-jet packet. -/
theorem expandedDifferentialEvaluationFullRank_isOpen
    {row κ : Type*} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (exponent : κ → (Fin n →₀ ℕ)) :
    IsOpen (expandedDifferentialEvaluationRankDefect q n z exponent)ᶜ :=
  (expandedDifferentialEvaluationRankDefect_isClosed q n z exponent).isOpen_compl

end

end GaloisForLFunctions.HTGeometry

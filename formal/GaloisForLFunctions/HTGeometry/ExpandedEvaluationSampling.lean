import GaloisForLFunctions.HTGeometry.ExpandedEvaluationVandermonde
import GaloisForLFunctions.HTGeometry.LinearIndependentMinorCertificate

/-!
# The full-rank moment packet is a sampling problem, not an analytic one

The translation-rank genericity laws all carry the same hypothesis: some row packet makes the
expanded differential evaluation matrix have injective `mulVec`.  Stated that way it looks like an
analytic condition on the packet.  It is not.

When the jet values are functions of the node — which is the only case the laws use, the jets being
those of one fixed packet function — the matrix entry at row `b` and column `(a, d)` is the value at
the node `z b` of the fixed function

  `g (a,d) : w ↦ w ^ d * ∏ k, (F k w) ^ (exponent a k)`.

So the matrix is a *sampling matrix* of the finite family `g`, and the question is whether that
family can be sampled to a nonsingular square matrix.  For a linearly independent family it always
can, and the sampled nodes are automatically distinct because a repeated node would repeat a row.

This file proves that reduction.  The independence input is supplied separately: it holds as soon as
the node coordinate and the jets are algebraically independent, and it fails exactly when a nonzero
algebraic relation among them is supported inside the monomial box — see
`ExpandedEvaluationRelationIdeal`.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

/-! ## Columns and `mulVec` -/

/-- **Injectivity of `mulVec` is independence of the columns.** -/
theorem mulVec_injective_of_linearIndependent_col {m N K : Type*} [Field K] [Fintype N]
    [DecidableEq N] (M : Matrix m N K)
    (h : LinearIndependent K (fun j : N => fun i : m => M i j)) :
    Function.Injective M.mulVec := by
  intro u v huv
  have hcomb : ∑ j, (u j - v j) • (fun i : m => M i j) = 0 := by
    funext i
    have h1 := congrFun huv i
    simp only [Matrix.mulVec, dotProduct] at h1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hsplit : ∑ j, ((u j - v j) * M i j)
        = (∑ j, M i j * u j) - (∑ j, M i j * v j) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsplit, h1, sub_self]
  have hall := (Fintype.linearIndependent_iff.mp h) (fun j => u j - v j) hcomb
  funext j
  exact sub_eq_zero.mp (hall j)

/-- A nonsingular square matrix has injective `mulVec`. -/
theorem mulVec_injective_of_det_ne_zero {N K : Type*} [Field K] [Fintype N] [DecidableEq N]
    {M : Matrix N N K} (h : M.det ≠ 0) : Function.Injective M.mulVec :=
  Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr h))

/-! ## The expanded monomial family -/

/-- The fixed function whose sampling the expanded evaluation matrix is: a power of the node times a
monomial in the jets at that node. -/
noncomputable def expandedMonomialFamily {κ : Type*} {n : ℕ} (F : Fin n → ℂ → ℂ)
    (exponent : κ → (Fin n →₀ ℕ)) (q : ℕ) : κ × Fin (q + 1) → ℂ → ℂ :=
  fun c w => w ^ (c.2 : ℕ) *
    MvPolynomial.eval (fun k => F k w) (MvPolynomial.monomial (exponent c.1) 1)

/-- **The evaluation matrix at a node packet is the sampling matrix of the family.** -/
theorem expandedDifferentialEvaluationMatrix_eq_coordinateMinor {κ : Type*} {q n : ℕ}
    (F : Fin n → ℂ → ℂ) (exponent : κ → (Fin n →₀ ℕ))
    (φ : κ × Fin (q + 1) → ℂ) :
    expandedDifferentialEvaluationMatrix q n φ exponent (fun p => F p.2 (φ p.1)) =
      coordinateMinor (expandedMonomialFamily F exponent q) φ := by
  ext b c
  rw [expandedDifferentialEvaluationMatrix, coordinateMinor_apply, expandedMonomialFamily]

/-! ## The reduction -/

/-- **Sampling theorem.**  A linearly independent expanded monomial family can be sampled to a
nonsingular evaluation matrix, so the full-rank hypothesis of the genericity laws is met by some
node packet. -/
theorem exists_node_packet_expandedEvaluation_det_ne_zero {κ : Type*} [Fintype κ]
    [DecidableEq κ] {q n : ℕ} (F : Fin n → ℂ → ℂ) (exponent : κ → (Fin n →₀ ℕ))
    (h : LinearIndependent ℂ (expandedMonomialFamily F exponent q)) :
    ∃ z : κ × Fin (q + 1) → ℂ,
      (expandedDifferentialEvaluationMatrix q n z exponent (fun p => F p.2 (z p.1))).det ≠ 0 := by
  classical
  obtain ⟨φ, hφ⟩ := exists_coordinateMinor_det_ne_zero (expandedMonomialFamily F exponent q) h
  refine ⟨φ, ?_⟩
  rw [expandedDifferentialEvaluationMatrix_eq_coordinateMinor]
  exact hφ

/-- **The sampled nodes are automatically distinct**: a repeated node would repeat a row, and a
matrix with two equal rows is singular. -/
theorem injective_of_expandedEvaluation_det_ne_zero {κ : Type*} [Fintype κ] [DecidableEq κ]
    {q n : ℕ} {F : Fin n → ℂ → ℂ} {exponent : κ → (Fin n →₀ ℕ)} {z : κ × Fin (q + 1) → ℂ}
    (h : (expandedDifferentialEvaluationMatrix q n z exponent (fun p => F p.2 (z p.1))).det ≠ 0) :
    Function.Injective z := by
  intro a b hab
  by_contra hne
  refine h (Matrix.det_zero_of_row_eq hne ?_)
  funext c
  simp [expandedDifferentialEvaluationMatrix, hab]

/-- **The full-rank hypothesis, produced.**  A linearly independent expanded monomial family yields
an injective node packet whose evaluation matrix has injective `mulVec`. -/
theorem exists_injective_node_packet_mulVec_injective {κ : Type*} [Fintype κ] [DecidableEq κ]
    {q n : ℕ} (F : Fin n → ℂ → ℂ) (exponent : κ → (Fin n →₀ ℕ))
    (h : LinearIndependent ℂ (expandedMonomialFamily F exponent q)) :
    ∃ z : κ × Fin (q + 1) → ℂ, Function.Injective z ∧
      Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent (fun p => F p.2 (z p.1))).mulVec := by
  obtain ⟨z, hz⟩ := exists_node_packet_expandedEvaluation_det_ne_zero F exponent h
  exact ⟨z, injective_of_expandedEvaluation_det_ne_zero hz, mulVec_injective_of_det_ne_zero hz⟩

end GaloisForLFunctions.HTGeometry

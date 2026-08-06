import GaloisForLFunctions.RHTower.DivisorReesDaggerIdentification
import GaloisForLFunctions.RHTower.WindingXiCircle

/-!
# Assembling the graded symbols over a finite set of divisor points

The graded Rees symbol lives at one divisor point.  Transporting it to a boundary graph means
carrying one copy over each vertex, which is the block-diagonal sum of the local symbols.

Mathlib has no positive-semidefiniteness lemma for block diagonals, so it is proved here: the
quadratic form of a block diagonal is the sum of the blockwise quadratic forms.  The assembled
symbol is then again an idempotent positive form, and its trace counts the vertices.  So the
four-unit budget reads, at the level of the graded symbol, as a bound of four on the number of
divisor points a single boundary unit can carry.
-/

open scoped BigOperators Matrix

open GaloisForLFunctions

namespace RHTower

noncomputable section

/-! ### Block diagonals of positive forms -/

variable {m o : Type*} [Fintype m] [DecidableEq m] [Fintype o] [DecidableEq o]

omit [DecidableEq m] in
/-- **A nonnegative multiple of a positive form is positive.**  Mathlib has no such lemma. -/
theorem posSemidef_smul {A : Matrix m m ℝ} (hA : A.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    (c • A).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hA.1]
    simp
  · have hform : (star x) ⬝ᵥ ((c • A) *ᵥ x) = c * ((star x) ⬝ᵥ (A *ᵥ x)) := by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [hform]
    exact mul_nonneg hc (hA.dotProduct_mulVec_nonneg x)

omit [DecidableEq m] in
/-- The quadratic form of a block diagonal is the sum of the blockwise quadratic forms. -/
theorem dotProduct_mulVec_blockDiagonal (M : o → Matrix m m ℝ) (x : m × o → ℝ) :
    (star x) ⬝ᵥ (Matrix.blockDiagonal M *ᵥ x)
      = ∑ k : o, (star fun i => x (i, k)) ⬝ᵥ (M k *ᵥ fun i => x (i, k)) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.blockDiagonal_apply, star_trivial,
    Fintype.sum_prod_type, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact Finset.sum_comm

omit [DecidableEq m] in
/-- **A block diagonal of positive forms is positive.**  Mathlib has no such lemma; it follows from
the blockwise decomposition of the quadratic form. -/
theorem posSemidef_blockDiagonal {M : o → Matrix m m ℝ} (hM : ∀ k, (M k).PosSemidef) :
    (Matrix.blockDiagonal M).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · rw [Matrix.IsHermitian, Matrix.blockDiagonal_conjTranspose]
    exact congrArg Matrix.blockDiagonal (funext fun k => (hM k).1)
  · rw [dotProduct_mulVec_blockDiagonal]
    exact Finset.sum_nonneg fun k _ => (hM k).dotProduct_mulVec_nonneg _

omit [DecidableEq m] in
/-- The trace of a block diagonal is the sum of the blockwise traces. -/
theorem trace_blockDiagonal (M : o → Matrix m m ℝ) :
    Matrix.trace (Matrix.blockDiagonal M) = ∑ k : o, Matrix.trace (M k) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.blockDiagonal_apply, Fintype.sum_prod_type,
    if_true]
  exact Finset.sum_comm

/-! ### The assembled boundary symbol -/

/-- The graded symbols of a family of spectral points, assembled over the vertices of a boundary
graph. -/
def xiGradedBoundarySymbol {V : Type*} [Fintype V] [DecidableEq V] (rho : V → ℂ) :
    Matrix (Fin 2 × V) (Fin 2 × V) ℝ :=
  Matrix.blockDiagonal fun w => gradedDivisorProjection (analyticOrderAt xi (rho w)).toNat

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The assembled boundary symbol is positive.** -/
theorem xiGradedBoundarySymbol_posSemidef (rho : V → ℂ) :
    (xiGradedBoundarySymbol rho).PosSemidef :=
  posSemidef_blockDiagonal fun w => by
    rw [gradedDivisorProjection_eq _ (one_ne_zero)]
    exact posSemidef_smul (gradedDivisorReesGram_posSemidef _ one_ne_zero)
      (inv_nonneg.mpr (gradedDivisorEnergy_pos _).le)

/-- **The assembled boundary symbol is again idempotent.**  Blockwise idempotence assembles. -/
theorem xiGradedBoundarySymbol_idempotent (rho : V → ℂ) :
    xiGradedBoundarySymbol rho * xiGradedBoundarySymbol rho = xiGradedBoundarySymbol rho := by
  rw [xiGradedBoundarySymbol, ← Matrix.blockDiagonal_mul]
  exact congrArg Matrix.blockDiagonal (funext fun w => gradedDivisorProjection_idempotent _)

/-- **The assembled trace counts the vertices.**  Each divisor point contributes exactly one unit,
whatever its multiplicity. -/
theorem trace_xiGradedBoundarySymbol (rho : V → ℂ) :
    Matrix.trace (xiGradedBoundarySymbol rho) = (Fintype.card V : ℝ) := by
  rw [xiGradedBoundarySymbol, trace_blockDiagonal]
  simp [trace_gradedDivisorProjection]

/-- **The four-unit budget is a four-vertex budget.**  At the level of the graded symbol, the
boundary relative trace stays inside four units exactly when the boundary graph carries at most
four divisor points. -/
theorem trace_xiGradedBoundarySymbol_le_four_iff (rho : V → ℂ) :
    Matrix.trace (xiGradedBoundarySymbol rho) ≤ 4 ↔ Fintype.card V ≤ 4 := by
  rw [trace_xiGradedBoundarySymbol]
  exact_mod_cast Nat.cast_le (α := ℝ)

/-- **The assembled boundary symbol is dagger-invariant.**  Reflecting every vertex across the
critical line leaves the whole assembled symbol unchanged, because it leaves each block unchanged. -/
theorem xiGradedBoundarySymbol_reflection (rho : V → ℂ) :
    xiGradedBoundarySymbol (fun w => burnolCoPoissonConormalReflection (rho w))
      = xiGradedBoundarySymbol rho :=
  congrArg Matrix.blockDiagonal
    (funext fun w => congrArg gradedDivisorProjection
      (xi_multiplicity_burnolCoPoissonConormalReflection (rho w)))

/-- The assembled trace is unchanged by the reflected dagger. -/
theorem trace_xiGradedBoundarySymbol_reflection (rho : V → ℂ) :
    Matrix.trace (xiGradedBoundarySymbol fun w => burnolCoPoissonConormalReflection (rho w))
      = Matrix.trace (xiGradedBoundarySymbol rho) := by
  rw [xiGradedBoundarySymbol_reflection]

/-! ### Only finitely many boundary points are nontrivial -/

/-- Off the divisor the graded symbol is the multiplicity-zero projection. -/
theorem xiGradedSymbol_multiplicity_eq_zero {rho : ℂ} (h : xi rho ≠ 0) :
    (analyticOrderAt xi rho).toNat = 0 := by
  rw [(xi_analyticOnNhd_univ rho (Set.mem_univ rho)).analyticOrderAt_eq_zero.mpr h]
  rfl

/-- **A compact piece of the boundary carries only finitely many nontrivial vertices.**  The Xi
zeros are isolated, so the graded symbol is the trivial multiplicity-zero projection at all but
finitely many points of any closed ball.  This is what makes the finite boundary-graph assembly
applicable to an actual compact piece of the boundary. -/
theorem finite_nontrivial_xiGradedMultiplicity (c : ℂ) (R : ℝ) :
    {rho ∈ Metric.closedBall c R | (analyticOrderAt xi rho).toNat ≠ 0}.Finite := by
  refine (xi_zeros_closedBall_finite c R).subset ?_
  rintro rho ⟨hmem, hord⟩
  refine ⟨hmem, ?_⟩
  by_contra hne
  exact hord (xiGradedSymbol_multiplicity_eq_zero hne)

/-- Off the divisor the graded symbol is the outer square of `(1, 0)`. -/
theorem xiGradedSymbol_eq_trivial {rho : ℂ} (h : xi rho ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    xiGradedSymbol rho t = Matrix.vecMulVec ![1, 0] ![1, 0] := by
  rw [xiGradedSymbol_eq_vecMulVec rho ht, xiGradedSymbol_multiplicity_eq_zero h]
  norm_num

/-- **A compact boundary region carries a finite-graph datum.**  Outside a finite set the graded
symbol field is the single trivial projection, so on any closed ball the field is a finitely
supported perturbation of a constant.  This is what lets the boundary-graph theorems apply to an
actual region of the continuation rather than to a hand-picked finite vertex set. -/
theorem exists_finite_xiGradedSymbol_nontrivial (c : ℂ) (R : ℝ) :
    ∃ S : Set ℂ, S.Finite ∧ ∀ rho ∈ Metric.closedBall c R, rho ∉ S →
      ∀ t : ℝ, t ≠ 0 → xiGradedSymbol rho t = Matrix.vecMulVec ![1, 0] ![1, 0] := by
  refine ⟨{z ∈ Metric.closedBall c R | xi z = 0}, xi_zeros_closedBall_finite c R, ?_⟩
  intro rho hmem hnot t ht
  refine xiGradedSymbol_eq_trivial (fun hz => hnot ⟨hmem, hz⟩) ht

end

end RHTower

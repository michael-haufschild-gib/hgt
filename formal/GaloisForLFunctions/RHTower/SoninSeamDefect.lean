/-
The `{σ_p}`-boundary defect on a torsion seam presentation: the commutator model always collapses.

A pinned `{σ_p}`-boundary defect on a torsion seam presentation `A` (with `det A = Xᵐ`) is a matrix
`Δ_p` whose Fitting boundary class `tr(adj(A)·Δ_p) mod Xᵐ` decides — via `FittingSeamBoundary` —
whether it is fake (a coboundary through the presentation) or a genuine divisor obstruction. The
natural first model of a `{σ_p}`-defect is the **commutator** `Δ_p = σ·A − A·σ`: the failure of the
`{σ_p}` action `σ` to preserve the divisor presentation `A`.

This module proves that model is **always fake**: `tr(adj(A)·(σA − Aσ)) = 0` for every `A` and every
`σ` (`fittingBoundaryTrace_commutatorDefect`), because the adjugate identities
`adj(A)·A = A·adj(A) = det(A)·1` and trace cyclicity make the two cyclic traces cancel. So no
`{σ_p}`-non-commutation with the presentation produces a live pinned defect
(`fittingBoundaryClass_commutatorDefect`); a nonzero boundary class is never a commutator
(`nonzero_fittingBoundaryClass_not_commutator`).

Non-fake defects nonetheless exist (`exists_nonfake_fittingBoundary`: a one-slot presentation with
`det A = X²`, defect `1`, boundary class `1 ≠ 0`), so the commutator vanishing is a genuine
restriction, not vacuity — and every such live defect is, by the theorem, a non-commutator.

Interpretation. At a pinned strip point the `{σ_p}` action is multiplication by the unit `p^(−s)`
(nonvanishing there — the unit-triviality of the prime side), i.e. a scalar, which commutes with the
presentation; its commutator defect is therefore `0` and fake. This is the presentation-level shadow
of the disjoint-carrier/freeness collapse. A live `{σ_p}`-boundary defect must be a **non-commutator
cross-boundary cochain** — the `{σ_p}` action pushing mass across a cutoff `|x| = λ` — which is not a
pinned-germ commutator. That object is non-local (trace-level / adelic), not a pinned germ.
-/
import GaloisForLFunctions.RHTower.FittingSeamBoundary

noncomputable section

namespace RHTower

open Matrix Polynomial

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The commutator `{σ_p}`-defect: the failure of the action `σ` to preserve the seam presentation
`A`. -/
def commutatorDefect (A σ : Matrix n n (Polynomial R)) : Matrix n n (Polynomial R) := σ * A - A * σ

/-- **The commutator defect always has zero Fitting boundary trace.**  For every presentation `A`
and every action `σ`, `tr(adj(A)·(σA − Aσ)) = 0`: the adjugate identities `adj(A)·A = A·adj(A) =
det(A)·1` and trace cyclicity make the two cyclic traces `det(A)·tr(σ)` cancel. -/
theorem fittingBoundaryTrace_commutatorDefect (A σ : Matrix n n (Polynomial R)) :
    fittingBoundaryTrace A (commutatorDefect A σ) = 0 := by
  rw [fittingBoundaryTrace, commutatorDefect, Matrix.mul_sub, Matrix.trace_sub]
  have h1 : (A.adjugate * (σ * A)).trace = (A.det • σ).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm (A.adjugate * σ) A, ← Matrix.mul_assoc,
      Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul]
  have h2 : (A.adjugate * (A * σ)).trace = (A.det • σ).trace := by
    rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  rw [h1, h2, sub_self]

/-- **The commutator `{σ_p}`-defect is fake at every level.**  Its Fitting boundary class in
`R[X]/(Xᵐ)` is zero, so no failure of `σ` to commute with the presentation yields a live pinned
divisor obstruction. -/
theorem fittingBoundaryClass_commutatorDefect (m : ℕ) (A σ : Matrix n n (Polynomial R)) :
    fittingBoundaryClass m A (commutatorDefect A σ) = 0 := by
  rw [fittingBoundaryClass, fittingBoundaryTrace_commutatorDefect, jetClass]
  exact map_zero _

/-- **A live boundary defect is never a commutator.**  If the Fitting boundary class of `Δ` is
nonzero, `Δ` is not `σ·A − A·σ` for any `σ`: a genuine pinned divisor obstruction must be a
non-commutator cochain. -/
theorem nonzero_fittingBoundaryClass_not_commutator (m : ℕ) {A Δ : Matrix n n (Polynomial R)}
    (hclass : fittingBoundaryClass m A Δ ≠ 0) :
    ¬ ∃ σ : Matrix n n (Polynomial R), Δ = commutatorDefect A σ := by
  rintro ⟨σ, rfl⟩
  exact hclass (fittingBoundaryClass_commutatorDefect m A σ)

/-- **Non-fake boundary defects exist**, so the commutator vanishing is a genuine restriction and not
vacuity.  A one-slot presentation with `det A = X²` carries the defect `Δ = 1` with boundary class
`1 ≠ 0` — a non-fake defect, necessarily a non-commutator by the theorem above. -/
theorem exists_nonfake_fittingBoundary :
    ∃ (A Δ : Matrix (Fin 1) (Fin 1) (Polynomial ℚ)),
      A.det = (X : Polynomial ℚ) ^ 2 ∧ fittingBoundaryClass 2 A Δ ≠ 0 := by
  refine ⟨Matrix.of ![![(X : Polynomial ℚ) ^ 2]], 1, ?_, ?_⟩
  · rw [Matrix.det_fin_one]; rfl
  · have hadj : (Matrix.of ![![(X : Polynomial ℚ) ^ 2]]).adjugate = 1 := Matrix.adjugate_fin_one _
    rw [fittingBoundaryClass, fittingBoundaryTrace, hadj, Matrix.one_mul, Matrix.trace_fin_one,
      Matrix.one_apply_eq]
    intro hzero
    rw [jetClass, Ideal.Quotient.eq_zero_iff_mem, jetIdeal, Ideal.mem_span_singleton] at hzero
    have hu : IsUnit ((X : Polynomial ℚ) ^ 2) := isUnit_of_dvd_one hzero
    rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_pow, Polynomial.degree_X] at hu
    simp at hu

end RHTower

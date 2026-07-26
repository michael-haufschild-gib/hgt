import GaloisForLFunctions.RHTower.QuasiHermitianIsTheOpenSubroute

/-!
# The remaining lane has no obstruction to compute, only a construction to find

Every lane closed in this development was closed by computing a budget, computing a demand, and
comparing them.  This file shows that method cannot apply to the quasi-Hermitian lane, and identifies
what replaces it.

**There is no lower bound on the metric.**  Given any prescribed real spectrum, the diagonal matrix
with those entries is already self-adjoint, so the metric is the identity and its condition number is
one.  No a priori bound on the conditioning can be extracted from the data, because the metric is part
of the construction rather than part of the problem.

**What makes the lane hard is circularity, not an obstruction.**  The diagonal model presupposes that
the spectrum is real.  A proof must build the operator from the arithmetic *without* assuming what it
is meant to conclude, and an equivalence between "the spectrum is real" and "a model exists" proves
nothing on its own.

**Where the construction lives.**  The quasi-Hermitian data is a de Branges structure: an
Hermite–Biehler function `E` with `|E*(z)| < |E(z)|` on the upper half-plane, for which
`A = (E + E*)/2` is real entire with only real zeros.  The hypothesis is that the completed zeta
function is such an `A`.

> **The obstruction-computing method that closed every other lane cannot close this one: one side of
> the comparison is free.  What remains is not an estimate to sharpen but an operator to build, and
> the building must not presuppose the reality it is to establish.**

This file formalizes the self-adjointness of a real diagonal model and the resulting absence of any
lower bound on the conditioning.  The circularity is a statement about proofs, not a theorem, and is
recorded here in prose rather than as a triviality.
-/

open Matrix

noncomputable section

namespace RHTower

section DiagonalModel

variable {n : ℕ}

/-- **A real diagonal matrix is self-adjoint.**  Its conjugate transpose is itself. -/
theorem diagonal_real_selfAdjoint (d : Fin n → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ)))ᴴ = Matrix.diagonal (fun i => (d i : ℂ)) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq]
  · simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply_ne, h, Ne.symm h]

/-- **Hence the identity metric works.**  With `Q = 1` the metric relation holds for the diagonal
model, so its condition number is one. -/
theorem diagonal_metric_identity (d : Fin n → ℝ) :
    (1 : Matrix (Fin n) (Fin n) ℂ) * 1 * Matrix.diagonal (fun i => (d i : ℂ))
      = (Matrix.diagonal (fun i => (d i : ℂ)))ᴴ * ((1 : Matrix (Fin n) (Fin n) ℂ) * 1) := by
  rw [diagonal_real_selfAdjoint]
  simp

/-- **So no lower bound on the conditioning exists.**  For every prescribed real spectrum there is a
model whose metric is the identity. -/
theorem no_conditioning_lower_bound (d : Fin n → ℝ) :
    ∃ Q : Matrix (Fin n) (Fin n) ℂ, Qᴴ = Q ∧ Q = 1 ∧
      Q * Q * Matrix.diagonal (fun i => (d i : ℂ))
        = (Matrix.diagonal (fun i => (d i : ℂ)))ᴴ * (Q * Q) :=
  ⟨1, by simp, rfl, diagonal_metric_identity d⟩

end DiagonalModel

end RHTower

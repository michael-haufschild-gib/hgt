import GaloisForLFunctions.HTGeometry.ReflectionPositiveHankel
import Mathlib.Analysis.Matrix.Order

/-!
# Positive matrix trace powers as reflection-positive moments

A positive semidefinite finite matrix supplies a canonical Hankel moment sequence: the
`k`-th moment is the real trace of its `(k + 1)`-st power.  The matrix seminorm induced by the
positive matrix makes the powers `A^k` into a reflected Gram orbit, so every real polynomial
square has nonnegative moment functional.

This is finite-dimensional positive-source infrastructure.  It does not assert that any
particular analytic moment sequence has such a realization.
-/

open scoped BigOperators ComplexOrder

namespace HTGeometry

open Matrix

noncomputable section

/-- The shifted trace-power moments of a finite complex matrix.  The shift makes the induced
matrix inner product read `m (i + j)` on the power orbit. -/
def matrixTracePowerMoment {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (k : ℕ) : ℝ :=
  (A ^ (k + 1)).trace.re

/-- For a positive semidefinite matrix, its induced matrix inner product makes the power orbit
Hankel with entries given by the shifted trace-power moments. -/
theorem trace_matrixPower_eq_matrixTracePowerMoment
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) (i j : ℕ) :
    ((A ^ j) * A * (A ^ i)ᴴ).trace =
      (matrixTracePowerMoment A (i + j) : ℂ) := by
  rw [(hA.isHermitian.pow i).eq]
  have hpow : (A ^ (i + j + 1)).PosSemidef := by
    simpa [add_assoc, add_comm, add_left_comm] using hA.pow (i + j + 1)
  have hreal : (A ^ (i + j + 1)).trace.im = 0 :=
    (Complex.nonneg_iff.mp hpow.trace_nonneg).2.symm
  have hmul : A ^ j * A * A ^ i = A ^ (i + j + 1) := by
    rw [← pow_succ, ← pow_add]
    congr 1
    omega
  rw [matrixTracePowerMoment, hmul]
  apply Complex.ext
  · simp
  · simpa using hreal

/-- **Finite positive trace-power theorem.**  Every positive semidefinite matrix produces a
reflection-positive Hankel moment functional. -/
theorem matrixTracePowerMoment_nonnegative
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) (p : Polynomial ℝ) :
    0 ≤ momentFunctional (matrixTracePowerMoment A) (p ^ 2) := by
  letI : SeminormedAddCommGroup (Matrix n n ℂ) :=
    A.toMatrixSeminormedAddCommGroup hA
  letI : InnerProductSpace ℂ (Matrix n n ℂ) :=
    A.toMatrixInnerProductSpace hA
  apply momentFunctional_pow_two_nonneg_of_complexReflectionPositiveGram
    (matrixTracePowerMoment A) (fun k => A ^ k)
  exact trace_matrixPower_eq_matrixTracePowerMoment hA

end

end HTGeometry

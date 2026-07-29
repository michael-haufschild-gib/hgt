import GaloisForLFunctions.HTGeometry.SourceQuadraticTransferSelector
import Mathlib.Analysis.Matrix.Order

/-!
# Positivity cannot be odd; reciprocal squares are the positive survivor

Let a self-adjoint source polarity act by conjugation. A positive-semidefinite matrix in its odd
sector must vanish: congruence preserves positivity, while oddness identifies that congruence with
the negative matrix. Thus a nonzero source-changing transfer cannot itself be a metric,
probability, or positive observable.

The strongest positive survivor is two-sided squaring. For any rectangular transfer `D`,
`Dᴴ * D` and `D * Dᴴ` are positive semidefinite and have equal rank. If a square transfer is odd
under a self-adjoint involution, both reciprocal squares are even under the same involution.

These statements are standard positive matrix and graded-operator algebra. They do not identify
the two squares with quantum or gravitational dynamics, derive a physical transfer, or prove a
theory of everything.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open scoped ComplexOrder Matrix MatrixOrder

set_option maxRecDepth 4096

/--
**Odd-positivity obstruction.** A positive-semidefinite law cannot nontrivially change a
self-adjoint source polarity.
-/
theorem posSemidef_sourceOdd_eq_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (A Q : Matrix n n ℂ)
    (hA : Aᴴ = A)
    (hQ : Q.PosSemidef)
    (hodd : A * Q * A = -Q) :
    Q = 0 := by
  have hneg : (-Q).PosSemidef := by
    have hcongr := hQ.conjTranspose_mul_mul_same A
    rw [hA, hodd] at hcongr
    exact hcongr
  exact le_antisymm (neg_nonneg.mp hneg.nonneg) hQ.nonneg

/-- Positive law seen on the domain side of a reciprocal transfer. -/
def reciprocalDomainSquare
    {m n : Type*} [Fintype m] [Fintype n]
    (D : Matrix m n ℂ) : Matrix n n ℂ :=
  Dᴴ * D

/-- Positive law seen on the codomain side of a reciprocal transfer. -/
def reciprocalCodomainSquare
    {m n : Type*} [Fintype m] [Fintype n]
    (D : Matrix m n ℂ) : Matrix m m ℂ :=
  D * Dᴴ

/-- The domain-side reciprocal square is positive semidefinite. -/
theorem reciprocalDomainSquare_posSemidef
    {m n : Type*} [Fintype m] [Fintype n]
    (D : Matrix m n ℂ) :
    (reciprocalDomainSquare D).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self D

/-- The codomain-side reciprocal square is positive semidefinite. -/
theorem reciprocalCodomainSquare_posSemidef
    {m n : Type*} [Fintype m] [Fintype n]
    (D : Matrix m n ℂ) :
    (reciprocalCodomainSquare D).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose D

/--
The two positive reciprocal squares have the same rank, even when source and target dimensions
differ.
-/
theorem reciprocalSquare_rank_eq
    {m n : Type*} [Fintype m] [Fintype n]
    (D : Matrix m n ℂ) :
    (reciprocalDomainSquare D).rank =
      (reciprocalCodomainSquare D).rank := by
  rw [reciprocalDomainSquare, reciprocalCodomainSquare,
    Matrix.rank_conjTranspose_mul_self, Matrix.rank_self_mul_conjTranspose]

/--
Squaring converts source-odd transfer into source-even positive laws on both sides.
-/
theorem sourceOdd_reciprocalSquares_even
    {n : Type*} [Fintype n] [DecidableEq n]
    (A D : Matrix n n ℂ)
    (hA2 : A * A = 1)
    (hAH : Aᴴ = A)
    (hodd : A * D * A = -D) :
    A * reciprocalDomainSquare D * A = reciprocalDomainSquare D ∧
      A * reciprocalCodomainSquare D * A = reciprocalCodomainSquare D := by
  have hoddH := congrArg Matrix.conjTranspose hodd
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_neg, hAH] at hoddH
  rw [← Matrix.mul_assoc] at hoddH
  have hanti : A * D = -D * A := by
    calc
      A * D = A * D * (A * A) := by rw [hA2, mul_one]
      _ = (A * D * A) * A := by simp only [Matrix.mul_assoc]
      _ = (-D) * A := by rw [hodd]
      _ = -D * A := by rfl
  have hantiH : A * Dᴴ = -Dᴴ * A := by
    calc
      A * Dᴴ = A * Dᴴ * (A * A) := by rw [hA2, mul_one]
      _ = (A * Dᴴ * A) * A := by simp only [Matrix.mul_assoc]
      _ = (-Dᴴ) * A := by rw [hoddH]
      _ = -Dᴴ * A := by rfl
  have hantiRight : D * A = -A * D := by
    calc
      D * A = (A * A) * (D * A) := by rw [hA2, one_mul]
      _ = A * (A * D * A) := by simp only [Matrix.mul_assoc]
      _ = A * (-D) := by rw [hodd]
      _ = -A * D := by simp
  have hantiHRight : Dᴴ * A = -A * Dᴴ := by
    calc
      Dᴴ * A = (A * A) * (Dᴴ * A) := by rw [hA2, one_mul]
      _ = A * (A * Dᴴ * A) := by simp only [Matrix.mul_assoc]
      _ = A * (-Dᴴ) := by rw [hoddH]
      _ = -A * Dᴴ := by simp
  constructor
  · simp only [reciprocalDomainSquare]
    calc
      A * (Dᴴ * D) * A = (A * Dᴴ) * (D * A) := by
        simp only [Matrix.mul_assoc]
      _ = (-Dᴴ * A) * (-A * D) := by rw [hantiH, hantiRight]
      _ = Dᴴ * (A * A) * D := by noncomm_ring
      _ = Dᴴ * D := by rw [hA2, Matrix.mul_one]
  · simp only [reciprocalCodomainSquare]
    calc
      A * (D * Dᴴ) * A = (A * D) * (Dᴴ * A) := by
        simp only [Matrix.mul_assoc]
      _ = (-D * A) * (-A * Dᴴ) := by rw [hanti, hantiHRight]
      _ = D * (A * A) * Dᴴ := by noncomm_ring
      _ = D * Dᴴ := by rw [hA2, Matrix.mul_one]

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.Quantum.PositiveConstraintSupport

/-!
# Positive block reduction by conserved charges

Pinching a matrix by its charge sectors preserves positivity and trace. Every
charge-invariant objective has exactly the same trace pairing before and after
pinching. Thus off-sector Gram coefficients can be discarded without altering
the feasible positive cone or any already block-diagonal objective.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.Quantum

open Matrix
open scoped ComplexOrder

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

/-- Orthogonal coordinate projection onto one charge sector. -/
def chargeProjection (charge : ι → κ) (q : κ) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => if charge i = q then 1 else 0

theorem chargeProjection_isHermitian (charge : ι → κ) (q : κ) :
    (chargeProjection charge q).IsHermitian := by
  ext i j
  simp [chargeProjection, Matrix.conjTranspose_apply, Matrix.diagonal_apply, eq_comm]

/-- Delete all matrix entries connecting different conserved charges. -/
def chargePinch (charge : ι → κ) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∑ q ∈ Finset.univ.image charge,
    chargeProjection charge q * A * chargeProjection charge q

theorem chargePinch_apply (charge : ι → κ) (A : Matrix ι ι ℂ) (i j : ι) :
    chargePinch charge A i j = if charge i = charge j then A i j else 0 := by
  have hi : charge i ∈ Finset.univ.image charge := Finset.mem_image_of_mem _ (Finset.mem_univ i)
  simp [chargePinch, chargeProjection, Matrix.sum_apply, Matrix.diagonal_mul,
    Matrix.mul_diagonal, hi, eq_comm]

/-- Block reduction preserves the positive cone. -/
theorem chargePinch_posSemidef (charge : ι → κ) {A : Matrix ι ι ℂ}
    (hA : A.PosSemidef) : (chargePinch charge A).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro q _
  simpa only [(chargeProjection_isHermitian charge q).eq] using
    hA.mul_mul_conjTranspose_same (chargeProjection charge q)

theorem chargePinch_idempotent (charge : ι → κ) (A : Matrix ι ι ℂ) :
    chargePinch charge (chargePinch charge A) = chargePinch charge A := by
  ext i j
  simp only [chargePinch_apply]
  split <;> rfl

theorem trace_chargePinch (charge : ι → κ) (A : Matrix ι ι ℂ) :
    (chargePinch charge A).trace = A.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, chargePinch_apply, ite_true]

/-- The fixed matrices are exactly those with no coefficients between different charges. -/
theorem chargePinch_eq_self_iff (charge : ι → κ) (A : Matrix ι ι ℂ) :
    chargePinch charge A = A ↔ ∀ i j, charge i ≠ charge j → A i j = 0 := by
  constructor
  · intro h i j hij
    have := congrFun (congrFun h i) j
    simpa only [chargePinch_apply, if_neg hij] using this.symm
  · intro h
    ext i j
    rw [chargePinch_apply]
    split
    · rfl
    · exact (h i j ‹_›).symm

/-- Pinching is self-adjoint for the trace pairing. -/
theorem trace_chargePinch_mul (charge : ι → κ) (A B : Matrix ι ι ℂ) :
    (chargePinch charge A * B).trace = (A * chargePinch charge B).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, chargePinch_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : charge i = charge j
  · simp only [h, ite_true]
  · simp only [if_neg h, if_neg (Ne.symm h), zero_mul, mul_zero]

/-- Every already reduced objective has the same value on the pinched feasible matrix. -/
theorem trace_chargePinch_mul_chargePinch (charge : ι → κ) (A B : Matrix ι ι ℂ) :
    (chargePinch charge A * chargePinch charge B).trace =
      (chargePinch charge A * B).trace := by
  rw [← trace_chargePinch_mul, chargePinch_idempotent]

end GaloisForLFunctions.HTGeometry.Quantum

import Mathlib

/-!
# Noncommutative reciprocal fusion and retained Jordan history

Quadratic congruence gives the exact noncommutative lift of reciprocal direct/reflected formation.
Its flat restriction is the scalar d'Alembert work law.  Away from commuting flats, the missing
coordinate is an explicit commutator history; in a rational algebra it is a sum of double
commutators.  Congruence nonassociativity has an exact ordered associator, while matrix trace
annihilates the Jordan-history sector.

This is the unconditional algebraic core of ULF-RFTM-2.  It contains no RH premise.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

section RingFusion

variable {A : Type*} [Ring A]

/-- Reciprocal work of an invertible formation coordinate. -/
def reciprocalUnitWork (u : Aˣ) : A := (u : A) + (↑u⁻¹ : A) - 2

/-- Quadratic direct formation. -/
def reciprocalDirectFusion (r q : Aˣ) : Aˣ := r * q * r

/-- Quadratic reflected formation. -/
def reciprocalReflectedFusion (r q : Aˣ) : Aˣ := r * q⁻¹ * r

/-- Sum of direct and inverse quadratic congruence actions. -/
def reciprocalCongruenceAction (r : Aˣ) (z : A) : A :=
  (r : A) * z * r + (↑r⁻¹ : A) * z * r⁻¹

/-- One-sided commutator-history correction to radial fusion. -/
def reciprocalCommutatorHistory (r : Aˣ) (z : A) : A :=
  (r : A) * (z * r - r * z) + (↑r⁻¹ : A) * (z * r⁻¹ - r⁻¹ * z)

/-- **Exact noncommutative reciprocal fusion.** -/
theorem reciprocalUnitWork_fusion (r q : Aˣ) :
    reciprocalUnitWork (reciprocalDirectFusion r q) +
      reciprocalUnitWork (reciprocalReflectedFusion r q) =
        reciprocalCongruenceAction r (reciprocalUnitWork q) +
          2 * reciprocalUnitWork (r * r) := by
  simp [reciprocalUnitWork, reciprocalDirectFusion, reciprocalReflectedFusion,
    reciprocalCongruenceAction]
  noncomm_ring

/-- Congruence splits into a radial term and a one-sided commutator history. -/
theorem reciprocalCongruenceAction_commutator_decomposition (r : Aˣ) (z : A) :
    reciprocalCongruenceAction r z =
      (((r * r : Aˣ) : A) + (↑(r * r)⁻¹ : A)) * z +
        reciprocalCommutatorHistory r z := by
  simp [reciprocalCongruenceAction, reciprocalCommutatorHistory]
  noncomm_ring

/-- The history correction vanishes on every commuting flat. -/
theorem reciprocalCommutatorHistory_eq_zero_of_commute (r : Aˣ) (z : A)
    (h : (r : A) * z = z * r) :
    reciprocalCommutatorHistory r z = 0 := by
  have hinv : (↑r⁻¹ : A) * z = z * r⁻¹ := by
    calc
      (↑r⁻¹ : A) * z = (↑r⁻¹ : A) * z * 1 := by simp
      _ = (↑r⁻¹ : A) * z * ((r : A) * r⁻¹) := by simp
      _ = (↑r⁻¹ : A) * (z * r) * r⁻¹ := by noncomm_ring
      _ = (↑r⁻¹ : A) * ((r : A) * z) * r⁻¹ := by rw [h]
      _ = ((↑r⁻¹ : A) * r) * z * r⁻¹ := by noncomm_ring
      _ = z * r⁻¹ := by simp
  simp [reciprocalCommutatorHistory, h, hinv]

/-- On a commuting flat, noncommutative fusion collapses to the scalar reciprocal fusion law. -/
theorem reciprocalUnitWork_radial_fusion (r q : Aˣ)
    (h : (r : A) * reciprocalUnitWork q = reciprocalUnitWork q * r) :
    reciprocalUnitWork (reciprocalDirectFusion r q) +
      reciprocalUnitWork (reciprocalReflectedFusion r q) =
        reciprocalUnitWork (r * r) * reciprocalUnitWork q +
          2 * reciprocalUnitWork (r * r) + 2 * reciprocalUnitWork q := by
  rw [reciprocalUnitWork_fusion, reciprocalCongruenceAction_commutator_decomposition,
    reciprocalCommutatorHistory_eq_zero_of_commute r (reciprocalUnitWork q) h]
  simp [reciprocalUnitWork]
  noncomm_ring

/-- Quadratic congruence as the ordered formation operation. -/
def reciprocalCongruenceFusion (r q : Aˣ) : Aˣ := r * q * r

/-- **Exact associator.**  Ordered history is the commutator of successive half-formations. -/
theorem reciprocalCongruenceFusion_associator (s r q : Aˣ) :
    (reciprocalCongruenceFusion s (reciprocalCongruenceFusion r q) : A) -
        reciprocalCongruenceFusion (s * r) q =
      (s : A) * r * q * ((r : A) * s - s * r) := by
  simp [reciprocalCongruenceFusion]
  noncomm_ring

end RingFusion

section JordanFusion

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- Jordan symmetrization in a rational algebra. -/
def reciprocalJordanProduct (a b : A) : A := (1 / 2 : ℚ) • (a * b + b * a)

/-- Additive commutator. -/
def reciprocalAdditiveCommutator (a b : A) : A := a * b - b * a

/-- Negative half double commutator created by one congruence leg. -/
def reciprocalDoubleCommutatorHistory (r z : A) : A :=
  -(1 / 2 : ℚ) • reciprocalAdditiveCommutator r (reciprocalAdditiveCommutator r z)

/-- Direct plus reciprocal double-commutator history. -/
def reciprocalJordanHistory (r : Aˣ) (z : A) : A :=
  reciprocalDoubleCommutatorHistory (r : A) z +
    reciprocalDoubleCommutatorHistory (↑r⁻¹ : A) z

theorem reciprocalJordanProduct_add_left (a b z : A) :
    reciprocalJordanProduct (a + b) z =
      reciprocalJordanProduct a z + reciprocalJordanProduct b z := by
  simp [reciprocalJordanProduct, add_mul, mul_add, smul_add]
  abel

theorem reciprocalJordanProduct_two_left (z : A) :
    reciprocalJordanProduct (2 : A) z = 2 * z := by
  have hc : algebraMap ℚ A (2 : ℚ)⁻¹ + algebraMap ℚ A (2 : ℚ)⁻¹ = 1 := by
    rw [← map_add]
    norm_num
  simp [reciprocalJordanProduct, Algebra.smul_def]
  noncomm_ring [hc]
  calc
    (4 : ℤ) • (algebraMap ℚ A (2 : ℚ)⁻¹ * z) =
        ((2 : ℤ) + 2) • (algebraMap ℚ A (2 : ℚ)⁻¹ * z) := by norm_num
    _ = (2 : ℤ) • (algebraMap ℚ A (2 : ℚ)⁻¹ * z) +
        (2 : ℤ) • (algebraMap ℚ A (2 : ℚ)⁻¹ * z) := by rw [add_zsmul]
    _ = (algebraMap ℚ A (2 : ℚ)⁻¹ * z + algebraMap ℚ A (2 : ℚ)⁻¹ * z) +
        (algebraMap ℚ A (2 : ℚ)⁻¹ * z + algebraMap ℚ A (2 : ℚ)⁻¹ * z) := by
          rw [two_zsmul]
    _ = z + z := by
      calc
        _ = (algebraMap ℚ A (2 : ℚ)⁻¹ + algebraMap ℚ A (2 : ℚ)⁻¹) * z +
            (algebraMap ℚ A (2 : ℚ)⁻¹ + algebraMap ℚ A (2 : ℚ)⁻¹) * z := by
              rw [add_mul]
        _ = z + z := by rw [hc, one_mul]
    _ = (2 : ℤ) • z := by rw [two_zsmul]

/-- One congruence leg is Jordan-radial part plus double-commutator history. -/
theorem reciprocal_congruence_eq_jordan_add_history (r z : A) :
    r * z * r = reciprocalJordanProduct (r * r) z +
      reciprocalDoubleCommutatorHistory r z := by
  have hc : algebraMap ℚ A (2 : ℚ)⁻¹ + algebraMap ℚ A (2 : ℚ)⁻¹ = 1 := by
    rw [← map_add]
    norm_num
  simp [reciprocalJordanProduct, reciprocalDoubleCommutatorHistory,
    reciprocalAdditiveCommutator, Algebra.smul_def]
  noncomm_ring [hc]
  rw [two_smul, ← add_mul, hc, one_mul]

/-- **Jordan fusion law.**  The noncommutative correction is retained as double-commutator
history. -/
theorem reciprocalUnitWork_jordan_fusion (r q : Aˣ) :
    reciprocalUnitWork (reciprocalDirectFusion r q) +
      reciprocalUnitWork (reciprocalReflectedFusion r q) =
        reciprocalJordanProduct (reciprocalUnitWork (r * r)) (reciprocalUnitWork q) +
          2 * reciprocalUnitWork q + 2 * reciprocalUnitWork (r * r) +
            reciprocalJordanHistory r (reciprocalUnitWork q) := by
  rw [reciprocalUnitWork_fusion]
  unfold reciprocalCongruenceAction
  rw [reciprocal_congruence_eq_jordan_add_history (r : A),
    reciprocal_congruence_eq_jordan_add_history (↑r⁻¹ : A)]
  let z : A := reciprocalUnitWork q
  have hw : reciprocalUnitWork (r * r) + 2 =
      (((r * r : Aˣ) : A) + (↑(r * r)⁻¹ : A)) := by
    simp [reciprocalUnitWork]
  have hJ : reciprocalJordanProduct ((r : A) * r) z +
      reciprocalJordanProduct ((↑r⁻¹ : A) * r⁻¹) z =
        reciprocalJordanProduct (reciprocalUnitWork (r * r)) z + 2 * z := by
    have hinv : ((r⁻¹ * r⁻¹ : Aˣ) : A) = (↑(r * r)⁻¹ : A) := by simp
    rw [← reciprocalJordanProduct_add_left, ← Units.val_mul, ← Units.val_mul, hinv, ← hw,
      reciprocalJordanProduct_add_left, reciprocalJordanProduct_two_left]
  change reciprocalJordanProduct ((r : A) * r) z +
      reciprocalDoubleCommutatorHistory (r : A) z +
      (reciprocalJordanProduct ((↑r⁻¹ : A) * r⁻¹) z +
        reciprocalDoubleCommutatorHistory (↑r⁻¹ : A) z) +
        2 * reciprocalUnitWork (r * r) =
    reciprocalJordanProduct (reciprocalUnitWork (r * r)) z + 2 * z +
      2 * reciprocalUnitWork (r * r) + reciprocalJordanHistory r z
  rw [reciprocalJordanHistory]
  rw [← hJ]
  abel

end JordanFusion

section MatrixTrace

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Matrix trace annihilates an additive commutator. -/
theorem trace_reciprocalAdditiveCommutator
    (A B : Matrix n n ℚ) :
    Matrix.trace (reciprocalAdditiveCommutator A B) = 0 := by
  rw [reciprocalAdditiveCommutator, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- **Tracial erasure.**  Every rational matrix trace annihilates double-commutator history. -/
theorem trace_reciprocalDoubleCommutatorHistory
    (R Z : Matrix n n ℚ) :
    Matrix.trace (reciprocalDoubleCommutatorHistory R Z) = 0 := by
  rw [reciprocalDoubleCommutatorHistory, Matrix.trace_smul,
    trace_reciprocalAdditiveCommutator]
  simp

/-- Rational two-mode half-formation used by the strict-history witness. -/
def reciprocalHistoryWitnessR : Matrix (Fin 2) (Fin 2) ℚ := !![2, 0; 0, 1]

/-- Inverse half-formation used by the strict-history witness. -/
def reciprocalHistoryWitnessRInv : Matrix (Fin 2) (Fin 2) ℚ := !![1 / 2, 0; 0, 1]

/-- Second positive formation coordinate used by the strict-history witness. -/
def reciprocalHistoryWitnessQ : Matrix (Fin 2) (Fin 2) ℚ := !![2, 1; 1, 2]

/-- Explicit inverse of the second witness formation. -/
def reciprocalHistoryWitnessQInv : Matrix (Fin 2) (Fin 2) ℚ :=
  !![2 / 3, -1 / 3; -1 / 3, 2 / 3]

/-- Positive radial work coordinate used by the strict-history witness. -/
def reciprocalHistoryWitnessZ : Matrix (Fin 2) (Fin 2) ℚ :=
  !![2 / 3, 2 / 3; 2 / 3, 2 / 3]

/-- Quadratic form of the diagonal witness half-formation. -/
def reciprocalHistoryWitnessRForm (x y : ℚ) : ℚ := 2 * x ^ 2 + y ^ 2

/-- Quadratic form of the second witness formation. -/
def reciprocalHistoryWitnessQForm (x y : ℚ) : ℚ :=
  2 * x ^ 2 + 2 * x * y + 2 * y ^ 2

/-- Quadratic form of the witness radial work coordinate. -/
def reciprocalHistoryWitnessZForm (x y : ℚ) : ℚ := (2 / 3) * (x + y) ^ 2

/-- The diagonal witness half-formation is positive definite. -/
theorem reciprocalHistoryWitnessRForm_pos {x y : ℚ} (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < reciprocalHistoryWitnessRForm x y := by
  rw [reciprocalHistoryWitnessRForm]
  rcases hxy with hx | hy
  · have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    exact by nlinarith [sq_nonneg y]
  · have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
    exact by nlinarith [sq_nonneg x]

/-- The second witness formation is positive definite. -/
theorem reciprocalHistoryWitnessQForm_pos {x y : ℚ} (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < reciprocalHistoryWitnessQForm x y := by
  rw [reciprocalHistoryWitnessQForm]
  have hxy2 : 0 < x ^ 2 + y ^ 2 := by
    rcases hxy with hx | hy
    · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg y]
    · nlinarith [sq_nonneg x, sq_pos_of_ne_zero hy]
  nlinarith [sq_nonneg (x + y)]

/-- The witness work coordinate is positive semidefinite. -/
theorem reciprocalHistoryWitnessZForm_nonneg (x y : ℚ) :
    0 ≤ reciprocalHistoryWitnessZForm x y := by
  exact mul_nonneg (by norm_num) (sq_nonneg _)

theorem reciprocalHistoryWitnessR_mul_inv :
    reciprocalHistoryWitnessR * reciprocalHistoryWitnessRInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reciprocalHistoryWitnessR, reciprocalHistoryWitnessRInv,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem reciprocalHistoryWitnessR_inv_mul :
    reciprocalHistoryWitnessRInv * reciprocalHistoryWitnessR = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reciprocalHistoryWitnessR, reciprocalHistoryWitnessRInv,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem reciprocalHistoryWitnessQ_mul_inv :
    reciprocalHistoryWitnessQ * reciprocalHistoryWitnessQInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reciprocalHistoryWitnessQ, reciprocalHistoryWitnessQInv,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem reciprocalHistoryWitnessQ_inv_mul :
    reciprocalHistoryWitnessQInv * reciprocalHistoryWitnessQ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reciprocalHistoryWitnessQ, reciprocalHistoryWitnessQInv,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The witness half-formation as a genuine unit. -/
def reciprocalHistoryWitnessRUnit : (Matrix (Fin 2) (Fin 2) ℚ)ˣ where
  val := reciprocalHistoryWitnessR
  inv := reciprocalHistoryWitnessRInv
  val_inv := reciprocalHistoryWitnessR_mul_inv
  inv_val := reciprocalHistoryWitnessR_inv_mul

/-- The second witness formation as a genuine unit. -/
def reciprocalHistoryWitnessQUnit : (Matrix (Fin 2) (Fin 2) ℚ)ˣ where
  val := reciprocalHistoryWitnessQ
  inv := reciprocalHistoryWitnessQInv
  val_inv := reciprocalHistoryWitnessQ_mul_inv
  inv_val := reciprocalHistoryWitnessQ_inv_mul

/-- The displayed radial coordinate is exactly the reciprocal work of the witness unit. -/
theorem reciprocalUnitWork_historyWitnessQ :
    reciprocalUnitWork reciprocalHistoryWitnessQUnit = reciprocalHistoryWitnessZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reciprocalUnitWork, reciprocalHistoryWitnessQUnit,
      reciprocalHistoryWitnessQ, reciprocalHistoryWitnessQInv, reciprocalHistoryWitnessZ,
      Matrix.ofNat_apply] <;>
    norm_num

/-- The inverse coordinate used in the history formula is the inverse of the witness unit. -/
theorem reciprocalHistoryWitnessRUnit_inv_val :
    ((↑reciprocalHistoryWitnessRUnit⁻¹ : Matrix (Fin 2) (Fin 2) ℚ)) =
      reciprocalHistoryWitnessRInv := rfl

/-- Exact nonzero self-adjoint history hidden from trace. -/
theorem reciprocalHistoryWitness_eq :
    reciprocalDoubleCommutatorHistory reciprocalHistoryWitnessR reciprocalHistoryWitnessZ +
      reciprocalDoubleCommutatorHistory reciprocalHistoryWitnessRInv reciprocalHistoryWitnessZ =
        !![0, -5 / 12; -5 / 12, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reciprocalDoubleCommutatorHistory, reciprocalAdditiveCommutator,
      reciprocalHistoryWitnessR, reciprocalHistoryWitnessRInv, reciprocalHistoryWitnessZ,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The strict history is the Jordan correction of two actual reciprocal formation units. -/
theorem reciprocalJordanHistory_witness_eq :
    reciprocalJordanHistory reciprocalHistoryWitnessRUnit
      (reciprocalUnitWork reciprocalHistoryWitnessQUnit) =
        !![0, -5 / 12; -5 / 12, 0] := by
  rw [reciprocalUnitWork_historyWitnessQ]
  exact reciprocalHistoryWitness_eq

/-- The retained history witness is genuinely nonzero. -/
theorem reciprocalHistoryWitness_ne_zero :
    reciprocalDoubleCommutatorHistory reciprocalHistoryWitnessR reciprocalHistoryWitnessZ +
      reciprocalDoubleCommutatorHistory reciprocalHistoryWitnessRInv reciprocalHistoryWitnessZ ≠
        0 := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 0 1) h
  rw [reciprocalHistoryWitness_eq] at h01
  norm_num at h01

/-- The same nonzero witness has exactly zero trace. -/
theorem trace_reciprocalHistoryWitness :
    Matrix.trace
      (reciprocalDoubleCommutatorHistory reciprocalHistoryWitnessR reciprocalHistoryWitnessZ +
        reciprocalDoubleCommutatorHistory reciprocalHistoryWitnessRInv reciprocalHistoryWitnessZ) =
      0 := by
  rw [Matrix.trace_add, trace_reciprocalDoubleCommutatorHistory,
    trace_reciprocalDoubleCommutatorHistory, zero_add]

end MatrixTrace

end GaloisForLFunctions.HTGeometry

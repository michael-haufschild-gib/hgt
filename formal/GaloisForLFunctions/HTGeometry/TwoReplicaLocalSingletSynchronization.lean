import GaloisForLFunctions.HTGeometry.FiniteQubitPauliBasisLaw
import GaloisForLFunctions.HTGeometry.CoherenceEndReconstruction
import GaloisForLFunctions.HTGeometry.FiniteConstraintGroupAverage
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Two-replica local-singlet synchronization

Exact Pauli reduction for the two-replica edge commutator Casimir. The physical
nine-generator double commutator is intertwined with a four-coordinate operator,
whose invariant eigenvalues are `0, 0, 48, 80` and whose kernel synchronizes
edge swap labels. Preconnected graph rigidity then leaves only global identity
and global swap coefficient modes.
-/

open scoped BigOperators Matrix Kronecker

namespace GaloisForLFunctions.HTGeometry

noncomputable section

abbrev TwoReplicaLocalIndex := Bool × Bool
abbrev TwoReplicaEdgeIndex := TwoReplicaLocalIndex × TwoReplicaLocalIndex
abbrev TwoReplicaEdgeLabel := Bool × Bool
abbrev TwoReplicaEdgeCoeff := TwoReplicaEdgeLabel → ℂ

def twoReplicaPauliLeft (a : Fin 3) :
    Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ :=
  finiteQubitPauli a ⊗ₖ (1 : Matrix Bool Bool ℂ)

def twoReplicaPauliRight (a : Fin 3) :
    Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ :=
  (1 : Matrix Bool Bool ℂ) ⊗ₖ finiteQubitPauli a

def twoReplicaLocalCorrelation :
    Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ :=
  ∑ a : Fin 3, finiteQubitPauli a ⊗ₖ finiteQubitPauli a

def twoReplicaLeftChannel :
    Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ →ₗ[ℂ]
      Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ where
  toFun X := ∑ a : Fin 3, twoReplicaPauliLeft a * X * twoReplicaPauliLeft a
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' z X := by
    simp [Finset.smul_sum]

def twoReplicaRightChannel :
    Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ →ₗ[ℂ]
      Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ where
  toFun X := ∑ a : Fin 3, twoReplicaPauliRight a * X * twoReplicaPauliRight a
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' z X := by
    simp [Finset.smul_sum]

def twoReplicaCrossChannel :
    Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ →ₗ[ℂ]
      Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ where
  toFun X := ∑ a : Fin 3, twoReplicaPauliLeft a * X * twoReplicaPauliRight a
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' z X := by
    simp [Finset.smul_sum]

def twoReplicaReverseCrossChannel :
    Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ →ₗ[ℂ]
      Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ where
  toFun X := ∑ a : Fin 3, twoReplicaPauliRight a * X * twoReplicaPauliLeft a
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' z X := by
    simp [Finset.smul_sum]

theorem finiteQubitPauli_mul_self (a : Fin 3) :
    finiteQubitPauli a * finiteQubitPauli a =
      (1 : Matrix Bool Bool ℂ) := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [finiteQubitPauli, Matrix.mul_apply, Fintype.sum_bool]

@[simp] theorem twoReplicaPauliLeft_mul_self (a : Fin 3) :
    twoReplicaPauliLeft a * twoReplicaPauliLeft a = 1 := by
  rw [twoReplicaPauliLeft, ← Matrix.mul_kronecker_mul,
    finiteQubitPauli_mul_self, Matrix.one_mul, Matrix.one_kronecker_one]

@[simp] theorem twoReplicaPauliRight_mul_self (a : Fin 3) :
    twoReplicaPauliRight a * twoReplicaPauliRight a = 1 := by
  rw [twoReplicaPauliRight, ← Matrix.mul_kronecker_mul,
    finiteQubitPauli_mul_self, Matrix.one_mul, Matrix.one_kronecker_one]

theorem twoReplicaLeftChannel_one :
    twoReplicaLeftChannel (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) =
      (3 : ℂ) • (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) := by
  change (∑ a : Fin 3,
      twoReplicaPauliLeft a * 1 * twoReplicaPauliLeft a) = _
  calc
    (∑ a : Fin 3,
        twoReplicaPauliLeft a * 1 * twoReplicaPauliLeft a) =
        ∑ _a : Fin 3,
          (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Matrix.mul_one, twoReplicaPauliLeft_mul_self]
    _ = (3 : ℂ) • (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) := by
      ext i j
      simp

theorem twoReplicaRightChannel_one :
    twoReplicaRightChannel (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) =
      (3 : ℂ) • (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) := by
  change (∑ a : Fin 3,
      twoReplicaPauliRight a * 1 * twoReplicaPauliRight a) = _
  calc
    (∑ a : Fin 3,
        twoReplicaPauliRight a * 1 * twoReplicaPauliRight a) =
        ∑ _a : Fin 3,
          (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Matrix.mul_one, twoReplicaPauliRight_mul_self]
    _ = (3 : ℂ) • (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) := by
      ext i j
      simp

theorem twoReplicaCrossChannel_one :
    twoReplicaCrossChannel (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) =
      twoReplicaLocalCorrelation := by
  change (∑ a : Fin 3,
      twoReplicaPauliLeft a * 1 * twoReplicaPauliRight a) = _
  rw [twoReplicaLocalCorrelation]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Matrix.mul_one, twoReplicaPauliLeft, twoReplicaPauliRight,
    ← Matrix.mul_kronecker_mul]
  simp

theorem twoReplicaReverseCrossChannel_one :
    twoReplicaReverseCrossChannel (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) =
      twoReplicaLocalCorrelation := by
  change (∑ a : Fin 3,
      twoReplicaPauliRight a * 1 * twoReplicaPauliLeft a) = _
  rw [twoReplicaLocalCorrelation]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Matrix.mul_one, twoReplicaPauliLeft, twoReplicaPauliRight,
    ← Matrix.mul_kronecker_mul]
  simp

def twoReplicaSwap : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ :=
  fun i j => if i.1 = j.2 ∧ i.2 = j.1 then 1 else 0

theorem twoReplicaLocalCorrelation_eq_swap :
    twoReplicaLocalCorrelation = (2 : ℂ) • twoReplicaSwap - 1 := by
  have h21 : (2 : Fin 3) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    norm_num [twoReplicaLocalCorrelation, twoReplicaSwap, finiteQubitPauli,
      Matrix.kronecker_apply, Fin.sum_univ_succ, Matrix.one_apply, h21]

@[simp] theorem twoReplicaSwap_sq :
    twoReplicaSwap * twoReplicaSwap = 1 := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    norm_num [twoReplicaSwap, Matrix.mul_apply, Fintype.sum_prod_type,
      Fintype.sum_bool, Matrix.one_apply]

theorem twoReplicaSwap_mul_right (a : Fin 3) :
    twoReplicaSwap * twoReplicaPauliRight a =
      twoReplicaPauliLeft a * twoReplicaSwap := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases a <;> fin_cases i₁ <;> fin_cases i₂ <;>
    fin_cases j₁ <;> fin_cases j₂ <;>
    norm_num [twoReplicaSwap, twoReplicaPauliLeft, twoReplicaPauliRight,
      finiteQubitPauli, Matrix.mul_apply, Fintype.sum_prod_type,
      Fintype.sum_bool, Matrix.kronecker_apply, Matrix.one_apply]

theorem twoReplicaSwap_mul_left (a : Fin 3) :
    twoReplicaSwap * twoReplicaPauliLeft a =
      twoReplicaPauliRight a * twoReplicaSwap := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases a <;> fin_cases i₁ <;> fin_cases i₂ <;>
    fin_cases j₁ <;> fin_cases j₂ <;>
    norm_num [twoReplicaSwap, twoReplicaPauliLeft, twoReplicaPauliRight,
      finiteQubitPauli, Matrix.mul_apply, Fintype.sum_prod_type,
      Fintype.sum_bool, Matrix.kronecker_apply, Matrix.one_apply]

theorem sum_twoReplicaPauliRight_mul_left :
    (∑ a : Fin 3, twoReplicaPauliRight a * twoReplicaPauliLeft a) =
      twoReplicaLocalCorrelation := by
  rw [twoReplicaLocalCorrelation]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [twoReplicaPauliRight, twoReplicaPauliLeft, ← Matrix.mul_kronecker_mul]
  simp

theorem sum_twoReplicaPauliLeft_mul_right :
    (∑ a : Fin 3, twoReplicaPauliLeft a * twoReplicaPauliRight a) =
      twoReplicaLocalCorrelation := by
  rw [twoReplicaLocalCorrelation]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [twoReplicaPauliRight, twoReplicaPauliLeft, ← Matrix.mul_kronecker_mul]
  simp

theorem twoReplicaSwap_mul_correlation :
    twoReplicaSwap * twoReplicaLocalCorrelation =
      (2 : ℂ) • (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) -
        twoReplicaSwap := by
  rw [twoReplicaLocalCorrelation_eq_swap]
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, twoReplicaSwap_sq]

theorem twoReplicaCorrelation_mul_swap :
    twoReplicaLocalCorrelation * twoReplicaSwap =
      (2 : ℂ) • (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) -
        twoReplicaSwap := by
  rw [twoReplicaLocalCorrelation_eq_swap]
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, twoReplicaSwap_sq]

theorem twoReplicaLocalCorrelation_sq :
    twoReplicaLocalCorrelation * twoReplicaLocalCorrelation =
      (3 : ℂ) • (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) -
        (2 : ℂ) • twoReplicaLocalCorrelation := by
  rw [twoReplicaLocalCorrelation_eq_swap]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, twoReplicaSwap_sq]
  module

theorem twoReplicaLeftChannel_swap :
    twoReplicaLeftChannel twoReplicaSwap =
      twoReplicaSwap * twoReplicaLocalCorrelation := by
  rw [twoReplicaLeftChannel]
  calc
    (∑ a : Fin 3,
        twoReplicaPauliLeft a * twoReplicaSwap * twoReplicaPauliLeft a) =
        ∑ a : Fin 3,
          twoReplicaSwap *
            (twoReplicaPauliRight a * twoReplicaPauliLeft a) := by
      apply Finset.sum_congr rfl
      intro a _ha
      calc
        twoReplicaPauliLeft a * twoReplicaSwap * twoReplicaPauliLeft a =
            (twoReplicaSwap * twoReplicaPauliRight a) *
              twoReplicaPauliLeft a := by
                rw [twoReplicaSwap_mul_right]
        _ = twoReplicaSwap *
            (twoReplicaPauliRight a * twoReplicaPauliLeft a) := by
              rw [Matrix.mul_assoc]
    _ = twoReplicaSwap *
        (∑ a : Fin 3, twoReplicaPauliRight a * twoReplicaPauliLeft a) := by
      rw [Matrix.mul_sum]
    _ = twoReplicaSwap * twoReplicaLocalCorrelation := by
      rw [sum_twoReplicaPauliRight_mul_left]

theorem twoReplicaRightChannel_swap :
    twoReplicaRightChannel twoReplicaSwap =
      twoReplicaSwap * twoReplicaLocalCorrelation := by
  rw [twoReplicaRightChannel]
  calc
    (∑ a : Fin 3,
        twoReplicaPauliRight a * twoReplicaSwap * twoReplicaPauliRight a) =
        ∑ a : Fin 3,
          twoReplicaSwap *
            (twoReplicaPauliLeft a * twoReplicaPauliRight a) := by
      apply Finset.sum_congr rfl
      intro a _ha
      calc
        twoReplicaPauliRight a * twoReplicaSwap * twoReplicaPauliRight a =
            (twoReplicaSwap * twoReplicaPauliLeft a) *
              twoReplicaPauliRight a := by
                rw [twoReplicaSwap_mul_left]
        _ = twoReplicaSwap *
            (twoReplicaPauliLeft a * twoReplicaPauliRight a) := by
              rw [Matrix.mul_assoc]
    _ = twoReplicaSwap *
        (∑ a : Fin 3, twoReplicaPauliLeft a * twoReplicaPauliRight a) := by
      rw [Matrix.mul_sum]
    _ = twoReplicaSwap * twoReplicaLocalCorrelation := by
      rw [sum_twoReplicaPauliLeft_mul_right]

theorem twoReplicaCrossChannel_swap :
    twoReplicaCrossChannel twoReplicaSwap =
      (3 : ℂ) • twoReplicaSwap := by
  rw [twoReplicaCrossChannel]
  calc
    (∑ a : Fin 3,
        twoReplicaPauliLeft a * twoReplicaSwap * twoReplicaPauliRight a) =
        ∑ _a : Fin 3, twoReplicaSwap := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Matrix.mul_assoc, twoReplicaSwap_mul_right, ← Matrix.mul_assoc,
        twoReplicaPauliLeft_mul_self, Matrix.one_mul]
    _ = (3 : ℂ) • twoReplicaSwap := by
      ext i j
      simp

theorem twoReplicaReverseCrossChannel_swap :
    twoReplicaReverseCrossChannel twoReplicaSwap =
      (3 : ℂ) • twoReplicaSwap := by
  rw [twoReplicaReverseCrossChannel]
  calc
    (∑ a : Fin 3,
        twoReplicaPauliRight a * twoReplicaSwap * twoReplicaPauliLeft a) =
        ∑ _a : Fin 3, twoReplicaSwap := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Matrix.mul_assoc, twoReplicaSwap_mul_left, ← Matrix.mul_assoc,
        twoReplicaPauliRight_mul_self, Matrix.one_mul]
    _ = (3 : ℂ) • twoReplicaSwap := by
      ext i j
      simp

theorem twoReplicaLeftChannel_correlation :
    twoReplicaLeftChannel twoReplicaLocalCorrelation =
      -twoReplicaLocalCorrelation := by
  rw [twoReplicaLocalCorrelation_eq_swap, map_sub, map_smul,
    twoReplicaLeftChannel_swap, twoReplicaLeftChannel_one,
    twoReplicaSwap_mul_correlation]
  module

theorem twoReplicaRightChannel_correlation :
    twoReplicaRightChannel twoReplicaLocalCorrelation =
      -twoReplicaLocalCorrelation := by
  rw [twoReplicaLocalCorrelation_eq_swap, map_sub, map_smul,
    twoReplicaRightChannel_swap, twoReplicaRightChannel_one,
    twoReplicaSwap_mul_correlation]
  module

theorem twoReplicaCrossChannel_correlation :
    twoReplicaCrossChannel twoReplicaLocalCorrelation =
      (3 : ℂ) • (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) +
        (2 : ℂ) • twoReplicaLocalCorrelation := by
  rw [twoReplicaLocalCorrelation_eq_swap, map_sub, map_smul,
    twoReplicaCrossChannel_swap, twoReplicaCrossChannel_one,
    twoReplicaLocalCorrelation_eq_swap]
  module

theorem twoReplicaReverseCrossChannel_correlation :
    twoReplicaReverseCrossChannel twoReplicaLocalCorrelation =
      (3 : ℂ) • (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) +
        (2 : ℂ) • twoReplicaLocalCorrelation := by
  rw [twoReplicaLocalCorrelation_eq_swap, map_sub, map_smul,
    twoReplicaReverseCrossChannel_swap, twoReplicaReverseCrossChannel_one,
    twoReplicaLocalCorrelation_eq_swap]
  module

def twoReplicaPauliPair (a : Fin 3) :
    Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ :=
  finiteQubitPauli a ⊗ₖ finiteQubitPauli a

@[simp] theorem twoReplicaPauliLeft_mul_right (a : Fin 3) :
    twoReplicaPauliLeft a * twoReplicaPauliRight a =
      twoReplicaPauliPair a := by
  rw [twoReplicaPauliLeft, twoReplicaPauliRight, twoReplicaPauliPair,
    ← Matrix.mul_kronecker_mul]
  simp

@[simp] theorem twoReplicaPauliRight_mul_left (a : Fin 3) :
    twoReplicaPauliRight a * twoReplicaPauliLeft a =
      twoReplicaPauliPair a := by
  rw [twoReplicaPauliLeft, twoReplicaPauliRight, twoReplicaPauliPair,
    ← Matrix.mul_kronecker_mul]
  simp

theorem twoReplicaLocalCorrelation_eq_sum_pair :
    twoReplicaLocalCorrelation = ∑ a : Fin 3, twoReplicaPauliPair a := by
  rfl

@[simp] theorem twoReplicaKronecker_mul
    (A B C D : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) :
    (A ⊗ₖ B) * (C ⊗ₖ D) = (A * C) ⊗ₖ (B * D) := by
  rw [Matrix.mul_kronecker_mul]

def twoReplicaEdgeCollective (a b : Fin 3) :
    Matrix TwoReplicaEdgeIndex TwoReplicaEdgeIndex ℂ :=
  (twoReplicaPauliLeft a ⊗ₖ twoReplicaPauliLeft b) +
    (twoReplicaPauliRight a ⊗ₖ twoReplicaPauliRight b)

theorem twoReplicaEdgeCollective_sq (a b : Fin 3) :
    twoReplicaEdgeCollective a b * twoReplicaEdgeCollective a b =
      (2 : ℂ) • (1 : Matrix TwoReplicaEdgeIndex TwoReplicaEdgeIndex ℂ) +
        (2 : ℂ) •
          (twoReplicaPauliPair a ⊗ₖ twoReplicaPauliPair b) := by
  rw [twoReplicaEdgeCollective, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_add]
  simp only [twoReplicaKronecker_mul, twoReplicaPauliLeft_mul_self,
    twoReplicaPauliRight_mul_self, twoReplicaPauliLeft_mul_right,
    twoReplicaPauliRight_mul_left, Matrix.one_kronecker_one]
  module

theorem twoReplica_sum_kronecker_sum
    (F G : Fin 3 → Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) :
    ((∑ a : Fin 3, F a) ⊗ₖ (∑ b : Fin 3, G b)) =
      ∑ a : Fin 3, ∑ b : Fin 3, F a ⊗ₖ G b := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [Matrix.kroneckerMap_apply, Matrix.sum_apply,
    Matrix.add_apply, Fin.sum_univ_succ]
  ring

theorem sum_twoReplicaEdgeCollective_sq :
    (∑ a : Fin 3, ∑ b : Fin 3,
      twoReplicaEdgeCollective a b * twoReplicaEdgeCollective a b) =
      (18 : ℂ) • (1 : Matrix TwoReplicaEdgeIndex TwoReplicaEdgeIndex ℂ) +
        (2 : ℂ) •
          (twoReplicaLocalCorrelation ⊗ₖ twoReplicaLocalCorrelation) := by
  simp_rw [twoReplicaEdgeCollective_sq]
  rw [twoReplicaLocalCorrelation_eq_sum_pair,
    twoReplica_sum_kronecker_sum]
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.kroneckerMap_apply, Fin.sum_univ_succ]
  ring

theorem twoReplicaEdgeCollective_sandwich_kronecker
    (a b : Fin 3)
    (X Y : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) :
    twoReplicaEdgeCollective a b * (X ⊗ₖ Y) *
        twoReplicaEdgeCollective a b =
      ((twoReplicaPauliLeft a * X * twoReplicaPauliLeft a) ⊗ₖ
        (twoReplicaPauliLeft b * Y * twoReplicaPauliLeft b)) +
      ((twoReplicaPauliRight a * X * twoReplicaPauliRight a) ⊗ₖ
        (twoReplicaPauliRight b * Y * twoReplicaPauliRight b)) +
      ((twoReplicaPauliLeft a * X * twoReplicaPauliRight a) ⊗ₖ
        (twoReplicaPauliLeft b * Y * twoReplicaPauliRight b)) +
      ((twoReplicaPauliRight a * X * twoReplicaPauliLeft a) ⊗ₖ
        (twoReplicaPauliRight b * Y * twoReplicaPauliLeft b)) := by
  simp only [twoReplicaEdgeCollective, Matrix.add_mul, Matrix.mul_add,
    twoReplicaKronecker_mul]
  module

theorem sum_twoReplicaEdgeCollective_sandwich_kronecker
    (X Y : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) :
    (∑ a : Fin 3, ∑ b : Fin 3,
      twoReplicaEdgeCollective a b * (X ⊗ₖ Y) *
        twoReplicaEdgeCollective a b) =
      (twoReplicaLeftChannel X ⊗ₖ twoReplicaLeftChannel Y) +
      (twoReplicaRightChannel X ⊗ₖ twoReplicaRightChannel Y) +
      (twoReplicaCrossChannel X ⊗ₖ twoReplicaCrossChannel Y) +
      (twoReplicaReverseCrossChannel X ⊗ₖ
        twoReplicaReverseCrossChannel Y) := by
  simp_rw [twoReplicaEdgeCollective_sandwich_kronecker]
  change
    (∑ a : Fin 3, ∑ b : Fin 3,
      (((twoReplicaPauliLeft a * X * twoReplicaPauliLeft a) ⊗ₖ
        (twoReplicaPauliLeft b * Y * twoReplicaPauliLeft b)) +
      ((twoReplicaPauliRight a * X * twoReplicaPauliRight a) ⊗ₖ
        (twoReplicaPauliRight b * Y * twoReplicaPauliRight b)) +
      ((twoReplicaPauliLeft a * X * twoReplicaPauliRight a) ⊗ₖ
        (twoReplicaPauliLeft b * Y * twoReplicaPauliRight b)) +
      ((twoReplicaPauliRight a * X * twoReplicaPauliLeft a) ⊗ₖ
        (twoReplicaPauliRight b * Y * twoReplicaPauliLeft b)))) =
      ((∑ a : Fin 3, twoReplicaPauliLeft a * X * twoReplicaPauliLeft a) ⊗ₖ
        (∑ b : Fin 3, twoReplicaPauliLeft b * Y * twoReplicaPauliLeft b)) +
      ((∑ a : Fin 3, twoReplicaPauliRight a * X * twoReplicaPauliRight a) ⊗ₖ
        (∑ b : Fin 3, twoReplicaPauliRight b * Y * twoReplicaPauliRight b)) +
      ((∑ a : Fin 3, twoReplicaPauliLeft a * X * twoReplicaPauliRight a) ⊗ₖ
        (∑ b : Fin 3, twoReplicaPauliLeft b * Y * twoReplicaPauliRight b)) +
      ((∑ a : Fin 3, twoReplicaPauliRight a * X * twoReplicaPauliLeft a) ⊗ₖ
        (∑ b : Fin 3, twoReplicaPauliRight b * Y * twoReplicaPauliLeft b))
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [Matrix.sum_apply, Matrix.add_apply, Matrix.kroneckerMap_apply,
    Fin.sum_univ_succ]
  ring

def twoReplicaMatrixCommutator
    (G : Matrix TwoReplicaEdgeIndex TwoReplicaEdgeIndex ℂ) :
    Matrix TwoReplicaEdgeIndex TwoReplicaEdgeIndex ℂ →ₗ[ℂ]
      Matrix TwoReplicaEdgeIndex TwoReplicaEdgeIndex ℂ where
  toFun X := G * X - X * G
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.add_mul]
    module
  map_smul' z X := by
    simp [smul_sub]

def twoReplicaEdgeCommutator (a b : Fin 3) :
    Matrix TwoReplicaEdgeIndex TwoReplicaEdgeIndex ℂ →ₗ[ℂ]
      Matrix TwoReplicaEdgeIndex TwoReplicaEdgeIndex ℂ :=
  twoReplicaMatrixCommutator (twoReplicaEdgeCollective a b)

def twoReplicaEdgeCasimir :
    Matrix TwoReplicaEdgeIndex TwoReplicaEdgeIndex ℂ →ₗ[ℂ]
      Matrix TwoReplicaEdgeIndex TwoReplicaEdgeIndex ℂ :=
  ∑ a : Fin 3, ∑ b : Fin 3,
    (twoReplicaEdgeCommutator a b).comp
      (twoReplicaEdgeCommutator a b)

theorem twoReplicaMatrixCommutator_sq
    (G X : Matrix TwoReplicaEdgeIndex TwoReplicaEdgeIndex ℂ) :
    twoReplicaMatrixCommutator G (twoReplicaMatrixCommutator G X) =
      G * G * X + X * G * G - G * X * G - G * X * G := by
  change G * (G * X - X * G) - (G * X - X * G) * G = _
  noncomm_ring

theorem twoReplicaEdgeCasimir_apply
    (X : Matrix TwoReplicaEdgeIndex TwoReplicaEdgeIndex ℂ) :
    twoReplicaEdgeCasimir X =
      ∑ a : Fin 3, ∑ b : Fin 3,
        twoReplicaMatrixCommutator (twoReplicaEdgeCollective a b)
          (twoReplicaMatrixCommutator (twoReplicaEdgeCollective a b) X) := by
  simp [twoReplicaEdgeCasimir, twoReplicaEdgeCommutator]

theorem twoReplicaEdgeCasimir_kronecker
    (X Y : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) :
    twoReplicaEdgeCasimir (X ⊗ₖ Y) =
      (36 : ℂ) • (X ⊗ₖ Y) +
      (2 : ℂ) •
        ((twoReplicaLocalCorrelation * X) ⊗ₖ
          (twoReplicaLocalCorrelation * Y)) +
      (2 : ℂ) •
        ((X * twoReplicaLocalCorrelation) ⊗ₖ
          (Y * twoReplicaLocalCorrelation)) -
      (2 : ℂ) •
        ((twoReplicaLeftChannel X ⊗ₖ twoReplicaLeftChannel Y) +
         (twoReplicaRightChannel X ⊗ₖ twoReplicaRightChannel Y) +
         (twoReplicaCrossChannel X ⊗ₖ twoReplicaCrossChannel Y) +
         (twoReplicaReverseCrossChannel X ⊗ₖ
            twoReplicaReverseCrossChannel Y)) := by
  rw [twoReplicaEdgeCasimir_apply]
  simp_rw [twoReplicaMatrixCommutator_sq]
  calc
    (∑ a : Fin 3, ∑ b : Fin 3,
      (twoReplicaEdgeCollective a b * twoReplicaEdgeCollective a b *
          (X ⊗ₖ Y) +
        (X ⊗ₖ Y) * twoReplicaEdgeCollective a b *
          twoReplicaEdgeCollective a b -
        twoReplicaEdgeCollective a b * (X ⊗ₖ Y) *
          twoReplicaEdgeCollective a b -
        twoReplicaEdgeCollective a b * (X ⊗ₖ Y) *
          twoReplicaEdgeCollective a b)) =
        (∑ a : Fin 3, ∑ b : Fin 3,
          twoReplicaEdgeCollective a b * twoReplicaEdgeCollective a b) *
            (X ⊗ₖ Y) +
        (X ⊗ₖ Y) *
          (∑ a : Fin 3, ∑ b : Fin 3,
            twoReplicaEdgeCollective a b * twoReplicaEdgeCollective a b) -
        (∑ a : Fin 3, ∑ b : Fin 3,
          twoReplicaEdgeCollective a b * (X ⊗ₖ Y) *
            twoReplicaEdgeCollective a b) -
        (∑ a : Fin 3, ∑ b : Fin 3,
          twoReplicaEdgeCollective a b * (X ⊗ₖ Y) *
            twoReplicaEdgeCollective a b) := by
      simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [Matrix.sum_mul, Matrix.mul_sum]
      simp_rw [Matrix.sum_mul, Matrix.mul_sum]
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [sum_twoReplicaEdgeCollective_sq,
        sum_twoReplicaEdgeCollective_sandwich_kronecker]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
        twoReplicaKronecker_mul]
      module

theorem twoReplicaEdgeCasimir_one_one :
    twoReplicaEdgeCasimir
        ((1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) ⊗ₖ
          (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ)) = 0 := by
  rw [twoReplicaEdgeCasimir_kronecker, twoReplicaLeftChannel_one,
    twoReplicaRightChannel_one, twoReplicaCrossChannel_one,
    twoReplicaReverseCrossChannel_one]
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  change _ = (0 : ℂ)
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.kroneckerMap_apply,
    Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply]
  ring

theorem twoReplicaEdgeCasimir_one_correlation :
    twoReplicaEdgeCasimir
        ((1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) ⊗ₖ
          twoReplicaLocalCorrelation) =
      (48 : ℂ) •
          ((1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) ⊗ₖ
            twoReplicaLocalCorrelation) -
        (16 : ℂ) •
          (twoReplicaLocalCorrelation ⊗ₖ twoReplicaLocalCorrelation) := by
  rw [twoReplicaEdgeCasimir_kronecker, twoReplicaLeftChannel_one,
    twoReplicaRightChannel_one, twoReplicaCrossChannel_one,
    twoReplicaReverseCrossChannel_one,
    twoReplicaLeftChannel_correlation,
    twoReplicaRightChannel_correlation,
    twoReplicaCrossChannel_correlation,
    twoReplicaReverseCrossChannel_correlation,
    twoReplicaLocalCorrelation_sq]
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.kroneckerMap_apply,
    Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]
  ring

theorem twoReplicaEdgeCasimir_correlation_one :
    twoReplicaEdgeCasimir
        (twoReplicaLocalCorrelation ⊗ₖ
          (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ)) =
      (48 : ℂ) •
          (twoReplicaLocalCorrelation ⊗ₖ
            (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ)) -
        (16 : ℂ) •
          (twoReplicaLocalCorrelation ⊗ₖ twoReplicaLocalCorrelation) := by
  rw [twoReplicaEdgeCasimir_kronecker, twoReplicaLeftChannel_one,
    twoReplicaRightChannel_one, twoReplicaCrossChannel_one,
    twoReplicaReverseCrossChannel_one,
    twoReplicaLeftChannel_correlation,
    twoReplicaRightChannel_correlation,
    twoReplicaCrossChannel_correlation,
    twoReplicaReverseCrossChannel_correlation,
    twoReplicaLocalCorrelation_sq]
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.kroneckerMap_apply,
    Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]
  ring

theorem twoReplicaEdgeCasimir_correlation_correlation :
    twoReplicaEdgeCasimir
        (twoReplicaLocalCorrelation ⊗ₖ twoReplicaLocalCorrelation) =
      (32 : ℂ) •
          (twoReplicaLocalCorrelation ⊗ₖ twoReplicaLocalCorrelation) -
        (48 : ℂ) •
          ((1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) ⊗ₖ
            twoReplicaLocalCorrelation) -
        (48 : ℂ) •
          (twoReplicaLocalCorrelation ⊗ₖ
            (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ)) := by
  rw [twoReplicaEdgeCasimir_kronecker,
    twoReplicaLeftChannel_correlation,
    twoReplicaRightChannel_correlation,
    twoReplicaCrossChannel_correlation,
    twoReplicaReverseCrossChannel_correlation,
    twoReplicaLocalCorrelation_sq]
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [Matrix.kroneckerMap_apply, Matrix.smul_apply,
    Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]
  ring

def twoReplicaLocalRaw : Bool →
    Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ
  | false => 1
  | true => twoReplicaLocalCorrelation

def twoReplicaEdgeRaw (x : TwoReplicaEdgeLabel) :
    Matrix TwoReplicaEdgeIndex TwoReplicaEdgeIndex ℂ :=
  twoReplicaLocalRaw x.1 ⊗ₖ twoReplicaLocalRaw x.2

def twoReplicaEdgeInvariantEmbed :
    TwoReplicaEdgeCoeff →ₗ[ℂ]
      Matrix TwoReplicaEdgeIndex TwoReplicaEdgeIndex ℂ where
  toFun c := ∑ x : TwoReplicaEdgeLabel, c x • twoReplicaEdgeRaw x
  map_add' c d := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' z c := by
    simp [Pi.smul_apply, smul_smul, Finset.smul_sum]

def twoReplicaEdgeCasimirCoeff :
    TwoReplicaEdgeCoeff →ₗ[ℂ] TwoReplicaEdgeCoeff where
  toFun c
    | (false, false) => 0
    | (false, true) => 48 * c (false, true) - 48 * c (true, true)
    | (true, false) => 48 * c (true, false) - 48 * c (true, true)
    | (true, true) =>
        -16 * c (false, true) - 16 * c (true, false) + 32 * c (true, true)
  map_add' c d := by
    funext x
    rcases x with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' a c := by
    funext x
    rcases x with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp <;> ring

theorem twoReplicaEdgeCasimir_intertwines_coeff
    (c : TwoReplicaEdgeCoeff) :
    twoReplicaEdgeCasimir (twoReplicaEdgeInvariantEmbed c) =
      twoReplicaEdgeInvariantEmbed (twoReplicaEdgeCasimirCoeff c) := by
  change twoReplicaEdgeCasimir
      (∑ x : TwoReplicaEdgeLabel, c x • twoReplicaEdgeRaw x) =
    ∑ x : TwoReplicaEdgeLabel,
      twoReplicaEdgeCasimirCoeff c x • twoReplicaEdgeRaw x
  rw [map_sum]
  simp_rw [map_smul]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool,
    twoReplicaEdgeRaw, twoReplicaLocalRaw,
    twoReplicaEdgeCasimir_one_one,
    twoReplicaEdgeCasimir_one_correlation,
    twoReplicaEdgeCasimir_correlation_one,
    twoReplicaEdgeCasimir_correlation_correlation,
    twoReplicaEdgeCasimirCoeff, LinearMap.coe_mk, AddHom.coe_mk,
    zero_smul]
  module

theorem trace_twoReplicaSwap : Matrix.trace twoReplicaSwap = 2 := by
  rw [Matrix.trace, Fintype.sum_prod_type]
  rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  change (1 : ℂ) + 0 + (0 + 1) = 2
  norm_num

theorem trace_twoReplicaLocalCorrelation :
    Matrix.trace twoReplicaLocalCorrelation = 0 := by
  rw [twoReplicaLocalCorrelation_eq_swap, Matrix.trace_sub,
    Matrix.trace_smul, trace_twoReplicaSwap, Matrix.trace_one]
  norm_num

theorem trace_twoReplicaLocalCorrelation_sq :
    Matrix.trace
      (twoReplicaLocalCorrelation * twoReplicaLocalCorrelation) = 12 := by
  rw [twoReplicaLocalCorrelation_sq, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one,
    trace_twoReplicaLocalCorrelation]
  norm_num

def twoReplicaLocalRawNorm : Bool → ℂ
  | false => 4
  | true => 12

theorem trace_twoReplicaLocalRaw_mul (x y : Bool) :
    Matrix.trace (twoReplicaLocalRaw x * twoReplicaLocalRaw y) =
      if x = y then twoReplicaLocalRawNorm x else 0 := by
  fin_cases x <;> fin_cases y <;>
    simp [twoReplicaLocalRaw, twoReplicaLocalRawNorm,
      trace_twoReplicaLocalCorrelation,
      trace_twoReplicaLocalCorrelation_sq, Matrix.trace_one]

def twoReplicaEdgeRawNorm (x : TwoReplicaEdgeLabel) : ℂ :=
  twoReplicaLocalRawNorm x.1 * twoReplicaLocalRawNorm x.2

theorem trace_twoReplicaEdgeRaw_mul (x y : TwoReplicaEdgeLabel) :
    Matrix.trace (twoReplicaEdgeRaw x * twoReplicaEdgeRaw y) =
      if x = y then twoReplicaEdgeRawNorm x else 0 := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  rw [twoReplicaEdgeRaw, twoReplicaEdgeRaw, twoReplicaKronecker_mul,
    Matrix.trace_kronecker, trace_twoReplicaLocalRaw_mul,
    trace_twoReplicaLocalRaw_mul]
  fin_cases x₁ <;> fin_cases x₂ <;> fin_cases y₁ <;> fin_cases y₂ <;>
    norm_num [twoReplicaEdgeRawNorm, twoReplicaLocalRawNorm]

theorem trace_twoReplicaEdgeRaw_mul_embed
    (x : TwoReplicaEdgeLabel) (c : TwoReplicaEdgeCoeff) :
    Matrix.trace
        (twoReplicaEdgeRaw x * twoReplicaEdgeInvariantEmbed c) =
      twoReplicaEdgeRawNorm x * c x := by
  change Matrix.trace
      (twoReplicaEdgeRaw x *
        ∑ y : TwoReplicaEdgeLabel, c y • twoReplicaEdgeRaw y) = _
  rw [Matrix.mul_sum, Matrix.trace_sum]
  simp_rw [Matrix.mul_smul, Matrix.trace_smul,
    trace_twoReplicaEdgeRaw_mul]
  rcases x with ⟨x₁, x₂⟩
  fin_cases x₁ <;> fin_cases x₂ <;>
    simp [twoReplicaEdgeRawNorm, twoReplicaLocalRawNorm]
  <;> ring

theorem twoReplicaEdgeRawNorm_ne_zero (x : TwoReplicaEdgeLabel) :
    twoReplicaEdgeRawNorm x ≠ 0 := by
  rcases x with ⟨x₁, x₂⟩
  fin_cases x₁ <;> fin_cases x₂ <;>
    norm_num [twoReplicaEdgeRawNorm, twoReplicaLocalRawNorm]

theorem twoReplicaEdgeInvariantEmbed_eq_zero_iff
    (c : TwoReplicaEdgeCoeff) :
    twoReplicaEdgeInvariantEmbed c = 0 ↔ c = 0 := by
  constructor
  · intro hc
    funext x
    have hx := congrArg
      (fun M => Matrix.trace (twoReplicaEdgeRaw x * M)) hc
    have hprod : twoReplicaEdgeRawNorm x * c x = 0 := by
      simpa [trace_twoReplicaEdgeRaw_mul_embed] using hx
    exact (mul_eq_zero.mp hprod).resolve_left
      (twoReplicaEdgeRawNorm_ne_zero x)
  · rintro rfl
    exact map_zero twoReplicaEdgeInvariantEmbed

theorem twoReplicaEdgeInvariantEmbed_injective :
    Function.Injective twoReplicaEdgeInvariantEmbed := by
  intro c d hcd
  have hzero : twoReplicaEdgeInvariantEmbed (c - d) = 0 := by
    rw [map_sub, hcd, sub_self]
  have := (twoReplicaEdgeInvariantEmbed_eq_zero_iff (c - d)).mp hzero
  exact sub_eq_zero.mp this

def twoReplicaSynchronizedCoeff (a b : ℂ) : TwoReplicaEdgeCoeff :=
  fun x => if x = (false, false) then a else b

theorem twoReplicaEdgeCasimirCoeff_eq_zero_iff (c : TwoReplicaEdgeCoeff) :
    twoReplicaEdgeCasimirCoeff c = 0 ↔
      ∃ a b : ℂ, c = twoReplicaSynchronizedCoeff a b := by
  constructor
  · intro hc
    have h01 := congrFun hc (false, true)
    have h10 := congrFun hc (true, false)
    change 48 * c (false, true) - 48 * c (true, true) = 0 at h01
    change 48 * c (true, false) - 48 * c (true, true) = 0 at h10
    have h01eq : c (false, true) = c (true, true) := by
      apply (mul_left_cancel₀ (show (48 : ℂ) ≠ 0 by norm_num))
      linear_combination h01
    have h10eq : c (true, false) = c (true, true) := by
      apply (mul_left_cancel₀ (show (48 : ℂ) ≠ 0 by norm_num))
      linear_combination h10
    refine ⟨c (false, false), c (true, true), ?_⟩
    funext x
    rcases x with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp [twoReplicaSynchronizedCoeff, h01eq, h10eq]
  · rintro ⟨a, b, rfl⟩
    funext x
    rcases x with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      norm_num [twoReplicaEdgeCasimirCoeff, twoReplicaSynchronizedCoeff] ;
      ring

def twoReplicaCoeffEigenZeroIdentity : TwoReplicaEdgeCoeff
  | (false, false) => 1
  | _ => 0

def twoReplicaCoeffEigenZeroSwap : TwoReplicaEdgeCoeff
  | (false, false) => 0
  | _ => 1

def twoReplicaCoeffEigenFortyEight : TwoReplicaEdgeCoeff
  | (false, true) => 1
  | (true, false) => -1
  | _ => 0

def twoReplicaCoeffEigenEighty : TwoReplicaEdgeCoeff
  | (false, true) => 3
  | (true, false) => 3
  | (true, true) => -2
  | _ => 0

theorem twoReplicaEdgeCasimirCoeff_eigen_zero_identity :
    twoReplicaEdgeCasimirCoeff twoReplicaCoeffEigenZeroIdentity = 0 := by
  funext x
  rcases x with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [twoReplicaEdgeCasimirCoeff,
      twoReplicaCoeffEigenZeroIdentity]

theorem twoReplicaEdgeCasimirCoeff_eigen_zero_swap :
    twoReplicaEdgeCasimirCoeff twoReplicaCoeffEigenZeroSwap = 0 := by
  funext x
  rcases x with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [twoReplicaEdgeCasimirCoeff,
      twoReplicaCoeffEigenZeroSwap]

theorem twoReplicaEdgeCasimirCoeff_eigen_fortyEight :
    twoReplicaEdgeCasimirCoeff twoReplicaCoeffEigenFortyEight =
      (48 : ℂ) • twoReplicaCoeffEigenFortyEight := by
  funext x
  rcases x with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [twoReplicaEdgeCasimirCoeff,
      twoReplicaCoeffEigenFortyEight]

theorem twoReplicaEdgeCasimirCoeff_eigen_eighty :
    twoReplicaEdgeCasimirCoeff twoReplicaCoeffEigenEighty =
      (80 : ℂ) • twoReplicaCoeffEigenEighty := by
  funext x
  rcases x with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [twoReplicaEdgeCasimirCoeff,
      twoReplicaCoeffEigenEighty]

theorem twoReplicaCoeffEigen_decomposition (c : TwoReplicaEdgeCoeff) :
    ∃ a b d e : ℂ,
      c = a • twoReplicaCoeffEigenZeroIdentity +
        b • twoReplicaCoeffEigenZeroSwap +
        d • twoReplicaCoeffEigenFortyEight +
        e • twoReplicaCoeffEigenEighty := by
  let e : ℂ :=
    (c (false, true) + c (true, false) - 2 * c (true, true)) / 10
  let d : ℂ := (c (false, true) - c (true, false)) / 2
  let b : ℂ := c (true, true) + 2 * e
  refine ⟨c (false, false), b, d, e, ?_⟩
  funext x
  rcases x with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [twoReplicaCoeffEigenZeroIdentity,
      twoReplicaCoeffEigenZeroSwap,
      twoReplicaCoeffEigenFortyEight,
      twoReplicaCoeffEigenEighty, b, d, e] <;>
    ring

theorem twoReplicaCoeffEigen_combination_eq_zero_iff
    (a b d e : ℂ) :
    a • twoReplicaCoeffEigenZeroIdentity +
        b • twoReplicaCoeffEigenZeroSwap +
        d • twoReplicaCoeffEigenFortyEight +
        e • twoReplicaCoeffEigenEighty = 0 ↔
      a = 0 ∧ b = 0 ∧ d = 0 ∧ e = 0 := by
  constructor
  · intro h
    have h00 := congrFun h (false, false)
    have h01 := congrFun h (false, true)
    have h10 := congrFun h (true, false)
    have h11 := congrFun h (true, true)
    simp [twoReplicaCoeffEigenZeroIdentity,
      twoReplicaCoeffEigenZeroSwap,
      twoReplicaCoeffEigenFortyEight,
      twoReplicaCoeffEigenEighty] at h00 h01 h10 h11
    have he10 : 10 * e = 0 := by
      linear_combination h01 + h10 - 2 * h11
    have he : e = 0 :=
      (mul_eq_zero.mp he10).resolve_left (by norm_num)
    have hb : b = 0 := by
      linear_combination h11 + 2 * he
    have hd : d = 0 := by
      linear_combination h01 - hb - 3 * he
    exact ⟨h00, hb, hd, he⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp

theorem twoReplicaEdgeCasimir_invariant_eigenvectors :
    twoReplicaEdgeCasimir
        (twoReplicaEdgeInvariantEmbed twoReplicaCoeffEigenZeroIdentity) = 0 ∧
    twoReplicaEdgeCasimir
        (twoReplicaEdgeInvariantEmbed twoReplicaCoeffEigenZeroSwap) = 0 ∧
    twoReplicaEdgeCasimir
        (twoReplicaEdgeInvariantEmbed twoReplicaCoeffEigenFortyEight) =
      (48 : ℂ) •
        twoReplicaEdgeInvariantEmbed twoReplicaCoeffEigenFortyEight ∧
    twoReplicaEdgeCasimir
        (twoReplicaEdgeInvariantEmbed twoReplicaCoeffEigenEighty) =
      (80 : ℂ) •
        twoReplicaEdgeInvariantEmbed twoReplicaCoeffEigenEighty := by
  constructor
  · rw [twoReplicaEdgeCasimir_intertwines_coeff,
      twoReplicaEdgeCasimirCoeff_eigen_zero_identity, map_zero]
  constructor
  · rw [twoReplicaEdgeCasimir_intertwines_coeff,
      twoReplicaEdgeCasimirCoeff_eigen_zero_swap, map_zero]
  constructor
  · rw [twoReplicaEdgeCasimir_intertwines_coeff,
      twoReplicaEdgeCasimirCoeff_eigen_fortyEight, map_smul]
  · rw [twoReplicaEdgeCasimir_intertwines_coeff,
      twoReplicaEdgeCasimirCoeff_eigen_eighty, map_smul]

theorem twoReplicaEdgeCasimir_embed_eq_zero_iff
    (c : TwoReplicaEdgeCoeff) :
    twoReplicaEdgeCasimir (twoReplicaEdgeInvariantEmbed c) = 0 ↔
      ∃ a b : ℂ, c = twoReplicaSynchronizedCoeff a b := by
  rw [twoReplicaEdgeCasimir_intertwines_coeff,
    twoReplicaEdgeInvariantEmbed_eq_zero_iff,
    twoReplicaEdgeCasimirCoeff_eq_zero_iff]

abbrev TwoReplicaGlobalCoeff (V : Type*) := (V → Bool) → ℂ

def twoReplicaAllIdentity {V : Type*} : V → Bool := fun _ => false

def twoReplicaAllSwap {V : Type*} : V → Bool := fun _ => true

def twoReplicaGlobalSynchronizedCoeff {V : Type*} (a b : ℂ) :
    TwoReplicaGlobalCoeff V := by
  classical
  exact fun x =>
    if x = twoReplicaAllIdentity then a
    else if x = twoReplicaAllSwap then b
    else 0

theorem twoReplicaAllIdentity_ne_allSwap
    {V : Type*} [Nonempty V] :
    (twoReplicaAllIdentity : V → Bool) ≠ twoReplicaAllSwap := by
  intro h
  let v : V := Classical.choice (inferInstance : Nonempty V)
  have hv := congrFun h v
  simp [twoReplicaAllIdentity, twoReplicaAllSwap] at hv

theorem exists_adj_mismatch_of_not_global
    {V : Type*} [Nonempty V]
    {G : SimpleGraph V} (hG : G.Preconnected)
    (x : V → Bool)
    (hid : x ≠ twoReplicaAllIdentity)
    (hswap : x ≠ twoReplicaAllSwap) :
    ∃ u v, G.Adj u v ∧ x u ≠ x v := by
  by_contra hnone
  push Not at hnone
  have hinvariant : ∀ ⦃u v⦄, G.Adj u v → x u = x v := by
    intro u v huv
    exact hnone u v huv
  let v₀ : V := Classical.choice (inferInstance : Nonempty V)
  have hconstant : x = fun _ => x v₀ := by
    funext v
    exact eq_of_preconnected_of_adjInvariant hG x hinvariant v v₀
  cases hx : x v₀ with
  | false =>
      apply hid
      rw [hconstant]
      funext v
      simp [twoReplicaAllIdentity, hx]
  | true =>
      apply hswap
      rw [hconstant]
      funext v
      simp [twoReplicaAllSwap, hx]

theorem twoReplicaGlobal_edgeMismatch_zero_iff
    {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} (hG : G.Preconnected)
    (c : TwoReplicaGlobalCoeff V) :
    (∀ ⦃u v⦄, G.Adj u v →
      ∀ x : V → Bool, x u ≠ x v → c x = 0) ↔
    ∃ a b : ℂ, c = twoReplicaGlobalSynchronizedCoeff a b := by
  classical
  constructor
  · intro hedge
    refine ⟨c twoReplicaAllIdentity, c twoReplicaAllSwap, ?_⟩
    funext x
    by_cases hid : x = twoReplicaAllIdentity
    · subst x
      simp [twoReplicaGlobalSynchronizedCoeff]
    by_cases hswap : x = twoReplicaAllSwap
    · subst x
      simp [twoReplicaGlobalSynchronizedCoeff, hid]
    · rcases exists_adj_mismatch_of_not_global hG x hid hswap with
        ⟨u, v, huv, hneq⟩
      rw [hedge huv x hneq]
      simp [twoReplicaGlobalSynchronizedCoeff, hid, hswap]
  · rintro ⟨a, b, rfl⟩
    intro u v huv x hneq
    have hid : x ≠ twoReplicaAllIdentity := by
      intro hx
      apply hneq
      rw [hx]
      rfl
    have hswap : x ≠ twoReplicaAllSwap := by
      intro hx
      apply hneq
      rw [hx]
      rfl
    simp [twoReplicaGlobalSynchronizedCoeff, hid, hswap]

/-! ## Physical swap coordinates and the global master constraint -/

/-- Physical invariant basis at one site: identity or two-replica swap. -/
def twoReplicaLocalSwapRaw : Bool →
    Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ
  | false => 1
  | true => twoReplicaSwap

/-- Physical identity/swap basis on one interaction edge. -/
def twoReplicaEdgeSwapRaw (x : TwoReplicaEdgeLabel) :
    Matrix TwoReplicaEdgeIndex TwoReplicaEdgeIndex ℂ :=
  twoReplicaLocalSwapRaw x.1 ⊗ₖ twoReplicaLocalSwapRaw x.2

/-- Coefficient embedding in the physical identity/swap basis. -/
def twoReplicaEdgeSwapInvariantEmbed :
    TwoReplicaEdgeCoeff →ₗ[ℂ]
      Matrix TwoReplicaEdgeIndex TwoReplicaEdgeIndex ℂ where
  toFun c := ∑ x : TwoReplicaEdgeLabel, c x • twoReplicaEdgeSwapRaw x
  map_add' c d := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' z c := by
    simp [Pi.smul_apply, smul_smul, Finset.smul_sum]

/-- Exact coefficient action of the physical edge Casimir in identity/swap
coordinates.  Only the two mismatched coefficients enter. -/
def twoReplicaEdgeSwapCasimirCoeff :
    TwoReplicaEdgeCoeff →ₗ[ℂ] TwoReplicaEdgeCoeff where
  toFun c
    | (false, false) => -32 * (c (false, true) + c (true, false))
    | (false, true) => 64 * c (false, true) + 16 * c (true, false)
    | (true, false) => 16 * c (false, true) + 64 * c (true, false)
    | (true, true) => -32 * (c (false, true) + c (true, false))
  map_add' c d := by
    funext x
    rcases x with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' a c := by
    funext x
    rcases x with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp <;> ring

theorem twoReplicaSwap_eq_half_one_add_correlation :
    twoReplicaSwap =
      (2 : ℂ)⁻¹ •
        ((1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) +
          twoReplicaLocalCorrelation) := by
  rw [twoReplicaLocalCorrelation_eq_swap]
  module

theorem twoReplicaEdgeSwapRaw_false_false :
    twoReplicaEdgeSwapRaw (false, false) =
      twoReplicaEdgeRaw (false, false) := by
  rfl

theorem twoReplicaEdgeSwapRaw_false_true :
    twoReplicaEdgeSwapRaw (false, true) =
      (2 : ℂ)⁻¹ • twoReplicaEdgeRaw (false, false) +
        (2 : ℂ)⁻¹ • twoReplicaEdgeRaw (false, true) := by
  change (1 ⊗ₖ twoReplicaSwap) = _
  rw [twoReplicaSwap_eq_half_one_add_correlation]
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
    simp [twoReplicaEdgeRaw, twoReplicaLocalRaw,
      Matrix.kroneckerMap_apply, h₁, h₂]

theorem twoReplicaEdgeSwapRaw_true_false :
    twoReplicaEdgeSwapRaw (true, false) =
      (2 : ℂ)⁻¹ • twoReplicaEdgeRaw (false, false) +
        (2 : ℂ)⁻¹ • twoReplicaEdgeRaw (true, false) := by
  change (twoReplicaSwap ⊗ₖ 1) = _
  rw [twoReplicaSwap_eq_half_one_add_correlation]
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
    simp [twoReplicaEdgeRaw, twoReplicaLocalRaw,
      Matrix.kroneckerMap_apply, h₁, h₂]

theorem twoReplicaEdgeSwapRaw_true_true :
    twoReplicaEdgeSwapRaw (true, true) =
      (4 : ℂ)⁻¹ • twoReplicaEdgeRaw (false, false) +
        (4 : ℂ)⁻¹ • twoReplicaEdgeRaw (false, true) +
        (4 : ℂ)⁻¹ • twoReplicaEdgeRaw (true, false) +
        (4 : ℂ)⁻¹ • twoReplicaEdgeRaw (true, true) := by
  change (twoReplicaSwap ⊗ₖ twoReplicaSwap) = _
  rw [twoReplicaSwap_eq_half_one_add_correlation]
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
    simp [twoReplicaEdgeRaw, twoReplicaLocalRaw,
      Matrix.kroneckerMap_apply, h₁, h₂] <;> ring

theorem twoReplicaEdgeCasimir_swapRaw_false_false :
    twoReplicaEdgeCasimir (twoReplicaEdgeSwapRaw (false, false)) = 0 := by
  rw [twoReplicaEdgeSwapRaw_false_false,
    twoReplicaEdgeRaw, twoReplicaLocalRaw,
    twoReplicaEdgeCasimir_one_one]

theorem twoReplicaEdgeCasimir_swapRaw_false_true :
    twoReplicaEdgeCasimir (twoReplicaEdgeSwapRaw (false, true)) =
      (-32 : ℂ) • twoReplicaEdgeSwapRaw (false, false) +
        (64 : ℂ) • twoReplicaEdgeSwapRaw (false, true) +
        (16 : ℂ) • twoReplicaEdgeSwapRaw (true, false) +
        (-32 : ℂ) • twoReplicaEdgeSwapRaw (true, true) := by
  have h00 : twoReplicaEdgeCasimir (twoReplicaEdgeRaw (false, false)) = 0 := by
    simpa [twoReplicaEdgeRaw, twoReplicaLocalRaw] using
      twoReplicaEdgeCasimir_one_one
  have h01 : twoReplicaEdgeCasimir (twoReplicaEdgeRaw (false, true)) =
      (48 : ℂ) • twoReplicaEdgeRaw (false, true) -
        (16 : ℂ) • twoReplicaEdgeRaw (true, true) := by
    simpa [twoReplicaEdgeRaw, twoReplicaLocalRaw] using
      twoReplicaEdgeCasimir_one_correlation
  rw [twoReplicaEdgeSwapRaw_false_true, map_add, map_smul, map_smul,
    h00, h01,
    twoReplicaEdgeSwapRaw_false_false,
    twoReplicaEdgeSwapRaw_true_false,
    twoReplicaEdgeSwapRaw_true_true]
  module

theorem twoReplicaEdgeCasimir_swapRaw_true_false :
    twoReplicaEdgeCasimir (twoReplicaEdgeSwapRaw (true, false)) =
      (-32 : ℂ) • twoReplicaEdgeSwapRaw (false, false) +
        (16 : ℂ) • twoReplicaEdgeSwapRaw (false, true) +
        (64 : ℂ) • twoReplicaEdgeSwapRaw (true, false) +
        (-32 : ℂ) • twoReplicaEdgeSwapRaw (true, true) := by
  have h00 : twoReplicaEdgeCasimir (twoReplicaEdgeRaw (false, false)) = 0 := by
    simpa [twoReplicaEdgeRaw, twoReplicaLocalRaw] using
      twoReplicaEdgeCasimir_one_one
  have h10 : twoReplicaEdgeCasimir (twoReplicaEdgeRaw (true, false)) =
      (48 : ℂ) • twoReplicaEdgeRaw (true, false) -
        (16 : ℂ) • twoReplicaEdgeRaw (true, true) := by
    simpa [twoReplicaEdgeRaw, twoReplicaLocalRaw] using
      twoReplicaEdgeCasimir_correlation_one
  rw [twoReplicaEdgeSwapRaw_true_false, map_add, map_smul, map_smul,
    h00, h10,
    twoReplicaEdgeSwapRaw_false_false,
    twoReplicaEdgeSwapRaw_false_true,
    twoReplicaEdgeSwapRaw_true_true]
  module

theorem twoReplicaEdgeCasimir_swapRaw_true_true :
    twoReplicaEdgeCasimir (twoReplicaEdgeSwapRaw (true, true)) = 0 := by
  have h00 : twoReplicaEdgeCasimir (twoReplicaEdgeRaw (false, false)) = 0 := by
    simpa [twoReplicaEdgeRaw, twoReplicaLocalRaw] using
      twoReplicaEdgeCasimir_one_one
  have h01 : twoReplicaEdgeCasimir (twoReplicaEdgeRaw (false, true)) =
      (48 : ℂ) • twoReplicaEdgeRaw (false, true) -
        (16 : ℂ) • twoReplicaEdgeRaw (true, true) := by
    simpa [twoReplicaEdgeRaw, twoReplicaLocalRaw] using
      twoReplicaEdgeCasimir_one_correlation
  have h10 : twoReplicaEdgeCasimir (twoReplicaEdgeRaw (true, false)) =
      (48 : ℂ) • twoReplicaEdgeRaw (true, false) -
        (16 : ℂ) • twoReplicaEdgeRaw (true, true) := by
    simpa [twoReplicaEdgeRaw, twoReplicaLocalRaw] using
      twoReplicaEdgeCasimir_correlation_one
  have h11 : twoReplicaEdgeCasimir (twoReplicaEdgeRaw (true, true)) =
      (32 : ℂ) • twoReplicaEdgeRaw (true, true) -
        (48 : ℂ) • twoReplicaEdgeRaw (false, true) -
        (48 : ℂ) • twoReplicaEdgeRaw (true, false) := by
    simpa [twoReplicaEdgeRaw, twoReplicaLocalRaw] using
      twoReplicaEdgeCasimir_correlation_correlation
  rw [twoReplicaEdgeSwapRaw_true_true]
  simp only [map_add, map_smul, h00, h01, h10, h11]
  module

/-- The swap-coordinate operator is not a surrogate: it is exactly
intertwined with the nine-generator physical double-commutator Casimir. -/
theorem twoReplicaEdgeCasimir_intertwines_swapCoeff
    (c : TwoReplicaEdgeCoeff) :
    twoReplicaEdgeCasimir (twoReplicaEdgeSwapInvariantEmbed c) =
      twoReplicaEdgeSwapInvariantEmbed
        (twoReplicaEdgeSwapCasimirCoeff c) := by
  change twoReplicaEdgeCasimir
      (∑ x : TwoReplicaEdgeLabel, c x • twoReplicaEdgeSwapRaw x) =
    ∑ x : TwoReplicaEdgeLabel,
      twoReplicaEdgeSwapCasimirCoeff c x • twoReplicaEdgeSwapRaw x
  rw [map_sum]
  simp_rw [map_smul]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool,
    twoReplicaEdgeCasimir_swapRaw_false_false,
    twoReplicaEdgeCasimir_swapRaw_false_true,
    twoReplicaEdgeCasimir_swapRaw_true_false,
    twoReplicaEdgeCasimir_swapRaw_true_true,
    twoReplicaEdgeSwapCasimirCoeff, LinearMap.coe_mk, AddHom.coe_mk]
  module

/-- In physical identity/swap coordinates, the edge Casimir vanishes exactly
when both mismatched swap coefficients vanish. -/
theorem twoReplicaEdgeSwapCasimirCoeff_eq_zero_iff
    (c : TwoReplicaEdgeCoeff) :
    twoReplicaEdgeSwapCasimirCoeff c = 0 ↔
      c (false, true) = 0 ∧ c (true, false) = 0 := by
  constructor
  · intro hc
    have h01 := congrFun hc (false, true)
    have h10 := congrFun hc (true, false)
    change 64 * c (false, true) + 16 * c (true, false) = 0 at h01
    change 16 * c (false, true) + 64 * c (true, false) = 0 at h10
    have hb : 240 * c (false, true) = 0 := by
      linear_combination 4 * h01 - h10
    have hd : 240 * c (true, false) = 0 := by
      linear_combination 4 * h10 - h01
    exact ⟨
      (mul_eq_zero.mp hb).resolve_left (by norm_num),
      (mul_eq_zero.mp hd).resolve_left (by norm_num)⟩
  · rintro ⟨h01, h10⟩
    funext x
    rcases x with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp [twoReplicaEdgeSwapCasimirCoeff, h01, h10]

/-- Replace the two endpoint labels of a global swap configuration. -/
def twoReplicaSetEdgeLabel
    {V : Type*} [DecidableEq V]
    (u v : V) (x : V → Bool) (p : TwoReplicaEdgeLabel) : V → Bool :=
  Function.update (Function.update x u p.1) v p.2

@[simp] theorem twoReplicaSetEdgeLabel_left
    {V : Type*} [DecidableEq V] {u v : V} (huv : u ≠ v)
    (x : V → Bool) (p : TwoReplicaEdgeLabel) :
    twoReplicaSetEdgeLabel u v x p u = p.1 := by
  simp [twoReplicaSetEdgeLabel, huv]

@[simp] theorem twoReplicaSetEdgeLabel_right
    {V : Type*} [DecidableEq V] {u v : V}
    (x : V → Bool) (p : TwoReplicaEdgeLabel) :
    twoReplicaSetEdgeLabel u v x p v = p.2 := by
  simp [twoReplicaSetEdgeLabel]

@[simp] theorem twoReplicaSetEdgeLabel_setEdge
    {V : Type*} [DecidableEq V] {u v : V} (huv : u ≠ v)
    (x : V → Bool) (p q : TwoReplicaEdgeLabel) :
    twoReplicaSetEdgeLabel u v (twoReplicaSetEdgeLabel u v x p) q =
      twoReplicaSetEdgeLabel u v x q := by
  funext w
  by_cases hwu : w = u
  · subst w
    simp [huv]
  by_cases hwv : w = v
  · subst w
    simp
  simp [twoReplicaSetEdgeLabel, hwu, hwv]

@[simp] theorem twoReplicaSetEdgeLabel_current
    {V : Type*} [DecidableEq V] {u v : V} (huv : u ≠ v)
    (x : V → Bool) :
    twoReplicaSetEdgeLabel u v x (x u, x v) = x := by
  funext w
  by_cases hwu : w = u
  · subst w
    simp [huv]
  by_cases hwv : w = v
  · subst w
    simp
  simp [twoReplicaSetEdgeLabel, hwv]

/-- The four physical coefficients in one edge slice, with every outside
swap label retained. -/
def twoReplicaGlobalEdgeSlice
    {V : Type*} [DecidableEq V]
    (u v : V) (c : TwoReplicaGlobalCoeff V) (x : V → Bool) :
    TwoReplicaEdgeCoeff :=
  fun p => c (twoReplicaSetEdgeLabel u v x p)

/-- Tensor extension of the exact physical edge Casimir coefficient action.
It applies the local physical Casimir independently to every outside block. -/
def twoReplicaGlobalEdgeCasimirCoeff
    {V : Type*} [Fintype V] [DecidableEq V]
    (u v : V) : TwoReplicaGlobalCoeff V →ₗ[ℂ] TwoReplicaGlobalCoeff V where
  toFun c x :=
    twoReplicaEdgeSwapCasimirCoeff
      (twoReplicaGlobalEdgeSlice u v c x) (x u, x v)
  map_add' c d := by
    funext x
    rcases hxu : x u with _ | _ <;> rcases hxv : x v with _ | _ <;>
      simp [twoReplicaGlobalEdgeSlice, twoReplicaEdgeSwapCasimirCoeff,
        hxu, hxv] <;> ring
  map_smul' a c := by
    funext x
    rcases hxu : x u with _ | _ <;> rcases hxv : x v with _ | _ <;>
      simp [twoReplicaGlobalEdgeSlice, twoReplicaEdgeSwapCasimirCoeff,
        hxu, hxv] <;> ring

/-- Exact tensor edge-kernel law in physical swap coordinates. -/
theorem twoReplicaGlobalEdgeCasimirCoeff_eq_zero_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {u v : V} (huv : u ≠ v) (c : TwoReplicaGlobalCoeff V) :
    twoReplicaGlobalEdgeCasimirCoeff u v c = 0 ↔
      ∀ x : V → Bool, x u ≠ x v → c x = 0 := by
  constructor
  · intro hc x hx
    have hslice :
        twoReplicaEdgeSwapCasimirCoeff
          (twoReplicaGlobalEdgeSlice u v c x) = 0 := by
      funext p
      have hp := congrFun hc (twoReplicaSetEdgeLabel u v x p)
      have hslices :
          twoReplicaGlobalEdgeSlice u v c
              (twoReplicaSetEdgeLabel u v x p) =
            twoReplicaGlobalEdgeSlice u v c x := by
        funext q
        simp [twoReplicaGlobalEdgeSlice, huv]
      change twoReplicaEdgeSwapCasimirCoeff
          (twoReplicaGlobalEdgeSlice u v c
            (twoReplicaSetEdgeLabel u v x p))
          ((twoReplicaSetEdgeLabel u v x p) u,
            (twoReplicaSetEdgeLabel u v x p) v) = 0 at hp
      rw [hslices,
        twoReplicaSetEdgeLabel_left huv,
        twoReplicaSetEdgeLabel_right] at hp
      exact hp
    have hmismatch :=
      (twoReplicaEdgeSwapCasimirCoeff_eq_zero_iff
        (twoReplicaGlobalEdgeSlice u v c x)).mp hslice
    rcases hxu : x u with _ | _ <;> rcases hxv : x v with _ | _
    · exact False.elim (hx (by simp [hxu, hxv]))
    · have hcur := twoReplicaSetEdgeLabel_current huv x
      rw [hxu, hxv] at hcur
      rw [← hcur]
      exact hmismatch.1
    · have hcur := twoReplicaSetEdgeLabel_current huv x
      rw [hxu, hxv] at hcur
      rw [← hcur]
      exact hmismatch.2
    · exact False.elim (hx (by simp [hxu, hxv]))
  · intro hmismatch
    funext x
    have h01 :
        twoReplicaGlobalEdgeSlice u v c x (false, true) = 0 := by
      apply hmismatch
      simp [huv]
    have h10 :
        twoReplicaGlobalEdgeSlice u v c x (true, false) = 0 := by
      apply hmismatch
      simp [huv]
    have hlocal :
        twoReplicaEdgeSwapCasimirCoeff
          (twoReplicaGlobalEdgeSlice u v c x) = 0 :=
      (twoReplicaEdgeSwapCasimirCoeff_eq_zero_iff _).2 ⟨h01, h10⟩
    exact congrFun hlocal (x u, x v)

/-- Hilbert realization of global swap coefficients. -/
abbrev TwoReplicaGlobalHilbertCoeff (V : Type*) :=
  EuclideanSpace ℂ (V → Bool)

/-- Hilbert-space tensor lift of one exact physical edge Casimir. -/
def twoReplicaGlobalEdgeCasimirHilbert
    {V : Type*} [Fintype V] [DecidableEq V]
    (u v : V) :
    TwoReplicaGlobalHilbertCoeff V →ₗ[ℂ]
      TwoReplicaGlobalHilbertCoeff V where
  toFun c := WithLp.toLp 2
    (twoReplicaGlobalEdgeCasimirCoeff u v c.ofLp)
  map_add' c d := by
    apply WithLp.ofLp_injective 2
    exact (twoReplicaGlobalEdgeCasimirCoeff u v).map_add c.ofLp d.ofLp
  map_smul' a c := by
    apply WithLp.ofLp_injective 2
    exact (twoReplicaGlobalEdgeCasimirCoeff u v).map_smul a c.ofLp

/-- Continuous physical edge constraints indexed by all ordered site pairs;
nonedges contribute the zero constraint. -/
noncomputable def twoReplicaGraphEdgeConstraint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (e : V × V) :
    TwoReplicaGlobalHilbertCoeff V →L[ℂ]
      TwoReplicaGlobalHilbertCoeff V :=
  by
    classical
    exact if G.Adj e.1 e.2 then
      LinearMap.toContinuousLinearMap
        (twoReplicaGlobalEdgeCasimirHilbert e.1 e.2)
    else 0

/-- Positive finite master constraint of all physical two-replica edge
Casimirs.  Ordered-pair duplication changes weights, never its kernel. -/
noncomputable def twoReplicaGraphMasterConstraint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    TwoReplicaGlobalHilbertCoeff V →L[ℂ]
      TwoReplicaGlobalHilbertCoeff V :=
  _root_.HTGeometry.finiteQuantumMasterConstraint
    (𝕜 := ℂ) (E := TwoReplicaGlobalHilbertCoeff V) (ι := V × V)
    (twoReplicaGraphEdgeConstraint G)

/-- **Global physical two-replica synchronization.** On every finite nonempty
connected interaction graph, the positive master constraint of the exact
physical edge Casimirs has only identity and global-swap modes. -/
theorem physicalState_twoReplicaGraphMasterConstraint_iff
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {G : SimpleGraph V} (hG : G.Preconnected)
    (c : TwoReplicaGlobalHilbertCoeff V) :
    GaloisForLFunctions.PhysicalState
        (twoReplicaGraphMasterConstraint G).toLinearMap c ↔
      ∃ a b : ℂ,
        c = WithLp.toLp 2 (twoReplicaGlobalSynchronizedCoeff a b) := by
  rw [twoReplicaGraphMasterConstraint,
    _root_.HTGeometry.physicalState_finiteQuantumMasterConstraint_iff]
  constructor
  · intro hfamily
    have hcoeff : ∃ a b : ℂ,
        c.ofLp = twoReplicaGlobalSynchronizedCoeff a b := by
      apply (twoReplicaGlobal_edgeMismatch_zero_iff hG c.ofLp).mp
      intro u v huv x hx
      have hedge := hfamily (u, v)
      rw [GaloisForLFunctions.PhysicalState] at hedge
      change twoReplicaGraphEdgeConstraint G (u, v) c = 0 at hedge
      simp only [twoReplicaGraphEdgeConstraint, huv, if_pos] at hedge
      have hedgeCoeff : twoReplicaGlobalEdgeCasimirCoeff u v c.ofLp = 0 := by
        have h := congrArg WithLp.ofLp hedge
        simpa [twoReplicaGlobalEdgeCasimirHilbert] using h
      exact (twoReplicaGlobalEdgeCasimirCoeff_eq_zero_iff huv.ne c.ofLp).mp
        hedgeCoeff x hx
    rcases hcoeff with ⟨a, b, hab⟩
    exact ⟨a, b, by
      apply WithLp.ofLp_injective 2
      simpa using hab⟩
  · intro hsync
    rcases hsync with ⟨a, b, rfl⟩
    have hmismatch :=
      (twoReplicaGlobal_edgeMismatch_zero_iff hG
        (twoReplicaGlobalSynchronizedCoeff a b)).mpr ⟨a, b, rfl⟩
    intro e
    rw [GaloisForLFunctions.PhysicalState]
    rcases e with ⟨u, v⟩
    by_cases huv : G.Adj u v
    · have hzero : twoReplicaGlobalEdgeCasimirCoeff u v
          (twoReplicaGlobalSynchronizedCoeff a b) = 0 :=
        (twoReplicaGlobalEdgeCasimirCoeff_eq_zero_iff huv.ne _).2
          (fun x hx => hmismatch huv x hx)
      apply WithLp.ofLp_injective 2
      simp [twoReplicaGraphEdgeConstraint,
        twoReplicaGlobalEdgeCasimirHilbert, huv, hzero]
    · simp [twoReplicaGraphEdgeConstraint, huv]

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.HaferkampTwoQubitCliffordSeeds
import GaloisForLFunctions.QECLean.Foundations.Tensor

/-!
# Exact two-qubit Pauli transport for the Haferkamp light-cone proof

Appendix B of Haferkamp--Faist--Kothakonda--Eisert--Yunger Halpern (2022)
needs a determinant-one two-qubit Clifford that reduces every nonidentity
two-site Pauli label to a nonzero multiple of target `Z`.  This module proves
that finite classification directly in the Boolean computational basis.
-/

open Matrix
open scoped Kronecker

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Conjugation by a tensor product factors into the conjugations on each
factor. -/
theorem twoQubitTensor_conjugation
    (U V : Matrix.unitaryGroup Bool ℂ) (M N : Matrix Bool Bool ℂ) :
    (Quantum.tensorGate U V : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        Matrix.kronecker M N *
        Matrix.conjTranspose
          (Quantum.tensorGate U V : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      Matrix.kronecker
        ((U : Matrix Bool Bool ℂ) * M * Matrix.conjTranspose (U : Matrix Bool Bool ℂ))
        ((V : Matrix Bool Bool ℂ) * N * Matrix.conjTranspose (V : Matrix Bool Bool ℂ)) := by
  simp only [Quantum.tensorGate_val]
  rw [Matrix.conjTranspose_kronecker]
  change ((U : Matrix Bool Bool ℂ) ⊗ₖ (V : Matrix Bool Bool ℂ)) *
      (M ⊗ₖ N) *
      (Matrix.conjTranspose (U : Matrix Bool Bool ℂ) ⊗ₖ
        Matrix.conjTranspose (V : Matrix Bool Bool ℂ)) = _
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rfl

/-- Chosen one-qubit Clifford normalizer for a Boolean Pauli label. -/
def boolAxisNormalizer : Option (Fin 3) → Matrix.unitaryGroup Bool ℂ
  | none => 1
  | some 0 => boolHadamard
  | some 1 => boolHadamardPhase
  | some 2 => 1

/-- Sign acquired when the chosen normalizer transports a Pauli label. -/
def boolAxisNormalizerScalar : Option (Fin 3) → ℂ
  | none => 1
  | some 0 => 1
  | some 1 => -1
  | some 2 => 1

/-- The target label after one-qubit normalization. -/
def boolAxisNormalizerTarget : Option (Fin 3) → Option (Fin 3)
  | none => none
  | some _ => some 2

/-- Every one-qubit Pauli label is transported to its support-preserving
normal form. -/
theorem boolAxisNormalizer_conj (p : Option (Fin 3)) :
    (boolAxisNormalizer p : Matrix Bool Bool ℂ) * boolPauliOption p *
        Matrix.conjTranspose (boolAxisNormalizer p : Matrix Bool Bool ℂ) =
      boolAxisNormalizerScalar p • boolPauliOption (boolAxisNormalizerTarget p) := by
  fin_cases p
  · simp [boolAxisNormalizer, boolAxisNormalizerScalar, boolAxisNormalizerTarget,
      boolPauliOption]
  · simpa [boolAxisNormalizer, boolAxisNormalizerScalar, boolAxisNormalizerTarget,
      boolPauliOption]
      using boolHadamard_conj_X
  · simpa [boolAxisNormalizer, boolAxisNormalizerScalar, boolAxisNormalizerTarget,
      boolPauliOption]
      using boolHadamardPhase_conj_Y
  · simp [boolAxisNormalizer, boolAxisNormalizerScalar, boolAxisNormalizerTarget,
      boolPauliOption]

/-- The normalization scalar is always nonzero. -/
theorem boolAxisNormalizerScalar_ne_zero (p : Option (Fin 3)) :
    boolAxisNormalizerScalar p ≠ 0 := by
  fin_cases p <;> norm_num [boolAxisNormalizerScalar]

/-- A nonidentity label normalizes to `Z`. -/
theorem boolAxisNormalizerTarget_eq_Z (p : Option (Fin 3)) (hp : p ≠ none) :
    boolAxisNormalizerTarget p = some 2 := by
  fin_cases p <;> simp_all [boolAxisNormalizerTarget]

/-- Tensorized local normalizer for a two-qubit Pauli label. -/
def boolTwoQubitLocalNormalizer (p q : Option (Fin 3)) :
    Matrix.unitaryGroup (Bool × Bool) ℂ :=
  Quantum.tensorGate (boolAxisNormalizer p) (boolAxisNormalizer q)

/-- Exact conjugation rule for the tensorized local normalizer. -/
theorem boolTwoQubitLocalNormalizer_conj
    (p q : Option (Fin 3)) :
    (boolTwoQubitLocalNormalizer p q : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli p q *
        Matrix.conjTranspose
          (boolTwoQubitLocalNormalizer p q : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      (boolAxisNormalizerScalar p * boolAxisNormalizerScalar q) •
        boolTwoQubitPauli (boolAxisNormalizerTarget p) (boolAxisNormalizerTarget q) := by
  rw [boolTwoQubitLocalNormalizer, boolTwoQubitPauli, twoQubitTensor_conjugation,
    boolAxisNormalizer_conj, boolAxisNormalizer_conj]
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  simp [boolTwoQubitPauli, Matrix.kronecker, mul_assoc, mul_left_comm]

/-- Composition of a unitary conjugation with a scalar-valued transport
identity. -/
theorem unitary_mul_conjugation_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U V : Matrix.unitaryGroup ι ℂ) (P Q : Matrix ι ι ℂ) (c : ℂ)
    (h : (V : Matrix ι ι ℂ) * P * Matrix.conjTranspose (V : Matrix ι ι ℂ) = c • Q) :
    ((U * V : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) * P *
        Matrix.conjTranspose ((U * V : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) =
      c • ((U : Matrix ι ι ℂ) * Q * Matrix.conjTranspose (U : Matrix ι ι ℂ)) := by
  rw [unitary_mul_conjugation, h]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

/-- A literal two-qubit Clifford transport.  The branches correspond to a
singleton already on target, a singleton on source, and two-site support. -/
def boolTwoQubitTransport (p q : Option (Fin 3)) :
    Matrix.unitaryGroup (Bool × Bool) ℂ :=
  if p = none then boolTwoQubitLocalNormalizer p q
  else if q = none then boolTwoQubitSWAP * boolTwoQubitLocalNormalizer p q
  else boolTwoQubitCNOT * boolTwoQubitLocalNormalizer p q

/-- Every nonidentity two-qubit Boolean Pauli is transported to a nonzero
multiple of target `Z` by the explicit unitary transport. -/
theorem boolTwoQubitTransport_conj
    (p q : Option (Fin 3)) (h : p ≠ none ∨ q ≠ none) :
    ∃ c : ℂ, c ≠ 0 ∧
      (boolTwoQubitTransport p q : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
          boolTwoQubitPauli p q *
          Matrix.conjTranspose
            (boolTwoQubitTransport p q : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
        c • boolTwoQubitPauli none (some 2) := by
  refine ⟨boolAxisNormalizerScalar p * boolAxisNormalizerScalar q,
    mul_ne_zero (boolAxisNormalizerScalar_ne_zero p) (boolAxisNormalizerScalar_ne_zero q), ?_⟩
  by_cases hp : p = none
  · subst p
    have hq : q ≠ none := by simpa using h
    rw [boolTwoQubitTransport, if_pos rfl]
    rw [boolTwoQubitLocalNormalizer_conj]
    change (1 * boolAxisNormalizerScalar q) •
        boolTwoQubitPauli none (boolAxisNormalizerTarget q) =
      (1 * boolAxisNormalizerScalar q) • boolTwoQubitPauli none (some 2)
    rw [boolAxisNormalizerTarget_eq_Z q hq]
  · by_cases hq : q = none
    · subst q
      rw [boolTwoQubitTransport, if_neg hp, if_pos rfl]
      rw [unitary_mul_conjugation_smul boolTwoQubitSWAP
        (boolTwoQubitLocalNormalizer p none) _ _ _
        (boolTwoQubitLocalNormalizer_conj p none)]
      rw [boolAxisNormalizerTarget_eq_Z p hp]
      simp only [boolAxisNormalizerTarget, boolAxisNormalizerScalar, mul_one]
      rw [boolTwoQubitSWAP_conj_sourceZ]
    · rw [boolTwoQubitTransport, if_neg hp, if_neg hq]
      rw [unitary_mul_conjugation_smul boolTwoQubitCNOT
        (boolTwoQubitLocalNormalizer p q) _ _ _
        (boolTwoQubitLocalNormalizer_conj p q)]
      rw [boolAxisNormalizerTarget_eq_Z p hp,
        boolAxisNormalizerTarget_eq_Z q hq]
      rw [boolTwoQubitCNOT_conj_twoZ]

/-- The type of nonidentity two-qubit Boolean Pauli labels. -/
def boolNonidentityTwoQubitPauliLabel :=
  {pq : Option (Fin 3) × Option (Fin 3) | pq.1 ≠ none ∨ pq.2 ≠ none}

/-- Closed `SU(4)` transport theorem for every nonidentity two-qubit Boolean
Pauli label. -/
theorem boolNonidentityTwoQubitPauli_exists_specialUnitaryTransport
    (pq : boolNonidentityTwoQubitPauliLabel) :
    ∃ U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ, ∃ c : ℂ, c ≠ 0 ∧
      (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) * boolTwoQubitPauli pq.1.1 pq.1.2 *
        Matrix.conjTranspose (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      c • boolTwoQubitPauli none (some 2) := by
  obtain ⟨c, hc, htransport⟩ := boolTwoQubitTransport_conj pq.1.1 pq.1.2 pq.2
  refine ⟨scalarSpecialUnitaryRepresentative (boolTwoQubitTransport pq.1.1 pq.1.2), c, hc, ?_⟩
  rw [scalarSpecialUnitaryRepresentative_conjugation_eq]
  exact htransport

end

end GaloisForLFunctions.HTGeometry

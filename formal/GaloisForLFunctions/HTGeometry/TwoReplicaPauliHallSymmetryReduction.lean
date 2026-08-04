import GaloisForLFunctions.HTGeometry.TwoReplicaPauliRelativeParityInverse
import GaloisForLFunctions.HTGeometry.LinearFamilyDefectSupermodularity

/-!
# Symmetry reduction of the two-replica Pauli Hall obstruction

Paired-Pauli conjugation sends each local collective commutator to itself or
its negative.  Hence it preserves the linear span of the complete local
commutator family.  The canonical greatest maximum-defect subspace is
therefore fixed by every paired-Pauli conjugation and splits into simultaneous
relative-parity sectors.

This turns the abstract canonical-obstruction theorem into a literal Pauli
statement.  No eigenbasis, diagonalization, positivity, or spectral premise
is used.
-/

open scoped Matrix Kronecker
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Conjugation of one one-qubit Pauli by another is positive on the same
axis and negative on a distinct axis. -/
theorem finiteQubitPauli_conj
    (a b : Fin 3) :
    finiteQubitPauli b * finiteQubitPauli a * finiteQubitPauli b =
      if b = a then finiteQubitPauli a else -finiteQubitPauli a := by
  by_cases hba : b = a
  · subst b
    rw [finiteQubitPauli_mul_self, Matrix.one_mul, if_pos rfl]
  · rw [if_neg hba]
    have hanti := finiteQubitPauli_mul_eq_neg_mul_of_ne hba
    calc
      finiteQubitPauli b * finiteQubitPauli a * finiteQubitPauli b =
          -(finiteQubitPauli a * finiteQubitPauli b) *
            finiteQubitPauli b := by rw [hanti]
      _ = -(finiteQubitPauli a *
            (finiteQubitPauli b * finiteQubitPauli b)) := by
              noncomm_ring
      _ = -finiteQubitPauli a := by
              rw [finiteQubitPauli_mul_self, Matrix.mul_one]

/-- Paired-Pauli conjugation acts with the same axis sign on the left
replica Pauli. -/
theorem twoReplicaPauliPair_conj_left
    (a b : Fin 3) :
    twoReplicaPauliPair b * twoReplicaPauliLeft a *
        twoReplicaPauliPair b =
      if b = a then twoReplicaPauliLeft a else -twoReplicaPauliLeft a := by
  rw [twoReplicaPauliPair, twoReplicaPauliLeft,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, finiteQubitPauli_conj,
    finiteQubitPauli_mul_self]
  by_cases hba : b = a
  · rw [if_pos hba, if_pos hba]
  · rw [if_neg hba, if_neg hba]
    ext i j
    simp

/-- Paired-Pauli conjugation acts with the same axis sign on the right
replica Pauli. -/
theorem twoReplicaPauliPair_conj_right
    (a b : Fin 3) :
    twoReplicaPauliPair b * twoReplicaPauliRight a *
        twoReplicaPauliPair b =
      if b = a then twoReplicaPauliRight a else -twoReplicaPauliRight a := by
  rw [twoReplicaPauliPair, twoReplicaPauliRight,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, finiteQubitPauli_conj,
    finiteQubitPauli_mul_self]
  by_cases hba : b = a
  · rw [if_pos hba, if_pos hba]
  · rw [if_neg hba, if_neg hba]
    ext i j
    simp

/-- Commutators are natural under conjugation by an involution. -/
theorem ringCommutator_conjugation_involution
    {A : Type*} [Ring A] (g p x : A) (hg : g * g = 1) :
    g * ringCommutator p (g * x * g) * g =
      ringCommutator (g * p * g) x := by
  unfold ringCommutator
  calc
    g * (p * (g * x * g) - (g * x * g) * p) * g =
        (g * p * g) * x * (g * g) -
          (g * g) * x * (g * p * g) := by noncomm_ring
    _ = (g * p * g) * x - x * (g * p * g) := by rw [hg]; simp

theorem ringCommutator_neg_left
    {A : Type*} [Ring A] (p x : A) :
    ringCommutator (-p) x = -ringCommutator p x := by
  unfold ringCommutator
  noncomm_ring

/-- Exact local covariance: paired conjugation fixes the collective
commutator on its own axis and negates it on either transverse axis. -/
theorem twoReplicaPairedPauli_collectiveCommutator_covariant
    (a b : Fin 3) (X : TwoReplicaLocalMatrix) :
    twoReplicaPairedPauliConjugationLinear b
        (twoReplicaLocalCollectiveCommutatorLinear a
          (twoReplicaPairedPauliConjugationLinear b X)) =
      if b = a then twoReplicaLocalCollectiveCommutatorLinear a X
      else -twoReplicaLocalCollectiveCommutatorLinear a X := by
  change twoReplicaPauliPair b *
      twoReplicaLocalCollectiveCommutator a
        (twoReplicaPauliPair b * X * twoReplicaPauliPair b) *
          twoReplicaPauliPair b = _
  rw [twoReplicaLocalCollectiveCommutator, Matrix.mul_add, Matrix.add_mul,
    ringCommutator_conjugation_involution _ _ _
      (twoReplicaPauliPair_mul_self b),
    ringCommutator_conjugation_involution _ _ _
      (twoReplicaPauliPair_mul_self b),
    twoReplicaPauliPair_conj_left,
    twoReplicaPauliPair_conj_right]
  by_cases hba : b = a
  · rw [if_pos hba, if_pos hba, if_pos hba]
    rfl
  · rw [if_neg hba, if_neg hba, if_neg hba,
      ringCommutator_neg_left, ringCommutator_neg_left]
    change -ringCommutator (twoReplicaPauliLeft a) X +
        -ringCommutator (twoReplicaPauliRight a) X =
      -(ringCommutator (twoReplicaPauliLeft a) X +
        ringCommutator (twoReplicaPauliRight a) X)
    module

@[simp] theorem twoReplicaPairedPauliConjugationEquiv_apply
    (a : Fin 3) (X : TwoReplicaLocalMatrix) :
    twoReplicaPairedPauliConjugationEquiv a X =
      twoReplicaPairedPauliConjugationLinear a X := rfl

@[simp] theorem twoReplicaPairedPauliConjugationEquiv_symm_apply
    (a : Fin 3) (X : TwoReplicaLocalMatrix) :
    (twoReplicaPairedPauliConjugationEquiv a).symm X =
      twoReplicaPairedPauliConjugationLinear a X := rfl

theorem twoReplicaPairedPauliConjugationEquiv_symm_toLinearMap_eq
    (b : Fin 3) :
    ((twoReplicaPairedPauliConjugationEquiv b).symm :
      TwoReplicaLocalMatrix →ₗ[ℂ] TwoReplicaLocalMatrix) =
    (twoReplicaPairedPauliConjugationEquiv b :
      TwoReplicaLocalMatrix →ₗ[ℂ] TwoReplicaLocalMatrix) := by
  apply LinearMap.ext
  intro X
  rfl

/-- Operator-level form of local covariance. -/
theorem twoReplicaPairedPauli_conjugatedCollectiveCommutator_eq
    (a b : Fin 3) :
    (((twoReplicaPairedPauliConjugationEquiv b :
        TwoReplicaLocalMatrix →ₗ[ℂ] TwoReplicaLocalMatrix).comp
      (twoReplicaLocalCollectiveCommutatorLinear a)).comp
      ((twoReplicaPairedPauliConjugationEquiv b).symm :
        TwoReplicaLocalMatrix →ₗ[ℂ] TwoReplicaLocalMatrix)) =
      if b = a then twoReplicaLocalCollectiveCommutatorLinear a
      else -twoReplicaLocalCollectiveCommutatorLinear a := by
  apply LinearMap.ext
  intro X
  change twoReplicaPairedPauliConjugationLinear b
      (twoReplicaLocalCollectiveCommutatorLinear a
        (twoReplicaPairedPauliConjugationLinear b X)) = _
  by_cases hba : b = a
  · rw [if_pos hba]
    simpa [hba] using
      twoReplicaPairedPauli_collectiveCommutator_covariant a b X
  · rw [if_neg hba]
    simpa [hba] using
      twoReplicaPairedPauli_collectiveCommutator_covariant a b X

/-- Every conjugated local generator lies in the original family span. -/
theorem twoReplicaPairedPauli_conjugatedCollectiveCommutator_mem_span
    (a b : Fin 3) :
    (((twoReplicaPairedPauliConjugationEquiv b :
        TwoReplicaLocalMatrix →ₗ[ℂ] TwoReplicaLocalMatrix).comp
      (twoReplicaLocalCollectiveCommutatorLinear a)).comp
      ((twoReplicaPairedPauliConjugationEquiv b).symm :
        TwoReplicaLocalMatrix →ₗ[ℂ] TwoReplicaLocalMatrix)) ∈
      linearFamilyOperatorSpan twoReplicaLocalCollectiveCommutatorLinear := by
  rw [twoReplicaPairedPauli_conjugatedCollectiveCommutator_eq]
  have hgenerator : twoReplicaLocalCollectiveCommutatorLinear a ∈
      linearFamilyOperatorSpan twoReplicaLocalCollectiveCommutatorLinear :=
    Submodule.subset_span ⟨a, rfl⟩
  split
  · exact hgenerator
  · exact Submodule.neg_mem _ hgenerator

/-- The canonical greatest Hall obstruction of the literal local collective
Pauli family is fixed by every paired-Pauli conjugation. -/
theorem twoReplicaLocalCollectiveCommutator_greatestMaximizer_fixed
    (U : Submodule ℂ TwoReplicaLocalMatrix)
    (hgreatest : ∀ V : Submodule ℂ TwoReplicaLocalMatrix,
      linearFamilyDefect twoReplicaLocalCollectiveCommutatorLinear V =
        linearFamilyDefect twoReplicaLocalCollectiveCommutatorLinear U →
      V ≤ U)
    (b : Fin 3) :
    U.map (twoReplicaPairedPauliConjugationLinear b) = U := by
  apply linearFamilyDefect_greatestMaximizer_map_eq_of_spanCovariant
      twoReplicaLocalCollectiveCommutatorLinear U
      (twoReplicaPairedPauliConjugationEquiv b)
      (twoReplicaPairedPauliConjugationEquiv b) hgreatest
  · intro a
    exact twoReplicaPairedPauli_conjugatedCollectiveCommutator_mem_span a b
  · intro a
    rw [twoReplicaPairedPauliConjugationEquiv_symm_toLinearMap_eq]
    exact twoReplicaPairedPauli_conjugatedCollectiveCommutator_mem_span a b

/-- The canonical greatest local Hall obstruction has the exact four-sector
relative-Pauli decomposition for every pair of Pauli axes. -/
theorem twoReplicaLocalCollectiveCommutator_greatestMaximizer_bigrading
    (U : Submodule ℂ TwoReplicaLocalMatrix)
    (hgreatest : ∀ V : Submodule ℂ TwoReplicaLocalMatrix,
      linearFamilyDefect twoReplicaLocalCollectiveCommutatorLinear V =
        linearFamilyDefect twoReplicaLocalCollectiveCommutatorLinear U →
      V ≤ U)
    (a b : Fin 3) :
    U =
      (((U ⊓ involutiveEvenSubspace
          (twoReplicaPairedPauliConjugationEquiv a)) ⊓
            involutiveEvenSubspace
              (twoReplicaPairedPauliConjugationEquiv b)) ⊔
        ((U ⊓ involutiveEvenSubspace
          (twoReplicaPairedPauliConjugationEquiv a)) ⊓
            involutiveOddSubspace
              (twoReplicaPairedPauliConjugationEquiv b))) ⊔
      (((U ⊓ involutiveOddSubspace
          (twoReplicaPairedPauliConjugationEquiv a)) ⊓
            involutiveEvenSubspace
              (twoReplicaPairedPauliConjugationEquiv b)) ⊔
        ((U ⊓ involutiveOddSubspace
          (twoReplicaPairedPauliConjugationEquiv a)) ⊓
            involutiveOddSubspace
              (twoReplicaPairedPauliConjugationEquiv b))) := by
  apply twoReplicaPairedPauliInvariantSubspace_eq_bigrading a b U
  · exact (twoReplicaLocalCollectiveCommutator_greatestMaximizer_fixed
      U hgreatest a).le
  · exact (twoReplicaLocalCollectiveCommutator_greatestMaximizer_fixed
      U hgreatest b).le

end

end GaloisForLFunctions.HTGeometry

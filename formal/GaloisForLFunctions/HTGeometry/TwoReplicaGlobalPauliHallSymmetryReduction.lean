import GaloisForLFunctions.HTGeometry.FinitePauliConjugationLaw
import GaloisForLFunctions.HTGeometry.LinearFamilyDefectSupermodularity
import GaloisForLFunctions.HTGeometry.FiniteCommutingInvolutionParityDecomposition
import GaloisForLFunctions.HTGeometry.TwoInvolutionCollectiveCommutator

open scoped BigOperators Matrix Kronecker
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

abbrev FiniteTwoReplicaConfiguration (σ : Type*) :=
  FiniteQubitConfiguration σ × FiniteQubitConfiguration σ

abbrev FiniteTwoReplicaMatrix (σ : Type*) :=
  Matrix (FiniteTwoReplicaConfiguration σ)
    (FiniteTwoReplicaConfiguration σ) ℂ

def finiteTwoReplicaPauliLeft
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) : FiniteTwoReplicaMatrix σ :=
  finitePauliMatrix P ⊗ₖ (1 : Matrix (FiniteQubitConfiguration σ)
    (FiniteQubitConfiguration σ) ℂ)

def finiteTwoReplicaPauliRight
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) : FiniteTwoReplicaMatrix σ :=
  (1 : Matrix (FiniteQubitConfiguration σ)
    (FiniteQubitConfiguration σ) ℂ) ⊗ₖ finitePauliMatrix P

def finiteTwoReplicaPairedPauli
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) : FiniteTwoReplicaMatrix σ :=
  finitePauliMatrix P ⊗ₖ finitePauliMatrix P

@[simp] theorem finiteTwoReplicaPauliLeft_mul_self
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) :
    finiteTwoReplicaPauliLeft P * finiteTwoReplicaPauliLeft P = 1 := by
  rw [finiteTwoReplicaPauliLeft, ← Matrix.mul_kronecker_mul,
    finitePauliMatrix_mul_self, Matrix.one_mul, Matrix.one_kronecker_one]

@[simp] theorem finiteTwoReplicaPauliRight_mul_self
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) :
    finiteTwoReplicaPauliRight P * finiteTwoReplicaPauliRight P = 1 := by
  rw [finiteTwoReplicaPauliRight, ← Matrix.mul_kronecker_mul,
    finitePauliMatrix_mul_self, Matrix.one_mul, Matrix.one_kronecker_one]

@[simp] theorem finiteTwoReplicaPauliLeft_mul_right
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) :
    finiteTwoReplicaPauliLeft P * finiteTwoReplicaPauliRight P =
      finiteTwoReplicaPairedPauli P := by
  rw [finiteTwoReplicaPauliLeft, finiteTwoReplicaPauliRight,
    finiteTwoReplicaPairedPauli, ← Matrix.mul_kronecker_mul]
  simp

@[simp] theorem finiteTwoReplicaPauliRight_mul_left
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) :
    finiteTwoReplicaPauliRight P * finiteTwoReplicaPauliLeft P =
      finiteTwoReplicaPairedPauli P := by
  rw [finiteTwoReplicaPauliLeft, finiteTwoReplicaPauliRight,
    finiteTwoReplicaPairedPauli, ← Matrix.mul_kronecker_mul]
  simp

@[simp] theorem finiteTwoReplicaPairedPauli_mul_self
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) :
    finiteTwoReplicaPairedPauli P * finiteTwoReplicaPairedPauli P = 1 := by
  rw [finiteTwoReplicaPairedPauli, ← Matrix.mul_kronecker_mul,
    finitePauliMatrix_mul_self, Matrix.one_kronecker_one]

theorem finiteTwoReplicaPairedPauli_conj_left
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (Q P : σ → Option (Fin 3)) :
    finiteTwoReplicaPairedPauli Q * finiteTwoReplicaPauliLeft P *
        finiteTwoReplicaPairedPauli Q =
      finitePauliConjugationSign Q P • finiteTwoReplicaPauliLeft P := by
  rw [finiteTwoReplicaPairedPauli, finiteTwoReplicaPauliLeft,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, finitePauliMatrix_conj,
    finitePauliMatrix_mul_self]
  rw [Matrix.smul_kronecker]

theorem finiteTwoReplicaPairedPauli_conj_right
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (Q P : σ → Option (Fin 3)) :
    finiteTwoReplicaPairedPauli Q * finiteTwoReplicaPauliRight P *
        finiteTwoReplicaPairedPauli Q =
      finitePauliConjugationSign Q P • finiteTwoReplicaPauliRight P := by
  rw [finiteTwoReplicaPairedPauli, finiteTwoReplicaPauliRight,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, finitePauliMatrix_conj,
    finitePauliMatrix_mul_self]
  rw [Matrix.kronecker_smul]

theorem finitePauliMatrix_mul_eq_sign_mul
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (Q P : σ → Option (Fin 3)) :
    finitePauliMatrix Q * finitePauliMatrix P =
      finitePauliConjugationSign Q P •
        (finitePauliMatrix P * finitePauliMatrix Q) := by
  calc
    finitePauliMatrix Q * finitePauliMatrix P =
        (finitePauliMatrix Q * finitePauliMatrix P) *
          (finitePauliMatrix Q * finitePauliMatrix Q) := by
            rw [finitePauliMatrix_mul_self, Matrix.mul_one]
    _ = (finitePauliMatrix Q * finitePauliMatrix P * finitePauliMatrix Q) *
          finitePauliMatrix Q := by noncomm_ring
    _ = (finitePauliConjugationSign Q P • finitePauliMatrix P) *
          finitePauliMatrix Q := by rw [finitePauliMatrix_conj]
    _ = finitePauliConjugationSign Q P •
          (finitePauliMatrix P * finitePauliMatrix Q) := by
            rw [Algebra.smul_mul_assoc]

/-- Paired global Pauli matrices commute exactly; one-replica commutation
signs cancel between replicas. -/
theorem finiteTwoReplicaPairedPauli_comm
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (Q P : σ → Option (Fin 3)) :
    finiteTwoReplicaPairedPauli Q * finiteTwoReplicaPairedPauli P =
      finiteTwoReplicaPairedPauli P * finiteTwoReplicaPairedPauli Q := by
  rw [finiteTwoReplicaPairedPauli, finiteTwoReplicaPairedPauli,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    finitePauliMatrix_mul_eq_sign_mul Q P]
  let s := finitePauliConjugationSign Q P
  let R := finitePauliMatrix P * finitePauliMatrix Q
  change (s • R) ⊗ₖ (s • R) = R ⊗ₖ R
  rw [Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul,
    finitePauliConjugationSign_sq]
  simp

def finiteTwoReplicaCollectiveCommutator
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) (X : FiniteTwoReplicaMatrix σ) :
    FiniteTwoReplicaMatrix σ :=
  ringCommutator (finiteTwoReplicaPauliLeft P) X +
    ringCommutator (finiteTwoReplicaPauliRight P) X

def finiteTwoReplicaCollectiveCommutatorLinear
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) :
    FiniteTwoReplicaMatrix σ →ₗ[ℂ] FiniteTwoReplicaMatrix σ where
  toFun := finiteTwoReplicaCollectiveCommutator P
  map_add' X Y := by
    simp [finiteTwoReplicaCollectiveCommutator, ringCommutator,
      Matrix.mul_add, Matrix.add_mul]
    module
  map_smul' c X := by
    simp [finiteTwoReplicaCollectiveCommutator, ringCommutator]
    module

/-- Exact square law of an arbitrary global collective Pauli commutator on
its paired-conjugation odd sector. -/
theorem finiteTwoReplicaCollectiveCommutator_sq_of_relativeOdd
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) (X : FiniteTwoReplicaMatrix σ)
    (hodd : finiteTwoReplicaPairedPauli P * X *
        finiteTwoReplicaPairedPauli P = -X) :
    finiteTwoReplicaCollectiveCommutator P
        (finiteTwoReplicaCollectiveCommutator P X) = 4 * X := by
  have hodd' :
      (finiteTwoReplicaPauliLeft P * finiteTwoReplicaPauliRight P) * X *
          (finiteTwoReplicaPauliLeft P * finiteTwoReplicaPauliRight P) = -X := by
    simpa only [finiteTwoReplicaPauliLeft_mul_right] using hodd
  exact twoInvolution_collectiveCommutator_sq_of_relativeOdd
    (finiteTwoReplicaPauliLeft P) (finiteTwoReplicaPauliRight P) X
    (finiteTwoReplicaPauliLeft_mul_self P)
    (finiteTwoReplicaPauliRight_mul_self P)
    (by rw [finiteTwoReplicaPauliLeft_mul_right,
      finiteTwoReplicaPauliRight_mul_left]) hodd'

/-- An arbitrary global collective Pauli commutator is injective on every
subspace odd under its paired conjugation. -/
theorem finiteTwoReplicaCollectiveCommutator_eq_zero_iff_of_relativeOdd
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) (X : FiniteTwoReplicaMatrix σ)
    (hodd : finiteTwoReplicaPairedPauli P * X *
        finiteTwoReplicaPairedPauli P = -X) :
    finiteTwoReplicaCollectiveCommutator P X = 0 ↔ X = 0 := by
  constructor
  · intro hzero
    have hsquare := finiteTwoReplicaCollectiveCommutator_sq_of_relativeOdd P X hodd
    rw [hzero] at hsquare
    have h4 : (4 : FiniteTwoReplicaMatrix σ) * X = 0 := by
      rw [← hsquare]
      simp [finiteTwoReplicaCollectiveCommutator, ringCommutator]
    have hfour : (4 : FiniteTwoReplicaMatrix σ) * X = (4 : ℂ) • X := by
      have hfourMatrix : (4 : FiniteTwoReplicaMatrix σ) =
          (4 : ℂ) • (1 : FiniteTwoReplicaMatrix σ) := by
        ext i j
        rw [Matrix.ofNat_apply]
        simp [Matrix.one_apply]
      rw [hfourMatrix, Algebra.smul_mul_assoc, Matrix.one_mul]
    rw [hfour] at h4
    exact (smul_eq_zero.mp h4).resolve_left (by norm_num)
  · rintro rfl
    simp [finiteTwoReplicaCollectiveCommutator, ringCommutator]

def finiteTwoReplicaPairedPauliConjugationLinear
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (Q : σ → Option (Fin 3)) :
    FiniteTwoReplicaMatrix σ →ₗ[ℂ] FiniteTwoReplicaMatrix σ where
  toFun X := finiteTwoReplicaPairedPauli Q * X *
    finiteTwoReplicaPairedPauli Q
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp

theorem finiteTwoReplicaPairedPauliConjugationLinear_involutive
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (Q : σ → Option (Fin 3)) :
    Function.Involutive (finiteTwoReplicaPairedPauliConjugationLinear Q) := by
  intro X
  change finiteTwoReplicaPairedPauli Q *
      (finiteTwoReplicaPairedPauli Q * X * finiteTwoReplicaPairedPauli Q) *
        finiteTwoReplicaPairedPauli Q = X
  calc
    _ = (finiteTwoReplicaPairedPauli Q * finiteTwoReplicaPairedPauli Q) * X *
        (finiteTwoReplicaPairedPauli Q * finiteTwoReplicaPairedPauli Q) := by
      noncomm_ring
    _ = X := by rw [finiteTwoReplicaPairedPauli_mul_self]; simp

/-- Paired-Pauli conjugations commute as global linear operators. -/
theorem finiteTwoReplicaPairedPauliConjugationLinear_comm
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (Q P : σ → Option (Fin 3)) (X : FiniteTwoReplicaMatrix σ) :
    finiteTwoReplicaPairedPauliConjugationLinear Q
        (finiteTwoReplicaPairedPauliConjugationLinear P X) =
      finiteTwoReplicaPairedPauliConjugationLinear P
        (finiteTwoReplicaPairedPauliConjugationLinear Q X) := by
  change finiteTwoReplicaPairedPauli Q *
      (finiteTwoReplicaPairedPauli P * X * finiteTwoReplicaPairedPauli P) *
        finiteTwoReplicaPairedPauli Q =
    finiteTwoReplicaPairedPauli P *
      (finiteTwoReplicaPairedPauli Q * X * finiteTwoReplicaPairedPauli Q) *
        finiteTwoReplicaPairedPauli P
  calc
    _ = (finiteTwoReplicaPairedPauli Q * finiteTwoReplicaPairedPauli P) * X *
        (finiteTwoReplicaPairedPauli P * finiteTwoReplicaPairedPauli Q) := by
          noncomm_ring
    _ = (finiteTwoReplicaPairedPauli P * finiteTwoReplicaPairedPauli Q) * X *
        (finiteTwoReplicaPairedPauli Q * finiteTwoReplicaPairedPauli P) := by
          rw [finiteTwoReplicaPairedPauli_comm Q P]
    _ = _ := by noncomm_ring

def finiteTwoReplicaPairedPauliConjugationEquiv
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (Q : σ → Option (Fin 3)) :
    FiniteTwoReplicaMatrix σ ≃ₗ[ℂ] FiniteTwoReplicaMatrix σ :=
  LinearEquiv.ofInvolutive (finiteTwoReplicaPairedPauliConjugationLinear Q)
    (finiteTwoReplicaPairedPauliConjugationLinear_involutive Q)

theorem ringCommutator_smul_left
    {A : Type*} [Ring A] [Algebra ℂ A]
    (c : ℂ) (p x : A) :
    ringCommutator (c • p) x = c • ringCommutator p x := by
  unfold ringCommutator
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  module

/-- Exact arbitrary-register covariance of every collective Pauli
commutator under every paired Pauli conjugation. -/
theorem finiteTwoReplicaPairedPauli_collectiveCommutator_covariant
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (Q P : σ → Option (Fin 3)) (X : FiniteTwoReplicaMatrix σ) :
    finiteTwoReplicaPairedPauliConjugationLinear Q
        (finiteTwoReplicaCollectiveCommutatorLinear P
          (finiteTwoReplicaPairedPauliConjugationLinear Q X)) =
      finitePauliConjugationSign Q P •
        finiteTwoReplicaCollectiveCommutatorLinear P X := by
  change finiteTwoReplicaPairedPauli Q *
      finiteTwoReplicaCollectiveCommutator P
        (finiteTwoReplicaPairedPauli Q * X * finiteTwoReplicaPairedPauli Q) *
          finiteTwoReplicaPairedPauli Q = _
  rw [finiteTwoReplicaCollectiveCommutator, Matrix.mul_add, Matrix.add_mul,
    ringCommutator_conjugation_involution _ _ _
      (finiteTwoReplicaPairedPauli_mul_self Q),
    ringCommutator_conjugation_involution _ _ _
      (finiteTwoReplicaPairedPauli_mul_self Q),
    finiteTwoReplicaPairedPauli_conj_left,
    finiteTwoReplicaPairedPauli_conj_right,
    ringCommutator_smul_left, ringCommutator_smul_left]
  change finitePauliConjugationSign Q P •
      ringCommutator (finiteTwoReplicaPauliLeft P) X +
      finitePauliConjugationSign Q P •
        ringCommutator (finiteTwoReplicaPauliRight P) X =
    finitePauliConjugationSign Q P •
      (ringCommutator (finiteTwoReplicaPauliLeft P) X +
        ringCommutator (finiteTwoReplicaPauliRight P) X)
  exact (smul_add _ _ _).symm

/-- Intertwining form of global Pauli covariance. -/
theorem finiteTwoReplicaPairedPauli_collectiveCommutator_intertwines
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (Q P : σ → Option (Fin 3)) (X : FiniteTwoReplicaMatrix σ) :
    finiteTwoReplicaPairedPauliConjugationLinear Q
        (finiteTwoReplicaCollectiveCommutatorLinear P X) =
      finitePauliConjugationSign Q P •
        finiteTwoReplicaCollectiveCommutatorLinear P
          (finiteTwoReplicaPairedPauliConjugationLinear Q X) := by
  have h := finiteTwoReplicaPairedPauli_collectiveCommutator_covariant
    Q P (finiteTwoReplicaPairedPauliConjugationLinear Q X)
  rw [finiteTwoReplicaPairedPauliConjugationLinear_involutive Q X] at h
  exact h

@[simp] theorem finiteTwoReplicaPairedPauliConjugationEquiv_apply
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (Q : σ → Option (Fin 3)) (X : FiniteTwoReplicaMatrix σ) :
    finiteTwoReplicaPairedPauliConjugationEquiv Q X =
      finiteTwoReplicaPairedPauliConjugationLinear Q X := rfl

@[simp] theorem finiteTwoReplicaPairedPauliConjugationEquiv_symm_apply
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (Q : σ → Option (Fin 3)) (X : FiniteTwoReplicaMatrix σ) :
    (finiteTwoReplicaPairedPauliConjugationEquiv Q).symm X =
      finiteTwoReplicaPairedPauliConjugationLinear Q X := rfl

theorem finiteTwoReplicaPairedPauliConjugationEquiv_symm_toLinearMap_eq
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (Q : σ → Option (Fin 3)) :
    ((finiteTwoReplicaPairedPauliConjugationEquiv Q).symm :
      FiniteTwoReplicaMatrix σ →ₗ[ℂ] FiniteTwoReplicaMatrix σ) =
    (finiteTwoReplicaPairedPauliConjugationEquiv Q :
      FiniteTwoReplicaMatrix σ →ₗ[ℂ] FiniteTwoReplicaMatrix σ) := by
  apply LinearMap.ext
  intro X
  rfl

def finiteTwoReplicaQLocalCollectiveCommutatorLinear
    (σ : Type*) [Fintype σ] [DecidableEq σ] (q : ℕ) :
    FiniteQLocalPauliLabel σ q →
      FiniteTwoReplicaMatrix σ →ₗ[ℂ] FiniteTwoReplicaMatrix σ :=
  fun P => finiteTwoReplicaCollectiveCommutatorLinear P.1

theorem finiteTwoReplicaPairedPauli_conjugatedQLocalCommutator_eq
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ℕ) (Q : σ → Option (Fin 3)) (P : FiniteQLocalPauliLabel σ q) :
    (((finiteTwoReplicaPairedPauliConjugationEquiv Q :
        FiniteTwoReplicaMatrix σ ≃ₗ[ℂ] FiniteTwoReplicaMatrix σ).toLinearMap.comp
      (finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q P)).comp
      ((finiteTwoReplicaPairedPauliConjugationEquiv Q).symm :
        FiniteTwoReplicaMatrix σ →ₗ[ℂ] FiniteTwoReplicaMatrix σ)) =
      finitePauliConjugationSign Q P.1 •
        finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q P := by
  apply LinearMap.ext
  intro X
  exact finiteTwoReplicaPairedPauli_collectiveCommutator_covariant Q P.1 X

theorem finiteTwoReplicaPairedPauli_conjugatedQLocalCommutator_mem_span
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ℕ) (Q : σ → Option (Fin 3)) (P : FiniteQLocalPauliLabel σ q) :
    (((finiteTwoReplicaPairedPauliConjugationEquiv Q :
        FiniteTwoReplicaMatrix σ ≃ₗ[ℂ] FiniteTwoReplicaMatrix σ).toLinearMap.comp
      (finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q P)).comp
      ((finiteTwoReplicaPairedPauliConjugationEquiv Q).symm :
        FiniteTwoReplicaMatrix σ →ₗ[ℂ] FiniteTwoReplicaMatrix σ)) ∈
      linearFamilyOperatorSpan
        (finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q) := by
  rw [finiteTwoReplicaPairedPauli_conjugatedQLocalCommutator_eq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨P, rfl⟩)

/-- The canonical greatest Hall obstruction for the full weight-at-most-q
global collective Pauli family is invariant under every paired Pauli string. -/
theorem finiteTwoReplicaQLocal_greatestMaximizer_fixed
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ℕ) (U : Submodule ℂ (FiniteTwoReplicaMatrix σ))
    (hgreatest : ∀ V : Submodule ℂ (FiniteTwoReplicaMatrix σ),
      linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q) V =
        linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q) U →
      V ≤ U)
    (Q : σ → Option (Fin 3)) :
    U.map (finiteTwoReplicaPairedPauliConjugationLinear Q) = U := by
  apply linearFamilyDefect_greatestMaximizer_map_eq_of_spanCovariant
      (finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q) U
      (finiteTwoReplicaPairedPauliConjugationEquiv Q)
      (finiteTwoReplicaPairedPauliConjugationEquiv Q) hgreatest
  · intro P
    exact finiteTwoReplicaPairedPauli_conjugatedQLocalCommutator_mem_span q Q P
  · intro P
    rw [finiteTwoReplicaPairedPauliConjugationEquiv_symm_toLinearMap_eq]
    exact finiteTwoReplicaPairedPauli_conjugatedQLocalCommutator_mem_span q Q P

/-- Every finite list of paired-Pauli symmetries resolves the canonical
global Hall obstruction into simultaneous parity pieces whose sum is exact. -/
theorem finiteTwoReplicaQLocal_greatestMaximizer_eq_simultaneousParityPieces
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ℕ) (U : Submodule ℂ (FiniteTwoReplicaMatrix σ))
    (hgreatest : ∀ V : Submodule ℂ (FiniteTwoReplicaMatrix σ),
      linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q) V =
        linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q) U →
      V ≤ U)
    (Qs : List (σ → Option (Fin 3))) :
    U = submoduleListSup (simultaneousParityPieces
      (Qs.map finiteTwoReplicaPairedPauliConjugationEquiv) U) := by
  apply invariantSubspace_eq_simultaneousParityPieces_sup
      (K := ℂ) (by norm_num)
  · intro C hC
    rcases List.mem_map.mp hC with ⟨Q, _hQ, rfl⟩
    exact finiteTwoReplicaPairedPauliConjugationLinear_involutive Q
  · rw [List.pairwise_map]
    apply List.pairwise_of_forall
    intro Q P X
    exact finiteTwoReplicaPairedPauliConjugationLinear_comm Q P X
  · intro C hC
    rcases List.mem_map.mp hC with ⟨Q, _hQ, rfl⟩
    exact (finiteTwoReplicaQLocal_greatestMaximizer_fixed
      q U hgreatest Q).le

/-- Finranks of the simultaneous parity pieces of the canonical global Hall
obstruction add exactly, for every finite list of paired-Pauli symmetries. -/
theorem finiteTwoReplicaQLocal_greatestMaximizer_finrank_parityPieces
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ℕ) (U : Submodule ℂ (FiniteTwoReplicaMatrix σ))
    (hgreatest : ∀ V : Submodule ℂ (FiniteTwoReplicaMatrix σ),
      linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q) V =
        linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q) U →
      V ≤ U)
    (Qs : List (σ → Option (Fin 3))) :
    Module.finrank ℂ U =
      ((simultaneousParityPieces
        (Qs.map finiteTwoReplicaPairedPauliConjugationEquiv) U).map
          (fun V : Submodule ℂ (FiniteTwoReplicaMatrix σ) =>
            Module.finrank ℂ V)).sum := by
  apply invariantSubspace_finrank_eq_simultaneousParityPieces_sum
      (K := ℂ) (by norm_num)
  · intro C hC
    rcases List.mem_map.mp hC with ⟨Q, _hQ, rfl⟩
    exact finiteTwoReplicaPairedPauliConjugationLinear_involutive Q
  · rw [List.pairwise_map]
    apply List.pairwise_of_forall
    intro Q P X
    exact finiteTwoReplicaPairedPauliConjugationLinear_comm Q P X
  · intro C hC
    rcases List.mem_map.mp hC with ⟨Q, _hQ, rfl⟩
    exact (finiteTwoReplicaQLocal_greatestMaximizer_fixed
      q U hgreatest Q).le

end

end GaloisForLFunctions.HTGeometry

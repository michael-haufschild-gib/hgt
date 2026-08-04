import GaloisForLFunctions.HTGeometry.TwoInvolutionCollectiveCommutator
import GaloisForLFunctions.HTGeometry.TwoReplicaLocalSingletSynchronization
import GaloisForLFunctions.HTGeometry.InvolutiveSubspaceParityDecomposition

/-!
# Two-replica Pauli relative-parity inverse

The abstract two-involution identity is instantiated for the literal
single-qubit Pauli matrices acting on two replicas.  Every sector odd under
the paired Pauli conjugation has an exact collective-commutator inverse.
-/

open scoped Matrix Kronecker
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

@[simp] theorem twoReplicaPauliPair_mul_self (a : Fin 3) :
    twoReplicaPauliPair a * twoReplicaPauliPair a =
      (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) := by
  rw [twoReplicaPauliPair, ← Matrix.mul_kronecker_mul,
    finiteQubitPauli_mul_self, Matrix.one_kronecker_one]

/-- Distinct one-qubit Pauli matrices anticommute. -/
theorem finiteQubitPauli_mul_eq_neg_mul_of_ne
    {a b : Fin 3} (hab : a ≠ b) :
    finiteQubitPauli a * finiteQubitPauli b =
      -(finiteQubitPauli b * finiteQubitPauli a) := by
  ext i j
  fin_cases a <;> fin_cases b <;> try { exact (hab rfl).elim } <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [finiteQubitPauli, Matrix.mul_apply, Fintype.sum_bool]

/-- Paired Pauli matrices commute: the sign from exchanging two one-replica
Paulis occurs twice and cancels. -/
theorem twoReplicaPauliPair_comm (a b : Fin 3) :
    twoReplicaPauliPair a * twoReplicaPauliPair b =
      twoReplicaPauliPair b * twoReplicaPauliPair a := by
  by_cases hab : a = b
  · subst b
    rfl
  · rw [twoReplicaPauliPair, twoReplicaPauliPair,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      finiteQubitPauli_mul_eq_neg_mul_of_ne hab]
    let Q := finiteQubitPauli b * finiteQubitPauli a
    change ((-Q) ⊗ₖ (-Q)) = (Q ⊗ₖ Q)
    rw [show -Q = (-1 : ℂ) • Q by simp]
    rw [Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul]
    norm_num

/-- Collective commutator of one physical Pauli acting on both replicas. -/
def twoReplicaLocalCollectiveCommutator (a : Fin 3)
    (X : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) :
    Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ :=
  ringCommutator (twoReplicaPauliLeft a) X +
    ringCommutator (twoReplicaPauliRight a) X

/-- Exact square law on the relative-odd Pauli sector. -/
theorem twoReplicaLocalCollectiveCommutator_sq_of_relativeOdd
    (a : Fin 3) (X : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ)
    (hodd : twoReplicaPauliPair a * X * twoReplicaPauliPair a = -X) :
    twoReplicaLocalCollectiveCommutator a
        (twoReplicaLocalCollectiveCommutator a X) = 4 * X := by
  have hodd' :
      (twoReplicaPauliLeft a * twoReplicaPauliRight a) * X *
          (twoReplicaPauliLeft a * twoReplicaPauliRight a) = -X := by
    simpa only [twoReplicaPauliLeft_mul_right] using hodd
  exact twoInvolution_collectiveCommutator_sq_of_relativeOdd
    (twoReplicaPauliLeft a) (twoReplicaPauliRight a) X
    (twoReplicaPauliLeft_mul_self a) (twoReplicaPauliRight_mul_self a)
    (by rw [twoReplicaPauliLeft_mul_right, twoReplicaPauliRight_mul_left])
    hodd'

/-- Four times the identity is a unit in the literal two-replica matrix
algebra. -/
theorem twoReplicaLocalMatrix_four_isUnit :
    IsUnit (4 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  change IsUnit
    (Matrix.det (Matrix.diagonal fun _ : TwoReplicaLocalIndex => (4 : ℂ)))
  rw [Matrix.det_diagonal]
  norm_num [Finset.prod_const, Fintype.card_prod]

/-- The literal Pauli collective commutator has no kernel on its
relative-odd sector. -/
theorem twoReplicaLocalCollectiveCommutator_eq_zero_iff_of_relativeOdd
    (a : Fin 3) (X : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ)
    (hodd : twoReplicaPauliPair a * X * twoReplicaPauliPair a = -X) :
    twoReplicaLocalCollectiveCommutator a X = 0 ↔ X = 0 := by
  have hodd' :
      (twoReplicaPauliLeft a * twoReplicaPauliRight a) * X *
          (twoReplicaPauliLeft a * twoReplicaPauliRight a) = -X := by
    simpa only [twoReplicaPauliLeft_mul_right] using hodd
  exact twoInvolution_collectiveCommutator_eq_zero_iff_of_relativeOdd
    (twoReplicaPauliLeft a) (twoReplicaPauliRight a) X
    (twoReplicaPauliLeft_mul_self a) (twoReplicaPauliRight_mul_self a)
    (by rw [twoReplicaPauliLeft_mul_right, twoReplicaPauliRight_mul_left])
    twoReplicaLocalMatrix_four_isUnit hodd'

abbrev TwoReplicaLocalMatrix :=
  Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ

/-- Paired-Pauli conjugation as a linear map. -/
def twoReplicaPairedPauliConjugationLinear (a : Fin 3) :
    TwoReplicaLocalMatrix →ₗ[ℂ] TwoReplicaLocalMatrix where
  toFun X := twoReplicaPauliPair a * X * twoReplicaPauliPair a
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp

/-- Paired-Pauli conjugation is an involution. -/
theorem twoReplicaPairedPauliConjugationLinear_involutive (a : Fin 3) :
    Function.Involutive (twoReplicaPairedPauliConjugationLinear a) := by
  intro X
  change twoReplicaPauliPair a *
      (twoReplicaPauliPair a * X * twoReplicaPauliPair a) *
        twoReplicaPauliPair a = X
  calc
    twoReplicaPauliPair a *
          (twoReplicaPauliPair a * X * twoReplicaPauliPair a) *
            twoReplicaPauliPair a =
        (twoReplicaPauliPair a * twoReplicaPauliPair a) * X *
          (twoReplicaPauliPair a * twoReplicaPauliPair a) := by
            noncomm_ring
    _ = X := by rw [twoReplicaPauliPair_mul_self]; simp

/-- Paired-Pauli conjugation as a linear equivalence. -/
def twoReplicaPairedPauliConjugationEquiv (a : Fin 3) :
    TwoReplicaLocalMatrix ≃ₗ[ℂ] TwoReplicaLocalMatrix :=
  LinearEquiv.ofInvolutive (twoReplicaPairedPauliConjugationLinear a)
    (twoReplicaPairedPauliConjugationLinear_involutive a)

/-- The three paired-Pauli conjugations commute as operators. -/
theorem twoReplicaPairedPauliConjugationLinear_comm
    (a b : Fin 3) (X : TwoReplicaLocalMatrix) :
    twoReplicaPairedPauliConjugationLinear a
        (twoReplicaPairedPauliConjugationLinear b X) =
      twoReplicaPairedPauliConjugationLinear b
        (twoReplicaPairedPauliConjugationLinear a X) := by
  change twoReplicaPauliPair a *
      (twoReplicaPauliPair b * X * twoReplicaPauliPair b) *
        twoReplicaPauliPair a =
    twoReplicaPauliPair b *
      (twoReplicaPauliPair a * X * twoReplicaPauliPair a) *
        twoReplicaPauliPair b
  calc
    twoReplicaPauliPair a *
          (twoReplicaPauliPair b * X * twoReplicaPauliPair b) *
            twoReplicaPauliPair a =
        (twoReplicaPauliPair a * twoReplicaPauliPair b) * X *
          (twoReplicaPauliPair b * twoReplicaPauliPair a) := by
            noncomm_ring
    _ = (twoReplicaPauliPair b * twoReplicaPauliPair a) * X *
          (twoReplicaPauliPair a * twoReplicaPauliPair b) := by
            rw [twoReplicaPauliPair_comm a b]
    _ = twoReplicaPauliPair b *
          (twoReplicaPauliPair a * X * twoReplicaPauliPair a) *
            twoReplicaPauliPair b := by
              noncomm_ring

/-- Literal collective Pauli commutator as a linear map. -/
def twoReplicaLocalCollectiveCommutatorLinear (a : Fin 3) :
    TwoReplicaLocalMatrix →ₗ[ℂ] TwoReplicaLocalMatrix where
  toFun X := twoReplicaLocalCollectiveCommutator a X
  map_add' X Y := by
    simp [twoReplicaLocalCollectiveCommutator, ringCommutator,
      Matrix.mul_add, Matrix.add_mul]
    module
  map_smul' c X := by
    simp [twoReplicaLocalCollectiveCommutator, ringCommutator]
    module

/-- Relative-odd eigenspace of paired-Pauli conjugation. -/
def twoReplicaRelativeOddSubspace (a : Fin 3) :
    Submodule ℂ TwoReplicaLocalMatrix :=
  LinearMap.ker
    (twoReplicaPairedPauliConjugationLinear a + LinearMap.id)

theorem mem_twoReplicaRelativeOddSubspace_iff
    (a : Fin 3) (X : TwoReplicaLocalMatrix) :
    X ∈ twoReplicaRelativeOddSubspace a ↔
      twoReplicaPauliPair a * X * twoReplicaPauliPair a = -X := by
  change twoReplicaPauliPair a * X * twoReplicaPauliPair a + X = 0 ↔ _
  exact add_eq_zero_iff_eq_neg

/-- Every subspace of a relative-odd Pauli sector is dimension-preserved by
one weight-one collective commutator. -/
theorem twoReplicaRelativeOdd_subspace_finrank
    (a : Fin 3) (U : Submodule ℂ TwoReplicaLocalMatrix)
    (hU : U ≤ twoReplicaRelativeOddSubspace a) :
    Module.finrank ℂ U ≤ Module.finrank ℂ
      (U.map (twoReplicaLocalCollectiveCommutatorLinear a)) := by
  let F : U →ₗ[ℂ]
      U.map (twoReplicaLocalCollectiveCommutatorLinear a) :=
    (twoReplicaLocalCollectiveCommutatorLinear a).domRestrict U |>.codRestrict
      (U.map (twoReplicaLocalCollectiveCommutatorLinear a))
      (fun x => Submodule.mem_map_of_mem x.2)
  have hF : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    have hmem : (x.1 - y.1) ∈ twoReplicaRelativeOddSubspace a :=
      hU (U.sub_mem x.2 y.2)
    have hodd := (mem_twoReplicaRelativeOddSubspace_iff a _).mp hmem
    have hval : twoReplicaLocalCollectiveCommutatorLinear a x.1 =
        twoReplicaLocalCollectiveCommutatorLinear a y.1 :=
      congrArg Subtype.val hxy
    have hzero :
        twoReplicaLocalCollectiveCommutator a (x.1 - y.1) = 0 := by
      change
        twoReplicaLocalCollectiveCommutatorLinear a (x.1 - y.1) = 0
      rw [map_sub, sub_eq_zero]
      exact hval
    have hdiff : x.1 - y.1 = 0 :=
      (twoReplicaLocalCollectiveCommutator_eq_zero_iff_of_relativeOdd
        a _ hodd).mp hzero
    exact sub_eq_zero.mp hdiff
  exact F.finrank_le_finrank_of_injective hF

/-- Every subspace invariant under two paired-Pauli conjugations splits into
its four simultaneous relative-parity sectors. -/
theorem twoReplicaPairedPauliInvariantSubspace_eq_bigrading
    (a b : Fin 3) (U : Submodule ℂ TwoReplicaLocalMatrix)
    (ha : U.map (twoReplicaPairedPauliConjugationLinear a) ≤ U)
    (hb : U.map (twoReplicaPairedPauliConjugationLinear b) ≤ U) :
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
  apply invariantSubspace_eq_commutingInvolution_bigrading
      (twoReplicaPairedPauliConjugationEquiv a)
      (twoReplicaPairedPauliConjugationEquiv b)
  · exact twoReplicaPairedPauliConjugationLinear_involutive a
  · exact twoReplicaPairedPauliConjugationLinear_involutive b
  · exact twoReplicaPairedPauliConjugationLinear_comm a b
  · norm_num
  · exact ha
  · exact hb

end

end GaloisForLFunctions.HTGeometry

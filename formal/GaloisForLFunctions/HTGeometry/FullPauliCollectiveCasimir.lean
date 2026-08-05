import GaloisForLFunctions.HTGeometry.AllReplicaTwoLocalPauliLieGeneration
import GaloisForLFunctions.HTGeometry.LieGeneratedCentralHallExpansion

open scoped BigOperators Matrix
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance matrixLieRing''
    {X : Type*} [Fintype X] [DecidableEq X] :
    LieRing (Matrix X X ℂ) :=
  LieRing.ofAssociativeRing

abbrev NonidentityPauliLabel (n : ℕ) :=
  {s : Fin n → Fin 4 // s ≠ 0}

/-- Structure coefficients of the full nonidentity Pauli basis, recovered by
Hilbert--Schmidt projection. -/
def fullPauliStructureCoeff (n : ℕ)
    (a b k : NonidentityPauliLabel n) : ℂ :=
  ((2 ^ n : ℂ)⁻¹) *
    QuantumAlg.hsInner (QuantumAlg.pauliMat k.1)
      (ringCommutator (QuantumAlg.pauliMat a.1)
        (QuantumAlg.pauliMat b.1))

private theorem pauliXor_ne_zero_of_omega_one
    {n : ℕ} {a b : Fin n → Fin 4}
    (h : QuantumAlg.pauliOmega a b = 1) :
    QuantumAlg.pauliXor a b ≠ 0 := by
  intro hzero
  have hab : b = a := by
    have hx := congrArg (QuantumAlg.pauliXor a) hzero
    simpa [QuantumAlg.pauliXor_self_left,
      QuantumAlg.pauliXor_zero_right] using hx
  rw [hab, QuantumAlg.pauliOmega_self_zero] at h
  norm_num at h

/-- The full Pauli basis closes with its Hilbert--Schmidt structure
coefficients. -/
theorem fullPauli_bracket_expansion
    (n : ℕ) (a b : NonidentityPauliLabel n) :
    ringCommutator (QuantumAlg.pauliMat a.1)
        (QuantumAlg.pauliMat b.1) =
      ∑ k : NonidentityPauliLabel n,
        fullPauliStructureCoeff n a b k • QuantumAlg.pauliMat k.1 := by
  classical
  by_cases homega : QuantumAlg.pauliOmega a.1 b.1 = 1
  · let r : NonidentityPauliLabel n :=
      ⟨QuantumAlg.pauliXor a.1 b.1,
        pauliXor_ne_zero_of_omega_one homega⟩
    have hclosed := QuantumAlg.pauliMat_bracket_closed a.1 b.1
    have hclosed' : ringCommutator (QuantumAlg.pauliMat a.1)
        (QuantumAlg.pauliMat b.1) =
        (QuantumAlg.pauliPhase a.1 b.1 -
          QuantumAlg.pauliPhase b.1 a.1) •
            QuantumAlg.pauliMat (QuantumAlg.pauliXor a.1 b.1) := by
      simpa [Ring.lie_def, ringCommutator] using hclosed
    change ⁅QuantumAlg.pauliMat a.1,
      QuantumAlg.pauliMat b.1⁆ = _
    rw [hclosed]
    rw [Finset.sum_eq_single r]
    · rw [fullPauliStructureCoeff, hclosed',
        QuantumAlg.hsInner_smul_right, QuantumAlg.pauliMat_hsInner]
      have hr : r.1 = QuantumAlg.pauliXor a.1 b.1 := rfl
      rw [if_pos hr]
      have hdim : (2 ^ n : ℂ) ≠ 0 := pow_ne_zero n (by norm_num)
      field_simp
      rw [hr]
    · intro k _ hkr
      rw [fullPauliStructureCoeff, hclosed',
        QuantumAlg.hsInner_smul_right, QuantumAlg.pauliMat_hsInner]
      have hk : k.1 ≠ QuantumAlg.pauliXor a.1 b.1 := by
        intro h
        exact hkr (Subtype.ext h)
      rw [if_neg hk, mul_zero, mul_zero, zero_smul]
    · exact fun h => absurd (Finset.mem_univ r) h
  · have hzero : QuantumAlg.pauliOmega a.1 b.1 = 0 :=
      QuantumAlg.zmod2_ne_one homega
    have hclosed := QuantumAlg.pauliMat_bracket_closed a.1 b.1
    have hclosed' : ringCommutator (QuantumAlg.pauliMat a.1)
        (QuantumAlg.pauliMat b.1) =
        (QuantumAlg.pauliPhase a.1 b.1 -
          QuantumAlg.pauliPhase b.1 a.1) •
            QuantumAlg.pauliMat (QuantumAlg.pauliXor a.1 b.1) := by
      simpa [Ring.lie_def, ringCommutator] using hclosed
    have hcoeff : QuantumAlg.pauliPhase a.1 b.1 -
        QuantumAlg.pauliPhase b.1 a.1 = 0 :=
      QuantumAlg.pauliPhase_sub_eq_zero hzero
    change ⁅QuantumAlg.pauliMat a.1,
      QuantumAlg.pauliMat b.1⁆ = _
    rw [hclosed, hcoeff, zero_smul]
    symm
    apply Finset.sum_eq_zero
    intro k _
    simp [fullPauliStructureCoeff, hclosed', hcoeff]

private theorem trace_triple_cycle
    {X : Type*} [Fintype X] [DecidableEq X]
    (A B C : Matrix X X ℂ) :
    (A * (B * C)).trace = (B * (C * A)).trace := by
  calc
    (A * (B * C)).trace = ((B * C) * A).trace :=
      Matrix.trace_mul_comm A (B * C)
    _ = (B * (C * A)).trace := by rw [Matrix.mul_assoc]

/-- Invariance of the trace pairing makes Pauli structure coefficients
antisymmetric in the two contracted Casimir indices. -/
theorem fullPauliStructureCoeff_antisymmetric_contracted
    (n : ℕ) (a b k : NonidentityPauliLabel n) :
    fullPauliStructureCoeff n k b a =
      -fullPauliStructureCoeff n a b k := by
  let A := QuantumAlg.pauliMat a.1
  let B := QuantumAlg.pauliMat b.1
  let K := QuantumAlg.pauliMat k.1
  have hA : Aᴴ = A := QuantumAlg.pauliMat_isHermitian a.1
  have hK : Kᴴ = K := QuantumAlg.pauliMat_isHermitian k.1
  have htrace : QuantumAlg.hsInner A (ringCommutator K B) =
      -QuantumAlg.hsInner K (ringCommutator A B) := by
    simp only [QuantumAlg.hsInner, hA, hK, ringCommutator,
      Matrix.mul_sub, Matrix.trace_sub]
    rw [trace_triple_cycle A K B,
      trace_triple_cycle A B K,
      trace_triple_cycle B K A]
    ring
  rw [fullPauliStructureCoeff, fullPauliStructureCoeff, htrace]
  ring

/-- Full Pauli direction in the arbitrary-replica vectorized commutator
representation. -/
def finiteReplicaFullPauliCommutatorMatrix
    (R : Type*) [Fintype R] [DecidableEq R]
    (n : ℕ) (q : NonidentityPauliLabel n) :
    Matrix ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n)))
      ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n))) ℂ :=
  finiteReplicaCommutatorMatrixLieHom R (Fin (2 ^ n))
    (QuantumAlg.pauliMat q.1)

theorem finiteTensorLocalMatrix_conjTranspose
    {R D : Type*} [Fintype R] [DecidableEq R]
    [Fintype D] [DecidableEq D]
    (M : R → Matrix D D ℂ) :
    (finiteTensorLocalMatrix M)ᴴ =
      finiteTensorLocalMatrix fun r => (M r)ᴴ := by
  ext x y
  simp only [Matrix.conjTranspose_apply, finiteTensorLocalMatrix]
  rw [← starRingEnd_apply, map_prod]
  rfl

theorem finiteTensorSingleSiteMatrix_conjTranspose
    {R D : Type*} [Fintype R] [DecidableEq R]
    [Fintype D] [DecidableEq D]
    (r : R) (A : Matrix D D ℂ) :
    (finiteTensorSingleSiteMatrix r A)ᴴ =
      finiteTensorSingleSiteMatrix r Aᴴ := by
  rw [finiteTensorSingleSiteMatrix,
    finiteTensorLocalMatrix_conjTranspose]
  congr 1
  funext s
  by_cases hsr : s = r <;> simp [hsr]

theorem finiteReplicaCollectiveMatrix_conjTranspose
    (R D : Type*) [Fintype R] [DecidableEq R]
    [Fintype D] [DecidableEq D]
    (A : Matrix D D ℂ) :
    (finiteReplicaCollectiveMatrix R D A)ᴴ =
      finiteReplicaCollectiveMatrix R D Aᴴ := by
  rw [finiteReplicaCollectiveMatrix, Matrix.conjTranspose_sum,
    finiteReplicaCollectiveMatrix]
  apply Finset.sum_congr rfl
  intro r _
  rw [finiteTensorSingleSiteMatrix_conjTranspose]

theorem finiteReplicaFullPauliCommutatorMatrix_conjTranspose
    (R : Type*) [Fintype R] [DecidableEq R]
    (n : ℕ) (q : NonidentityPauliLabel n) :
    (finiteReplicaFullPauliCommutatorMatrix R n q)ᴴ =
      finiteReplicaFullPauliCommutatorMatrix R n q := by
  change (matrixCommutatorRepresentation
    (finiteReplicaCollectiveMatrix R (Fin (2 ^ n))
      (QuantumAlg.pauliMat q.1)))ᴴ = _
  apply matrixCommutatorRepresentation_conjTranspose
  rw [finiteReplicaCollectiveMatrix_conjTranspose,
    QuantumAlg.pauliMat_isHermitian]

theorem finiteReplicaFullPauliCommutatorMatrix_bracket
    (R : Type*) [Fintype R] [DecidableEq R]
    (n : ℕ) (a b : NonidentityPauliLabel n) :
    ringCommutator
        (finiteReplicaFullPauliCommutatorMatrix R n a)
        (finiteReplicaFullPauliCommutatorMatrix R n b) =
      ∑ k : NonidentityPauliLabel n,
        fullPauliStructureCoeff n a b k •
          finiteReplicaFullPauliCommutatorMatrix R n k := by
  let f := finiteReplicaCommutatorMatrixLieHom R (Fin (2 ^ n))
  have hmap := f.map_lie (QuantumAlg.pauliMat a.1)
    (QuantumAlg.pauliMat b.1)
  have hsource : ⁅QuantumAlg.pauliMat a.1,
      QuantumAlg.pauliMat b.1⁆ =
      ∑ k : NonidentityPauliLabel n,
        fullPauliStructureCoeff n a b k • QuantumAlg.pauliMat k.1 := by
    simpa [Ring.lie_def, ringCommutator] using
      fullPauli_bracket_expansion n a b
  rw [hsource] at hmap
  simpa [f, finiteReplicaFullPauliCommutatorMatrix,
    map_sum, map_smul, Ring.lie_def, ringCommutator] using hmap.symm

/-- The full-system arbitrary-replica Pauli Casimir is central. -/
theorem finiteReplicaFullPauliCommutator_quadraticCasimir_commutes
    (R : Type*) [Fintype R] [DecidableEq R]
    (n : ℕ) (b : NonidentityPauliLabel n) :
    (∑ a : NonidentityPauliLabel n,
        finiteReplicaFullPauliCommutatorMatrix R n a *
          finiteReplicaFullPauliCommutatorMatrix R n a) *
        finiteReplicaFullPauliCommutatorMatrix R n b =
      finiteReplicaFullPauliCommutatorMatrix R n b *
        (∑ a : NonidentityPauliLabel n,
          finiteReplicaFullPauliCommutatorMatrix R n a *
            finiteReplicaFullPauliCommutatorMatrix R n a) := by
  exact quadraticCasimir_commutes_of_antisymmetric_structure
    (finiteReplicaFullPauliCommutatorMatrix R n)
    (fullPauliStructureCoeff n)
    (finiteReplicaFullPauliCommutatorMatrix_bracket R n)
    (fullPauliStructureCoeff_antisymmetric_contracted n)
    b

/-- Exact all-subspace Hall expansion for arbitrary replica order from
weight-two physical generators, modulo only the full collective commutant. -/
theorem finiteReplicaTwoLocalPauli_subspace_finrank_mod_fullCommutant
    (R : Type*) [Fintype R] [DecidableEq R]
    (n : ℕ)
    (U V : Submodule ℂ
      (EuclideanSpace ℂ
        ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n)))))
    (hLV : ∀ A : QuantumAlg.twoLocalPauliMatrices n, ∀ x,
      x ∈ V →
        finiteReplicaCommutatorEndLieHom R (Fin (2 ^ n)) A.1 x ∈ V)
    (hLU : ∀ A : QuantumAlg.twoLocalPauliMatrices n, ∀ x,
      x ∈ U →
        finiteReplicaCommutatorEndLieHom R (Fin (2 ^ n)) A.1 x ∈ V) :
    Module.finrank ℂ U ≤ Module.finrank ℂ V +
      Module.finrank ℂ
        (hermitianMatrixFamilyCommonKernel
          (finiteReplicaFullPauliCommutatorMatrix R n)) := by
  apply lieGeneratedCentralFamily_subspace_finrank_mod_commonKernel
    (fun A : QuantumAlg.twoLocalPauliMatrices n =>
      matrixCommutatorRepresentation
        (finiteReplicaCollectiveMatrix R (Fin (2 ^ n)) A.1))
    (finiteReplicaFullPauliCommutatorMatrix R n)
    (finiteReplicaFullPauliCommutatorMatrix_conjTranspose R n)
    (finiteReplicaFullPauliCommutator_quadraticCasimir_commutes R n)
    ?_ U V hLV hLU
  intro q
  simpa [finiteReplicaFullPauliCommutatorMatrix] using
    (finiteReplicaPauliCommutatorEnd_mem_lieSpan_twoLocal
      R q.1 q.2)

end

end GaloisForLFunctions.HTGeometry

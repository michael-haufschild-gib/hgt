import GaloisForLFunctions.HTGeometry.FiniteReplicaCollectiveCommutantUniversalBound
import GaloisForLFunctions.HTGeometry.FiniteReplicaCollectiveCommutantExact

open scoped BigOperators Matrix
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Pauli strings are linearly independent, directly from their exact
Hilbert--Schmidt Gram matrix.  This local proof keeps the collective-
commutant theorem independent of the orthogonal-DLA development. -/
private theorem fullPauli_linearIndependent (n : ℕ) :
    LinearIndependent ℂ
      (fun s : Fin n → Fin 4 => QuantumAlg.pauliMat s) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc s
  have h1 : QuantumAlg.hsInner (QuantumAlg.pauliMat s)
      (∑ t, c t • QuantumAlg.pauliMat t) = c s * (2 ^ n : ℂ) := by
    rw [QuantumAlg.hsInner_sum_right]
    have hterm : ∀ t, QuantumAlg.hsInner (QuantumAlg.pauliMat s)
        (c t • QuantumAlg.pauliMat t) =
          if s = t then c t * (2 ^ n : ℂ) else 0 := fun t => by
      rw [QuantumAlg.hsInner_smul_right, QuantumAlg.pauliMat_hsInner,
        mul_ite, mul_zero]
    rw [Finset.sum_congr rfl (fun t _ => hterm t), Finset.sum_ite_eq]
    simp
  rw [hc] at h1
  simp only [QuantumAlg.hsInner, Matrix.mul_zero, Matrix.trace_zero] at h1
  exact (mul_eq_zero.mp h1.symm).resolve_right
    (pow_ne_zero n two_ne_zero)

private theorem card_fullPauliIndex (n : ℕ) :
    Fintype.card (Fin n → Fin 4) = 2 ^ n * 2 ^ n := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    show (4 : ℕ) = 2 * 2 from rfl, mul_pow]

/-- The full Pauli family spans every complex matrix on `n` qubits. -/
private theorem fullPauli_span_top (n : ℕ) :
    Submodule.span ℂ
      (Set.range (fun s : Fin n → Fin 4 => QuantumAlg.pauliMat s)) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have hM : Module.finrank ℂ
      (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) = 2 ^ n * 2 ^ n := by
    simp [Module.finrank_matrix]
  rw [finrank_span_eq_card (fullPauli_linearIndependent n),
    card_fullPauliIndex, hM]

abbrev euclideanUnvec
    {C : Type*} [Fintype C]
    (x : EuclideanSpace ℂ (C × C)) : Matrix C C ℂ :=
  fun i j => x.ofLp (j, i)

abbrev euclideanUnvecLinear
    (C : Type*) [Fintype C] :
    EuclideanSpace ℂ (C × C) →ₗ[ℂ] Matrix C C ℂ where
  toFun := euclideanUnvec
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem vec_euclideanUnvec
    {C : Type*} [Fintype C]
    (x : EuclideanSpace ℂ (C × C)) :
    Matrix.vec (euclideanUnvec x) = x.ofLp := rfl

theorem finiteTensorSingleSiteMatrix_one
    {R D : Type*} [Fintype R] [DecidableEq R]
    [Fintype D] [DecidableEq D] (r : R) :
    finiteTensorSingleSiteMatrix r (1 : Matrix D D ℂ) = 1 := by
  rw [finiteTensorSingleSiteMatrix]
  have hfun : (fun s : R => if s = r then (1 : Matrix D D ℂ) else 1) =
      fun _ => 1 := by
    funext s
    simp
  rw [hfun]
  exact finiteTensorLocalMatrix_one

theorem finiteReplicaCollectiveMatrix_one
    (R D : Type*) [Fintype R] [DecidableEq R]
    [Fintype D] [DecidableEq D] :
    finiteReplicaCollectiveMatrix R D (1 : Matrix D D ℂ) =
      (Fintype.card R : ℂ) • 1 := by
  rw [finiteReplicaCollectiveMatrix]
  simp_rw [finiteTensorSingleSiteMatrix_one]
  rw [Finset.sum_const, Finset.card_univ]
  ext x y
  simp [Matrix.one_apply]

abbrev finiteReplicaCollectiveCentralizerAt
    (R D : Type*) [Fintype R] [DecidableEq R]
    [Fintype D] [DecidableEq D]
    (X : Matrix (R → D) (R → D) ℂ) :
    Submodule ℂ (Matrix D D ℂ) where
  carrier := {A | ringCommutator (finiteReplicaCollectiveMatrix R D A) X = 0}
  zero_mem' := by
    change ringCommutator (finiteReplicaCollectiveMatrix R D 0) X = 0
    rw [show finiteReplicaCollectiveMatrix R D 0 = 0 from
      (finiteReplicaCollectiveMatrixLinear R D).map_zero]
    simp [ringCommutator]
  add_mem' := by
    intro A B hA hB
    change ringCommutator (finiteReplicaCollectiveMatrix R D A) X = 0 at hA
    change ringCommutator (finiteReplicaCollectiveMatrix R D B) X = 0 at hB
    change ringCommutator (finiteReplicaCollectiveMatrix R D (A + B)) X = 0
    have hadd := (finiteReplicaCollectiveMatrixLinear R D).map_add A B
    change finiteReplicaCollectiveMatrix R D (A + B) =
      finiteReplicaCollectiveMatrix R D A + finiteReplicaCollectiveMatrix R D B at hadd
    rw [hadd]
    calc
      ringCommutator
          (finiteReplicaCollectiveMatrix R D A + finiteReplicaCollectiveMatrix R D B) X =
          ringCommutator (finiteReplicaCollectiveMatrix R D A) X +
            ringCommutator (finiteReplicaCollectiveMatrix R D B) X := by
        simp only [ringCommutator, Matrix.add_mul, Matrix.mul_add]
        abel
      _ = 0 := by rw [hA, hB, add_zero]
  smul_mem' := by
    intro c A hA
    change ringCommutator (finiteReplicaCollectiveMatrix R D A) X = 0 at hA
    change ringCommutator (finiteReplicaCollectiveMatrix R D (c • A)) X = 0
    have hsmul := (finiteReplicaCollectiveMatrixLinear R D).map_smul c A
    change finiteReplicaCollectiveMatrix R D (c • A) =
      c • finiteReplicaCollectiveMatrix R D A at hsmul
    rw [hsmul]
    calc
      ringCommutator (c • finiteReplicaCollectiveMatrix R D A) X =
          c • ringCommutator (finiteReplicaCollectiveMatrix R D A) X := by
        ext
        simp [ringCommutator, Matrix.mul_apply]
        ring
      _ = 0 := by rw [hA, smul_zero]

theorem finiteReplicaFullPauli_commonKernel_unvec_commutes
    (r n : ℕ)
    (x : hermitianMatrixFamilyCommonKernel
      (finiteReplicaFullPauliCommutatorMatrix (Fin r) n))
    (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    ringCommutator
        (finiteReplicaCollectiveMatrix (Fin r) (Fin (2 ^ n)) A)
        (euclideanUnvec x.1) = 0 := by
  have hpauli : ∀ s : Fin n → Fin 4,
      QuantumAlg.pauliMat s ∈ finiteReplicaCollectiveCentralizerAt
        (Fin r) (Fin (2 ^ n)) (euclideanUnvec x.1) := by
    intro s
    by_cases hs : s = 0
    · subst s
      change ringCommutator
        (finiteReplicaCollectiveMatrix (Fin r) (Fin (2 ^ n))
          (QuantumAlg.pauliMat 0)) (euclideanUnvec x.1) = 0
      have hpzero : QuantumAlg.pauliMat (0 : Fin n → Fin 4) = 1 := by
        rw [QuantumAlg.pauliMat, QuantumAlg.pauliStr_zero,
          Matrix.submatrix_one_equiv]
      rw [hpzero, finiteReplicaCollectiveMatrix_one]
      simp [ringCommutator]
    · let q : NonidentityPauliLabel n := ⟨s, hs⟩
      have hxq :
          (finiteReplicaFullPauliCommutatorMatrix (Fin r) n q).toEuclideanLin x.1 = 0 := by
        apply LinearMap.mem_ker.mp
        have hle : hermitianMatrixFamilyCommonKernel
            (finiteReplicaFullPauliCommutatorMatrix (Fin r) n) ≤
            LinearMap.ker
              (finiteReplicaFullPauliCommutatorMatrix (Fin r) n q).toEuclideanLin :=
          iInf_le _ q
        exact hle x.2
      have hmul :
          finiteReplicaFullPauliCommutatorMatrix (Fin r) n q *ᵥ x.1.ofLp = 0 := by
        have h := congrArg WithLp.ofLp hxq
        exact h
      have hvec : Matrix.vec
          (ringCommutator
            (finiteReplicaCollectiveMatrix (Fin r) (Fin (2 ^ n))
              (QuantumAlg.pauliMat s))
            (euclideanUnvec x.1)) = 0 := by
        rw [← matrixCommutatorRepresentation_mulVec_vec]
        exact hmul
      apply Matrix.vec_inj.mp
      simpa using hvec
  have hspan : Submodule.span ℂ
      (Set.range (fun s : Fin n → Fin 4 => QuantumAlg.pauliMat s)) ≤
      finiteReplicaCollectiveCentralizerAt
        (Fin r) (Fin (2 ^ n)) (euclideanUnvec x.1) := Submodule.span_le.mpr (by
        intro P hP
        obtain ⟨s, rfl⟩ := hP
        exact hpauli s)
  have hA : A ∈ Submodule.span ℂ
      (Set.range (fun s : Fin n → Fin 4 => QuantumAlg.pauliMat s)) := by
    rw [fullPauli_span_top]
    exact Submodule.mem_top
  exact hspan hA

abbrev finiteReplicaFullPauliCommonKernelToCommutant
    (r n : ℕ) :
    hermitianMatrixFamilyCommonKernel
        (finiteReplicaFullPauliCommutatorMatrix (Fin r) n) →ₗ[ℂ]
      finiteReplicaCollectiveCommutant r (2 ^ n) where
  toFun x := ⟨euclideanUnvec x.1, by
    intro b a
    rw [← finiteReplicaCollectiveMatrix_single_eq_replicaMoveMatrix]
    exact sub_eq_zero.mp
      (finiteReplicaFullPauli_commonKernel_unvec_commutes r n x
        (Matrix.single b a 1))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finiteReplicaFullPauliCommonKernelToCommutant_injective
    (r n : ℕ) :
    Function.Injective (finiteReplicaFullPauliCommonKernelToCommutant r n) := by
  intro x y hxy
  apply Subtype.ext
  apply (EuclideanSpace.equiv _ ℂ).injective
  funext p
  have hm := congrArg Subtype.val hxy
  have hp := congrFun (congrFun hm p.2) p.1
  exact hp

/-- In the stable range `r ≤ 2^n`, the simultaneous kernel of every
replicated full-Pauli commutator has dimension at most `r!`. -/
theorem finiteReplicaFullPauli_commonKernel_finrank_le_factorial
    {r n : ℕ} (hrn : r ≤ 2 ^ n) :
    Module.finrank ℂ
      (hermitianMatrixFamilyCommonKernel
        (finiteReplicaFullPauliCommutatorMatrix (Fin r) n)) ≤ Nat.factorial r := by
  calc
    Module.finrank ℂ
        (hermitianMatrixFamilyCommonKernel
          (finiteReplicaFullPauliCommutatorMatrix (Fin r) n)) ≤
        Module.finrank ℂ (finiteReplicaCollectiveCommutant r (2 ^ n)) :=
      LinearMap.finrank_le_finrank_of_injective
        (finiteReplicaFullPauliCommonKernelToCommutant_injective r n)
    _ ≤ Nat.factorial r := finiteReplicaCollectiveCommutant_finrank_le_factorial hrn

/-- In the stable range, every vector surviving all replicated full-Pauli
commutators becomes a linear combination of replica-position permutations
after unvectorization.  Thus the Hall correction has no unidentified sector. -/
theorem finiteReplicaFullPauli_commonKernel_image_mem_replicaPermutationSpan
    {r n : ℕ} (hrn : r ≤ 2 ^ n)
    (x : hermitianMatrixFamilyCommonKernel
      (finiteReplicaFullPauliCommutatorMatrix (Fin r) n)) :
    finiteReplicaFullPauliCommonKernelToCommutant r n x ∈
      Submodule.span ℂ (Set.range
        (fun σ : Equiv.Perm (Fin r) =>
          (⟨replicaPermutationMatrix r (2 ^ n) σ,
            replicaPermutationMatrix_mem_collectiveCommutant
              r (2 ^ n) σ⟩ :
              finiteReplicaCollectiveCommutant r (2 ^ n)))) := by
  rw [replicaPermutationMatrix_span_eq_collectiveCommutant hrn]
  exact Submodule.mem_top

/-- At every finite replica order, with no stable-range assumption, the
simultaneous full-Pauli commutator kernel has dimension at most
`(2^n)^r r!`. -/
theorem finiteReplicaFullPauli_commonKernel_finrank_le_tuple_factorial
    (r n : ℕ) :
    Module.finrank ℂ
      (hermitianMatrixFamilyCommonKernel
        (finiteReplicaFullPauliCommutatorMatrix (Fin r) n)) ≤
      (2 ^ n) ^ r * Nat.factorial r := by
  calc
    Module.finrank ℂ
        (hermitianMatrixFamilyCommonKernel
          (finiteReplicaFullPauliCommutatorMatrix (Fin r) n)) ≤
        Module.finrank ℂ (finiteReplicaCollectiveCommutant r (2 ^ n)) :=
      LinearMap.finrank_le_finrank_of_injective
        (finiteReplicaFullPauliCommonKernelToCommutant_injective r n)
    _ ≤ (2 ^ n) ^ r * Nat.factorial r :=
      finiteReplicaCollectiveCommutant_finrank_le_tuple_factorial r (2 ^ n)

/-- Quantitative arbitrary-subspace Hall expansion from physical two-local
Pauli directions.  In the stable replica range, the only possible rank loss
is at most the factorial dimension of the replica-permutation sector. -/
theorem finiteReplicaTwoLocalPauli_subspace_finrank_le_add_factorial
    {r n : ℕ} (hrn : r ≤ 2 ^ n)
    (U V : Submodule ℂ
      (EuclideanSpace ℂ
        (((Fin r → Fin (2 ^ n)) × (Fin r → Fin (2 ^ n))))))
    (hLV : ∀ A : QuantumAlg.twoLocalPauliMatrices n, ∀ x,
      x ∈ V →
        finiteReplicaCommutatorEndLieHom (Fin r) (Fin (2 ^ n)) A.1 x ∈ V)
    (hLU : ∀ A : QuantumAlg.twoLocalPauliMatrices n, ∀ x,
      x ∈ U →
        finiteReplicaCommutatorEndLieHom (Fin r) (Fin (2 ^ n)) A.1 x ∈ V) :
    Module.finrank ℂ U ≤ Module.finrank ℂ V + Nat.factorial r := by
  refine le_trans
    (finiteReplicaTwoLocalPauli_subspace_finrank_mod_fullCommutant
      (Fin r) n U V hLV hLU) ?_
  exact Nat.add_le_add_left
    (finiteReplicaFullPauli_commonKernel_finrank_le_factorial hrn) _

/-- Universal arbitrary-subspace Hall expansion from physical two-local
Pauli directions.  For every finite physical and replica register, the total
rank loss is bounded by the exact tuple-orbit count `(2^n)^r r!`. -/
theorem finiteReplicaTwoLocalPauli_subspace_finrank_le_add_tuple_factorial
    (r n : ℕ)
    (U V : Submodule ℂ
      (EuclideanSpace ℂ
        (((Fin r → Fin (2 ^ n)) × (Fin r → Fin (2 ^ n))))))
    (hLV : ∀ A : QuantumAlg.twoLocalPauliMatrices n, ∀ x,
      x ∈ V →
        finiteReplicaCommutatorEndLieHom (Fin r) (Fin (2 ^ n)) A.1 x ∈ V)
    (hLU : ∀ A : QuantumAlg.twoLocalPauliMatrices n, ∀ x,
      x ∈ U →
        finiteReplicaCommutatorEndLieHom (Fin r) (Fin (2 ^ n)) A.1 x ∈ V) :
    Module.finrank ℂ U ≤
      Module.finrank ℂ V + (2 ^ n) ^ r * Nat.factorial r := by
  refine le_trans
    (finiteReplicaTwoLocalPauli_subspace_finrank_mod_fullCommutant
      (Fin r) n U V hLV hLU) ?_
  exact Nat.add_le_add_left
    (finiteReplicaFullPauli_commonKernel_finrank_le_tuple_factorial r n) _

end
end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.FullPauliCollectiveCommutantBound
import Mathlib.Algebra.Algebra.Operations

/-!
# Linear-depth replicated local-Pauli Hall expansion

Every nonidentity full Pauli direction has a constructive nested-commutator
decomposition through one- and two-local Pauli directions.  This file retains
that depth instead of passing directly to an unfiltered Lie span.  At most
`n` local factors suffice on an `n`-qubit register.  The full central-Casimir
Hall law then yields an `n`-step subspace expansion theorem at every finite
replica order, with only the collective commutant as defect.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Linear span of the identity and all replicated physical one- and two-local
Pauli commutator endomorphisms. -/
def finiteReplicaTwoLocalPauliEndGeneratorSpan
    (R : Type*) [Fintype R] [DecidableEq R] (n : ℕ) :
    Submodule ℂ
      (Module.End ℂ (EuclideanSpace ℂ
        ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n))))) :=
  Submodule.span ℂ
    (Set.insert 1
      (Set.range fun A : QuantumAlg.twoLocalPauliMatrices n =>
        finiteReplicaCommutatorEndLieHom R (Fin (2 ^ n)) A.1))

theorem one_le_finiteReplicaTwoLocalPauliEndGeneratorSpan
    (R : Type*) [Fintype R] [DecidableEq R] (n : ℕ) :
    1 ≤ finiteReplicaTwoLocalPauliEndGeneratorSpan R n := by
  rw [Submodule.one_le]
  apply Submodule.subset_span
  exact Set.mem_insert 1 _

theorem finiteReplicaTwoLocalPauliEnd_mem_generatorSpan
    (R : Type*) [Fintype R] [DecidableEq R]
    {n : ℕ} (A : QuantumAlg.twoLocalPauliMatrices n) :
    finiteReplicaCommutatorEndLieHom R (Fin (2 ^ n)) A.1 ∈
      finiteReplicaTwoLocalPauliEndGeneratorSpan R n := by
  apply Submodule.subset_span
  exact Set.mem_insert_iff.mpr (.inr ⟨A, rfl⟩)

theorem pauliWeight4_pos_of_ne_zero
    {n : ℕ} (s : Fin n → Fin 4) (hs : s ≠ 0) :
    0 < QuantumAlg.pauliWeight4 s := by
  rw [Nat.pos_iff_ne_zero]
  intro hw
  apply hs
  funext i
  by_contra hi
  have himem : i ∈ QuantumAlg.pauliSupport4 s := by
    simpa using hi
  have hempty : QuantumAlg.pauliSupport4 s = ∅ :=
    Finset.card_eq_zero.mp hw
  rw [hempty] at himem
  simp at himem

theorem pauliWeight4_le_card
    {n : ℕ} (s : Fin n → Fin 4) :
    QuantumAlg.pauliWeight4 s ≤ n := by
  rw [QuantumAlg.pauliWeight4]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
    (Fintype.card_fin n)

/-- A replicated Pauli direction of physical weight `w` lies in the `w`th
associative power of the local generator span. -/
theorem finiteReplicaPauliCommutatorEnd_mem_generatorSpan_pow_weight
    (R : Type*) [Fintype R] [DecidableEq R]
    {n : ℕ} (s : Fin n → Fin 4) (hs : s ≠ 0) :
    finiteReplicaCommutatorEndLieHom R (Fin (2 ^ n)) (QuantumAlg.pauliMat s) ∈
      (finiteReplicaTwoLocalPauliEndGeneratorSpan R n) ^
        QuantumAlg.pauliWeight4 s := by
  classical
  let S := finiteReplicaTwoLocalPauliEndGeneratorSpan R n
  let f := finiteReplicaCommutatorEndLieHom R (Fin (2 ^ n))
  induction hweight : QuantumAlg.pauliWeight4 s using Nat.strong_induction_on generalizing s with
  | h w ih =>
      by_cases hsmall : w ≤ 2
      · let A : QuantumAlg.twoLocalPauliMatrices n :=
          ⟨QuantumAlg.pauliMat s, ⟨s, hs, by simpa [hweight] using hsmall, rfl⟩⟩
        have hA : f (QuantumAlg.pauliMat s) ∈ S := by
          exact finiteReplicaTwoLocalPauliEnd_mem_generatorSpan R A
        have hpos : 0 < w := by
          simpa [hweight] using pauliWeight4_pos_of_ne_zero s hs
        have hmono : S ^ (1 : ℕ) ≤ S ^ w :=
          pow_le_pow_right' (a := S)
            (one_le_finiteReplicaTwoLocalPauliEndGeneratorSpan R n)
            hpos
        rw [Submodule.pow_one] at hmono
        exact hmono hA
      · have hlarge : 2 < QuantumAlg.pauliWeight4 s := by omega
        obtain ⟨t, u, ht, hu, htWeight, huWeight, htu, hxor⟩ :=
          QuantumAlg.exists_pauliWeightTwo_anticommuting_decomposition s hlarge
        have htmem : f (QuantumAlg.pauliMat t) ∈
            S ^ QuantumAlg.pauliWeight4 t := by
          exact ih (QuantumAlg.pauliWeight4 t)
            (by simpa [hweight] using htWeight) t ht rfl
        let A : QuantumAlg.twoLocalPauliMatrices n :=
          ⟨QuantumAlg.pauliMat u, ⟨u, hu, huWeight.le, rfl⟩⟩
        have humem : f (QuantumAlg.pauliMat u) ∈ S ^ (1 : ℕ) := by
          rw [Submodule.pow_one]
          exact finiteReplicaTwoLocalPauliEnd_mem_generatorSpan R A
        have hprod1 :
            f (QuantumAlg.pauliMat t) * f (QuantumAlg.pauliMat u) ∈
              S ^ (QuantumAlg.pauliWeight4 t + 1) := by
          rw [S.pow_add (by norm_num : (1 : ℕ) ≠ 0)]
          exact Submodule.mul_mem_mul htmem humem
        have hprod2 :
            f (QuantumAlg.pauliMat u) * f (QuantumAlg.pauliMat t) ∈
              S ^ (QuantumAlg.pauliWeight4 t + 1) := by
          rw [add_comm, S.pow_add (pauliWeight4_pos_of_ne_zero t ht).ne']
          exact Submodule.mul_mem_mul humem htmem
        have hbracket : ⁅f (QuantumAlg.pauliMat t), f (QuantumAlg.pauliMat u)⁆ ∈
            S ^ (QuantumAlg.pauliWeight4 t + 1) := by
          simpa [Ring.lie_def] using
            (Submodule.sub_mem (S ^ (QuantumAlg.pauliWeight4 t + 1)) hprod1 hprod2)
        have hmap := f.map_lie (QuantumAlg.pauliMat t) (QuantumAlg.pauliMat u)
        rw [QuantumAlg.pauliMat_bracket_closed, hxor] at hmap
        simp only [map_smul] at hmap
        let c := QuantumAlg.pauliPhase t u - QuantumAlg.pauliPhase u t
        have hc : c ≠ 0 := QuantumAlg.pauliPhase_sub_ne_zero htu
        have hscaled : f (QuantumAlg.pauliMat s) ∈
            S ^ (QuantumAlg.pauliWeight4 t + 1) := by
          have hcbracket : c • f (QuantumAlg.pauliMat s) ∈
              S ^ (QuantumAlg.pauliWeight4 t + 1) := by
            simpa [c] using hmap.symm ▸ hbracket
          have hinv := (S ^ (QuantumAlg.pauliWeight4 t + 1)).smul_mem c⁻¹ hcbracket
          simpa [hc] using hinv
        have hdepth : QuantumAlg.pauliWeight4 t + 1 ≤ w := by
          omega
        have hone : 1 ≤ S :=
          one_le_finiteReplicaTwoLocalPauliEndGeneratorSpan R n
        have hmono : S ^ (QuantumAlg.pauliWeight4 t + 1) ≤ S ^ w :=
          pow_le_pow_right' (a := S) hone hdepth
        exact hmono hscaled

/-- Image of a vector subspace under every endomorphism in an operator
submodule. -/
def endomorphismSubmoduleImage
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (S : Submodule 𝕜 (Module.End 𝕜 V)) (U : Submodule 𝕜 V) :
    Submodule 𝕜 V :=
  ⨆ T : S, U.map T.1

theorem endomorphism_mem_endomorphismSubmoduleImage
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    {S : Submodule 𝕜 (Module.End 𝕜 V)} {U : Submodule 𝕜 V}
    {T : Module.End 𝕜 V} (hT : T ∈ S) {x : V} (hx : x ∈ U) :
    T x ∈ endomorphismSubmoduleImage S U := by
  apply Submodule.mem_iSup_of_mem (⟨T, hT⟩ : S)
  exact ⟨x, hx, rfl⟩

/-- Subspace reached from `U` by complex linear combinations of products of
at most `k` replicated physical one- and two-local commutator directions. -/
def finiteReplicaTwoLocalPauliWordShadow
    (R : Type*) [Fintype R] [DecidableEq R] (n k : ℕ)
    (U : Submodule ℂ
      (EuclideanSpace ℂ ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n))))) :
    Submodule ℂ
      (EuclideanSpace ℂ ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n)))) :=
  endomorphismSubmoduleImage
    ((finiteReplicaTwoLocalPauliEndGeneratorSpan R n) ^ k) U

theorem finiteReplicaFullPauliCommutator_mem_wordShadow
    (R : Type*) [Fintype R] [DecidableEq R]
    (n : ℕ)
    (U : Submodule ℂ
      (EuclideanSpace ℂ ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n)))))
    (q : NonidentityPauliLabel n) {x} (hx : x ∈ U) :
    (finiteReplicaFullPauliCommutatorMatrix R n q).toEuclideanLin x ∈
      finiteReplicaTwoLocalPauliWordShadow R n n U := by
  let S := finiteReplicaTwoLocalPauliEndGeneratorSpan R n
  have hweight := finiteReplicaPauliCommutatorEnd_mem_generatorSpan_pow_weight
    R q.1 q.2
  have hone : 1 ≤ S :=
    one_le_finiteReplicaTwoLocalPauliEndGeneratorSpan R n
  have hmono : S ^ QuantumAlg.pauliWeight4 q.1 ≤ S ^ n :=
    pow_le_pow_right' (a := S) hone (pauliWeight4_le_card q.1)
  have hfull :
      finiteReplicaCommutatorEndLieHom R (Fin (2 ^ n))
          (QuantumAlg.pauliMat q.1) ∈ S ^ n :=
    hmono hweight
  apply endomorphism_mem_endomorphismSubmoduleImage hfull hx

/-- **Linear-depth all-replica Hall law.** After at most `n` physical
one- and two-local commutator factors, every source subspace expands modulo
only the exact full collective commutant. -/
theorem finiteReplicaTwoLocalPauliWordShadow_finrank_mod_fullCommutant
    (R : Type*) [Fintype R] [DecidableEq R]
    (n : ℕ)
    (U : Submodule ℂ
      (EuclideanSpace ℂ ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n))))) :
    Module.finrank ℂ U ≤
      Module.finrank ℂ (finiteReplicaTwoLocalPauliWordShadow R n n U) +
        Module.finrank ℂ
          (hermitianMatrixFamilyCommonKernel
            (finiteReplicaFullPauliCommutatorMatrix R n)) := by
  apply centralHermitianMatrixFamily_subspace_finrank_mod_commonKernel
    (finiteReplicaFullPauliCommutatorMatrix R n)
    (finiteReplicaFullPauliCommutatorMatrix_conjTranspose R n)
    (finiteReplicaFullPauliCommutator_quadraticCasimir_commutes R n)
  intro q x hx
  exact finiteReplicaFullPauliCommutator_mem_wordShadow R n U q hx

/-- Stable-range linear-depth Hall law with only the factorial
replica-permutation defect. -/
theorem finiteReplicaTwoLocalPauliWordShadow_finrank_le_add_factorial
    {r n : ℕ} (hrn : r ≤ 2 ^ n)
    (U : Submodule ℂ
      (EuclideanSpace ℂ
        ((Fin r → Fin (2 ^ n)) × (Fin r → Fin (2 ^ n))))) :
    Module.finrank ℂ U ≤
      Module.finrank ℂ
          (finiteReplicaTwoLocalPauliWordShadow (Fin r) n n U) +
        Nat.factorial r := by
  refine le_trans
    (finiteReplicaTwoLocalPauliWordShadow_finrank_mod_fullCommutant
      (Fin r) n U) ?_
  exact Nat.add_le_add_left
    (finiteReplicaFullPauli_commonKernel_finrank_le_factorial hrn) _

/-- Universal all-order linear-depth Hall law with the tuple-orbit defect. -/
theorem finiteReplicaTwoLocalPauliWordShadow_finrank_le_add_tuple_factorial
    (r n : ℕ)
    (U : Submodule ℂ
      (EuclideanSpace ℂ
        ((Fin r → Fin (2 ^ n)) × (Fin r → Fin (2 ^ n))))) :
    Module.finrank ℂ U ≤
      Module.finrank ℂ
          (finiteReplicaTwoLocalPauliWordShadow (Fin r) n n U) +
        (2 ^ n) ^ r * Nat.factorial r := by
  refine le_trans
    (finiteReplicaTwoLocalPauliWordShadow_finrank_mod_fullCommutant
      (Fin r) n U) ?_
  exact Nat.add_le_add_left
    (finiteReplicaFullPauli_commonKernel_finrank_le_tuple_factorial r n) _

end

end GaloisForLFunctions.HTGeometry

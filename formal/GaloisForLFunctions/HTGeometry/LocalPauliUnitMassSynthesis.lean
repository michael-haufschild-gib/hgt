import GaloisForLFunctions.HTGeometry.AllReplicaPauliLeakageLaw
import GaloisForLFunctions.HTGeometry.FiniteReplicaTwoLocalPauliWordHall
import GaloisForLFunctions.HTGeometry.PauliXorIncidenceHypercontractivityLaw

/-!
# Unit-mass local synthesis of every replicated Pauli direction

A Pauli string of weight past two is the halved bracket of a strictly lighter string with a
weight-two string that anticommutes with it, and the anticommutation forces the bracket
coefficient to have modulus exactly two.  The bracket therefore makes two copies of a product and
halves each, so a combination of unit `ℓ¹` coefficient mass stays at mass one.

Grading the word set by the number of local factors, strong induction on the physical Pauli weight
gives every replicated commutator direction of weight `w` a unit-mass synthesis over words of
length at most `w`, hence at most `n` on an `n`-qubit register.
-/

open scoped BigOperators Matrix Pointwise

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Generic

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- Enlarging the word set preserves a unit-mass synthesis. -/
theorem hasUnitMassSynthesis_mono {S T : Set A} (hST : S ⊆ T) {a : A}
    (h : HasUnitMassSynthesis S a) : HasUnitMassSynthesis T a := by
  obtain ⟨ι, hι, c, w, hw, hcm, hae⟩ := h
  exact ⟨ι, hι, c, w, fun i => hST (hw i), hcm, hae⟩

/-- **Unit mass survives the halved bracket, with word length added.**  The two factor sets may
differ, provided both orders of their products land in the target set. -/
theorem hasUnitMassSynthesis_bracket_of_mem {S T U : Set A}
    (hST : ∀ x ∈ S, ∀ y ∈ T, x * y ∈ U) (hTS : ∀ y ∈ T, ∀ x ∈ S, y * x ∈ U)
    {a b : A} (ha : HasUnitMassSynthesis S a) (hb : HasUnitMassSynthesis T b)
    {ζ : ℂ} (hζ : ‖ζ‖ = 2) :
    HasUnitMassSynthesis U (ζ⁻¹ • (a * b - b * a)) := by
  obtain ⟨ι, hι, c, w, hw, hcm, hae⟩ := ha
  obtain ⟨κ, hκ, e, v, hv, hem, hbe⟩ := hb
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hζ
    norm_num at hζ
  classical
  refine ⟨(ι × κ) ⊕ (ι × κ), inferInstance,
    Sum.elim (fun p => ζ⁻¹ * c p.1 * e p.2) (fun p => -(ζ⁻¹ * c p.1 * e p.2)),
    Sum.elim (fun p => w p.1 * v p.2) (fun p => v p.2 * w p.1),
    ?_, ?_, ?_⟩
  · rintro (p | p)
    · exact hST _ (hw p.1) _ (hv p.2)
    · exact hTS _ (hv p.2) _ (hw p.1)
  · have hhalf : ‖ζ⁻¹‖ = 1 / 2 := by
      rw [norm_inv, hζ]
      norm_num
    have hpiece : ∑ p : ι × κ, ‖ζ⁻¹ * c p.1 * e p.2‖ = 1 / 2 := by
      have hterm : ∀ p : ι × κ, ‖ζ⁻¹ * c p.1 * e p.2‖ = ‖ζ⁻¹‖ * (‖c p.1‖ * ‖e p.2‖) := by
        intro p
        rw [norm_mul, norm_mul, mul_assoc]
      rw [Finset.sum_congr rfl fun p _ => hterm p, ← Finset.mul_sum, Fintype.sum_prod_type]
      have hinner : ∀ i : ι, ∑ j : κ, ‖c i‖ * ‖e j‖ = ‖c i‖ := by
        intro i
        rw [← Finset.mul_sum, hem, mul_one]
      rw [Finset.sum_congr rfl fun i _ => hinner i, hcm, hhalf, mul_one]
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, norm_neg]
    rw [hpiece]
    norm_num
  · have hAB : ∑ p : ι × κ, (ζ⁻¹ * c p.1 * e p.2) • (w p.1 * v p.2) = ζ⁻¹ • (a * b) := by
      rw [hae, hbe, Finset.sum_mul_sum, Finset.smul_sum, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_mul_smul, smul_smul, mul_assoc]
    have hBA : ∑ p : ι × κ, (ζ⁻¹ * c p.1 * e p.2) • (v p.2 * w p.1) = ζ⁻¹ • (b * a) := by
      rw [hae, hbe, Finset.sum_mul_sum, Finset.smul_sum, Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_mul_smul, smul_smul]
      ring_nf
    have hneg : ∑ p : ι × κ, (-(ζ⁻¹ * c p.1 * e p.2)) • (v p.2 * w p.1) = -(ζ⁻¹ • (b * a)) := by
      rw [← hBA, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun p _ => neg_smul _ _
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [hAB, hneg, smul_sub]
    abel

/-- Every power of a set containing the identity contains the identity. -/
theorem one_mem_setPow {G : Set A} (hG : (1 : A) ∈ G) : ∀ k : ℕ, (1 : A) ∈ G ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      simpa using Set.mul_mem_mul ih hG

/-- Padding by the identity embeds shorter words among longer ones. -/
theorem setPow_subset_setPow {G : Set A} (hG : (1 : A) ∈ G) {k m : ℕ} (hkm : k ≤ m) :
    G ^ k ⊆ G ^ m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
  intro x hx
  rw [pow_add]
  simpa using Set.mul_mem_mul hx (one_mem_setPow hG d)

end Generic

section Pauli

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [Fintype R] [DecidableEq R] (n : ℕ)

/-- The vectorized collective commutator of a Pauli string at arbitrary replica order. -/
def replicaCommutatorMat (s : Fin n → Fin 4) :
    Matrix ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n)))
      ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n))) ℂ :=
  matrixCommutatorRepresentation
    (finiteReplicaCollectiveMatrix R (Fin (2 ^ n)) (QuantumAlg.pauliMat s))

/-- The named full-Pauli commutator matrices are the commutator matrices of their labels. -/
theorem finiteReplicaFullPauliCommutatorMatrix_eq_replicaCommutatorMat
    (q : NonidentityPauliLabel n) :
    finiteReplicaFullPauliCommutatorMatrix R n q = replicaCommutatorMat R n q.1 := rfl

/-- **The replicated commutator directions close under the bracket**, with the physical Pauli
string phase as the single coefficient. -/
theorem replicaCommutatorMat_bracket (s t : Fin n → Fin 4) :
    replicaCommutatorMat R n s * replicaCommutatorMat R n t
        - replicaCommutatorMat R n t * replicaCommutatorMat R n s
      = (QuantumAlg.pauliPhase s t - QuantumAlg.pauliPhase t s)
          • replicaCommutatorMat R n (QuantumAlg.pauliXor s t) := by
  have hphys : QuantumAlg.pauliMat s * QuantumAlg.pauliMat t
      - QuantumAlg.pauliMat t * QuantumAlg.pauliMat s
      = (QuantumAlg.pauliPhase s t - QuantumAlg.pauliPhase t s)
          • QuantumAlg.pauliMat (QuantumAlg.pauliXor s t) := by
    have h := QuantumAlg.pauliMat_bracket_closed s t
    rwa [Ring.lie_def] at h
  have hcoll : finiteReplicaCollectiveMatrix R (Fin (2 ^ n)) (QuantumAlg.pauliMat s) *
        finiteReplicaCollectiveMatrix R (Fin (2 ^ n)) (QuantumAlg.pauliMat t) -
      finiteReplicaCollectiveMatrix R (Fin (2 ^ n)) (QuantumAlg.pauliMat t) *
        finiteReplicaCollectiveMatrix R (Fin (2 ^ n)) (QuantumAlg.pauliMat s)
      = finiteReplicaCollectiveMatrix R (Fin (2 ^ n))
          (QuantumAlg.pauliMat s * QuantumAlg.pauliMat t
            - QuantumAlg.pauliMat t * QuantumAlg.pauliMat s) :=
    finiteReplicaCollectiveMatrix_bracket R (Fin (2 ^ n)) _ _
  have hsmulC : finiteReplicaCollectiveMatrix R (Fin (2 ^ n))
      ((QuantumAlg.pauliPhase s t - QuantumAlg.pauliPhase t s)
        • QuantumAlg.pauliMat (QuantumAlg.pauliXor s t))
      = (QuantumAlg.pauliPhase s t - QuantumAlg.pauliPhase t s) •
        finiteReplicaCollectiveMatrix R (Fin (2 ^ n))
          (QuantumAlg.pauliMat (QuantumAlg.pauliXor s t)) :=
    (finiteReplicaCollectiveMatrixLinear R (Fin (2 ^ n))).map_smul _ _
  rw [replicaCommutatorMat, replicaCommutatorMat, replicaCommutatorMat,
    matrixCommutatorRepresentation_bracket, hcoll, hphys, hsmulC, map_smul]

/-- Identity together with every replicated Pauli commutator of physical weight at most two. -/
def twoLocalReplicaCommutatorSet :
    Set (Matrix ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n)))
      ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n))) ℂ) :=
  insert 1 {M | ∃ s : Fin n → Fin 4, s ≠ 0 ∧ QuantumAlg.pauliWeight4 s ≤ 2 ∧
    M = replicaCommutatorMat R n s}

/-- Anticommutation makes the bracket coefficient have modulus exactly two. -/
theorem norm_pauliPhase_sub {m : ℕ} {s t : Fin m → Fin 4}
    (h : QuantumAlg.pauliOmega s t = 1) :
    ‖QuantumAlg.pauliPhase s t - QuantumAlg.pauliPhase t s‖ = 2 := by
  rw [QuantumAlg.pauliPhase_swap s t, h, QuantumAlg.negOnePow_one, neg_one_mul, sub_neg_eq_add,
    ← two_mul, norm_mul, norm_pauliPhase]
  norm_num

/-- **Lemma D -- unit-mass local synthesis.**  Every replicated Pauli commutator direction of
physical weight `w` is a unit-`ℓ¹`-mass combination of words of length at most `w` in the
identity and the replicated one- and two-local commutator directions. -/
theorem replicaCommutatorMat_hasUnitMassSynthesis (s : Fin n → Fin 4) (hs : s ≠ 0) :
    HasUnitMassSynthesis (twoLocalReplicaCommutatorSet R n ^ QuantumAlg.pauliWeight4 s)
      (replicaCommutatorMat R n s) := by
  classical
  have hone : (1 : Matrix ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n)))
      ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n))) ℂ) ∈ twoLocalReplicaCommutatorSet R n :=
    Set.mem_insert _ _
  induction hweight : QuantumAlg.pauliWeight4 s using Nat.strong_induction_on generalizing s with
  | h w ih =>
      subst hweight
      by_cases hsmall : QuantumAlg.pauliWeight4 s ≤ 2
      · have hmem : replicaCommutatorMat R n s ∈ twoLocalReplicaCommutatorSet R n :=
          Set.mem_insert_of_mem _ ⟨s, hs, by omega, rfl⟩
        refine hasUnitMassSynthesis_mono
          (setPow_subset_setPow hone (pauliWeight4_pos_of_ne_zero s hs)) ?_
        refine hasUnitMassSynthesis_of_mem ?_
        rw [pow_one]
        exact hmem
      · have hlarge : 2 < QuantumAlg.pauliWeight4 s := by omega
        obtain ⟨t, u, ht, hu, htW, huW, homega, hxor⟩ :=
          QuantumAlg.exists_pauliWeightTwo_anticommuting_decomposition s hlarge
        have hIH : HasUnitMassSynthesis
            (twoLocalReplicaCommutatorSet R n ^ QuantumAlg.pauliWeight4 t)
            (replicaCommutatorMat R n t) := ih (QuantumAlg.pauliWeight4 t) (by omega) t ht rfl
        have humem : replicaCommutatorMat R n u ∈ twoLocalReplicaCommutatorSet R n :=
          Set.mem_insert_of_mem _ ⟨u, hu, huW.le, rfl⟩
        have hu1 : HasUnitMassSynthesis (twoLocalReplicaCommutatorSet R n ^ 1)
            (replicaCommutatorMat R n u) := by
          refine hasUnitMassSynthesis_of_mem ?_
          rw [pow_one]
          exact humem
        have hzne : QuantumAlg.pauliPhase t u - QuantumAlg.pauliPhase u t ≠ 0 :=
          QuantumAlg.pauliPhase_sub_ne_zero homega
        have hznorm : ‖QuantumAlg.pauliPhase t u - QuantumAlg.pauliPhase u t‖ = 2 :=
          norm_pauliPhase_sub homega
        have hb := replicaCommutatorMat_bracket R n t u
        rw [hxor] at hb
        have hrep : replicaCommutatorMat R n s
            = (QuantumAlg.pauliPhase t u - QuantumAlg.pauliPhase u t)⁻¹ •
                (replicaCommutatorMat R n t * replicaCommutatorMat R n u
                  - replicaCommutatorMat R n u * replicaCommutatorMat R n t) := by
          rw [hb, smul_smul, inv_mul_cancel₀ hzne, one_smul]
        have hST : ∀ x ∈ twoLocalReplicaCommutatorSet R n ^ QuantumAlg.pauliWeight4 t,
            ∀ y ∈ twoLocalReplicaCommutatorSet R n ^ 1,
            x * y ∈ twoLocalReplicaCommutatorSet R n ^ (QuantumAlg.pauliWeight4 t + 1) := by
          intro x hx y hy
          rw [pow_add]
          exact Set.mul_mem_mul hx hy
        have hTS : ∀ y ∈ twoLocalReplicaCommutatorSet R n ^ 1,
            ∀ x ∈ twoLocalReplicaCommutatorSet R n ^ QuantumAlg.pauliWeight4 t,
            y * x ∈ twoLocalReplicaCommutatorSet R n ^ (QuantumAlg.pauliWeight4 t + 1) := by
          intro y hy x hx
          rw [show QuantumAlg.pauliWeight4 t + 1 = 1 + QuantumAlg.pauliWeight4 t from by omega,
            pow_add]
          exact Set.mul_mem_mul hy hx
        rw [hrep]
        refine hasUnitMassSynthesis_mono
          (setPow_subset_setPow hone
            (by omega : QuantumAlg.pauliWeight4 t + 1 ≤ QuantumAlg.pauliWeight4 s)) ?_
        exact hasUnitMassSynthesis_bracket_of_mem hST hTS hIH hu1 hznorm

/-- **Lemma D at the uniform word length `n`.** -/
theorem finiteReplicaFullPauliCommutatorMatrix_hasUnitMassSynthesis
    (q : NonidentityPauliLabel n) :
    HasUnitMassSynthesis (twoLocalReplicaCommutatorSet R n ^ n)
      (finiteReplicaFullPauliCommutatorMatrix R n q) := by
  refine hasUnitMassSynthesis_mono
    (setPow_subset_setPow (Set.mem_insert _ _) (pauliWeight4_le_card q.1)) ?_
  exact replicaCommutatorMat_hasUnitMassSynthesis R n q.1 q.2

end Pauli

end

end GaloisForLFunctions.HTGeometry

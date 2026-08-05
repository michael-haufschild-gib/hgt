import GaloisForLFunctions.HTGeometry.TwoReplicaGlobalCliffordTwirlRange
import GaloisForLFunctions.HTGeometry.FinitePauliCharacterProjector
import GaloisForLFunctions.HTGeometry.VisibleKernelRecoveryHallExpansion

/-!
# Aggregate visible quotient detector for two-replica Pauli families

All cutoff-family images of a zero-character source are summed before
quotienting by occupied nonsinglet input. Exact Pauli-character projectors
prove that this aggregation loses no hidden component whenever the quotient
subspace is paired-Pauli invariant.
-/

open scoped BigOperators Matrix Kronecker
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open QuantumAlg

/-- Full Pauli-word indexing of the weight-at-most-`q` collective family;
words above cutoff act by zero. -/
def finiteTwoReplicaPauliCutoffCollective
    (σ : Type*) [Fintype σ] [DecidableEq σ]
    (q : ℕ) (P : σ → Option (Fin 3)) :
    FiniteTwoReplicaMatrix σ →ₗ[ℂ] FiniteTwoReplicaMatrix σ :=
  if finitePauliWeight P ≤ q then
    finiteTwoReplicaCollectiveCommutatorLinear P
  else 0

/-- Sum of every cutoff collective commutator, used as one quotient detector. -/
def finiteTwoReplicaPauliCutoffAggregate
    (σ : Type*) [Fintype σ] [DecidableEq σ]
    (q : ℕ) :
    FiniteTwoReplicaMatrix σ →ₗ[ℂ] FiniteTwoReplicaMatrix σ :=
  ∑ P : σ → Option (Fin 3),
    finiteTwoReplicaPauliCutoffCollective σ q P

/-- Full-word zero extension and subtype-indexed `q`-local families have the
same one-step shadow on every subspace. -/
theorem linearFamilyShadow_pauliCutoff_eq_qlocal
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ℕ) (U : Submodule ℂ (FiniteTwoReplicaMatrix σ)) :
    linearFamilyShadow
        (finiteTwoReplicaPauliCutoffCollective σ q) U =
      linearFamilyShadow
        (finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q) U := by
  apply le_antisymm
  · apply iSup_le
    intro P
    by_cases hP : finitePauliWeight P ≤ q
    · rw [finiteTwoReplicaPauliCutoffCollective, if_pos hP]
      exact le_iSup
        (fun R : FiniteQLocalPauliLabel σ q =>
          U.map (finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q R))
        ⟨P, hP⟩
    · rw [finiteTwoReplicaPauliCutoffCollective, if_neg hP,
        Submodule.map_zero]
      exact bot_le
  · apply iSup_le
    rintro ⟨P, hP⟩
    have hle := le_iSup
      (fun R : σ → Option (Fin 3) =>
        U.map (finiteTwoReplicaPauliCutoffCollective σ q R)) P
    simpa [linearFamilyShadow,
      finiteTwoReplicaPauliCutoffCollective, hP,
      finiteTwoReplicaQLocalCollectiveCommutatorLinear] using hle

/-- The all-identity Pauli label has trivial conjugation character. -/
theorem finitePauliConjugationSign_zero
    {σ : Type*} [Fintype σ]
    (Q : σ → Option (Fin 3)) :
    finitePauliConjugationSign Q (pauliCharacterZero (σ := σ)) = 1 := by
  rw [finitePauliConjugationSign]
  apply Finset.prod_eq_one
  intro s _hs
  simp [pauliCharacterZero, boolPauliConjugationSign]

/-- A collective commutator labelled by `P` sends zero-character input into
the exact paired-Pauli character grade `P`. -/
theorem finiteTwoReplicaCollectiveCommutator_mem_character_of_zero
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) (X : FiniteTwoReplicaMatrix σ)
    (hX : X ∈ finiteTwoReplicaPauliCharacterSubspace
      (pauliCharacterZero (σ := σ))) :
    finiteTwoReplicaCollectiveCommutatorLinear P X ∈
      finiteTwoReplicaPauliCharacterSubspace P := by
  rw [mem_finiteTwoReplicaPauliCharacterSubspace_iff]
  intro Q
  rw [finiteTwoReplicaPairedPauli_collectiveCommutator_intertwines]
  have hfix :=
    (mem_finiteTwoReplicaPauliCharacterSubspace_iff
      (pauliCharacterZero (σ := σ)) X).mp hX Q
  rw [finitePauliConjugationSign_zero] at hfix
  simp only [one_smul] at hfix
  rw [hfix]

/-- The cutoff family retains exact character covariance, including its zero
maps above cutoff. -/
theorem finiteTwoReplicaPauliCutoffCollective_mem_character_of_zero
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ℕ) (P : σ → Option (Fin 3))
    (X : FiniteTwoReplicaMatrix σ)
    (hX : X ∈ finiteTwoReplicaPauliCharacterSubspace
      (pauliCharacterZero (σ := σ))) :
    finiteTwoReplicaPauliCutoffCollective σ q P X ∈
      finiteTwoReplicaPauliCharacterSubspace P := by
  by_cases hP : finitePauliWeight P ≤ q
  · rw [finiteTwoReplicaPauliCutoffCollective, if_pos hP]
    exact finiteTwoReplicaCollectiveCommutator_mem_character_of_zero
      P X hX
  · rw [finiteTwoReplicaPauliCutoffCollective, if_neg hP,
      LinearMap.zero_apply]
    exact Submodule.zero_mem _

/-- Lossless aggregation modulo an invariant subspace: the aggregate belongs
to `W` exactly when every labelled component belongs to `W`. -/
theorem finiteTwoReplicaPauliCutoffAggregate_mem_iff
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ℕ) (W : Submodule ℂ (FiniteTwoReplicaMatrix σ))
    (hW : ∀ Q : σ → Option (Fin 3),
      W.map (finiteTwoReplicaPairedPauliConjugationLinear Q) ≤ W)
    (X : FiniteTwoReplicaMatrix σ)
    (hX : X ∈ finiteTwoReplicaPauliCharacterSubspace
      (pauliCharacterZero (σ := σ))) :
    finiteTwoReplicaPauliCutoffAggregate σ q X ∈ W ↔
      ∀ P : σ → Option (Fin 3),
        finiteTwoReplicaPauliCutoffCollective σ q P X ∈ W := by
  constructor
  · intro hsum P
    apply finiteTwoReplicaPauliCharacter_component_mem_of_sum_mem
      W hW
      (fun R => finiteTwoReplicaPauliCutoffCollective σ q R X)
      (fun R =>
        finiteTwoReplicaPauliCutoffCollective_mem_character_of_zero
          q R X hX)
    · simpa [finiteTwoReplicaPauliCutoffAggregate] using hsum
  · intro h
    rw [finiteTwoReplicaPauliCutoffAggregate]
    simp only [LinearMap.sum_apply]
    exact Submodule.sum_mem W fun P _ => h P

/-- Single aggregate detector from a source subspace into the quotient by
occupied target input. -/
def finiteTwoReplicaPauliVisibleQuotientDetector
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ℕ)
    (Uₛ W : Submodule ℂ (FiniteTwoReplicaMatrix σ)) :
    Uₛ →ₗ[ℂ] (FiniteTwoReplicaMatrix σ ⧸ W) :=
  (W.mkQ.comp (finiteTwoReplicaPauliCutoffAggregate σ q)).domRestrict Uₛ

/-- Exact hidden-kernel classification of the aggregate quotient detector. -/
theorem finiteTwoReplicaPauliVisibleQuotientDetector_mem_ker_iff
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ℕ)
    (Uₛ W : Submodule ℂ (FiniteTwoReplicaMatrix σ))
    (hUₛ : Uₛ ≤ finiteTwoReplicaPauliCharacterSubspace
      (pauliCharacterZero (σ := σ)))
    (hW : ∀ Q : σ → Option (Fin 3),
      W.map (finiteTwoReplicaPairedPauliConjugationLinear Q) ≤ W)
    (x : Uₛ) :
    x ∈ LinearMap.ker
        (finiteTwoReplicaPauliVisibleQuotientDetector q Uₛ W) ↔
      ∀ P : σ → Option (Fin 3),
        finiteTwoReplicaPauliCutoffCollective σ q P x ∈ W := by
  rw [LinearMap.mem_ker]
  change Submodule.Quotient.mk
      (finiteTwoReplicaPauliCutoffAggregate σ q x) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  exact finiteTwoReplicaPauliCutoffAggregate_mem_iff
    q W hW x (hUₛ x.property)

/-- Tautological inclusion of detector range into the physical quotient. -/
def finiteTwoReplicaPauliVisibleRangeInclusion
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ℕ)
    (Uₛ W : Submodule ℂ (FiniteTwoReplicaMatrix σ)) :
    LinearMap.range
        (finiteTwoReplicaPauliVisibleQuotientDetector q Uₛ W) →ₗ[ℂ]
      (FiniteTwoReplicaMatrix σ ⧸ W) :=
  (LinearMap.range
    (finiteTwoReplicaPauliVisibleQuotientDetector q Uₛ W)).subtype

/-- Detector-range inclusion is injective. -/
theorem finiteTwoReplicaPauliVisibleRangeInclusion_injective
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ℕ)
    (Uₛ W : Submodule ℂ (FiniteTwoReplicaMatrix σ)) :
    Function.Injective
      (finiteTwoReplicaPauliVisibleRangeInclusion q Uₛ W) := by
  exact Subtype.val_injective

/-- The included detector range lies in literal one-step output modulo
occupied target input. -/
theorem finiteTwoReplicaPauliVisibleRangeInclusion_range_le
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ℕ)
    (Uₛ W : Submodule ℂ (FiniteTwoReplicaMatrix σ)) :
    LinearMap.range
        (finiteTwoReplicaPauliVisibleRangeInclusion q Uₛ W) ≤
      (W ⊔ linearFamilyShadow
        (finiteTwoReplicaPauliCutoffCollective σ q) Uₛ).map W.mkQ := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨x, hx⟩ := y.property
  change (y : FiniteTwoReplicaMatrix σ ⧸ W) ∈ _
  rw [← hx]
  refine ⟨finiteTwoReplicaPauliCutoffAggregate σ q x, ?_, rfl⟩
  apply (le_sup_right :
    linearFamilyShadow
        (finiteTwoReplicaPauliCutoffCollective σ q) Uₛ ≤
      W ⊔ linearFamilyShadow
        (finiteTwoReplicaPauliCutoffCollective σ q) Uₛ)
  rw [finiteTwoReplicaPauliCutoffAggregate]
  simp only [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro P _hP
  exact (le_iSup
    (fun R => Uₛ.map
      (finiteTwoReplicaPauliCutoffCollective σ q R)) P)
    ⟨x, x.property, rfl⟩

/-- The zero-product-Clifford-twirl layer of every canonical greatest
`q`-local obstruction is paired-Pauli invariant. -/
theorem finiteTwoReplicaQLocal_greatestMaximizer_zeroTwirl_pairedPauli_invariant
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ℕ) (U : Submodule ℂ (FiniteTwoReplicaMatrix σ))
    (hgreatest : ∀ W : Submodule ℂ (FiniteTwoReplicaMatrix σ),
      linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q) W =
        linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q) U →
      W ≤ U)
    (Q : σ → Option (Fin 3)) :
    (U ⊓ LinearMap.ker
      (finiteProductCliffordTwoReplicaTwirlLinear (V := σ))).map
        (finiteTwoReplicaPairedPauliConjugationLinear Q) ≤
      U ⊓ LinearMap.ker finiteProductCliffordTwoReplicaTwirlLinear := by
  rintro _ ⟨X, hX, rfl⟩
  constructor
  · rw [← finiteTwoReplicaQLocal_greatestMaximizer_fixed
      q U hgreatest Q]
    exact Submodule.mem_map_of_mem hX.1
  · exact finiteProductCliffordTwoReplicaTwirl_ker_pairedPauli_invariant Q
      (Submodule.mem_map_of_mem hX.2)

/-- Every vector in product-Clifford twirl range is fixed by every
paired-Pauli conjugation. -/
theorem finiteProductCliffordTwoReplicaTwirl_range_pairedPauli_fixed
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (Q : σ → Option (Fin 3))
    (X : FiniteTwoReplicaMatrix σ)
    (hX : X ∈ LinearMap.range
      (finiteProductCliffordTwoReplicaTwirlLinear (V := σ))) :
    finiteTwoReplicaPairedPauliConjugationLinear Q X = X := by
  obtain ⟨Y, rfl⟩ := hX
  rw [← finiteProductCliffordDoubledConjugation_pauliHalfTurn]
  exact repTwirl_conj finiteProductCliffordDoubledGate
    finiteProductCliffordDoubledGate_mul Y
    (finitePauliHalfTurnCode Q)

/-- Product-Clifford twirl range lies in the exact trivial paired-Pauli
character grade. -/
theorem finiteProductCliffordTwoReplicaTwirl_range_le_zeroCharacter
    {σ : Type*} [Fintype σ] [DecidableEq σ] :
    LinearMap.range
        (finiteProductCliffordTwoReplicaTwirlLinear (V := σ)) ≤
      finiteTwoReplicaPauliCharacterSubspace
        (pauliCharacterZero (σ := σ)) := by
  intro X hX
  rw [mem_finiteTwoReplicaPauliCharacterSubspace_iff]
  intro Q
  rw [finiteProductCliffordTwoReplicaTwirl_range_pairedPauli_fixed Q X hX,
    finitePauliConjugationSign_zero, one_smul]

/-- The swap-word sector of any subspace, hence of every canonical
maximizer, is exact zero paired-Pauli character. -/
theorem finiteTwoReplicaQLocal_greatestMaximizer_swapSector_le_zeroCharacter
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (U : Submodule ℂ (FiniteTwoReplicaMatrix σ)) :
    U ⊓ LinearMap.range
        (finiteTwoReplicaSwapInvariantEmbed (V := σ)) ≤
      finiteTwoReplicaPauliCharacterSubspace
        (pauliCharacterZero (σ := σ)) := by
  rw [← finiteProductCliffordTwoReplicaTwirl_range_eq]
  exact inf_le_right.trans
    finiteProductCliffordTwoReplicaTwirl_range_le_zeroCharacter

end

end GaloisForLFunctions.HTGeometry

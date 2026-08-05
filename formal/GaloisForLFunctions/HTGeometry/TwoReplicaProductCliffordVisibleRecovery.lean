import GaloisForLFunctions.HTGeometry.TwoReplicaGraphVisibleRecovery
import GaloisForLFunctions.HTGeometry.TwoReplicaPauliVisibleQuotientDetector

/-!
# Product-Clifford separation and physical visible recovery

Collective Pauli commutators send the complete product-Clifford singlet range
into the exact zero-twirl layer.  This supplies the disjoint physical layers
required by visible recovery.  The aggregate Pauli quotient detector then
discharges visible rank and hidden-image recovery automatically.

For the canonical greatest Hall obstruction, all mixed-layer premises reduce
to one remaining condition: reproduction of its zero-product-Clifford-twirl
part.  Identity and global replica swap remain as the exact unavoidable
common-kernel correction.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every collective Pauli commutator of a product-Clifford singlet has zero
product-Clifford twirl. -/
theorem finiteProductCliffordTwoReplicaTwirl_collectiveCommutator_eq_zero_of_mem_range
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : V → Option (Fin 3)) (X : FiniteTwoReplicaMatrix V)
    (hX : X ∈ LinearMap.range
      (finiteProductCliffordTwoReplicaTwirlLinear (V := V))) :
    finiteProductCliffordTwoReplicaTwirlLinear
        (finiteTwoReplicaCollectiveCommutatorLinear P X) = 0 := by
  let O : V → Option (Fin 3) := pauliCharacterZero
  by_cases hP : P = O
  · subst P
    have hM : finitePauliMatrix O = 1 := by
      rw [finitePauliMatrix_eq_finiteLocalMatrix]
      simpa [O, pauliCharacterZero, boolPauliOption] using
        (finiteLocalMatrix_one (sigma := V))
    simp [finiteTwoReplicaCollectiveCommutatorLinear,
      finiteTwoReplicaCollectiveCommutator, finiteTwoReplicaPauliLeft,
      finiteTwoReplicaPauliRight, hM, ringCommutator]
  · obtain ⟨Q, hQ⟩ := exists_finitePauliConjugationSign_ne hP
    have hQone : finitePauliConjugationSign Q P ≠ 1 := by
      intro h
      apply hQ
      rw [h, finitePauliConjugationSign_zero]
    have hQneg : finitePauliConjugationSign Q P = -1 := by
      have hsq := finitePauliConjugationSign_sq Q P
      rcases mul_self_eq_one_iff.mp hsq with h | h
      · exact (hQone h).elim
      · exact h
    let Y := finiteTwoReplicaCollectiveCommutatorLinear P X
    have hYchar : Y ∈ finiteTwoReplicaPauliCharacterSubspace P :=
      finiteTwoReplicaCollectiveCommutator_mem_character_of_zero P X
        (finiteProductCliffordTwoReplicaTwirl_range_le_zeroCharacter hX)
    have hY :=
      (mem_finiteTwoReplicaPauliCharacterSubspace_iff P Y).mp hYchar Q
    have htw := congrArg
      (finiteProductCliffordTwoReplicaTwirlLinear (V := V)) hY
    rw [finiteProductCliffordTwoReplicaTwirl_pairedPauli_input,
      map_smul, hQneg] at htw
    have hneg : finiteProductCliffordTwoReplicaTwirlLinear Y =
        -finiteProductCliffordTwoReplicaTwirlLinear Y := by
      simpa using htw
    apply Matrix.ext
    intro i j
    have hij := congrFun (congrFun hneg i) j
    simp only [Matrix.neg_apply] at hij
    exact add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp hij)

/-- The complete one-step `q`-local shadow of a product-Clifford singlet
subspace lies in the zero-product-Clifford-twirl layer. -/
theorem finiteTwoReplicaQLocal_shadow_le_productCliffordTwirl_ker_of_le_range
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (Uₛ : Submodule ℂ (FiniteTwoReplicaMatrix V))
    (hUₛ : Uₛ ≤ LinearMap.range
      (finiteProductCliffordTwoReplicaTwirlLinear (V := V))) :
    linearFamilyShadow
        (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) Uₛ ≤
      LinearMap.ker finiteProductCliffordTwoReplicaTwirlLinear := by
  apply iSup_le
  rintro ⟨P, hP⟩
  rintro _ ⟨X, hX, rfl⟩
  change finiteProductCliffordTwoReplicaTwirlLinear
    (finiteTwoReplicaCollectiveCommutatorLinear P X) = 0
  exact
    finiteProductCliffordTwoReplicaTwirl_collectiveCommutator_eq_zero_of_mem_range
      P X (hUₛ hX)

/--
Visible recovery with its detector, visible-rank estimate, and source-output
separation specialized to the literal `q`-local Pauli family.  Only target
reproduction remains as an explicit premise.
-/
theorem finiteTwoReplica_graphVisibleRecovery_of_pauliDetector
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {q : ℕ} (hq : 2 ≤ q)
    {G : SimpleGraph V} (hG : G.Preconnected)
    (Uₛ U_w : Submodule ℂ (FiniteTwoReplicaMatrix V))
    (hUₛ : Uₛ ≤ LinearMap.range
      (finiteProductCliffordTwoReplicaTwirlLinear (V := V)))
    (hUw : U_w ≤ LinearMap.ker
      (finiteProductCliffordTwoReplicaTwirlLinear (V := V)))
    (hUwInvariant : ∀ Q : V → Option (Fin 3),
      U_w.map (finiteTwoReplicaPairedPauliConjugationLinear Q) ≤ U_w)
    (hUwReproduced : U_w ≤ linearFamilyShadow
      (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) U_w) :
    Module.finrank ℂ ((Uₛ ⊔ U_w) :
        Submodule ℂ (FiniteTwoReplicaMatrix V)) ≤
      Module.finrank ℂ
          (linearFamilyShadow
            (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q)
            (Uₛ ⊔ U_w)) +
        Module.finrank ℂ
          ((Uₛ ⊓ finiteTwoReplicaGlobalSynchronizedSubmodule (V := V)) :
            Submodule ℂ (FiniteTwoReplicaMatrix V)) := by
  let T := finiteProductCliffordTwoReplicaTwirlLinear (V := V)
  let S := LinearMap.range (finiteTwoReplicaSwapInvariantEmbed (V := V))
  let W := LinearMap.ker T
  let F := finiteTwoReplicaPauliVisibleQuotientDetector q Uₛ U_w
  have hSrange : S = LinearMap.range T := by
    exact finiteProductCliffordTwoReplicaTwirl_range_eq.symm
  have hSW : Disjoint S W := by
    rw [hSrange]
    rw [disjoint_iff]
    exact finiteProductCliffordTwoReplicaTwirl_range_inf_ker
  have hUₛS : Uₛ ≤ S := by
    rw [hSrange]
    exact hUₛ
  have hUwW : U_w ≤ W := by
    simpa [W, T] using hUw
  have hsourceShadowW : linearFamilyShadow
      (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) Uₛ ≤ W := by
    simpa [W, T] using
      finiteTwoReplicaQLocal_shadow_le_productCliffordTwirl_ker_of_le_range
        q Uₛ hUₛ
  have hUₛzero : Uₛ ≤ finiteTwoReplicaPauliCharacterSubspace
      (pauliCharacterZero (σ := V)) :=
    hUₛ.trans finiteProductCliffordTwoReplicaTwirl_range_le_zeroCharacter
  have hhidden : ∀ x : LinearMap.ker F,
      ∀ P : FiniteQLocalPauliLabel V q,
        finiteTwoReplicaQLocalCollectiveCommutatorLinear V q P
          (((x : LinearMap.ker F) : Uₛ) : FiniteTwoReplicaMatrix V) ∈ U_w := by
    intro x P
    have hx :=
      (finiteTwoReplicaPauliVisibleQuotientDetector_mem_ker_iff
        q Uₛ U_w hUₛzero hUwInvariant
        ((x : LinearMap.ker F) : Uₛ)).mp x.property P.1
    simpa [finiteTwoReplicaPauliCutoffCollective, P.2,
      finiteTwoReplicaQLocalCollectiveCommutatorLinear] using hx
  have hvisible : Module.finrank ℂ (LinearMap.range F) +
        Module.finrank ℂ U_w ≤
      Module.finrank ℂ
        ((U_w ⊔ linearFamilyShadow
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) Uₛ) :
            Submodule ℂ (FiniteTwoReplicaMatrix V)) := by
    apply visibleQuotientDetector_finrank Uₛ U_w
      (linearFamilyShadow
        (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) Uₛ)
      F (finiteTwoReplicaPauliVisibleRangeInclusion q Uₛ U_w)
      (finiteTwoReplicaPauliVisibleRangeInclusion_injective q Uₛ U_w)
    simpa [linearFamilyShadow_pauliCutoff_eq_qlocal] using
      (finiteTwoReplicaPauliVisibleRangeInclusion_range_le q Uₛ U_w)
  exact finiteTwoReplica_graphVisibleRecovery_finrank_mod_synchronized
    hq hG W Uₛ U_w F hSW hUₛS hUwW hsourceShadowW
      hUwReproduced hhidden hvisible

/-- For the canonical greatest maximum-defect subspace, the complete mixed
two-replica Hall inequality modulo global identity/swap follows from one
remaining zero-twirl reproduction statement. -/
theorem finiteTwoReplicaQLocal_greatestMaximizer_finrank_mod_synchronized_of_zeroTwirl_reproduced
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {q : ℕ} (hq : 2 ≤ q)
    {G : SimpleGraph V} (hG : G.Preconnected)
    (U : Submodule ℂ (FiniteTwoReplicaMatrix V))
    (hgreatest : ∀ W : Submodule ℂ (FiniteTwoReplicaMatrix V),
      linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) W =
        linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) U →
      W ≤ U)
    (hzeroTwirlReproduced :
      U ⊓ LinearMap.ker
          (finiteProductCliffordTwoReplicaTwirlLinear (V := V)) ≤
        linearFamilyShadow
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q)
          (U ⊓ LinearMap.ker
            (finiteProductCliffordTwoReplicaTwirlLinear (V := V)))) :
    Module.finrank ℂ U ≤
      Module.finrank ℂ
          (linearFamilyShadow
            (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) U) +
        Module.finrank ℂ
          (((U ⊓ LinearMap.range
              (finiteTwoReplicaSwapInvariantEmbed (V := V))) ⊓
            finiteTwoReplicaGlobalSynchronizedSubmodule (V := V)) :
              Submodule ℂ (FiniteTwoReplicaMatrix V)) := by
  let Uₛ := U ⊓ LinearMap.range
    (finiteTwoReplicaSwapInvariantEmbed (V := V))
  let U_w := U ⊓ LinearMap.ker
    (finiteProductCliffordTwoReplicaTwirlLinear (V := V))
  have hsplit : U = Uₛ ⊔ U_w := by
    simpa [Uₛ, U_w] using
      finiteTwoReplicaQLocal_greatestMaximizer_productCliffordTwirl_split
        q U hgreatest
  have hmain := finiteTwoReplica_graphVisibleRecovery_of_pauliDetector
    hq hG Uₛ U_w
    (by
      intro X hX
      rw [finiteProductCliffordTwoReplicaTwirl_range_eq]
      exact hX.2)
    (by
      intro X hX
      exact hX.2)
    (finiteTwoReplicaQLocal_greatestMaximizer_zeroTwirl_pairedPauli_invariant
      q U hgreatest)
    hzeroTwirlReproduced
  rw [← hsplit] at hmain
  simpa [Uₛ] using hmain

end

end GaloisForLFunctions.HTGeometry

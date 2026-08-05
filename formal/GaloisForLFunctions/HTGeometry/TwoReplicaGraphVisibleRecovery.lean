import GaloisForLFunctions.HTGeometry.TwoReplicaPositiveGraphEdgeCasimir
import GaloisForLFunctions.HTGeometry.VisibleKernelRecoveryCommonKernel

/-!
# Visible recovery on a connected physical interaction graph

This module combines the positive graph-edge Casimir with the abstract
common-kernel recovery law.  The resulting dimension inequality is stated for
the ordinary family of `q`-local collective Pauli commutators.  Its only
unrecovered source directions are the two globally synchronized swap-word
modes already forced into the common kernel of every collective commutator.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Restriction of the positive graph-edge Casimir to the detector kernel. -/
def finiteTwoReplicaPhysicalGraphKernelRecovery
    {V Z : Type*} [Fintype V] [DecidableEq V]
    [AddCommMonoid Z] [Module ℂ Z]
    (G : SimpleGraph V)
    (Uₛ : Submodule ℂ (FiniteTwoReplicaMatrix V))
    (F : Uₛ →ₗ[ℂ] Z) :
    LinearMap.ker F →ₗ[ℂ] FiniteTwoReplicaMatrix V :=
  (finiteTwoReplicaPhysicalGraphCasimir G).comp
    (Uₛ.subtype.comp (LinearMap.ker F).subtype)

/--
Physical mixed visible-recovery law.  Let `Uₛ` be a source sector inside the
product-Clifford swap-word range and `U_w` a disjoint visible sector.  If the
visible detector supplies the required rank, the hidden detector kernel is
returned through one connected graph Casimir, and `U_w` is reproduced by the
same `q`-local family, then the mixed source dimension is bounded by the
one-step shadow dimension plus precisely the overlap with the globally
synchronized identity/swap sector.

The graph Casimir is a sum of weight-two physical collective Pauli
commutator squares, so `2 ≤ q` is sufficient.  Connectedness identifies its
kernel inside the swap-word range exactly; no quotient is hidden in the
statement.
-/
theorem finiteTwoReplica_graphVisibleRecovery_finrank_mod_synchronized
    {V Z : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    [AddCommGroup Z] [Module ℂ Z]
    {q : ℕ} (hq : 2 ≤ q)
    {G : SimpleGraph V} (hG : G.Preconnected)
    (W Uₛ U_w : Submodule ℂ (FiniteTwoReplicaMatrix V))
    (F : Uₛ →ₗ[ℂ] Z)
    (hSW : Disjoint
      (LinearMap.range (finiteTwoReplicaSwapInvariantEmbed (V := V))) W)
    (hUₛS : Uₛ ≤
      LinearMap.range (finiteTwoReplicaSwapInvariantEmbed (V := V)))
    (hUwW : U_w ≤ W)
    (hsourceShadowW :
      linearFamilyShadow
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) Uₛ ≤ W)
    (hUwReproduced : U_w ≤
      linearFamilyShadow
        (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) U_w)
    (hhidden : ∀ x : LinearMap.ker F,
      ∀ P : FiniteQLocalPauliLabel V q,
        finiteTwoReplicaQLocalCollectiveCommutatorLinear V q P
          (((x : LinearMap.ker F) : Uₛ) : FiniteTwoReplicaMatrix V) ∈ U_w)
    (hvisible : Module.finrank ℂ (LinearMap.range F) +
        Module.finrank ℂ U_w ≤
      Module.finrank ℂ
        ((U_w ⊔ linearFamilyShadow
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) Uₛ) :
            Submodule ℂ (FiniteTwoReplicaMatrix V))) :
    Module.finrank ℂ ((Uₛ ⊔ U_w) :
        Submodule ℂ (FiniteTwoReplicaMatrix V)) ≤
      Module.finrank ℂ
          (linearFamilyShadow
            (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q)
            (Uₛ ⊔ U_w)) +
        Module.finrank ℂ
          ((Uₛ ⊓ finiteTwoReplicaGlobalSynchronizedSubmodule (V := V)) :
            Submodule ℂ (FiniteTwoReplicaMatrix V)) := by
  let A := finiteTwoReplicaQLocalCollectiveCommutatorLinear V q
  let S := LinearMap.range (finiteTwoReplicaSwapInvariantEmbed (V := V))
  let N := finiteTwoReplicaGlobalSynchronizedSubmodule (V := V)
  let C := linearFamilyShadow A Uₛ
  let Yout := linearFamilyShadow A (Uₛ ⊔ U_w)
  let R := finiteTwoReplicaPhysicalGraphKernelRecovery G Uₛ F
  have hRrangeS : LinearMap.range R ≤ S := by
    rintro _ ⟨x, rfl⟩
    apply finiteTwoReplicaPhysicalGraphCasimir_mem_swapRange G
    exact hUₛS (x : Uₛ).property
  have hRkerN : ∀ x : LinearMap.ker R,
      ((((x : LinearMap.ker R) : LinearMap.ker F) : Uₛ) :
        FiniteTwoReplicaMatrix V) ∈ N := by
    intro x
    let s : FiniteTwoReplicaMatrix V :=
      ((((x : LinearMap.ker R) : LinearMap.ker F) : Uₛ) :
        FiniteTwoReplicaMatrix V)
    have hsS : s ∈ S := hUₛS
      (((x : LinearMap.ker R) : LinearMap.ker F) : Uₛ).property
    apply (finiteTwoReplicaPhysicalGraphCasimir_eq_zero_iff_of_mem_swapRange
      hG hsS).1
    exact x.property
  have hRshadow : LinearMap.range R ≤ linearFamilyShadow A U_w := by
    rintro _ ⟨x, rfl⟩
    apply finiteTwoReplicaPhysicalGraphCasimir_mem_qlocalShadow hq G U_w
    intro u v huv a b
    let Pq : FiniteQLocalPauliLabel V q :=
      ⟨finiteEdgePauliLabel u v a b, by
        rw [finitePauliWeight_finiteEdgePauliLabel huv.ne]
        exact hq⟩
    simpa [A, finiteTwoReplicaQLocalCollectiveCommutatorLinear, Pq,
      R, finiteTwoReplicaPhysicalGraphKernelRecovery] using hhidden x Pq
  have hout : (U_w ⊔ C) ⊔ LinearMap.range R ≤ Yout := by
    rw [show Yout = linearFamilyShadow A Uₛ ⊔
        linearFamilyShadow A U_w by
      simp [Yout, linearFamilyShadow_sup]]
    exact sup_le
      (sup_le (hUwReproduced.trans le_sup_right) le_sup_left)
      (hRshadow.trans le_sup_right)
  exact visibleKernelRecovery_subspace_finrank_mod_commonKernel
    S W N Uₛ U_w C Yout F R hSW hUₛS hUwW hsourceShadowW
      hRrangeS hRkerN hvisible hout

end

end GaloisForLFunctions.HTGeometry

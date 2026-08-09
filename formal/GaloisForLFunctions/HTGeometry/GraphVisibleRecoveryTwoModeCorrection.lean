import GaloisForLFunctions.HTGeometry.TwoReplicaGraphVisibleRecovery
import GaloisForLFunctions.HTGeometry.GraphEdgeCasimirSingletKernelRank

/-!
# The recovery correction never exceeds two dimensions

The correction term of the connected-graph mixed recovery inequality is an intersection with the
span of the global identity and the global replica swap.  That span is two-dimensional on any
nonempty register, so the correction is an absolute constant: the singlet recovery mechanism loses
no dimension beyond the two universal zero modes.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-- The synchronized correction term costs at most two dimensions, whatever the source. -/
theorem finrank_inf_globalSynchronized_le_two (U : Submodule ℂ (FiniteTwoReplicaMatrix V)) :
    Module.finrank ℂ (↥(U ⊓ finiteTwoReplicaGlobalSynchronizedSubmodule (V := V))) ≤ 2 := by
  calc Module.finrank ℂ (↥(U ⊓ finiteTwoReplicaGlobalSynchronizedSubmodule (V := V)))
      ≤ Module.finrank ℂ (finiteTwoReplicaGlobalSynchronizedSubmodule (V := V)) :=
        Submodule.finrank_mono inf_le_right
    _ = 2 := finrank_finiteTwoReplicaGlobalSynchronizedSubmodule

/-- **The connected-graph mixed recovery inequality with an absolute correction.** -/
theorem finiteTwoReplica_graphVisibleRecovery_finrank_le_shadow_add_two
    {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
    {q : ℕ} (hq : 2 ≤ q) {G : SimpleGraph V} (hG : G.Preconnected)
    (W Uₛ U_w : Submodule ℂ (FiniteTwoReplicaMatrix V)) (F : Uₛ →ₗ[ℂ] Z)
    (hSW : Disjoint (LinearMap.range (finiteTwoReplicaSwapInvariantEmbed (V := V))) W)
    (hUₛS : Uₛ ≤ LinearMap.range (finiteTwoReplicaSwapInvariantEmbed (V := V)))
    (hUwW : U_w ≤ W)
    (hsourceShadowW :
      linearFamilyShadow (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) Uₛ ≤ W)
    (hUwReproduced : U_w ≤
      linearFamilyShadow (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) U_w)
    (hhidden : ∀ x : LinearMap.ker F, ∀ P : FiniteQLocalPauliLabel V q,
      finiteTwoReplicaQLocalCollectiveCommutatorLinear V q P
        (((x : LinearMap.ker F) : Uₛ) : FiniteTwoReplicaMatrix V) ∈ U_w)
    (hvisible : Module.finrank ℂ (LinearMap.range F) + Module.finrank ℂ U_w ≤
      Module.finrank ℂ
        ((U_w ⊔ linearFamilyShadow
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) Uₛ) :
            Submodule ℂ (FiniteTwoReplicaMatrix V))) :
    Module.finrank ℂ ((Uₛ ⊔ U_w) : Submodule ℂ (FiniteTwoReplicaMatrix V)) ≤
      Module.finrank ℂ
          (linearFamilyShadow (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q)
            (Uₛ ⊔ U_w)) + 2 :=
  le_trans
    (finiteTwoReplica_graphVisibleRecovery_finrank_mod_synchronized hq hG W Uₛ U_w F hSW hUₛS
      hUwW hsourceShadowW hUwReproduced hhidden hvisible)
    (Nat.add_le_add_left (finrank_inf_globalSynchronized_le_two Uₛ) _)

end

end GaloisForLFunctions.HTGeometry

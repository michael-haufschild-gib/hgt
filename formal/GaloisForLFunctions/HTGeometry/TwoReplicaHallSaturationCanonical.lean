import GaloisForLFunctions.HTGeometry.TwoReplicaSingleSiteZeroTwirlRecovery
import GaloisForLFunctions.HTGeometry.GraphVisibleRecoveryTwoModeCorrection
import GaloisForLFunctions.HTGeometry.CanonicalTwoReplicaObstruction

/-!
# Two-replica Hall saturation at the canonical obstruction

The one-site collective family reproduces the zero-twirl layer of the canonical obstruction, so the
last premise of the mixed recovery inequality is discharged and the inequality holds outright.

Its correction term is an intersection with the span of the global identity and the global replica
swap, which is two-dimensional, so the canonical obstruction expands under the weight-at-most-`q`
family up to an absolute constant — independent of the register and of the interaction graph.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The zero-twirl layer of the canonical obstruction reproduces itself.** -/
theorem canonicalTwoReplicaObstruction_zeroTwirl_reproduced {q : ℕ} (hq : 1 ≤ q) :
    canonicalTwoReplicaHiddenLayer V q ≤
      linearFamilyShadow (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q)
        (canonicalTwoReplicaHiddenLayer V q) :=
  finiteTwoReplicaQLocal_greatestMaximizer_zeroTwirl_reproduced hq
    (canonicalTwoReplicaQLocalObstruction V q)
    (fun W hW => le_canonicalTwoReplicaQLocalObstruction q W hW)

variable [Nonempty V]

/-- **Hall saturation for the canonical obstruction**, modulo the exact global identity/swap
correction. -/
theorem canonicalTwoReplicaObstruction_finrank_mod_synchronized
    {q : ℕ} (hq : 2 ≤ q) {G : SimpleGraph V} (hG : G.Preconnected) :
    Module.finrank ℂ (canonicalTwoReplicaQLocalObstruction V q) ≤
      Module.finrank ℂ
          (linearFamilyShadow (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q)
            (canonicalTwoReplicaQLocalObstruction V q)) +
        Module.finrank ℂ
          (↥(canonicalTwoReplicaVisibleSource V q ⊓
            finiteTwoReplicaGlobalSynchronizedSubmodule (V := V))) :=
  finiteTwoReplicaQLocal_greatestMaximizer_finrank_mod_synchronized hq hG
    (canonicalTwoReplicaQLocalObstruction V q)
    (fun W hW => le_canonicalTwoReplicaQLocalObstruction q W hW)

/-- **Hall saturation with an absolute correction.**  The canonical weight-at-most-`q` obstruction
expands under its own family up to two dimensions, whatever the register and whatever the
preconnected interaction graph. -/
theorem canonicalTwoReplicaObstruction_finrank_le_shadow_add_two
    {q : ℕ} (hq : 2 ≤ q) {G : SimpleGraph V} (hG : G.Preconnected) :
    Module.finrank ℂ (canonicalTwoReplicaQLocalObstruction V q) ≤
      Module.finrank ℂ
          (linearFamilyShadow (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q)
            (canonicalTwoReplicaQLocalObstruction V q)) + 2 :=
  le_trans (canonicalTwoReplicaObstruction_finrank_mod_synchronized hq hG)
    (Nat.add_le_add_left
      (finrank_inf_globalSynchronized_le_two (canonicalTwoReplicaVisibleSource V q)) _)

end

end GaloisForLFunctions.HTGeometry

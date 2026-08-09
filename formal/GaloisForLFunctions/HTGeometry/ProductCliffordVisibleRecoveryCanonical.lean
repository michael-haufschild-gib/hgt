import GaloisForLFunctions.HTGeometry.TwoReplicaProductCliffordVisibleRecovery
import GaloisForLFunctions.HTGeometry.GraphEdgeCasimirSingletKernelRank

/-!
# The mixed recovery inequality at the canonical obstruction

The product-Clifford split, paired-Pauli invariance of the hidden layer, the aggregate detector and
the connected graph Casimir all hold at the canonical obstruction with no greatest-maximizer
premise.  What remains is the zero-twirl reproduction condition, which is a genuine hypothesis of
the statement rather than a bookkeeping one.

The correction term is an intersection with the two-dimensional synchronized sector, so the
inequality also holds with the constant `2` in place of that dimension.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-- **The mixed two-replica recovery inequality at the canonical obstruction.**  The only premise
left is zero-twirl reproduction of the hidden layer. -/
theorem canonicalTwoReplicaObstruction_finrank_mod_synchronized_of_zeroTwirl_reproduced
    {q : ℕ} (hq : 2 ≤ q) {G : SimpleGraph V} (hG : G.Preconnected)
    (hzeroTwirlReproduced :
      canonicalTwoReplicaHiddenLayer V q ≤
        linearFamilyShadow (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q)
          (canonicalTwoReplicaHiddenLayer V q)) :
    Module.finrank ℂ (canonicalTwoReplicaQLocalObstruction V q) ≤
      Module.finrank ℂ
          (linearFamilyShadow (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q)
            (canonicalTwoReplicaQLocalObstruction V q)) +
        Module.finrank ℂ
          (↥(canonicalTwoReplicaVisibleSource V q ⊓
            finiteTwoReplicaGlobalSynchronizedSubmodule (V := V))) :=
  finiteTwoReplicaQLocal_greatestMaximizer_finrank_mod_synchronized_of_zeroTwirl_reproduced
    hq hG (canonicalTwoReplicaQLocalObstruction V q)
    (fun W hW => le_canonicalTwoReplicaQLocalObstruction q W hW) hzeroTwirlReproduced

/-- **The correction term costs at most two dimensions.**  The synchronized sector is exactly the
span of the global identity and the global replica swap. -/
theorem canonicalTwoReplicaObstruction_finrank_le_shadow_add_two_of_zeroTwirl_reproduced
    {q : ℕ} (hq : 2 ≤ q) {G : SimpleGraph V} (hG : G.Preconnected)
    (hzeroTwirlReproduced :
      canonicalTwoReplicaHiddenLayer V q ≤
        linearFamilyShadow (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q)
          (canonicalTwoReplicaHiddenLayer V q)) :
    Module.finrank ℂ (canonicalTwoReplicaQLocalObstruction V q) ≤
      Module.finrank ℂ
          (linearFamilyShadow (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q)
            (canonicalTwoReplicaQLocalObstruction V q)) + 2 := by
  refine le_trans
    (canonicalTwoReplicaObstruction_finrank_mod_synchronized_of_zeroTwirl_reproduced
      hq hG hzeroTwirlReproduced) ?_
  refine Nat.add_le_add_left ?_ _
  calc Module.finrank ℂ
        (↥(canonicalTwoReplicaVisibleSource V q ⊓
          finiteTwoReplicaGlobalSynchronizedSubmodule (V := V)))
      ≤ Module.finrank ℂ (finiteTwoReplicaGlobalSynchronizedSubmodule (V := V)) :=
        Submodule.finrank_mono inf_le_right
    _ = 2 := finrank_finiteTwoReplicaGlobalSynchronizedSubmodule

end

end GaloisForLFunctions.HTGeometry

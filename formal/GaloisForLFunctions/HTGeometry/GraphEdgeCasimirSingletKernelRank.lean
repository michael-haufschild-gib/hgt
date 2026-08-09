import GaloisForLFunctions.HTGeometry.TwoReplicaPositiveGraphEdgeCasimir
import GaloisForLFunctions.HTGeometry.GlobalCliffordTwirlRangeCanonical

/-!
# The two universal zero modes of the graph edge Casimir

The graph-summed edge Casimir vanishes on the product-Clifford singlet sector exactly on the span
of the global identity and the global replica swap.  On a nonempty register those two words are
distinct, and the coefficient embedding is injective, so the span is two-dimensional: the kernel has
exactly two universal zero modes, which is what a recovery map must quotient by before it can be
injective.

The singlet sector is stated both as the swap-word range and as the product-Clifford twirl range;
the two coincide.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-- The global identity and global replica swap are independent. -/
theorem finiteTwoReplicaGlobalSynchronizedMap_injective :
    Function.Injective (finiteTwoReplicaGlobalSynchronizedMap (V := V)) := by
  classical
  intro z w h
  have hcoeff : twoReplicaGlobalSynchronizedCoeff (V := V) z.1 z.2
      = twoReplicaGlobalSynchronizedCoeff (V := V) w.1 w.2 :=
    finiteTwoReplicaSwapInvariantEmbed_injective h
  have hne : (twoReplicaAllIdentity : V → Bool) ≠ twoReplicaAllSwap :=
    twoReplicaAllIdentity_ne_allSwap
  have h0 := congrFun hcoeff twoReplicaAllIdentity
  have h1 := congrFun hcoeff twoReplicaAllSwap
  rw [twoReplicaGlobalSynchronizedCoeff, twoReplicaGlobalSynchronizedCoeff] at h0 h1
  simp only [if_neg hne.symm] at h0 h1
  exact Prod.ext h0 h1

/-- **The synchronized sector is exactly two-dimensional.** -/
theorem finrank_finiteTwoReplicaGlobalSynchronizedSubmodule :
    Module.finrank ℂ (finiteTwoReplicaGlobalSynchronizedSubmodule (V := V)) = 2 := by
  rw [finiteTwoReplicaGlobalSynchronizedSubmodule,
    LinearMap.finrank_range_of_inj finiteTwoReplicaGlobalSynchronizedMap_injective]
  simp

/-- **The graph-Casimir kernel on the product-Clifford singlet sector.**  Stated at the twirl range
itself, which is the sitewise identity/swap algebra. -/
theorem finiteTwoReplicaPhysicalGraphCasimir_ker_inf_twirlRange
    {G : SimpleGraph V} (hG : G.Preconnected) :
    LinearMap.ker (finiteTwoReplicaPhysicalGraphCasimir G) ⊓
        LinearMap.range (finiteProductCliffordTwoReplicaTwirlLinear (V := V)) =
      finiteTwoReplicaGlobalSynchronizedSubmodule (V := V) := by
  rw [finiteProductCliffordTwoReplicaTwirl_range_eq]
  exact finiteTwoReplicaPhysicalGraphCasimir_ker_inf_swapRange hG

/-- **Exactly two universal zero modes.**  On the singlet sector the graph Casimir kills a
two-dimensional space, so a recovery map built from it is injective only after those two modes are
removed. -/
theorem finrank_finiteTwoReplicaPhysicalGraphCasimir_ker_inf_twirlRange
    {G : SimpleGraph V} (hG : G.Preconnected) :
    Module.finrank ℂ
        (↥(LinearMap.ker (finiteTwoReplicaPhysicalGraphCasimir G) ⊓
          LinearMap.range (finiteProductCliffordTwoReplicaTwirlLinear (V := V)))) = 2 := by
  rw [finiteTwoReplicaPhysicalGraphCasimir_ker_inf_twirlRange hG]
  exact finrank_finiteTwoReplicaGlobalSynchronizedSubmodule

end

end GaloisForLFunctions.HTGeometry

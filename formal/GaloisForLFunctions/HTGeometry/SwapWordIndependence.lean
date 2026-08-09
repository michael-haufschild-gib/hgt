import GaloisForLFunctions.HTGeometry.TwoReplicaGlobalSingletEdgeCasimirBridge

/-!
# The swap words are a basis of the sitewise identity/swap algebra

Each Boolean word selects an identity or a replica swap at every site, giving `2^{|V|}` global
matrices.  The explicit tensor Möbius functional recovers every coefficient of a linear combination,
so the coefficient embedding is injective and the words are linearly independent — with no
dimension count.

Their span is exactly the range of that embedding, which is the sector every singlet statement in
this layer is phrased over.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The swap words are linearly independent.**  Independence is the Möbius extractor, not a
dimension count. -/
theorem linearIndependent_finiteTwoReplicaSwapRaw :
    LinearIndependent ℂ (finiteTwoReplicaSwapRaw (V := V)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hzero : finiteTwoReplicaSwapInvariantEmbed (V := V) g = 0 := hg
  have hg0 : g = 0 :=
    finiteTwoReplicaSwapInvariantEmbed_injective (by simpa using hzero)
  exact congrFun hg0 i

/-- The span of the swap words is the range of the coefficient embedding. -/
theorem span_range_finiteTwoReplicaSwapRaw :
    Submodule.span ℂ (Set.range (finiteTwoReplicaSwapRaw (V := V)))
      = LinearMap.range (finiteTwoReplicaSwapInvariantEmbed (V := V)) := by
  classical
  refine le_antisymm (Submodule.span_le.mpr ?_) ?_
  · rintro _ ⟨x, rfl⟩
    refine ⟨fun y => if y = x then (1 : ℂ) else 0, ?_⟩
    change ∑ y : V → Bool, (if y = x then (1 : ℂ) else 0) • finiteTwoReplicaSwapRaw y
      = finiteTwoReplicaSwapRaw x
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      simp [hy]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  · rintro _ ⟨c, rfl⟩
    change ∑ x : V → Bool, c x • finiteTwoReplicaSwapRaw x ∈ _
    exact Submodule.sum_mem _ fun x _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)

end

end GaloisForLFunctions.HTGeometry

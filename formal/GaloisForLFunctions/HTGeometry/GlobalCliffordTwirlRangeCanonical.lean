import GaloisForLFunctions.HTGeometry.PauliVisibleQuotientDetectorCanonical

/-!
# Dimension of the sitewise swap algebra, and the canonical twirl split

The doubled product-Clifford twirl is an idempotent whose range is the span of the sitewise
identity/swap words.  Those words are the image of an injective coefficient embedding, so the range
has dimension `2^{|V|}` — one dimension per swap pattern, including the single scalar dimension of
the empty register.

Idempotence splits any invariant subspace into its range and kernel parts.  Applied to the canonical
weight-at-most-`q` obstruction, which is product-Clifford invariant, this is a direct sum: the two
summands meet in zero because the range and kernel of an idempotent do.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The sitewise swap algebra has one dimension per swap pattern.** -/
theorem finrank_finiteProductCliffordTwoReplicaTwirl_range :
    Module.finrank ℂ
        (LinearMap.range (finiteProductCliffordTwoReplicaTwirlLinear (V := V)))
      = 2 ^ Fintype.card V := by
  rw [finiteProductCliffordTwoReplicaTwirl_range_eq,
    LinearMap.finrank_range_of_inj finiteTwoReplicaSwapInvariantEmbed_injective]
  show Module.finrank ℂ ((V → Bool) → ℂ) = 2 ^ Fintype.card V
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fun, Fintype.card_bool]

/-- On the empty register the sitewise swap algebra is one-dimensional. -/
theorem finrank_finiteProductCliffordTwoReplicaTwirl_range_empty :
    Module.finrank ℂ
        (LinearMap.range (finiteProductCliffordTwoReplicaTwirlLinear (V := Fin 0))) = 1 := by
  rw [finrank_finiteProductCliffordTwoReplicaTwirl_range]
  simp

/-- **The canonical obstruction splits along the twirl.** -/
theorem canonicalTwoReplicaQLocalObstruction_twirl_split (q : ℕ) :
    canonicalTwoReplicaVisibleSource V q ⊔ canonicalTwoReplicaHiddenLayer V q
      = canonicalTwoReplicaQLocalObstruction V q :=
  (finiteTwoReplicaQLocal_greatestMaximizer_productCliffordTwirl_split q
    (canonicalTwoReplicaQLocalObstruction V q)
    (fun W hW => le_canonicalTwoReplicaQLocalObstruction q W hW)).symm

/-- **The split is direct.**  The identity/swap part and the zero-twirl part of the canonical
obstruction meet in zero, because the range and kernel of an idempotent do. -/
theorem canonicalTwoReplicaQLocalObstruction_twirl_disjoint (q : ℕ) :
    Disjoint (canonicalTwoReplicaVisibleSource V q) (canonicalTwoReplicaHiddenLayer V q) := by
  rw [disjoint_iff, canonicalTwoReplicaVisibleSource, canonicalTwoReplicaHiddenLayer]
  refine le_antisymm ?_ bot_le
  calc canonicalTwoReplicaQLocalObstruction V q ⊓
        LinearMap.range (finiteTwoReplicaSwapInvariantEmbed (V := V)) ⊓
        (canonicalTwoReplicaQLocalObstruction V q ⊓
          LinearMap.ker (finiteProductCliffordTwoReplicaTwirlLinear (V := V)))
      ≤ LinearMap.range (finiteTwoReplicaSwapInvariantEmbed (V := V)) ⊓
          LinearMap.ker (finiteProductCliffordTwoReplicaTwirlLinear (V := V)) :=
        inf_le_inf inf_le_right inf_le_right
    _ = ⊥ := by
        rw [← finiteProductCliffordTwoReplicaTwirl_range_eq]
        exact finiteProductCliffordTwoReplicaTwirl_range_inf_ker

end

end GaloisForLFunctions.HTGeometry

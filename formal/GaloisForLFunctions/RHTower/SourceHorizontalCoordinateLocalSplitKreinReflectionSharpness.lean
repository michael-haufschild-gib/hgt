import GaloisForLFunctions.RHTower.SourceHorizontalUniversalSplitKreinReflectionSharpness

/-!
# Coordinate-local split-Krein reflection still receives every shared Ward packet

The universal split carrier already shows that bounded involutive infinite-index reflection is
nonselective for the shared HB/FZZ-P/PW-B/RBH source. This module imposes a strong causal-locality
condition and proves that the same countermodel survives.

A vector is supported on `S ⊆ ℕ` when both split sectors vanish outside `S`. Sector exchange
preserves this support for every `S`, not only for one chosen filtration. Hence it preserves all
prefixes, tails, and single-coordinate time sectors exactly. The canonical size-`m` packet
embeddings also vanish at every coordinate `n ≥ m`, before and after reflection.

Thus one fixed bounded norm-preserving involution, exact split-Krein anti-isometry, maximal
coordinate-support locality, and finite-prefix source landing coexist for every hypothetical
off-wall Xi packet. Abstract causal/local reflection existence cannot produce the missing shared
Ward orientation. A survivor must impose source-semantic cross-coordinate phase/weight
compatibility, irreversible dynamics, or nonlinear/singular/domain-changing structure.

`[NEW] [SHARED-WARD ROUTE-CLASS KILL] [CAUSAL LOCALITY] [PREFIX SHARPNESS]`
-/

open scoped BigOperators InnerProductSpace ENNReal

namespace RHTower

noncomputable section

/-- Simultaneous coordinate support of the two split `ℓ²` sectors. -/
def sourceHorizontalSplitSupportedOn (S : Set ℕ)
    (x : SourceHorizontalSplitKreinCarrier) : Prop :=
  ∀ n : ℕ, n ∉ S → x.1 n = 0 ∧ x.2 n = 0

/-- Maximal zero-propagation locality: every coordinate-support sector is invariant in both
directions. In particular, every prefix and tail filtration is preserved exactly. -/
def SourceHorizontalCoordinateSupportLocal
    (T : SourceHorizontalSplitKreinCarrier →L[ℝ]
      SourceHorizontalSplitKreinCarrier) : Prop :=
  ∀ (S : Set ℕ) (x : SourceHorizontalSplitKreinCarrier),
    sourceHorizontalSplitSupportedOn S (T x) ↔
      sourceHorizontalSplitSupportedOn S x

/-- Sector exchange is local for every coordinate subset, not merely causal for one prefix
filtration. -/
theorem sourceHorizontalSplitSwap_coordinateSupportLocal :
    SourceHorizontalCoordinateSupportLocal sourceHorizontalSplitSwap := by
  intro S x
  constructor
  · intro h n hn
    have hx := h n hn
    simpa using hx.symm
  · intro h n hn
    have hx := h n hn
    simpa using hx.symm

/-- A split-carrier vector is confined to the first `m` coordinates. -/
def sourceHorizontalSplitPrefixSupported (m : ℕ)
    (x : SourceHorizontalSplitKreinCarrier) : Prop :=
  sourceHorizontalSplitSupportedOn (Set.Iio m) x

/-- Sector exchange preserves every finite prefix exactly. -/
theorem sourceHorizontalSplitSwap_prefixSupported_iff (m : ℕ)
    (x : SourceHorizontalSplitKreinCarrier) :
    sourceHorizontalSplitPrefixSupported m (sourceHorizontalSplitSwap x) ↔
      sourceHorizontalSplitPrefixSupported m x :=
  sourceHorizontalSplitSwap_coordinateSupportLocal (Set.Iio m) x

/-- Sector exchange is norm-preserving for the product Hilbert norm. -/
theorem norm_sourceHorizontalSplitSwap
    (x : SourceHorizontalSplitKreinCarrier) :
    ‖sourceHorizontalSplitSwap x‖ = ‖x‖ := by
  simp [Prod.norm_def, max_comm]

/-- The canonical positive packet embedding uses no coordinate at or beyond its packet size. -/
theorem sourceHorizontalPositiveSplitEmbedding_prefixSupported {m : ℕ}
    (hm : 1 ≤ m) (w : Fin m → ℝ) (x : Fin m → ℝ) :
    sourceHorizontalSplitPrefixSupported m
      (sourceHorizontalPositiveSplitEmbedding w x) := by
  intro n hn
  have hmn : m ≤ n := Nat.le_of_not_gt hn
  rw [sourceHorizontalPositiveSplitEmbedding_apply]
  constructor
  · rw [lp.coeFn_sum]
    simp only [Finset.sum_apply, lp.single_apply, Pi.single_apply]
    apply Finset.sum_eq_zero
    intro i _hi
    have hne : n ≠ (i : ℕ) := by omega
    simp [hne]
  · simp only [lp.single_apply, Pi.single_apply]
    have hne : n ≠ 0 := by omega
    simp [hne]

/-- The negative packet embedding is confined to the same finite prefix. -/
theorem sourceHorizontalNegativeSplitEmbedding_prefixSupported {m : ℕ}
    (hm : 1 ≤ m) (w : Fin m → ℝ) (x : Fin m → ℝ) :
    sourceHorizontalSplitPrefixSupported m
      (sourceHorizontalNegativeSplitEmbedding w x) := by
  rw [sourceHorizontalNegativeSplitEmbedding_apply]
  exact (sourceHorizontalSplitSwap_prefixSupported_iff m _).2
    (sourceHorizontalPositiveSplitEmbedding_prefixSupported hm w x)

/-- Exact all-packet reflection landing with both source and reflected images confined to the
packet-size prefix. -/
def SourceHorizontalAllPacketBoundedPrefixLocalReflectionLanding
    (q : XiZeroCopy)
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (Q : QuadraticForm ℝ M) (T : M →L[ℝ] M)
    (prefixSupported : ℕ → M → Prop) : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ p : Fin m → Nat.Primes,
    Function.Injective p →
      ∃ f : (Fin m → ℝ) →ₗ[ℝ] M,
        (∀ x,
          (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' x =
            Q (f x)) ∧
        (∀ x, (sourceZeroHorizontalSharedReservoirMatrix
          (xiZeroCopyLineConjEquiv q) p).toQuadraticForm' x =
            Q (T (f x))) ∧
        (∀ x, prefixSupported m (f x) ∧ prefixSupported m (T (f x)))

/-- Every left-half-plane packet has an exact finite-prefix local landing in the fixed split
carrier. -/
theorem sourceHorizontalSplitKrein_allPacketPrefixLocalLanding_of_left
    (q : XiZeroCopy) (hleft : (q.1 : ℂ).re < 1 / 2) :
    SourceHorizontalAllPacketBoundedPrefixLocalReflectionLanding q
      sourceHorizontalSplitKreinForm sourceHorizontalSplitSwap
      sourceHorizontalSplitPrefixSupported := by
  intro m hm p _hp
  let w : Fin m → ℝ := sourceZeroHorizontalSharedWeights q p
  have hw : ∀ i, 0 ≤ w i := fun i => abs_nonneg _
  have hm1 : 1 ≤ m := le_trans (by norm_num) hm
  refine ⟨sourceHorizontalPositiveSplitEmbedding w, ?_, ?_, ?_⟩
  · intro x
    calc
      (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' x =
          reservoirWeightedForm w x := by
        rw [sourceZeroHorizontalSharedReservoirMatrix,
          sourceZeroHorizontalOrientation_eq_one_of_left q hleft]
        simpa [w] using DFunLike.congr_fun
          (orientedSourceSharedReservoirMatrix_toQuadraticForm_one hw) x
      _ = sourceHorizontalSplitKreinForm
          (sourceHorizontalPositiveSplitEmbedding w x) :=
        (sourceHorizontalSplitKreinForm_positiveEmbedding w x).symm
  · intro x
    calc
      (sourceZeroHorizontalSharedReservoirMatrix
          (xiZeroCopyLineConjEquiv q) p).toQuadraticForm' x =
          -(reservoirWeightedForm w x) := by
        rw [sourceZeroHorizontalSharedReservoirMatrix,
          sourceZeroHorizontalOrientation_reflection,
          sourceZeroHorizontalOrientation_eq_one_of_left q hleft,
          sourceZeroHorizontalSharedWeights_reflection]
        exact DFunLike.congr_fun
          (orientedSourceSharedReservoirMatrix_toQuadraticForm_neg_one hw) x
      _ = sourceHorizontalSplitKreinForm
          (sourceHorizontalSplitSwap
            (sourceHorizontalPositiveSplitEmbedding w x)) := by
        rw [sourceHorizontalSplitKreinForm_swap,
          sourceHorizontalSplitKreinForm_positiveEmbedding]
  · intro x
    have hs := sourceHorizontalPositiveSplitEmbedding_prefixSupported hm1 w x
    exact ⟨hs, (sourceHorizontalSplitSwap_prefixSupported_iff m _).2 hs⟩

/-- Every right-half-plane packet has an exact finite-prefix local landing in the same fixed split
carrier. -/
theorem sourceHorizontalSplitKrein_allPacketPrefixLocalLanding_of_right
    (q : XiZeroCopy) (hright : 1 / 2 < (q.1 : ℂ).re) :
    SourceHorizontalAllPacketBoundedPrefixLocalReflectionLanding q
      sourceHorizontalSplitKreinForm sourceHorizontalSplitSwap
      sourceHorizontalSplitPrefixSupported := by
  intro m hm p _hp
  let w : Fin m → ℝ := sourceZeroHorizontalSharedWeights q p
  have hw : ∀ i, 0 ≤ w i := fun i => abs_nonneg _
  have hm1 : 1 ≤ m := le_trans (by norm_num) hm
  refine ⟨sourceHorizontalNegativeSplitEmbedding w, ?_, ?_, ?_⟩
  · intro x
    calc
      (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' x =
          -(reservoirWeightedForm w x) := by
        rw [sourceZeroHorizontalSharedReservoirMatrix,
          sourceZeroHorizontalOrientation_eq_neg_one_of_right q hright]
        exact DFunLike.congr_fun
          (orientedSourceSharedReservoirMatrix_toQuadraticForm_neg_one hw) x
      _ = sourceHorizontalSplitKreinForm
          (sourceHorizontalNegativeSplitEmbedding w x) :=
        (sourceHorizontalSplitKreinForm_negativeEmbedding w x).symm
  · intro x
    calc
      (sourceZeroHorizontalSharedReservoirMatrix
          (xiZeroCopyLineConjEquiv q) p).toQuadraticForm' x =
          reservoirWeightedForm w x := by
        rw [sourceZeroHorizontalSharedReservoirMatrix,
          sourceZeroHorizontalOrientation_reflection,
          sourceZeroHorizontalOrientation_eq_neg_one_of_right q hright,
          sourceZeroHorizontalSharedWeights_reflection]
        simpa [w] using DFunLike.congr_fun
          (orientedSourceSharedReservoirMatrix_toQuadraticForm_one hw) x
      _ = sourceHorizontalSplitKreinForm
          (sourceHorizontalSplitSwap
            (sourceHorizontalNegativeSplitEmbedding w x)) := by
        rw [sourceHorizontalSplitSwap_negativeEmbedding,
          sourceHorizontalSplitKreinForm_positiveEmbedding]
  · intro x
    have hs := sourceHorizontalNegativeSplitEmbedding_prefixSupported hm1 w x
    constructor
    · exact hs
    · rw [sourceHorizontalSplitSwap_negativeEmbedding]
      exact sourceHorizontalPositiveSplitEmbedding_prefixSupported hm1 w x

/-- Closed countermodel certificate for the causal/local bounded split-reflection route. -/
def SourceHorizontalCoordinateLocalBoundedSplitKreinReflectionRouteKilled : Prop :=
  (∀ x : SourceHorizontalSplitKreinCarrier,
      ‖sourceHorizontalSplitSwap x‖ = ‖x‖) ∧
    sourceHorizontalSplitSwap * sourceHorizontalSplitSwap = 1 ∧
    (∀ x : SourceHorizontalSplitKreinCarrier,
      sourceHorizontalSplitKreinForm (sourceHorizontalSplitSwap x) =
        -sourceHorizontalSplitKreinForm x) ∧
    SourceHorizontalCoordinateSupportLocal sourceHorizontalSplitSwap ∧
    ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 →
      SourceHorizontalAllPacketBoundedPrefixLocalReflectionLanding q
        sourceHorizontalSplitKreinForm sourceHorizontalSplitSwap
        sourceHorizontalSplitPrefixSupported

/-- **[SHARED-WARD ROUTE-CLASS KILL].** Boundedness, norm preservation, involution, exact
split-Krein reflection, preservation of every coordinate-support sector, and finite-prefix packet
landing all coexist for every hypothetical off-wall Xi copy. Causal/local reflection existence
therefore cannot force the common HB/FZZ-P/PW-B/RBH Ward wall. -/
theorem sourceHorizontalCoordinateLocalBoundedSplitKreinReflectionRouteKilled :
    SourceHorizontalCoordinateLocalBoundedSplitKreinReflectionRouteKilled := by
  refine ⟨norm_sourceHorizontalSplitSwap,
    sourceHorizontalSplitSwap_involutive,
    sourceHorizontalSplitKreinForm_swap,
    sourceHorizontalSplitSwap_coordinateSupportLocal, ?_⟩
  intro q hoff
  rcases lt_or_gt_of_ne hoff with hleft | hright
  · exact sourceHorizontalSplitKrein_allPacketPrefixLocalLanding_of_left q hleft
  · exact sourceHorizontalSplitKrein_allPacketPrefixLocalLanding_of_right q hright

end

end RHTower

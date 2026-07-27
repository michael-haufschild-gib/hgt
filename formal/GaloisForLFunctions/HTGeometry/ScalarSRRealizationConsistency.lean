import GaloisForLFunctions.HTGeometry.ScalarSRRealizationBridge
import GaloisForLFunctions.HTGeometry.InfiniteGeometricLayerTowerWitness
import GaloisForLFunctions.HTGeometry.EllipticHypertranscendenceFreeProof
import GaloisForLFunctions.HTGeometry.ChannelSRRealization

/-!
# The scalar realization datum is consistent

`ScalarSRRealization` is the analytic input of the whole scalar Stanley–Reisner layer, and no
realization is exhibited anywhere, so a priori every theorem consuming one could be vacuous.  It is
not: over the empty vertex type the Stanley–Reisner ring has no vertex coordinates, the difference
relation is vacuous, and the only requirement left is a hypertranscendental meromorphic function to
serve as the carrier of every nonzero class.  The explicit entire function of
`InfiniteGeometricLayerTowerWitness` supplies it.

This is the degenerate end of the datum, and it is exactly what it claims: a consistency proof.  A
realization over a *nonempty* vertex set is a different question.  On a single vertex whose
coordinate is killed in the Stanley–Reisner ring the difference relation forces every carrier to be
invariant under the vertex step, so such a realization exists precisely when some hypertranscendental
meromorphic function has a nonzero period.  By `rat_dependent_periods_of_hypertranscendental` its
period group would then have `ℚ`-rank exactly one, the extreme case the period-rank law allows.

* **`emptyScalarSRRealization`** — the realization;
* **`emptyChannelSRRealization`** — the same carrier read on every channel, for the channel datum;
* `facetComplementRankOne_emptyScalarSRRealization` — the codimension law on it.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Classical

/-- The carrier assignment over the empty vertex type: every nonzero class carries the explicit
hypertranscendental entire function, the zero class carries zero. -/
noncomputable def emptyScalarSRCarrier
    (q : stanleyReisnerRing ℂ ({∅} : Finset (Finset Empty))) : ℂ → ℂ :=
  if q = 0 then 0 else dyadicLayerEntireFunction

theorem meromorphicNFOn_dyadicLayerEntireFunction :
    MeromorphicNFOn dyadicLayerEntireFunction Set.univ := fun z _ =>
  (((contDiff_dyadicLayerEntireFunction).differentiable (by simp)).analyticAt z).meromorphicNFAt

theorem meromorphicNFOn_emptyScalarSRCarrier (q : stanleyReisnerRing ℂ
    ({∅} : Finset (Finset Empty))) : MeromorphicNFOn (emptyScalarSRCarrier q) Set.univ := by
  by_cases hq : q = 0
  · rw [emptyScalarSRCarrier, if_pos hq]
    exact fun z _ => (analyticAt_const (v := (0 : ℂ))).meromorphicNFAt
  · rw [emptyScalarSRCarrier, if_neg hq]
    exact meromorphicNFOn_dyadicLayerEntireFunction

theorem hypertranscendental_emptyScalarSRCarrier
    {q : stanleyReisnerRing ℂ ({∅} : Finset (Finset Empty))} (hq : q ≠ 0) :
    Hypertranscendental (emptyScalarSRCarrier q) := by
  rw [emptyScalarSRCarrier, if_neg hq]
  exact hypertranscendental_dyadicLayerEntireFunction

/-- **The scalar realization datum is consistent.**  Over the empty vertex type there are no vertex
coordinates, so the difference relation is vacuous and the explicit hypertranscendental entire
function realizes every nonzero class. -/
noncomputable def emptyScalarSRRealization :
    ScalarSRRealization ({∅} : Finset (Finset Empty)) where
  ω := Empty.elim
  indep := linearIndependent_empty_type
  carrier := emptyScalarSRCarrier
  carrier_meromorphic := meromorphicNFOn_emptyScalarSRCarrier
  carrier_zero := by
    rw [emptyScalarSRCarrier, if_pos rfl]
  carrier_vertex := fun v _ => v.elim
  carrier_ht := fun _ hq => hypertranscendental_emptyScalarSRCarrier hq

/-- The same carrier read on every channel realizes the channel datum. -/
noncomputable def emptyChannelSRCarrier {ι : Type*}
    (q : stanleyReisnerRing ℂ ({∅} : Finset (Finset Empty))) : ℂ → ι → ℂ :=
  fun z _ => emptyScalarSRCarrier q z

/-- **The channel realization datum is consistent**, for every nonempty channel index. -/
noncomputable def emptyChannelSRRealization (ι : Type*) [Nonempty ι] :
    ChannelSRRealization ι ({∅} : Finset (Finset Empty)) where
  ω := Empty.elim
  indep := linearIndependent_empty_type
  carrier := emptyChannelSRCarrier
  carrier_zero := by
    funext z i
    show emptyScalarSRCarrier 0 z = 0
    rw [emptyScalarSRCarrier, if_pos rfl]
    rfl
  carrier_vertex := fun v _ => v.elim
  carrier_meromorphic := fun q _ => meromorphicNFOn_emptyScalarSRCarrier q
  carrier_ht := fun _ hq =>
    ⟨Classical.arbitrary ι, hypertranscendental_emptyScalarSRCarrier hq⟩

/-- The facet-codimension law holds on the realization just built. -/
theorem facetComplementRankOne_emptyScalarSRRealization
    (hanti : FacetAntichain (↑({∅} : Finset (Finset Empty)) : Set (Finset Empty)))
    (hsub : ∀ F ∈ ({∅} : Finset (Finset Empty)), F ⊆ (∅ : Finset Empty)) :
    FacetComplementRankOne (∅ : Finset Empty)
      (↑({∅} : Finset (Finset Empty)) : Set (Finset Empty)) :=
  facetComplementRankOne_of_scalarSRRealization hanti emptyScalarSRRealization hsub

end GaloisForLFunctions.HTGeometry

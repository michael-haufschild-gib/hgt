import GaloisForLFunctions.HTGeometry.FiniteLocalInteractionFamily

/-!
# Exact factorization of disconnected local interaction packets

Two label packets whose site supports are disjoint act on opposite tensor factors after the
canonical configuration reindexing. Their full affine matrix family is therefore exactly a
Kronecker sum of the two packet families. This is the concrete local-generator input for
disconnected spectral-cluster cancellation.
-/

open scoped Kronecker BigOperators

namespace GaloisForLFunctions.HTGeometry
namespace FiniteLocalInteractionFamily

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]

omit [Fintype E] in
theorem support_disjoint_packetSiteSupport_of_mem
    (L : FiniteLocalInteractionFamily V E A)
    {left right : Finset E}
    (hdisj :
      Disjoint (L.packetSiteSupport left) (L.packetSiteSupport right))
    {e : E} (he : e ∈ right) :
    Disjoint (L.packetSiteSupport left) (L.support e) := by
  rw [Finset.disjoint_left]
  intro v hvleft hve
  exact (Finset.disjoint_left.mp hdisj hvleft)
    (Finset.mem_biUnion.mpr ⟨e, he, hve⟩)

/-- Right-packet interactions represented on the outside of the left packet's site sector. -/
def packetOutsideInteraction
    (L : FiniteLocalInteractionFamily V E A)
    (left right : Finset E)
    (hdisj :
      Disjoint (L.packetSiteSupport left) (L.packetSiteSupport right)) :
    {e : E // e ∈ right} →
      Matrix (OutsideConfiguration A (L.packetSiteSupport left))
        (OutsideConfiguration A (L.packetSiteSupport left)) ℂ :=
  fun e =>
    liftLocalMatrixOutsideDisjoint
      (L.support_disjoint_packetSiteSupport_of_mem hdisj e.2)
      (L.interaction e.1)

/-- The two packet label sets, lifted to the original global product-configuration space. -/
def splitPacketGlobalInteraction
    (L : FiniteLocalInteractionFamily V E A)
    (left right : Finset E) :
    Sum {e : E // e ∈ left} {e : E // e ∈ right} →
      Matrix (∀ v, A v) (∀ v, A v) ℂ
  | Sum.inl e => L.globalInteraction e.1
  | Sum.inr e => L.globalInteraction e.1

omit [Fintype E] in
/-- Every split-packet global interaction becomes the corresponding tensor-factor interaction. -/
theorem reindex_splitPacketGlobalInteraction
    (L : FiniteLocalInteractionFamily V E A)
    (left right : Finset E)
    (hdisj :
      Disjoint (L.packetSiteSupport left) (L.packetSiteSupport right))
    (label : Sum {e : E // e ∈ left} {e : E // e ∈ right}) :
    Matrix.reindex
        (configurationSplitEquiv A (L.packetSiteSupport left))
        (configurationSplitEquiv A (L.packetSiteSupport left))
        (L.splitPacketGlobalInteraction left right label) =
      splitAffineInteraction
        (L.packetLocalInteraction left)
        (L.packetOutsideInteraction left right hdisj)
        label := by
  cases label with
  | inl e =>
      rw [splitPacketGlobalInteraction, splitAffineInteraction]
      rw [← L.lift_packetLocalInteraction_eq_globalInteraction left e]
      exact reindex_liftLocalMatrix_eq_kronecker_one
        (L.packetSiteSupport left) (L.packetLocalInteraction left e)
  | inr e =>
      rw [splitPacketGlobalInteraction, splitAffineInteraction,
        globalInteraction]
      exact reindex_liftLocalMatrix_disjoint_eq_one_kronecker
        (L.support_disjoint_packetSiteSupport_of_mem hdisj e.2)
        (L.interaction e.1)

omit [Fintype E] in
/-- **Exact disconnected local affine factorization.** Disjoint-support packets form a literal
Kronecker sum after reindexing, for arbitrary finite complex local matrices. -/
theorem reindex_splitPacketAffineFamily_eq_kroneckerSum
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (left right : Finset E)
    (hdisj :
      Disjoint (L.packetSiteSupport left) (L.packetSiteSupport right))
    (coupling : Sum {e : E // e ∈ left} {e : E // e ∈ right} → ℂ) :
    Matrix.reindex
        (configurationSplitEquiv A (L.packetSiteSupport left))
        (configurationSplitEquiv A (L.packetSiteSupport left))
        (affineMatrixFamily
          (Matrix.diagonal (onsiteProductEnergy onsite))
          (L.splitPacketGlobalInteraction left right)
          coupling) =
      kroneckerSum
        (affineMatrixFamily
          (Matrix.diagonal
            (localOnsiteEnergy onsite (L.packetSiteSupport left)))
          (L.packetLocalInteraction left)
          (leftSplitCoupling coupling))
        (affineMatrixFamily
          (Matrix.diagonal
            (outsideOnsiteEnergy onsite (L.packetSiteSupport left)))
          (L.packetOutsideInteraction left right hdisj)
          (rightSplitCoupling coupling)) := by
  let S := L.packetSiteSupport left
  let e := configurationSplitEquiv A S
  change Matrix.reindexAlgEquiv ℂ ℂ e
      (affineMatrixFamily
        (Matrix.diagonal (onsiteProductEnergy onsite))
        (L.splitPacketGlobalInteraction left right)
        coupling) = _
  rw [affineMatrixFamily, map_add, map_sum]
  dsimp only [e, S]
  simp_rw [map_smul, Matrix.reindexAlgEquiv_apply,
    L.reindex_splitPacketGlobalInteraction left right hdisj]
  rw [reindex_diagonal_onsiteProductEnergy_eq_kroneckerSum]
  exact affineMatrixFamily_splitAffineInteraction_eq_kroneckerSum
    (Matrix.diagonal (localOnsiteEnergy onsite S))
    (Matrix.diagonal (outsideOnsiteEnergy onsite S))
    (L.packetLocalInteraction left)
    (L.packetOutsideInteraction left right hdisj)
    coupling

end FiniteLocalInteractionFamily
end GaloisForLFunctions.HTGeometry

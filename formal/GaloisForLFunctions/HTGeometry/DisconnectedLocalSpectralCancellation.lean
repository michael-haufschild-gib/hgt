import GaloisForLFunctions.HTGeometry.DisconnectedLocalAffineFactorization
import GaloisForLFunctions.HTGeometry.LocalAffineSpectralFactorization

/-!
# Disconnected spectral cancellation for actual local generators

Exact disconnected tensor factorization and analytic simple-root uniqueness produce a globally
labelled spectral branch whose Boolean interaction contrast vanishes whenever the active labels
split into two nonempty packets with disjoint site supports. This is the actual local-generator
linked-cluster theorem, with no self-adjointness, normality, or positivity assumption.
-/

open Filter Topology
open scoped Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry
namespace FiniteLocalInteractionFamily

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]

omit [Fintype E] in
/-- **Actual disconnected local spectral cancellation.** If two nonempty label packets touch
disjoint site sets, their jointly activated analytic eigenvalue branch has zero full cross-packet
Möbius response. -/
theorem exists_disconnectedLocalBranch_crossPacket_eq_zero
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (left right : Finset E)
    (hleft : left.Nonempty) (hright : right.Nonempty)
    (hdisj :
      Disjoint (L.packetSiteSupport left) (L.packetSiteSupport right))
    (x : ∀ v, A v) :
    ∃ totalBranch :
        (Sum {e : E // e ∈ left} {e : E // e ∈ right} → ℂ) → ℂ,
      AnalyticAt ℂ totalBranch 0 ∧
      totalBranch 0 = onsiteProductEnergy onsite x ∧
      (∀ᶠ coupling in 𝓝 0,
        matrixCharpolyRelation
          (affineMatrixFamily
            (Matrix.diagonal (onsiteProductEnergy onsite))
            (L.splitPacketGlobalInteraction left right)
            coupling,
            totalBranch coupling) = 0) ∧
      ∀ z : Sum {e : E // e ∈ left} {e : E // e ∈ right} → ℂ,
        finsetMobiusResponse
          ((Finset.univ : Finset {e : E // e ∈ left}).map
              (sumInlEmbedding {e : E // e ∈ left} {e : E // e ∈ right}) ∪
            (Finset.univ : Finset {e : E // e ∈ right}).map
              (sumInrEmbedding {e : E // e ∈ left} {e : E // e ∈ right}))
          (fun active =>
            totalBranch (restrictInteractionPacket active z)) = 0 := by
  let S := L.packetSiteSupport left
  let xlocal := restrictLocalConfiguration S x
  let xout := restrictOutsideConfiguration S x
  have hinjLeft :
      Function.Injective (localOnsiteEnergy onsite S) :=
    localOnsiteEnergy_injective_of_product onsite hinj S
  have hinjRight :
      Function.Injective (outsideOnsiteEnergy onsite S) :=
    outsideOnsiteEnergy_injective_of_product onsite hinj S
  obtain ⟨branchLeft, branchRight, totalBranch,
      hleftAnalytic, hrightAnalytic, htotalAnalytic,
      hleft0, hright0, htotal0,
      hleftRoot, hrightRoot, htotalRoot, hsplit, hcross⟩ :=
    disconnectedAffineEigenvalueBranch_crossPacket_eq_zero
      (localOnsiteEnergy onsite S) hinjLeft
      (outsideOnsiteEnergy onsite S) hinjRight
      (L.packetLocalInteraction left)
      (L.packetOutsideInteraction left right hdisj)
      xlocal xout
  have hsplitX :
      onsiteProductEnergy onsite x =
        localOnsiteEnergy onsite S xlocal +
          outsideOnsiteEnergy onsite S xout := by
    let e := configurationSplitEquiv A S
    have hex : e.symm (xlocal, xout) = x := e.symm_apply_apply x
    rw [← hex, onsiteProductEnergy_configurationSplit]
  have htotal0Global :
      totalBranch 0 = onsiteProductEnergy onsite x := by
    rw [htotal0, hsplitX]
  have hglobalRoot :
      ∀ᶠ coupling in 𝓝 0,
        matrixCharpolyRelation
          (affineMatrixFamily
            (Matrix.diagonal (onsiteProductEnergy onsite))
            (L.splitPacketGlobalInteraction left right)
            coupling,
            totalBranch coupling) = 0 := by
    filter_upwards [htotalRoot] with coupling hroot
    have hreindex :=
      L.reindex_splitPacketAffineFamily_eq_kroneckerSum
        onsite left right hdisj coupling
    have hEval :
        (affineMatrixFamily
          (Matrix.diagonal (onsiteProductEnergy onsite))
          (L.splitPacketGlobalInteraction left right)
          coupling).charpoly.eval (totalBranch coupling) = 0 := by
      rw [← Matrix.charpoly_reindex
        (configurationSplitEquiv A (L.packetSiteSupport left))]
      rw [hreindex, Matrix.eval_charpoly]
      rw [affineMatrixFamily_splitAffineInteraction_eq_kroneckerSum
        (Matrix.diagonal (localOnsiteEnergy onsite S))
        (Matrix.diagonal (outsideOnsiteEnergy onsite S))
        (L.packetLocalInteraction left)
        (L.packetOutsideInteraction left right hdisj)
        coupling] at hroot
      exact hroot
    rw [Matrix.eval_charpoly] at hEval
    exact hEval
  refine ⟨totalBranch, htotalAnalytic, htotal0Global, hglobalRoot, ?_⟩
  intro z
  apply hcross z (Finset.univ : Finset {e : E // e ∈ left})
    (Finset.univ : Finset {e : E // e ∈ right})
  · obtain ⟨e, he⟩ := hleft
    exact ⟨⟨e, he⟩, Finset.mem_univ _⟩
  · obtain ⟨e, he⟩ := hright
    exact ⟨⟨e, he⟩, Finset.mem_univ _⟩

end FiniteLocalInteractionFamily
end GaloisForLFunctions.HTGeometry

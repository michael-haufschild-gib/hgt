import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaAllFaceIndependence
import GaloisForLFunctions.HTGeometry.WickContractedMatroidPersistence
import GaloisForLFunctions.HTGeometry.FacePacketDisplacementFreeness

/-!
# The exact independence threshold of the multiple elliptic-gamma faces

Two halves of the face analysis meet at the same number.  A face retaining at least two periods has
a differentially independent external packet; a face retaining fewer has a packet of differentially
algebraic germs.  Together they say that retaining two periods is not merely sufficient for
independence but equivalent to it, for a single germ, for one packet, and for an arbitrary family
of packets.

* **`hypertranscendentalOver_facePacket_iff`** — an external translate of a face coordinate is
  hypertranscendental over the constants exactly when the face retains at least two periods;
* **`diffIndepOn_multipleEllipticGammaFacePacket_iff`** — the same threshold for one whole packet;
* **`diffIndepOn_facePacketUnion_iff`** — and for an arbitrary family of faces, giving the exact
  independence criterion of the hierarchy.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher HTGeometry
open MatroidGluing MatroidGluing.Rank MatroidGluing.Meromorphic

noncomputable section

attribute [local instance] facePacketMeroDecidableEq

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The untranslated face coordinate lies in its own external packet. -/
theorem multipleEllipticGammaLogDerivFaceMero_mem_facePacket
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) :
    addTranslationMeroEquiv 0 (multipleEllipticGammaLogDerivFaceMero τ hτ J) ∈
      multipleEllipticGammaFacePacket τ hτ J :=
  ⟨0, faceShiftLattice_zero τ J, rfl⟩

/-- **The hypertranscendence threshold of a face.**  Every external translate of the face
coordinate is hypertranscendental over the constants precisely when the face retains at least two
periods; below the threshold the whole packet is differentially algebraic. -/
theorem hypertranscendentalOver_facePacket_iff
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (hι : 2 ≤ Fintype.card ι) (J : Finset ι) {y : meroField (Set.univ : Set ℂ)}
    (hy : y ∈ multipleEllipticGammaFacePacket τ hτ J) :
    HypertranscendentalOver ℂ y ↔ 2 ≤ (Jᶜ).card := by
  constructor
  · intro hHT
    by_contra hlt
    exact hHT (differentialAlgebraicOver_facePacket_of_compl_lt_two τ hτ hQ hι J
      (by omega) hy)
  · intro hJ
    have hsub : ({y} : Set (meroField (Set.univ : Set ℂ))) ⊆
        facePacketUnion τ hτ {L : Finset ι | 2 ≤ (Lᶜ).card} := by
      rintro z (rfl : z = y)
      exact Set.mem_iUnion₂.mpr ⟨J, hJ, hy⟩
    exact diffIndepOn_singleton_iff_hypertranscendentalOver.mp
      ((multipleEllipticGammaProperFacePackets_diffIndepOn τ hτ hQ hι).subset hsub)

/-- **The independence threshold of one packet.**  A face packet is differentially independent over
the constants exactly when the face retains at least two periods. -/
theorem diffIndepOn_multipleEllipticGammaFacePacket_iff
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (hι : 2 ≤ Fintype.card ι) (J : Finset ι) :
    DiffIndepOn ℂ (multipleEllipticGammaFacePacket τ hτ J) ↔ 2 ≤ (Jᶜ).card := by
  constructor
  · intro hindep
    have hmem := multipleEllipticGammaLogDerivFaceMero_mem_facePacket τ hτ J
    have hsub : ({addTranslationMeroEquiv 0
        (multipleEllipticGammaLogDerivFaceMero τ hτ J)} :
          Set (meroField (Set.univ : Set ℂ))) ⊆
        multipleEllipticGammaFacePacket τ hτ J := by
      rintro z (rfl : z = _)
      exact hmem
    exact (hypertranscendentalOver_facePacket_iff τ hτ hQ hι J hmem).mp
      (diffIndepOn_singleton_iff_hypertranscendentalOver.mp (hindep.subset hsub))
  · intro hJ
    refine (multipleEllipticGammaProperFacePackets_diffIndepOn τ hτ hQ hι).subset ?_
    intro z hz
    exact Set.mem_iUnion₂.mpr ⟨J, hJ, hz⟩

/-- **The exact independence criterion of the hierarchy.**  An arbitrary family of face packets is
jointly differentially independent over the constants precisely when every face in the family
retains at least two periods. -/
theorem diffIndepOn_facePacketUnion_iff
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (hι : 2 ≤ Fintype.card ι) (S : Set (Finset ι)) :
    DiffIndepOn ℂ (facePacketUnion τ hτ S) ↔ ∀ L ∈ S, 2 ≤ (Lᶜ).card := by
  constructor
  · intro hindep L hLS
    refine (diffIndepOn_multipleEllipticGammaFacePacket_iff τ hτ hQ hι L).mp
      (hindep.subset ?_)
    intro z hz
    exact Set.mem_iUnion₂.mpr ⟨L, hLS, hz⟩
  · intro hS
    refine (multipleEllipticGammaProperFacePackets_diffIndepOn τ hτ hQ hι).subset ?_
    intro z hz
    obtain ⟨L, hLS, hzL⟩ := Set.mem_iUnion₂.mp hz
    exact Set.mem_iUnion₂.mpr ⟨L, hS L hLS, hzL⟩

end

end GaloisForLFunctions

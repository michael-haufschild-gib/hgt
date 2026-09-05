import GaloisForLFunctions.HTGeometry.MultipleSineFaceDifferenceSystem
import GaloisForLFunctions.HTGeometry.MeromorphicRankTwoRaySourceBoundary
import GaloisForLFunctions.HTGeometry.ElementaryOstrowski

/-!
# Descending face-lifting for the multiple sine, reduced to a telescoper

The Ostrowski criterion turns the differential independence of the translation block of a face over
the deeper face field into the exclusion of a *simultaneous jet telescoper*: a nonzero constant jet
form of the displacements which is a defect of a single element of the deeper field.  For a ray
period family the two surviving directions already cut the ambient meromorphic field down to the
constants, so the criterion applies with the rank-two generator boundary.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

noncomputable local instance msntDecidableEq :
    DecidableEq (meroField (Set.univ : Set ℂ)) := Classical.decEq _

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Descending face-lifting for the multiple sine.**  If no nonzero constant jet form of the
displacements is a simultaneous defect in the deeper face field, the translation block of the face
is differentially algebraically independent over that field. -/
theorem sineFacePacket_differentialIndependent_of_no_telescoping (ω : ι → ℂ)
    (hω : ∀ k, 0 < (ω k).im) {S : Set (Finset ι)}
    (hS : ∀ L ∈ S, ∀ p : ι, p ∉ L → insert p L ∈ S)
    (hS2 : ∀ L ∈ S, 2 ≤ (Lᶜ : Finset ι).card)
    (J : Finset ι) {q u : ι} (hqJ : q ∉ J) (huJ : u ∉ J)
    (h2 : 2 ≤ (Jᶜ : Finset ι).card) (hqS : insert q J ∈ S) (huS : insert u J ∈ S)
    {μ : ℂ} {rad : ι → ℝ} (hμ : μ ≠ 0)
    (hqω : ω q = μ * (rad q : ℂ)) (huω : ω u = μ * (rad u : ℂ))
    (hirr : Irrational (rad q / rad u))
    (hnot : ∀ c : (↥(facePacket ω hω J) × ℕ) →₀ ℂ, c ≠ 0 →
      ∀ k : ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S)), ∃ i,
        (sineFaceDifferenceSystem ω hω hS hS2 q u).defect i k ≠
          Finsupp.linearCombination ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S))
            (fun p ↦ differentialJet p.2
              (sineFacePacketDisplacement ω hω J hqJ huJ h2 hqS huS i p.1))
            (Finsupp.mapRange
              (algebraMap ℂ ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S)))
              (map_zero (algebraMap ℂ
                ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S)))) c)) :
    DifferentialIndependent ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S))
      (sineFacePacketBlock ω hω J) := by
  classical
  haveI : DifferentialAlgebra ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S))
      (meroField (Set.univ : Set ℂ)) :=
    ⟨fun x => derivationClosedDifferential_apply _
      (derivationClosed_differentialAdjoin ℂ (sineDeeperGenerators ω hω S)) x⟩
  haveI : CharZero ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S)) :=
    charZero_of_injective_algebraMap
      (algebraMap ℂ ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S))).injective
  have hper : sineFacePacketPeriods ω q u = ![μ * (rad q : ℂ), μ * (rad u : ℂ)] := by
    funext i
    fin_cases i
    · simpa [sineFacePacketPeriods] using hqω
    · simpa [sineFacePacketPeriods] using huω
  refine differentialIndependent_of_no_constant_simultaneous_jet_telescoping
    (sineFaceDifferenceSystem ω hω hS hS2 q u)
    (rankTwoGeneratorMeromorphicDifferenceDifferentialField (sineFacePacketPeriods ω q u))
    (fun i k => rfl)
    (fun z hz => ?_)
    (sineFacePacketBlock ω hω J)
    (sineFacePacketDisplacement ω hω J hqJ huJ h2 hqS huS)
    (fun i y => ?_) hnot
  · rw [hper] at hz
    obtain ⟨w, hw⟩ := (rankTwoRay_generator_jointFixed_iff_constant hμ hirr z).mp hz
    exact ⟨w, by simpa [meromorphicConstantEmbedding] using hw⟩
  · show addTranslationMeroEquiv (sineFacePacketPeriods ω q u i) (sineFacePacketBlock ω hω J y) =
      sineFacePacketBlock ω hω J y +
        (sineFacePacketDisplacement ω hω J hqJ huJ h2 hqS huS i y :
          meroField (Set.univ : Set ℂ))
    show _ = sineFacePacketBlock ω hω J y +
      (addTranslationMeroEquiv (sineFacePacketPeriods ω q u i) (sineFacePacketBlock ω hω J y) -
        sineFacePacketBlock ω hω J y)
    ring

end

end GaloisForLFunctions.HTGeometry

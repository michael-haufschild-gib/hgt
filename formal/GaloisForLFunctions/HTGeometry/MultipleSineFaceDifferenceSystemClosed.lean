import GaloisForLFunctions.HTGeometry.MultipleSineBoundaryFaceField
import GaloisForLFunctions.HTGeometry.MeromorphicRankTwoRaySourceBoundary

/-!
# The rank-two difference system over a face family closed under deletion

Once the boundary faces are part of the generating family, translation stability of the deeper face
field needs only closure of the family under deleting one more direction.  This is the form the
descending induction uses: the two structural translations of a ray period family are commuting
difference-differential automorphisms of the deeper field, and the Ostrowski criterion reduces the
independence of a face packet over that field to the exclusion of a simultaneous telescoper.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

noncomputable local instance msdscDecidableEq :
    DecidableEq (meroField (Set.univ : Set ℂ)) := Classical.decEq _

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

set_option synthInstance.maxHeartbeats 1000000 in
theorem sineDeeperGenerators_period_translate_stable_of_closed (ω : ι → ℂ)
    (hω : ∀ k, 0 < (ω k).im) {S : Set (Finset ι)}
    (hS : ∀ L ∈ S, ∀ p : ι, p ∉ L → insert p L ∈ S) (q u : ι) (i : Fin 2)
    (x : meroField (Set.univ : Set ℂ))
    (hx : x ∈ differentialAdjoin ℂ (sineDeeperGenerators ω hω S)) :
    addTranslationMeroEquiv (sineFacePacketPeriods ω q u i) x
      ∈ differentialAdjoin ℂ (sineDeeperGenerators ω hω S) := by
  fin_cases i
  · exact differentialAdjoin_sineDeeperGenerators_translate_stable_of_closed ω hω q
      (fun L hL hq => hS L hL q hq) hx
  · exact differentialAdjoin_sineDeeperGenerators_translate_stable_of_closed ω hω u
      (fun L hL hu => hS L hL u hu) hx

set_option synthInstance.maxHeartbeats 1000000 in
theorem sineDeeperGenerators_period_neg_translate_stable_of_closed (ω : ι → ℂ)
    (hω : ∀ k, 0 < (ω k).im) {S : Set (Finset ι)}
    (hS : ∀ L ∈ S, ∀ p : ι, p ∉ L → insert p L ∈ S) (q u : ι) (i : Fin 2)
    (x : meroField (Set.univ : Set ℂ))
    (hx : x ∈ differentialAdjoin ℂ (sineDeeperGenerators ω hω S)) :
    addTranslationMeroEquiv (-sineFacePacketPeriods ω q u i) x
      ∈ differentialAdjoin ℂ (sineDeeperGenerators ω hω S) := by
  fin_cases i
  · exact differentialAdjoin_sineDeeperGenerators_neg_translate_stable_of_closed ω hω q
      (fun L hL hq => hS L hL q hq) hx
  · exact differentialAdjoin_sineDeeperGenerators_neg_translate_stable_of_closed ω hω u
      (fun L hL hu => hS L hL u hu) hx

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The two structural translations as a difference-differential structure on the deeper face
field**, over a family closed under deleting one more direction. -/
def sineFaceDifferenceSystemClosed (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    {S : Set (Finset ι)} (hS : ∀ L ∈ S, ∀ p : ι, p ∉ L → insert p L ∈ S) (q u : ι) :
    CommutingDifferenceDifferentialField (Fin 2) ℂ
      ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S)) where
  aut i := meroTranslationRestrict (differentialAdjoin ℂ (sineDeeperGenerators ω hω S))
    (sineFacePacketPeriods ω q u i)
    (sineDeeperGenerators_period_translate_stable_of_closed ω hω hS q u i)
    (sineDeeperGenerators_period_neg_translate_stable_of_closed ω hω hS q u i)
  aut_comm i j x := by
    apply Subtype.ext
    show addTranslationMeroEquiv (sineFacePacketPeriods ω q u i)
      (addTranslationMeroEquiv (sineFacePacketPeriods ω q u j)
        (x : meroField (Set.univ : Set ℂ))) = _
    show _ = addTranslationMeroEquiv (sineFacePacketPeriods ω q u j)
      (addTranslationMeroEquiv (sineFacePacketPeriods ω q u i)
        (x : meroField (Set.univ : Set ℂ)))
    rw [addTranslationMeroEquiv_add, addTranslationMeroEquiv_add, add_comm]
  aut_deriv i x := by
    apply Subtype.ext
    exact addTranslationMeroEquiv_deriv (sineFacePacketPeriods ω q u i)
      (x : meroField (Set.univ : Set ℂ))
  aut_algebraMap i c := by
    apply Subtype.ext
    show addTranslationMeroEquiv (sineFacePacketPeriods ω q u i)
      (algebraMap ℂ (meroField (Set.univ : Set ℂ)) c) = _
    exact addTranslationMeroEquiv_algebraMap_complex _ c

@[simp]
theorem sineFaceDifferenceSystemClosed_aut_coe (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    {S : Set (Finset ι)} (hS : ∀ L ∈ S, ∀ p : ι, p ∉ L → insert p L ∈ S) (q u : ι) (i : Fin 2)
    (x : ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S))) :
    (((sineFaceDifferenceSystemClosed ω hω hS q u).aut i x :
        ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S))) :
      meroField (Set.univ : Set ℂ))
      = addTranslationMeroEquiv (sineFacePacketPeriods ω q u i)
        (x : meroField (Set.univ : Set ℂ)) := rfl

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **Descending face-lifting for the multiple sine over a closed family.**  If no nonzero constant
jet form of the displacements is a simultaneous defect in the deeper face field, the translation
block of the face is differentially independent over that field. -/
theorem sineFacePacket_differentialIndependent_of_no_telescoping_closed (ω : ι → ℂ)
    (hω : ∀ k, 0 < (ω k).im) {S : Set (Finset ι)}
    (hS : ∀ L ∈ S, ∀ p : ι, p ∉ L → insert p L ∈ S)
    (J : Finset ι) {q u : ι} (hqJ : q ∉ J) (huJ : u ∉ J)
    (h2 : 2 ≤ (Jᶜ : Finset ι).card) (hqS : insert q J ∈ S) (huS : insert u J ∈ S)
    {μ : ℂ} {rad : ι → ℝ} (hμ : μ ≠ 0)
    (hqω : ω q = μ * (rad q : ℂ)) (huω : ω u = μ * (rad u : ℂ))
    (hirr : Irrational (rad q / rad u))
    (hnot : ∀ c : (↥(facePacket ω hω J) × ℕ) →₀ ℂ, c ≠ 0 →
      ∀ k : ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S)), ∃ i,
        (sineFaceDifferenceSystemClosed ω hω hS q u).defect i k ≠
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
    (sineFaceDifferenceSystemClosed ω hω hS q u)
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

import GaloisForLFunctions.HTGeometry.SemilinearDifferentialRank
import GaloisForLFunctions.HTGeometry.FacePacketFreeTelescoping

/-!
# Completing one face layer over the deeper face field

The face-lifting lemma makes each individual `s`-face packet differentially independent over the
deeper face field `K_(s+1)`.  Uniform simplicial-star gluing then makes the whole `s`-layer jointly
independent over the same field.  The acting automorphisms are the structural translations, which
normalize `K_(s+1)` without fixing it, so the gluing theorem used is the base-normalizing one.

* **`facePacketSemilinearEquiv`** — a structural translation as a base-normalizing differential
  automorphism over the deeper face field;
* **`multipleEllipticGammaFaceStar_diffIndepOn_deeper`** — joint independence of a whole uniform
  face layer over the deeper face field.
-/

open Filter Topology Set Function Complex
open scoped Classical Differential

namespace GaloisForLFunctions

open Bottcher HTGeometry
open MatroidGluing MatroidGluing.Rank MatroidGluing.Meromorphic

noncomputable section

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The deeper face field is a differential algebra inside the ambient meromorphic field. -/
instance facePacketDeeperDifferentialAlgebra (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (S : Set (Finset ι)) :
    DifferentialAlgebra ↥(differentialAdjoin ℂ (facePacketUnion τ hτ S))
      (meroField (Set.univ : Set ℂ)) :=
  ⟨fun x => derivationClosedDifferential_apply _
    (derivationClosed_differentialAdjoin ℂ (facePacketUnion τ hτ S)) x⟩

/-- **A structural translation as a base-normalizing differential automorphism over the deeper face
field.**  It normalizes the deeper field by `facePacketFieldTranslation` and commutes with the
derivation. -/
def facePacketSemilinearEquiv (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) {S : Set (Finset ι)}
    (q : ι) (hS : ∀ L ∈ S, q ∉ L → insert q L ∈ S) :
    DifferentialSemilinearEquiv ↥(differentialAdjoin ℂ (facePacketUnion τ hτ S))
      (meroField (Set.univ : Set ℂ)) where
  baseEquiv := facePacketFieldTranslation τ hτ q hS
  ambientEquiv := addTranslationMeroEquiv (τ q)
  map_algebraMap' _ := rfl
  map_base_deriv' c := by
    apply Subtype.ext
    exact addTranslationMeroEquiv_deriv (τ q) (c : meroField (Set.univ : Set ℂ))
  map_ambient_deriv' x := addTranslationMeroEquiv_deriv (τ q) x

@[simp]
theorem facePacketSemilinearEquiv_ambient (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    {S : Set (Finset ι)} (q : ι) (hS : ∀ L ∈ S, q ∉ L → insert q L ∈ S)
    (x : meroField (Set.univ : Set ℂ)) :
    (facePacketSemilinearEquiv τ hτ q hS).ambientEquiv x =
      addTranslationMeroEquiv (τ q) x := rfl

set_option synthInstance.maxHeartbeats 400000 in
/-- **Joint independence of a whole uniform face layer over the deeper face field.**  Each face
packet is independent over the deeper field by the face-lifting lemma; the star of every direction
is a union of full translation orbits, so the nested-star gluing engine applies with the structural
translations acting as base-normalizing automorphisms. -/
theorem multipleEllipticGammaFaceStar_diffIndepOn_deeper (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    {S : Set (Finset ι)} (hS : ∀ L ∈ S, ∀ p : ι, p ∉ L → insert p L ∈ S)
    (faces : Finset (Finset ι)) (s : ℕ)
    (huniform : ∀ J ∈ faces, J.card = s)
    (hAtomic : ∀ J ∈ faces,
      DiffIndepOn ↥(differentialAdjoin ℂ (facePacketUnion τ hτ S))
        (multipleEllipticGammaFacePacket τ hτ J))
    (hStarInj : ∀ (A : Finset ι) (q : ι), A.card < s → q ∉ A →
      ∀ (m n : ℤ) (y z : meroField (Set.univ : Set ℂ)),
        y ∈ (⋃ J ∈ faces.filter (fun J => insert q A ⊆ J),
          multipleEllipticGammaFacePacketSlice τ hτ J q) →
        z ∈ (⋃ J ∈ faces.filter (fun J => insert q A ⊆ J),
          multipleEllipticGammaFacePacketSlice τ hτ J q) →
        (meroTranslationPerm (τ q) ^ m) y = (meroTranslationPerm (τ q) ^ n) z → m = n)
    (hOffDA : ∀ (A : Finset ι) (q : ι), A.card < s → q ∉ A →
      ∀ t : Finset (meroField (Set.univ : Set ℂ)),
        (↑t : Set (meroField (Set.univ : Set ℂ))) ⊆
          (⋃ J ∈ (faces.filter (fun J => A ⊆ J)).filter (fun J => q ∉ J),
            multipleEllipticGammaFacePacket τ hτ J) →
        ∀ n : ℤ, ∀ z ∈ (⇑(meroTranslationPerm (τ q) ^ n)) ''
            (↑t : Set (meroField (Set.univ : Set ℂ))),
          DifferentialAlgebraicOver
            (differentialAdjoin ↥(differentialAdjoin ℂ (facePacketUnion τ hτ S))
              (↑t : Set (meroField (Set.univ : Set ℂ)))) z) :
    DiffIndepOn ↥(differentialAdjoin ℂ (facePacketUnion τ hτ S))
      (faceStar faces (multipleEllipticGammaFacePacket τ hτ) ∅) := by
  refine differentialRank_uniformFace_nestedStar_diffIndepOn_of_orbit_semilinear
    faces (multipleEllipticGammaFacePacket τ hτ)
    (fun q => facePacketSemilinearEquiv τ hτ q (fun L hL hq => hS L hL q hq)) s huniform hAtomic
    (fun A q => ⋃ J ∈ faces.filter (fun J => insert q A ⊆ J),
      multipleEllipticGammaFacePacketSlice τ hτ J q)
    (fun A q _ _ => ?_) (fun A q hA hq => hStarInj A q hA hq)
    (fun A q hA hq t ht n z hz => hOffDA A q hA hq t ht n z (by
      simpa [Finset.coe_image] using hz))
  exact faceStar_eq_orbitUnion τ hτ faces A q

set_option synthInstance.maxHeartbeats 400000 in
/-- **Completing one face layer.**  Each face of a uniform layer has two surviving directions whose
next faces are deeper; the face-lifting lemma then makes every face packet independent over the
deeper face field, and star gluing makes the whole layer jointly independent over it. -/
theorem multipleEllipticGammaFaceLayer_diffIndepOn_deeper (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    {S : Set (Finset ι)} (hS : ∀ L ∈ S, ∀ p : ι, p ∉ L → insert p L ∈ S)
    (faces : Finset (Finset ι)) (s : ℕ)
    (huniform : ∀ J ∈ faces, J.card = s)
    (dq du : Finset ι → ι)
    (hq : ∀ J ∈ faces, dq J ∉ J) (hu : ∀ J ∈ faces, du J ∉ J)
    (hqS : ∀ J ∈ faces, insert (dq J) J ∈ S) (huS : ∀ J ∈ faces, insert (du J) J ∈ S)
    (hJS : ∀ J ∈ faces, J ∉ S)
    (hv : ∀ J ∈ faces, LinearIndependent ℚ (facePacketPeriods τ (dq J) (du J)))
    (hfree : ∀ J ∈ faces, DifferentialIndependent
      ↥(differentialAdjoin ℂ (facePacketUnion τ hτ (facePacketBaseFamily S J (dq J))))
      (facePalette τ hτ (insert (dq J) J) (dq J)))
    (hinjD : ∀ (J : Finset ι) (hJ : J ∈ faces),
      Function.Injective (facePacketDisplacementSlice τ hτ J (hq J hJ)))
    (hStarInj : ∀ (A : Finset ι) (q : ι), A.card < s → q ∉ A →
      ∀ (m n : ℤ) (y z : meroField (Set.univ : Set ℂ)),
        y ∈ (⋃ J ∈ faces.filter (fun J => insert q A ⊆ J),
          multipleEllipticGammaFacePacketSlice τ hτ J q) →
        z ∈ (⋃ J ∈ faces.filter (fun J => insert q A ⊆ J),
          multipleEllipticGammaFacePacketSlice τ hτ J q) →
        (meroTranslationPerm (τ q) ^ m) y = (meroTranslationPerm (τ q) ^ n) z → m = n)
    (hOffDA : ∀ (A : Finset ι) (q : ι), A.card < s → q ∉ A →
      ∀ t : Finset (meroField (Set.univ : Set ℂ)),
        (↑t : Set (meroField (Set.univ : Set ℂ))) ⊆
          (⋃ J ∈ (faces.filter (fun J => A ⊆ J)).filter (fun J => q ∉ J),
            multipleEllipticGammaFacePacket τ hτ J) →
        ∀ n : ℤ, ∀ z ∈ (⇑(meroTranslationPerm (τ q) ^ n)) ''
            (↑t : Set (meroField (Set.univ : Set ℂ))),
          DifferentialAlgebraicOver
            (differentialAdjoin ↥(differentialAdjoin ℂ (facePacketUnion τ hτ S))
              (↑t : Set (meroField (Set.univ : Set ℂ)))) z) :
    DiffIndepOn ↥(differentialAdjoin ℂ (facePacketUnion τ hτ S))
      (faceStar faces (multipleEllipticGammaFacePacket τ hτ) ∅) :=
  multipleEllipticGammaFaceStar_diffIndepOn_deeper τ hτ hS faces s huniform
    (fun J hJ => facePacket_differentialIndependent_of_free τ hτ hS J (hq J hJ) (hu J hJ)
      (hqS J hJ) (huS J hJ) (hJS J hJ) (hv J hJ) (hfree J hJ) (hinjD J hJ))
    hStarInj hOffDA

end

end GaloisForLFunctions

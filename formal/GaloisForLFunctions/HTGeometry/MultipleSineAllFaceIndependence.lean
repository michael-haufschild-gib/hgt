import GaloisForLFunctions.HTGeometry.MultipleSineFaceStarOrbit

/-!
# All maximal-face packets are jointly independent

The nested-star gluing engine takes three analytic inputs: each face packet is independent, each
star is a union of full orbits with distinct exponents, and each off-face direction moves a packet
only by a differentially algebraic amount.  All three are now available for the multiple-sine face
packets of a ray period family, so the engine applies and the union of all maximal-face packets is
differentially independent over the constants — and hence over `ℂ(z)`.

This is the joint atomicity of the top face layer: every external translate of every maximal-face
coordinate is differentially independent of all the others.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open GaloisForLFunctions.MatroidGluing GaloisForLFunctions.MatroidGluing.Rank
open GaloisForLFunctions.MatroidGluing.Meromorphic

noncomputable section

noncomputable local instance mafDecidableEq :
    DecidableEq (meroField (Set.univ : Set ℂ)) := Classical.decEq _

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The maximal faces: those whose complement is a pair. -/
def maximalFaces (ι : Type) [Fintype ι] [DecidableEq ι] : Finset (Finset ι) :=
  Finset.univ.filter (fun J => (Jᶜ : Finset ι).card = 2)

theorem mem_maximalFaces_iff (J : Finset ι) :
    J ∈ maximalFaces ι ↔ (Jᶜ : Finset ι).card = 2 := by
  rw [maximalFaces, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ J, h⟩⟩

theorem card_of_mem_maximalFaces {J : Finset ι} (hJ : J ∈ maximalFaces ι) :
    J.card = Fintype.card ι - 2 := by
  have hc := (mem_maximalFaces_iff J).mp hJ
  have htotal := Finset.card_add_card_compl J
  omega

/-- The translation of the meromorphic field, as a differential automorphism over the constants. -/
theorem toEquiv_addTranslationMeroDifferentialAlgEquiv (q : ℂ) :
    (addTranslationMeroDifferentialAlgEquiv q).toAlgEquiv.toEquiv
      = meroTranslationPerm q := rfl

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Joint atomicity of the top face layer.**  For a ray period family with rationally independent
periods, the union of the external packets of all maximal faces is differentially independent over
the complex constants. -/
theorem multipleSineMaximalFaces_diffIndepOn {μ : ℂ} {rad : ι → ℝ} (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im) :
    DiffIndepOn ℂ
      (faceStar (maximalFaces ι) (facePacket (fun k => μ * (rad k : ℂ)) hω) ∅) := by
  classical
  set ω : ι → ℂ := fun k => μ * (rad k : ℂ) with hωdef
  have hfaces : ∀ J ∈ maximalFaces ι, (Jᶜ : Finset ι).card = 2 :=
    fun J hJ => (mem_maximalFaces_iff J).mp hJ
  refine differentialRank_uniformFace_nestedStar_diffIndepOn_of_orbit
    (F := ℂ) (E := meroField (Set.univ : Set ℂ))
    (maximalFaces ι) (facePacket ω hω)
    (fun q => addTranslationMeroDifferentialAlgEquiv (ω q))
    (Fintype.card ι - 2)
    (fun J hJ => card_of_mem_maximalFaces hJ)
    (fun J hJ => diffIndepOn_facePacket hrad hind hω (hfaces J hJ))
    (fun A q => ⋃ J ∈ (maximalFaces ι).filter (fun J => insert q A ⊆ J),
      facePacketSlice ω hω J q)
    ?_ ?_ ?_
  · intro A q _ _
    rw [toEquiv_addTranslationMeroDifferentialAlgEquiv]
    exact faceStar_eq_orbitUnion ω hω (maximalFaces ι) A q
  · intro A q _ _ m n y z hy hz hyz
    rw [toEquiv_addTranslationMeroDifferentialAlgEquiv] at hyz
    exact facePacketSlice_zpow_injective hrad hind hω (maximalFaces ι) hfaces A q m n y z
      hy hz hyz
  · intro A q _ _ t ht n z hz
    rw [Finset.coe_image, toEquiv_addTranslationMeroDifferentialAlgEquiv] at hz
    obtain ⟨y, hyt, rfl⟩ := hz
    obtain ⟨J, hJ, hyJ⟩ := Set.mem_iUnion₂.mp (ht hyt)
    have hJf := Finset.mem_filter.mp hJ
    have hJf' := Finset.mem_filter.mp hJf.1
    have hqJ : q ∉ J := hJf.2
    have hJcard : (Jᶜ : Finset ι).card = 2 := hfaces J hJf'.1
    have hstep := differentialAlgebraicOver_facePacket_offStar ω hω hJcard hqJ hyJ n
    rw [meroTranslationPerm_zpow_apply]
    exact differentialAlgebraicOver_differentialAdjoin_of_sub (↑t : Set (meroField Set.univ))
      (subset_differentialAdjoin ℂ (↑t : Set (meroField Set.univ)) hyt) hstep

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Joint atomicity over the natural rational base.**  The same union is differentially
independent over the embedded rational coordinate field: adjoining the coordinate is a purely
differential-algebraic extension of the constants. -/
theorem multipleSineMaximalFaces_diffIndepOn_rationalBase {μ : ℂ} {rad : ι → ℝ}
    (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im) :
    DiffIndepOn meromorphicRationalCoordinateField
      (faceStar (maximalFaces ι) (facePacket (fun k => μ * (rad k : ℂ)) hω) ∅) := by
  have hC := multipleSineMaximalFaces_diffIndepOn hrad hind hω
  have hadj := HTGeometry.diffIndepOn_differentialAdjoin_singleton_of_differentialAlgebraicOver
    differentialAlgebraicOver_meromorphicRationalCoordinate hC
  rwa [differentialAdjoin_meromorphicRationalCoordinate_eq] at hadj

end

end GaloisForLFunctions.HTGeometry

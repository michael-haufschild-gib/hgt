import GaloisForLFunctions.HTGeometry.BottomFaceCrossSeparation
import GaloisForLFunctions.HTGeometry.BottomFacePacketUnconditional
import GaloisForLFunctions.HTGeometry.FaceLayerDescendingUnion

/-!
# The whole bottom layer is jointly differentially independent

All three hypotheses of the star gluing engine are available for the layer of faces with exactly
two surviving parameters: atomicity of each packet, faithfulness of the star exponent, and
differential algebraicity of the off-star translates.  Assembling them makes the union of all
bottom-face packets differentially independent over the constants, and — by differential-algebraic
base change — over any differentially algebraic extension of them.

* `addTranslationMeroDifferentialAlgEquiv_zpow_apply` — the bundled direction acts by translation;
* **`multipleEllipticGammaFaceStar_diffIndepOn_bottom`** — joint independence of the bottom layer;
* **`facePacketUnion_diffIndepOn_bottom`** — the same statement in packet-union form, which is the
  first step of the descending induction.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry
open MatroidGluing MatroidGluing.Rank MatroidGluing.Meromorphic

noncomputable section

attribute [local instance] facePacketMeroDecidableEq

attribute [local instance] ellipticGammaStructuralGeneratorRestrictedDifferential
  ellipticGammaStructuralGeneratorDifferentialAlgebra ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The bundled differential translation acts as the additive translation by the corresponding
integer multiple. -/
theorem addTranslationMeroDifferentialAlgEquiv_zpow_apply (q : ℂ) (n : ℤ)
    (x : meroField (Set.univ : Set ℂ)) :
    ((addTranslationMeroDifferentialAlgEquiv q).toAlgEquiv.toEquiv ^ n) x =
      addTranslationMeroEquiv ((n : ℂ) * q) x := by
  have hperm : (addTranslationMeroDifferentialAlgEquiv q).toAlgEquiv.toEquiv =
      meroTranslationPerm q := rfl
  rw [hperm, meroTranslationPerm_zpow_apply]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **Joint independence of the whole bottom layer.**  For a family of faces each having exactly two
surviving parameters, the union of the external orbit packets is differentially independent over the
constants.  Atomicity of a single packet is the order-one packet theorem transported along the
two-period normalization; the star exponent is faithful because on one face distinct lattice shifts
give distinct germs and across two faces no translates agree at all; and off-star translations are
structural, hence move a packet element by a differentially algebraic resonant defect. -/
theorem multipleEllipticGammaFaceStar_diffIndepOn_bottom
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (faces : Finset (Finset ι)) (s : ℕ)
    (huniform : ∀ J ∈ faces, J.card = s)
    (hbottom : ∀ J ∈ faces, ∃ a b : ι, a ∉ J ∧ b ∉ J ∧ a ≠ b ∧
      ∀ i, i ∉ J → i = a ∨ i = b) :
    DiffIndepOn ℂ (faceStar faces (multipleEllipticGammaFacePacket τ hτ) ∅) := by
  classical
  refine multipleEllipticGammaFaceStar_diffIndepOn τ hτ faces s huniform ?_ ?_ ?_
  · intro J hJfaces
    obtain ⟨a, b, haJ, hbJ, hab, hJ⟩ := hbottom J hJfaces
    exact diffIndepOn_of_diffIndepOn_differentialAdjoin
      (multipleEllipticGammaFacePacket_diffIndepOn_bottom τ hτ hQ J haJ hbJ hab hJ
        (linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent τ hQ hab)
        (G := (∅ : Set (meroField (Set.univ : Set ℂ)))) (by simp))
  · intro A q _ _ m n y z hy hz heq
    obtain ⟨J, hJmem, hyJ⟩ := Set.mem_iUnion₂.mp hy
    obtain ⟨J', hJ'mem, hzJ'⟩ := Set.mem_iUnion₂.mp hz
    obtain ⟨hJfaces, hJsub⟩ := Finset.mem_filter.mp hJmem
    obtain ⟨hJ'faces, -⟩ := Finset.mem_filter.mp hJ'mem
    obtain ⟨a, b, haJ, hbJ, hab, hJ⟩ := hbottom J hJfaces
    obtain ⟨a', b', haJ', hbJ', hab', hJ'⟩ := hbottom J' hJ'faces
    have hperiods :=
      linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent τ hQ hab
    have hperiods' :=
      linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent τ hQ hab'
    rw [addTranslationMeroDifferentialAlgEquiv_zpow_apply,
      addTranslationMeroDifferentialAlgEquiv_zpow_apply] at heq
    by_cases hJJ' : J = J'
    · subst hJJ'
      exact multipleEllipticGammaFacePacketSlice_exponent_eq_bottom τ hτ hQ J haJ hbJ hab hJ
        hperiods (hJsub (Finset.mem_insert_self q A)) hyJ hzJ' heq
    · rcases exists_separating_parameter_of_ne hJJ' with ⟨x, hxJ, hxJ'⟩ | ⟨x, hxJ', hxJ⟩
      · rcases hJ x hxJ with rfl | rfl
        · exact multipleEllipticGammaFacePacketSlice_exponent_eq_bottom_cross τ hτ hQ J J'
            haJ hbJ hab hJ haJ' hbJ' hab' hJ' hperiods hperiods' hxJ' hyJ hzJ' heq
        · exact multipleEllipticGammaFacePacketSlice_exponent_eq_bottom_cross τ hτ hQ J J'
            hbJ haJ hab.symm (fun i hi => (hJ i hi).symm) haJ' hbJ' hab' hJ'
            (linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent τ hQ
              hab.symm)
            hperiods' hxJ' hyJ hzJ' heq
      · rcases hJ' x hxJ' with rfl | rfl
        · exact (multipleEllipticGammaFacePacketSlice_exponent_eq_bottom_cross τ hτ hQ J' J
            haJ' hbJ' hab' hJ' haJ hbJ hab hJ hperiods' hperiods hxJ hzJ' hyJ heq.symm).symm
        · exact (multipleEllipticGammaFacePacketSlice_exponent_eq_bottom_cross τ hτ hQ J' J
            hbJ' haJ' hab'.symm (fun i hi => (hJ' i hi).symm) haJ hbJ hab hJ
            (linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent τ hQ
              hab'.symm)
            hperiods hxJ hzJ' hyJ heq.symm).symm
  · intro A q _ _ t ht n z hz
    obtain ⟨y, hyt, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hz)
    obtain ⟨J, hJmem, hyJ⟩ := Set.mem_iUnion₂.mp (ht (Finset.mem_coe.mpr hyt))
    obtain ⟨hJfilter, hqJ⟩ := Finset.mem_filter.mp hJmem
    obtain ⟨hJfaces, -⟩ := Finset.mem_filter.mp hJfilter
    obtain ⟨a, b, haJ, hbJ, hab, hJ⟩ := hbottom J hJfaces
    rw [addTranslationMeroDifferentialAlgEquiv_zpow_apply]
    exact differentialAlgebraicOver_offStar_translate_bottom τ hτ J haJ hbJ hab hJ
      (linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent τ hQ hab)
      hqJ n hyJ (Finset.mem_coe.mpr hyt)

set_option maxHeartbeats 800000 in
/-- **The bottom layer over a differentially algebraic extension.**  Adjoining differentially
algebraic coefficients does not change independence. -/
theorem multipleEllipticGammaFaceStar_diffIndepOn_bottom_daExtension
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (faces : Finset (Finset ι)) (s : ℕ)
    (huniform : ∀ J ∈ faces, J.card = s)
    (hbottom : ∀ J ∈ faces, ∃ a b : ι, a ∉ J ∧ b ∉ J ∧ a ≠ b ∧
      ∀ i, i ∉ J → i = a ∨ i = b)
    {G : Set (meroField (Set.univ : Set ℂ))}
    (hG : ∀ g ∈ G, DifferentialAlgebraicOver ℂ g) :
    DiffIndepOn ↥(differentialAdjoin ℂ G)
      (faceStar faces (multipleEllipticGammaFacePacket τ hτ) ∅) :=
  diffIndepOn_differentialAdjoin_of_differentialAlgebraicOver
    (multipleEllipticGammaFaceStar_diffIndepOn_bottom τ hτ hQ faces s huniform hbottom) hG

set_option maxHeartbeats 800000 in
/-- **The bottom layer in packet-union form.**  This is the base step of the descending induction
over face layers. -/
theorem facePacketUnion_diffIndepOn_bottom
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (faces : Finset (Finset ι)) (s : ℕ)
    (huniform : ∀ J ∈ faces, J.card = s)
    (hbottom : ∀ J ∈ faces, ∃ a b : ι, a ∉ J ∧ b ∉ J ∧ a ≠ b ∧
      ∀ i, i ∉ J → i = a ∨ i = b) :
    DiffIndepOn ℂ (facePacketUnion τ hτ (↑faces : Set (Finset ι))) := by
  rw [← faceStar_empty_eq_facePacketUnion]
  exact multipleEllipticGammaFaceStar_diffIndepOn_bottom τ hτ hQ faces s huniform hbottom

set_option maxHeartbeats 800000 in
/-- **The bottom layer over the empty deeper family.**  The first step of the descending induction
asks for independence over the field generated by the packets of the deeper faces, which at the
bottom is the differential adjunction of the empty set. -/
theorem facePacketUnion_diffIndepOn_bottom_step
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (faces : Finset (Finset ι)) (s : ℕ)
    (huniform : ∀ J ∈ faces, J.card = s)
    (hbottom : ∀ J ∈ faces, ∃ a b : ι, a ∉ J ∧ b ∉ J ∧ a ≠ b ∧
      ∀ i, i ∉ J → i = a ∨ i = b) :
    DiffIndepOn ↥(differentialAdjoin ℂ (facePacketUnion τ hτ (∅ : Set (Finset ι))))
      (facePacketUnion τ hτ (↑faces : Set (Finset ι))) := by
  rw [facePacketUnion_empty, ← faceStar_empty_eq_facePacketUnion]
  exact multipleEllipticGammaFaceStar_diffIndepOn_bottom_daExtension τ hτ hQ faces s huniform
    hbottom (by simp)

end

end GaloisForLFunctions

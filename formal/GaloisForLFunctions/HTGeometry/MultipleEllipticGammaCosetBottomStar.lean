import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaCosetBottomFace
import GaloisForLFunctions.HTGeometry.BottomFaceStarIndependence

/-!
# The labelled bottom layer is jointly independent

All three hypotheses of the star gluing engine are available for the labelled packets of the layer
of faces with exactly two surviving parameters.  The coset label is inert:

* atomicity is `cosetFacePacket_diffIndepOn_bottom`;
* the star exponent is faithful because the label and the lattice part of a labelled shift are
  uniquely determined, and across two faces no translates agree at all;
* off-star translations are structural, hence move a labelled packet element by a translate of a
  resonant defect, which is differentially algebraic.

* **`cosetFaceStar_diffIndepOn_bottom`** — joint independence of the labelled bottom layer;
* **`cosetFaceStar_diffIndepOn_bottom_family`** — the same for an arbitrary finite face family.
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

/-- Labelled slice points differing by a multiple of the deleted direction have equal
exponents. -/
theorem cosetFaceShiftSetSlice_zsmul_eq
    (τ : ι → ℂ) (hQ : PeriodsIntegrallyIndependent τ)
    {A : Set ℂ} (hA : CosetSeparated τ A) (J : Finset ι) {q : ι} (hq : q ∈ J)
    {m n : ℤ} {g g' : ℂ} (hg : g ∈ cosetFaceShiftSetSlice τ A J q)
    (hg' : g' ∈ cosetFaceShiftSetSlice τ A J q)
    (heq : (m : ℂ) * τ q + g = (n : ℂ) * τ q + g') : m = n := by
  classical
  obtain ⟨α, hα, u, hu, rfl⟩ := hg
  obtain ⟨α', hα', u', hu', rfl⟩ := hg'
  have hmem : (m : ℂ) * τ q + u ∈ faceShiftLattice τ J :=
    faceShiftLattice_add_zsmul τ J hq (faceShiftLatticeSlice_subset τ J q hu) m
  have hmem' : (n : ℂ) * τ q + u' ∈ faceShiftLattice τ J :=
    faceShiftLattice_add_zsmul τ J hq (faceShiftLatticeSlice_subset τ J q hu') n
  have hsplit : α + ((m : ℂ) * τ q + u) = α' + ((n : ℂ) * τ q + u') := by
    linear_combination heq
  obtain ⟨-, hlat⟩ :=
    cosetFaceShiftSet_label_unique τ hA J hα hα' hmem hmem' hsplit
  exact faceShiftLatticeSlice_zsmul_eq τ hQ J q hu hu' (by linear_combination hlat)

/-- **Star exponents on one labelled bottom face.** -/
theorem cosetFacePacketSlice_exponent_eq_bottom
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {A : Set ℂ} (hA : CosetSeparated τ A)
    (J : Finset ι) {a b : ι} (haJ : a ∉ J) (hbJ : b ∉ J) (hab : a ≠ b)
    (hJ : ∀ i, i ∉ J → i = a ∨ i = b)
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ a) (τ b)))
    {q : ι} (hq : q ∈ J) {m n : ℤ} {y z : meroField (Set.univ : Set ℂ)}
    (hy : y ∈ cosetFacePacketSlice τ hτ A J q)
    (hz : z ∈ cosetFacePacketSlice τ hτ A J q)
    (heq : addTranslationMeroEquiv ((m : ℂ) * τ q) y =
      addTranslationMeroEquiv ((n : ℂ) * τ q) z) :
    m = n := by
  classical
  obtain ⟨g, hg, rfl⟩ := hy
  obtain ⟨g', hg', rfl⟩ := hz
  rw [addTranslationMeroEquiv_add, addTranslationMeroEquiv_add] at heq
  have hmem : ((m : ℂ) * τ q + g) ∈ cosetFaceShiftSet τ A J :=
    cosetFaceShiftSet_add_zsmul τ A J hq (cosetFaceShiftSetSlice_subset τ A J q hg) m
  have hmem' : ((n : ℂ) * τ q + g') ∈ cosetFaceShiftSet τ A J :=
    cosetFaceShiftSet_add_zsmul τ A J hq (cosetFaceShiftSetSlice_subset τ A J q hg') n
  have hshift := cosetFaceShiftSet_translate_injective_bottom τ hτ hQ hA J haJ hbJ hab hJ
    hperiods hmem hmem' heq
  exact cosetFaceShiftSetSlice_zsmul_eq τ hQ hA J hq hg hg' hshift

/-- **Cross-face star exponents at the labelled bottom layer.** -/
theorem cosetFacePacketSlice_exponent_eq_bottom_cross
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (A : Set ℂ)
    (J J' : Finset ι) {a b a' b' : ι}
    (haJ : a ∉ J) (hbJ : b ∉ J) (hab : a ≠ b) (hJ : ∀ i, i ∉ J → i = a ∨ i = b)
    (haJ' : a' ∉ J') (hbJ' : b' ∉ J') (hab' : a' ≠ b') (hJ' : ∀ i, i ∉ J' → i = a' ∨ i = b')
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ a) (τ b)))
    (hperiods' : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ a') (τ b')))
    (hsepa : a ∈ J') {q : ι} {m n : ℤ} {y z : meroField (Set.univ : Set ℂ)}
    (hy : y ∈ cosetFacePacketSlice τ hτ A J q)
    (hz : z ∈ cosetFacePacketSlice τ hτ A J' q)
    (heq : addTranslationMeroEquiv ((m : ℂ) * τ q) y =
      addTranslationMeroEquiv ((n : ℂ) * τ q) z) :
    m = n := by
  classical
  exfalso
  obtain ⟨g, -, rfl⟩ := hy
  obtain ⟨g', -, rfl⟩ := hz
  rw [addTranslationMeroEquiv_add, addTranslationMeroEquiv_add] at heq
  have haa' : a ≠ a' := fun h => haJ' (h ▸ hsepa)
  have hab'' : a ≠ b' := fun h => hbJ' (h ▸ hsepa)
  exact multipleEllipticGammaFace_translate_ne_bottom τ hτ hQ J J' haJ hbJ hab hJ
    haJ' hbJ' hab' hJ' hperiods hperiods' haa' hab'' _ _ heq

/-- **Off-star displacements at the labelled bottom layer are differentially algebraic.** -/
theorem differentialAlgebraicOver_cosetOffStar_displacement_bottom
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ) (J : Finset ι) {a b : ι}
    (haJ : a ∉ J) (hbJ : b ∉ J) (hab : a ≠ b) (hJ : ∀ i, i ∉ J → i = a ∨ i = b)
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ a) (τ b)))
    {q : ι} (hq : q ∉ J) (n : ℤ) {y : meroField (Set.univ : Set ℂ)}
    (hy : y ∈ cosetFacePacket τ hτ A J) :
    DifferentialAlgebraicOver ℂ
      (addTranslationMeroEquiv ((n : ℂ) * τ q) y - y) := by
  classical
  obtain ⟨g, -, rfl⟩ := hy
  show DifferentialAlgebraicOver ℂ
    (addTranslationMeroEquiv ((n : ℂ) * τ q)
        (addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ J)) -
      addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ J))
  have hform : ∀ (s : ℂ) (Ψ : meroField (Set.univ : Set ℂ)) (t : ℂ),
      addTranslationMeroEquiv t (addTranslationMeroEquiv s Ψ) -
          addTranslationMeroEquiv s Ψ =
        addTranslationMeroEquiv s (addTranslationMeroEquiv t Ψ - Ψ) := by
    intro s Ψ t
    rw [map_sub, addTranslationMeroEquiv_add, addTranslationMeroEquiv_add, add_comm s t]
  rw [hform, multipleEllipticGammaLogDerivFaceMero_two_surviving τ hτ J haJ hbJ hab hJ,
    hform, addTranslationMeroEquiv_add]
  have hres : ∃ p r' r : ℤ, (n : ℂ) * τ q = p + r' * τ b + r * τ a := by
    rcases hJ q hq with rfl | rfl
    · exact ⟨0, 0, n, by push_cast; ring⟩
    · exact ⟨0, n, 0, by push_cast; ring⟩
  exact differentialAlgebraicOver_translate_resonant_defect (hτ a) (hτ b) hperiods hres

set_option synthInstance.maxHeartbeats 800000 in
/-- **Off-star translates are differentially algebraic over any generated field containing the
point.** -/
theorem differentialAlgebraicOver_cosetOffStar_translate_bottom
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ) (J : Finset ι) {a b : ι}
    (haJ : a ∉ J) (hbJ : b ∉ J) (hab : a ≠ b) (hJ : ∀ i, i ∉ J → i = a ∨ i = b)
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ a) (τ b)))
    {q : ι} (hq : q ∉ J) (n : ℤ) {t : Set (meroField (Set.univ : Set ℂ))}
    {y : meroField (Set.univ : Set ℂ)} (hy : y ∈ cosetFacePacket τ hτ A J)
    (hyt : y ∈ t) :
    DifferentialAlgebraicOver ↥(differentialAdjoin ℂ t)
      (addTranslationMeroEquiv ((n : ℂ) * τ q) y) := by
  classical
  haveI : DifferentialAlgebra ↥(differentialAdjoin ℂ t) (meroField (Set.univ : Set ℂ)) :=
    ⟨fun x => derivationClosedDifferential_apply _
      (derivationClosed_differentialAdjoin ℂ t) x⟩
  have hdC := differentialAlgebraicOver_cosetOffStar_displacement_bottom τ hτ A J haJ hbJ hab hJ
    hperiods hq n hy
  have hd : DifferentialAlgebraicOver ↥(differentialAdjoin ℂ t)
      (addTranslationMeroEquiv ((n : ℂ) * τ q) y - y) := by
    intro hind
    exact hdC (HTGeometry.DifferentialIndependent.restrictScalarsTower hind)
  have hyD : DifferentialAlgebraicOver ↥(differentialAdjoin ℂ t) y := by
    have := HTGeometry.differentialAlgebraicOver_algebraMap
      (E := meroField (Set.univ : Set ℂ))
      (⟨y, subset_differentialAdjoin ℂ t hyt⟩ : ↥(differentialAdjoin ℂ t))
    simpa using this
  have hsum := differentialAlgebraicOver_add hd hyD
  simpa using hsum

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Joint independence of the whole labelled bottom layer.** -/
theorem cosetFaceStar_diffIndepOn_bottom
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {A : Set ℂ} (hA : CosetSeparated τ A)
    (faces : Finset (Finset ι)) (s : ℕ)
    (huniform : ∀ J ∈ faces, J.card = s)
    (hbottom : ∀ J ∈ faces, ∃ a b : ι, a ∉ J ∧ b ∉ J ∧ a ≠ b ∧
      ∀ i, i ∉ J → i = a ∨ i = b) :
    DiffIndepOn ℂ (faceStar faces (cosetFacePacket τ hτ A) ∅) := by
  classical
  refine cosetFaceStar_diffIndepOn τ hτ A faces s huniform ?_ ?_ ?_
  · intro J hJfaces
    obtain ⟨a, b, haJ, hbJ, hab, hJ⟩ := hbottom J hJfaces
    exact diffIndepOn_of_diffIndepOn_differentialAdjoin
      (cosetFacePacket_diffIndepOn_bottom τ hτ hQ hA J haJ hbJ hab hJ
        (linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent τ hQ hab)
        (G := (∅ : Set (meroField (Set.univ : Set ℂ)))) (by simp))
  · intro B q _ _ m n y z hy hz heq
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
      exact cosetFacePacketSlice_exponent_eq_bottom τ hτ hQ hA J haJ hbJ hab hJ
        hperiods (hJsub (Finset.mem_insert_self q B)) hyJ hzJ' heq
    · rcases exists_separating_parameter_of_ne hJJ' with ⟨x, hxJ, hxJ'⟩ | ⟨x, hxJ', hxJ⟩
      · rcases hJ x hxJ with rfl | rfl
        · exact cosetFacePacketSlice_exponent_eq_bottom_cross τ hτ hQ A J J'
            haJ hbJ hab hJ haJ' hbJ' hab' hJ' hperiods hperiods' hxJ' hyJ hzJ' heq
        · exact cosetFacePacketSlice_exponent_eq_bottom_cross τ hτ hQ A J J'
            hbJ haJ hab.symm (fun i hi => (hJ i hi).symm) haJ' hbJ' hab' hJ'
            (linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent τ hQ
              hab.symm)
            hperiods' hxJ' hyJ hzJ' heq
      · rcases hJ' x hxJ' with rfl | rfl
        · exact (cosetFacePacketSlice_exponent_eq_bottom_cross τ hτ hQ A J' J
            haJ' hbJ' hab' hJ' haJ hbJ hab hJ hperiods' hperiods hxJ hzJ' hyJ heq.symm).symm
        · exact (cosetFacePacketSlice_exponent_eq_bottom_cross τ hτ hQ A J' J
            hbJ' haJ' hab'.symm (fun i hi => (hJ' i hi).symm) haJ hbJ hab hJ
            (linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent τ hQ
              hab'.symm)
            hperiods hxJ hzJ' hyJ heq.symm).symm
  · intro B q _ _ t ht n z hz
    obtain ⟨y, hyt, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hz)
    obtain ⟨J, hJmem, hyJ⟩ := Set.mem_iUnion₂.mp (ht (Finset.mem_coe.mpr hyt))
    obtain ⟨hJfilter, hqJ⟩ := Finset.mem_filter.mp hJmem
    obtain ⟨hJfaces, -⟩ := Finset.mem_filter.mp hJfilter
    obtain ⟨a, b, haJ, hbJ, hab, hJ⟩ := hbottom J hJfaces
    rw [addTranslationMeroDifferentialAlgEquiv_zpow_apply]
    exact differentialAlgebraicOver_cosetOffStar_translate_bottom τ hτ A J haJ hbJ hab hJ
      (linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent τ hQ hab)
      hqJ n hyJ (Finset.mem_coe.mpr hyt)

/-- **The labelled bottom layer over a differentially algebraic extension.** -/
theorem cosetFaceStar_diffIndepOn_bottom_daExtension
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {A : Set ℂ} (hA : CosetSeparated τ A)
    (faces : Finset (Finset ι)) (s : ℕ)
    (huniform : ∀ J ∈ faces, J.card = s)
    (hbottom : ∀ J ∈ faces, ∃ a b : ι, a ∉ J ∧ b ∉ J ∧ a ≠ b ∧
      ∀ i, i ∉ J → i = a ∨ i = b)
    {G : Set (meroField (Set.univ : Set ℂ))}
    (hG : ∀ g ∈ G, DifferentialAlgebraicOver ℂ g) :
    DiffIndepOn ↥(differentialAdjoin ℂ G)
      (faceStar faces (cosetFacePacket τ hτ A) ∅) :=
  diffIndepOn_differentialAdjoin_of_differentialAlgebraicOver
    (cosetFaceStar_diffIndepOn_bottom τ hτ hQ hA faces s huniform hbottom) hG

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Joint independence of an arbitrary finite family of labelled bottom faces.** -/
theorem cosetFaceStar_diffIndepOn_bottom_family
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {A : Set ℂ} (hA : CosetSeparated τ A)
    (faces : Finset (Finset ι))
    (hbottom : ∀ J ∈ faces, ∃ a b : ι, a ∉ J ∧ b ∉ J ∧ a ≠ b ∧
      ∀ i, i ∉ J → i = a ∨ i = b) :
    DiffIndepOn ℂ (faceStar faces (cosetFacePacket τ hτ A) ∅) := by
  classical
  apply cosetFaceStar_diffIndepOn_bottom
    τ hτ hQ hA faces (Fintype.card ι - 2) _ hbottom
  intro J hJfaces
  obtain ⟨a, b, haJ, hbJ, hab, hJ⟩ := hbottom J hJfaces
  have hcomp : Jᶜ = {a, b} := by
    ext i
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact hJ i
    · rintro (rfl | rfl)
      · exact haJ
      · exact hbJ
  have hcardcomp : (Jᶜ).card = 2 := by
    rw [hcomp, Finset.card_pair hab]
  have htotal := Finset.card_add_card_compl J
  omega

end

end GaloisForLFunctions

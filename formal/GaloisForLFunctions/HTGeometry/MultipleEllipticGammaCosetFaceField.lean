import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaCosetFaceDisjointness
import GaloisForLFunctions.HTGeometry.FacePacketFieldTranslation
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaFacePalette

/-!
# The labelled face field and its translations

The labelled analogues of the coface system, the generated differential field of a family of
labelled packets, its stability under the structural translations, and the bilateral palette used
by the one-slice nonsummability obstruction.  Every proof is the unlabelled one with the label
carried along: the label commutes with every translation.

* `cosetFacePacketUnion` — the union of the labelled packets of a family of faces;
* **`differentialAdjoin_cosetFacePacketUnion_translate_stable`** and its inverse form;
* `cosetFacePacketFieldTranslation` — the structural translation as a field automorphism;
* `cosetFacePalette` and **`cosetFacePacket_oneSlice_ne_coboundary`**.
-/

open Filter Topology Set Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher MatroidGluing MatroidGluing.Rank MatroidGluing.Meromorphic

noncomputable section

attribute [local instance] facePacketMeroDecidableEq

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The labelled coface system -/

/-- **A deleted direction preserves the labelled packet.** -/
theorem cosetFacePacket_translate_mem (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ)
    (J : Finset ι) {q : ι} (hq : q ∈ J) {y : meroField (Set.univ : Set ℂ)}
    (hy : y ∈ cosetFacePacket τ hτ A J) :
    addTranslationMeroEquiv (τ q) y ∈ cosetFacePacket τ hτ A J := by
  obtain ⟨g, hg, rfl⟩ := hy
  refine ⟨τ q + g, ?_, ?_⟩
  · have h1 : ((1 : ℤ) : ℂ) * τ q + g ∈ cosetFaceShiftSet τ A J :=
      cosetFaceShiftSet_add_zsmul τ A J hq hg 1
    simpa using h1
  · rw [addTranslationMeroEquiv_add]

/-- **A surviving direction changes a labelled packet element by an element of the next labelled
packet.** -/
theorem cosetFacePacket_translate_sub_mem (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ)
    (J : Finset ι) {q : ι} (hq : q ∉ J) {y : meroField (Set.univ : Set ℂ)}
    (hy : y ∈ cosetFacePacket τ hτ A J) :
    addTranslationMeroEquiv (τ q) y - y ∈ cosetFacePacket τ hτ A (insert q J) := by
  obtain ⟨g, hg, rfl⟩ := hy
  refine ⟨g, cosetFaceShiftSet_mono τ A (Finset.subset_insert q J) hg, ?_⟩
  exact (facePacket_coface τ hτ J hq g).symm

/-! ## The generated field of a labelled family -/

/-- The union of the labelled packets of a family of deleted faces. -/
def cosetFacePacketUnion (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ)
    (S : Set (Finset ι)) : Set (meroField (Set.univ : Set ℂ)) :=
  ⋃ L ∈ S, cosetFacePacket τ hτ A L

theorem cosetFacePacketUnion_empty (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ) :
    cosetFacePacketUnion τ hτ A (∅ : Set (Finset ι)) = ∅ := by
  simp [cosetFacePacketUnion]

theorem cosetFacePacketUnion_union (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ)
    (S T : Set (Finset ι)) :
    cosetFacePacketUnion τ hτ A (S ∪ T) =
      cosetFacePacketUnion τ hτ A S ∪ cosetFacePacketUnion τ hτ A T := by
  ext y
  simp only [cosetFacePacketUnion, Set.mem_iUnion, Set.mem_union, exists_prop]
  constructor
  · rintro ⟨L, hL | hL, hyL⟩
    · exact Or.inl ⟨L, hL, hyL⟩
    · exact Or.inr ⟨L, hL, hyL⟩
  · rintro (⟨L, hL, hyL⟩ | ⟨L, hL, hyL⟩)
    · exact ⟨L, Or.inl hL, hyL⟩
    · exact ⟨L, Or.inr hL, hyL⟩

theorem cosetFaceStar_empty_eq_cosetFacePacketUnion (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (A : Set ℂ) (faces : Finset (Finset ι)) :
    faceStar faces (cosetFacePacket τ hτ A) ∅ =
      cosetFacePacketUnion τ hτ A (↑faces : Set (Finset ι)) := by
  rw [faceStar, cosetFacePacketUnion]
  refine Set.iUnion_congr fun J => ?_
  refine Set.iUnion_congr_Prop ?_ fun _ => rfl
  simp

/-- **The generators move inside the generated field.** -/
theorem cosetFacePacketUnion_translate_mem (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ)
    {S : Set (Finset ι)} (q : ι) (hS : ∀ L ∈ S, q ∉ L → insert q L ∈ S)
    {y : meroField (Set.univ : Set ℂ)} (hy : y ∈ cosetFacePacketUnion τ hτ A S) :
    addTranslationMeroEquiv (τ q) y ∈
      differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S) := by
  obtain ⟨L, hL, hyL⟩ := Set.mem_iUnion₂.mp hy
  by_cases hqL : q ∈ L
  · refine subset_differentialAdjoin ℂ _ ?_
    exact Set.mem_iUnion₂.mpr ⟨L, hL, cosetFacePacket_translate_mem τ hτ A L hqL hyL⟩
  · have hnext : addTranslationMeroEquiv (τ q) y - y ∈
        cosetFacePacket τ hτ A (insert q L) :=
      cosetFacePacket_translate_sub_mem τ hτ A L hqL hyL
    have hy' : y ∈ differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S) :=
      subset_differentialAdjoin ℂ _ (Set.mem_iUnion₂.mpr ⟨L, hL, hyL⟩)
    have hnext' : addTranslationMeroEquiv (τ q) y - y ∈
        differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S) :=
      subset_differentialAdjoin ℂ _
        (Set.mem_iUnion₂.mpr ⟨insert q L, hS L hL hqL, hnext⟩)
    have hsum := (differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S)).add_mem hnext' hy'
    simpa using hsum

set_option synthInstance.maxHeartbeats 400000 in
/-- **The labelled deeper face field is translation stable.** -/
theorem differentialAdjoin_cosetFacePacketUnion_translate_stable (τ : ι → ℂ)
    (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ)
    {S : Set (Finset ι)} (q : ι) (hS : ∀ L ∈ S, q ∉ L → insert q L ∈ S)
    {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S)) :
    addTranslationMeroEquiv (τ q) x ∈
      differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S) :=
  differentialAdjoin_translate_stable_of_generators (τ q) _
    (fun _y hy => cosetFacePacketUnion_translate_mem τ hτ A q hS hy) hx

/-- **The inverse translation also moves the labelled generators inside the generated field.** -/
theorem cosetFacePacketUnion_neg_translate_mem (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ)
    {S : Set (Finset ι)} (q : ι) (hS : ∀ L ∈ S, q ∉ L → insert q L ∈ S)
    {y : meroField (Set.univ : Set ℂ)} (hy : y ∈ cosetFacePacketUnion τ hτ A S) :
    addTranslationMeroEquiv (-τ q) y ∈
      differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S) := by
  obtain ⟨L, hL, hyL⟩ := Set.mem_iUnion₂.mp hy
  obtain ⟨g, hg, rfl⟩ := hyL
  by_cases hqL : q ∈ L
  · refine subset_differentialAdjoin ℂ _ ?_
    refine Set.mem_iUnion₂.mpr ⟨L, hL, ?_⟩
    refine ⟨-τ q + g, ?_, ?_⟩
    · have h1 : ((-1 : ℤ) : ℂ) * τ q + g ∈ cosetFaceShiftSet τ A L :=
        cosetFaceShiftSet_add_zsmul τ A L hqL hg (-1)
      simpa using h1
    · rw [addTranslationMeroEquiv_add]
  · have hlat : -τ q + g ∈ cosetFaceShiftSet τ A (insert q L) := by
      have hgIns : g ∈ cosetFaceShiftSet τ A (insert q L) :=
        cosetFaceShiftSet_mono τ A (Finset.subset_insert q L) hg
      have h1 : ((-1 : ℤ) : ℂ) * τ q + g ∈ cosetFaceShiftSet τ A (insert q L) :=
        cosetFaceShiftSet_add_zsmul τ A (insert q L) (Finset.mem_insert_self q L) hgIns (-1)
      simpa using h1
    have hcoface := facePacket_coface τ hτ L hqL (-τ q + g)
    have hcancel : addTranslationMeroEquiv (τ q)
        (addTranslationMeroEquiv (-τ q + g)
          (multipleEllipticGammaLogDerivFaceMero τ hτ L)) =
        addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ L) := by
      have harg : τ q + (-τ q + g) = g := by ring
      rw [addTranslationMeroEquiv_add, harg]
    rw [hcancel] at hcoface
    have hnext : addTranslationMeroEquiv (-τ q + g)
        (multipleEllipticGammaLogDerivFaceMero τ hτ (insert q L)) ∈
        differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S) :=
      subset_differentialAdjoin ℂ _
        (Set.mem_iUnion₂.mpr ⟨insert q L, hS L hL hqL, ⟨-τ q + g, hlat, rfl⟩⟩)
    have hy' : addTranslationMeroEquiv g
        (multipleEllipticGammaLogDerivFaceMero τ hτ L) ∈
        differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S) :=
      subset_differentialAdjoin ℂ _
        (Set.mem_iUnion₂.mpr ⟨L, hL, ⟨g, hg, rfl⟩⟩)
    have hsplit : addTranslationMeroEquiv (-τ q)
        (addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ L)) =
        addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ L) -
          addTranslationMeroEquiv (-τ q + g)
            (multipleEllipticGammaLogDerivFaceMero τ hτ (insert q L)) := by
      have hL2 : addTranslationMeroEquiv (-τ q)
          (addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ L)) =
          addTranslationMeroEquiv (-τ q + g)
            (multipleEllipticGammaLogDerivFaceMero τ hτ L) :=
        addTranslationMeroEquiv_add _ _ _
      rw [hL2, ← hcoface]
      abel
    rw [hsplit]
    exact (differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S)).sub_mem hy' hnext

/-- **The labelled deeper face field is stable under the inverse translation.** -/
theorem differentialAdjoin_cosetFacePacketUnion_neg_translate_stable (τ : ι → ℂ)
    (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ) {S : Set (Finset ι)} (q : ι)
    (hS : ∀ L ∈ S, q ∉ L → insert q L ∈ S)
    {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S)) :
    addTranslationMeroEquiv (-τ q) x ∈
      differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S) :=
  differentialAdjoin_translate_stable_of_generators (-τ q) _
    (fun _y hy => cosetFacePacketUnion_neg_translate_mem τ hτ A q hS hy) hx

/-- **The structural translation as an automorphism of the labelled deeper face field.** -/
def cosetFacePacketFieldTranslation (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ)
    {S : Set (Finset ι)} (q : ι) (hS : ∀ L ∈ S, q ∉ L → insert q L ∈ S) :
    differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S) ≃+*
      differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S) where
  toFun x := ⟨addTranslationMeroEquiv (τ q) (x : meroField (Set.univ : Set ℂ)),
    differentialAdjoin_cosetFacePacketUnion_translate_stable τ hτ A q hS x.2⟩
  invFun x := ⟨addTranslationMeroEquiv (-τ q) (x : meroField (Set.univ : Set ℂ)),
    differentialAdjoin_cosetFacePacketUnion_neg_translate_stable τ hτ A q hS x.2⟩
  left_inv x := by
    apply Subtype.ext
    show addTranslationMeroEquiv (-τ q)
      (addTranslationMeroEquiv (τ q) (x : meroField (Set.univ : Set ℂ))) = _
    rw [addTranslationMeroEquiv_add, neg_add_cancel, addTranslationMeroEquiv_zero_apply]
  right_inv x := by
    apply Subtype.ext
    show addTranslationMeroEquiv (τ q)
      (addTranslationMeroEquiv (-τ q) (x : meroField (Set.univ : Set ℂ))) = _
    rw [addTranslationMeroEquiv_add, add_neg_cancel, addTranslationMeroEquiv_zero_apply]
  map_mul' x y := by
    apply Subtype.ext
    show addTranslationMeroEquiv (τ q)
      ((x : meroField (Set.univ : Set ℂ)) * (y : meroField (Set.univ : Set ℂ))) = _
    rw [map_mul]
    rfl
  map_add' x y := by
    apply Subtype.ext
    show addTranslationMeroEquiv (τ q)
      ((x : meroField (Set.univ : Set ℂ)) + (y : meroField (Set.univ : Set ℂ))) = _
    rw [map_add]
    rfl

@[simp]
theorem cosetFacePacketFieldTranslation_coe (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ)
    {S : Set (Finset ι)} (q : ι) (hS : ∀ L ∈ S, q ∉ L → insert q L ∈ S)
    (x : differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S)) :
    ((cosetFacePacketFieldTranslation τ hτ A q hS x :
        differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S)) :
        meroField (Set.univ : Set ℂ)) =
      addTranslationMeroEquiv (τ q) (x : meroField (Set.univ : Set ℂ)) := rfl

/-! ## The labelled palette -/

/-- The bilateral palette of the labelled packet of the deleted face `J` in the direction `q`. -/
def cosetFacePalette (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ) (J : Finset ι) (q : ι) :
    (↥(cosetFacePacketSlice τ hτ A J q) × ℤ) → meroField (Set.univ : Set ℂ) :=
  fun p => addTranslationMeroEquiv ((p.2 : ℂ) * τ q) (p.1 : meroField (Set.univ : Set ℂ))

/-- **The genuine translation moves the labelled palette one slice.** -/
theorem cosetFacePalette_shift (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ)
    (J : Finset ι) (q : ι) (p : ↥(cosetFacePacketSlice τ hτ A J q) × ℤ) :
    (addTranslationMeroDifferentialAlgEquiv (τ q)).toAlgEquiv (cosetFacePalette τ hτ A J q p) =
      cosetFacePalette τ hτ A J q (p.1, p.2 + 1) := by
  have harg : τ q + (p.2 : ℂ) * τ q = ((p.2 + 1 : ℤ) : ℂ) * τ q := by push_cast; ring
  show addTranslationMeroEquiv (τ q)
      (addTranslationMeroEquiv ((p.2 : ℂ) * τ q) (p.1 : meroField (Set.univ : Set ℂ))) = _
  rw [addTranslationMeroEquiv_add, harg]
  rfl

/-- **The labelled palette enumerates the labelled packet.** -/
theorem range_cosetFacePalette (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ)
    (J : Finset ι) {q : ι} (hq : q ∈ J) :
    Set.range (cosetFacePalette τ hτ A J q) = cosetFacePacket τ hτ A J := by
  rw [cosetFacePacket_eq_orbitUnion τ hτ A J hq]
  ext y
  constructor
  · rintro ⟨⟨a, m⟩, rfl⟩
    refine ⟨m, (a : meroField (Set.univ : Set ℂ)), a.2, ?_⟩
    rw [meroTranslationPerm_zpow_apply]
    rfl
  · rintro ⟨m, a, ha, rfl⟩
    refine ⟨(⟨a, ha⟩, m), ?_⟩
    show addTranslationMeroEquiv ((m : ℂ) * τ q) a = _
    rw [meroTranslationPerm_zpow_apply]

/-- **One-slice nonsummability on a labelled face packet.** -/
theorem cosetFacePacket_oneSlice_ne_coboundary (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (A : Set ℂ) (J : Finset ι) (q : ι)
    (hindep : DifferentialIndependent ℂ (cosetFacePalette τ hτ A J q))
    (c : (↥(cosetFacePacketSlice τ hτ A J q) × ℕ) →₀ ℂ) (hc : c ≠ 0)
    (g : differentialAdjoin ℂ (Set.range (cosetFacePalette τ hτ A J q))) :
    (addTranslationMeroDifferentialAlgEquiv (τ q)).toAlgEquiv
        (g : meroField (Set.univ : Set ℂ)) - (g : meroField (Set.univ : Set ℂ)) ≠
      ((c.sum (fun j a =>
        algebraMap ℂ (differentialAdjoin ℂ (Set.range (cosetFacePalette τ hτ A J q))) a *
          ⟨differentialJet j.2 (cosetFacePalette τ hτ A J q (j.1, 0)),
            differentialJet_mem_differentialAdjoin ℂ
              (Set.mem_range_self (j.1, 0)) j.2⟩) :
        differentialAdjoin ℂ (Set.range (cosetFacePalette τ hτ A J q))) :
        meroField (Set.univ : Set ℂ)) :=
  oneSlice_ne_coboundary_of_ambient_shift (cosetFacePalette τ hτ A J q) hindep
    (addTranslationMeroDifferentialAlgEquiv (τ q))
    (fun p => cosetFacePalette_shift τ hτ A J q p) c hc g

end

end GaloisForLFunctions

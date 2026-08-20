import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaCosetFreeTelescoping
import GaloisForLFunctions.HTGeometry.FacePacketLayerGluing
import GaloisForLFunctions.HTGeometry.FaceLayerOffStarDisplacement
import GaloisForLFunctions.HTGeometry.FaceLayerDescendingUnion

/-!
# Labelled layer gluing, off-star displacement, and the descending step

The labelled analogues of `FacePacketLayerGluing`, `FaceLayerOffStarDisplacement` and
`FaceLayerDescendingUnion`.

* `cosetFacePacketSemilinearEquiv` — the structural translation as a base-normalizing differential
  automorphism over the labelled deeper field;
* **`cosetFaceStar_diffIndepOn_deeper`**, **`cosetFaceLayer_diffIndepOn_deeper`**;
* **`differentialAlgebraicOver_cosetOffStar_translate_deeper`** — the off-star hypothesis;
* **`cosetFacePacketUnion_diffIndepOn_union`** — the descending step.
-/

open Filter Topology Set Function Complex
open scoped Differential BigOperators

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

/-- The labelled deeper face field is a differential algebra inside the ambient meromorphic
field. -/
instance cosetFacePacketDeeperDifferentialAlgebra (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (A : Set ℂ) (S : Set (Finset ι)) :
    DifferentialAlgebra ↥(differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S))
      (meroField (Set.univ : Set ℂ)) :=
  ⟨fun x => derivationClosedDifferential_apply _
    (derivationClosed_differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S)) x⟩

/-- **A structural translation as a base-normalizing differential automorphism over the labelled
deeper face field.** -/
def cosetFacePacketSemilinearEquiv (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ)
    {S : Set (Finset ι)} (q : ι) (hS : ∀ L ∈ S, q ∉ L → insert q L ∈ S) :
    DifferentialSemilinearEquiv ↥(differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S))
      (meroField (Set.univ : Set ℂ)) where
  baseEquiv := cosetFacePacketFieldTranslation τ hτ A q hS
  ambientEquiv := addTranslationMeroEquiv (τ q)
  map_algebraMap' _ := rfl
  map_base_deriv' c := by
    apply Subtype.ext
    exact addTranslationMeroEquiv_deriv (τ q) (c : meroField (Set.univ : Set ℂ))
  map_ambient_deriv' x := addTranslationMeroEquiv_deriv (τ q) x

@[simp]
theorem cosetFacePacketSemilinearEquiv_ambient (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ)
    {S : Set (Finset ι)} (q : ι) (hS : ∀ L ∈ S, q ∉ L → insert q L ∈ S)
    (x : meroField (Set.univ : Set ℂ)) :
    (cosetFacePacketSemilinearEquiv τ hτ A q hS).ambientEquiv x =
      addTranslationMeroEquiv (τ q) x := rfl

set_option synthInstance.maxHeartbeats 400000 in
/-- **Joint independence of a whole uniform labelled face layer over the labelled deeper face
field.** -/
theorem cosetFaceStar_diffIndepOn_deeper (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ)
    {S : Set (Finset ι)} (hS : ∀ L ∈ S, ∀ p : ι, p ∉ L → insert p L ∈ S)
    (faces : Finset (Finset ι)) (s : ℕ)
    (huniform : ∀ J ∈ faces, J.card = s)
    (hAtomic : ∀ J ∈ faces,
      DiffIndepOn ↥(differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S))
        (cosetFacePacket τ hτ A J))
    (hStarInj : ∀ (B : Finset ι) (q : ι), B.card < s → q ∉ B →
      ∀ (m n : ℤ) (y z : meroField (Set.univ : Set ℂ)),
        y ∈ (⋃ J ∈ faces.filter (fun J => insert q B ⊆ J),
          cosetFacePacketSlice τ hτ A J q) →
        z ∈ (⋃ J ∈ faces.filter (fun J => insert q B ⊆ J),
          cosetFacePacketSlice τ hτ A J q) →
        (meroTranslationPerm (τ q) ^ m) y = (meroTranslationPerm (τ q) ^ n) z → m = n)
    (hOffDA : ∀ (B : Finset ι) (q : ι), B.card < s → q ∉ B →
      ∀ t : Finset (meroField (Set.univ : Set ℂ)),
        (↑t : Set (meroField (Set.univ : Set ℂ))) ⊆
          (⋃ J ∈ (faces.filter (fun J => B ⊆ J)).filter (fun J => q ∉ J),
            cosetFacePacket τ hτ A J) →
        ∀ n : ℤ, ∀ z ∈ (⇑(meroTranslationPerm (τ q) ^ n)) ''
            (↑t : Set (meroField (Set.univ : Set ℂ))),
          DifferentialAlgebraicOver
            (differentialAdjoin ↥(differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S))
              (↑t : Set (meroField (Set.univ : Set ℂ)))) z) :
    DiffIndepOn ↥(differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S))
      (faceStar faces (cosetFacePacket τ hτ A) ∅) := by
  refine differentialRank_uniformFace_nestedStar_diffIndepOn_of_orbit_semilinear
    faces (cosetFacePacket τ hτ A)
    (fun q => cosetFacePacketSemilinearEquiv τ hτ A q (fun L hL hq => hS L hL q hq)) s huniform
    hAtomic
    (fun B q => ⋃ J ∈ faces.filter (fun J => insert q B ⊆ J),
      cosetFacePacketSlice τ hτ A J q)
    (fun B q _ _ => ?_) (fun B q hB hq => hStarInj B q hB hq)
    (fun B q hB hq t ht n z hz => hOffDA B q hB hq t ht n z (by
      simpa [Finset.coe_image] using! hz))
  exact cosetFaceStar_eq_orbitUnion τ hτ A faces B q

set_option synthInstance.maxHeartbeats 400000 in
/-- **Completing one labelled face layer.** -/
theorem cosetFaceLayer_diffIndepOn_deeper (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ)
    {S : Set (Finset ι)} (hS : ∀ L ∈ S, ∀ p : ι, p ∉ L → insert p L ∈ S)
    (faces : Finset (Finset ι)) (s : ℕ)
    (huniform : ∀ J ∈ faces, J.card = s)
    (dq du : Finset ι → ι)
    (hq : ∀ J ∈ faces, dq J ∉ J) (hu : ∀ J ∈ faces, du J ∉ J)
    (hqS : ∀ J ∈ faces, insert (dq J) J ∈ S) (huS : ∀ J ∈ faces, insert (du J) J ∈ S)
    (hJS : ∀ J ∈ faces, J ∉ S)
    (hv : ∀ J ∈ faces, LinearIndependent ℚ (facePacketPeriods τ (dq J) (du J)))
    (hfree : ∀ J ∈ faces, DifferentialIndependent
      ↥(differentialAdjoin ℂ
        (cosetFacePacketUnion τ hτ A (facePacketBaseFamily S J (dq J))))
      (cosetFacePalette τ hτ A (insert (dq J) J) (dq J)))
    (hinjD : ∀ (J : Finset ι) (hJ : J ∈ faces),
      Function.Injective (cosetFacePacketDisplacementSlice τ hτ A J (hq J hJ)))
    (hStarInj : ∀ (B : Finset ι) (q : ι), B.card < s → q ∉ B →
      ∀ (m n : ℤ) (y z : meroField (Set.univ : Set ℂ)),
        y ∈ (⋃ J ∈ faces.filter (fun J => insert q B ⊆ J),
          cosetFacePacketSlice τ hτ A J q) →
        z ∈ (⋃ J ∈ faces.filter (fun J => insert q B ⊆ J),
          cosetFacePacketSlice τ hτ A J q) →
        (meroTranslationPerm (τ q) ^ m) y = (meroTranslationPerm (τ q) ^ n) z → m = n)
    (hOffDA : ∀ (B : Finset ι) (q : ι), B.card < s → q ∉ B →
      ∀ t : Finset (meroField (Set.univ : Set ℂ)),
        (↑t : Set (meroField (Set.univ : Set ℂ))) ⊆
          (⋃ J ∈ (faces.filter (fun J => B ⊆ J)).filter (fun J => q ∉ J),
            cosetFacePacket τ hτ A J) →
        ∀ n : ℤ, ∀ z ∈ (⇑(meroTranslationPerm (τ q) ^ n)) ''
            (↑t : Set (meroField (Set.univ : Set ℂ))),
          DifferentialAlgebraicOver
            (differentialAdjoin ↥(differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S))
              (↑t : Set (meroField (Set.univ : Set ℂ)))) z) :
    DiffIndepOn ↥(differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S))
      (faceStar faces (cosetFacePacket τ hτ A) ∅) :=
  cosetFaceStar_diffIndepOn_deeper τ hτ A hS faces s huniform
    (fun J hJ => cosetFacePacket_differentialIndependent_of_free τ hτ A hS J (hq J hJ) (hu J hJ)
      (hqS J hJ) (huS J hJ) (hJS J hJ) (hv J hJ) (hfree J hJ) (hinjD J hJ))
    hStarInj hOffDA

/-! ## Off-star displacement -/

/-- A deleted direction preserves the labelled packet in every integer degree. -/
theorem cosetFacePacket_zsmul_translate_mem (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ)
    (J : Finset ι) {q : ι} (hq : q ∈ J) (n : ℤ) {y : meroField (Set.univ : Set ℂ)}
    (hy : y ∈ cosetFacePacket τ hτ A J) :
    addTranslationMeroEquiv ((n : ℂ) * τ q) y ∈ cosetFacePacket τ hτ A J := by
  obtain ⟨g, hg, rfl⟩ := hy
  refine ⟨(n : ℂ) * τ q + g, cosetFaceShiftSet_add_zsmul τ A J hq hg n, ?_⟩
  rw [addTranslationMeroEquiv_add]

set_option maxHeartbeats 800000 in
/-- **A surviving direction displaces the labelled packet inside the labelled deeper face
field.** -/
theorem cosetFacePacket_zsmul_displacement_mem (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ)
    {S : Set (Finset ι)} (J : Finset ι) {q : ι} (hq : q ∉ J) (hqS : insert q J ∈ S) (n : ℤ)
    {y : meroField (Set.univ : Set ℂ)} (hy : y ∈ cosetFacePacket τ hτ A J) :
    addTranslationMeroEquiv ((n : ℂ) * τ q) y - y ∈
      differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S) := by
  classical
  set w : meroField (Set.univ : Set ℂ) := addTranslationMeroEquiv (τ q) y - y with hwdef
  have hw : w ∈ cosetFacePacket τ hτ A (insert q J) :=
    cosetFacePacket_translate_sub_mem τ hτ A J hq hy
  have hmemK : ∀ m : ℤ, addTranslationMeroEquiv ((m : ℂ) * τ q) w ∈
      differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S) := by
    intro m
    refine subset_differentialAdjoin ℂ _ (Set.mem_iUnion₂.mpr ⟨insert q J, hqS, ?_⟩)
    exact cosetFacePacket_zsmul_translate_mem τ hτ A (insert q J)
      (Finset.mem_insert_self q J) m hw
  induction n using Int.induction_on with
  | zero =>
      have hz : addTranslationMeroEquiv (((0 : ℤ) : ℂ) * τ q) y - y = 0 := by
        rw [Int.cast_zero, zero_mul, addTranslationMeroEquiv_zero_apply, sub_self]
      rw [hz]
      exact (differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S)).zero_mem
  | succ k ih =>
      have hcast : ((((k : ℤ) + 1 : ℤ)) : ℂ) * τ q = (((k : ℤ) : ℂ) * τ q) + τ q := by
        push_cast; ring
      have hsplit : addTranslationMeroEquiv ((((k : ℤ) + 1 : ℤ) : ℂ) * τ q) y - y =
          (addTranslationMeroEquiv (((k : ℤ) : ℂ) * τ q) y - y) +
            addTranslationMeroEquiv (((k : ℤ) : ℂ) * τ q) w := by
        rw [hwdef, map_sub, hcast, ← addTranslationMeroEquiv_add]
        ring
      rw [hsplit]
      exact (differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S)).add_mem ih (hmemK (k : ℤ))
  | pred k ih =>
      have hcast : ((((-(k : ℤ)) - 1 : ℤ)) : ℂ) * τ q + τ q = ((-(k : ℤ) : ℤ) : ℂ) * τ q := by
        push_cast; ring
      have hsplit : addTranslationMeroEquiv (((-(k : ℤ) - 1 : ℤ) : ℂ) * τ q) y - y =
          (addTranslationMeroEquiv (((-(k : ℤ) : ℤ) : ℂ) * τ q) y - y) -
            addTranslationMeroEquiv (((-(k : ℤ) - 1 : ℤ) : ℂ) * τ q) w := by
        rw [hwdef, map_sub, addTranslationMeroEquiv_add, hcast]
        ring
      rw [hsplit]
      exact (differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S)).sub_mem ih
        (hmemK (-(k : ℤ) - 1))

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **The labelled off-star hypothesis at an arbitrary layer.** -/
theorem differentialAlgebraicOver_cosetOffStar_translate_deeper (τ : ι → ℂ)
    (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ)
    {S : Set (Finset ι)} (J : Finset ι) {q : ι} (hq : q ∉ J) (hqS : insert q J ∈ S) (n : ℤ)
    {t : Set (meroField (Set.univ : Set ℂ))} {y : meroField (Set.univ : Set ℂ)}
    (hy : y ∈ cosetFacePacket τ hτ A J) (hyt : y ∈ t) :
    DifferentialAlgebraicOver
      (differentialAdjoin ↥(differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S)) t)
      (addTranslationMeroEquiv ((n : ℂ) * τ q) y) := by
  classical
  set K : IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
    differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S) with hKdef
  set E : IntermediateField ↥K (meroField (Set.univ : Set ℂ)) :=
    differentialAdjoin ↥K t with hEdef
  have hdisp : addTranslationMeroEquiv ((n : ℂ) * τ q) y - y ∈ K :=
    cosetFacePacket_zsmul_displacement_mem τ hτ A J hq hqS n hy
  have h1 : addTranslationMeroEquiv ((n : ℂ) * τ q) y - y ∈ E :=
    E.algebraMap_mem ⟨_, hdisp⟩
  have h2 : y ∈ E := subset_differentialAdjoin ↥K t hyt
  have hsum : addTranslationMeroEquiv ((n : ℂ) * τ q) y =
      (addTranslationMeroEquiv ((n : ℂ) * τ q) y - y) + y := by ring
  have hmemE : addTranslationMeroEquiv ((n : ℂ) * τ q) y ∈ E := by
    rw [hsum]
    exact E.add_mem h1 h2
  have := HTGeometry.differentialAlgebraicOver_algebraMap
    (E := meroField (Set.univ : Set ℂ)) (⟨_, hmemE⟩ : ↥E)
  simpa using this

/-! ## The descending step -/

/-- **The descending step for labelled face families.** -/
theorem cosetFacePacketUnion_diffIndepOn_union (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ)
    (S T : Set (Finset ι))
    (hdeep : DiffIndepOn ℂ (cosetFacePacketUnion τ hτ A S))
    (hlayer : DiffIndepOn ↥(differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A S))
      (cosetFacePacketUnion τ hτ A T)) :
    DiffIndepOn ℂ (cosetFacePacketUnion τ hτ A (S ∪ T)) := by
  rw [cosetFacePacketUnion_union, Set.union_comm]
  exact diffIndepOn_union_of_base hdeep hlayer

end

end GaloisForLFunctions

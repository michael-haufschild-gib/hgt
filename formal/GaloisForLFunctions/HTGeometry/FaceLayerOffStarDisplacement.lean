import GaloisForLFunctions.HTGeometry.FaceTranslateInjective
import GaloisForLFunctions.HTGeometry.FacePacketLayerGluing

/-!
# Off-star displacements at an arbitrary face layer

A direction surviving on a face acts on its packet by the coface equation: one step moves a packet
element by an element of the next packet, which is one level deeper.  Iterating, every integer
translation moves a packet element inside the deeper face field, so the off-star hypothesis of the
star gluing engine holds at every layer whose cofaces are already present in the deeper family.

* `facePacket_zsmul_translate_mem` — a deleted direction preserves the packet in every degree;
* **`facePacket_zsmul_displacement_mem`** — a surviving direction displaces the packet inside the
  deeper face field;
* **`differentialAlgebraicOver_offStar_translate_deeper`** — the off-star hypothesis.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A deleted direction preserves the packet in every integer degree. -/
theorem facePacket_zsmul_translate_mem (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι)
    {q : ι} (hq : q ∈ J) (n : ℤ) {y : meroField (Set.univ : Set ℂ)}
    (hy : y ∈ multipleEllipticGammaFacePacket τ hτ J) :
    addTranslationMeroEquiv ((n : ℂ) * τ q) y ∈ multipleEllipticGammaFacePacket τ hτ J := by
  obtain ⟨g, hg, rfl⟩ := hy
  refine ⟨(n : ℂ) * τ q + g, faceShiftLattice_add_zsmul τ J hq hg n, ?_⟩
  rw [addTranslationMeroEquiv_add]

set_option maxHeartbeats 800000 in
/-- **A surviving direction displaces the packet inside the deeper face field.**  One step is the
coface equation; the general step telescopes, because the coface packet is stable under the same
direction. -/
theorem facePacket_zsmul_displacement_mem (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    {S : Set (Finset ι)} (J : Finset ι) {q : ι} (hq : q ∉ J) (hqS : insert q J ∈ S) (n : ℤ)
    {y : meroField (Set.univ : Set ℂ)} (hy : y ∈ multipleEllipticGammaFacePacket τ hτ J) :
    addTranslationMeroEquiv ((n : ℂ) * τ q) y - y ∈
      differentialAdjoin ℂ (facePacketUnion τ hτ S) := by
  classical
  set w : meroField (Set.univ : Set ℂ) := addTranslationMeroEquiv (τ q) y - y with hwdef
  have hw : w ∈ multipleEllipticGammaFacePacket τ hτ (insert q J) :=
    facePacket_translate_sub_mem τ hτ J hq hy
  have hmemK : ∀ m : ℤ, addTranslationMeroEquiv ((m : ℂ) * τ q) w ∈
      differentialAdjoin ℂ (facePacketUnion τ hτ S) := by
    intro m
    refine subset_differentialAdjoin ℂ _ (Set.mem_iUnion₂.mpr ⟨insert q J, hqS, ?_⟩)
    exact facePacket_zsmul_translate_mem τ hτ (insert q J) (Finset.mem_insert_self q J) m hw
  induction n using Int.induction_on with
  | zero =>
      have hz : addTranslationMeroEquiv (((0 : ℤ) : ℂ) * τ q) y - y = 0 := by
        rw [Int.cast_zero, zero_mul, addTranslationMeroEquiv_zero_apply, sub_self]
      rw [hz]
      exact (differentialAdjoin ℂ (facePacketUnion τ hτ S)).zero_mem
  | succ k ih =>
      have hcast : ((((k : ℤ) + 1 : ℤ)) : ℂ) * τ q = (((k : ℤ) : ℂ) * τ q) + τ q := by
        push_cast; ring
      have hsplit : addTranslationMeroEquiv ((((k : ℤ) + 1 : ℤ) : ℂ) * τ q) y - y =
          (addTranslationMeroEquiv (((k : ℤ) : ℂ) * τ q) y - y) +
            addTranslationMeroEquiv (((k : ℤ) : ℂ) * τ q) w := by
        rw [hwdef, map_sub, hcast, ← addTranslationMeroEquiv_add]
        ring
      rw [hsplit]
      exact (differentialAdjoin ℂ (facePacketUnion τ hτ S)).add_mem ih (hmemK (k : ℤ))
  | pred k ih =>
      have hcast : ((((-(k : ℤ)) - 1 : ℤ)) : ℂ) * τ q + τ q = ((-(k : ℤ) : ℤ) : ℂ) * τ q := by
        push_cast; ring
      have hsplit : addTranslationMeroEquiv (((-(k : ℤ) - 1 : ℤ) : ℂ) * τ q) y - y =
          (addTranslationMeroEquiv (((-(k : ℤ) : ℤ) : ℂ) * τ q) y - y) -
            addTranslationMeroEquiv (((-(k : ℤ) - 1 : ℤ) : ℂ) * τ q) w := by
        rw [hwdef, map_sub, addTranslationMeroEquiv_add, hcast]
        ring
      rw [hsplit]
      exact (differentialAdjoin ℂ (facePacketUnion τ hτ S)).sub_mem ih
        (hmemK (-(k : ℤ) - 1))

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **The off-star hypothesis at an arbitrary layer.**  A translate of a packet element in a
surviving direction differs from it by an element of the deeper face field, hence lies in — and so
is differentially algebraic over — any differential extension of that field containing the
element. -/
theorem differentialAlgebraicOver_offStar_translate_deeper (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    {S : Set (Finset ι)} (J : Finset ι) {q : ι} (hq : q ∉ J) (hqS : insert q J ∈ S) (n : ℤ)
    {t : Set (meroField (Set.univ : Set ℂ))} {y : meroField (Set.univ : Set ℂ)}
    (hy : y ∈ multipleEllipticGammaFacePacket τ hτ J) (hyt : y ∈ t) :
    DifferentialAlgebraicOver
      (differentialAdjoin ↥(differentialAdjoin ℂ (facePacketUnion τ hτ S)) t)
      (addTranslationMeroEquiv ((n : ℂ) * τ q) y) := by
  classical
  set K : IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
    differentialAdjoin ℂ (facePacketUnion τ hτ S) with hKdef
  set E : IntermediateField ↥K (meroField (Set.univ : Set ℂ)) :=
    differentialAdjoin ↥K t with hEdef
  have hdisp : addTranslationMeroEquiv ((n : ℂ) * τ q) y - y ∈ K :=
    facePacket_zsmul_displacement_mem τ hτ J hq hqS n hy
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

end

end GaloisForLFunctions

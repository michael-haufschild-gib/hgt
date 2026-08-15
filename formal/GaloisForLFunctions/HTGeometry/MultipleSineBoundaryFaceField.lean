import GaloisForLFunctions.HTGeometry.MultipleSineFaceNoTelescoping
import GaloisForLFunctions.HTGeometry.MultipleSineOrderOneSourceDA

/-!
# The deeper face field with the boundary faces included

A face retaining a single period carries the order-one source, which is a period cotangent up to a
rational function.  Its translation defect in the surviving direction is therefore rational, so the
packets of the boundary faces can be adjoined to the deeper face field without breaking translation
stability — and then stability needs no lower bound on the number of surviving periods, only that
the family of faces is closed under deleting one more direction.

This is what makes the descending induction run: the layer above the boundary must translate its
packets into a field containing the boundary packets.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

noncomputable local instance msbffDecidableEq :
    DecidableEq (meroField (Set.univ : Set ℂ)) := Classical.decEq _

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### The defect of a boundary packet is rational -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The translation defect of a boundary packet is rational.**  A face retaining one period has
the order-one source as coordinate, which is invariant under that period up to a rational
function. -/
theorem facePacket_boundary_translate_sub_mem (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    {L : Finset ι} (hL : (Lᶜ : Finset ι).card = 1) {q : ι} (hq : q ∉ L)
    {y : meroField (Set.univ : Set ℂ)} (hy : y ∈ facePacket ω hω L) :
    addTranslationMeroEquiv (ω q) y - y ∈ meromorphicRationalCoordinateField := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hL
  have hqa : q = a := by
    have hqc : q ∈ (Lᶜ : Finset ι) := Finset.mem_compl.mpr hq
    rw [ha] at hqc
    simpa using hqc
  subst hqa
  have hne : (Lᶜ : Finset ι).Nonempty := ⟨q, by rw [ha]; simp⟩
  have hsingle : ({q} : Finset ι).Nonempty := ⟨q, by simp⟩
  have hsrc : frameSourceMero ω hω (Lᶜ : Finset ι) hne
      = frameSourceMero ω hω ({q} : Finset ι) hsingle :=
    frameSourceMero_congr ω hω ha hne hsingle
  rw [facePacket_eq ω hω hne] at hy
  obtain ⟨α, rfl⟩ := hy
  have hw0 : ω q ≠ 0 := by
    intro h
    have := hω q
    rw [h] at this
    simp at this
  have hexact : frameSourceMero ω hω ({q} : Finset ι) hsingle
      = periodCotMero (ω q) + ratMero (orderOneCorrection (ω q)) :=
    frameSourceMero_singleton_eq ω hω q hsingle
  have hstep : addTranslationMeroEquiv (ω q)
        (frameSourceMero ω hω (Lᶜ : Finset ι) hne)
        - frameSourceMero ω hω (Lᶜ : Finset ι) hne
      = addTranslationMeroEquiv (ω q) (ratMero (orderOneCorrection (ω q)))
        - ratMero (orderOneCorrection (ω q)) := by
    rw [hsrc, hexact, map_add, addTranslationMeroEquiv_periodCotMero hw0]
    ring
  have hcomm : addTranslationMeroEquiv (ω q)
        (addTranslationMeroEquiv (faceShift ω L α)
          (frameSourceMero ω hω (Lᶜ : Finset ι) hne))
        - addTranslationMeroEquiv (faceShift ω L α)
          (frameSourceMero ω hω (Lᶜ : Finset ι) hne)
      = addTranslationMeroEquiv (faceShift ω L α)
          (addTranslationMeroEquiv (ω q) (frameSourceMero ω hω (Lᶜ : Finset ι) hne)
            - frameSourceMero ω hω (Lᶜ : Finset ι) hne) := by
    rw [map_sub, addTranslationMeroEquiv_add, addTranslationMeroEquiv_add]
    have harg : faceShift ω L α + ω q = ω q + faceShift ω L α := by ring
    rw [harg]
  rw [hcomm, hstep, map_sub]
  refine sub_mem ?_ ?_
  · exact addTranslationMeroAlgEquiv_mem_rationalCoordinateField _
      (addTranslationMeroAlgEquiv_mem_rationalCoordinateField _
        ((mem_meromorphicRationalCoordinateField_iff _).mpr
          ⟨orderOneCorrection (ω q), rfl⟩))
  · exact addTranslationMeroAlgEquiv_mem_rationalCoordinateField _
      ((mem_meromorphicRationalCoordinateField_iff _).mpr
        ⟨orderOneCorrection (ω q), rfl⟩)

set_option synthInstance.maxHeartbeats 1000000 in
/-- The backward defect of a boundary packet is rational as well. -/
theorem facePacket_boundary_neg_translate_sub_mem (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    {L : Finset ι} (hL : (Lᶜ : Finset ι).card = 1) {q : ι} (hq : q ∉ L)
    {y : meroField (Set.univ : Set ℂ)} (hy : y ∈ facePacket ω hω L) :
    addTranslationMeroEquiv (-(ω q)) y - y ∈ meromorphicRationalCoordinateField := by
  have hstep := facePacket_boundary_translate_sub_mem ω hω hL hq hy
  have hback : addTranslationMeroEquiv (-(ω q))
      (addTranslationMeroEquiv (ω q) y - y) = y - addTranslationMeroEquiv (-(ω q)) y := by
    rw [map_sub, addTranslationMeroEquiv_add, neg_add_cancel,
      addTranslationMeroEquiv_zero_apply]
  have hmem : addTranslationMeroEquiv (-(ω q)) (addTranslationMeroEquiv (ω q) y - y)
      ∈ meromorphicRationalCoordinateField :=
    addTranslationMeroAlgEquiv_mem_rationalCoordinateField (-(ω q)) hstep
  rw [hback] at hmem
  have hneg := neg_mem hmem
  have hid : -(y - addTranslationMeroEquiv (-(ω q)) y)
      = addTranslationMeroEquiv (-(ω q)) y - y := by ring
  rwa [hid] at hneg

/-! ### Stability of the deeper field without a bound on the surviving periods -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- **A structural translation moves a deeper generator inside the deeper field**, for any family of
faces closed under deleting one more direction. -/
theorem sineDeeperGenerators_translate_mem_of_closed (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    {S : Set (Finset ι)} (q : ι) (hS : ∀ L ∈ S, q ∉ L → insert q L ∈ S)
    {y : meroField (Set.univ : Set ℂ)} (hy : y ∈ sineDeeperGenerators ω hω S) :
    addTranslationMeroEquiv (ω q) y ∈ differentialAdjoin ℂ (sineDeeperGenerators ω hω S) := by
  classical
  rcases hy with hy | hy
  · obtain ⟨L, hL, hyL⟩ := Set.mem_iUnion₂.mp hy
    by_cases hq : q ∈ L
    · exact subset_differentialAdjoin ℂ _
        (Or.inl (Set.mem_iUnion₂.mpr ⟨L, hL, facePacket_translate_mem ω hω hq hyL⟩))
    · have hyK : y ∈ differentialAdjoin ℂ (sineDeeperGenerators ω hω S) :=
        subset_differentialAdjoin ℂ _ (Or.inl (Set.mem_iUnion₂.mpr ⟨L, hL, hyL⟩))
      rcases lt_or_ge (Lᶜ : Finset ι).card 2 with hcard | hcard
      · by_cases h0 : (Lᶜ : Finset ι).card = 0
        · have hempty : ¬ (Lᶜ : Finset ι).Nonempty := by
            rw [← Finset.card_pos, h0]
            omega
          rw [facePacket, dif_neg hempty] at hyL
          exact absurd hyL (Set.notMem_empty _)
        · have h1 : (Lᶜ : Finset ι).card = 1 := by omega
          have hrat := facePacket_boundary_translate_sub_mem ω hω h1 hq hyL
          have hval : addTranslationMeroEquiv (ω q) y
              = y + (addTranslationMeroEquiv (ω q) y - y) := by ring
          rw [hval]
          exact (differentialAdjoin ℂ (sineDeeperGenerators ω hω S)).add_mem hyK
            (subset_differentialAdjoin ℂ _ (Or.inr hrat))
      · obtain ⟨d, hd, r, hr, hstep⟩ :=
          facePacket_offFace_translate_sub_mem ω hω hq hcard hyL
        have hdK : d ∈ differentialAdjoin ℂ (sineDeeperGenerators ω hω S) :=
          subset_differentialAdjoin ℂ _
            (Or.inl (Set.mem_iUnion₂.mpr ⟨insert q L, hS L hL hq, hd⟩))
        have hrK : r ∈ differentialAdjoin ℂ (sineDeeperGenerators ω hω S) :=
          subset_differentialAdjoin ℂ _ (Or.inr hr)
        have hval : addTranslationMeroEquiv (ω q) y = y + r - d := by
          linear_combination hstep
        rw [hval]
        exact (differentialAdjoin ℂ (sineDeeperGenerators ω hω S)).sub_mem
          ((differentialAdjoin ℂ (sineDeeperGenerators ω hω S)).add_mem hyK hrK) hdK
  · exact subset_differentialAdjoin ℂ _
      (Or.inr (addTranslationMeroAlgEquiv_mem_rationalCoordinateField (ω q) hy))

set_option synthInstance.maxHeartbeats 1000000 in
/-- The inverse structural translation likewise. -/
theorem sineDeeperGenerators_neg_translate_mem_of_closed (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    {S : Set (Finset ι)} (q : ι) (hS : ∀ L ∈ S, q ∉ L → insert q L ∈ S)
    {y : meroField (Set.univ : Set ℂ)} (hy : y ∈ sineDeeperGenerators ω hω S) :
    addTranslationMeroEquiv (-(ω q)) y
      ∈ differentialAdjoin ℂ (sineDeeperGenerators ω hω S) := by
  classical
  rcases hy with hy | hy
  · obtain ⟨L, hL, hyL⟩ := Set.mem_iUnion₂.mp hy
    by_cases hq : q ∈ L
    · exact subset_differentialAdjoin ℂ _
        (Or.inl (Set.mem_iUnion₂.mpr ⟨L, hL, facePacket_neg_translate_mem ω hω hq hyL⟩))
    · have hyK : y ∈ differentialAdjoin ℂ (sineDeeperGenerators ω hω S) :=
        subset_differentialAdjoin ℂ _ (Or.inl (Set.mem_iUnion₂.mpr ⟨L, hL, hyL⟩))
      rcases lt_or_ge (Lᶜ : Finset ι).card 2 with hcard | hcard
      · by_cases h0 : (Lᶜ : Finset ι).card = 0
        · have hempty : ¬ (Lᶜ : Finset ι).Nonempty := by
            rw [← Finset.card_pos, h0]
            omega
          rw [facePacket, dif_neg hempty] at hyL
          exact absurd hyL (Set.notMem_empty _)
        · have h1 : (Lᶜ : Finset ι).card = 1 := by omega
          have hrat := facePacket_boundary_neg_translate_sub_mem ω hω h1 hq hyL
          have hval : addTranslationMeroEquiv (-(ω q)) y
              = y + (addTranslationMeroEquiv (-(ω q)) y - y) := by ring
          rw [hval]
          exact (differentialAdjoin ℂ (sineDeeperGenerators ω hω S)).add_mem hyK
            (subset_differentialAdjoin ℂ _ (Or.inr hrat))
      · obtain ⟨d, hd, r, hr, hstep⟩ :=
          facePacket_offFace_neg_translate_sub_mem ω hω hq hcard hyL
        have hdK : d ∈ differentialAdjoin ℂ (sineDeeperGenerators ω hω S) :=
          subset_differentialAdjoin ℂ _
            (Or.inl (Set.mem_iUnion₂.mpr ⟨insert q L, hS L hL hq, hd⟩))
        have hrK : r ∈ differentialAdjoin ℂ (sineDeeperGenerators ω hω S) :=
          subset_differentialAdjoin ℂ _ (Or.inr hr)
        have hval : addTranslationMeroEquiv (-(ω q)) y = y + d - r := by
          linear_combination hstep
        rw [hval]
        exact (differentialAdjoin ℂ (sineDeeperGenerators ω hω S)).sub_mem
          ((differentialAdjoin ℂ (sineDeeperGenerators ω hω S)).add_mem hyK hdK) hrK
  · exact subset_differentialAdjoin ℂ _
      (Or.inr (addTranslationMeroAlgEquiv_mem_rationalCoordinateField (-(ω q)) hy))

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The deeper face field is translation stable** for every family closed under deleting one more
direction. -/
theorem differentialAdjoin_sineDeeperGenerators_translate_stable_of_closed (ω : ι → ℂ)
    (hω : ∀ k, 0 < (ω k).im) {S : Set (Finset ι)} (q : ι)
    (hS : ∀ L ∈ S, q ∉ L → insert q L ∈ S)
    {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ differentialAdjoin ℂ (sineDeeperGenerators ω hω S)) :
    addTranslationMeroEquiv (ω q) x ∈ differentialAdjoin ℂ (sineDeeperGenerators ω hω S) :=
  differentialAdjoin_translate_stable_of_generators (ω q) _
    (fun _ hy => sineDeeperGenerators_translate_mem_of_closed ω hω q hS hy) hx

set_option synthInstance.maxHeartbeats 1000000 in
/-- And stable in the inverse direction. -/
theorem differentialAdjoin_sineDeeperGenerators_neg_translate_stable_of_closed (ω : ι → ℂ)
    (hω : ∀ k, 0 < (ω k).im) {S : Set (Finset ι)} (q : ι)
    (hS : ∀ L ∈ S, q ∉ L → insert q L ∈ S)
    {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ differentialAdjoin ℂ (sineDeeperGenerators ω hω S)) :
    addTranslationMeroEquiv (-(ω q)) x ∈ differentialAdjoin ℂ (sineDeeperGenerators ω hω S) :=
  differentialAdjoin_translate_stable_of_generators (-(ω q)) _
    (fun _ hy => sineDeeperGenerators_neg_translate_mem_of_closed ω hω q hS hy) hx

end

end GaloisForLFunctions.HTGeometry

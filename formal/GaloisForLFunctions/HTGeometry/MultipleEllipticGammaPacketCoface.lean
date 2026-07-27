import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaTelescope

/-!
# Coface behaviour of the face packets

The descending face-lifting step needs two structural facts about the packets: a deleted direction
moves a packet inside itself, and a *surviving* direction moves it by an element of the next
packet.  Both follow from the intrinsic coface equation together with commutativity of the
translations, and together they are the "stability of the deeper field" step of the argument.

* `faceShiftLattice_mono`;
* **`facePacket_translate_mem`** — a deleted direction preserves the packet;
* **`facePacket_translate_sub_mem`** — a surviving direction changes a packet element by an element
  of the next packet, which is the primitive system `(T_q − 1) Y = T^a F_{J ∪ {q}}` of the
  face-lifting lemma.
-/

open Filter Topology Set Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The external lattice grows with the deleted face. -/
theorem faceShiftLattice_mono (τ : ι → ℂ) {J J' : Finset ι} (hJ : J ⊆ J') :
    faceShiftLattice τ J ⊆ faceShiftLattice τ J' := by
  rintro g ⟨n, hn, rfl⟩
  exact ⟨n, fun i hi => hn i fun hiJ => hi (hJ hiJ), rfl⟩

/-- **A deleted direction preserves the packet.** -/
theorem facePacket_translate_mem (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) {q : ι}
    (hq : q ∈ J) {y : meroField (Set.univ : Set ℂ)}
    (hy : y ∈ multipleEllipticGammaFacePacket τ hτ J) :
    addTranslationMeroEquiv (τ q) y ∈ multipleEllipticGammaFacePacket τ hτ J := by
  obtain ⟨g, hg, rfl⟩ := hy
  refine ⟨τ q + g, ?_, ?_⟩
  · have h1 : ((1 : ℤ) : ℂ) * τ q + g ∈ faceShiftLattice τ J :=
      faceShiftLattice_add_zsmul τ J hq hg 1
    simpa using h1
  · rw [addTranslationMeroEquiv_add]

/-- **A surviving direction changes a packet element by an element of the next packet.**  This is
the primitive system of the descending face-lifting lemma. -/
theorem facePacket_translate_sub_mem (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) {q : ι}
    (hq : q ∉ J) {y : meroField (Set.univ : Set ℂ)}
    (hy : y ∈ multipleEllipticGammaFacePacket τ hτ J) :
    addTranslationMeroEquiv (τ q) y - y ∈
      multipleEllipticGammaFacePacket τ hτ (insert q J) := by
  obtain ⟨g, hg, rfl⟩ := hy
  refine ⟨g, faceShiftLattice_mono τ (Finset.subset_insert q J) hg, ?_⟩
  have hcomm : addTranslationMeroEquiv (τ q)
      (addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ J)) =
      addTranslationMeroEquiv g
        (addTranslationMeroEquiv (τ q) (multipleEllipticGammaLogDerivFaceMero τ hτ J)) := by
    rw [addTranslationMeroEquiv_add, addTranslationMeroEquiv_add, add_comm]
  rw [hcomm, ← map_sub,
    multipleEllipticGammaLogDerivFaceMero_addTranslation_sub τ hτ J q hq]

/-- The explicit primitive equation on a translated block: the displacement in a surviving
direction is the same translate of the next face coordinate. -/
theorem facePacket_coface (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) {q : ι}
    (hq : q ∉ J) (g : ℂ) :
    addTranslationMeroEquiv (τ q)
        (addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ J)) -
      addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ J) =
      addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ (insert q J)) := by
  have hcomm : addTranslationMeroEquiv (τ q)
      (addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ J)) =
      addTranslationMeroEquiv g
        (addTranslationMeroEquiv (τ q) (multipleEllipticGammaLogDerivFaceMero τ hτ J)) := by
    rw [addTranslationMeroEquiv_add, addTranslationMeroEquiv_add, add_comm]
  rw [hcomm, ← map_sub,
    multipleEllipticGammaLogDerivFaceMero_addTranslation_sub τ hτ J q hq]

end

end GaloisForLFunctions

import GaloisForLFunctions.HTGeometry.FacePacketFreeTelescoping

/-!
# The bottom face packet is a single point

The external lattice of a face is the integer span of the parameters it retains, so the empty face
retains nothing and its lattice is `{0}`.  Its packet is then the single untranslated face
log-derivative, and every labelling of that packet is injective — in particular the displacement
labelling whose injectivity is the freeness hypothesis of the telescoping layer.

* `faceShiftLattice_empty`, `multipleEllipticGammaFacePacket_empty`;
* **`facePacketDisplacementSlice_injective_empty`** — freeness at the base of the face induction.
-/

open Filter Topology Set Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

namespace HTGeometry

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The empty face retains no parameter, so its external lattice is trivial. -/
theorem faceShiftLattice_empty (τ : ι → ℂ) : faceShiftLattice τ (∅ : Finset ι) = {0} := by
  ext g
  constructor
  · rintro ⟨n, hn, rfl⟩
    have hzero : ∀ i, n i = 0 := fun i => hn i (Finset.notMem_empty i)
    simp [hzero]
  · rintro rfl
    exact ⟨0, fun i _ => rfl, by simp⟩

/-- The packet of the empty face is the untranslated face log-derivative. -/
theorem multipleEllipticGammaFacePacket_empty (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    multipleEllipticGammaFacePacket τ hτ (∅ : Finset ι) =
      {multipleEllipticGammaLogDerivFaceMero τ hτ (∅ : Finset ι)} := by
  rw [multipleEllipticGammaFacePacket, faceShiftLattice_empty, Set.image_singleton,
    addTranslationMeroEquiv_zero_apply]

theorem multipleEllipticGammaFacePacket_empty_subsingleton (τ : ι → ℂ)
    (hτ : ∀ i, 0 < (τ i).im) :
    (multipleEllipticGammaFacePacket τ hτ (∅ : Finset ι)).Subsingleton := by
  rw [multipleEllipticGammaFacePacket_empty]
  exact Set.subsingleton_singleton

/-- **Freeness at the base of the face induction.**  The displacement labelling of the empty face is
injective, because its packet has a single element. -/
theorem facePacketDisplacementSlice_injective_empty (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    {q : ι} (hq : q ∉ (∅ : Finset ι)) :
    Function.Injective (facePacketDisplacementSlice τ hτ (∅ : Finset ι) hq) := by
  intro y z _
  exact Subtype.ext (multipleEllipticGammaFacePacket_empty_subsingleton τ hτ y.2 z.2)

end HTGeometry

end

end GaloisForLFunctions

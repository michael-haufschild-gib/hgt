import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaFacePacket
import GaloisForLFunctions.HTGeometry.FreeShiftTransport

/-!
# The bilateral palette of a face packet

A face packet is the union of the full translation orbits of its zero-exponent slice, so in a fixed
deleted direction it is exactly the range of a bilateral palette `x (a, m) = σ_(m τ_q) a` indexed by
the slice and by `ℤ`.  On such a palette the genuine additive translation moves the slice index by
one, so the transported one-slice nonsummability obstruction applies verbatim.

* `facePalette` — the bilateral palette of a face packet in a deleted direction;
* **`facePalette_shift`** — the genuine translation moves the palette one slice;
* **`range_facePalette`** — its range is the packet;
* **`facePacket_oneSlice_ne_coboundary`** — hence, once the palette is differentially independent,
  no nonzero finite constant-coefficient one-slice jet form is a coboundary for the actual
  translation.
-/

open Filter Topology Set Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher MatroidGluing MatroidGluing.Meromorphic

noncomputable section

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The bilateral palette of the packet of the deleted face `J` in the deleted direction `q`. -/
def facePalette (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) (q : ι) :
    (↥(multipleEllipticGammaFacePacketSlice τ hτ J q) × ℤ) → meroField (Set.univ : Set ℂ) :=
  fun p => addTranslationMeroEquiv ((p.2 : ℂ) * τ q) (p.1 : meroField (Set.univ : Set ℂ))

/-- **The genuine translation moves the palette one slice.** -/
theorem facePalette_shift (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) (q : ι)
    (p : ↥(multipleEllipticGammaFacePacketSlice τ hτ J q) × ℤ) :
    (addTranslationMeroDifferentialAlgEquiv (τ q)).toAlgEquiv (facePalette τ hτ J q p) =
      facePalette τ hτ J q (p.1, p.2 + 1) := by
  have harg : τ q + (p.2 : ℂ) * τ q = ((p.2 + 1 : ℤ) : ℂ) * τ q := by push_cast; ring
  show addTranslationMeroEquiv (τ q)
      (addTranslationMeroEquiv ((p.2 : ℂ) * τ q) (p.1 : meroField (Set.univ : Set ℂ))) = _
  rw [addTranslationMeroEquiv_add, harg]
  rfl

/-- **The palette enumerates the packet.** -/
theorem range_facePalette (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) {q : ι}
    (hq : q ∈ J) :
    Set.range (facePalette τ hτ J q) = multipleEllipticGammaFacePacket τ hτ J := by
  rw [multipleEllipticGammaFacePacket_eq_orbitUnion τ hτ J hq]
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

/-- **One-slice nonsummability on a face packet, for the actual translation.**  If the bilateral
palette of the packet is differentially independent over the constants, no nonzero finite
constant-coefficient linear form in the jets of its zero slice is a coboundary for the genuine
translation by `τ q`. -/
theorem facePacket_oneSlice_ne_coboundary (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (J : Finset ι) (q : ι)
    (hindep : DifferentialIndependent ℂ (facePalette τ hτ J q))
    (c : (↥(multipleEllipticGammaFacePacketSlice τ hτ J q) × ℕ) →₀ ℂ) (hc : c ≠ 0)
    (g : differentialAdjoin ℂ (Set.range (facePalette τ hτ J q))) :
    (addTranslationMeroDifferentialAlgEquiv (τ q)).toAlgEquiv
        (g : meroField (Set.univ : Set ℂ)) - (g : meroField (Set.univ : Set ℂ)) ≠
      ((c.sum (fun j a =>
        algebraMap ℂ (differentialAdjoin ℂ (Set.range (facePalette τ hτ J q))) a *
          ⟨differentialJet j.2 (facePalette τ hτ J q (j.1, 0)),
            differentialJet_mem_differentialAdjoin ℂ
              (Set.mem_range_self (j.1, 0)) j.2⟩) :
        differentialAdjoin ℂ (Set.range (facePalette τ hτ J q))) :
        meroField (Set.univ : Set ℂ)) :=
  oneSlice_ne_coboundary_of_ambient_shift (facePalette τ hτ J q) hindep
    (addTranslationMeroDifferentialAlgEquiv (τ q))
    (fun p => facePalette_shift τ hτ J q p) c hc g

end

end GaloisForLFunctions

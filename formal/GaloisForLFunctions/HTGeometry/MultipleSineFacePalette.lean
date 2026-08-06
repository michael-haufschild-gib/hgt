import GaloisForLFunctions.HTGeometry.MultipleSineFacePrimitiveEquation

/-!
# The bilateral palette of a face packet

Along a direction of the face, a packet is the disjoint union of full translation orbits of its
slice.  Indexing an orbit by `ℤ` presents the packet as a bilateral palette

```text
(y, n) ↦ T^{n ω_q} y,   y in the slice,
```

on which the translation acts by the unit shift of the second coordinate.  This is the shape the
twisted one-slice obstruction consumes: a differentially independent bilateral family whose
ambient shift moves it by exactly one slice.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open GaloisForLFunctions.MatroidGluing GaloisForLFunctions.MatroidGluing.Meromorphic

noncomputable section

noncomputable local instance mfpDecidableEq :
    DecidableEq (meroField (Set.univ : Set ℂ)) := Classical.decEq _

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The bilateral palette of a face packet along a direction of the face. -/
def facePalette (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) (J : Finset ι) (q : ι) :
    (↥(facePacketSlice ω hω J q) × ℤ) → meroField (Set.univ : Set ℂ) :=
  fun p => addTranslationMeroEquiv ((p.2 : ℂ) * ω q) (p.1 : meroField (Set.univ : Set ℂ))

theorem facePalette_apply (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) (J : Finset ι) (q : ι)
    (p : ↥(facePacketSlice ω hω J q) × ℤ) :
    facePalette ω hω J q p
      = addTranslationMeroEquiv ((p.2 : ℂ) * ω q) (p.1 : meroField (Set.univ : Set ℂ)) := rfl

/-- **The translation moves the palette by exactly one slice.** -/
theorem facePalette_shift (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) (J : Finset ι) (q : ι)
    (p : ↥(facePacketSlice ω hω J q) × ℤ) :
    addTranslationMeroEquiv (ω q) (facePalette ω hω J q p)
      = facePalette ω hω J q (p.1, p.2 + 1) := by
  rw [facePalette_apply, facePalette_apply, addTranslationMeroEquiv_add]
  have harg : ω q + (p.2 : ℂ) * ω q = ((p.2 + 1 : ℤ) : ℂ) * ω q := by
    push_cast
    ring
  rw [harg]

/-- **The palette parametrizes the packet.** -/
theorem range_facePalette (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) {J : Finset ι} {q : ι}
    (hq : q ∈ J) :
    Set.range (facePalette ω hω J q) = facePacket ω hω J := by
  classical
  rw [facePacket_eq_orbitUnion ω hω hq]
  ext x
  constructor
  · rintro ⟨⟨y, n⟩, rfl⟩
    refine ⟨n, (y : meroField (Set.univ : Set ℂ)), y.2, ?_⟩
    rw [meroTranslationPerm_zpow_apply]
    rfl
  · rintro ⟨n, y, hy, rfl⟩
    refine ⟨(⟨y, hy⟩, n), ?_⟩
    rw [facePalette_apply, meroTranslationPerm_zpow_apply]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **The palette is injective.**  Distinct slice points or distinct exponents give distinct
elements of the packet. -/
theorem facePalette_injective {μ : ℂ} {rad : ι → ℝ} (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    {J : Finset ι} (hcard : (Jᶜ : Finset ι).card = 2) {q : ι} (hq : q ∈ J) :
    Function.Injective (facePalette (fun k => μ * (rad k : ℂ)) hω J q) := by
  classical
  set ω : ι → ℂ := fun k => μ * (rad k : ℂ) with hωdef
  have hfaces : ∀ L ∈ ({J} : Finset (Finset ι)), (Lᶜ : Finset ι).card = 2 := by
    intro L hL
    rw [Finset.mem_singleton.mp hL]
    exact hcard
  have hmem : ∀ y : ↥(facePacketSlice ω hω J q),
      (y : meroField (Set.univ : Set ℂ)) ∈
        ⋃ L ∈ ({J} : Finset (Finset ι)).filter (fun L => insert q (∅ : Finset ι) ⊆ L),
          facePacketSlice ω hω L q := by
    intro y
    refine Set.mem_iUnion₂.mpr ⟨J, ?_, y.2⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_singleton_self J, ?_⟩
    intro k hk
    rw [Finset.mem_insert] at hk
    rcases hk with rfl | hk
    · exact hq
    · exact absurd hk (Finset.notMem_empty k)
  rintro ⟨y, m⟩ ⟨z, n⟩ hyz
  rw [facePalette_apply, facePalette_apply] at hyz
  have hperm : (meroTranslationPerm (ω q) ^ m) (y : meroField (Set.univ : Set ℂ))
      = (meroTranslationPerm (ω q) ^ n) (z : meroField (Set.univ : Set ℂ)) := by
    rw [meroTranslationPerm_zpow_apply, meroTranslationPerm_zpow_apply]
    exact hyz
  have hmn : m = n :=
    facePacketSlice_zpow_injective hrad hind hω ({J} : Finset (Finset ι)) hfaces
      (∅ : Finset ι) q m n _ _ (hmem y) (hmem z) hperm
  subst hmn
  have hyzval : (y : meroField (Set.univ : Set ℂ)) = (z : meroField (Set.univ : Set ℂ)) :=
    (addTranslationMeroEquiv ((m : ℂ) * ω q)).injective hyz
  exact Prod.ext (Subtype.ext hyzval) rfl

end

end GaloisForLFunctions.HTGeometry

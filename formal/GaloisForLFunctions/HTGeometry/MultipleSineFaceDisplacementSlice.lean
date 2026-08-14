import GaloisForLFunctions.HTGeometry.MultipleSineFaceSeparation
import GaloisForLFunctions.HTGeometry.MultipleSineFaceDifferenceSystem

/-!
# The displacement labelling of a multiple-sine face packet

Faithful labelling makes the exponent of a packet element well defined, so the displacement of a
packet element in a surviving direction can be labelled by the corresponding element of the zero
slice of the next packet.  The primitive equation then reads

```text
(T_q - 1) y + d(y) ∈ ℂ(z),
```

with `d(y)` in the zero slice of the deeper packet, and the labelling `y ↦ d(y)` is injective.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### The exponent of a packet element -/

theorem exists_exponent_of_mem_facePacket (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    {J : Finset ι} (hne : (Jᶜ : Finset ι).Nonempty) {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ facePacket ω hω J) :
    ∃ α : {k // k ∈ J} → ℤ,
      addTranslationMeroEquiv (faceShift ω J α)
        (frameSourceMero ω hω (Jᶜ : Finset ι) hne) = x := by
  rw [facePacket_eq ω hω hne] at hx
  exact hx

/-- The exponent labelling a packet element. -/
def facePacketExponent (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) {J : Finset ι}
    (hne : (Jᶜ : Finset ι).Nonempty) (y : ↥(facePacket ω hω J)) : {k // k ∈ J} → ℤ :=
  (exists_exponent_of_mem_facePacket ω hω hne y.2).choose

theorem facePacketExponent_spec (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) {J : Finset ι}
    (hne : (Jᶜ : Finset ι).Nonempty) (y : ↥(facePacket ω hω J)) :
    addTranslationMeroEquiv (faceShift ω J (facePacketExponent ω hω hne y))
        (frameSourceMero ω hω (Jᶜ : Finset ι) hne)
      = (y : meroField (Set.univ : Set ℂ)) :=
  (exists_exponent_of_mem_facePacket ω hω hne y.2).choose_spec

theorem facePacketExponent_injective (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    {J : Finset ι} (hne : (Jᶜ : Finset ι).Nonempty) :
    Function.Injective (facePacketExponent ω hω hne (J := J)) := by
  intro y z hyz
  refine Subtype.ext ?_
  rw [← facePacketExponent_spec ω hω hne y, ← facePacketExponent_spec ω hω hne z, hyz]

/-! ### The displacement labelling -/

/-- The displacement labelling of a packet element by the zero slice of the deeper packet. -/
def sineDisplacementSlice (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) {J : Finset ι} {q : ι}
    (hq : q ∉ J) (hne : (Jᶜ : Finset ι).Nonempty)
    (hne' : ((insert q J)ᶜ : Finset ι).Nonempty) (y : ↥(facePacket ω hω J)) :
    ↥(facePacketSlice ω hω (insert q J) q) :=
  ⟨faceDisplacement ω hω J q hne' (facePacketExponent ω hω hne y),
    faceDisplacement_mem_slice ω hω hq hne' _⟩

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The displacement labelling is injective.** -/
theorem sineDisplacementSlice_injective {μ : ℂ} {rad : ι → ℝ} (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    {J : Finset ι} {q : ι} (hq : q ∉ J) (hJ' : 2 ≤ ((insert q J)ᶜ : Finset ι).card)
    (hne : (Jᶜ : Finset ι).Nonempty) (hne' : ((insert q J)ᶜ : Finset ι).Nonempty) :
    Function.Injective
      (sineDisplacementSlice (fun k => μ * (rad k : ℂ)) hω hq hne hne') := by
  intro y z hyz
  have hval : faceDisplacement (fun k => μ * (rad k : ℂ)) hω J q hne'
        (facePacketExponent (fun k => μ * (rad k : ℂ)) hω hne y)
      = faceDisplacement (fun k => μ * (rad k : ℂ)) hω J q hne'
        (facePacketExponent (fun k => μ * (rad k : ℂ)) hω hne z) :=
    congrArg (fun w : ↥(facePacketSlice (fun k => μ * (rad k : ℂ)) hω (insert q J) q) =>
      (w : meroField (Set.univ : Set ℂ))) hyz
  have hexp := faceDisplacement_injective (fun k => μ * (rad k : ℂ)) hω hq hne'
    (facePacket_label_injective hrad hind hω hJ' hne') hval
  exact facePacketExponent_injective _ hω hne hexp

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The primitive equation in labelled form.**  The translation defect of a packet element and its
displacement label differ by a rational function. -/
theorem sineDisplacementSlice_primitive (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    {J : Finset ι} {q : ι} (hq : q ∉ J) (h2 : 2 ≤ (Jᶜ : Finset ι).card)
    (hne : (Jᶜ : Finset ι).Nonempty) (hne' : ((insert q J)ᶜ : Finset ι).Nonempty)
    (y : ↥(facePacket ω hω J)) :
    addTranslationMeroEquiv (ω q) (y : meroField (Set.univ : Set ℂ))
          - (y : meroField (Set.univ : Set ℂ))
        + (sineDisplacementSlice ω hω hq hne hne' y : meroField (Set.univ : Set ℂ))
      ∈ meromorphicRationalCoordinateField := by
  have hprim := faceDisplacement_primitive ω hω hq h2 hne hne'
    (facePacketExponent ω hω hne y)
  rw [facePacketExponent_spec ω hω hne y] at hprim
  exact hprim

/-! ### The zero slice of the palette -/

@[simp] theorem facePalette_zero (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) (J : Finset ι) (q : ι)
    (a : ↥(facePacketSlice ω hω J q)) :
    facePalette ω hω J q (a, 0) = (a : meroField (Set.univ : Set ℂ)) := by
  rw [facePalette_apply]
  show addTranslationMeroEquiv (((0 : ℤ) : ℂ) * ω q) (a : meroField (Set.univ : Set ℂ)) = _
  rw [Int.cast_zero, zero_mul, addTranslationMeroEquiv_zero_apply]

end

end GaloisForLFunctions.HTGeometry

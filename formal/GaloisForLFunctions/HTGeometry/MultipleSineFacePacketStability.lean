import GaloisForLFunctions.HTGeometry.MultipleSineFaceDisplacement

/-!
# Face packets are stable in their own directions

A packet is indexed by integer exponents on its face, and translating by a period of the face
shifts one exponent by one.  So every direction of the face maps the packet onto itself, whereas a
direction outside it moves the packet off itself entirely.

Stability in the face's own directions is what makes the deeper layers a translation-stable
coefficient field in the layer descent.
-/

open Filter Set Topology Complex
open scoped Differential

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

/-- The unit exponent vector of one direction of a face. -/
def unitExp {J : Finset ι} {p : ι} (hp : p ∈ J) : {k // k ∈ J} → ℤ :=
  fun k => if k = (⟨p, hp⟩ : {k // k ∈ J}) then 1 else 0

omit [Fintype ι] in
theorem faceShift_unitExp (ω : ι → ℂ) {J : Finset ι} {p : ι} (hp : p ∈ J) :
    faceShift ω J (unitExp hp) = ω p :=
  faceShift_single ω J hp

set_option synthInstance.maxHeartbeats 1000000 in
/-- **A face direction maps the packet into itself.** -/
theorem facePacket_translate_mem (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) {J : Finset ι} {p : ι}
    (hp : p ∈ J) {x : meroField (Set.univ : Set ℂ)} (hx : x ∈ facePacket ω hω J) :
    addTranslationMeroEquiv (ω p) x ∈ facePacket ω hω J := by
  classical
  by_cases h : (Jᶜ : Finset ι).Nonempty
  · rw [facePacket_eq ω hω h] at hx ⊢
    obtain ⟨α, rfl⟩ := hx
    refine ⟨α + unitExp hp, ?_⟩
    show addTranslationMeroEquiv (faceShift ω J (α + unitExp hp))
        (frameSourceMero ω hω (Jᶜ : Finset ι) h)
      = addTranslationMeroEquiv (ω p)
        (addTranslationMeroEquiv (faceShift ω J α) (frameSourceMero ω hω (Jᶜ : Finset ι) h))
    rw [addTranslationMeroEquiv_add]
    have harg : faceShift ω J (α + unitExp hp) = ω p + faceShift ω J α := by
      rw [faceShift_add, faceShift_unitExp ω hp]
      ring
    exact congrArg (fun t => addTranslationMeroEquiv t
      (frameSourceMero ω hω (Jᶜ : Finset ι) h)) harg
  · rw [facePacket, dif_neg h] at hx
    exact absurd hx (Set.notMem_empty _)

set_option synthInstance.maxHeartbeats 1000000 in
/-- **A face direction maps the packet onto itself.** -/
theorem facePacket_translate_image (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) {J : Finset ι} {p : ι}
    (hp : p ∈ J) :
    (fun x => addTranslationMeroEquiv (ω p) x) '' facePacket ω hω J = facePacket ω hω J := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact facePacket_translate_mem ω hω hp hy
  · intro x hx
    by_cases h : (Jᶜ : Finset ι).Nonempty
    · rw [facePacket_eq ω hω h] at hx
      obtain ⟨α, rfl⟩ := hx
      refine ⟨addTranslationMeroEquiv (faceShift ω J (α - unitExp hp))
        (frameSourceMero ω hω (Jᶜ : Finset ι) h), ?_, ?_⟩
      · rw [facePacket_eq ω hω h]
        exact ⟨α - unitExp hp, rfl⟩
      · show addTranslationMeroEquiv (ω p)
            (addTranslationMeroEquiv (faceShift ω J (α - unitExp hp))
              (frameSourceMero ω hω (Jᶜ : Finset ι) h))
          = addTranslationMeroEquiv (faceShift ω J α) (frameSourceMero ω hω (Jᶜ : Finset ι) h)
        rw [addTranslationMeroEquiv_add]
        have harg : ω p + faceShift ω J (α - unitExp hp) = faceShift ω J α := by
          have hsub : faceShift ω J (α - unitExp hp) + faceShift ω J (unitExp hp)
              = faceShift ω J α := by
            rw [← faceShift_add]
            congr 1
            abel
          rw [faceShift_unitExp ω hp] at hsub
          rw [← hsub]
          ring
        exact congrArg (fun t => addTranslationMeroEquiv t
          (frameSourceMero ω hω (Jᶜ : Finset ι) h)) harg
    · rw [facePacket, dif_neg h] at hx
      exact absurd hx (Set.notMem_empty _)

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.MultipleSineFacePalette

/-!
# The displacement of a face block into the zero slice

The primitive equation sends an external translate of a face coordinate to the corresponding
translate of the deeper face coordinate.  That target has vanishing exponent in the new direction,
so it lies in the zero slice of the deeper packet's bilateral palette.

Displacement is therefore a labelling of the block of a face by the zero slice of the palette one
layer down — the shape the twisted one-slice obstruction needs on the right-hand side of a
coboundary equation.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open GaloisForLFunctions.MatroidGluing GaloisForLFunctions.MatroidGluing.Meromorphic

noncomputable section

noncomputable local instance mfdDecidableEq :
    DecidableEq (meroField (Set.univ : Set ℂ)) := Classical.decEq _

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### Extending an exponent vector by one direction -/

/-- The exponent vector of a face, read as an exponent vector of the face one layer down. -/
def extendExp (J : Finset ι) (q : ι) (α : {k // k ∈ J} → ℤ) :
    {k // k ∈ insert q J} → ℤ :=
  fun k => if h : (k : ι) ∈ J then α ⟨(k : ι), h⟩ else 0

omit [Fintype ι] in
theorem extendExp_zero (J : Finset ι) {q : ι} (hq : q ∉ J) (α : {k // k ∈ J} → ℤ)
    (k : {k // k ∈ insert q J}) (hk : (k : ι) = q) : extendExp J q α k = 0 := by
  rw [extendExp]
  simp only [hk]
  exact dif_neg hq

omit [Fintype ι] in
theorem extendExp_injective (J : Finset ι) (q : ι) :
    Function.Injective (extendExp J q (ι := ι)) := by
  intro α β h
  funext k
  have hk : ((⟨(k : ι), Finset.mem_insert_of_mem k.2⟩ : {k // k ∈ insert q J}) : ι) ∈ J := k.2
  have := congrFun h ⟨(k : ι), Finset.mem_insert_of_mem k.2⟩
  rw [extendExp, extendExp] at this
  simpa only [dif_pos hk] using this

omit [Fintype ι] in
theorem faceShift_extendExp (ω : ι → ℂ) {J : Finset ι} {q : ι} (hq : q ∉ J)
    (α : {k // k ∈ J} → ℤ) :
    faceShift ω (insert q J) (extendExp J q α) = faceShift ω J α :=
  faceShift_extend ω hq α

/-! ### The displacement map -/

/-- The displacement of an external block of a face: the translate of the deeper face coordinate by
the same external shift. -/
def faceDisplacement (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) (J : Finset ι) (q : ι)
    (hne' : ((insert q J)ᶜ : Finset ι).Nonempty) :
    ({k // k ∈ J} → ℤ) → meroField (Set.univ : Set ℂ) :=
  fun α => addTranslationMeroEquiv (faceShift ω J α)
    (frameSourceMero ω hω ((insert q J)ᶜ : Finset ι) hne')

/-- **The displacement lands in the zero slice** of the deeper packet's palette. -/
theorem faceDisplacement_mem_slice (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) {J : Finset ι} {q : ι}
    (hq : q ∉ J) (hne' : ((insert q J)ᶜ : Finset ι).Nonempty) (α : {k // k ∈ J} → ℤ) :
    faceDisplacement ω hω J q hne' α ∈ facePacketSlice ω hω (insert q J) q := by
  classical
  rw [facePacketSlice_eq ω hω q hne']
  refine ⟨extendExp J q α, fun k hk => extendExp_zero J hq α k hk, ?_⟩
  rw [faceDisplacement]
  exact congrArg (fun t => addTranslationMeroEquiv t
    (frameSourceMero ω hω ((insert q J)ᶜ : Finset ι) hne'))
    (faceShift_extendExp ω hq α).symm

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The primitive equation in displacement form.**  The translation defect of a block element is
its displacement, up to the rational base. -/
theorem faceDisplacement_primitive (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) {J : Finset ι} {q : ι}
    (hq : q ∉ J) (h2 : 2 ≤ (Jᶜ : Finset ι).card) (hne : (Jᶜ : Finset ι).Nonempty)
    (hne' : ((insert q J)ᶜ : Finset ι).Nonempty) (α : {k // k ∈ J} → ℤ) :
    addTranslationMeroEquiv (ω q)
          (addTranslationMeroEquiv (faceShift ω J α)
            (frameSourceMero ω hω (Jᶜ : Finset ι) hne))
        - addTranslationMeroEquiv (faceShift ω J α)
            (frameSourceMero ω hω (Jᶜ : Finset ι) hne)
        + faceDisplacement ω hω J q hne' α
      ∈ meromorphicRationalCoordinateField :=
  facePacket_primitive_equation ω hω hq h2 hne hne' α

/-- **The displacement labelling is injective** whenever the deeper packet family is. -/
theorem faceDisplacement_injective (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) {J : Finset ι} {q : ι}
    (hq : q ∉ J) (hne' : ((insert q J)ᶜ : Finset ι).Nonempty)
    (hinj : Function.Injective (fun β : {k // k ∈ insert q J} → ℤ =>
      addTranslationMeroEquiv (faceShift ω (insert q J) β)
        (frameSourceMero ω hω ((insert q J)ᶜ : Finset ι) hne'))) :
    Function.Injective (faceDisplacement ω hω J q hne') := by
  intro α β hαβ
  refine extendExp_injective J q (hinj ?_)
  show addTranslationMeroEquiv (faceShift ω (insert q J) (extendExp J q α))
      (frameSourceMero ω hω ((insert q J)ᶜ : Finset ι) hne')
    = addTranslationMeroEquiv (faceShift ω (insert q J) (extendExp J q β))
      (frameSourceMero ω hω ((insert q J)ᶜ : Finset ι) hne')
  rw [faceShift_extendExp ω hq α, faceShift_extendExp ω hq β]
  exact hαβ

end

end GaloisForLFunctions.HTGeometry

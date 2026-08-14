import GaloisForLFunctions.HTGeometry.MultipleSineFaceDifferenceSystem

/-!
# The translation block of a face, indexed by its exponents

The packet of a face is the range of its exponent parametrization, and the displacement labelling
of the multiple-sine hierarchy is written on exponents, not on packet elements.  Indexing the
translation block by exponents therefore keeps the block, its displacements and the zero-slice
labelling on one index type, which is what the telescoper argument needs.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

noncomputable local instance msbeDecidableEq :
    DecidableEq (meroField (Set.univ : Set ℂ)) := Classical.decEq _

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The translation block of a face, indexed by the exponents of its own directions. -/
def sineFaceBlockExp (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) (J : Finset ι)
    (hne : (Jᶜ : Finset ι).Nonempty) : ({k // k ∈ J} → ℤ) → meroField (Set.univ : Set ℂ) :=
  fun α => addTranslationMeroEquiv (faceShift ω J α) (frameSourceMero ω hω (Jᶜ : Finset ι) hne)

theorem sineFaceBlockExp_mem (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) {J : Finset ι}
    (hne : (Jᶜ : Finset ι).Nonempty) (α : {k // k ∈ J} → ℤ) :
    sineFaceBlockExp ω hω J hne α ∈ facePacket ω hω J := by
  rw [facePacket_eq ω hω hne]
  exact ⟨α, rfl⟩

@[simp] theorem range_sineFaceBlockExp (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) {J : Finset ι}
    (hne : (Jᶜ : Finset ι).Nonempty) :
    Set.range (sineFaceBlockExp ω hω J hne) = facePacket ω hω J :=
  (facePacket_eq ω hω hne).symm

set_option synthInstance.maxHeartbeats 1000000 in
/-- The displacement of an exponent-indexed block element in either structural direction lies in the
deeper face field. -/
theorem sineFaceBlockExp_period_displacement_mem (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    {S : Set (Finset ι)} {J : Finset ι} {q u : ι} (hqJ : q ∉ J) (huJ : u ∉ J)
    (h2 : 2 ≤ (Jᶜ : Finset ι).card) (hqS : insert q J ∈ S) (huS : insert u J ∈ S)
    (hne : (Jᶜ : Finset ι).Nonempty) (i : Fin 2) (α : {k // k ∈ J} → ℤ) :
    addTranslationMeroEquiv (sineFacePacketPeriods ω q u i) (sineFaceBlockExp ω hω J hne α)
        - sineFaceBlockExp ω hω J hne α
      ∈ differentialAdjoin ℂ (sineDeeperGenerators ω hω S) := by
  have hmem : ∀ p : ι, p ∉ J → insert p J ∈ S →
      addTranslationMeroEquiv (ω p) (sineFaceBlockExp ω hω J hne α)
          - sineFaceBlockExp ω hω J hne α
        ∈ differentialAdjoin ℂ (sineDeeperGenerators ω hω S) := by
    intro p hpJ hpS
    obtain ⟨d, hd, r, hr, hstep⟩ :=
      facePacket_offFace_translate_sub_mem ω hω hpJ h2 (sineFaceBlockExp_mem ω hω hne α)
    rw [hstep]
    refine (differentialAdjoin ℂ (sineDeeperGenerators ω hω S)).sub_mem ?_ ?_
    · exact subset_differentialAdjoin ℂ _ (Or.inr hr)
    · exact subset_differentialAdjoin ℂ _
        (Or.inl (Set.mem_iUnion₂.mpr ⟨insert p J, hpS, hd⟩))
  fin_cases i
  · exact hmem q hqJ hqS
  · exact hmem u huJ huS

/-- The displacements of the exponent-indexed block. -/
def sineFaceBlockExpDisplacement (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    {S : Set (Finset ι)} {J : Finset ι} {q u : ι} (hqJ : q ∉ J) (huJ : u ∉ J)
    (h2 : 2 ≤ (Jᶜ : Finset ι).card) (hqS : insert q J ∈ S) (huS : insert u J ∈ S)
    (hne : (Jᶜ : Finset ι).Nonempty) :
    Fin 2 → ({k // k ∈ J} → ℤ) → ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S)) :=
  fun i α => ⟨addTranslationMeroEquiv (sineFacePacketPeriods ω q u i)
      (sineFaceBlockExp ω hω J hne α) - sineFaceBlockExp ω hω J hne α,
    sineFaceBlockExp_period_displacement_mem ω hω hqJ huJ h2 hqS huS hne i α⟩

end

end GaloisForLFunctions.HTGeometry

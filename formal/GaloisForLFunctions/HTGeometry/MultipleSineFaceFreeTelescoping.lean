import GaloisForLFunctions.HTGeometry.MultipleSineFaceDisplacementSlice
import GaloisForLFunctions.HTGeometry.MultipleSineFaceNoTelescoping
import GaloisForLFunctions.HTGeometry.DifferentialAdjoinBaseAbsorb
import GaloisForLFunctions.HTGeometry.TwistedFreeShiftAffineTransport
import GaloisForLFunctions.HTGeometry.FacePacketFreeTelescoping

/-!
# Descending face-lifting for the multiple sine on a free deeper field

The deeper face field of the multiple sine is generated, over the field of the remaining deeper
packets and the rational coordinates, by the palette of the packet one layer up.  If that palette is
differentially independent over the complementary base, the deeper field is a free differential
extension, and the twisted one-slice obstruction — in its affine form, because the primitive
equation of the multiple sine holds only modulo `ℂ(z)` — excludes every simultaneous telescoper.
The Ostrowski criterion then makes the translation block of the face differentially independent over
the deeper field.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

noncomputable local instance msftDecidableEq :
    DecidableEq (meroField (Set.univ : Set ℂ)) := Classical.decEq _

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### The palette is independent over the complementary deeper base -/

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **Palette independence over the complementary deeper base.**  Splitting off the packet of the
face one layer up from the other deeper packets leaves it differentially independent over the field
they generate together with the rational coordinates. -/
theorem sineFacePalette_differentialIndependent_of_deeper {μ : ℂ} {rad : ι → ℝ}
    (hrad : ∀ k, 0 < rad k) (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    (S : Set (Finset ι)) (hSfaces : ∀ L ∈ S, 2 ≤ (Lᶜ : Finset ι).card)
    (hdeep : DiffIndepOn ↥meromorphicRationalCoordinateField
      (sineFacePacketUnion (fun k => μ * (rad k : ℂ)) hω S))
    (J : Finset ι) {q : ι} (hqS : insert q J ∈ S) :
    DifferentialIndependent
      ↥(differentialAdjoin ℂ (sineDeeperGenerators (fun k => μ * (rad k : ℂ)) hω
        (facePacketBaseFamily S J q)))
      (facePalette (fun k => μ * (rad k : ℂ)) hω (insert q J) q) := by
  classical
  set ω : ι → ℂ := fun k => μ * (rad k : ℂ) with hωdef
  set K : Finset ι := insert q J with hK
  set P : Set (meroField (Set.univ : Set ℂ)) := facePacket ω hω K with hP
  set B : Set (meroField (Set.univ : Set ℂ)) :=
    sineFacePacketUnion ω hω (facePacketBaseFamily S J q) with hB
  have hKcard : 2 ≤ (Kᶜ : Finset ι).card := hSfaces K hqS
  have hPB : Disjoint P B := by
    rw [Set.disjoint_left]
    intro y hyP hyB
    obtain ⟨L, hLbase, hyL⟩ := Set.mem_iUnion₂.mp hyB
    have hLS : L ∈ S := hLbase.1
    have hLK : L ≠ K := hLbase.2
    exact Set.disjoint_left.mp
      (facePacket_disjoint_of_two_le hrad hind hω hKcard (hSfaces L hLS) (Ne.symm hLK))
      hyP hyL
  have hsub : P ∪ B ⊆ sineFacePacketUnion ω hω S := by
    intro y hy
    rcases hy with hyP | hyB
    · exact Set.mem_iUnion₂.mpr ⟨K, hqS, hyP⟩
    · obtain ⟨L, hL, hyL⟩ := Set.mem_iUnion₂.mp hyB
      exact Set.mem_iUnion₂.mpr ⟨L, hL.1, hyL⟩
  have hrel : DiffIndepOn ↥(differentialAdjoin ↥meromorphicRationalCoordinateField B) P :=
    ((diffIndepOn_union_iff hPB).mp (hdeep.subset hsub)).2
  have habs := differentialIndependent_differentialAdjoin_base
    (K₀ := meromorphicRationalCoordinateField)
    meromorphicRationalCoordinateField_derivationClosed B hrel
  have hcarrier : ((differentialAdjoin ℂ
        ((meromorphicRationalCoordinateField : Set (meroField (Set.univ : Set ℂ))) ∪ B) :
      IntermediateField ℂ (meroField (Set.univ : Set ℂ))) :
      Set (meroField (Set.univ : Set ℂ)))
      = ((differentialAdjoin ℂ (sineDeeperGenerators ω hω (facePacketBaseFamily S J q)) :
        IntermediateField ℂ (meroField (Set.univ : Set ℂ))) :
        Set (meroField (Set.univ : Set ℂ))) :=
    congrArg (fun T => ((differentialAdjoin ℂ T :
        IntermediateField ℂ (meroField (Set.univ : Set ℂ))) :
      Set (meroField (Set.univ : Set ℂ)))) (Set.union_comm _ _)
  have hset : DiffIndepOn
      ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω (facePacketBaseFamily S J q))) P :=
    differentialIndependent_of_coe_eq hcarrier habs
  have hmemP : ∀ p : ↥(facePacketSlice ω hω K q) × ℤ, facePalette ω hω K q p ∈ P := by
    intro p
    rw [hP, ← range_facePalette ω hω (J := K) (q := q) (by rw [hK]; exact Finset.mem_insert_self q J)]
    exact Set.mem_range_self p
  have he : Function.Injective
      (fun p : ↥(facePacketSlice ω hω K q) × ℤ => (⟨facePalette ω hω K q p, hmemP p⟩ : ↥P)) := by
    intro x y hxy
    exact facePalette_injective_of_two_le hrad hind hω hKcard
      (by rw [hK]; exact Finset.mem_insert_self q J)
      (congrArg (fun z : ↥P => (z : meroField (Set.univ : Set ℂ))) hxy)
  exact (show DifferentialIndependent
    ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω (facePacketBaseFamily S J q)))
    (Subtype.val : ↥P → meroField (Set.univ : Set ℂ)) from hset).comp _ he

/-! ### The deeper field is free over the complementary base -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The deeper face field is generated by the target palette over the complementary base.** -/
theorem sineDeeperGenerators_le_free_adjoin (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    (S : Set (Finset ι)) (J : Finset ι) (q : ι)
    {z : meroField (Set.univ : Set ℂ)}
    (hz : z ∈ differentialAdjoin ℂ (sineDeeperGenerators ω hω S)) :
    z ∈ differentialAdjoin
      ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω (facePacketBaseFamily S J q)))
      (Set.range (facePalette ω hω (insert q J) q)) := by
  classical
  set F₀ : IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
    differentialAdjoin ℂ (sineDeeperGenerators ω hω (facePacketBaseFamily S J q)) with hF₀
  set E : IntermediateField ↥F₀ (meroField (Set.univ : Set ℂ)) :=
    differentialAdjoin ↥F₀ (Set.range (facePalette ω hω (insert q J) q)) with hE
  haveI : DifferentialAlgebra ↥F₀ (meroField (Set.univ : Set ℂ)) :=
    ⟨fun x => derivationClosedDifferential_apply _
      (derivationClosed_differentialAdjoin ℂ
        (sineDeeperGenerators ω hω (facePacketBaseFamily S J q))) x⟩
  have hEclosed : DerivationClosed E := derivationClosed_differentialAdjoin _ _
  have hgens : ∀ y ∈ sineDeeperGenerators ω hω S, y ∈ E := by
    intro y hy
    rcases hy with hy | hy
    · obtain ⟨L, hL, hyL⟩ := Set.mem_iUnion₂.mp hy
      by_cases hLt : L = insert q J
      · subst hLt
        refine subset_differentialAdjoin _ _ ?_
        rw [range_facePalette ω hω (Finset.mem_insert_self q L)]
        exact hyL
      · have hmem : y ∈ sineDeeperGenerators ω hω (facePacketBaseFamily S J q) :=
          Or.inl (Set.mem_iUnion₂.mpr ⟨L, ⟨hL, hLt⟩, hyL⟩)
        exact E.algebraMap_mem ⟨y, subset_differentialAdjoin ℂ _ hmem⟩
    · have hmem : y ∈ sineDeeperGenerators ω hω (facePacketBaseFamily S J q) := Or.inr hy
      exact E.algebraMap_mem ⟨y, subset_differentialAdjoin ℂ _ hmem⟩
  let p : ∀ y : meroField (Set.univ : Set ℂ),
      y ∈ differentialAdjoin ℂ (sineDeeperGenerators ω hω S) → Prop := fun y _ => y ∈ E
  change p z hz
  refine IntermediateField.adjoin_induction ℂ (p := p) ?_ ?_ ?_ ?_ ?_ hz
  · rintro y ⟨y₀, hy₀, n, rfl⟩
    exact hEclosed.differentialJet_mem (hgens y₀ hy₀) n
  · intro c
    exact E.algebraMap_mem (algebraMap ℂ ↥F₀ c)
  · intro y w _ _ hy hw
    exact E.add_mem hy hw
  · intro y _ hy
    exact E.inv_mem hy
  · intro y w _ _ hy hw
    exact E.mul_mem hy hw

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.MultipleSineFaceDisplacementSlice
import GaloisForLFunctions.HTGeometry.MultipleSineFaceDifferenceSystemClosed
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

noncomputable local instance msfrtDecidableEq :
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
/-- **From packet independence to palette independence.**  The palette parametrizes the packet
faithfully, so independence of the packet as a set gives independence of the palette family. -/
theorem facePalette_differentialIndependent_of_diffIndepOn
    {F : Type*} [Field F] [Algebra F (meroField (Set.univ : Set ℂ))]
    {μ : ℂ} {rad : ι → ℝ} (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    {K : Finset ι} (hK : 2 ≤ (Kᶜ : Finset ι).card) {q : ι} (hq : q ∈ K)
    (hset : DiffIndepOn F (facePacket (fun k => μ * (rad k : ℂ)) hω K)) :
    DifferentialIndependent F (facePalette (fun k => μ * (rad k : ℂ)) hω K q) := by
  have hmemP : ∀ p : ↥(facePacketSlice (fun k => μ * (rad k : ℂ)) hω K q) × ℤ,
      facePalette (fun k => μ * (rad k : ℂ)) hω K q p
        ∈ facePacket (fun k => μ * (rad k : ℂ)) hω K := by
    intro p
    rw [← range_facePalette (fun k => μ * (rad k : ℂ)) hω hq]
    exact Set.mem_range_self p
  have he : Function.Injective
      (fun p : ↥(facePacketSlice (fun k => μ * (rad k : ℂ)) hω K q) × ℤ =>
        (⟨facePalette (fun k => μ * (rad k : ℂ)) hω K q p, hmemP p⟩ :
          ↥(facePacket (fun k => μ * (rad k : ℂ)) hω K))) := by
    intro x y hxy
    exact facePalette_injective_of_two_le hrad hind hω hK hq
      (congrArg (fun z : ↥(facePacket (fun k => μ * (rad k : ℂ)) hω K) =>
        (z : meroField (Set.univ : Set ℂ))) hxy)
  exact GaloisForLFunctions.DifferentialIndependent.comp
    (show DifferentialIndependent F
      (Subtype.val : ↥(facePacket (fun k => μ * (rad k : ℂ)) hω K)
        → meroField (Set.univ : Set ℂ)) from hset)
    (fun p : ↥(facePacketSlice (fun k => μ * (rad k : ℂ)) hω K q) × ℤ =>
      (⟨facePalette (fun k => μ * (rad k : ℂ)) hω K q p, hmemP p⟩ :
        ↥(facePacket (fun k => μ * (rad k : ℂ)) hω K))) he


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
  have hKcard : 2 ≤ ((insert q J)ᶜ : Finset ι).card := hSfaces (insert q J) hqS
  have hPB : Disjoint (facePacket (fun k => μ * (rad k : ℂ)) hω (insert q J))
      (sineFacePacketUnion (fun k => μ * (rad k : ℂ)) hω (facePacketBaseFamily S J q)) := by
    rw [Set.disjoint_left]
    intro y hyP hyB
    obtain ⟨L, hLbase, hyL⟩ := Set.mem_iUnion₂.mp hyB
    exact Set.disjoint_left.mp
      (facePacket_disjoint_of_two_le hrad hind hω hKcard (hSfaces L hLbase.1)
        (Ne.symm hLbase.2)) hyP hyL
  have hsub : facePacket (fun k => μ * (rad k : ℂ)) hω (insert q J)
        ∪ sineFacePacketUnion (fun k => μ * (rad k : ℂ)) hω (facePacketBaseFamily S J q)
      ⊆ sineFacePacketUnion (fun k => μ * (rad k : ℂ)) hω S := by
    intro y hy
    rcases hy with hyP | hyB
    · exact Set.mem_iUnion₂.mpr ⟨insert q J, hqS, hyP⟩
    · obtain ⟨L, hL, hyL⟩ := Set.mem_iUnion₂.mp hyB
      exact Set.mem_iUnion₂.mpr ⟨L, hL.1, hyL⟩
  have hrel : DiffIndepOn ↥(differentialAdjoin ↥meromorphicRationalCoordinateField
        (sineFacePacketUnion (fun k => μ * (rad k : ℂ)) hω (facePacketBaseFamily S J q)))
      (facePacket (fun k => μ * (rad k : ℂ)) hω (insert q J)) :=
    ((diffIndepOn_union_iff hPB).mp (hdeep.subset hsub)).2
  have habs : DifferentialIndependent
      ↥(differentialAdjoin ℂ
        ((meromorphicRationalCoordinateField : Set (meroField (Set.univ : Set ℂ)))
          ∪ sineFacePacketUnion (fun k => μ * (rad k : ℂ)) hω (facePacketBaseFamily S J q)))
      (Subtype.val : ↥(facePacket (fun k => μ * (rad k : ℂ)) hω (insert q J))
        → meroField (Set.univ : Set ℂ)) :=
    differentialIndependent_differentialAdjoin_base
      (K₀ := meromorphicRationalCoordinateField)
      meromorphicRationalCoordinateField_derivationClosed _ hrel
  have hcarrier : ((differentialAdjoin ℂ
        ((meromorphicRationalCoordinateField : Set (meroField (Set.univ : Set ℂ)))
          ∪ sineFacePacketUnion (fun k => μ * (rad k : ℂ)) hω (facePacketBaseFamily S J q)) :
      IntermediateField ℂ (meroField (Set.univ : Set ℂ))) :
      Set (meroField (Set.univ : Set ℂ)))
      = ((differentialAdjoin ℂ (sineDeeperGenerators (fun k => μ * (rad k : ℂ)) hω
          (facePacketBaseFamily S J q)) :
        IntermediateField ℂ (meroField (Set.univ : Set ℂ))) :
        Set (meroField (Set.univ : Set ℂ))) :=
    congrArg (fun T => ((differentialAdjoin ℂ T :
        IntermediateField ℂ (meroField (Set.univ : Set ℂ))) :
      Set (meroField (Set.univ : Set ℂ)))) (Set.union_comm _ _)
  have hset : DiffIndepOn
      ↥(differentialAdjoin ℂ (sineDeeperGenerators (fun k => μ * (rad k : ℂ)) hω
        (facePacketBaseFamily S J q)))
      (facePacket (fun k => μ * (rad k : ℂ)) hω (insert q J)) :=
    differentialIndependent_of_coe_eq hcarrier habs
  exact facePalette_differentialIndependent_of_diffIndepOn hrad hind hω hKcard
    (Finset.mem_insert_self q J) hset

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
        rw [range_facePalette ω hω (Finset.mem_insert_self q J)]
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


/-! ### Excluding the telescoper -/

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **No simultaneous telescoper on a free deeper face field.**  If the packet one layer up is
differentially independent over the field generated by the other deeper packets and the rational
coordinates, and the displacement labelling is injective, then no nonzero finite constant-coefficient
jet form of the displacements is a coboundary in the surviving direction. -/
theorem sineFacePacket_no_telescoping_of_free (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    {S : Set (Finset ι)} (hS : ∀ L ∈ S, ∀ p : ι, p ∉ L → insert p L ∈ S)
    (J : Finset ι) {q u : ι} (hqJ : q ∉ J) (huJ : u ∉ J)
    (hqS : insert q J ∈ S) (huS : insert u J ∈ S) (hJS : J ∉ S)
    (h2 : 2 ≤ (Jᶜ : Finset ι).card) (hne : (Jᶜ : Finset ι).Nonempty)
    (hne' : ((insert q J)ᶜ : Finset ι).Nonempty)
    (hindep : DifferentialIndependent
      ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω (facePacketBaseFamily S J q)))
      (facePalette ω hω (insert q J) q))
    (hinjD : Function.Injective (sineDisplacementSlice ω hω hqJ hne hne'))
    (c : (↥(facePacket ω hω J) × ℕ) →₀ ℂ) (hc : c ≠ 0)
    (k : ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S))) :
    (sineFaceDifferenceSystemClosed ω hω hS q u).defect 0 k ≠
      Finsupp.linearCombination ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S))
        (fun p ↦ differentialJet p.2
          (sineFacePacketDisplacement ω hω J hqJ huJ h2 hqS huS 0 p.1))
        (Finsupp.mapRange
          (algebraMap ℂ ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S)))
          (map_zero (algebraMap ℂ
            ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S)))) c) := by
  classical
  intro hEq
  have hS₀ : ∀ L ∈ facePacketBaseFamily S J q, q ∉ L →
      insert q L ∈ facePacketBaseFamily S J q :=
    facePacketBaseFamily_closed hS hqJ hJS
  set F₀ : IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
    differentialAdjoin ℂ (sineDeeperGenerators ω hω (facePacketBaseFamily S J q)) with hF₀
  set P : (↥(facePacketSlice ω hω (insert q J) q) × ℤ) → meroField (Set.univ : Set ℂ) :=
    facePalette ω hω (insert q J) q with hPdef
  let φ : ↥F₀ ≃+* ↥F₀ :=
    meroTranslationRestrict F₀ (ω q)
      (fun x hx =>
        differentialAdjoin_sineDeeperGenerators_translate_stable_of_closed ω hω q hS₀ hx)
      (fun x hx =>
        differentialAdjoin_sineDeeperGenerators_neg_translate_stable_of_closed ω hω q hS₀ hx)
  let e : ↥(facePacket ω hω J) × ℕ → ↥(facePacketSlice ω hω (insert q J) q) × ℕ :=
    fun p => (sineDisplacementSlice ω hω hqJ hne hne' p.1, p.2)
  have he : Function.Injective e := by
    rintro ⟨a, m⟩ ⟨b, n⟩ h
    have h1 : sineDisplacementSlice ω hω hqJ hne hne' a
        = sineDisplacementSlice ω hω hqJ hne hne' b := congrArg Prod.fst h
    have h2' : m = n := congrArg Prod.snd h
    rw [hinjD h1, h2']
  set c' : (↥(facePacketSlice ω hω (insert q J) q) × ℕ) →₀ ↥F₀ :=
    Finsupp.mapRange (fun z : ℂ => -(algebraMap ℂ ↥F₀ z)) (by simp)
      (Finsupp.mapDomain e c) with hc'def
  have hc' : c' ≠ 0 := by
    rw [hc'def]
    intro hzero
    have hneginj : Function.Injective (fun z : ℂ => -(algebraMap ℂ ↥F₀ z)) := by
      intro x y hxy
      exact (algebraMap ℂ ↥F₀).injective (neg_injective hxy)
    have h1 : Finsupp.mapDomain e c = 0 :=
      Finsupp.mapRange_injective (fun z : ℂ => -(algebraMap ℂ ↥F₀ z)) (by simp) hneginj
        (by simpa using hzero)
    exact hc (Finsupp.mapDomain_injective he (by simpa using h1))
  set rr : ↥(facePacket ω hω J) → meroField (Set.univ : Set ℂ) := fun y =>
    addTranslationMeroEquiv (ω q) (y : meroField (Set.univ : Set ℂ))
      - (y : meroField (Set.univ : Set ℂ))
      + (sineDisplacementSlice ω hω hqJ hne hne' y : meroField (Set.univ : Set ℂ)) with hrrdef
  have hrrmem : ∀ y : ↥(facePacket ω hω J), rr y ∈ F₀ := fun y =>
    subset_differentialAdjoin ℂ _
      (Or.inr (sineDisplacementSlice_primitive ω hω hqJ h2 hne hne' y))
  have hjetmem : ∀ (y : ↥(facePacket ω hω J)) (n : ℕ), differentialJet n (rr y) ∈ F₀ :=
    fun y n => (derivationClosed_differentialAdjoin ℂ
      (sineDeeperGenerators ω hω (facePacketBaseFamily S J q))).differentialJet_mem
      (hrrmem y) n
  set b : ↥F₀ := c.sum (fun p a =>
    algebraMap ℂ ↥F₀ a * ⟨differentialJet p.2 (rr p.1), hjetmem p.1 p.2⟩) with hbdef
  have hkmem : (k : meroField (Set.univ : Set ℂ)) ∈ differentialAdjoin ↥F₀ (Set.range P) :=
    sineDeeperGenerators_le_free_adjoin ω hω S J q k.2
  refine affineSlice_ne_coboundary_of_twisted_ambient_shift P hindep
    (addTranslationMeroEquiv (ω q)) φ
    (fun y => addTranslationMeroEquiv_deriv (ω q) y)
    (fun bb => rfl)
    (fun p => facePalette_shift ω hω (insert q J) q p)
    b c' hc' ⟨(k : meroField (Set.univ : Set ℂ)), hkmem⟩ ?_
  -- both sides become the same finite sum in the ambient field
  have hbcoe : (b : meroField (Set.univ : Set ℂ))
      = c.sum (fun p a => algebraMap ℂ (meroField (Set.univ : Set ℂ)) a *
        differentialJet p.2 (rr p.1)) := by
    rw [hbdef]
    simp only [Finsupp.sum]
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [MulMemClass.coe_mul]
    congr 1
  have hRHS : ((c'.sum (fun j a =>
        algebraMap ↥F₀ ↥(differentialAdjoin ↥F₀ (Set.range P)) a *
          ⟨differentialJet j.2 (P (j.1, 0)),
            differentialJet_mem_differentialAdjoin ↥F₀
              (Set.mem_range_self (j.1, 0)) j.2⟩) :
        ↥(differentialAdjoin ↥F₀ (Set.range P))) : meroField (Set.univ : Set ℂ)) =
      c.sum (fun p a => -(algebraMap ℂ (meroField (Set.univ : Set ℂ)) a) *
        differentialJet p.2
          (sineDisplacementSlice ω hω hqJ hne hne' p.1 :
            meroField (Set.univ : Set ℂ))) := by
    rw [hc'def, Finsupp.sum_mapRange_index (by intro a; simp),
      Finsupp.sum_mapDomain_index_inj he]
    simp only [Finsupp.sum]
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hPD : P (sineDisplacementSlice ω hω hqJ hne hne' p.1, 0)
        = (sineDisplacementSlice ω hω hqJ hne hne' p.1 : meroField (Set.univ : Set ℂ)) := by
      rw [hPdef]
      exact facePalette_zero ω hω (insert q J) q _
    rw [MulMemClass.coe_mul]
    show ((algebraMap ↥F₀ ↥(differentialAdjoin ↥F₀ (Set.range P))
        (-(algebraMap ℂ ↥F₀ (c p))) : ↥(differentialAdjoin ↥F₀ (Set.range P))) :
        meroField (Set.univ : Set ℂ)) *
        differentialJet p.2 (P ((e p).1, 0)) = _
    have hcoef : ((algebraMap ↥F₀ ↥(differentialAdjoin ↥F₀ (Set.range P))
          (-(algebraMap ℂ ↥F₀ (c p))) : ↥(differentialAdjoin ↥F₀ (Set.range P))) :
          meroField (Set.univ : Set ℂ))
        = -(algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c p)) := by
      rw [map_neg]
      show -((algebraMap ↥F₀ ↥(differentialAdjoin ↥F₀ (Set.range P))
        (algebraMap ℂ ↥F₀ (c p)) : ↥(differentialAdjoin ↥F₀ (Set.range P))) :
        meroField (Set.univ : Set ℂ)) = _
      congr 1
    rw [hcoef]
    congr 2
  have hLHS : ((Finsupp.linearCombination
        ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S))
        (fun p ↦ differentialJet p.2
          (sineFacePacketDisplacement ω hω J hqJ huJ h2 hqS huS 0 p.1))
        (Finsupp.mapRange
          (algebraMap ℂ ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S)))
          (map_zero (algebraMap ℂ
            ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S)))) c) :
        ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S))) :
        meroField (Set.univ : Set ℂ)) =
      c.sum (fun p a => algebraMap ℂ (meroField (Set.univ : Set ℂ)) a *
        differentialJet p.2
          (addTranslationMeroEquiv (ω q) (p.1 : meroField (Set.univ : Set ℂ))
            - (p.1 : meroField (Set.univ : Set ℂ)))) := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by intro a; simp)]
    simp only [Finsupp.sum]
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hcoefK : ((algebraMap ℂ ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S)) (c p) :
        ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S))) :
        meroField (Set.univ : Set ℂ))
        = algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c p) :=
      (IsScalarTower.algebraMap_apply ℂ
        ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S))
        (meroField (Set.univ : Set ℂ)) (c p)).symm
    have hD : ((sineFacePacketDisplacement ω hω J hqJ huJ h2 hqS huS 0 p.1 :
        ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S))) :
        meroField (Set.univ : Set ℂ))
        = addTranslationMeroEquiv (ω q) (p.1 : meroField (Set.univ : Set ℂ))
          - (p.1 : meroField (Set.univ : Set ℂ)) := rfl
    rw [Algebra.smul_def, MulMemClass.coe_mul,
      coe_differentialJet_differentialAdjoin, Algebra.algebraMap_self_apply, hcoefK, hD]
  have hjetsplit : ∀ (p : ↥(facePacket ω hω J) × ℕ),
      differentialJet p.2 (addTranslationMeroEquiv (ω q) (p.1 : meroField (Set.univ : Set ℂ))
          - (p.1 : meroField (Set.univ : Set ℂ)))
        = differentialJet p.2 (rr p.1)
          - differentialJet p.2 (sineDisplacementSlice ω hω hqJ hne hne' p.1 :
              meroField (Set.univ : Set ℂ)) := by
    intro p
    have hadd : differentialJet p.2 (rr p.1)
        = differentialJet p.2 (addTranslationMeroEquiv (ω q)
              (p.1 : meroField (Set.univ : Set ℂ)) - (p.1 : meroField (Set.univ : Set ℂ)))
          + differentialJet p.2 (sineDisplacementSlice ω hω hqJ hne hne' p.1 :
              meroField (Set.univ : Set ℂ)) :=
      differentialJet_additive p.2 _ _
    rw [hadd]
    ring
  have hsum : c.sum (fun p a => algebraMap ℂ (meroField (Set.univ : Set ℂ)) a *
        differentialJet p.2
          (addTranslationMeroEquiv (ω q) (p.1 : meroField (Set.univ : Set ℂ))
            - (p.1 : meroField (Set.univ : Set ℂ))))
      = c.sum (fun p a => algebraMap ℂ (meroField (Set.univ : Set ℂ)) a *
          differentialJet p.2 (rr p.1))
        + c.sum (fun p a => -(algebraMap ℂ (meroField (Set.univ : Set ℂ)) a) *
          differentialJet p.2
            (sineDisplacementSlice ω hω hqJ hne hne' p.1 :
              meroField (Set.univ : Set ℂ))) := by
    simp only [Finsupp.sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hjetsplit p]
    ring
  show addTranslationMeroEquiv (ω q) (k : meroField (Set.univ : Set ℂ))
      - (k : meroField (Set.univ : Set ℂ)) = _
  have hdef : ((sineFaceDifferenceSystemClosed ω hω hS q u).defect 0 k :
        ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S))) =
      (sineFaceDifferenceSystemClosed ω hω hS q u).aut 0 k - k := rfl
  have hcoeEq := congrArg (fun w : ↥(differentialAdjoin ℂ (sineDeeperGenerators ω hω S)) =>
    (w : meroField (Set.univ : Set ℂ))) hEq
  rw [hdef] at hcoeEq
  simp only [AddSubgroupClass.coe_sub] at hcoeEq
  rw [sineFaceDifferenceSystemClosed_aut_coe, sineFacePacketPeriods_zero] at hcoeEq
  rw [hcoeEq, hLHS, hsum]
  show _ = ((algebraMap ↥F₀ ↥(differentialAdjoin ↥F₀ (Set.range P)) b :
      ↥(differentialAdjoin ↥F₀ (Set.range P))) : meroField (Set.univ : Set ℂ)) + _
  have hbb : ((algebraMap ↥F₀ ↥(differentialAdjoin ↥F₀ (Set.range P)) b :
      ↥(differentialAdjoin ↥F₀ (Set.range P))) : meroField (Set.univ : Set ℂ))
      = (b : meroField (Set.univ : Set ℂ)) := rfl
  rw [hbb, hRHS, hbcoe]

/-! ### Descending face-lifting on a free deeper field -/

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **Descending face-lifting for the multiple sine on a free deeper field.**  The translation block
of a face is differentially independent over the differential field generated by the deeper packets
and the rational coordinates. -/
theorem sineFacePacket_differentialIndependent_of_free {μ : ℂ} {rad : ι → ℝ}
    (hrad : ∀ k, 0 < rad k) (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    {S : Set (Finset ι)} (hS : ∀ L ∈ S, ∀ p : ι, p ∉ L → insert p L ∈ S)
    (J : Finset ι) {q u : ι} (hqJ : q ∉ J) (huJ : u ∉ J)
    (hqS : insert q J ∈ S) (huS : insert u J ∈ S) (hJS : J ∉ S)
    (h2 : 2 ≤ (Jᶜ : Finset ι).card) (hne : (Jᶜ : Finset ι).Nonempty)
    (hne' : ((insert q J)ᶜ : Finset ι).Nonempty)
    (hqu2 : 2 ≤ ((insert q J)ᶜ : Finset ι).card)
    {γ : ℂ} (hγ : γ ≠ 0) (hqω : μ * (rad q : ℂ) = γ * (rad q : ℂ))
    (huω : μ * (rad u : ℂ) = γ * (rad u : ℂ))
    (hirr : Irrational (rad q / rad u))
    (hindep : DifferentialIndependent
      ↥(differentialAdjoin ℂ (sineDeeperGenerators (fun k => μ * (rad k : ℂ)) hω
        (facePacketBaseFamily S J q)))
      (facePalette (fun k => μ * (rad k : ℂ)) hω (insert q J) q)) :
    DifferentialIndependent
      ↥(differentialAdjoin ℂ (sineDeeperGenerators (fun k => μ * (rad k : ℂ)) hω S))
      (sineFacePacketBlock (fun k => μ * (rad k : ℂ)) hω J) := by
  refine sineFacePacket_differentialIndependent_of_no_telescoping_closed
    (fun k => μ * (rad k : ℂ)) hω hS J hqJ huJ h2 hqS huS hγ hqω huω hirr ?_
  intro c hc k
  exact ⟨0, sineFacePacket_no_telescoping_of_free (fun k => μ * (rad k : ℂ)) hω hS J
    hqJ huJ hqS huS hJS h2 hne hne' hindep
    (sineDisplacementSlice_injective hrad hind hω hqJ hqu2 hne hne') c hc k⟩



/-! ### Palette independence with the boundary faces adjoined -/

theorem sineDeeperGenerators_baseFamily_union (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    (N B : Set (Finset ι)) (J : Finset ι) (q : ι) (hqB : insert q J ∉ B) :
    sineDeeperGenerators ω hω (facePacketBaseFamily N J q) ∪ sineFacePacketUnion ω hω B
      = sineDeeperGenerators ω hω (facePacketBaseFamily (N ∪ B) J q) := by
  have hfam : facePacketBaseFamily (N ∪ B) J q = facePacketBaseFamily N J q ∪ B := by
    ext L
    simp only [facePacketBaseFamily, Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hL | hL, hne⟩
      · exact Or.inl ⟨hL, hne⟩
      · exact Or.inr hL
    · rintro (⟨hL, hne⟩ | hL)
      · exact ⟨Or.inl hL, hne⟩
      · exact ⟨Or.inr hL, fun h => hqB (h ▸ hL)⟩
  rw [hfam, sineDeeperGenerators, sineDeeperGenerators, sineFacePacketUnion_union]
  ext y
  simp only [Set.mem_union]
  tauto

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **Palette independence over the deeper base with boundary.**  The packets of the boundary faces
are differentially algebraic over the constants, so adjoining them to the complementary deeper base
leaves the palette of the target packet independent. -/
theorem sineFacePalette_differentialIndependent_of_deeper_with_boundary {μ : ℂ} {rad : ι → ℝ}
    (hrad : ∀ k, 0 < rad k) (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    (N B : Set (Finset ι)) (hNfaces : ∀ L ∈ N, 2 ≤ (Lᶜ : Finset ι).card)
    (hBDA : ∀ L ∈ B, ∀ y ∈ facePacket (fun k => μ * (rad k : ℂ)) hω L,
      DifferentialAlgebraicOver ℂ y)
    (hdeep : DiffIndepOn ↥meromorphicRationalCoordinateField
      (sineFacePacketUnion (fun k => μ * (rad k : ℂ)) hω N))
    (J : Finset ι) {q : ι} (hqN : insert q J ∈ N) (hqB : insert q J ∉ B) :
    DifferentialIndependent
      ↥(differentialAdjoin ℂ (sineDeeperGenerators (fun k => μ * (rad k : ℂ)) hω
        (facePacketBaseFamily (N ∪ B) J q)))
      (facePalette (fun k => μ * (rad k : ℂ)) hω (insert q J) q) := by
  classical
  haveI : DifferentialAlgebra
      ↥(differentialAdjoin ℂ (sineDeeperGenerators (fun k => μ * (rad k : ℂ)) hω
        (facePacketBaseFamily N J q)))
      (meroField (Set.univ : Set ℂ)) :=
    ⟨fun x => derivationClosedDifferential_apply _
      (derivationClosed_differentialAdjoin ℂ
        (sineDeeperGenerators (fun k => μ * (rad k : ℂ)) hω
          (facePacketBaseFamily N J q))) x⟩
  have hKcard : 2 ≤ ((insert q J)ᶜ : Finset ι).card := hNfaces (insert q J) hqN
  have hsetN : DiffIndepOn
      ↥(differentialAdjoin ℂ (sineDeeperGenerators (fun k => μ * (rad k : ℂ)) hω
        (facePacketBaseFamily N J q)))
      (facePacket (fun k => μ * (rad k : ℂ)) hω (insert q J)) := by
    have hfam := sineFacePalette_differentialIndependent_of_deeper hrad hind hω N hNfaces
      hdeep J hqN
    have hrange := diffIndepOn_range_of_differentialIndependent hfam
    rwa [range_facePalette (fun k => μ * (rad k : ℂ)) hω (Finset.mem_insert_self q J)] at hrange
  have hBBDA : ∀ y ∈ sineFacePacketUnion (fun k => μ * (rad k : ℂ)) hω B,
      DifferentialAlgebraicOver
        ↥(differentialAdjoin ℂ (sineDeeperGenerators (fun k => μ * (rad k : ℂ)) hω
          (facePacketBaseFamily N J q))) y := by
    intro y hy
    obtain ⟨L, hLB, hyL⟩ := Set.mem_iUnion₂.mp hy
    have hdaC := hBDA L hLB y hyL
    intro hindep
    exact hdaC (HTGeometry.DifferentialIndependent.restrictScalarsTower hindep)
  have hnested := diffIndepOn_differentialAdjoin_of_differentialAlgebraicOver hsetN hBBDA
  have hcarrier : ((differentialAdjoin
        ↥(differentialAdjoin ℂ (sineDeeperGenerators (fun k => μ * (rad k : ℂ)) hω
          (facePacketBaseFamily N J q)))
        (sineFacePacketUnion (fun k => μ * (rad k : ℂ)) hω B) :
      IntermediateField _ (meroField (Set.univ : Set ℂ))) :
      Set (meroField (Set.univ : Set ℂ)))
      = ((differentialAdjoin ℂ (sineDeeperGenerators (fun k => μ * (rad k : ℂ)) hω
          (facePacketBaseFamily (N ∪ B) J q)) :
        IntermediateField ℂ (meroField (Set.univ : Set ℂ))) :
        Set (meroField (Set.univ : Set ℂ))) := by
    rw [coe_differentialAdjoin_differentialAdjoin,
      sineDeeperGenerators_baseFamily_union (fun k => μ * (rad k : ℂ)) hω N B J q hqB]
  have hset : DiffIndepOn
      ↥(differentialAdjoin ℂ (sineDeeperGenerators (fun k => μ * (rad k : ℂ)) hω
        (facePacketBaseFamily (N ∪ B) J q)))
      (facePacket (fun k => μ * (rad k : ℂ)) hω (insert q J)) :=
    differentialIndependent_of_coe_eq hcarrier hnested
  exact facePalette_differentialIndependent_of_diffIndepOn hrad hind hω hKcard
    (Finset.mem_insert_self q J) hset


end

end GaloisForLFunctions.HTGeometry

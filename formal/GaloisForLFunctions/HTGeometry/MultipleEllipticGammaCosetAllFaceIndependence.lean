import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaCosetTranslateInjective
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaAllFaceIndependence

/-!
# All labelled proper face packets are jointly differentially independent

The labelled analogue of `MultipleEllipticGammaAllFaceIndependence`.  Under integral period
independence and coset separation of the labels, the union of the labelled external translation
packets of every face retaining at least two periods is differentially independent over the
constants.

This is the arbitrary-complex-translation extension of the structural hierarchy theorem: the label
set is an arbitrary family of complex numbers pairwise inequivalent modulo the full period lattice
`ℤ + ∑_i ℤ τ_i`, so a whole system of external cosets is jointly free.

* **`cosetProperFacePackets_diffIndepOn`** — the theorem.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry
open MatroidGluing MatroidGluing.Rank MatroidGluing.Meromorphic

noncomputable section

attribute [local instance] facePacketMeroDecidableEq

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem cosetFacePalette_differentialIndependent_of_deeper
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {A : Set ℂ} (hA : CosetSeparated τ A)
    (S : Set (Finset ι)) (hSfaces : ∀ L ∈ S, 2 ≤ (Lᶜ).card)
    (hdeep : DiffIndepOn ℂ (cosetFacePacketUnion τ hτ A S))
    (J : Finset ι) {q : ι} (hqS : insert q J ∈ S) :
    DifferentialIndependent
      ↥(differentialAdjoin ℂ
        (cosetFacePacketUnion τ hτ A (facePacketBaseFamily S J q)))
      (cosetFacePalette τ hτ A (insert q J) q) := by
  classical
  let K := insert q J
  let B := cosetFacePacketUnion τ hτ A (facePacketBaseFamily S J q)
  let P := cosetFacePacket τ hτ A K
  have hKcard : 2 ≤ (Kᶜ).card := hSfaces K hqS
  have hPB : Disjoint P B := by
    rw [Set.disjoint_left]
    intro y hyP hyB
    obtain ⟨L, hLbase, hyL⟩ := Set.mem_iUnion₂.mp hyB
    have hLS : L ∈ S := hLbase.1
    have hLK : L ≠ K := hLbase.2
    obtain ⟨g, hg, hgy⟩ := hyP
    obtain ⟨h, hh, hhy⟩ := hyL
    exact (cosetFace_translate_ne_of_ne τ hτ hQ hA K L hLK.symm
      hKcard (hSfaces L hLS) hg hh) (hgy.trans hhy.symm)
  have hsub : P ∪ B ⊆ cosetFacePacketUnion τ hτ A S := by
    intro y hy
    rcases hy with hyP | hyB
    · exact Set.mem_iUnion₂.mpr ⟨K, hqS, hyP⟩
    · obtain ⟨L, hL, hyL⟩ := Set.mem_iUnion₂.mp hyB
      exact Set.mem_iUnion₂.mpr ⟨L, hL.1, hyL⟩
  have hrel : DiffIndepOn ↥(differentialAdjoin ℂ B) P :=
    ((diffIndepOn_union_iff hPB).mp (hdeep.subset hsub)).2
  let e :
      (↥(cosetFacePacketSlice τ hτ A K q) × ℤ) → P :=
    fun p => ⟨cosetFacePalette τ hτ A K q p, by
      change cosetFacePalette τ hτ A K q p ∈ cosetFacePacket τ hτ A K
      rw [← range_cosetFacePalette τ hτ A K (Finset.mem_insert_self q J)]
      exact Set.mem_range_self p⟩
  have he : Function.Injective e := by
    intro x y hxy
    apply cosetFacePalette_injective τ hτ hQ hA K hKcard (Finset.mem_insert_self q J)
    exact congrArg (fun z : P => (z : meroField (Set.univ : Set ℂ))) hxy
  have hfamily :=
    (show DifferentialIndependent ↥(differentialAdjoin ℂ B)
      (Subtype.val : P → meroField (Set.univ : Set ℂ)) from hrel).comp e he
  simpa [e, K, P, B] using! hfamily

set_option maxHeartbeats 1600000 in
theorem cosetFaceLayer_star_exponent_eq
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {A : Set ℂ} (hA : CosetSeparated τ A)
    (faces : Finset (Finset ι)) (hfaces : ∀ J ∈ faces, 2 ≤ (Jᶜ).card)
    {B : Finset ι} {q : ι}
    {m n : ℤ} {y z : meroField (Set.univ : Set ℂ)}
    (hy : y ∈ (⋃ J ∈ faces.filter (fun J => insert q B ⊆ J),
      cosetFacePacketSlice τ hτ A J q))
    (hz : z ∈ (⋃ J ∈ faces.filter (fun J => insert q B ⊆ J),
      cosetFacePacketSlice τ hτ A J q))
    (heq : (meroTranslationPerm (τ q) ^ m) y =
      (meroTranslationPerm (τ q) ^ n) z) :
    m = n := by
  classical
  obtain ⟨J, hJfilter, hyJ⟩ := Set.mem_iUnion₂.mp hy
  obtain ⟨L, hLfilter, hzL⟩ := Set.mem_iUnion₂.mp hz
  obtain ⟨hJfaces, hqJsub⟩ := Finset.mem_filter.mp hJfilter
  obtain ⟨hLfaces, hqLsub⟩ := Finset.mem_filter.mp hLfilter
  have hqJ : q ∈ J := hqJsub (Finset.mem_insert_self q B)
  have hqL : q ∈ L := hqLsub (Finset.mem_insert_self q B)
  obtain ⟨g, hg, hgy⟩ := hyJ
  obtain ⟨h, hh, hhz⟩ := hzL
  have hgJ : (m : ℂ) * τ q + g ∈ cosetFaceShiftSet τ A J :=
    cosetFaceShiftSet_add_zsmul τ A J hqJ
      (cosetFaceShiftSetSlice_subset τ A J q hg) m
  have hhL : (n : ℂ) * τ q + h ∈ cosetFaceShiftSet τ A L :=
    cosetFaceShiftSet_add_zsmul τ A L hqL
      (cosetFaceShiftSetSlice_subset τ A L q hh) n
  have htrans :
      addTranslationMeroEquiv ((m : ℂ) * τ q + g)
          (multipleEllipticGammaLogDerivFaceMero τ hτ J) =
        addTranslationMeroEquiv ((n : ℂ) * τ q + h)
          (multipleEllipticGammaLogDerivFaceMero τ hτ L) := by
    have heq' :
        addTranslationMeroEquiv ((m : ℂ) * τ q) y =
          addTranslationMeroEquiv ((n : ℂ) * τ q) z := by
      simpa [meroTranslationPerm_zpow_apply] using heq
    rw [← hgy, ← hhz, addTranslationMeroEquiv_add,
      addTranslationMeroEquiv_add] at heq'
    exact heq'
  have hJL : J = L := by
    by_contra hne
    exact (cosetFace_translate_ne_of_ne τ hτ hQ hA J L hne
      (hfaces J hJfaces) (hfaces L hLfaces) hgJ hhL) htrans
  subst L
  have hshift :
      (m : ℂ) * τ q + g = (n : ℂ) * τ q + h :=
    cosetFaceShiftSet_translate_injective τ hτ hQ hA J (hfaces J hJfaces) hgJ hhL htrans
  exact cosetFaceShiftSetSlice_zsmul_eq τ hQ hA J hqJ hg hh hshift

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Labelled packets of faces below the hypertranscendental range are differentially
algebraic. -/
theorem differentialAlgebraicOver_cosetFacePacket_of_compl_lt_two
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (hι : 2 ≤ Fintype.card ι) (A : Set ℂ) (L : Finset ι) (hLcard : (Lᶜ).card < 2)
    {y : meroField (Set.univ : Set ℂ)}
    (hy : y ∈ cosetFacePacket τ hτ A L) :
    DifferentialAlgebraicOver ℂ y := by
  classical
  obtain ⟨g, -, rfl⟩ := hy
  have hzero : (0 : ℂ) ∈ faceShiftLattice τ L := ⟨0, fun _ _ => rfl, by simp⟩
  have hmem : multipleEllipticGammaLogDerivFaceMero τ hτ L ∈
      multipleEllipticGammaFacePacket τ hτ L :=
    ⟨0, hzero, by
      change addTranslationMeroEquiv 0
        (multipleEllipticGammaLogDerivFaceMero τ hτ L) = _
      rw [addTranslationMeroEquiv_zero_apply]⟩
  have hbase : DifferentialAlgebraicOver ℂ
      (multipleEllipticGammaLogDerivFaceMero τ hτ L) :=
    differentialAlgebraicOver_facePacket_of_compl_lt_two τ hτ hQ hι L hLcard hmem
  exact (HTGeometry.DifferentialAlgEquiv.differentialAlgebraicOver_map_iff
    (addTranslationMeroDifferentialAlgEquiv g) _).mpr hbase

set_option maxHeartbeats 2500000 in
set_option synthInstance.maxHeartbeats 1200000 in
theorem cosetFacePalette_differentialIndependent_of_deeper_with_boundary
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {A : Set ℂ} (hA : CosetSeparated τ A)
    (N Bd : Set (Finset ι))
    (hNfaces : ∀ L ∈ N, 2 ≤ (Lᶜ).card)
    (hBDA : ∀ L ∈ Bd, ∀ y ∈ cosetFacePacket τ hτ A L,
      DifferentialAlgebraicOver ℂ y)
    (hdeep : DiffIndepOn ℂ (cosetFacePacketUnion τ hτ A N))
    (J : Finset ι) {q : ι} (hqN : insert q J ∈ N) (hqB : insert q J ∉ Bd) :
    DifferentialIndependent
      ↥(differentialAdjoin ℂ
        (cosetFacePacketUnion τ hτ A (facePacketBaseFamily (N ∪ Bd) J q)))
      (cosetFacePalette τ hτ A (insert q J) q) := by
  classical
  let K := insert q J
  let N0 := cosetFacePacketUnion τ hτ A (facePacketBaseFamily N J q)
  let BB := cosetFacePacketUnion τ hτ A Bd
  let P := cosetFacePacket τ hτ A K
  have hfamilyN :=
    cosetFacePalette_differentialIndependent_of_deeper τ hτ hQ hA N hNfaces hdeep J hqN
  have hsetN : DiffIndepOn ↥(differentialAdjoin ℂ N0) P := by
    have hrange := diffIndepOn_range_of_differentialIndependent hfamilyN
    simpa [N0, P, K, range_cosetFacePalette τ hτ A (insert q J)
      (Finset.mem_insert_self q J)] using hrange
  have hBBDA : ∀ y ∈ BB,
      DifferentialAlgebraicOver ↥(differentialAdjoin ℂ N0) y := by
    intro y hy
    obtain ⟨L, hLB, hyL⟩ := Set.mem_iUnion₂.mp hy
    have hdaC := hBDA L hLB y hyL
    intro hind
    exact hdaC (HTGeometry.DifferentialIndependent.restrictScalarsTower hind)
  have hsetNested : DiffIndepOn
      ↥(differentialAdjoin ↥(differentialAdjoin ℂ N0) BB) P :=
    diffIndepOn_differentialAdjoin_of_differentialAlgebraicOver hsetN hBBDA
  have hsetUnion : DiffIndepOn ↥(differentialAdjoin ℂ (N0 ∪ BB)) P :=
    (diffIndepOn_union_iff_nested N0 BB P).mpr hsetNested
  have hgen :
      cosetFacePacketUnion τ hτ A (facePacketBaseFamily (N ∪ Bd) J q) = N0 ∪ BB := by
    ext y
    constructor
    · intro hy
      obtain ⟨L, hLbase, hyL⟩ := Set.mem_iUnion₂.mp hy
      rcases hLbase.1 with hLN | hLB
      · exact Or.inl (Set.mem_iUnion₂.mpr ⟨L, ⟨hLN, hLbase.2⟩, hyL⟩)
      · exact Or.inr (Set.mem_iUnion₂.mpr ⟨L, hLB, hyL⟩)
    · rintro (hyN | hyB)
      · obtain ⟨L, hLbase, hyL⟩ := Set.mem_iUnion₂.mp hyN
        exact Set.mem_iUnion₂.mpr ⟨L, ⟨Or.inl hLbase.1, hLbase.2⟩, hyL⟩
      · obtain ⟨L, hLB, hyL⟩ := Set.mem_iUnion₂.mp hyB
        have hLK : L ≠ K := by
          intro h
          subst L
          exact hqB hLB
        exact Set.mem_iUnion₂.mpr ⟨L, ⟨Or.inr hLB, hLK⟩, hyL⟩
  rw [hgen]
  let e :
      (↥(cosetFacePacketSlice τ hτ A K q) × ℤ) → P :=
    fun p => ⟨cosetFacePalette τ hτ A K q p, by
      change cosetFacePalette τ hτ A K q p ∈ cosetFacePacket τ hτ A K
      rw [← range_cosetFacePalette τ hτ A K (Finset.mem_insert_self q J)]
      exact Set.mem_range_self p⟩
  have he : Function.Injective e := by
    intro x y hxy
    apply cosetFacePalette_injective τ hτ hQ hA K (hNfaces K hqN)
      (Finset.mem_insert_self q J)
    exact congrArg (fun z : P => (z : meroField (Set.univ : Set ℂ))) hxy
  have hfamily :=
    (show DifferentialIndependent ↥(differentialAdjoin ℂ (N0 ∪ BB))
      (Subtype.val : P → meroField (Set.univ : Set ℂ)) from hsetUnion).comp e he
  simpa [e, K, P] using! hfamily

set_option maxHeartbeats 3000000 in
set_option synthInstance.maxHeartbeats 1200000 in
theorem cosetFaceLayer_diffIndepOn_with_boundary
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {A : Set ℂ} (hA : CosetSeparated τ A)
    (N Bd : Set (Finset ι))
    (hSclosed : ∀ L ∈ N ∪ Bd, ∀ p : ι, p ∉ L → insert p L ∈ N ∪ Bd)
    (hNfaces : ∀ L ∈ N, 2 ≤ (Lᶜ).card)
    (hBDA : ∀ L ∈ Bd, ∀ y ∈ cosetFacePacket τ hτ A L,
      DifferentialAlgebraicOver ℂ y)
    (hNB : Disjoint N Bd)
    (hdeep : DiffIndepOn ℂ (cosetFacePacketUnion τ hτ A N))
    (faces : Finset (Finset ι)) (s : ℕ)
    (huniform : ∀ J ∈ faces, J.card = s)
    (dq du : Finset ι → ι)
    (hq : ∀ J ∈ faces, dq J ∉ J) (hu : ∀ J ∈ faces, du J ∉ J)
    (hqu : ∀ J ∈ faces, dq J ≠ du J)
    (hcoface : ∀ J ∈ faces, ∀ p : ι, p ∉ J → insert p J ∈ N)
    (hJS : ∀ J ∈ faces, J ∉ N ∪ Bd)
    (hfaces : ∀ J ∈ faces, 2 ≤ (Jᶜ).card) :
    DiffIndepOn
      ↥(differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A (N ∪ Bd)))
      (faceStar faces (cosetFacePacket τ hτ A) ∅) := by
  classical
  apply cosetFaceLayer_diffIndepOn_deeper τ hτ A hSclosed
    faces s huniform dq du hq hu
    (fun J hJ => Or.inl (hcoface J hJ (dq J) (hq J hJ)))
    (fun J hJ => Or.inl (hcoface J hJ (du J) (hu J hJ))) hJS
  · intro J hJ
    simpa [facePacketPeriods, ellipticGammaSourcePeriods] using
      (linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent
        τ hQ (hqu J hJ))
  · intro J hJ
    exact cosetFacePalette_differentialIndependent_of_deeper_with_boundary
      τ hτ hQ hA N Bd hNfaces hBDA hdeep J
        (hcoface J hJ (dq J) (hq J hJ))
        (fun hB => Set.disjoint_left.mp hNB
          (hcoface J hJ (dq J) (hq J hJ)) hB)
  · intro J hJ
    exact cosetFacePacketDisplacementSlice_injective τ hτ hQ hA J (hq J hJ)
      (hNfaces (insert (dq J) J) (hcoface J hJ (dq J) (hq J hJ)))
  · intro C q _ _ m n y z hy hz heq
    exact cosetFaceLayer_star_exponent_eq τ hτ hQ hA faces hfaces hy hz heq
  · intro C q _ _ t ht n z hz
    obtain ⟨y, hyt, rfl⟩ := hz
    obtain ⟨J, hJfilter, hyJ⟩ :=
      Set.mem_iUnion₂.mp (ht (Finset.mem_coe.mpr hyt))
    obtain ⟨hJfilter', hqJ⟩ := Finset.mem_filter.mp hJfilter
    obtain ⟨hJfaces, -⟩ := Finset.mem_filter.mp hJfilter'
    have hqS' : insert q J ∈ N ∪ Bd :=
      Or.inl (hcoface J hJfaces q hqJ)
    simpa [meroTranslationPerm_zpow_apply] using
      (differentialAlgebraicOver_cosetOffStar_translate_deeper
        τ hτ A J hqJ hqS' n hyJ (Finset.mem_coe.mpr hyt))

set_option maxHeartbeats 3000000 in
set_option synthInstance.maxHeartbeats 1200000 in
theorem cosetFaceLayer_diffIndepOn_with_boundary_auto
    [Nonempty ι]
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {A : Set ℂ} (hA : CosetSeparated τ A)
    (N Bd : Set (Finset ι))
    (hSclosed : ∀ L ∈ N ∪ Bd, ∀ p : ι, p ∉ L → insert p L ∈ N ∪ Bd)
    (hNfaces : ∀ L ∈ N, 2 ≤ (Lᶜ).card)
    (hBDA : ∀ L ∈ Bd, ∀ y ∈ cosetFacePacket τ hτ A L,
      DifferentialAlgebraicOver ℂ y)
    (hNB : Disjoint N Bd)
    (hdeep : DiffIndepOn ℂ (cosetFacePacketUnion τ hτ A N))
    (faces : Finset (Finset ι)) (s : ℕ)
    (huniform : ∀ J ∈ faces, J.card = s)
    (hthree : ∀ J ∈ faces, 3 ≤ (Jᶜ).card)
    (hcoface : ∀ J ∈ faces, ∀ p : ι, p ∉ J → insert p J ∈ N)
    (hJS : ∀ J ∈ faces, J ∉ N ∪ Bd) :
    DiffIndepOn
      ↥(differentialAdjoin ℂ (cosetFacePacketUnion τ hτ A (N ∪ Bd)))
      (faceStar faces (cosetFacePacket τ hτ A) ∅) := by
  classical
  have hpair : ∀ J ∈ faces, ∃ q u : ι, q ∉ J ∧ u ∉ J ∧ q ≠ u := by
    intro J hJ
    obtain ⟨P, hPsub, hPcard⟩ :=
      Finset.exists_subset_card_eq (show 2 ≤ (Jᶜ).card by
        have := hthree J hJ
        omega)
    obtain ⟨q, u, hqu, hP⟩ := Finset.card_eq_two.mp hPcard
    have hqP : q ∈ P := by rw [hP]; simp
    have huP : u ∈ P := by rw [hP]; simp
    exact ⟨q, u, Finset.mem_compl.mp (hPsub hqP),
      Finset.mem_compl.mp (hPsub huP), hqu⟩
  let i0 : ι := Classical.choice (inferInstance : Nonempty ι)
  let dq : Finset ι → ι := fun J =>
    if hJ : J ∈ faces then (hpair J hJ).choose else i0
  let du : Finset ι → ι := fun J =>
    if hJ : J ∈ faces then (hpair J hJ).choose_spec.choose else i0
  have hq : ∀ J ∈ faces, dq J ∉ J := by
    intro J hJ
    simp only [dq, dif_pos hJ]
    exact (hpair J hJ).choose_spec.choose_spec.1
  have hu : ∀ J ∈ faces, du J ∉ J := by
    intro J hJ
    simp only [du, dif_pos hJ]
    exact (hpair J hJ).choose_spec.choose_spec.2.1
  have hqu : ∀ J ∈ faces, dq J ≠ du J := by
    intro J hJ
    simp only [dq, du, dif_pos hJ]
    exact (hpair J hJ).choose_spec.choose_spec.2.2
  exact cosetFaceLayer_diffIndepOn_with_boundary
    τ hτ hQ hA N Bd hSclosed hNfaces hBDA hNB hdeep faces s huniform
      dq du hq hu hqu hcoface hJS (fun J hJ => by
        have := hthree J hJ
        omega)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1500000 in
/-- **All labelled proper face packets are jointly differentially independent.**  Under integral
period independence and coset separation of the labels, the union of the labelled external
translation packets of every face retaining at least two periods is differentially independent
over the constants. -/
theorem cosetProperFacePackets_diffIndepOn
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι)
    {A : Set ℂ} (hA : CosetSeparated τ A) :
    DiffIndepOn ℂ
      (cosetFacePacketUnion τ hτ A {J : Finset ι | 2 ≤ (Jᶜ).card}) := by
  classical
  letI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hboundary :
      ∀ L ∈ multipleEllipticGammaBoundaryFaces (ι := ι),
        ∀ y ∈ cosetFacePacket τ hτ A L,
          DifferentialAlgebraicOver ℂ y := by
    intro L hL y hy
    exact differentialAlgebraicOver_cosetFacePacket_of_compl_lt_two
      τ hτ hQ hι A L hL hy
  have hind : ∀ k, DiffIndepOn ℂ
      (cosetFacePacketUnion τ hτ A (multipleEllipticGammaDeeperFaces (ι := ι) k)) := by
    intro k
    induction k with
    | zero =>
        rw [multipleEllipticGammaDeeperFaces_zero, cosetFacePacketUnion_empty]
        exact diffIndepOn_empty
    | succ k ih =>
        let N := multipleEllipticGammaDeeperFaces (ι := ι) k
        let Bd := multipleEllipticGammaBoundaryFaces (ι := ι)
        let faces := multipleEllipticGammaFaceLayer (ι := ι) k
        have hNfaces : ∀ L ∈ N, 2 ≤ (Lᶜ).card := by
          intro L hL
          exact hL.1
        have hNB : Disjoint N Bd := by
          rw [Set.disjoint_left]
          intro L hLN hLB
          exact (not_lt_of_ge hLN.1) hLB
        have hSclosed :
            ∀ L ∈ N ∪ Bd, ∀ p : ι, p ∉ L → insert p L ∈ N ∪ Bd := by
          intro L hL p hp
          have hcard := face_compl_card_insert_add_one L hp
          have hlt : ((insert p L)ᶜ).card < k + 2 := by
            rcases hL with hLN | hLB
            · have := hLN.2
              omega
            · change (Lᶜ).card < 2 at hLB
              omega
          by_cases hb : ((insert p L)ᶜ).card < 2
          · exact Or.inr hb
          · exact Or.inl ⟨by omega, hlt⟩
        have hBDA :
            ∀ L ∈ Bd, ∀ y ∈ cosetFacePacket τ hτ A L,
              DifferentialAlgebraicOver ℂ y := hboundary
        have hBUnionDA :
            ∀ y ∈ cosetFacePacketUnion τ hτ A Bd,
              DifferentialAlgebraicOver ℂ y := by
          intro y hy
          obtain ⟨L, hLB, hyL⟩ := Set.mem_iUnion₂.mp hy
          exact hBDA L hLB y hyL
        have huniform :
            ∀ J ∈ faces, J.card = Fintype.card ι - (k + 2) := by
          intro J hJ
          have hcomp : (Jᶜ).card = k + 2 := by
            simpa [faces, multipleEllipticGammaFaceLayer] using hJ
          have htotal := Finset.card_add_card_compl J
          omega
        have hlayerBig : DiffIndepOn
            ↥(differentialAdjoin ℂ
              (cosetFacePacketUnion τ hτ A (N ∪ Bd)))
            (cosetFacePacketUnion τ hτ A (↑faces : Set (Finset ι))) := by
          rw [← cosetFaceStar_empty_eq_cosetFacePacketUnion]
          by_cases hk : k = 0
          · subst k
            have hbottom :
                ∀ J ∈ faces, ∃ a b : ι, a ∉ J ∧ b ∉ J ∧ a ≠ b ∧
                  ∀ i, i ∉ J → i = a ∨ i = b := by
              intro J hJ
              have hcomp : (Jᶜ).card = 2 := by
                simpa [faces, multipleEllipticGammaFaceLayer] using hJ
              obtain ⟨a, b, hab, hJc⟩ := Finset.card_eq_two.mp hcomp
              have haJ : a ∉ J := by
                have : a ∈ Jᶜ := by rw [hJc]; simp
                exact Finset.mem_compl.mp this
              have hbJ : b ∉ J := by
                have : b ∈ Jᶜ := by rw [hJc]; simp
                exact Finset.mem_compl.mp this
              refine ⟨a, b, haJ, hbJ, hab, ?_⟩
              intro i hi
              have hiC : i ∈ Jᶜ := Finset.mem_compl.mpr hi
              rw [hJc] at hiC
              simpa using hiC
            have hNempty : N = ∅ := multipleEllipticGammaDeeperFaces_zero
            rw [hNempty, Set.empty_union]
            exact cosetFaceStar_diffIndepOn_bottom_daExtension
              τ hτ hQ hA faces (Fintype.card ι - 2)
              (by
                intro J hJ
                simpa using huniform J hJ)
              hbottom hBUnionDA
          · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
            have hthree : ∀ J ∈ faces, 3 ≤ (Jᶜ).card := by
              intro J hJ
              have hcomp : (Jᶜ).card = k + 2 := by
                simpa [faces, multipleEllipticGammaFaceLayer] using hJ
              omega
            have hcoface :
                ∀ J ∈ faces, ∀ p : ι, p ∉ J → insert p J ∈ N := by
              intro J hJ p hp
              have hcomp : (Jᶜ).card = k + 2 := by
                simpa [faces, multipleEllipticGammaFaceLayer] using hJ
              have hins := face_compl_card_insert_add_one J hp
              exact ⟨by omega, by omega⟩
            have hJS : ∀ J ∈ faces, J ∉ N ∪ Bd := by
              intro J hJ hmem
              have hcomp : (Jᶜ).card = k + 2 := by
                simpa [faces, multipleEllipticGammaFaceLayer] using hJ
              rcases hmem with hJN | hJB
              · exact (ne_of_lt hJN.2) hcomp
              · change (Jᶜ).card < 2 at hJB
                omega
            exact cosetFaceLayer_diffIndepOn_with_boundary_auto
              τ hτ hQ hA N Bd hSclosed hNfaces hBDA hNB ih faces
                (Fintype.card ι - (k + 2)) huniform hthree hcoface hJS
        let NG := cosetFacePacketUnion τ hτ A N
        let BG := cosetFacePacketUnion τ hτ A Bd
        let I := cosetFacePacketUnion τ hτ A (↑faces : Set (Finset ι))
        have hlayerUnion : DiffIndepOn
            ↥(differentialAdjoin ℂ (NG ∪ BG)) I := by
          rw [← cosetFacePacketUnion_union]
          exact hlayerBig
        have hlayerNested : DiffIndepOn
            ↥(differentialAdjoin ↥(differentialAdjoin ℂ NG) BG) I :=
          (diffIndepOn_union_iff_nested NG BG I).mp hlayerUnion
        have hBGDA : ∀ y ∈ BG,
            DifferentialAlgebraicOver ↥(differentialAdjoin ℂ NG) y := by
          intro y hy
          obtain ⟨L, hLB, hyL⟩ := Set.mem_iUnion₂.mp hy
          have hdaC := hboundary L hLB y hyL
          intro hdi
          exact hdaC (HTGeometry.DifferentialIndependent.restrictScalarsTower hdi)
        have hlayer : DiffIndepOn ↥(differentialAdjoin ℂ NG) I :=
          (diffIndepOn_differentialAdjoin_iff_of_differentialAlgebraicOver hBGDA).mp
            hlayerNested
        rw [multipleEllipticGammaDeeperFaces_succ]
        exact cosetFacePacketUnion_diffIndepOn_union τ hτ A N
          (↑faces : Set (Finset ι)) ih hlayer
  have hfinal := hind (Fintype.card ι - 1)
  have hfaces :
      multipleEllipticGammaDeeperFaces (ι := ι) (Fintype.card ι - 1) =
        {J : Finset ι | 2 ≤ (Jᶜ).card} := by
    ext J
    simp only [multipleEllipticGammaDeeperFaces, Set.mem_setOf_eq]
    have hcardle : (Jᶜ).card ≤ Fintype.card ι := Finset.card_le_univ _
    constructor
    · exact fun h => h.1
    · intro h
      constructor
      · exact h
      · omega
  rwa [hfaces] at hfinal

end

end GaloisForLFunctions

import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaFacePacketDisjointness
import GaloisForLFunctions.HTGeometry.FaceLayerOffStarDisplacement

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
theorem facePalette_differentialIndependent_of_deeper
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (S : Set (Finset ι)) (hSfaces : ∀ L ∈ S, 2 ≤ (Lᶜ).card)
    (hdeep : DiffIndepOn ℂ (facePacketUnion τ hτ S))
    (J : Finset ι) {q : ι} (hqS : insert q J ∈ S) :
    DifferentialIndependent
      ↥(differentialAdjoin ℂ
        (facePacketUnion τ hτ (facePacketBaseFamily S J q)))
      (facePalette τ hτ (insert q J) q) := by
  classical
  let K := insert q J
  let B := facePacketUnion τ hτ (facePacketBaseFamily S J q)
  let P := multipleEllipticGammaFacePacket τ hτ K
  have hKcard : 2 ≤ (Kᶜ).card := hSfaces K hqS
  have hPB : Disjoint P B := by
    rw [Set.disjoint_left]
    intro y hyP hyB
    obtain ⟨L, hLbase, hyL⟩ := Set.mem_iUnion₂.mp hyB
    have hLS : L ∈ S := hLbase.1
    have hLK : L ≠ K := hLbase.2
    obtain ⟨g, hg, hgy⟩ := hyP
    obtain ⟨h, hh, hhy⟩ := hyL
    exact (multipleEllipticGammaFace_translate_ne_of_ne τ hτ hQ K L hLK.symm
      hKcard (hSfaces L hLS) hg hh) (hgy.trans hhy.symm)
  have hsub : P ∪ B ⊆ facePacketUnion τ hτ S := by
    intro y hy
    rcases hy with hyP | hyB
    · exact Set.mem_iUnion₂.mpr ⟨K, hqS, hyP⟩
    · obtain ⟨L, hL, hyL⟩ := Set.mem_iUnion₂.mp hyB
      exact Set.mem_iUnion₂.mpr ⟨L, hL.1, hyL⟩
  have hrel : DiffIndepOn ↥(differentialAdjoin ℂ B) P :=
    ((diffIndepOn_union_iff hPB).mp (hdeep.subset hsub)).2
  let e :
      (↥(multipleEllipticGammaFacePacketSlice τ hτ K q) × ℤ) → P :=
    fun p => ⟨facePalette τ hτ K q p, by
      change facePalette τ hτ K q p ∈
        multipleEllipticGammaFacePacket τ hτ K
      rw [← range_facePalette τ hτ K (Finset.mem_insert_self q J)]
      exact Set.mem_range_self p⟩
  have he : Function.Injective e := by
    intro x y hxy
    apply facePalette_injective τ hτ hQ K hKcard (Finset.mem_insert_self q J)
    exact congrArg (fun z : P => (z : meroField (Set.univ : Set ℂ))) hxy
  have hfamily :=
    (show DifferentialIndependent ↥(differentialAdjoin ℂ B)
      (Subtype.val : P → meroField (Set.univ : Set ℂ)) from hrel).comp e he
  simpa [e, K, P, B] using hfamily

set_option maxHeartbeats 1600000 in
theorem faceLayer_star_exponent_eq
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (faces : Finset (Finset ι)) (hfaces : ∀ J ∈ faces, 2 ≤ (Jᶜ).card)
    {A : Finset ι} {q : ι}
    {m n : ℤ} {y z : meroField (Set.univ : Set ℂ)}
    (hy : y ∈ (⋃ J ∈ faces.filter (fun J => insert q A ⊆ J),
      multipleEllipticGammaFacePacketSlice τ hτ J q))
    (hz : z ∈ (⋃ J ∈ faces.filter (fun J => insert q A ⊆ J),
      multipleEllipticGammaFacePacketSlice τ hτ J q))
    (heq : (meroTranslationPerm (τ q) ^ m) y =
      (meroTranslationPerm (τ q) ^ n) z) :
    m = n := by
  classical
  obtain ⟨J, hJfilter, hyJ⟩ := Set.mem_iUnion₂.mp hy
  obtain ⟨L, hLfilter, hzL⟩ := Set.mem_iUnion₂.mp hz
  obtain ⟨hJfaces, hqJsub⟩ := Finset.mem_filter.mp hJfilter
  obtain ⟨hLfaces, hqLsub⟩ := Finset.mem_filter.mp hLfilter
  have hqJ : q ∈ J := hqJsub (Finset.mem_insert_self q A)
  have hqL : q ∈ L := hqLsub (Finset.mem_insert_self q A)
  obtain ⟨g, hg, hgy⟩ := hyJ
  obtain ⟨h, hh, hhz⟩ := hzL
  have hgJ : (m : ℂ) * τ q + g ∈ faceShiftLattice τ J :=
    faceShiftLattice_add_zsmul τ J hqJ
      (faceShiftLatticeSlice_subset τ J q hg) m
  have hhL : (n : ℂ) * τ q + h ∈ faceShiftLattice τ L :=
    faceShiftLattice_add_zsmul τ L hqL
      (faceShiftLatticeSlice_subset τ L q hh) n
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
    exact (multipleEllipticGammaFace_translate_ne_of_ne τ hτ hQ J L hne
      (hfaces J hJfaces) (hfaces L hLfaces) hgJ hhL) htrans
  subst L
  have hshift :
      (m : ℂ) * τ q + g = (n : ℂ) * τ q + h :=
    faceShiftLattice_translate_injective τ hτ hQ J (hfaces J hJfaces) hgJ hhL htrans
  exact faceShiftLatticeSlice_zsmul_eq τ hQ J q hg hh hshift

set_option maxHeartbeats 3000000 in
set_option synthInstance.maxHeartbeats 1200000 in
theorem multipleEllipticGammaFaceLayer_diffIndepOn_of_deeper
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {S : Set (Finset ι)}
    (hSclosed : ∀ L ∈ S, ∀ p : ι, p ∉ L → insert p L ∈ S)
    (hSfaces : ∀ L ∈ S, 2 ≤ (Lᶜ).card)
    (hdeep : DiffIndepOn ℂ (facePacketUnion τ hτ S))
    (faces : Finset (Finset ι)) (s : ℕ)
    (huniform : ∀ J ∈ faces, J.card = s)
    (dq du : Finset ι → ι)
    (hq : ∀ J ∈ faces, dq J ∉ J) (hu : ∀ J ∈ faces, du J ∉ J)
    (hqu : ∀ J ∈ faces, dq J ≠ du J)
    (hcoface : ∀ J ∈ faces, ∀ p : ι, p ∉ J → insert p J ∈ S)
    (hJS : ∀ J ∈ faces, J ∉ S)
    (hfaces : ∀ J ∈ faces, 2 ≤ (Jᶜ).card) :
    DiffIndepOn ↥(differentialAdjoin ℂ (facePacketUnion τ hτ S))
      (faceStar faces (multipleEllipticGammaFacePacket τ hτ) ∅) := by
  classical
  apply multipleEllipticGammaFaceLayer_diffIndepOn_deeper τ hτ hSclosed
    faces s huniform dq du hq hu
    (fun J hJ => hcoface J hJ (dq J) (hq J hJ))
    (fun J hJ => hcoface J hJ (du J) (hu J hJ)) hJS
  · intro J hJ
    simpa [facePacketPeriods, ellipticGammaSourcePeriods] using
      (linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent
        τ hQ (hqu J hJ))
  · intro J hJ
    exact facePalette_differentialIndependent_of_deeper τ hτ hQ S hSfaces hdeep J
      (hcoface J hJ (dq J) (hq J hJ))
  · intro J hJ
    exact facePacketDisplacementSlice_injective τ hτ hQ J (hq J hJ)
      (hSfaces (insert (dq J) J) (hcoface J hJ (dq J) (hq J hJ)))
  · intro A q _ _ m n y z hy hz heq
    exact faceLayer_star_exponent_eq τ hτ hQ faces hfaces hy hz heq
  · intro A q _ _ t ht n z hz
    obtain ⟨y, hyt, rfl⟩ := hz
    obtain ⟨J, hJfilter, hyJ⟩ :=
      Set.mem_iUnion₂.mp (ht (Finset.mem_coe.mpr hyt))
    obtain ⟨hJfilter', hqJ⟩ := Finset.mem_filter.mp hJfilter
    obtain ⟨hJfaces, -⟩ := Finset.mem_filter.mp hJfilter'
    have hqS' : insert q J ∈ S := hcoface J hJfaces q hqJ
    simpa [meroTranslationPerm_zpow_apply] using
      (differentialAlgebraicOver_offStar_translate_deeper τ hτ J hqJ hqS' n hyJ
        (Finset.mem_coe.mpr hyt))

set_option maxHeartbeats 3000000 in
set_option synthInstance.maxHeartbeats 1200000 in
theorem multipleEllipticGammaFaceLayer_diffIndepOn_of_deeper_auto
    [Nonempty ι]
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {S : Set (Finset ι)}
    (hSclosed : ∀ L ∈ S, ∀ p : ι, p ∉ L → insert p L ∈ S)
    (hSfaces : ∀ L ∈ S, 2 ≤ (Lᶜ).card)
    (hdeep : DiffIndepOn ℂ (facePacketUnion τ hτ S))
    (faces : Finset (Finset ι)) (s : ℕ)
    (huniform : ∀ J ∈ faces, J.card = s)
    (hthree : ∀ J ∈ faces, 3 ≤ (Jᶜ).card)
    (hcoface : ∀ J ∈ faces, ∀ p : ι, p ∉ J → insert p J ∈ S)
    (hJS : ∀ J ∈ faces, J ∉ S) :
    DiffIndepOn ↥(differentialAdjoin ℂ (facePacketUnion τ hτ S))
      (faceStar faces (multipleEllipticGammaFacePacket τ hτ) ∅) := by
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
  exact multipleEllipticGammaFaceLayer_diffIndepOn_of_deeper
    τ hτ hQ hSclosed hSfaces hdeep faces s huniform dq du hq hu hqu hcoface hJS
      (fun J hJ => by
        have := hthree J hJ
        omega)

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem differentialAlgebraicOver_faceCoordinate_of_compl_card_one
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (hι : 2 ≤ Fintype.card ι) (L : Finset ι) (hLcard : (Lᶜ).card = 1) :
    DifferentialAlgebraicOver ℂ
      (multipleEllipticGammaLogDerivFaceMero τ hτ L) := by
  classical
  obtain ⟨a, hLa⟩ := Finset.card_eq_one.mp hLcard
  have haL : a ∉ L := by
    have : a ∈ Lᶜ := by rw [hLa]; simp
    exact Finset.mem_compl.mp this
  have hLpos : 0 < L.card := by
    have htotal := Finset.card_add_card_compl L
    omega
  obtain ⟨b, hbL⟩ := Finset.card_pos.mp hLpos
  have hab : a ≠ b := fun hab => haL (hab ▸ hbL)
  let J := L.erase b
  have haJ : a ∉ J := fun h => haL (Finset.mem_of_mem_erase h)
  have hbJ : b ∉ J := Finset.notMem_erase b L
  have hJ : ∀ i, i ∉ J → i = a ∨ i = b := by
    intro i hiJ
    by_cases hiL : i ∈ L
    · exact Or.inr (by
        by_contra hib
        exact hiJ (Finset.mem_erase.mpr ⟨hib, hiL⟩))
    · have hiLc : i ∈ Lᶜ := Finset.mem_compl.mpr hiL
      rw [hLa] at hiLc
      exact Or.inl (by simpa using hiLc)
  have hJL : insert b J = L := by
    exact Finset.insert_erase hbL
  have hzero : (0 : ℂ) ∈ faceShiftLattice τ J := by
    refine ⟨0, ?_, by simp⟩
    intro i hi
    rfl
  have hface :
      multipleEllipticGammaLogDerivFaceMero τ hτ J ∈
        multipleEllipticGammaFacePacket τ hτ J := by
    refine ⟨0, hzero, ?_⟩
    change addTranslationMeroEquiv 0
      (multipleEllipticGammaLogDerivFaceMero τ hτ J) =
        multipleEllipticGammaLogDerivFaceMero τ hτ J
    rw [addTranslationMeroEquiv_zero_apply]
  have hda := differentialAlgebraicOver_offStar_displacement_bottom τ hτ J
    haJ hbJ hab hJ
    (linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent τ hQ hab)
    hbJ (1 : ℤ) hface
  rw [Int.cast_one, one_mul,
    multipleEllipticGammaLogDerivFaceMero_addTranslation_sub τ hτ J b hbJ,
    hJL] at hda
  exact hda

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem differentialAlgebraicOver_facePacket_of_compl_lt_two
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (hι : 2 ≤ Fintype.card ι) (L : Finset ι) (hLcard : (Lᶜ).card < 2)
    {y : meroField (Set.univ : Set ℂ)}
    (hy : y ∈ multipleEllipticGammaFacePacket τ hτ L) :
    DifferentialAlgebraicOver ℂ y := by
  classical
  obtain ⟨g, -, rfl⟩ := hy
  have hbase : DifferentialAlgebraicOver ℂ
      (multipleEllipticGammaLogDerivFaceMero τ hτ L) := by
    by_cases hzero : (Lᶜ).card = 0
    · have hLuniv : L = Finset.univ := by
        have hc : Lᶜ = ∅ := Finset.card_eq_zero.mp hzero
        ext i
        simp only [Finset.mem_univ, iff_true]
        by_contra hiL
        have hiC : i ∈ Lᶜ := Finset.mem_compl.mpr hiL
        rw [hc] at hiC
        simp at hiC
      let a : ι := Classical.choice (Fintype.card_pos_iff.mp (by omega))
      let J := L.erase a
      have haL : a ∈ L := by rw [hLuniv]; simp
      have haJ : a ∉ J := Finset.notMem_erase a L
      have hJcomp : (Jᶜ).card = 1 := by
        have hJL : insert a J = L := Finset.insert_erase haL
        have hJcard : J.card + 1 = L.card := by
          rw [← Finset.card_insert_of_notMem haJ, hJL]
        have htotalJ := Finset.card_add_card_compl J
        have htotalL := Finset.card_add_card_compl L
        omega
      have hJda :=
        differentialAlgebraicOver_faceCoordinate_of_compl_card_one τ hτ hQ hι J hJcomp
      have hTda :
          DifferentialAlgebraicOver ℂ
            (addTranslationMeroEquiv (τ a)
              (multipleEllipticGammaLogDerivFaceMero τ hτ J)) :=
        (HTGeometry.DifferentialAlgEquiv.differentialAlgebraicOver_map_iff
          (addTranslationMeroDifferentialAlgEquiv (τ a)) _).mpr hJda
      have hdiff := differentialAlgebraicOver_sub hTda hJda
      rw [multipleEllipticGammaLogDerivFaceMero_addTranslation_sub τ hτ J a haJ,
        Finset.insert_erase haL] at hdiff
      exact hdiff
    · have hone : (Lᶜ).card = 1 := by omega
      exact differentialAlgebraicOver_faceCoordinate_of_compl_card_one
        τ hτ hQ hι L hone
  exact (HTGeometry.DifferentialAlgEquiv.differentialAlgebraicOver_map_iff
    (addTranslationMeroDifferentialAlgEquiv g) _).mpr hbase

set_option maxHeartbeats 2500000 in
set_option synthInstance.maxHeartbeats 1200000 in
theorem facePalette_differentialIndependent_of_deeper_with_boundary
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (N B : Set (Finset ι))
    (hNfaces : ∀ L ∈ N, 2 ≤ (Lᶜ).card)
    (hBDA : ∀ L ∈ B, ∀ y ∈ multipleEllipticGammaFacePacket τ hτ L,
      DifferentialAlgebraicOver ℂ y)
    (hdeep : DiffIndepOn ℂ (facePacketUnion τ hτ N))
    (J : Finset ι) {q : ι} (hqN : insert q J ∈ N) (hqB : insert q J ∉ B) :
    DifferentialIndependent
      ↥(differentialAdjoin ℂ
        (facePacketUnion τ hτ (facePacketBaseFamily (N ∪ B) J q)))
      (facePalette τ hτ (insert q J) q) := by
  classical
  let K := insert q J
  let N0 := facePacketUnion τ hτ (facePacketBaseFamily N J q)
  let BB := facePacketUnion τ hτ B
  let P := multipleEllipticGammaFacePacket τ hτ K
  have hfamilyN :=
    facePalette_differentialIndependent_of_deeper τ hτ hQ N hNfaces hdeep J hqN
  have hsetN : DiffIndepOn ↥(differentialAdjoin ℂ N0) P := by
    have hrange := diffIndepOn_range_of_differentialIndependent hfamilyN
    simpa [N0, P, K, range_facePalette τ hτ (insert q J)
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
      facePacketUnion τ hτ (facePacketBaseFamily (N ∪ B) J q) = N0 ∪ BB := by
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
      (↥(multipleEllipticGammaFacePacketSlice τ hτ K q) × ℤ) → P :=
    fun p => ⟨facePalette τ hτ K q p, by
      change facePalette τ hτ K q p ∈
        multipleEllipticGammaFacePacket τ hτ K
      rw [← range_facePalette τ hτ K (Finset.mem_insert_self q J)]
      exact Set.mem_range_self p⟩
  have he : Function.Injective e := by
    intro x y hxy
    apply facePalette_injective τ hτ hQ K (hNfaces K hqN)
      (Finset.mem_insert_self q J)
    exact congrArg (fun z : P => (z : meroField (Set.univ : Set ℂ))) hxy
  have hfamily :=
    (show DifferentialIndependent ↥(differentialAdjoin ℂ (N0 ∪ BB))
      (Subtype.val : P → meroField (Set.univ : Set ℂ)) from hsetUnion).comp e he
  simpa [e, K, P] using hfamily

set_option maxHeartbeats 3000000 in
set_option synthInstance.maxHeartbeats 1200000 in
theorem multipleEllipticGammaFaceLayer_diffIndepOn_with_boundary
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (N B : Set (Finset ι))
    (hSclosed : ∀ L ∈ N ∪ B, ∀ p : ι, p ∉ L → insert p L ∈ N ∪ B)
    (hNfaces : ∀ L ∈ N, 2 ≤ (Lᶜ).card)
    (hBDA : ∀ L ∈ B, ∀ y ∈ multipleEllipticGammaFacePacket τ hτ L,
      DifferentialAlgebraicOver ℂ y)
    (hNB : Disjoint N B)
    (hdeep : DiffIndepOn ℂ (facePacketUnion τ hτ N))
    (faces : Finset (Finset ι)) (s : ℕ)
    (huniform : ∀ J ∈ faces, J.card = s)
    (dq du : Finset ι → ι)
    (hq : ∀ J ∈ faces, dq J ∉ J) (hu : ∀ J ∈ faces, du J ∉ J)
    (hqu : ∀ J ∈ faces, dq J ≠ du J)
    (hcoface : ∀ J ∈ faces, ∀ p : ι, p ∉ J → insert p J ∈ N)
    (hJS : ∀ J ∈ faces, J ∉ N ∪ B)
    (hfaces : ∀ J ∈ faces, 2 ≤ (Jᶜ).card) :
    DiffIndepOn
      ↥(differentialAdjoin ℂ (facePacketUnion τ hτ (N ∪ B)))
      (faceStar faces (multipleEllipticGammaFacePacket τ hτ) ∅) := by
  classical
  apply multipleEllipticGammaFaceLayer_diffIndepOn_deeper τ hτ hSclosed
    faces s huniform dq du hq hu
    (fun J hJ => Or.inl (hcoface J hJ (dq J) (hq J hJ)))
    (fun J hJ => Or.inl (hcoface J hJ (du J) (hu J hJ))) hJS
  · intro J hJ
    simpa [facePacketPeriods, ellipticGammaSourcePeriods] using
      (linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent
        τ hQ (hqu J hJ))
  · intro J hJ
    exact facePalette_differentialIndependent_of_deeper_with_boundary
      τ hτ hQ N B hNfaces hBDA hdeep J
        (hcoface J hJ (dq J) (hq J hJ))
        (fun hB => Set.disjoint_left.mp hNB
          (hcoface J hJ (dq J) (hq J hJ)) hB)
  · intro J hJ
    exact facePacketDisplacementSlice_injective τ hτ hQ J (hq J hJ)
      (hNfaces (insert (dq J) J) (hcoface J hJ (dq J) (hq J hJ)))
  · intro A q _ _ m n y z hy hz heq
    exact faceLayer_star_exponent_eq τ hτ hQ faces hfaces hy hz heq
  · intro A q _ _ t ht n z hz
    obtain ⟨y, hyt, rfl⟩ := hz
    obtain ⟨J, hJfilter, hyJ⟩ :=
      Set.mem_iUnion₂.mp (ht (Finset.mem_coe.mpr hyt))
    obtain ⟨hJfilter', hqJ⟩ := Finset.mem_filter.mp hJfilter
    obtain ⟨hJfaces, -⟩ := Finset.mem_filter.mp hJfilter'
    have hqS' : insert q J ∈ N ∪ B :=
      Or.inl (hcoface J hJfaces q hqJ)
    simpa [meroTranslationPerm_zpow_apply] using
      (differentialAlgebraicOver_offStar_translate_deeper
        τ hτ J hqJ hqS' n hyJ (Finset.mem_coe.mpr hyt))

set_option maxHeartbeats 3000000 in
set_option synthInstance.maxHeartbeats 1200000 in
theorem multipleEllipticGammaFaceLayer_diffIndepOn_with_boundary_auto
    [Nonempty ι]
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (N B : Set (Finset ι))
    (hSclosed : ∀ L ∈ N ∪ B, ∀ p : ι, p ∉ L → insert p L ∈ N ∪ B)
    (hNfaces : ∀ L ∈ N, 2 ≤ (Lᶜ).card)
    (hBDA : ∀ L ∈ B, ∀ y ∈ multipleEllipticGammaFacePacket τ hτ L,
      DifferentialAlgebraicOver ℂ y)
    (hNB : Disjoint N B)
    (hdeep : DiffIndepOn ℂ (facePacketUnion τ hτ N))
    (faces : Finset (Finset ι)) (s : ℕ)
    (huniform : ∀ J ∈ faces, J.card = s)
    (hthree : ∀ J ∈ faces, 3 ≤ (Jᶜ).card)
    (hcoface : ∀ J ∈ faces, ∀ p : ι, p ∉ J → insert p J ∈ N)
    (hJS : ∀ J ∈ faces, J ∉ N ∪ B) :
    DiffIndepOn
      ↥(differentialAdjoin ℂ (facePacketUnion τ hτ (N ∪ B)))
      (faceStar faces (multipleEllipticGammaFacePacket τ hτ) ∅) := by
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
  exact multipleEllipticGammaFaceLayer_diffIndepOn_with_boundary
    τ hτ hQ N B hSclosed hNfaces hBDA hNB hdeep faces s huniform
      dq du hq hu hqu hcoface hJS (fun J hJ => by
        have := hthree J hJ
        omega)

/-- Faces below the hypertranscendental range: zero or one surviving period. -/
def multipleEllipticGammaBoundaryFaces : Set (Finset ι) :=
  {J | (Jᶜ).card < 2}

/-- Nonboundary faces already installed before layer `k`; their survivor count lies in
`[2, k + 1]`. -/
def multipleEllipticGammaDeeperFaces (k : ℕ) : Set (Finset ι) :=
  {J | 2 ≤ (Jᶜ).card ∧ (Jᶜ).card < k + 2}

/-- Layer `k` has exactly `k + 2` surviving periods. -/
def multipleEllipticGammaFaceLayer (k : ℕ) : Finset (Finset ι) :=
  Finset.univ.filter (fun J => (Jᶜ).card = k + 2)

theorem multipleEllipticGammaDeeperFaces_zero :
    multipleEllipticGammaDeeperFaces (ι := ι) 0 = ∅ := by
  ext J
  simp only [multipleEllipticGammaDeeperFaces, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, iff_false]
  omega

theorem multipleEllipticGammaDeeperFaces_succ (k : ℕ) :
    multipleEllipticGammaDeeperFaces (ι := ι) (k + 1) =
      multipleEllipticGammaDeeperFaces (ι := ι) k ∪
        (↑(multipleEllipticGammaFaceLayer (ι := ι) k) : Set (Finset ι)) := by
  ext J
  simp only [multipleEllipticGammaDeeperFaces, multipleEllipticGammaFaceLayer,
    Set.mem_setOf_eq, Set.mem_union, Finset.mem_coe, Finset.mem_filter,
    Finset.mem_univ, true_and]
  omega

set_option maxHeartbeats 1000000 in
theorem face_compl_card_insert_add_one
    (J : Finset ι) {q : ι} (hq : q ∉ J) :
    ((insert q J)ᶜ).card + 1 = (Jᶜ).card := by
  have hinsert := Finset.card_insert_of_notMem hq
  have htotalJ := Finset.card_add_card_compl J
  have htotalInsert := Finset.card_add_card_compl (insert q J)
  omega

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1500000 in
/-- **All proper face packets are jointly differentially independent.**  Under integral period
independence, the union of the external translation packets of every face retaining at least two
periods is differentially independent over the constants. -/
theorem multipleEllipticGammaProperFacePackets_diffIndepOn
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι) :
    DiffIndepOn ℂ
      (facePacketUnion τ hτ {J : Finset ι | 2 ≤ (Jᶜ).card}) := by
  classical
  letI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hboundary :
      ∀ L ∈ multipleEllipticGammaBoundaryFaces (ι := ι),
        ∀ y ∈ multipleEllipticGammaFacePacket τ hτ L,
          DifferentialAlgebraicOver ℂ y := by
    intro L hL y hy
    exact differentialAlgebraicOver_facePacket_of_compl_lt_two
      τ hτ hQ hι L hL hy
  have hind : ∀ k, DiffIndepOn ℂ
      (facePacketUnion τ hτ (multipleEllipticGammaDeeperFaces (ι := ι) k)) := by
    intro k
    induction k with
    | zero =>
        rw [multipleEllipticGammaDeeperFaces_zero, facePacketUnion_empty]
        exact diffIndepOn_empty
    | succ k ih =>
        let N := multipleEllipticGammaDeeperFaces (ι := ι) k
        let B := multipleEllipticGammaBoundaryFaces (ι := ι)
        let faces := multipleEllipticGammaFaceLayer (ι := ι) k
        have hNfaces : ∀ L ∈ N, 2 ≤ (Lᶜ).card := by
          intro L hL
          exact hL.1
        have hNB : Disjoint N B := by
          rw [Set.disjoint_left]
          intro L hLN hLB
          exact (not_lt_of_ge hLN.1) hLB
        have hSclosed :
            ∀ L ∈ N ∪ B, ∀ p : ι, p ∉ L → insert p L ∈ N ∪ B := by
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
            ∀ L ∈ B, ∀ y ∈ multipleEllipticGammaFacePacket τ hτ L,
              DifferentialAlgebraicOver ℂ y := hboundary
        have hBUnionDA :
            ∀ y ∈ facePacketUnion τ hτ B,
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
              (facePacketUnion τ hτ (N ∪ B)))
            (facePacketUnion τ hτ (↑faces : Set (Finset ι))) := by
          rw [← faceStar_empty_eq_facePacketUnion]
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
            have hNempty : N = ∅ := by
              exact multipleEllipticGammaDeeperFaces_zero
            rw [hNempty, Set.empty_union]
            exact multipleEllipticGammaFaceStar_diffIndepOn_bottom_daExtension
              τ hτ hQ faces (Fintype.card ι - 2)
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
            have hJS : ∀ J ∈ faces, J ∉ N ∪ B := by
              intro J hJ hmem
              have hcomp : (Jᶜ).card = k + 2 := by
                simpa [faces, multipleEllipticGammaFaceLayer] using hJ
              rcases hmem with hJN | hJB
              · exact (ne_of_lt hJN.2) hcomp
              · change (Jᶜ).card < 2 at hJB
                omega
            exact multipleEllipticGammaFaceLayer_diffIndepOn_with_boundary_auto
              τ hτ hQ N B hSclosed hNfaces hBDA hNB ih faces
                (Fintype.card ι - (k + 2)) huniform hthree hcoface hJS
        let NG := facePacketUnion τ hτ N
        let BG := facePacketUnion τ hτ B
        let I := facePacketUnion τ hτ (↑faces : Set (Finset ι))
        have hlayerUnion : DiffIndepOn
            ↥(differentialAdjoin ℂ (NG ∪ BG)) I := by
          rw [← facePacketUnion_union]
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
        exact facePacketUnion_diffIndepOn_union τ hτ N
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



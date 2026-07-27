import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaGenericStructuralUniversalityLaw

open scoped BigOperators
open Finset

noncomputable section

namespace GaloisForLFunctions

open Bottcher HTGeometry
open MatroidGluing MatroidGluing.Rank

attribute [local instance] facePacketMeroDecidableEq

attribute [local instance] ellipticGammaStructuralGeneratorRestrictedDifferential
  ellipticGammaStructuralGeneratorDifferentialAlgebra ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 3000000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem faceDifferenceCube_ne_of_distinct_bottom_faces
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (K M : Finset ι) (hKM : K ≠ M)
    {a b : ι} (haK : a ∉ K) (hbK : b ∉ K) (hab : a ≠ b)
    (hK : ∀ i, i ∉ K → i = a ∨ i = b)
    {c d : ι} (hcM : c ∉ M) (hdM : d ∉ M) (hcd : c ≠ d)
    (hM : ∀ i, i ∉ M → i = c ∨ i = d)
    (V W : Finset ι) (hVK : V ⊆ K) (hWM : W ⊆ M)
    {g h : ℂ} (hg : g ∈ faceShiftLattice τ K) (hh : h ∈ faceShiftLattice τ M) :
    faceDifferenceCube τ V g
        (multipleEllipticGammaLogDerivFaceMero τ hτ K) ≠
      faceDifferenceCube τ W h
        (multipleEllipticGammaLogDerivFaceMero τ hτ M) := by
  classical
  let faces : Finset (Finset ι) := {K, M}
  let P := faceStar faces (multipleEllipticGammaFacePacket τ hτ) ∅
  let ΨK := multipleEllipticGammaLogDerivFaceMero τ hτ K
  let ΨM := multipleEllipticGammaLogDerivFaceMero τ hτ M
  have hbottom : ∀ J ∈ faces, ∃ p q : ι, p ∉ J ∧ q ∉ J ∧ p ≠ q ∧
      ∀ i, i ∉ J → i = p ∨ i = q := by
    intro J hJ
    simp only [faces, Finset.mem_insert, Finset.mem_singleton] at hJ
    rcases hJ with rfl | rfl
    · exact ⟨a, b, haK, hbK, hab, hK⟩
    · exact ⟨c, d, hcM, hdM, hcd, hM⟩
  have hdiff : DiffIndepOn ℂ P :=
    multipleEllipticGammaFaceStar_diffIndepOn_bottom_family τ hτ hQ faces hbottom
  have hlin : LinearIndependent ℂ (Subtype.val : P →
      meroField (Set.univ : Set ℂ)) :=
    (show DifferentialIndependent ℂ (Subtype.val : P →
      meroField (Set.univ : Set ℂ)) from hdiff).algebraicIndependent.linearIndependent
  have hpacketK :
      multipleEllipticGammaFacePacket τ hτ K ⊆ P := by
    intro y hy
    exact Set.mem_iUnion₂.mpr ⟨K, Finset.mem_filter.mpr ⟨by simp [faces], by simp⟩, hy⟩
  have hpacketM :
      multipleEllipticGammaFacePacket τ hτ M ⊆ P := by
    intro y hy
    exact Set.mem_iUnion₂.mpr ⟨M, Finset.mem_filter.mpr ⟨by simp [faces], by simp⟩, hy⟩
  let i0 : P :=
    ⟨addTranslationMeroEquiv g ΨK, hpacketK ⟨g, hg, rfl⟩⟩
  let S0 : Submodule ℂ (meroField (Set.univ : Set ℂ)) :=
    Submodule.span ℂ (Subtype.val '' (Set.univ \ ({i0} : Set P)))
  let rawK : Finset ι → meroField (Set.univ : Set ℂ) := fun E =>
    (-1 : meroField (Set.univ : Set ℂ)) ^ (V.card - E.card) *
      addTranslationMeroEquiv (g + ∑ i ∈ E, τ i) ΨK
  let rawM : Finset ι → meroField (Set.univ : Set ℂ) := fun E =>
    (-1 : meroField (Set.univ : Set ℂ)) ^ (W.card - E.card) *
      addTranslationMeroEquiv (h + ∑ i ∈ E, τ i) ΨM
  have hrestK :
      ∑ E ∈ V.powerset.erase ∅, rawK E ∈ S0 := by
    apply Submodule.sum_mem
    intro E hE
    have hEV : E ⊆ V :=
      Finset.mem_powerset.mp (Finset.mem_of_mem_erase hE)
    have hEK : E ⊆ K := fun i hi => hVK (hEV hi)
    have hgE : g + ∑ i ∈ E, τ i ∈ faceShiftLattice τ K :=
      faceShiftLattice_add_subsetSum τ K E hEK hg
    let iE : P :=
      ⟨addTranslationMeroEquiv (g + ∑ i ∈ E, τ i) ΨK,
        hpacketK ⟨g + ∑ i ∈ E, τ i, hgE, rfl⟩⟩
    have hEne : E ≠ ∅ := Finset.ne_of_mem_erase hE
    have hiE_ne : iE ≠ i0 := by
      intro hi
      have hfun := congrArg (fun x : P => (x : meroField (Set.univ : Set ℂ))) hi
      have hperiods :=
        linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent τ hQ hab
      have hshift :
          g + ∑ i ∈ E, τ i = g :=
        faceShiftLattice_translate_injective_bottom τ hτ hQ K haK hbK hab hK hperiods
          hgE hg (by simpa [iE, i0, ΨK] using hfun)
      apply hEne
      apply periodSubsetSum_injective τ hQ
      have hshift' :
          g + ∑ i ∈ E, τ i = g + 0 := by simpa using hshift
      exact add_left_cancel hshift'
    have hiE_mem : (iE : meroField (Set.univ : Set ℂ)) ∈ S0 := by
      apply Submodule.subset_span
      exact ⟨iE, ⟨Set.mem_univ _, by simpa using hiE_ne⟩, rfl⟩
    have hsmul := S0.smul_mem ((-1 : ℂ) ^ (V.card - E.card)) hiE_mem
    simpa [rawK, iE, ΨK, Algebra.smul_def] using hsmul
  have hallM :
      ∑ E ∈ W.powerset, rawM E ∈ S0 := by
    apply Submodule.sum_mem
    intro E hE
    have hEW : E ⊆ W := Finset.mem_powerset.mp hE
    have hEM : E ⊆ M := fun i hi => hWM (hEW hi)
    have hhE : h + ∑ i ∈ E, τ i ∈ faceShiftLattice τ M :=
      faceShiftLattice_add_subsetSum τ M E hEM hh
    let iE : P :=
      ⟨addTranslationMeroEquiv (h + ∑ i ∈ E, τ i) ΨM,
        hpacketM ⟨h + ∑ i ∈ E, τ i, hhE, rfl⟩⟩
    have hiE_ne : iE ≠ i0 := by
      intro hi
      have hfun := congrArg (fun x : P => (x : meroField (Set.univ : Set ℂ))) hi
      have hperiodsK :=
        linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent τ hQ hab
      have hperiodsM :=
        linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent τ hQ hcd
      have hcross :
          addTranslationMeroEquiv g ΨK ≠
            addTranslationMeroEquiv (h + ∑ i ∈ E, τ i) ΨM := by
        rcases exists_separating_parameter_of_ne hKM with
          ⟨x, hxK, hxM⟩ | ⟨x, hxM, hxK⟩
        · rcases hK x hxK with rfl | rfl
          · exact multipleEllipticGammaFace_translate_ne_bottom τ hτ hQ K M
              haK hbK hab hK hcM hdM hcd hM hperiodsK hperiodsM
              (ne_of_mem_of_not_mem hxM hcM) (ne_of_mem_of_not_mem hxM hdM)
              g (h + ∑ i ∈ E, τ i)
          · exact multipleEllipticGammaFace_translate_ne_bottom τ hτ hQ K M
              hbK haK hab.symm (fun i hi => (hK i hi).symm)
              hcM hdM hcd hM
              (linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent
                τ hQ hab.symm)
              hperiodsM (ne_of_mem_of_not_mem hxM hcM)
              (ne_of_mem_of_not_mem hxM hdM) g (h + ∑ i ∈ E, τ i)
        · rcases hM x hxM with rfl | rfl
          · exact (multipleEllipticGammaFace_translate_ne_bottom τ hτ hQ M K
              hcM hdM hcd hM haK hbK hab hK hperiodsM hperiodsK
              (ne_of_mem_of_not_mem hxK haK) (ne_of_mem_of_not_mem hxK hbK)
              (h + ∑ i ∈ E, τ i) g).symm
          · exact (multipleEllipticGammaFace_translate_ne_bottom τ hτ hQ M K
              hdM hcM hcd.symm (fun i hi => (hM i hi).symm)
              haK hbK hab hK
              (linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent
                τ hQ hcd.symm)
              hperiodsK (ne_of_mem_of_not_mem hxK haK)
              (ne_of_mem_of_not_mem hxK hbK) (h + ∑ i ∈ E, τ i) g).symm
      exact hcross (by simpa [iE, i0, ΨK, ΨM] using hfun.symm)
    have hiE_mem : (iE : meroField (Set.univ : Set ℂ)) ∈ S0 := by
      apply Submodule.subset_span
      exact ⟨iE, ⟨Set.mem_univ _, by simpa using hiE_ne⟩, rfl⟩
    have hsmul := S0.smul_mem ((-1 : ℂ) ^ (W.card - E.card)) hiE_mem
    simpa [rawM, iE, ΨM, Algebra.smul_def] using hsmul
  intro heq
  have hleft :
      (∑ E ∈ V.powerset.erase ∅, rawK E) + rawK ∅ =
        faceDifferenceCube τ V g ΨK := by
    rw [faceDifferenceCube]
    exact Finset.sum_erase_add V.powerset rawK (by simp)
  have hraw0 :
      rawK ∅ =
        (∑ E ∈ W.powerset, rawM E) -
          ∑ E ∈ V.powerset.erase ∅, rawK E := by
    have heq' :
        faceDifferenceCube τ V g ΨK =
          faceDifferenceCube τ W h ΨM := by
      simpa [ΨK, ΨM] using heq
    rw [← hleft] at heq'
    rw [faceDifferenceCube] at heq'
    change
      (∑ E ∈ V.powerset.erase ∅, rawK E) + rawK ∅ =
        ∑ E ∈ W.powerset, rawM E at heq'
    linear_combination heq'
  have hraw0_mem : rawK ∅ ∈ S0 := by
    rw [hraw0]
    exact S0.sub_mem hallM hrestK
  have hsmul_mem :
      ((-1 : ℂ) ^ V.card) •
          (i0 : meroField (Set.univ : Set ℂ)) ∈ S0 := by
    simpa [rawK, i0, ΨK, Algebra.smul_def] using hraw0_mem
  have hcoeff : (-1 : ℂ) ^ V.card ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hi0_mem : (i0 : meroField (Set.univ : Set ℂ)) ∈ S0 :=
    (S0.smul_mem_iff hcoeff).mp hsmul_mem
  exact (linearIndependent_iff_notMem_span.mp hlin i0) hi0_mem

omit [Fintype ι] in
theorem exists_compatible_two_subsets_of_incomparable
    (S T : Finset ι) (hS : 2 ≤ S.card) (hT : 2 ≤ T.card)
    (hST : ¬ S ⊆ T) (hTS : ¬ T ⊆ S) :
    ∃ A B : Finset ι,
      A ⊆ S ∧ B ⊆ T ∧ A.card = 2 ∧ B.card = 2 ∧ A ≠ B ∧
        A ∩ T = B ∩ S := by
  classical
  obtain ⟨x, hxS, hxT⟩ := Finset.not_subset.mp hST
  obtain ⟨y, hyT, hyS⟩ := Finset.not_subset.mp hTS
  by_cases hC : (S ∩ T).Nonempty
  · rcases hC with ⟨c, hc⟩
    have hcS : c ∈ S := (Finset.mem_inter.mp hc).1
    have hcT : c ∈ T := (Finset.mem_inter.mp hc).2
    refine ⟨{c, x}, {c, y}, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact hcS
      · exact hxS
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact hcT
      · exact hyT
    · simp [ne_of_mem_of_not_mem hcT hxT]
    · simp [ne_of_mem_of_not_mem hcS hyS]
    · intro heq
      have hxy : x ∈ ({c, y} : Finset ι) := by
        rw [← heq]
        simp
      rcases Finset.mem_insert.mp hxy with hxc | hxy
      · exact hxT (hxc ▸ hcT)
      · have hxy' : x = y := by simpa using hxy
        exact hxT (hxy' ▸ hyT)
    · ext i
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hic | hix, hiT⟩
        · exact ⟨Or.inl hic, hic ▸ hcS⟩
        · exact False.elim (hxT (hix ▸ hiT))
      · rintro ⟨hic | hiy, hiS⟩
        · exact ⟨Or.inl hic, hic ▸ hcT⟩
        · exact False.elim (hyS (hiy ▸ hiS))
  · obtain ⟨A, hAS, hAcard⟩ := Finset.exists_subset_card_eq hS
    obtain ⟨B, hBT, hBcard⟩ := Finset.exists_subset_card_eq hT
    have hdisj : Disjoint S T := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      exact Finset.not_nonempty_iff_eq_empty.mp hC
    have hAint : A ∩ T = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.mp (hdisj.mono hAS (fun _ h => h))
    have hBint : B ∩ S = ∅ := by
      rw [Finset.inter_comm]
      exact Finset.disjoint_iff_inter_eq_empty.mp (hdisj.mono (fun _ h => h) hBT)
    refine ⟨A, B, hAS, hBT, hAcard, hBcard, ?_, hAint.trans hBint.symm⟩
    intro hAB
    obtain ⟨a, haA⟩ : A.Nonempty := Finset.card_pos.mp (by omega)
    exact Finset.disjoint_left.mp hdisj (hAS haA) (hBT (hAB ▸ haA))

set_option maxHeartbeats 3000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **Complete face-packet disjointness.** External-lattice translates of any two distinct deletion
faces retaining at least two periods are unequal. -/
theorem multipleEllipticGammaFace_translate_ne_of_ne
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (J L : Finset ι) (hJLne : J ≠ L)
    (hJcard : 2 ≤ (Jᶜ).card) (hLcard : 2 ≤ (Lᶜ).card)
    {g h : ℂ} (hg : g ∈ faceShiftLattice τ J) (hh : h ∈ faceShiftLattice τ L) :
    addTranslationMeroEquiv g
        (multipleEllipticGammaLogDerivFaceMero τ hτ J) ≠
      addTranslationMeroEquiv h
        (multipleEllipticGammaLogDerivFaceMero τ hτ L) := by
  classical
  by_cases hJL : J ⊆ L
  · exact multipleEllipticGammaFace_translate_ne_of_ssubset
      τ hτ hQ J L hJL hJLne hLcard hg hh
  by_cases hLJ : L ⊆ J
  · exact (multipleEllipticGammaFace_translate_ne_of_ssubset
      τ hτ hQ L J hLJ hJLne.symm hJcard hh hg).symm
  let S := Jᶜ
  let T := Lᶜ
  have hST : ¬ S ⊆ T := by
    intro hsub
    apply hLJ
    intro i hiL
    by_contra hiJ
    have hiS : i ∈ S := by simpa [S] using hiJ
    have hiT := hsub hiS
    exact (Finset.mem_compl.mp hiT) hiL
  have hTS : ¬ T ⊆ S := by
    intro hsub
    apply hJL
    intro i hiJ
    by_contra hiL
    have hiT : i ∈ T := by simpa [T] using hiL
    have hiS := hsub hiT
    exact (Finset.mem_compl.mp hiS) hiJ
  obtain ⟨A, B, hAS, hBT, hAcard, hBcard, hAB, hcompat⟩ :=
    exists_compatible_two_subsets_of_incomparable S T hJcard hLcard hST hTS
  obtain ⟨a, b, hab, hA⟩ := Finset.card_eq_two.mp hAcard
  obtain ⟨c, d, hcd, hB⟩ := Finset.card_eq_two.mp hBcard
  let K := Aᶜ
  let M := Bᶜ
  let U := S \ A
  let U' := T \ B
  let V := U' \ U
  let W := U \ U'
  have hJK : J ⊆ K := by
    intro i hiJ
    change i ∈ Aᶜ
    rw [Finset.mem_compl]
    intro hiA
    exact (Finset.mem_compl.mp (hAS hiA)) hiJ
  have hLM : L ⊆ M := by
    intro i hiL
    change i ∈ Bᶜ
    rw [Finset.mem_compl]
    intro hiB
    exact (Finset.mem_compl.mp (hBT hiB)) hiL
  have hJU : J ∪ U = K := by
    ext i
    simp only [U, S, K, Finset.mem_union, Finset.mem_sdiff, Finset.mem_compl]
    constructor
    · rintro (hiJ | ⟨-, hiA⟩)
      · intro hiA
        exact (Finset.mem_compl.mp (hAS hiA)) hiJ
      · exact hiA
    · intro hiA
      by_cases hiJ : i ∈ J
      · exact Or.inl hiJ
      · exact Or.inr ⟨hiJ, hiA⟩
  have hLU' : L ∪ U' = M := by
    ext i
    simp only [U', T, M, Finset.mem_union, Finset.mem_sdiff, Finset.mem_compl]
    constructor
    · rintro (hiL | ⟨-, hiB⟩)
      · intro hiB
        exact (Finset.mem_compl.mp (hBT hiB)) hiL
      · exact hiB
    · intro hiB
      by_cases hiL : i ∈ L
      · exact Or.inl hiL
      · exact Or.inr ⟨hiL, hiB⟩
  have hUJ : Disjoint U J := by
    rw [Finset.disjoint_left]
    intro i hiU hiJ
    exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp hiU).1) hiJ
  have hU'L : Disjoint U' L := by
    rw [Finset.disjoint_left]
    intro i hiU hiL
    exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp hiU).1) hiL
  have hUV : Disjoint U V := by
    rw [Finset.disjoint_left]
    intro i hiU hiV
    exact (Finset.mem_sdiff.mp hiV).2 hiU
  have hU'W : Disjoint U' W := by
    rw [Finset.disjoint_left]
    intro i hiU hiW
    exact (Finset.mem_sdiff.mp hiW).2 hiU
  have htotalLeft : U ∪ V = U ∪ U' := by
    ext i
    simp [V]
  have htotalRight : U' ∪ W = U ∪ U' := by
    ext i
    simp [W, or_comm]
  have hVK : V ⊆ K := by
    intro i hiV
    change i ∈ Aᶜ
    rw [Finset.mem_compl]
    intro hiA
    have hiU' := (Finset.mem_sdiff.mp hiV).1
    have hiT := (Finset.mem_sdiff.mp hiU').1
    have hiB := (Finset.mem_sdiff.mp hiU').2
    have hiS := hAS hiA
    have hiAT : i ∈ A ∩ T := Finset.mem_inter.mpr ⟨hiA, hiT⟩
    have hiBS : i ∈ B ∩ S := hcompat ▸ hiAT
    exact hiB (Finset.mem_inter.mp hiBS).1
  have hWM : W ⊆ M := by
    intro i hiW
    change i ∈ Bᶜ
    rw [Finset.mem_compl]
    intro hiB
    have hiU := (Finset.mem_sdiff.mp hiW).1
    have hiS := (Finset.mem_sdiff.mp hiU).1
    have hiA := (Finset.mem_sdiff.mp hiU).2
    have hiT := hBT hiB
    have hiBS : i ∈ B ∩ S := Finset.mem_inter.mpr ⟨hiB, hiS⟩
    have hiAT : i ∈ A ∩ T := hcompat.symm ▸ hiBS
    exact hiA (Finset.mem_inter.mp hiAT).1
  have hKM : K ≠ M := by
    intro h
    apply hAB
    have hc := congrArg (fun X : Finset ι => Xᶜ) h
    simpa [K, M] using hc
  have haK : a ∉ K := by
    change a ∉ Aᶜ
    rw [hA]
    simp
  have hbK : b ∉ K := by
    change b ∉ Aᶜ
    rw [hA]
    simp
  have hK : ∀ i, i ∉ K → i = a ∨ i = b := by
    intro i hi
    have hiA : i ∈ A := by simpa [K] using hi
    rw [hA] at hiA
    simpa using hiA
  have hcM : c ∉ M := by
    change c ∉ Bᶜ
    rw [hB]
    simp
  have hdM : d ∉ M := by
    change d ∉ Bᶜ
    rw [hB]
    simp
  have hM : ∀ i, i ∉ M → i = c ∨ i = d := by
    intro i hi
    have hiB : i ∈ B := by simpa [M] using hi
    rw [hB] at hiB
    simpa using hiB
  have hgK : g ∈ faceShiftLattice τ K :=
    faceShiftLattice_mono τ hJK hg
  have hhM : h ∈ faceShiftLattice τ M :=
    faceShiftLattice_mono τ hLM hh
  intro heq
  have hcube := congrArg
    (fun f : meroField (Set.univ : Set ℂ) =>
      faceDifferenceCube τ (U ∪ U') 0 f) heq
  change faceDifferenceCube τ (U ∪ U') 0
      (addTranslationMeroEquiv g
        (multipleEllipticGammaLogDerivFaceMero τ hτ J)) =
    faceDifferenceCube τ (U ∪ U') 0
      (addTranslationMeroEquiv h
        (multipleEllipticGammaLogDerivFaceMero τ hτ L)) at hcube
  rw [faceDifferenceCube_translate, faceDifferenceCube_translate] at hcube
  simp only [zero_add] at hcube
  have hleft :
      faceDifferenceCube τ (U ∪ U') g
          (multipleEllipticGammaLogDerivFaceMero τ hτ J) =
        faceDifferenceCube τ V g
          (multipleEllipticGammaLogDerivFaceMero τ hτ K) := by
    rw [← htotalLeft]
    rw [faceDifferenceCube_face_partition τ hτ J U V hUJ hUV g, hJU]
  have hright :
      faceDifferenceCube τ (U ∪ U') h
          (multipleEllipticGammaLogDerivFaceMero τ hτ L) =
        faceDifferenceCube τ W h
          (multipleEllipticGammaLogDerivFaceMero τ hτ M) := by
    rw [← htotalRight]
    rw [faceDifferenceCube_face_partition τ hτ L U' W hU'L hU'W h, hLU']
  rw [hleft, hright] at hcube
  exact (faceDifferenceCube_ne_of_distinct_bottom_faces τ hτ hQ K M hKM
    haK hbK hab hK hcM hdM hcd hM V W hVK hWM hgK hhM) hcube

end GaloisForLFunctions

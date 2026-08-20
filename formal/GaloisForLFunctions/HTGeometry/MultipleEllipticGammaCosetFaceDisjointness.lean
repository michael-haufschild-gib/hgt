import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaCosetBottomStar
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaFacePacketDisjointness

/-!
# Labelled face-packet disjointness

Two distinct deletion faces have no common labelled translate.  The proof is the unlabelled one:
apply the difference cube of the complementary directions to both sides, which turns each side into
a cube over a bottom face, and use linear independence of the labelled bottom star.

The coset label enters only through the labelled bottom layer, which is already jointly
independent, and through the faithful labelling of the labelled shift set.

* **`cosetFaceShiftSet_mono`**, **`cosetFaceShiftSet_add_subsetSum`** — shift-set closure;
* **`cosetFaceDifferenceCube_ne_of_distinct_bottom_faces`** — the cross-bottom-face inequality;
* **`cosetFace_translate_ne_of_ne`** — complete labelled face-packet disjointness.
-/

open scoped BigOperators Differential
open Finset Set

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

omit [DecidableEq ι] in
theorem cosetFaceShiftSet_mono (τ : ι → ℂ) (A : Set ℂ) {J J' : Finset ι} (hJ : J ⊆ J') :
    cosetFaceShiftSet τ A J ⊆ cosetFaceShiftSet τ A J' := by
  rintro g ⟨α, hα, u, hu, rfl⟩
  exact ⟨α, hα, u, faceShiftLattice_mono τ hJ hu, rfl⟩

theorem cosetFaceShiftSet_add_subsetSum
    (τ : ι → ℂ) (A : Set ℂ) (K E : Finset ι) (hEK : E ⊆ K)
    {g : ℂ} (hg : g ∈ cosetFaceShiftSet τ A K) :
    g + ∑ i ∈ E, τ i ∈ cosetFaceShiftSet τ A K := by
  obtain ⟨α, hα, u, hu, rfl⟩ := hg
  exact ⟨α, hα, u + ∑ i ∈ E, τ i, faceShiftLattice_add_subsetSum τ K E hEK hu, by ring⟩

set_option maxHeartbeats 3000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **Difference cubes over distinct labelled bottom faces never agree.** -/
theorem cosetFaceDifferenceCube_ne_of_distinct_bottom_faces
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {A : Set ℂ} (hA : CosetSeparated τ A)
    (K M : Finset ι) (hKM : K ≠ M)
    {a b : ι} (haK : a ∉ K) (hbK : b ∉ K) (hab : a ≠ b)
    (hK : ∀ i, i ∉ K → i = a ∨ i = b)
    {c d : ι} (hcM : c ∉ M) (hdM : d ∉ M) (hcd : c ≠ d)
    (hM : ∀ i, i ∉ M → i = c ∨ i = d)
    (V W : Finset ι) (hVK : V ⊆ K) (hWM : W ⊆ M)
    {g h : ℂ} (hg : g ∈ cosetFaceShiftSet τ A K) (hh : h ∈ cosetFaceShiftSet τ A M) :
    faceDifferenceCube τ V g
        (multipleEllipticGammaLogDerivFaceMero τ hτ K) ≠
      faceDifferenceCube τ W h
        (multipleEllipticGammaLogDerivFaceMero τ hτ M) := by
  classical
  let faces : Finset (Finset ι) := {K, M}
  let P := faceStar faces (cosetFacePacket τ hτ A) ∅
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
    cosetFaceStar_diffIndepOn_bottom_family τ hτ hQ hA faces hbottom
  have hlin : LinearIndependent ℂ (Subtype.val : P →
      meroField (Set.univ : Set ℂ)) :=
    (show DifferentialIndependent ℂ (Subtype.val : P →
      meroField (Set.univ : Set ℂ)) from hdiff).algebraicIndependent.linearIndependent
  have hpacketK : cosetFacePacket τ hτ A K ⊆ P := by
    intro y hy
    exact Set.mem_iUnion₂.mpr ⟨K, Finset.mem_filter.mpr ⟨by simp [faces], by simp⟩, hy⟩
  have hpacketM : cosetFacePacket τ hτ A M ⊆ P := by
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
    have hgE : g + ∑ i ∈ E, τ i ∈ cosetFaceShiftSet τ A K :=
      cosetFaceShiftSet_add_subsetSum τ A K E hEK hg
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
        cosetFaceShiftSet_translate_injective_bottom τ hτ hQ hA K haK hbK hab hK hperiods
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
    have hhE : h + ∑ i ∈ E, τ i ∈ cosetFaceShiftSet τ A M :=
      cosetFaceShiftSet_add_subsetSum τ A M E hEM hh
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

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- A labelled translate of a bottom face coordinate is never a difference cube of another
labelled translate, once one cube term is already known to differ. -/
theorem cosetBottom_translate_ne_faceDifferenceCube_of_term_ne
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {A : Set ℂ} (hA : CosetSeparated τ A)
    (K : Finset ι) {a b : ι}
    (haK : a ∉ K) (hbK : b ∉ K) (hab : a ≠ b)
    (hK : ∀ i, i ∉ K → i = a ∨ i = b)
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ a) (τ b)))
    (V : Finset ι) (hVK : V ⊆ K)
    {g h : ℂ} (hg : g ∈ cosetFaceShiftSet τ A K) (hh : h ∈ cosetFaceShiftSet τ A K)
    (E0 : Finset ι) (hE0 : E0 ∈ V.powerset)
    (hne :
      addTranslationMeroEquiv (h + ∑ i ∈ E0, τ i)
          (multipleEllipticGammaLogDerivFaceMero τ hτ K) ≠
        addTranslationMeroEquiv g
          (multipleEllipticGammaLogDerivFaceMero τ hτ K)) :
    addTranslationMeroEquiv g
        (multipleEllipticGammaLogDerivFaceMero τ hτ K) ≠
      faceDifferenceCube τ V h
        (multipleEllipticGammaLogDerivFaceMero τ hτ K) := by
  classical
  let P := cosetFacePacket τ hτ A K
  let Ψ := multipleEllipticGammaLogDerivFaceMero τ hτ K
  have hE0K : E0 ⊆ K :=
    fun i hi => hVK (Finset.mem_powerset.mp hE0 hi)
  have hhE0 : h + ∑ i ∈ E0, τ i ∈ cosetFaceShiftSet τ A K :=
    cosetFaceShiftSet_add_subsetSum τ A K E0 hE0K hh
  let i0 : P :=
    ⟨addTranslationMeroEquiv (h + ∑ i ∈ E0, τ i) Ψ,
      ⟨h + ∑ i ∈ E0, τ i, hhE0, rfl⟩⟩
  let ig : P :=
    ⟨addTranslationMeroEquiv g Ψ, ⟨g, hg, rfl⟩⟩
  have hdiff : DiffIndepOn ℂ P :=
    diffIndepOn_of_diffIndepOn_differentialAdjoin
      (cosetFacePacket_diffIndepOn_bottom τ hτ hQ hA K
        haK hbK hab hK hperiods
        (G := (∅ : Set (meroField (Set.univ : Set ℂ)))) (by simp))
  have hlin : LinearIndependent ℂ (Subtype.val : P →
      meroField (Set.univ : Set ℂ)) :=
    (show DifferentialIndependent ℂ (Subtype.val : P →
      meroField (Set.univ : Set ℂ)) from hdiff).algebraicIndependent.linearIndependent
  let S0 : Submodule ℂ (meroField (Set.univ : Set ℂ)) :=
    Submodule.span ℂ (Subtype.val '' (Set.univ \ ({i0} : Set P)))
  have hig_ne : ig ≠ i0 := by
    intro heq
    apply hne
    exact (congrArg (fun x : P => (x : meroField (Set.univ : Set ℂ))) heq).symm
  have hig_mem : (ig : meroField (Set.univ : Set ℂ)) ∈ S0 := by
    apply Submodule.subset_span
    exact ⟨ig, ⟨Set.mem_univ _, by simpa using hig_ne⟩, rfl⟩
  let raw : Finset ι → meroField (Set.univ : Set ℂ) := fun E =>
    (-1 : meroField (Set.univ : Set ℂ)) ^ (V.card - E.card) *
      addTranslationMeroEquiv (h + ∑ i ∈ E, τ i) Ψ
  have hrest_mem :
      ∑ E ∈ V.powerset.erase E0, raw E ∈ S0 := by
    apply Submodule.sum_mem
    intro E hE
    have hEV : E ⊆ V :=
      Finset.mem_powerset.mp (Finset.mem_of_mem_erase hE)
    have hEK : E ⊆ K := fun i hi => hVK (hEV hi)
    have hhE : h + ∑ i ∈ E, τ i ∈ cosetFaceShiftSet τ A K :=
      cosetFaceShiftSet_add_subsetSum τ A K E hEK hh
    let iE : P :=
      ⟨addTranslationMeroEquiv (h + ∑ i ∈ E, τ i) Ψ,
        ⟨h + ∑ i ∈ E, τ i, hhE, rfl⟩⟩
    have hEE0 : E ≠ E0 := Finset.ne_of_mem_erase hE
    have hiE_ne : iE ≠ i0 := by
      intro hi
      have hfun := congrArg (fun x : P => (x : meroField (Set.univ : Set ℂ))) hi
      have hshift :
          h + ∑ i ∈ E, τ i = h + ∑ i ∈ E0, τ i :=
        cosetFaceShiftSet_translate_injective_bottom τ hτ hQ hA K haK hbK hab hK hperiods
          hhE hhE0 hfun
      apply hEE0
      apply periodSubsetSum_injective τ hQ
      exact add_left_cancel hshift
    have hiE_mem : (iE : meroField (Set.univ : Set ℂ)) ∈ S0 := by
      apply Submodule.subset_span
      exact ⟨iE, ⟨Set.mem_univ _, by simpa using hiE_ne⟩, rfl⟩
    have hsmul := S0.smul_mem ((-1 : ℂ) ^ (V.card - E.card)) hiE_mem
    simpa [raw, iE, Ψ, Algebra.smul_def] using hsmul
  intro heq
  have hsum :
      (∑ E ∈ V.powerset.erase E0, raw E) + raw E0 =
        faceDifferenceCube τ V h Ψ := by
    rw [faceDifferenceCube]
    exact Finset.sum_erase_add V.powerset raw hE0
  have hdecomp :
      (ig : meroField (Set.univ : Set ℂ)) =
        (∑ E ∈ V.powerset.erase E0, raw E) + raw E0 := by
    exact heq.trans hsum.symm
  have hraw_mem : raw E0 ∈ S0 := by
    have hraw :
        raw E0 = (ig : meroField (Set.univ : Set ℂ)) -
          ∑ E ∈ V.powerset.erase E0, raw E := by
      rw [hdecomp]
      abel
    rw [hraw]
    exact S0.sub_mem hig_mem hrest_mem
  have hsmul_mem :
      ((-1 : ℂ) ^ (V.card - E0.card)) •
          (i0 : meroField (Set.univ : Set ℂ)) ∈ S0 := by
    simpa [raw, i0, Ψ, Algebra.smul_def] using hraw_mem
  have hcoeff : (-1 : ℂ) ^ (V.card - E0.card) ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hi0_mem : (i0 : meroField (Set.univ : Set ℂ)) ∈ S0 :=
    (S0.smul_mem_iff hcoeff).mp hsmul_mem
  exact (linearIndependent_iff_notMem_span.mp hlin i0) hi0_mem

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- A labelled translate of a bottom face coordinate is never a nonempty difference cube of
another labelled translate. -/
theorem cosetBottom_translate_ne_faceDifferenceCube
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {A : Set ℂ} (hA : CosetSeparated τ A)
    (K : Finset ι) {a b : ι}
    (haK : a ∉ K) (hbK : b ∉ K) (hab : a ≠ b)
    (hK : ∀ i, i ∉ K → i = a ∨ i = b)
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ a) (τ b)))
    (V : Finset ι) (hVK : V ⊆ K) (hV : V.Nonempty)
    {g h : ℂ} (hg : g ∈ cosetFaceShiftSet τ A K) (hh : h ∈ cosetFaceShiftSet τ A K) :
    addTranslationMeroEquiv g
        (multipleEllipticGammaLogDerivFaceMero τ hτ K) ≠
      faceDifferenceCube τ V h
        (multipleEllipticGammaLogDerivFaceMero τ hτ K) := by
  classical
  obtain ⟨q, hqV⟩ := hV
  let Ψ := multipleEllipticGammaLogDerivFaceMero τ hτ K
  by_cases hne0 :
      addTranslationMeroEquiv (h + ∑ i ∈ (∅ : Finset ι), τ i) Ψ ≠
        addTranslationMeroEquiv g Ψ
  · exact cosetBottom_translate_ne_faceDifferenceCube_of_term_ne τ hτ hQ hA K
      haK hbK hab hK hperiods V hVK hg hh ∅ (by simp) hne0
  · have heq0 :
        addTranslationMeroEquiv (h + ∑ i ∈ (∅ : Finset ι), τ i) Ψ =
          addTranslationMeroEquiv g Ψ := not_ne_iff.mp hne0
    have hsingleV : ({q} : Finset ι) ∈ V.powerset := by
      rw [Finset.mem_powerset]
      simpa using hqV
    have hsingleK : ({q} : Finset ι) ⊆ K :=
      fun i hi => by
        have hiq : i = q := by simpa using hi
        subst i
        exact hVK hqV
    have hhq : h + ∑ i ∈ ({q} : Finset ι), τ i ∈ cosetFaceShiftSet τ A K :=
      cosetFaceShiftSet_add_subsetSum τ A K {q} hsingleK hh
    have hne1 :
        addTranslationMeroEquiv (h + ∑ i ∈ ({q} : Finset ι), τ i) Ψ ≠
          addTranslationMeroEquiv g Ψ := by
      intro heq1
      have hfun :
          addTranslationMeroEquiv h Ψ =
            addTranslationMeroEquiv (h + ∑ i ∈ ({q} : Finset ι), τ i) Ψ := by
        calc
          addTranslationMeroEquiv h Ψ =
              addTranslationMeroEquiv
                (h + ∑ i ∈ (∅ : Finset ι), τ i) Ψ := by simp
          _ = addTranslationMeroEquiv g Ψ := heq0
          _ = addTranslationMeroEquiv
                (h + ∑ i ∈ ({q} : Finset ι), τ i) Ψ := heq1.symm
      have hshift :
          h = h + ∑ i ∈ ({q} : Finset ι), τ i :=
        cosetFaceShiftSet_translate_injective_bottom τ hτ hQ hA K haK hbK hab hK hperiods
          hh hhq hfun
      have hsubset :
          (∅ : Finset ι) = {q} := by
        apply periodSubsetSum_injective τ hQ
        have hshift' :
            h + 0 = h + ∑ i ∈ ({q} : Finset ι), τ i := by simpa using hshift
        simpa using add_left_cancel hshift'
      simpa using congrArg (fun E : Finset ι => q ∈ E) hsubset
    exact cosetBottom_translate_ne_faceDifferenceCube_of_term_ne τ hτ hQ hA K
      haK hbK hab hK hperiods V hVK hg hh {q} hsingleV hne1

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Labelled strict face-depth rigidity, relative to a bottom extension. -/
theorem cosetFace_translate_ne_of_nested_of_bottom_extension
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {A : Set ℂ} (hA : CosetSeparated τ A)
    (J L K : Finset ι) (hJL : J ⊆ L) (hJLne : J ≠ L) (hLK : L ⊆ K)
    {a b : ι} (haK : a ∉ K) (hbK : b ∉ K) (hab : a ≠ b)
    (hK : ∀ i, i ∉ K → i = a ∨ i = b)
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ a) (τ b)))
    {g h : ℂ} (hg : g ∈ cosetFaceShiftSet τ A J) (hh : h ∈ cosetFaceShiftSet τ A L) :
    addTranslationMeroEquiv g
        (multipleEllipticGammaLogDerivFaceMero τ hτ J) ≠
      addTranslationMeroEquiv h
        (multipleEllipticGammaLogDerivFaceMero τ hτ L) := by
  classical
  let U := K \ J
  let U' := K \ L
  let V := L \ J
  have hJK : J ⊆ K := fun i hi => hLK (hJL hi)
  have hUdisjJ : Disjoint U J := by
    rw [Finset.disjoint_left]
    simp [U]
  have hU'disjL : Disjoint U' L := by
    rw [Finset.disjoint_left]
    simp [U']
  have hU'V : Disjoint U' V := by
    rw [Finset.disjoint_left]
    intro i hiU hiV
    exact (Finset.mem_sdiff.mp hiU).2 (Finset.mem_sdiff.mp hiV).1
  have hpartition : U = U' ∪ V := by
    ext i
    simp only [U, U', V, Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hiK, hiJ⟩
      by_cases hiL : i ∈ L
      · exact Or.inr ⟨hiL, hiJ⟩
      · exact Or.inl ⟨hiK, hiL⟩
    · rintro (⟨hiK, hiL⟩ | ⟨hiL, hiJ⟩)
      · exact ⟨hiK, fun hiJ => hiL (hJL hiJ)⟩
      · exact ⟨hLK hiL, hiJ⟩
  have hJunion : J ∪ U = K := by
    change J ∪ (K \ J) = K
    rw [Finset.union_comm, Finset.sdiff_union_of_subset hJK]
  have hLunion : L ∪ U' = K := by
    change L ∪ (K \ L) = K
    rw [Finset.union_comm, Finset.sdiff_union_of_subset hLK]
  have hVK : V ⊆ K := fun i hi => hLK (Finset.mem_sdiff.mp hi).1
  have hV : V.Nonempty := by
    change (L \ J).Nonempty
    rw [Finset.sdiff_nonempty]
    intro hLJ
    exact hJLne (Finset.Subset.antisymm hJL hLJ)
  have hgK : g ∈ cosetFaceShiftSet τ A K :=
    cosetFaceShiftSet_mono τ A hJK hg
  have hhK : h ∈ cosetFaceShiftSet τ A K :=
    cosetFaceShiftSet_mono τ A hLK hh
  intro heq
  have hcube := congrArg
    (fun f : meroField (Set.univ : Set ℂ) => faceDifferenceCube τ U 0 f) heq
  change faceDifferenceCube τ U 0
      (addTranslationMeroEquiv g
        (multipleEllipticGammaLogDerivFaceMero τ hτ J)) =
    faceDifferenceCube τ U 0
      (addTranslationMeroEquiv h
        (multipleEllipticGammaLogDerivFaceMero τ hτ L)) at hcube
  rw [faceDifferenceCube_translate, faceDifferenceCube_translate] at hcube
  simp only [zero_add] at hcube
  have hleft :
      faceDifferenceCube τ U g
          (multipleEllipticGammaLogDerivFaceMero τ hτ J) =
        addTranslationMeroEquiv g
          (multipleEllipticGammaLogDerivFaceMero τ hτ K) := by
    rw [faceDifferenceCube_face τ hτ J U hUdisjJ g, hJunion]
  have hright :
      faceDifferenceCube τ U h
          (multipleEllipticGammaLogDerivFaceMero τ hτ L) =
        faceDifferenceCube τ V h
          (multipleEllipticGammaLogDerivFaceMero τ hτ K) := by
    rw [hpartition]
    rw [faceDifferenceCube_face_partition τ hτ L U' V hU'disjL hU'V h]
    rw [hLunion]
  rw [hleft, hright] at hcube
  exact (cosetBottom_translate_ne_faceDifferenceCube τ hτ hQ hA K haK hbK hab hK hperiods
    V hVK hV hgK hhK) hcube

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **Labelled strict face-depth rigidity.** -/
theorem cosetFace_translate_ne_of_ssubset
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {A : Set ℂ} (hA : CosetSeparated τ A)
    (J L : Finset ι) (hJL : J ⊆ L) (hJLne : J ≠ L) (hL : 2 ≤ (Lᶜ).card)
    {g h : ℂ} (hg : g ∈ cosetFaceShiftSet τ A J) (hh : h ∈ cosetFaceShiftSet τ A L) :
    addTranslationMeroEquiv g
        (multipleEllipticGammaLogDerivFaceMero τ hτ J) ≠
      addTranslationMeroEquiv h
        (multipleEllipticGammaLogDerivFaceMero τ hτ L) := by
  classical
  obtain ⟨B, hBL, hBcard⟩ := Finset.exists_subset_card_eq hL
  obtain ⟨a, b, hab, hB⟩ := Finset.card_eq_two.mp hBcard
  let K : Finset ι := Bᶜ
  have hLK : L ⊆ K := by
    intro i hiL
    change i ∈ Bᶜ
    rw [Finset.mem_compl]
    intro hiB
    exact (Finset.mem_compl.mp (hBL hiB)) hiL
  have haB : a ∈ B := by
    rw [hB]
    exact Finset.mem_insert_self a {b}
  have hbB : b ∈ B := by
    rw [hB]
    simp
  have haK : a ∉ K := by
    change a ∉ Bᶜ
    simpa using haB
  have hbK : b ∉ K := by
    change b ∉ Bᶜ
    simpa using hbB
  have hK : ∀ i, i ∉ K → i = a ∨ i = b := by
    intro i hi
    have hiB : i ∈ B := by
      simpa [K] using hi
    rw [hB] at hiB
    simpa using hiB
  exact cosetFace_translate_ne_of_nested_of_bottom_extension
    τ hτ hQ hA J L K hJL hJLne hLK haK hbK hab hK
      (linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent τ hQ hab)
      hg hh

set_option maxHeartbeats 3000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **Complete labelled face-packet disjointness.**  Labelled translates of any two distinct
deletion faces are distinct. -/
theorem cosetFace_translate_ne_of_ne
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {A : Set ℂ} (hA : CosetSeparated τ A)
    (J L : Finset ι) (hJLne : J ≠ L)
    (hJcard : 2 ≤ (Jᶜ).card) (hLcard : 2 ≤ (Lᶜ).card)
    {g h : ℂ} (hg : g ∈ cosetFaceShiftSet τ A J) (hh : h ∈ cosetFaceShiftSet τ A L) :
    addTranslationMeroEquiv g
        (multipleEllipticGammaLogDerivFaceMero τ hτ J) ≠
      addTranslationMeroEquiv h
        (multipleEllipticGammaLogDerivFaceMero τ hτ L) := by
  classical
  by_cases hJL : J ⊆ L
  · exact cosetFace_translate_ne_of_ssubset
      τ hτ hQ hA J L hJL hJLne hLcard hg hh
  by_cases hLJ : L ⊆ J
  · exact (cosetFace_translate_ne_of_ssubset
      τ hτ hQ hA L J hLJ hJLne.symm hJcard hh hg).symm
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
  obtain ⟨Aq, Bq, hAS, hBT, hAcard, hBcard, hAB, hcompat⟩ :=
    exists_compatible_two_subsets_of_incomparable S T hJcard hLcard hST hTS
  obtain ⟨a, b, hab, hAeq⟩ := Finset.card_eq_two.mp hAcard
  obtain ⟨c, d, hcd, hBeq⟩ := Finset.card_eq_two.mp hBcard
  let K := Aqᶜ
  let M := Bqᶜ
  let U := S \ Aq
  let U' := T \ Bq
  let V := U' \ U
  let W := U \ U'
  have hJK : J ⊆ K := by
    intro i hiJ
    change i ∈ Aqᶜ
    rw [Finset.mem_compl]
    intro hiA
    exact (Finset.mem_compl.mp (hAS hiA)) hiJ
  have hLM : L ⊆ M := by
    intro i hiL
    change i ∈ Bqᶜ
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
    change i ∈ Aqᶜ
    rw [Finset.mem_compl]
    intro hiA
    have hiU' := (Finset.mem_sdiff.mp hiV).1
    have hiT := (Finset.mem_sdiff.mp hiU').1
    have hiB := (Finset.mem_sdiff.mp hiU').2
    have hiS := hAS hiA
    have hiAT : i ∈ Aq ∩ T := Finset.mem_inter.mpr ⟨hiA, hiT⟩
    have hiBS : i ∈ Bq ∩ S := hcompat ▸ hiAT
    exact hiB (Finset.mem_inter.mp hiBS).1
  have hWM : W ⊆ M := by
    intro i hiW
    change i ∈ Bqᶜ
    rw [Finset.mem_compl]
    intro hiB
    have hiU := (Finset.mem_sdiff.mp hiW).1
    have hiS := (Finset.mem_sdiff.mp hiU).1
    have hiA := (Finset.mem_sdiff.mp hiU).2
    have hiT := hBT hiB
    have hiBS : i ∈ Bq ∩ S := Finset.mem_inter.mpr ⟨hiB, hiS⟩
    have hiAT : i ∈ Aq ∩ T := hcompat.symm ▸ hiBS
    exact hiA (Finset.mem_inter.mp hiAT).1
  have hKM : K ≠ M := by
    intro hk
    apply hAB
    have hc := congrArg (fun X : Finset ι => Xᶜ) hk
    simpa [K, M] using hc
  have haK : a ∉ K := by
    change a ∉ Aqᶜ
    rw [hAeq]
    simp
  have hbK : b ∉ K := by
    change b ∉ Aqᶜ
    rw [hAeq]
    simp
  have hK : ∀ i, i ∉ K → i = a ∨ i = b := by
    intro i hi
    have hiA : i ∈ Aq := by simpa [K] using hi
    rw [hAeq] at hiA
    simpa using hiA
  have hcM : c ∉ M := by
    change c ∉ Bqᶜ
    rw [hBeq]
    simp
  have hdM : d ∉ M := by
    change d ∉ Bqᶜ
    rw [hBeq]
    simp
  have hM : ∀ i, i ∉ M → i = c ∨ i = d := by
    intro i hi
    have hiB : i ∈ Bq := by simpa [M] using hi
    rw [hBeq] at hiB
    simpa using hiB
  have hgK : g ∈ cosetFaceShiftSet τ A K :=
    cosetFaceShiftSet_mono τ A hJK hg
  have hhM : h ∈ cosetFaceShiftSet τ A M :=
    cosetFaceShiftSet_mono τ A hLM hh
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
  exact (cosetFaceDifferenceCube_ne_of_distinct_bottom_faces τ hτ hQ hA K M hKM
    haK hbK hab hK hcM hdM hcd hM V W hVK hWM hgK hhM) hcube

end GaloisForLFunctions

end

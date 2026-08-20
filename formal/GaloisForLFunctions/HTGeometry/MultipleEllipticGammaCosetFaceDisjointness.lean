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

omit [Fintype ι] [DecidableEq ι] in
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

end GaloisForLFunctions

end

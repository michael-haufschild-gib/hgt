import GaloisForLFunctions.HTGeometry.BottomFaceStarIndependence
import GaloisForLFunctions.HTGeometry.FaceTranslateInjective
import Mathlib.Data.Finset.Powerset

/-!
# Strict face-depth rigidity for multiple elliptic gamma functions

Finite differences descend any proper deletion chain to a bottom face.  Bottom-packet differential
independence then prevents a translate of a shallower coordinate from colliding with a translate of
a deeper coordinate.  The final theorem is
`multipleEllipticGammaFace_translate_ne_of_ssubset`.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace GaloisForLFunctions

open Bottcher HTGeometry

attribute [local instance] facePacketMeroDecidableEq

attribute [local instance] ellipticGammaStructuralGeneratorRestrictedDifferential
  ellipticGammaStructuralGeneratorDifferentialAlgebra ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Alternating Boolean cube of translations: the simultaneous finite difference in `U`,
started at shift `g`. -/
def faceDifferenceCube
    (τ : ι → ℂ) (U : Finset ι) (g : ℂ)
    (f : meroField (Set.univ : Set ℂ)) :
    meroField (Set.univ : Set ℂ) :=
  ∑ E ∈ U.powerset,
    (-1 : meroField (Set.univ : Set ℂ)) ^ (U.card - E.card) *
      addTranslationMeroEquiv (g + ∑ i ∈ E, τ i) f

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem faceDifferenceCube_empty
    (τ : ι → ℂ) (g : ℂ) (f : meroField (Set.univ : Set ℂ)) :
    faceDifferenceCube τ ∅ g f = addTranslationMeroEquiv g f := by
  simp [faceDifferenceCube]

omit [Fintype ι] in
set_option maxHeartbeats 1000000 in
theorem faceDifferenceCube_insert
    (τ : ι → ℂ) (U : Finset ι) {q : ι} (hq : q ∉ U)
    (g : ℂ) (f : meroField (Set.univ : Set ℂ)) :
    faceDifferenceCube τ (insert q U) g f =
      addTranslationMeroEquiv (τ q) (faceDifferenceCube τ U g f) -
        faceDifferenceCube τ U g f := by
  classical
  have hdisj : Disjoint U.powerset (Finset.image (insert q) U.powerset) := by
    rw [Finset.disjoint_left]
    intro E hEU hEimg
    obtain ⟨F, hFU, rfl⟩ := Finset.mem_image.mp hEimg
    exact hq (Finset.mem_powerset.mp hEU (Finset.mem_insert_self q F))
  rw [faceDifferenceCube, Finset.powerset_insert, Finset.sum_union hdisj]
  rw [Finset.sum_image]
  · simp only [faceDifferenceCube, Finset.card_insert_of_notMem hq]
    rw [map_sum]
    simp only [map_mul, map_pow, map_neg, map_one]
    have hneg :
        (∑ x ∈ U.powerset,
          (-1 : meroField (Set.univ : Set ℂ)) ^ (U.card + 1 - x.card) *
            addTranslationMeroEquiv (g + ∑ i ∈ x, τ i) f) =
          -(∑ x ∈ U.powerset,
            (-1 : meroField (Set.univ : Set ℂ)) ^ (U.card - x.card) *
              addTranslationMeroEquiv (g + ∑ i ∈ x, τ i) f) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hcard : x.card ≤ U.card :=
        Finset.card_le_card (Finset.mem_powerset.mp hx)
      have hexp : U.card + 1 - x.card = (U.card - x.card) + 1 := by omega
      rw [hexp, pow_succ]
      ring
    have htrans :
        (∑ x ∈ U.powerset,
          (-1 : meroField (Set.univ : Set ℂ)) ^ (U.card + 1 - (insert q x).card) *
            addTranslationMeroEquiv (g + ∑ i ∈ insert q x, τ i) f) =
          ∑ x ∈ U.powerset,
            (-1 : meroField (Set.univ : Set ℂ)) ^ (U.card - x.card) *
              addTranslationMeroEquiv (τ q + (g + ∑ i ∈ x, τ i)) f := by
      refine Finset.sum_congr rfl fun x hx => ?_
      have hqx : q ∉ x := fun h =>
        hq (Finset.mem_powerset.mp hx h)
      rw [Finset.card_insert_of_notMem hqx, Finset.sum_insert hqx]
      have hcard : x.card ≤ U.card :=
        Finset.card_le_card (Finset.mem_powerset.mp hx)
      have hexp : U.card + 1 - (x.card + 1) = U.card - x.card := by omega
      rw [hexp]
      congr 2
      abel
    have hmap :
        (∑ x ∈ U.powerset,
          (-1 : meroField (Set.univ : Set ℂ)) ^ (U.card - x.card) *
            addTranslationMeroEquiv (τ q + (g + ∑ i ∈ x, τ i)) f) =
          ∑ x ∈ U.powerset,
            (-1 : meroField (Set.univ : Set ℂ)) ^ (U.card - x.card) *
              addTranslationMeroEquiv (τ q)
                (addTranslationMeroEquiv (g + ∑ i ∈ x, τ i) f) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [addTranslationMeroEquiv_add]
    rw [hneg, htrans, hmap]
    abel
  · intro E hEU F hFU hEF
    have hqE : q ∉ E := fun h =>
      hq (Finset.mem_powerset.mp hEU h)
    have hqF : q ∉ F := fun h =>
      hq (Finset.mem_powerset.mp hFU h)
    ext a
    by_cases haq : a = q
    · subst a
      simp [hqE, hqF]
    · have hmem := congrArg (fun X : Finset ι => a ∈ X) hEF
      simpa [haq] using hmem

set_option maxHeartbeats 1000000 in
theorem faceDifferenceCube_face
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (J U : Finset ι) (hdisj : Disjoint U J) (g : ℂ) :
    faceDifferenceCube τ U g
        (multipleEllipticGammaLogDerivFaceMero τ hτ J) =
      addTranslationMeroEquiv g
        (multipleEllipticGammaLogDerivFaceMero τ hτ (J ∪ U)) := by
  classical
  induction U using Finset.induction_on generalizing J with
  | empty =>
      simp
  | @insert q U hq ih =>
      have hqJ : q ∉ J := by
        intro h
        exact Finset.disjoint_left.mp hdisj (Finset.mem_insert_self q U) h
      have hUJ : Disjoint U J :=
        hdisj.mono (Finset.subset_insert q U) (fun _ h => h)
      rw [faceDifferenceCube_insert τ U hq]
      rw [ih J hUJ]
      rw [facePacket_coface τ hτ (J ∪ U) (by
        simp [hq, hqJ]) g]
      congr 2
      ext i
      simp [or_comm]

omit [Fintype ι] [DecidableEq ι] in
set_option maxHeartbeats 1000000 in
theorem faceDifferenceCube_translate
    (τ : ι → ℂ) (U : Finset ι) (a b : ℂ)
    (f : meroField (Set.univ : Set ℂ)) :
    faceDifferenceCube τ U a (addTranslationMeroEquiv b f) =
      faceDifferenceCube τ U (a + b) f := by
  classical
  simp only [faceDifferenceCube]
  refine Finset.sum_congr rfl fun E hE => ?_
  rw [addTranslationMeroEquiv_add]
  congr 2
  abel

omit [Fintype ι] in
set_option maxHeartbeats 1000000 in
theorem faceDifferenceCube_union
    (τ : ι → ℂ) (U V : Finset ι) (hUV : Disjoint U V)
    (g : ℂ) (f : meroField (Set.univ : Set ℂ)) :
    faceDifferenceCube τ (U ∪ V) g f =
      faceDifferenceCube τ V 0 (faceDifferenceCube τ U g f) := by
  classical
  induction V using Finset.induction_on with
  | empty =>
      rw [Finset.union_empty, faceDifferenceCube_empty,
        addTranslationMeroEquiv_zero_apply]
  | @insert q V hq ih =>
      have hqU : q ∉ U := by
        intro h
        exact Finset.disjoint_left.mp hUV h (Finset.mem_insert_self q V)
      have hUV' : Disjoint U V :=
        hUV.mono (fun _ h => h) (Finset.subset_insert q V)
      rw [Finset.union_insert, faceDifferenceCube_insert τ (U ∪ V) (by simp [hq, hqU])]
      rw [faceDifferenceCube_insert τ V hq]
      rw [ih hUV']

set_option maxHeartbeats 1000000 in
theorem faceDifferenceCube_face_partition
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (J U V : Finset ι) (hUJ : Disjoint U J) (hUV : Disjoint U V)
    (g : ℂ) :
    faceDifferenceCube τ (U ∪ V) g
        (multipleEllipticGammaLogDerivFaceMero τ hτ J) =
      faceDifferenceCube τ V g
        (multipleEllipticGammaLogDerivFaceMero τ hτ (J ∪ U)) := by
  rw [faceDifferenceCube_union τ U V hUV]
  rw [faceDifferenceCube_face τ hτ J U hUJ g]
  rw [faceDifferenceCube_translate]
  simp

set_option maxHeartbeats 1000000 in
theorem periodSubsetSum_injective
    (τ : ι → ℂ) (hQ : PeriodsIntegrallyIndependent τ) :
    Function.Injective (fun E : Finset ι => ∑ i ∈ E, τ i) := by
  classical
  intro E F hEF
  let n : ι → ℤ := fun i =>
    (if i ∈ E then 1 else 0) - (if i ∈ F then 1 else 0)
  have hrel : ((0 : ℤ) : ℂ) + ∑ i, (n i : ℂ) * τ i = 0 := by
    have hsumE : ∑ i, ((if i ∈ E then 1 else 0 : ℤ) : ℂ) * τ i =
        ∑ i ∈ E, τ i := by
      simp
    have hsumF : ∑ i, ((if i ∈ F then 1 else 0 : ℤ) : ℂ) * τ i =
        ∑ i ∈ F, τ i := by
      simp
    norm_num
    simp only [n, Int.cast_sub, sub_mul, Finset.sum_sub_distrib, hsumE, hsumF]
    exact sub_eq_zero.mpr hEF
  obtain ⟨-, hn⟩ := hQ 0 n hrel
  ext i
  have hi := hn i
  simp only [n] at hi
  by_cases hiE : i ∈ E <;> by_cases hiF : i ∈ F <;> simp [hiE, hiF] at hi ⊢

set_option maxHeartbeats 1000000 in
theorem faceShiftLattice_add_subsetSum
    (τ : ι → ℂ) (K E : Finset ι) (hEK : E ⊆ K)
    {g : ℂ} (hg : g ∈ faceShiftLattice τ K) :
    g + ∑ i ∈ E, τ i ∈ faceShiftLattice τ K := by
  classical
  induction E using Finset.induction_on with
  | empty =>
      simpa using hg
  | @insert q E hq ih =>
      have hqK : q ∈ K := hEK (Finset.mem_insert_self q E)
      have hEK' : E ⊆ K := fun i hi => hEK (Finset.mem_insert_of_mem hi)
      have hmem := faceShiftLattice_add_zsmul τ K hqK (ih hEK') (1 : ℤ)
      rw [Finset.sum_insert hq]
      norm_num at hmem
      convert hmem using 1
      abel

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem bottom_translate_ne_faceDifferenceCube_of_term_ne
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (K : Finset ι) {a b : ι}
    (haK : a ∉ K) (hbK : b ∉ K) (hab : a ≠ b)
    (hK : ∀ i, i ∉ K → i = a ∨ i = b)
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ a) (τ b)))
    (V : Finset ι) (hVK : V ⊆ K)
    {g h : ℂ} (hg : g ∈ faceShiftLattice τ K) (hh : h ∈ faceShiftLattice τ K)
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
  let P := multipleEllipticGammaFacePacket τ hτ K
  let Ψ := multipleEllipticGammaLogDerivFaceMero τ hτ K
  have hE0K : E0 ⊆ K :=
    fun i hi => hVK (Finset.mem_powerset.mp hE0 hi)
  have hhE0 : h + ∑ i ∈ E0, τ i ∈ faceShiftLattice τ K :=
    faceShiftLattice_add_subsetSum τ K E0 hE0K hh
  let i0 : P :=
    ⟨addTranslationMeroEquiv (h + ∑ i ∈ E0, τ i) Ψ,
      ⟨h + ∑ i ∈ E0, τ i, hhE0, rfl⟩⟩
  let ig : P :=
    ⟨addTranslationMeroEquiv g Ψ, ⟨g, hg, rfl⟩⟩
  have hdiff : DiffIndepOn ℂ P :=
    diffIndepOn_of_diffIndepOn_differentialAdjoin
      (multipleEllipticGammaFacePacket_diffIndepOn_bottom τ hτ hQ K
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
    have hhE : h + ∑ i ∈ E, τ i ∈ faceShiftLattice τ K :=
      faceShiftLattice_add_subsetSum τ K E hEK hh
    let iE : P :=
      ⟨addTranslationMeroEquiv (h + ∑ i ∈ E, τ i) Ψ,
        ⟨h + ∑ i ∈ E, τ i, hhE, rfl⟩⟩
    have hEE0 : E ≠ E0 := Finset.ne_of_mem_erase hE
    have hiE_ne : iE ≠ i0 := by
      intro hi
      have hfun := congrArg (fun x : P => (x : meroField (Set.univ : Set ℂ))) hi
      have hshift :
          h + ∑ i ∈ E, τ i = h + ∑ i ∈ E0, τ i :=
        faceShiftLattice_translate_injective_bottom τ hτ hQ K haK hbK hab hK hperiods
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
theorem bottom_translate_ne_faceDifferenceCube
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (K : Finset ι) {a b : ι}
    (haK : a ∉ K) (hbK : b ∉ K) (hab : a ≠ b)
    (hK : ∀ i, i ∉ K → i = a ∨ i = b)
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ a) (τ b)))
    (V : Finset ι) (hVK : V ⊆ K) (hV : V.Nonempty)
    {g h : ℂ} (hg : g ∈ faceShiftLattice τ K) (hh : h ∈ faceShiftLattice τ K) :
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
  · exact bottom_translate_ne_faceDifferenceCube_of_term_ne τ hτ hQ K
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
    have hhq : h + ∑ i ∈ ({q} : Finset ι), τ i ∈ faceShiftLattice τ K :=
      faceShiftLattice_add_subsetSum τ K {q} hsingleK hh
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
        faceShiftLattice_translate_injective_bottom τ hτ hQ K haK hbK hab hK hperiods
          hh hhq hfun
      have hsubset :
          (∅ : Finset ι) = {q} := by
        apply periodSubsetSum_injective τ hQ
        have hshift' :
            h + 0 = h + ∑ i ∈ ({q} : Finset ι), τ i := by simpa using hshift
        simpa using add_left_cancel hshift'
      simpa using congrArg (fun E : Finset ι => q ∈ E) hsubset
    exact bottom_translate_ne_faceDifferenceCube_of_term_ne τ hτ hQ K
      haK hbK hab hK hperiods V hVK hg hh {q} hsingleV hne1

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem multipleEllipticGammaFace_translate_ne_of_nested_of_bottom_extension
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (J L K : Finset ι) (hJL : J ⊆ L) (hJLne : J ≠ L) (hLK : L ⊆ K)
    {a b : ι} (haK : a ∉ K) (hbK : b ∉ K) (hab : a ≠ b)
    (hK : ∀ i, i ∉ K → i = a ∨ i = b)
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ a) (τ b)))
    {g h : ℂ} (hg : g ∈ faceShiftLattice τ J) (hh : h ∈ faceShiftLattice τ L) :
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
  have hgK : g ∈ faceShiftLattice τ K :=
    faceShiftLattice_mono τ hJK hg
  have hhK : h ∈ faceShiftLattice τ K :=
    faceShiftLattice_mono τ hLK hh
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
  exact (bottom_translate_ne_faceDifferenceCube τ hτ hQ K haK hbK hab hK hperiods
    V hVK hV hgK hhK) hcube

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **Strict face-depth rigidity.**  Along every proper deletion chain whose deeper face retains at
least two parameters, no external-lattice translate of the shallower face coordinate equals an
external-lattice translate of the deeper face coordinate. -/
theorem multipleEllipticGammaFace_translate_ne_of_ssubset
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (J L : Finset ι) (hJL : J ⊆ L) (hJLne : J ≠ L) (hL : 2 ≤ (Lᶜ).card)
    {g h : ℂ} (hg : g ∈ faceShiftLattice τ J) (hh : h ∈ faceShiftLattice τ L) :
    addTranslationMeroEquiv g
        (multipleEllipticGammaLogDerivFaceMero τ hτ J) ≠
      addTranslationMeroEquiv h
        (multipleEllipticGammaLogDerivFaceMero τ hτ L) := by
  classical
  obtain ⟨A, hAL, hAcard⟩ := Finset.exists_subset_card_eq hL
  obtain ⟨a, b, hab, hA⟩ := Finset.card_eq_two.mp hAcard
  let K : Finset ι := Aᶜ
  have hLK : L ⊆ K := by
    intro i hiL
    change i ∈ Aᶜ
    rw [Finset.mem_compl]
    intro hiA
    exact (Finset.mem_compl.mp (hAL hiA)) hiL
  have haA : a ∈ A := by
    rw [hA]
    exact Finset.mem_insert_self a {b}
  have hbA : b ∈ A := by
    rw [hA]
    simp
  have haK : a ∉ K := by
    change a ∉ Aᶜ
    simpa using haA
  have hbK : b ∉ K := by
    change b ∉ Aᶜ
    simpa using hbA
  have hK : ∀ i, i ∉ K → i = a ∨ i = b := by
    intro i hi
    have hiA : i ∈ A := by
      simpa [K] using hi
    rw [hA] at hiA
    simpa using hiA
  exact multipleEllipticGammaFace_translate_ne_of_nested_of_bottom_extension
    τ hτ hQ J L K hJL hJLne hLK haK hbK hab hK
      (linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent τ hQ hab)
      hg hh

end GaloisForLFunctions

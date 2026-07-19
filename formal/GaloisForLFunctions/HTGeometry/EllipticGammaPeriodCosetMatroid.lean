import GaloisForLFunctions.HTGeometry.EllipticGammaStructuralGeneratorSpectrum
import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary

/-!
# Period-coset matroid of elliptic-gamma defects

The external-defect Ostrowski theorem proves freeness after choosing distinct nonzero period
cosets.  The structural-generator spectrum proves that the zero coset is differentially
algebraic, while same-coset defects differ by a differentially algebraic element.  This module
combines those directions into an exact represented matroid: on a nonzero-coset family, the rank
is precisely the number of distinct rank-three period cosets.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher
open HTGeometry

noncomputable section

universe u v w

/-! ## General differential collision law -/

/-- A differentially independent family cannot contain two distinct entries whose difference is
differentially algebraic over the base. -/
theorem DifferentialIndependent.sub_not_differentialAlgebraic
    {F E ι : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {x : ι → E} (hx : DifferentialIndependent F x) {i j : ι} (hij : i ≠ j) :
    ¬ DifferentialAlgebraicOver F (x i - x j) := by
  let left : Unit → E := fun _ ↦ x i
  let right : Unit → E := fun _ ↦ x j
  have hinjective : Function.Injective
      (Sum.elim (fun _ : Unit ↦ i) (fun _ : Unit ↦ j)) := by
    intro a b hab
    cases a with
    | inl a =>
        cases b with
        | inl b => simp
        | inr b => exact False.elim (hij hab)
    | inr a =>
        cases b with
        | inl b => exact False.elim (hij hab.symm)
        | inr b => simp
  have hpair : DifferentialIndependent F (Sum.elim left right) := by
    have hcomp := hx.comp
      (Sum.elim (fun _ : Unit ↦ i) (fun _ : Unit ↦ j)) hinjective
    convert hcomp using 1
    funext s
    cases s <;> rfl
  have hleft := (differentialIndependent_sumElim_right_iff left right).mp hpair |>.2
  intro hsub
  let S := differentialAdjoin F (Set.range right)
  letI : DifferentialAlgebra S E :=
    ⟨fun c ↦ derivationClosedDifferential_apply S
      (derivationClosed_differentialAdjoin F (Set.range right)) c⟩
  have hsubS : DifferentialAlgebraicOver S (x i - x j) :=
    differentialAlgebraicOver_mono hsub
  have hxjS : DifferentialAlgebraicOver S (x j) := by
    have hxj : x j ∈ S := by
      exact subset_differentialAdjoin F (Set.range right)
        ⟨(), by simp [right]⟩
    simpa using differentialAlgebraicOver_algebraMap
      (F := S) (E := E) (⟨x j, hxj⟩ : S)
  have hxiS : DifferentialAlgebraicOver S (x i) := by
    simpa only [sub_add_cancel] using differentialAlgebraicOver_add hsubS hxjS
  have hxiHT : HypertranscendentalOver S (x i) := by
    rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
    simpa [left, S] using hleft
  exact hxiHT hxiS

/-- Every entry of a differentially independent family is hypertranscendental over the base. -/
theorem DifferentialIndependent.apply_not_differentialAlgebraic
    {F E ι : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {x : ι → E} (hx : DifferentialIndependent F x) (i : ι) :
    ¬ DifferentialAlgebraicOver F (x i) := by
  have hsingle : DifferentialIndependent F (fun _ : Unit ↦ x i) :=
    hx.comp (fun _ : Unit ↦ i) (fun _ _ _ ↦ Subsingleton.elim _ _)
  have hHT : HypertranscendentalOver F (x i) := by
    rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
    exact hsingle
  exact hHT

/-- **Differential collision-matroid law.**  If injectively labelled subfamilies are
differentially independent and equal labels force a DA difference, then the represented
differential matroid is exactly the collision matroid of the labels. -/
theorem differentialFamilyMatroid_eq_affineCollisionMatroid_of_parallel
    {F E : Type u} {ι : Type v} {Frame : Type w}
    [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (x : ι → E) (frame : ι → Frame)
    (hindep : ∀ I : Set ι, Set.InjOn frame I →
      DifferentialIndependent F (fun i : I ↦ x i))
    (hparallel : ∀ i j, i ≠ j → frame i = frame j →
      DifferentialAlgebraicOver F (x i - x j)) :
    differentialFamilyMatroid (F := F) x = affineCollisionMatroid frame := by
  rw [differentialFamilyMatroid_eq_affineCollisionMatroid_iff]
  intro I
  constructor
  · intro hI i hi j hj hframe
    by_contra hij
    have hsubtype : (⟨i, hi⟩ : I) ≠ ⟨j, hj⟩ := by
      intro heq
      exact hij (congrArg Subtype.val heq)
    exact (hI.sub_not_differentialAlgebraic hsubtype)
      (hparallel i j hij hframe)
  · exact hindep I

/-! ## Pointed collision matroids -/

/-- The collision matroid of a label map with one distinguished loop label.  Each nonloop label
has rank one, while every index carrying `loopFrame` is a loop. -/
def affinePointedCollisionMatroid {Λ Frame : Type*}
    (frame : Λ → Frame) (loopFrame : Frame) : Matroid Λ :=
  (Matroid.uniqueBaseOn {q | q ≠ loopFrame} Set.univ).comap frame

@[simp]
theorem affinePointedCollisionMatroid_ground {Λ Frame : Type*}
    (frame : Λ → Frame) (loopFrame : Frame) :
    (affinePointedCollisionMatroid frame loopFrame).E = Set.univ := by
  simp [affinePointedCollisionMatroid]

/-- Independence in a pointed collision matroid means injective nonloop labels. -/
theorem affinePointedCollisionMatroid_indep_iff {Λ Frame : Type*}
    (frame : Λ → Frame) (loopFrame : Frame) (I : Set Λ) :
    (affinePointedCollisionMatroid frame loopFrame).Indep I ↔
      Set.InjOn frame I ∧ ∀ i ∈ I, frame i ≠ loopFrame := by
  rw [affinePointedCollisionMatroid, Matroid.comap_indep_iff,
    Matroid.uniqueBaseOn_indep_iff (Set.subset_univ _)]
  constructor
  · rintro ⟨himage, hinj⟩
    refine ⟨hinj, ?_⟩
    intro i hi
    exact himage ⟨i, hi, rfl⟩
  · rintro ⟨hinj, hnonloop⟩
    refine ⟨?_, hinj⟩
    rintro q ⟨i, hi, rfl⟩
    exact hnonloop i hi

/-- The extended rank of a pointed collision packet is the number of distinct nonloop labels. -/
theorem affinePointedCollisionMatroid_eRk {Λ Frame : Type*}
    (frame : Λ → Frame) (loopFrame : Frame) (I : Set Λ) :
    (affinePointedCollisionMatroid frame loopFrame).eRk I =
      ((frame '' I) ∩ {q | q ≠ loopFrame}).encard := by
  rw [affinePointedCollisionMatroid, Matroid.eRk_comap]
  exact (Matroid.uniqueBaseOn_inter_isBasis
    (I := {q | q ≠ loopFrame}) (E := Set.univ)
    (X := frame '' I) (Set.subset_univ _)).eRk_eq_encard

/-- **Pointed differential collision-matroid law.**  If injective nonloop subfamilies are
differentially independent, the loop label gives DA entries, and repeated labels give DA
differences, then the represented differential matroid is the pointed collision matroid. -/
theorem differentialFamilyMatroid_eq_affinePointedCollisionMatroid_of_parallel
    {F E : Type u} {ι : Type v} {Frame : Type w}
    [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (x : ι → E) (frame : ι → Frame) (loopFrame : Frame)
    (hindep : ∀ I : Set ι, Set.InjOn frame I →
      (∀ i ∈ I, frame i ≠ loopFrame) →
      DifferentialIndependent F (fun i : I ↦ x i))
    (hloop : ∀ i, frame i = loopFrame →
      DifferentialAlgebraicOver F (x i))
    (hparallel : ∀ i j, i ≠ j → frame i = frame j →
      DifferentialAlgebraicOver F (x i - x j)) :
    differentialFamilyMatroid (F := F) x =
      affinePointedCollisionMatroid frame loopFrame := by
  apply Matroid.ext_indep
  · simp [differentialFamilyMatroid]
  · intro I _
    rw [differentialFamilyMatroid_indep_iff,
      affinePointedCollisionMatroid_indep_iff]
    constructor
    · intro hI
      constructor
      · intro i hi j hj hframe
        by_contra hij
        have hsubtype : (⟨i, hi⟩ : I) ≠ ⟨j, hj⟩ := by
          intro heq
          exact hij (congrArg Subtype.val heq)
        exact (hI.sub_not_differentialAlgebraic hsubtype)
          (hparallel i j hij hframe)
      · intro i hi hframe
        exact (hI.apply_not_differentialAlgebraic ⟨i, hi⟩)
          (hloop i hframe)
    · rintro ⟨hinj, hnonloop⟩
      exact hindep I hinj hnonloop

/-! ## Rank-three period quotient -/

/-- The additive rank-three period group `ℤ + ℤ tau + ℤ sigma`. -/
def ellipticGammaPeriodSubgroup (sigma tau : ℂ) : AddSubgroup ℂ where
  carrier := {h | ∃ a b n : ℤ,
    h = (a : ℂ) + (b : ℂ) * tau + (n : ℂ) * sigma}
  zero_mem' := ⟨0, 0, 0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, b, n, rfl⟩ ⟨a', b', n', rfl⟩
    refine ⟨a + a', b + b', n + n', ?_⟩
    push_cast
    ring
  neg_mem' := by
    rintro x ⟨a, b, n, rfl⟩
    refine ⟨-a, -b, -n, ?_⟩
    push_cast
    ring

/-- The class of a shift modulo the rank-three elliptic-gamma period group. -/
def ellipticGammaPeriodClass (sigma tau h : ℂ) :
    ℂ ⧸ ellipticGammaPeriodSubgroup sigma tau :=
  QuotientAddGroup.mk h

theorem ellipticGammaPeriodClass_eq_iff
    (sigma tau h k : ℂ) :
    ellipticGammaPeriodClass sigma tau h =
        ellipticGammaPeriodClass sigma tau k ↔
      ∃ a b n : ℤ, h - k = a + b * tau + n * sigma := by
  change QuotientAddGroup.mk h = QuotientAddGroup.mk k ↔ _
  rw [QuotientAddGroup.eq_iff_sub_mem]
  rfl

theorem ellipticGammaPeriodClass_ne_zero_iff
    (sigma tau h : ℂ) :
    ellipticGammaPeriodClass sigma tau h ≠ 0 ↔
      ThetaTranslationNonresonant tau sigma h := by
  change QuotientAddGroup.mk h ≠ 0 ↔ _
  rw [ne_eq, QuotientAddGroup.eq_zero_iff]
  rfl

/-! ## Exact represented matroid and rank -/

local instance ellipticGammaPeriodCosetDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance ellipticGammaPeriodCosetComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance ellipticGammaPeriodCosetComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  meromorphicEllipticCompositumComplexAlgebraMero

local instance ellipticGammaPeriodCosetAmbientDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance ellipticGammaPeriodCosetMeroCharZero :
    CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap ℂ (meroField Set.univ)).injective

local instance ellipticGammaPeriodCosetRestrictedDifferential
    (sigma tau : ℂ) :
    Differential (meromorphicEllipticCompositum sigma tau) :=
  meromorphicEllipticCompositumDifferential sigma tau

local instance ellipticGammaPeriodCosetDifferentialAlgebra
    (sigma tau : ℂ) :
    DifferentialAlgebra (meromorphicEllipticCompositum sigma tau)
      (meroField Set.univ) :=
  ⟨fun x ↦ derivationClosedDifferential_apply
    (meromorphicEllipticCompositum sigma tau)
    (meromorphicEllipticCompositum_derivationClosed sigma tau) x⟩

/-- **Full period-coset partition matroid.**  For an arbitrary family of shifts, the differential
matroid of genuine elliptic-gamma defects over the paired elliptic compositum is the pointed
collision matroid of rank-three period classes.  The zero class consists of loops, and every
nonzero class is a rank-one parallel class. -/
theorem ellipticGammaExternalDefectFamily_differentialMatroid_eq_periodCosetPartitionMatroid
    {κ : Type*} [DecidableEq κ]
    (h : κ → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) :
    differentialFamilyMatroid (F := meromorphicEllipticCompositum sigma tau)
        (ellipticGammaExternalDefectFamily h sigma tau hsigma htau) =
      affinePointedCollisionMatroid
        (ellipticGammaPeriodClass sigma tau ∘ h) 0 := by
  apply differentialFamilyMatroid_eq_affinePointedCollisionMatroid_of_parallel
  · intro I hframe hnonzero
    simpa [ellipticGammaExternalDefectFamily] using
      ellipticGammaExternalDefectFamily_differentialIndependent
        (fun j : I ↦ h j) sigma tau hsigma htau hindependent
        (fun j ↦ (ellipticGammaPeriodClass_ne_zero_iff sigma tau (h j)).mp
          (by simpa [Function.comp_apply] using hnonzero j j.property))
        (by
          intro i j hji hres
          apply hji
          apply Subtype.ext
          apply hframe j.property i.property
          rw [Function.comp_apply, Function.comp_apply,
            ellipticGammaPeriodClass_eq_iff]
          exact hres)
  · intro i hzero
    apply (differentialAlgebraicOver_ellipticGammaExternalLogDerivDefectMero_iff_resonant
      (h i) sigma tau hsigma htau hindependent).2
    have hclass : ellipticGammaPeriodClass sigma tau (h i) =
        ellipticGammaPeriodClass sigma tau 0 := by
      simpa [Function.comp_apply, ellipticGammaPeriodClass] using hzero
    have hres :=
      (ellipticGammaPeriodClass_eq_iff sigma tau (h i) 0).mp hclass
    simpa using hres
  · intro i j hij hframe
    apply differentialAlgebraicOver_ellipticGammaExternalDefect_sub_of_sameCoset
    rw [← ellipticGammaPeriodClass_eq_iff sigma tau (h i) (h j)]
    simpa [Function.comp_apply] using hframe

/-- An arbitrary external-defect subfamily is independent exactly when its period classes are
pairwise distinct and nonzero. -/
theorem ellipticGammaExternalDefectFamily_indep_iff_periodClass_injOn_and_ne_zero
    {κ : Type*} [DecidableEq κ]
    (h : κ → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (I : Set κ) :
    (differentialFamilyMatroid (F := meromorphicEllipticCompositum sigma tau)
      (ellipticGammaExternalDefectFamily h sigma tau hsigma htau)).Indep I ↔
      Set.InjOn (ellipticGammaPeriodClass sigma tau ∘ h) I ∧
        ∀ i ∈ I, ellipticGammaPeriodClass sigma tau (h i) ≠ 0 := by
  rw [ellipticGammaExternalDefectFamily_differentialMatroid_eq_periodCosetPartitionMatroid
    h sigma tau hsigma htau hindependent,
    affinePointedCollisionMatroid_indep_iff]
  rfl

/-- **Exact defect-family rank law.**  The extended differential rank of any external-defect
packet is the number of distinct nonzero rank-three period classes that it meets. -/
theorem ellipticGammaExternalDefectFamily_eRk_eq_nonzeroPeriodClass_encard
    {κ : Type*} [DecidableEq κ]
    (h : κ → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (I : Set κ) :
    (differentialFamilyMatroid (F := meromorphicEllipticCompositum sigma tau)
      (ellipticGammaExternalDefectFamily h sigma tau hsigma htau)).eRk I =
      (((ellipticGammaPeriodClass sigma tau ∘ h) '' I) ∩
        {q | q ≠ 0}).encard := by
  rw [ellipticGammaExternalDefectFamily_differentialMatroid_eq_periodCosetPartitionMatroid
    h sigma tau hsigma htau hindependent,
    affinePointedCollisionMatroid_eRk]

/-- **Exact period-coset matroid.**  For a family avoiding the zero period coset, the differential
matroid of genuine elliptic-gamma defects over the paired elliptic compositum is exactly the
collision matroid of their rank-three period classes.  Thus repetitions within a coset are
parallel and distinct cosets are free. -/
theorem ellipticGammaExternalDefectFamily_differentialMatroid_eq_periodCosetMatroid
    {κ : Type*} [DecidableEq κ]
    (h : κ → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (hnonres : ∀ j, ThetaTranslationNonresonant tau sigma (h j)) :
    differentialFamilyMatroid (F := meromorphicEllipticCompositum sigma tau)
        (ellipticGammaExternalDefectFamily h sigma tau hsigma htau) =
      affineCollisionMatroid (ellipticGammaPeriodClass sigma tau ∘ h) := by
  rw [ellipticGammaExternalDefectFamily_differentialMatroid_eq_periodCosetPartitionMatroid
    h sigma tau hsigma htau hindependent]
  apply Matroid.ext_indep
  · simp
  · intro I _
    rw [affinePointedCollisionMatroid_indep_iff,
      affineCollisionMatroid_indep_iff]
    constructor
    · exact And.left
    · intro hinj
      refine ⟨hinj, ?_⟩
      intro i hi
      exact (ellipticGammaPeriodClass_ne_zero_iff sigma tau (h i)).2
        (hnonres i)

/-- A subfamily of nonresonant external defects is independent exactly when its period classes
are pairwise distinct. -/
theorem ellipticGammaExternalDefectFamily_indep_iff_periodClass_injOn
    {κ : Type*} [DecidableEq κ]
    (h : κ → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (hnonres : ∀ j, ThetaTranslationNonresonant tau sigma (h j))
    (I : Set κ) :
    (differentialFamilyMatroid (F := meromorphicEllipticCompositum sigma tau)
      (ellipticGammaExternalDefectFamily h sigma tau hsigma htau)).Indep I ↔
      Set.InjOn (ellipticGammaPeriodClass sigma tau ∘ h) I := by
  rw [ellipticGammaExternalDefectFamily_differentialMatroid_eq_periodCosetMatroid
    h sigma tau hsigma htau hindependent hnonres,
    affineCollisionMatroid_indep_iff]

/-- The extended differential rank of a nonresonant packet is the number of period cosets it
meets. -/
theorem ellipticGammaExternalDefectFamily_eRk_eq_periodClass_encard
    {κ : Type*} [DecidableEq κ]
    (h : κ → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (hnonres : ∀ j, ThetaTranslationNonresonant tau sigma (h j))
    (I : Set κ) :
    (differentialFamilyMatroid (F := meromorphicEllipticCompositum sigma tau)
      (ellipticGammaExternalDefectFamily h sigma tau hsigma htau)).eRk I =
      ((ellipticGammaPeriodClass sigma tau ∘ h) '' I).encard := by
  rw [ellipticGammaExternalDefectFamily_differentialMatroid_eq_periodCosetMatroid
    h sigma tau hsigma htau hindependent hnonres,
    affineCollisionMatroid_eRk]

end

end GaloisForLFunctions

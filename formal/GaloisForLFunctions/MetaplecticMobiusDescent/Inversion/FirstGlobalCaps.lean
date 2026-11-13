/-
First global caps adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.GlobalPriorityWeights

/-!
# First global caps

Dyadic exponents, parent cells and outer cells of the first global caps
(`InverseFirstGlobalCaps`) and the parent bijection of the first global family; live selector
bounds and source cell ratios.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
namespace InverseFirstGlobalParents
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open RayFourExpansion InverseMoment
open InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityValidSource InversePrioritySecondSource
open InverseInitialArithmetic (sourceIdeal)
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

def ofOriginal (k : FirstOriginalOuter ι) : Source ι 0 where
  cube := k.1
  firstCommon := k.2.1
  firstDivisor := k.2.2
  quotientSupport := ∅
  oldAssigned := Fin.elim0

def toOriginal (x : Source ι 0) : FirstOriginalOuter ι :=
  ⟨x.cube,⟨x.firstCommon,x.firstDivisor⟩⟩

omit [DecidableEq ι] in
@[simp] theorem toOriginal_ofOriginal (k : FirstOriginalOuter ι) :
    toOriginal (ofOriginal k)=k := by cases k with | mk b k => cases k; rfl

omit [DecidableEq ι] in
@[simp] theorem toOriginal_fill (x : Source ι 0) (D : Finset ι) :
    toOriginal (fillFirstQuotient x D)=toOriginal x := rfl

omit [DecidableEq ι] in
theorem ofOriginal_injective : Function.Injective (ofOriginal (ι:=ι)) :=
  Function.LeftInverse.injective toOriginal_ofOriginal

omit [DecidableEq ι] in
theorem ofOriginal_toOriginal (x : Source ι 0) :
    ofOriginal (toOriginal x)=eraseFirstQuotient x := by
  apply Source.ext <;> try rfl
  exact funext (fun i=>Fin.elim0 i)

omit [DecidableEq ι] in

theorem fill_ofOriginal_injective : Function.Injective
    (fun q : FirstOriginalOuter ι × Finset ι=>fillFirstQuotient (ofOriginal q.1) q.2) := by
  intro x y h
  apply Prod.ext
  · simpa only [toOriginal_fill,toOriginal_ofOriginal] using congrArg toOriginal h
  · exact congrArg Source.quotientSupport h

def originalOuterSource (pool : Finset ι) (Q : Finset (ι→₀ℕ)) : Finset (Source ι 0) :=
  (firstOriginalOuter pool Q).image ofOriginal

theorem originalOuterSource_empty (pool : Finset ι) (Q : Finset (ι→₀ℕ)) :
    ∀x∈originalOuterSource pool Q,x.quotientSupport=∅ := by
  intro x hx
  obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp hx
  rfl

theorem sum_originalOuterSource {A : Type*} [AddCommMonoid A]
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (H : Source ι 0→A) :
    (∑x∈originalOuterSource pool Q,H x)=∑k∈firstOriginalOuter pool Q,H (ofOriginal k) := by
  exact Finset.sum_image (fun _ _ _ _ h=>ofOriginal_injective h)

def originalSelector (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (x : Source ι 0) (D : Finset ι) : ℂ := selector (toOriginal x) D

omit [DecidableEq ι] in
@[simp] theorem originalSelector_ofOriginal (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (k : FirstOriginalOuter ι) (D : Finset ι) :
    originalSelector selector (ofOriginal k) D=selector k D := by
  simp only [originalSelector,toOriginal_ofOriginal]

omit [DecidableEq ι] in
@[simp] theorem originalSelector_ofOriginal_fun (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (k : FirstOriginalOuter ι) : originalSelector selector (ofOriginal k)=selector k :=
  funext (originalSelector_ofOriginal selector k)

def originalParentSource (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) : Finset (Source ι 0) :=
  globalParentSource (originalOuterSource pool Q) pool (originalSelector selector)

theorem mem_originalParentSource (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (x : Source ι 0) :
    x∈originalParentSource pool Q selector ↔
      ∃k∈firstOriginalOuter pool Q,∃D∈pool.powerset,
        selector k D≠0 ∧ fillFirstQuotient (ofOriginal k) D=x := by
  simp only [originalParentSource,globalParentSource,Finset.mem_biUnion,
    originalOuterSource,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨y,⟨k,hk,rfl⟩,D,⟨hD,hs⟩,he⟩
    exact ⟨k,hk,D,hD,by simpa using hs,he⟩
  · rintro ⟨k,hk,D,hD,hs,he⟩
    exact ⟨ofOriginal k,⟨k,hk,rfl⟩,D,⟨hD,by simpa using hs⟩,he⟩

theorem original_fill_valid (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (k : FirstOriginalOuter ι) (hk : k∈firstOriginalOuter pool Q) (D : Finset ι) :
    SourceValid p (fillFirstQuotient (ofOriginal k) D) := by
  obtain ⟨hb,hC,hE⟩:=(mem_firstOriginalOuter pool Q k).mp hk
  refine ⟨reopenedCubeFamily_admissible Q k.1 hb,?_,?_,?_⟩
  · exact Finset.disjoint_left.mpr (fun i hi hiB=>
      (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hC hi)).2 hiB)
  · exact (Finset.mem_powerset.mp hE).trans
      (Finset.union_subset_union_right (Finset.filter_subset _ _))
  · exact fun i=>Fin.elim0 i

theorem originalParentSource_valid (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) :
    ∀x∈originalParentSource pool Q selector,SourceValid p x := by
  intro x hx
  obtain ⟨k,hk,D,hD,hs,rfl⟩:=(mem_originalParentSource pool Q selector x).mp hx
  exact original_fill_valid p pool Q k hk D

theorem sum_originalParentSource {A : Type*} [AddCommMonoid A]
    (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (H : Source ι 0→A) :
    (∑x∈originalParentSource pool Q selector,H x)=
      ∑k∈firstOriginalOuter pool Q,∑D∈pool.powerset.filter (fun D=>selector k D≠0),
        H (fillFirstQuotient (ofOriginal k) D) := by
  rw [originalParentSource,sum_globalParentSource _ _ _ (originalOuterSource_empty pool Q),
    sum_originalOuterSource]
  simp only [originalSelector_ofOriginal]

theorem signed_originalParentSource (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (H : Source ι 0→ℂ) :
    (∑x∈originalParentSource pool Q selector,selector (toOriginal x) x.quotientSupport*H x)=
      ∑k∈firstOriginalOuter pool Q,∑D∈pool.powerset,
        selector k D*H (fillFirstQuotient (ofOriginal k) D) := by
  rw [sum_originalParentSource]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro D hD
  by_cases hs:selector k D=0 <;> simp [toOriginal,ofOriginal,fillFirstQuotient,hs]

theorem real_originalParentSource (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (H : Source ι 0→ℝ) :
    (∑x∈originalParentSource pool Q selector,‖selector (toOriginal x) x.quotientSupport‖*H x)=
      ∑k∈firstOriginalOuter pool Q,∑D∈pool.powerset,
        ‖selector k D‖*H (fillFirstQuotient (ofOriginal k) D) := by
  rw [sum_originalParentSource]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro D hD
  by_cases hs:selector k D=0 <;> simp [toOriginal,ofOriginal,fillFirstQuotient,hs]

theorem original_supports (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (hQ : ∀v∈Q,v.support⊆pool) (k : FirstOriginalOuter ι)
    (hk : k∈firstOriginalOuter pool Q) :
    k.1.leftExponent∈Q ∧ k.1.rightExponent∈Q ∧
      k.1.support⊆pool ∧ k.2.1⊆pool ∧ k.2.2⊆pool := by
  obtain ⟨hb,hC,hE⟩:=(mem_firstOriginalOuter pool Q k).mp hk
  have hb' := (mem_reopenedCubeFamily Q k.1).mp hb
  have hs := reopenedCubeFamily_support pool Q hQ k.1 hb
  have hc : k.2.1⊆pool := (Finset.mem_powerset.mp hC).trans Finset.sdiff_subset
  refine ⟨hb'.1,hb'.2.1,hs,hc,?_⟩
  exact (Finset.mem_powerset.mp hE).trans (Finset.union_subset hc
    ((Finset.filter_subset _ _).trans hs))

variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

theorem original_principal_extra (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) :
    ∀x∈originalParentSource pool Q selector,
      cubePrincipalSupport x.cube.support x.cube.leftExponent x.cube.rightExponent
        x.cube.leftBit x.cube.rightBit ⊆ x.cube.support := by
  intro x hx
  exact Finset.filter_subset _ _

omit [DecidableEq ι] [∀i,(Ideal.span {p i}).IsMaximal] in

theorem original_parent_data (k : FirstOriginalOuter ι) (D : Finset ι) :
    (parent p (fillFirstQuotient (ofOriginal k) D)).cube=k.1 ∧
    (parent p (fillFirstQuotient (ofOriginal k) D)).firstCommon=k.2.1 ∧
    (parent p (fillFirstQuotient (ofOriginal k) D)).firstDivisor=k.2.2 ∧
    (parent p (fillFirstQuotient (ofOriginal k) D)).quotient=sourceIdeal p D :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem original_assigned_conditions (hp : ∀i,p i≠0)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (expansion : SecondParentSource ι (0+(J.card+J.card))→Finset (SecondExpansionData ι))
    (hE : ∀y∈assignedParents p (originalParentSource pool Q selector) negative J lists,
      ∀x∈expansion y,x.divisor⊆x.sourceCommon) :
    ActualSecondSourceConditions p (attachedSecondFamily
      (assignedParents p (originalParentSource pool Q selector) negative J lists) expansion) :=
  assigned_family_conditions p hp _ (originalParentSource_valid p pool Q selector)
    negative J lists expansion hE

theorem original_whole_assigned_conditions (hp : ∀i,p i≠0)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (expansion : SecondParentSource ι (0+(J.card+J.card))→Finset (SecondExpansionData ι))
    (hE : ∀y∈wholeAssignedParents p
      (fun x=>cubePrincipalSupport x.cube.support x.cube.leftExponent x.cube.rightExponent
        x.cube.leftBit x.cube.rightBit)
      (originalParentSource pool Q selector) negative J lists,
      ∀x∈expansion y,x.divisor⊆x.sourceCommon) :
    ActualSecondSourceConditions p (attachedSecondFamily
      (wholeAssignedParents p
        (fun x=>cubePrincipalSupport x.cube.support x.cube.leftExponent x.cube.rightExponent
          x.cube.leftBit x.cube.rightBit)
        (originalParentSource pool Q selector) negative J lists) expansion) :=
  whole_assigned_family_conditions p hp _ _ (originalParentSource_valid p pool Q selector)
    (original_principal_extra pool Q selector) negative J lists expansion hE

variable (hg : ∀i,lambda∉Ideal.span {p i})

theorem original_priority_slice
    (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (ray : RayCharacter×RayCharacter)
    (core : FirstCoreIndex) (H : Source ι 0→ℂ) :
    (∑x∈originalParentSource pool Q selector,
      globalPriorityOuter p hg negative Ψ m ray core
        (fun x=>(‖selector (toOriginal x) x.quotientSupport‖:ℂ)) x*H x)=
    ∑k∈firstOriginalOuter pool Q,∑D∈pool.powerset,
      (priorityOuter p hg k.1 negative Ψ m (selector k) ray core D:ℂ)*
        H (fillFirstQuotient (ofOriginal k) D) := by
  have h:=global_original_priority_slice p hg (originalOuterSource pool Q) pool
    (originalSelector selector) (originalOuterSource_empty pool Q) negative Ψ m ray core H
  rw [sum_originalOuterSource] at h
  simp only [originalSelector_ofOriginal_fun] at h
  simpa only [originalParentSource,originalSelector,toOriginal,eraseFirstQuotient,ofOriginal] using h

theorem original_second_energy_source
    (hp : ∀i,p i≠0) (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (extra : CubeCoordinates ι→Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (om : ℝ→ℂ) (X t Y : ℝ) :
    (∑k∈firstOriginalOuter pool Q,
      firstWholePrioritySecondEnergy p hp hg hinj pool k.1 k.2.1 (extra k.1)
        negative Ψ m ((∏ i ∈ k.2.2,p i))
        slots lists a (selector k) om X t Y)=
    firstCoreMassBound*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,
      ∑J∈slots.powerset,(∑x∈originalParentSource pool Q selector,
        globalPriorityOuter p hg negative Ψ m ray core
          (fun x=>(‖selector (toOriginal x) x.quotientSupport‖:ℂ)) x*
        (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
        parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra x.cube)
          a om X t Y ray core (parent p x)).re := by
  have h:=global_second_energy_source p hg hp hinj (originalOuterSource pool Q) pool
    (originalSelector selector) (originalOuterSource_empty pool Q) extra negative Ψ m
    slots lists a om X t Y
  rw [sum_originalOuterSource] at h
  simp only [originalSelector_ofOriginal_fun] at h
  simpa only [originalParentSource,originalSelector,toOriginal,eraseFirstQuotient,ofOriginal] using h

end InverseFirstGlobalParents

end

noncomputable section
namespace InverseFirstGlobalCaps
open InverseMoment InverseFirstGlobalParents InverseFirstPriorityParents
open InverseMomentWholePriorityParents InverseMomentFirstChildWindows
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks (dyadIndex dyadScale dyadScale_pos dyadIndex_bounds)
open Eisenstein (ringComplex)
open InverseInitialArithmetic (sourceIdeal)
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]

def outerNorms (p : ι→O) (x : FirstOriginalOuter ι) : Fin 5→ℝ :=
  ![‖ringComplex (aLabel p x.1.support x.1.rightBit)‖^2,
    ‖ringComplex (aLabel p x.1.support x.1.leftBit)‖^2,
    primeProductNorm p x.2.1,
    ‖ringComplex ((∏ i ∈ x.2.2,p i))‖^2,
    primeProductNorm p (cubeActiveSupport x.1.support
      (fun i=>x.1.leftExponent i+x.1.rightExponent i) x.1.leftBit x.1.rightBit)]

def outerGate (p : ι→O) (k : SourceIndex) (x : FirstOriginalOuter ι) : Prop :=
  ∀i : Fin 5,dyadIndex (outerNorms p x i)=k i.castSucc

def outerCell (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) :=
  (firstOriginalOuter pool Q).filter (outerGate p k)

def parentCell (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ) :=
  (originalParentSource pool Q (fun x=>commonSelector p (selector x) l)).filter
    (fun x=>outerGate p k (toOriginal x))

theorem mem_parentCell (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ)
    (x : Source ι 0) : x∈parentCell p pool Q selector k l ↔
    ∃o∈outerCell p pool Q k,∃D∈pool.powerset,
      commonSelector p (selector o) l D≠0 ∧ fillFirstQuotient (ofOriginal o) D=x := by
  simp only [parentCell,outerCell,Finset.mem_filter,mem_originalParentSource]
  constructor
  · rintro ⟨⟨o,ho,D,hD,hs,rfl⟩,hg⟩
    exact ⟨o,⟨ho,by simpa using hg⟩,D,hD,hs,rfl⟩
  · rintro ⟨o,⟨ho,hg⟩,D,hD,hs,rfl⟩
    exact ⟨⟨o,ho,D,hD,hs,rfl⟩,by simpa using hg⟩

def originalNorms (p : ι→O) (x : Σ _ : FirstOriginalOuter ι,Ideal O×O) : Fin 6→ℝ :=
  sourceNorms (fun y=>outerNorms p y.1 0) (fun y=>outerNorms p y.1 1)
    (fun y=>outerNorms p y.1 2) (fun y=>outerNorms p y.1 4)
    (fun y=>(∏ i ∈ y.1.2.2,p i))
    (fun y=>y.2.2) x

lemma originalNorms_outer (p : ι→O) (x : Σ _ : FirstOriginalOuter ι,Ideal O×O)
    (i : Fin 5) : originalNorms p x i.castSucc=outerNorms p x.1 i := by
  fin_cases i <;> rfl

lemma originalNorms_frequency (p : ι→O) (x : Σ _ : FirstOriginalOuter ι,Ideal O×O) :
    originalNorms p x 5=‖ringComplex x.2.2‖^2 := rfl

theorem sourceCell_outer (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) (k : SourceIndex)
    (x : Σ _ : FirstOriginalOuter ι,Ideal O×O)
    (hx : x∈sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y) k) :
    x.1∈outerCell p pool Q k := by
  obtain ⟨hs,hk⟩:=Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨(Finset.mem_sigma.mp hs).1,?_⟩
  intro i
  simpa only [sourceIndex,originalNorms_outer] using congrFun hk i.castSucc

variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma outerNorms_ge_one (x : FirstOriginalOuter ι) : ∀i,1≤ outerNorms p x i := by
  intro i
  fin_cases i
  · exact SecondPassArithmetic.element_norm_ge_one _ (primeProduct_ne_zero p hp _ _)
  · exact SecondPassArithmetic.element_norm_ge_one _ (primeProduct_ne_zero p hp _ _)
  · exact primeProductNorm_ge_one p hp _
  · change 1≤‖ringComplex ((∏ i ∈ x.2.2,p i))‖^2
    change 1 ≤ primeProductNorm p _
    exact primeProductNorm_ge_one p hp _
  · exact primeProductNorm_ge_one p hp _

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma source_norms_ge_one (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ)
    (x : Σ _ : FirstOriginalOuter ι,Ideal O×O)
    (hx : x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y) :
    ∀i,1≤ originalNorms p x i := by
  have hf:=((mem_firstRetainedSource p labels x.1.1 Y x.2).mp (Finset.mem_sigma.mp hx).2).2
  have hn : x.2.2≠0 := (Finset.mem_erase.mp hf).1
  intro i
  fin_cases i
  · exact outerNorms_ge_one p hp x.1 0
  · exact outerNorms_ge_one p hp x.1 1
  · exact outerNorms_ge_one p hp x.1 2
  · exact outerNorms_ge_one p hp x.1 3
  · exact outerNorms_ge_one p hp x.1 4
  · exact SecondPassArithmetic.element_norm_ge_one _ hn

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem sourceCell_frequency (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) (k : SourceIndex)
    (x : Σ _ : FirstOriginalOuter ι,Ideal O×O)
    (hx : x∈sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y) k) :
    dyadScale (k 5)≤‖ringComplex x.2.2‖^2 ∧
      ‖ringComplex x.2.2‖^2≤2*dyadScale (k 5) := by
  have h:=sourceCell_ratios (originalNorms p) _ (source_norms_ge_one p hp pool Q labels Y) k x hx 5
  exact ⟨by simpa only [originalNorms_frequency,one_mul] using (le_div_iff₀ (dyadScale_pos _)).mp h.1,
    by simpa only [originalNorms_frequency] using (div_le_iff₀ (dyadScale_pos _)).mp h.2⟩

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma outerGate_dyads (k : SourceIndex) (x : FirstOriginalOuter ι) (hx : outerGate p k x) :
    ∀i : Fin 5,dyadScale (k i.castSucc)≤ outerNorms p x i ∧
      outerNorms p x i≤2*dyadScale (k i.castSucc) := by
  intro i
  have h:=dyadIndex_bounds _ (outerNorms_ge_one p hp x i)
  rw [hx i] at h
  exact ⟨h.1,h.2.le⟩

omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma commonSelector_norm (selector : Finset ι→ℂ) (l : ℕ) (D : Finset ι) :
    ‖commonSelector p selector l D‖≤‖selector D‖ := by
  unfold commonSelector
  split_ifs <;> simp

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma live_common_dyads (selector : Finset ι→ℂ) (l : ℕ) (D : Finset ι)
    (hlive : commonSelector p selector l D≠0) :
    dyadScale l≤ primeProductNorm p D ∧ primeProductNorm p D≤2*dyadScale l := by
  have he : dyadIndex (primeProductNorm p D)=l := by
    by_contra h
    exact hlive (by simp [commonSelector,h])
  have h:=dyadIndex_bounds _ (primeProductNorm_ge_one p hp D)
  rw [he] at h
  exact ⟨h.1,h.2.le⟩

omit [DecidableEq ι] [∀i,(Ideal.span {p i}).IsMaximal] in
lemma sourceIdeal_norm (D : Finset ι) : (Ideal.absNorm (sourceIdeal p D):ℝ)=primeProductNorm p D := by
  simp only [sourceIdeal,←ringComplex_norm_sq_eq_absNorm_span,primeProductNorm]

omit [∀i,(Ideal.span {p i}).IsMaximal] in

theorem parentCell_cube_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ)
    (Z ell eta : ℝ)
    (hQ : ∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta))
    (x : Source ι 0) (hx : x∈parentCell p pool Q selector k l) :
    ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤ Z^(ell+eta) ∧
    ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤ Z^(ell+eta) := by
  obtain ⟨o,ho,D,hD,hs,rfl⟩:=(mem_parentCell p pool Q selector k l x).mp hx
  exact reopenedCubeFamily_cube_norms p Q _ hQ o.1
    ((mem_firstOriginalOuter pool Q o).mp (Finset.mem_filter.mp ho).1).1

def dyadicExponent (Z : ℝ) (n : ℕ) : ℝ := Real.logb Z (dyadScale n)

lemma rpow_dyadicExponent (Z : ℝ) (hZ : 1<Z) (n : ℕ) :
    Z^dyadicExponent Z n=dyadScale n :=
  Real.rpow_logb (by linarith) (by linarith) (dyadScale_pos n)

lemma dyad_power_bounds (Z eta q : ℝ) (hZ : 1<Z) (h2 : 2≤ Z^eta) (n : ℕ)
    (hq : dyadScale n≤ q ∧ q≤2*dyadScale n) :
    Z^dyadicExponent Z n≤ q ∧ q≤ Z^(dyadicExponent Z n+eta) := by
  rw [Real.rpow_add (by linarith),rpow_dyadicExponent Z hZ]
  refine ⟨hq.1,hq.2.trans ?_⟩
  nlinarith [dyadScale_pos n]

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem parentCell_norm_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ)
    (Z eta : ℝ) (hZ : 1<Z) (h2 : 2≤ Z^eta)
    (x : Source ι 0) (hx : x∈parentCell p pool Q selector k l) :
    (∀i : Fin 5,Z^dyadicExponent Z (k i.castSucc)≤ outerNorms p (toOriginal x) i ∧
      outerNorms p (toOriginal x) i≤ Z^(dyadicExponent Z (k i.castSucc)+eta)) ∧
    (Ideal.absNorm (parent p x).quotient:ℝ)=primeProductNorm p x.quotientSupport ∧
    Z^dyadicExponent Z l≤(Ideal.absNorm (parent p x).quotient:ℝ) ∧
    (Ideal.absNorm (parent p x).quotient:ℝ)≤ Z^(dyadicExponent Z l+eta) := by
  obtain ⟨o,ho,D,hD,hs,rfl⟩:=(mem_parentCell p pool Q selector k l x).mp hx
  have hg := outerGate_dyads p hp k o (Finset.mem_filter.mp ho).2
  have hd := live_common_dyads p hp (selector o) l D hs
  simp only [toOriginal_fill,toOriginal_ofOriginal]
  refine ⟨fun i=>dyad_power_bounds Z eta _ hZ h2 _ (hg i),sourceIdeal_norm p D,?_⟩
  change Z^dyadicExponent Z l≤(Ideal.absNorm (sourceIdeal p D):ℝ) ∧
    (Ideal.absNorm (sourceIdeal p D):ℝ)≤ Z^(dyadicExponent Z l+eta)
  rw [sourceIdeal_norm]
  exact dyad_power_bounds Z eta _ hZ h2 l hd

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem parentCell_ideal_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ)
    (Z eta : ℝ) (hZ : 1<Z) (h2 : 2≤ Z^eta)
    (x : Source ι 0) (hx : x∈parentCell p pool Q selector k l) :
    (Z^dyadicExponent Z (k 2)≤ primeProductNorm p x.firstCommon ∧
      primeProductNorm p x.firstCommon≤ Z^(dyadicExponent Z (k 2)+eta)) ∧
    (Z^dyadicExponent Z (k 3)≤(Ideal.absNorm (sourceIdeal p x.firstDivisor):ℝ) ∧
      (Ideal.absNorm (sourceIdeal p x.firstDivisor):ℝ)≤ Z^(dyadicExponent Z (k 3)+eta)) ∧
    (Z^dyadicExponent Z (k 4)≤(Ideal.absNorm (sourceIdeal p (cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)):ℝ) ∧
      (Ideal.absNorm (sourceIdeal p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)):ℝ)
        ≤ Z^(dyadicExponent Z (k 4)+eta)) := by
  have h:=(parentCell_norm_bounds p hp pool Q selector k l Z eta hZ h2 x hx).1
  refine ⟨h 2,?_,?_⟩
  · simpa [sourceIdeal_norm,outerNorms,toOriginal,primeProductNorm] using h 3
  · simpa [sourceIdeal_norm,outerNorms,toOriginal] using h 4

def jNorm (p : ι→O) (x : FirstOriginalOuter ι) : ℝ :=
  ‖ringComplex (jLabel p x.1.support (fun i=>x.1.leftExponent i+x.1.rightExponent i)
    x.1.leftBit x.1.rightBit)‖^2

def labelParentCell (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l j : ℕ) :=
  (parentCell p pool Q selector k l).filter (fun x=>dyadIndex (jNorm p (toOriginal x))=j)

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem labelParentCell_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l j : ℕ)
    (Z eta : ℝ) (hZ : 1<Z) (h2 : 2≤ Z^eta)
    (x : Source ι 0) (hx : x∈labelParentCell p pool Q selector k l j) :
    x∈parentCell p pool Q selector k l ∧
    Z^dyadicExponent Z j≤ jNorm p (toOriginal x) ∧
      jNorm p (toOriginal x)≤ Z^(dyadicExponent Z j+eta) := by
  obtain ⟨hm,hj⟩:=Finset.mem_filter.mp hx
  have hn : 1≤ jNorm p (toOriginal x) :=
    SecondPassArithmetic.element_norm_ge_one _ (primeProduct_ne_zero p hp _ _)
  have hd:=dyadIndex_bounds _ hn
  rw [hj] at hd
  exact ⟨hm,dyad_power_bounds Z eta _ hZ h2 j ⟨hd.1,hd.2.le⟩⟩

theorem raw_column_exponent (Z r : ℝ) (hZ : 1<Z) (a b c : ℕ) :
    Z^r/(dyadScale a*dyadScale b*dyadScale c)=
      Z^(r-dyadicExponent Z a-dyadicExponent Z b-dyadicExponent Z c) := by
  simp only [Real.rpow_sub (show 0<Z by linarith),rpow_dyadicExponent Z hZ]
  simp only [div_div]

theorem columnScales_exponents (Z r : ℝ) (hZ : 1<Z) (k : SourceIndex) (l : ℕ) :
    columnScales k l (Z^r) (Z^r)=rawScales k l
      (Z^(r-dyadicExponent Z (k 0)-dyadicExponent Z (k 2)-dyadicExponent Z l))
      (Z^(r-dyadicExponent Z (k 1)-dyadicExponent Z (k 2)-dyadicExponent Z l)) := by
  simp only [columnScales,raw_column_exponent Z r hZ]

theorem columnScales_products (Z r : ℝ) (k : SourceIndex) (l : ℕ) :
    let s:=columnScales k l (Z^r) (Z^r)
    s 0*s 2*s 5*s 7=Z^r ∧ s 1*s 2*s 5*s 8=Z^r :=
  ⟨columnScales_left k l _ _,columnScales_right k l _ _⟩

theorem sourceCell_parent (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) (k : SourceIndex)
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (l : ℕ)
    (x : Σ _ : FirstOriginalOuter ι,Ideal O×O)
    (hx : x∈sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y) k)
    (D : Finset ι) (hD : D⊆pool) (hs : commonSelector p (selector x.1) l D≠0) :
    fillFirstQuotient (ofOriginal x.1) D∈parentCell p pool Q selector k l :=
  (mem_parentCell p pool Q selector k l _).mpr
    ⟨x.1,sourceCell_outer p pool Q labels Y k x hx,D,Finset.mem_powerset.mpr hD,hs,rfl⟩

theorem outerCell_eq_of_first_five (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (k k' : SourceIndex) (h : ∀i : Fin 5,k i.castSucc=k' i.castSucc) :
    outerCell p pool Q k=outerCell p pool Q k' := by
  ext x
  simp only [outerCell, Finset.mem_filter, outerGate, h]

omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma live_selector_norm_le_one (selector : Finset ι→ℂ)
    (hs : ∀D,‖selector D‖≤1) (l : ℕ) (D : Finset ι) :
    ‖commonSelector p selector l D‖≤1 := (commonSelector_norm p selector l D).trans (hs D)

include hp in

theorem sourceCell_actual_ratios
    (hg : ∀i,lambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O)) (Y : ℝ)
    (selector C₁ C₂ : (Σ _ : FirstOriginalOuter ι,Ideal O×O)→Finset ι→ℂ)
    (k : SourceIndex) (l : ℕ) (T₁ T₂ : ℝ)
    (x : Σ _ : FirstOriginalOuter ι,Ideal O×O)
    (hx : x∈sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y) k)
    (j : FirstCommonIndex ι)
    (hn : commonSelector p (selector x) l j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j≠0) :
    ∀i,actualOuterRatios p (outerNorms p x.1 0) (outerNorms p x.1 1)
      (outerNorms p x.1 2) (outerNorms p x.1 4)
      ((∏ i ∈ x.1.2.2,p i)) x.2.2 j (rawScales k l T₁ T₂) i∈Set.Icc 1 2 := by
  exact actual_original_cell_ratios p hp hg _ selector C₁ C₂
    (fun y=>outerNorms p y.1 0) (fun y=>outerNorms p y.1 1)
    (fun y=>outerNorms p y.1 2) (fun y=>outerNorms p y.1 4)
    (fun y=>(∏ i ∈ y.1.2.2,p i)) (fun y=>y.2.2)
    (source_norms_ge_one p hp pool Q labels Y) k l T₁ T₂ x hx j hn

end InverseFirstGlobalCaps

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

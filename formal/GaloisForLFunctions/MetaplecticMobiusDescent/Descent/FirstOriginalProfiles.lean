/-
First original profiles adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.SecondCellPhysicalPartition

/-!
# First original profiles

Coefficients, summands and divisor elements of the first original profile
(`InverseMomentFirstOriginalProfile`); column centers, scalar caps and the choice of the first
tail order.
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
namespace InverseMomentFirstOriginalProfile
open InverseMoment Eisenstein FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
open CompletedHeight
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
abbrev OriginalIndex (ι : Type*) := Σ _ : FirstOriginalOuter ι,Ideal O×O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

def leftNorm (x : OriginalIndex ι) : ℝ := ‖ringComplex (aLabel p x.1.1.support x.1.1.rightBit)‖^2
def rightNorm (x : OriginalIndex ι) : ℝ := ‖ringComplex (aLabel p x.1.1.support x.1.1.leftBit)‖^2
def commonNorm (x : OriginalIndex ι) : ℝ := primeProductNorm p x.1.2.1
def activeNorm (x : OriginalIndex ι) : ℝ := primeProductNorm p (cubeActiveSupport x.1.1.support
  (fun i=>x.1.1.leftExponent i+x.1.1.rightExponent i) x.1.1.leftBit x.1.1.rightBit)
def divisorElement (k : FirstOriginalOuter ι) : O := (∏ i ∈ k.2.2,p i)

include hp in
theorem original_source_positive (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) :
    ∀x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun k=>k.1) Y,
      0<leftNorm p x ∧ 0<rightNorm p x ∧ 0<commonNorm p x ∧ 0<activeNorm p x ∧
      divisorElement p x.1≠0 ∧ x.2.2≠0 := by
  intro x hx
  have hm := (Finset.mem_sigma.mp hx).2
  have hk := ((mem_firstRetainedSource p labels x.1.1 Y x.2).mp hm).2
  refine ⟨?_,?_,primeProductNorm_pos p hp _,primeProductNorm_pos p hp _,?_,(Finset.mem_erase.mp hk).1⟩
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero
      (primeProduct_ne_zero p hp _ _)))
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero
      (primeProduct_ne_zero p hp _ _)))
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)

include hp in
theorem original_source_norms_ge_one (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) :
    ∀x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun k=>k.1) Y,
      ∀i,1≤ InverseMomentFirstChildWindows.sourceNorms (leftNorm p) (rightNorm p) (commonNorm p)
        (activeNorm p) (fun x=>divisorElement p x.1) (fun x=>x.2.2) x i := by
  intro x hx
  have hh := original_source_positive p hp pool Q labels Y x hx
  apply InverseMomentFirstChildWindows.sourceNorms_ge_one
  · exact element_norm_ge_one _ (primeProduct_ne_zero p hp _ _)
  · exact element_norm_ge_one _ (primeProduct_ne_zero p hp _ _)
  · exact primeProductNorm_ge_one p hp _
  · exact primeProductNorm_ge_one p hp _
  · exact hh.2.2.2.2.1
  · exact hh.2.2.2.2.2

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem original_weight_bound (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (β : Ideal O→(ι→₀ℕ)→ℂ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ) (Γ Y : ℝ)
    (hΓ : 0≤Γ) (hβ : ∀I∈labels,∀v∈Q,‖β I v‖≤Γ) :
    ∀k∈firstOriginalOuter pool Q,∀x∈firstRetainedSource p labels k.1 Y,
      ‖firstOriginalWeight p β R k x‖≤Γ^2 := by
  intro k hk x hx
  have hb := (mem_firstOriginalOuter pool Q k).mp hk
  have hf := ((mem_firstRetainedSource p labels k.1 Y x).mp hx).1
  exact (firstOriginalWeight_norm_le p β R k x).trans
    (reopenedPairCoefficient_bound Q labels β Γ hΓ hβ k.1 hb.1 k.2.1 x.1 hf)

theorem actual_old_profile (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om⊆Set.Icc a b) (theta x : ℝ) (hx : 0<x) :
    InverseMomentFirstProfileUniform.positiveSource (priorityLogWindow om a b ha hs false) 1 theta x=
      normTwistedSource om theta x ∧
    InverseMomentFirstProfileUniform.positiveSource (priorityLogWindow om a b ha hs true) 1 (-theta) x=
      star (normTwistedSource om theta x) := by
  constructor
  · simp [InverseMomentFirstProfileUniform.positiveSource,priorityLogWindow,
      CanonicalCubeSeparation.sourceLogProfile_apply,Real.exp_log hx,normTwistedSource]
  · simp [InverseMomentFirstProfileUniform.positiveSource,priorityLogWindow,
      SecondPassIntegration.conjugateProfile_apply,CanonicalCubeSeparation.sourceLogProfile_apply,
      Real.exp_log hx,normTwistedSource,JointLogSeparation.kernelLogPhase_conjugate]

end InverseMomentFirstOriginalProfile
end

noncomputable section
namespace InverseMomentFirstOriginalProfile
open InverseMoment Eisenstein FirstPassCubeLabels SecondPassArithmetic
open CompletedHeight
open InverseMomentFirstProfileUniform
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι κ : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hg : ∀i,lambda∉Ideal.span {p i})

include hp in
lemma physical_rows_congr_positive (F : Finset ι) (selector C₁ C₂ : Finset ι→ℂ)
    (W₁ W₂ V₁ V₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R K : ℝ) (d h : O)
    (hA₁ : 0<A₁) (hA₂ : 0<A₂) (hC : 0<C)
    (h₁ : ∀x,0<x→W₁ x=V₁ x) (h₂ : ∀x,0<x→W₂ x=V₂ x) :
    firstBlockedPhysicalRows p hg F selector C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h=
      firstBlockedPhysicalRows p hg F selector C₁ C₂ V₁ V₂ Φ A₁ A₂ C R K d h := by
  unfold firstBlockedPhysicalRows
  apply Finset.sum_congr rfl
  intro j hj
  have he₁ := h₁ (A₁*C*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1)
    (mul_pos (mul_pos (mul_pos hA₁ hC) (primeProductNorm_pos p hp _)) (primeProductNorm_pos p hp _))
  have he₂ := h₂ (A₂*C*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2)
    (mul_pos (mul_pos (mul_pos hA₂ hC) (primeProductNorm_pos p hp _)) (primeProductNorm_pos p hp _))
  simp [firstNormProfile,firstCommonNorms,he₁,he₂]

include hp in
lemma physical_family_congr_positive (S : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ→Finset ι→ℂ) (w : κ→ℂ)
    (W₁ W₂ V₁ V₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R : κ→ℝ) (K : ℝ)
    (d h : κ→O) (s : Fin 9→ℝ) (hs : ∀i,0<s i)
    (hpos : ∀x∈S,0<A₁ x ∧ 0<A₂ x ∧ 0<C x)
    (h₁ : ∀x,0<x→W₁ x=V₁ x) (h₂ : ∀x,0<x→W₂ x=V₂ x) :
    firstFamilyPhysicalRows p hg S F selector C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h s=
      firstFamilyPhysicalRows p hg S F selector C₁ C₂ w V₁ V₂ Φ A₁ A₂ C R K d h s := by
  unfold firstFamilyPhysicalRows
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  exact physical_rows_congr_positive p hp hg F (selector x) (C₁ x) (C₂ x) _ _ _ _ Φ
    (A₁ x) (A₂ x) (C x) (R x) K (d x) (h x) (hpos x hx).1 (hpos x hx).2.1 (hpos x hx).2.2
    (fun y hy=>h₁ _ (div_pos hy (mul_pos (mul_pos (mul_pos (hs 0) (hs 2)) (hs 5)) (hs 7))))
    (fun y hy=>h₂ _ (div_pos hy (mul_pos (mul_pos (mul_pos (hs 1) (hs 2)) (hs 5)) (hs 8))))

include hp in

theorem original_family_profiles (S : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ→Finset ι→ℂ) (w : κ→ℂ)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hsom : Function.support om⊆Set.Icc a b)
    (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R : κ→ℝ) (K X theta : ℝ)
    (d h : κ→O) (s : Fin 9→ℝ) (hs : ∀i,0<s i)
    (hpos : ∀x∈S,0<A₁ x ∧ 0<A₂ x ∧ 0<C x)
    (hX : 0<X) (hleft : s 0*s 2*s 5*s 7=X) (hright : s 1*s 2*s 5*s 8=X) :
    firstFamilyPhysicalRows p hg S F selector C₁ C₂ w
      (fun y=>star (normTwistedSource om theta ((s 0*s 2*s 5*s 7)*y/X)))
      (fun y=>normTwistedSource om theta ((s 1*s 2*s 5*s 8)*y/X)) Φ A₁ A₂ C R K d h s=
    firstFamilyPhysicalRows p hg S F selector C₁ C₂ w
      (positiveSource (priorityLogWindow om a b ha hsom true) 1 (-theta))
      (positiveSource (priorityLogWindow om a b ha hsom false) 1 theta) Φ A₁ A₂ C R K d h s := by
  apply physical_family_congr_positive p hp hg S F selector C₁ C₂ w _ _ _ _ Φ A₁ A₂ C R K d h s hs hpos
  · intro y hy
    rw [hleft,mul_div_cancel_left₀ y (ne_of_gt hX)]
    exact (actual_old_profile om a b ha hsom theta y hy).2.symm
  · intro y hy
    rw [hright,mul_div_cancel_left₀ y (ne_of_gt hX)]
    exact (actual_old_profile om a b ha hsom theta y hy).1.symm

end InverseMomentFirstOriginalProfile
end

noncomputable section
namespace InverseMomentFirstOriginalProfile
open InverseMoment Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseSecondSourceBlocks
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

def originalNorms (x : OriginalIndex ι) : Fin 6→ℝ :=
  sourceNorms (leftNorm p) (rightNorm p) (commonNorm p) (activeNorm p)
    (fun x=>divisorElement p x.1) (fun x=>x.2.2) x

def originalOuterCell (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) :
    Finset (FirstOriginalOuter ι) :=
  (firstOriginalOuter pool Q).filter (fun x=>∀i:Fin 5,
    dyadIndex (originalNorms p ⟨x,(1,1)⟩ i.castSucc)=k i.castSucc)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma originalNorms_outer (x : OriginalIndex ι) (i : Fin 5) :
    originalNorms p ⟨x.1,(1,1)⟩ i.castSucc=originalNorms p x i.castSucc := by
  unfold originalNorms sourceNorms
  fin_cases i <;> simp [Fin.castSucc,leftNorm,rightNorm,commonNorm,activeNorm]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem original_cell_subset (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) (k : SourceIndex) :
    sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) k ⊆
    firstGlobalRetainedSource p (originalOuterCell p pool Q k) (fun _=>labels) (fun x=>x.1) Y := by
  intro x hx
  obtain ⟨hxs,hk⟩ := Finset.mem_filter.mp hx
  obtain ⟨ho,hf⟩ := Finset.mem_sigma.mp hxs
  apply Finset.mem_sigma.mpr
  refine ⟨Finset.mem_filter.mpr ⟨ho,?_⟩,hf⟩
  intro i
  rw [originalNorms_outer p x i]
  exact congrFun hk i.castSucc

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma original_outer_cell_subset (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) :
    originalOuterCell p pool Q k⊆firstOriginalOuter pool Q := Finset.filter_subset _ _

theorem original_outer_cell_ratios (hp : ∀i,p i≠0)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex)
    (x : FirstOriginalOuter ι) (hx : x∈originalOuterCell p pool Q k) (i : Fin 5) :
    originalNorms p ⟨x,(1,1)⟩ i.castSucc/dyadScale (k i.castSucc)∈Set.Icc 1 2 := by
  have hnorm : ∀j:Fin 6,1≤ originalNorms p ⟨x,(1,1)⟩ j := by
    apply sourceNorms_ge_one
    · exact element_norm_ge_one _ (primeProduct_ne_zero p hp _ _)
    · exact element_norm_ge_one _ (primeProduct_ne_zero p hp _ _)
    · exact primeProductNorm_ge_one p hp _
    · exact primeProductNorm_ge_one p hp _
    · exact Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
    · exact one_ne_zero
  have hh := dyadIndex_bounds _ (hnorm i.castSucc)
  rw [(Finset.mem_filter.mp hx).2 i] at hh
  exact ⟨(le_div_iff₀ (dyadScale_pos _)).mpr (by simpa using hh.1),
    (div_le_iff₀ (dyadScale_pos _)).mpr hh.2.le⟩

end InverseMomentFirstOriginalProfile
end

noncomputable section
namespace InverseMomentFirstOriginalProfile
open InverseMoment Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows CompletedHeight
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg : ∀i,lambda∉Ideal.span {p i})

def coefficient (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (negative : Bool)
    (x : OriginalIndex ι) : Finset ι→ℂ :=
  firstCanonicalCoefficient p hg x.1.1 x.1.2.1 negative Ψ m (divisorElement p x.1)
    (mark (if negative then x.1.1.rightExponent else x.1.1.leftExponent)) x.2

def weight (β : Ideal O→(ι→₀ℕ)→ℂ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ) (Ψ : O→*ℂ) (m : O)
    (x : OriginalIndex ι) : ℂ :=
  retainedCubeWeight p hp hg x.1.1 x.1.2.1 Ψ Ψ m m
    (divisorElement p x.1) (firstOriginalWeight p β R x.1) x.2

def sourceSummand (β : Ideal O→(ι→₀ℕ)→ℂ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (x : OriginalIndex ι) (j : FirstCommonIndex ι) : ℂ :=
  weight p hp hg β R Ψ m x *
    firstCommonWeight p hg (coefficient p hg Ψ m mark true x)
      (coefficient p hg Ψ m mark false x) x.2.2 j *
    firstNormProfile (fun y=>star (W y)) W Φ (fun _ _=>1) K
      (firstCommonNorms p (leftNorm p x) (rightNorm p x) (commonNorm p x) (activeNorm p x)
        (divisorElement p x.1) x.2.2 j)

theorem original_retained_sum (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ) (s : Fin 9→ℝ) (hs : ∀i,0<s i) :
    originalRetainedFamily p hp hg pool Q labels β Ψ m mark W Φ K Y R s=
      ∑x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y,
        ∑j∈firstCommonIndices pool,sourceSummand p hp hg β R Ψ m mark W Φ K x j := by
  have hleft : s 0*s 2*s 5*s 7≠0 := ne_of_gt (mul_pos (mul_pos (mul_pos (hs 0) (hs 2)) (hs 5)) (hs 7))
  have hright : s 1*s 2*s 5*s 8≠0 := ne_of_gt (mul_pos (mul_pos (mul_pos (hs 1) (hs 2)) (hs 5)) (hs 8))
  simp only [originalRetainedFamily,firstFamilyPhysicalRows,firstBlockedPhysicalRows,
    Finset.mul_sum,sourceSummand,weight,coefficient,leftNorm,rightNorm,commonNorm,activeNorm,divisorElement,
    Bool.false_eq_true,ite_true,ite_false,one_mul]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro j hj
  simp only [firstNormProfile,mul_div_cancel₀ _ hleft,mul_div_cancel₀ _ hright]
  ring

theorem original_retained_cell_partition (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ) (s : Fin 9→ℝ) (hs : ∀i,0<s i) :
    let source := firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y
    let term := sourceSummand p hp hg β R Ψ m mark W Φ K
    originalRetainedFamily p hp hg pool Q labels β Ψ m mark W Φ K Y R s=
      ∑k∈sourceKeys (originalNorms p) source,∑l∈liveCommonKeys p pool source (fun _ _=>1) term,
        ∑x∈sourceCell (originalNorms p) source k,∑j∈firstCommonIndices pool,
          commonSelector p (fun _=>1) l j.2.1*term x j := by
  intro source term
  rw [original_retained_sum p hp hg pool Q labels β Ψ m mark W Φ K Y R s hs]
  simpa only [one_mul] using original_live_signed_partition p pool source (originalNorms p) (fun _ _=>1) term

end InverseMomentFirstOriginalProfile
end

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic SchwartzPlanePoisson
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

theorem canonicalCubeOuter_norm_le_one_of_good
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (b : CubeCoordinates ι) (C : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (hΨ₁ : ∀ u,‖Ψ₁ u‖ ≤ 1) (hΨ₂ : ∀ u,‖Ψ₂ u‖ ≤ 1) (m₁ m₂ f : O) :
    ‖canonicalCubeOuter p hg b C Ψ₁ Ψ₂ m₁ m₂ f‖ ≤ 1 := by
  have hsource (Ψ : O →* ℂ) (hΨ : ∀ u, ‖Ψ u‖ ≤ 1) (m f : O) (S : Finset ι) :
      ‖canonicalSourceCoefficient p hg Ψ m f (fun _ => 1) S‖ ≤ 1 := by
    have hm := primeCoprimeMask_norm_le_one p S m
    have hr := primeSubsetRow_norm_le_one p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S f
    simp only [canonicalSourceCoefficient,norm_mul,norm_pow,norm_one,mul_one,
      secondColumnCoefficient_norm_one_of_good p hp hinj hg hc S,one_mul]
    calc
      ‖Ψ (∏ i ∈ S,p i)‖ * ‖primeCoprimeMask p S m‖ *
          ‖primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S f‖^4
        ≤ 1 * 1 * 1^4 := by gcongr <;> exact hΨ _
      _ = 1 := by norm_num
  show ‖canonicalCubeOuter p hg b C Ψ₁ Ψ₂ m₁ m₂ f‖ ≤ 1
  simp only [canonicalCubeOuter,norm_mul,norm_star]
  exact (mul_le_mul (hsource Ψ₁ hΨ₁ _ _ _) (hsource Ψ₂ hΨ₂ _ _ _)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)


theorem canonicalCubeDualZero_norm_le_of_good
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (hΨ₁ : ∀u,‖Ψ₁ u‖≤1) (hΨ₂ : ∀u,‖Ψ₂ u‖≤1)
    (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    ‖canonicalCubeDualZero p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K‖≤
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        ‖H₁ (b.rightDivisor∪C)‖*‖H₂ (b.leftDivisor∪C)‖*|K| *‖paperRadialFourier W 0‖ else 0 := by
  have hout := canonicalCubeOuter_norm_le_one_of_good p hp hg hinj hc b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ f
  rw [canonicalCubeDualZero_eq_density p hp hg hinj]
  split_ifs with hB
  · let M := C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit
    have hprod : (∏i∈M,(1-(1:ℂ)/Ideal.absNorm (Ideal.span {p i})))=
        ((∏i∈M,(1-(1:ℝ)/Ideal.absNorm (Ideal.span {p i}))):ℝ) := by
      simp only [Complex.ofReal_prod,Complex.ofReal_sub,Complex.ofReal_one,
        Complex.ofReal_div,Complex.ofReal_natCast]
    rw [show (C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)=M from rfl,hprod]
    simp only [norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (primeDensity_nonneg_le_one p M).1]
    calc
      _ ≤ 1*(‖H₁ (b.rightDivisor∪C)‖*‖H₂ (b.leftDivisor∪C)‖)*|K| *‖paperRadialFourier W 0‖*
          ∏i∈M,(1-(1:ℝ)/Ideal.absNorm (Ideal.span {p i})) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                hout
                (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (abs_nonneg _)) (norm_nonneg _))
          (primeDensity_nonneg_le_one p M).1
      _ ≤ _ := by
        simpa only [one_mul] using mul_le_of_le_one_right
          (show 0≤(1*(‖H₁ (b.rightDivisor∪C)‖*‖H₂ (b.leftDivisor∪C)‖)*|K| *‖paperRadialFourier W 0‖) by positivity)
          (primeDensity_nonneg_le_one p M).2
  · simp

theorem first_marked_zero_uniform (ε : ℝ) (hε : 0<ε) :
    ∃ Cm : ℝ,0<Cm ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,lambda∉Ideal.span {p i})
      (_hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
      (Ψ₁ Ψ₂ : O→*ℂ),(∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      ∀ (m₁ m₂ f : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists → (∀ i∈slots,∀ k∈lists i,‖a i k‖≤1) →
      ∀ (test₁ test₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (G₁ G₂ L K : ℝ),0≤ G₁ → 0≤ G₂ → 0≤ L →
      (∀ U,‖test₁ U‖≤ G₁) → (∀ U,‖test₂ U‖≤ G₂) →
      (∀ U,test₁ U≠0 → primeProductNorm p U≤ L) →
      (∀ U,test₂ U≠0 → primeProductNorm p U≤ L) →
      ‖canonicalCubeDualZero p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂ f
        (wholeMarkedTest slots lists a test₁) (wholeMarkedTest slots lists a test₂) W K‖ ≤
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        (Cm*L^ε*G₁)*(Cm*L^ε*G₂) * |K| * ‖paperRadialFourier W 0‖ else 0 := by
  obtain ⟨Cm,hCm,hmark⟩ := whole_marked_test_uniform ε hε
  refine ⟨Cm,hCm,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hc pool b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ f slots lists a hslots ha
    test₁ test₂ W G₁ G₂ L K hG₁ hG₂ hL ht₁ ht₂ hs₁ hs₂
  apply (canonicalCubeDualZero_norm_le_of_good p hp hg hinj hc pool b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ f _ _ W K).trans
  split_ifs
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul (hmark p hp hcop slots lists a hslots ha test₁ G₁ L hG₁ hL ht₁ hs₁ _)
        (hmark p hp hcop slots lists a hslots ha test₂ G₂ L hG₂ hL ht₂ hs₂ _)
        (norm_nonneg _) (by positivity)) (abs_nonneg _)) (norm_nonneg _)
  · exact le_rfl

end
end InverseMoment

namespace InverseMoment
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

theorem primeProductNorm_union_le_mul {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal] (A U : Finset ι) :
    primeProductNorm p (A∪U)≤ primeProductNorm p A*primeProductNorm p U := by
  have he : A∪U=A∪(U\A) := by ext i;simp only [Finset.mem_union,Finset.mem_sdiff];tauto
  rw [he,primeProductNorm_union p A (U\A) Finset.disjoint_sdiff]
  exact mul_le_mul_of_nonneg_left (primeProductNorm_mono p hp Finset.sdiff_subset)
    (primeProductNorm_pos p hp A).le

theorem whole_cube_marked_test_uniform (ε : ℝ) (hε : 0<ε) :
    ∃ Cm : ℝ,0<Cm ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (_hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists → (∀ i∈slots,∀ k∈lists i,‖a i k‖≤1) →
      ∀ (extra : Finset ι) (test : Finset ι→ℂ) (E G L : ℝ),0≤ E → 0≤ G → 0≤ L →
      primeProductNorm p extra≤ E → (∀ U,‖test U‖≤ G) →
      (∀ U,test U≠0→primeProductNorm p U≤ L) →
      ∀ U,‖primeMark slots lists a (extra∪U)*test U‖≤ Cm*(E*L)^ε*G := by
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_small_power ε hε
  refine ⟨Cm,hCm,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha extra test E G L hE hG hL he hb hs U
  by_cases hz : test U=0
  · simp only [hz,mul_zero,norm_zero];positivity
  have hnorm : primeProductNorm p (extra∪U)≤ E*L :=
    (primeProductNorm_union_le_mul p hp extra U).trans
      (mul_le_mul he (hs U hz) (primeProductNorm_pos p hp U).le hE)
  have hnorm0 := (primeProductNorm_pos p hp (extra∪U)).le
  rw [norm_mul]
  calc
    _ ≤ (Cm*(primeProductNorm p (extra∪U))^ε)*G :=
      mul_le_mul (hmark p hp hcop slots lists a hslots ha _) (hb U) (norm_nonneg _) (by positivity)
    _ ≤ _ := by gcongr

theorem first_whole_cube_marked_zero_uniform (ε : ℝ) (hε : 0<ε) :
    ∃ Cm : ℝ,0<Cm ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,lambda∉Ideal.span {p i})
      (_hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι) (b : CubeCoordinates ι) (C extra₁ extra₂ : Finset ι)
      (Ψ₁ Ψ₂ : O→*ℂ),(∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      ∀ (m₁ m₂ f : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists → (∀ i∈slots,∀ k∈lists i,‖a i k‖≤1) →
      ∀ (test₁ test₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (E G₁ G₂ L K : ℝ),
      0≤ E → 0≤ G₁ → 0≤ G₂ → 0≤ L → primeProductNorm p extra₁≤ E → primeProductNorm p extra₂≤ E →
      (∀ U,‖test₁ U‖≤ G₁) → (∀ U,‖test₂ U‖≤ G₂) →
      (∀ U,test₁ U≠0→primeProductNorm p U≤ L) → (∀ U,test₂ U≠0→primeProductNorm p U≤ L) →
      ‖canonicalCubeDualZero p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂ f
        (fun U=>primeMark slots lists a (extra₁∪U)*test₁ U)
        (fun U=>primeMark slots lists a (extra₂∪U)*test₂ U) W K‖ ≤
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        (Cm*(E*L)^ε*G₁)*(Cm*(E*L)^ε*G₂) * |K| * ‖SchwartzPlanePoisson.paperRadialFourier W 0‖ else 0 := by
  obtain ⟨Cm,hCm,hmark⟩ := whole_cube_marked_test_uniform ε hε
  refine ⟨Cm,hCm,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hc pool b C extra₁ extra₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m₁ m₂ f slots lists a hslots ha test₁ test₂ W E G₁ G₂ L K hE hG₁ hG₂ hL he₁ he₂ hb₁ hb₂ hs₁ hs₂
  apply (canonicalCubeDualZero_norm_le_of_good p hp hg hinj hc pool b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ f _ _ W K).trans
  split_ifs
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul (hmark p hp hcop slots lists a hslots ha extra₁ test₁ E G₁ L hE hG₁ hL he₁ hb₁ hs₁ _)
        (hmark p hp hcop slots lists a hslots ha extra₂ test₂ E G₂ L hE hG₂ hL he₂ hb₂ hs₂ _)
        (norm_nonneg _) (by positivity)) (abs_nonneg _)) (norm_nonneg _)
  · exact le_rfl

end
end InverseMoment

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic InverseInitialArithmetic
open Eisenstein (ringComplex)
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀ i,p i≠0)

include hp in
theorem cube_whole_support_norm (b : CubeCoordinates ι) :
    primeProductNorm p b.support≤
      ‖ringComplex (primeProduct p b.support b.leftExponent)‖^2*
      ‖ringComplex (primeProduct p b.support b.rightExponent)‖^2 := by
  have hd := cubeRadical_span_dvd_product p b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.support_pos
  have hne : (Ideal.span {primeProduct p b.support (fun i=>b.leftExponent i+b.rightExponent i)}:Ideal O)≠0 :=
    Ideal.span_singleton_eq_bot.not.mpr (primeProduct_ne_zero p hp _ _)
  have hn := Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hne))
    (Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hd))
  have he : (Ideal.absNorm (sourceIdeal p b.support):ℝ)=primeProductNorm p b.support := by
    simpa only [sourceIdeal,primeProductNorm,map_prod] using
      (ringComplex_norm_sq_eq_absNorm_span (∏i∈b.support,p i)).symm
  have hh : primeProductNorm p b.support≤
      ‖ringComplex (primeProduct p b.support (fun i=>b.leftExponent i+b.rightExponent i))‖^2 := by
    rw [ringComplex_norm_sq_eq_absNorm_span,←he]
    exact_mod_cast hn
  simpa only [primeProduct_add,map_mul,norm_mul,mul_pow] using hh

include hp in
theorem cube_whole_support_dyad (b : CubeCoordinates ι) (B : ℝ) (hB : 0≤ B)
    (hl : ‖ringComplex (primeProduct p b.support b.leftExponent)‖^2≤ B)
    (hr : ‖ringComplex (primeProduct p b.support b.rightExponent)‖^2≤ B) :
    primeProductNorm p b.support≤ B^2 :=
  (cube_whole_support_norm p hp b).trans ((mul_le_mul hl hr (sq_nonneg _) hB).trans_eq (pow_two B).symm)

end InverseMoment

end

noncomputable section
namespace InverseMomentFirstLiveCaps
open InverseMoment InverseMomentFirstOriginalProfile Eisenstein FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O"=>Eisenstein.O

lemma factor_four_bound (a b c d L:ℝ)(ha:1≤ a)(hb:1≤ b)(hc:1≤ c)(hd:1≤ d)
    (h:a*b*c*d≤ L): a≤ L ∧ b≤ L ∧ c≤ L ∧ d≤ L:=by
  have ha0:0≤ a:=zero_le_one.trans ha
  have hb0:0≤ b:=zero_le_one.trans hb
  have hc0:0≤ c:=zero_le_one.trans hc
  have hd0:0≤ d:=zero_le_one.trans hd
  have hab:1≤ a*b:=ha.trans (le_mul_of_one_le_right ha0 hb)
  have habc:1≤ a*b*c:=hab.trans (le_mul_of_one_le_right (mul_nonneg ha0 hb0) hc)
  have habd:1≤ a*b*d:=hab.trans (le_mul_of_one_le_right (mul_nonneg ha0 hb0) hd)
  have ha':a≤ a*b*c*d:=by
    calc
      a≤ a*b:=le_mul_of_one_le_right ha0 hb
      _≤ a*b*c:=le_mul_of_one_le_right (mul_nonneg ha0 hb0) hc
      _≤ a*b*c*d:=le_mul_of_one_le_right (mul_nonneg (mul_nonneg ha0 hb0) hc0) hd
  have hb':b≤ a*b*c*d:=by
    calc
      b≤ a*b:=le_mul_of_one_le_left hb0 ha
      _≤ a*b*c:=le_mul_of_one_le_right (mul_nonneg ha0 hb0) hc
      _≤ a*b*c*d:=le_mul_of_one_le_right (mul_nonneg (mul_nonneg ha0 hb0) hc0) hd
  have hc':c≤ a*b*c*d:=by
    calc
      c≤ a*b*c:=le_mul_of_one_le_left hc0 hab
      _≤ a*b*c*d:=le_mul_of_one_le_right (mul_nonneg (mul_nonneg ha0 hb0) hc0) hd
  exact ⟨ha'.trans h,hb'.trans h,hc'.trans h,(le_mul_of_one_le_left hd0 habc).trans h⟩

theorem first_profile_live_factors (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(K L:ℝ)(q:Fin 9→ℝ)
    (hq:∀i,1≤ q i)(hW:∀x,W x≠0→x≤ L)
    (hn:firstNormProfile (fun y=>star (W y)) W Φ (fun _ _=>1) K q≠0):
    q 0≤ L ∧ q 1≤ L ∧ q 2≤ L ∧ q 5≤ L:=by
  have h₁:W (q 0*q 2*q 5*q 7)≠0:=by
    intro h
    apply hn
    simp [firstNormProfile,h]
  have h₂:W (q 1*q 2*q 5*q 8)≠0:=by
    intro h
    apply hn
    simp [firstNormProfile,h]
  have hb₁:=factor_four_bound (q 0) (q 2) (q 5) (q 7) L (hq _) (hq _) (hq _) (hq _) (hW _ h₁)
  have hb₂:=factor_four_bound (q 1) (q 2) (q 5) (q 8) L (hq _) (hq _) (hq _) (hq _) (hW _ h₂)
  exact ⟨hb₁.1,hb₂.1,hb₁.2.1,hb₁.2.2.1⟩

variable {ι:Type*}[DecidableEq ι]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i})

theorem original_live_profile_caps
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))(Y:ℝ)
    (β:Ideal O→(ι→₀ℕ)→ℂ)(cutoff:CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(K L:ℝ)
    (hW:∀y,W y≠0→y≤ L)(x:OriginalIndex ι)
    (hx:x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y)
    (j:FirstCommonIndex ι)
    (hn:sourceSummand p hp hg β cutoff Ψ m mark W Φ K x j≠0):
    leftNorm p x≤ L ∧ rightNorm p x≤ L ∧ commonNorm p x≤ L ∧ primeProductNorm p j.2.1≤ L:=by
  have hq:∀i,1≤ firstCommonNorms p (leftNorm p x) (rightNorm p x) (commonNorm p x) (activeNorm p x)
      (divisorElement p x.1) x.2.2 j i:=by
    have hs:=original_source_norms_ge_one p hp pool Q labels Y x hx
    intro i
    fin_cases i
    · exact hs 0
    · exact hs 1
    · exact hs 2
    · exact hs 3
    · exact hs 4
    · exact primeProductNorm_ge_one p hp _
    · exact hs 5
    · exact primeProductNorm_ge_one p hp _
    · exact primeProductNorm_ge_one p hp _
  have hprof:firstNormProfile (fun y=>star (W y)) W Φ (fun _ _=>1) K
      (firstCommonNorms p (leftNorm p x) (rightNorm p x) (commonNorm p x) (activeNorm p x)
        (divisorElement p x.1) x.2.2 j)≠0:=by
    intro hz
    exact hn (by unfold sourceSummand;rw [hz,mul_zero])
  exact first_profile_live_factors W Φ K L _ hq hW hprof

end InverseMomentFirstLiveCaps

end

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

theorem first_whole_cube_canonical_tail (ε : ℝ) (hε : 0<ε) (order : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct Cm : ℝ),0<Ct ∧ 0<Cm ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,lambda∉Ideal.span {p i})
      (_hchar : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι) (b : CubeCoordinates ι),b.Admissible →
      ∀ (common divisor : Finset ι),Disjoint common b.support →
      ∀ (f : Ideal O),f≠0 →
      ∀ (Ψ₁ Ψ₂ : O→*ℂ),(∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      ∀ (m₁ m₂ : O) (extra₁ extra₂ : Finset ι) (E : ℝ) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
      0≤ E → primeProductNorm p extra₁≤ E → primeProductNorm p extra₂≤ E →
      (slots : Set σ).PairwiseDisjoint lists → (∀ i∈slots,∀ k∈lists i,‖a i k‖≤1) →
      ∀ (test₁ test₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ))
      (G₁ G₂ Z M r ell V delta B j eta tau : ℝ),0≤ G₁ → 0≤ G₂ → 0<Z →
      (∀ U,‖test₁ U‖≤ G₁) → (∀ U,‖test₂ U‖≤ G₂) →
      (∀ U,test₁ U≠0 → primeProductNorm p U≤ Z^(r+eta)) →
      (∀ U,test₂ U≠0 → primeProductNorm p U≤ Z^(r+eta)) →
      ‖ringComplex (primeProduct p b.support b.leftExponent)‖^2≤ Z^(ell+eta) →
      ‖ringComplex (primeProduct p b.support b.rightExponent)‖^2≤ Z^(ell+eta) →
      (Ideal.absNorm f : ℝ)≤ Z^(V+eta) → primeProductNorm p divisor≤ Z^(delta+eta) →
      Z^(B-eta)≤ primeProductNorm p common →
      Z^(j-eta)≤‖ringComplex (jLabel p b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit)‖^2 →
      let residualPool := pool\(b.support∪common)
      let C₁ := canonicalCubeResidual p hg b common true Ψ₁ m₁ (cubicIdealGenerator f)
        (fun U=>primeMark slots lists a (extra₁∪U)*test₁ U)
      let C₂ := canonicalCubeResidual p hg b common false Ψ₂ m₂ (cubicIdealGenerator f)
        (fun U=>primeMark slots lists a (extra₂∪U)*test₂ U)
      let U₁ := Z^(r+eta)/(‖ringComplex (aLabel p b.support b.rightBit)‖^2*primeProductNorm p common)
      let U₂ := Z^(r+eta)/(‖ringComplex (aLabel p b.support b.leftBit)‖^2*primeProductNorm p common)
      let G₁' := Cm*(E*Z^(r+eta))^ε*G₁
      let G₂' := Cm*(E*Z^(r+eta))^ε*G₂
      let active := cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      let slow := Z^M/(primeProductNorm p divisor*primeProductNorm p active*U₁*U₂)
      let T := childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f)
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau))
      ‖∑' h : {h : O // h∉T},actualFirstKernel p hp hg residualPool b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit C₁ C₂ W
        (fun _=>1) (fun _=>1) 1 1 (Z^M)
        ((∏ i ∈ divisor,p i)) h.val‖ ≤
      ((1+diagonalControl sieveCutoff)*U₁)*((1+diagonalControl sieveCutoff)*U₂)*(G₁'*G₂'*Z^M)*
        ((Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 slow)^2*(1+Z^tau)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_first_physical_tail order
  obtain ⟨Cm,hCm,hmark⟩ := whole_cube_marked_test_uniform ε hε
  refine ⟨s,Ct,Cm,hCt,hCm,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hchar pool b hb common divisor hcommon f hf0 Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m₁ m₂ extra₁ extra₂ E slots lists a hE he₁ he₂ hslots ha test₁ test₂ W G₁ G₂ Z M r ell V delta B j eta tau hG₁ hG₂ hZ
    htest₁ htest₂ hs₁ hs₂ hb₁ hb₂ hf hd hc hj residualPool C₁ C₂ U₁ U₂ G₁' G₂' active slow T
  have hdis : Disjoint residualPool (b.support∪common) := by
    apply Finset.disjoint_left.mpr
    intro i hi hi2
    exact (Finset.mem_sdiff.mp hi).2 hi2
  apply htail p hp hinj hcop hg hchar residualPool b.support common divisor b.leftExponent b.rightExponent
    b.leftBit b.rightBit b.support_pos (hdis.mono_right Finset.subset_union_left) f hf0 C₁ C₂ W
    G₁' G₂' Z M r ell V delta B j eta tau (by dsimp [G₁']; positivity) (by dsimp [G₂']; positivity) hZ
  · intro N hN
    exact (canonical_residual_norm p hg b common true Ψ₁ hΨ₁ m₁ _ _ N).trans
      (hmark p hp hcop slots lists a hslots ha extra₁ test₁ E G₁ (Z^(r+eta)) hE hG₁
        (Real.rpow_pos_of_pos hZ _).le he₁ htest₁ hs₁ _)
  · intro N hN
    exact (canonical_residual_norm p hg b common false Ψ₂ hΨ₂ m₂ _ _ N).trans
      (hmark p hp hcop slots lists a hslots ha extra₂ test₂ E G₂ (Z^(r+eta)) hE hG₂
        (Real.rpow_pos_of_pos hZ _).le he₂ htest₂ hs₂ _)
  · exact hb₁
  · exact hb₂
  · exact hf
  · exact hd
  · exact hc
  · exact hj
  · intro N hN hn
    have ht := canonical_residual_test_nonzero p hg b common true Ψ₁ m₁
      (cubicIdealGenerator f) _ N hn
    have hn' := hs₁ _ (mul_ne_zero_iff.mp ht).2
    have he := cube_whole_column_norm p b hb common N hcommon
      (hdis.mono_left (Finset.mem_powerset.mp hN)) true
    simp only [ite_true] at he
    exact he ▸ hn'
  · intro N hN hn
    have ht := canonical_residual_test_nonzero p hg b common false Ψ₂ m₂
      (cubicIdealGenerator f) _ N hn
    have hn' := hs₂ _ (mul_ne_zero_iff.mp ht).2
    have he := cube_whole_column_norm p b hb common N hcommon
      (hdis.mono_left (Finset.mem_powerset.mp hN)) false
    simp only [ite_false,Bool.false_eq_true] at he
    exact he ▸ hn'

end
end InverseMoment

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
section
variable {ι:Type*} [DecidableEq ι]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

def firstLocalPhysicalTail (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ) (W:𝓢(ℝ,ℂ))
    (K:ℝ) (T:Finset ι→Finset O) (D:Finset ι):ℂ :=
  ∑'h:{h:O // h∉T D},actualFirstKernel p hp hg (pool\(b.support∪C)) b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
    (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
    (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂) W (fun _=>1) (fun _=>1) 1 1 K
    ((∏ i ∈ D,p i)) h.val

theorem cube_tail_support_test (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ) (W:𝓢(ℝ,ℂ))
    (K L:ℝ) (T:Finset ι→Finset O)
    (hs:∀U,H₁ U≠0→primeProductNorm p U≤ L) (hC:¬primeProductNorm p C≤ L) :
    canonicalCubeDualTail p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K T=0 := by
  have hz (U:Finset ι):H₁ ((b.rightDivisor∪C)∪U)=0:=by
    by_contra h
    exact hC ((primeProductNorm_mono p hp
      (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left)).trans (hs _ h))
  have hcoef (U:Finset ι):canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁ U=0:=by
    simp only [canonicalCubeResidual,originalLabelColumn,multiplicativeCoreColumn,ite_true,hz,mul_zero,zero_mul]
  simp only [canonicalCubeDualTail,actualFirstKernel,threeGaussRowFactor,hcoef,mul_zero,
    star_zero,zero_mul,ite_self,Finset.sum_const_zero,tsum_zero]

end

theorem full_first_tail_from_local (ε:ℝ) (hε:0<ε) :
    ∃Ctail:ℝ,0<Ctail ∧ ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i})
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
      (H₁ H₂:CubeCoordinates ι→Finset ι→ℂ) (W:𝓢(ℝ,ℂ)) (K B L F Γ E:ℝ)
      (T:CubeCoordinates ι→Finset ι→Ideal O→Finset ι→Finset O),
      1≤ B → 0<L → 1≤ F → 0≤Γ → 0≤ E →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖ringComplex (primeProduct p b.support b.leftExponent)‖^2≤ B) →
      (∀b∈bs,‖ringComplex (primeProduct p b.support b.rightExponent)‖^2≤ B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤ F) →
      (∀b∈bs,∀C∈(pool\b.support).powerset,∀I∈labels,‖a b C I‖≤Γ) →
      (∀b∈bs,∀U,H₁ b U≠0→primeProductNorm p U≤ L) →
      (∀b∈bs,∀C∈boundedPrimeSupports p (pool\b.support) L,∀I∈labels,
        ∀D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
        ‖firstLocalPhysicalTail p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂
          (cubicIdealGenerator I) (H₁ b) (H₂ b) W K (T b C I) D‖≤ E) →
      ‖∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*
        canonicalCubeDualTail p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂
          (cubicIdealGenerator I) (H₁ b) (H₂ b) W K (T b C I)‖≤
        Ctail*B^(4+ε)*L^2*F*Γ*E := by
  have hdc := diagonalControl_nonneg sieveCutoff
  obtain ⟨Cb,hCb,hcount⟩:=cube_coordinates_parity_count ε hε
  refine ⟨Cb*(1+diagonalControl sieveCutoff)^3,by positivity,?_⟩
  intro ι _ p hp _ hinj hcop hg hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ H₁ H₂ W K B L F Γ E T
    hB hL hF hΓ hE hΨ₁ hΨ₂ hadm hb₁ hb₂ hI0 hIF ha hs hlocal
  have hBp:0<B:=zero_lt_one.trans_le hB
  have hlabel:(labels.card:ℝ)≤(1+diagonalControl sieveCutoff)*F:=(finite_ideal_card_bound labels F hF hIF).trans (mul_le_mul_of_nonneg_right (by linarith) (zero_le_one.trans hF))
  have hbcount:(bs.card:ℝ)≤ Cb*B^(1+ε)*B:=by
    apply hcount p hp hinj bs B B hB hBp.le hadm hb₁ hb₂
    intro b hb
    have hn:primeProductNorm p (cubeActiveSupport b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)≤ B^2:=
      (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans
        (cube_whole_support_dyad p hp b B hBp.le (hb₁ b hb) (hb₂ b hb))
    change ‖ringComplex (∏i∈cubeActiveSupport b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i)‖^2≤ B^2 at hn
    nlinarith [norm_nonneg (ringComplex (∏i∈cubeActiveSupport b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i))]
  let z (b:CubeCoordinates ι) (C:Finset ι) (I:Ideal O):ℂ:=
    canonicalCubeDualTail p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (cubicIdealGenerator I) (H₁ b) (H₂ b) W K (T b C I)
  have hblock (b:CubeCoordinates ι) (hb:b∈bs) (C:Finset ι)
      (hC:C∈boundedPrimeSupports p (pool\b.support) L) (I:Ideal O) (hI:I∈labels):
      ‖z b C I‖≤(1+diagonalControl sieveCutoff)*(L*B^2)*E:=by
    have hCB:Disjoint C b.support:=Finset.disjoint_left.mpr (fun i hi hib=>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hC).1) hi)).2 hib)
    dsimp only [z,canonicalCubeDualTail]
    rw [norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) (canonicalCubeOuter_norm_le_one_of_good p hp hg hinj hc b C
      Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ _)).trans
    calc
      _≤∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,E:=by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro D hD
        rw [norm_mul]
        exact (mul_le_mul (sourceMobiusDivisor_norm_le_one p hp D)
          (hlocal b hb C hC I hI D hD) (norm_nonneg _) zero_le_one).trans_eq (one_mul E)
      _= ((C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset.card:ℝ)*E:=by simp
      _≤_:=mul_le_mul_of_nonneg_right (cubeSourceDivisors_card p hp hinj b C B L hBp hL hCB
        (hb₁ b hb) (hb₂ b hb) (Finset.mem_filter.mp hC).2) hE
  have hcommon (b:CubeCoordinates ι) (hb:b∈bs):
      ‖∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I‖≤
      ((1+diagonalControl sieveCutoff)*L)*((1+diagonalControl sieveCutoff)*F)*Γ*((1+diagonalControl sieveCutoff)*(L*B^2)*E):=by
    have heq:(∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I)=
        ∑C∈boundedPrimeSupports p (pool\b.support) L,∑I∈labels,a b C I*z b C I:=by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro C hC hnot
      have hn:¬primeProductNorm p C≤ L:=fun h=>hnot (Finset.mem_filter.mpr ⟨hC,h⟩)
      apply Finset.sum_eq_zero
      intro I hI
      rw [show z b C I=0 from cube_tail_support_test p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂ _
        (H₁ b) (H₂ b) W K L (T b C I) (hs b hb) hn,mul_zero]
    rw [heq]
    calc
      _≤∑C∈boundedPrimeSupports p (pool\b.support) L,∑I∈labels,Γ*((1+diagonalControl sieveCutoff)*(L*B^2)*E):=by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro C hC
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro I hI
        rw [norm_mul]
        exact mul_le_mul (ha b hb C (Finset.mem_filter.mp hC).1 I hI) (hblock b hb C hC I hI) (norm_nonneg _) hΓ
      _= ((boundedPrimeSupports p (pool\b.support) L).card:ℝ)*(labels.card:ℝ)*Γ*((1+diagonalControl sieveCutoff)*(L*B^2)*E):=by simp;ring
      _≤_:=by gcongr;exact boundedPrimeSupports_card_positive p hp hinj _ _ hL
  change ‖∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I‖≤_
  calc
    _≤∑b∈bs,((1+diagonalControl sieveCutoff)*L)*((1+diagonalControl sieveCutoff)*F)*Γ*((1+diagonalControl sieveCutoff)*(L*B^2)*E):=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hcommon)
    _= (bs.card:ℝ)*(((1+diagonalControl sieveCutoff)*L)*((1+diagonalControl sieveCutoff)*F)*Γ*((1+diagonalControl sieveCutoff)*(L*B^2)*E)):=by simp
    _≤(Cb*B^(1+ε)*B)*(((1+diagonalControl sieveCutoff)*L)*((1+diagonalControl sieveCutoff)*F)*Γ*((1+diagonalControl sieveCutoff)*(L*B^2)*E)):=by gcongr
    _= _:=by
      have he:B^(1+ε)*B*B^2=B^(4+ε):=by
        calc
          _=B^(1+ε)*B^(1:ℝ)*B^(2:ℝ):=by rw [Real.rpow_one,Real.rpow_two]
          _=B^((1+ε)+1+2):=by rw [←Real.rpow_add hBp,←Real.rpow_add hBp]
          _= _:=by congr 1;ring
      calc
        _=(Cb*(1+diagonalControl sieveCutoff)^3)*(B^(1+ε)*B*B^2)*L^2*F*Γ*E:=by ring
        _= _:=by rw [he]

end InverseMoment

end

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

theorem first_canonical_marked_tail (ε : ℝ) (hε : 0<ε) (order : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct Cm : ℝ),0<Ct ∧ 0<Cm ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,lambda∉Ideal.span {p i})
      (_hchar : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι) (b : CubeCoordinates ι),b.Admissible →
      ∀ (common divisor : Finset ι),Disjoint common b.support →
      ∀ (f : Ideal O),f≠0 →
      ∀ (Ψ₁ Ψ₂ : O→*ℂ),(∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      ∀ (m₁ m₂ : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists → (∀ i∈slots,∀ k∈lists i,‖a i k‖≤1) →
      ∀ (test₁ test₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ))
      (G₁ G₂ Z M r ell V delta B j eta tau : ℝ),0≤ G₁ → 0≤ G₂ → 0<Z →
      (∀ U,‖test₁ U‖≤ G₁) → (∀ U,‖test₂ U‖≤ G₂) →
      (∀ U,test₁ U≠0 → primeProductNorm p U≤ Z^(r+eta)) →
      (∀ U,test₂ U≠0 → primeProductNorm p U≤ Z^(r+eta)) →
      ‖ringComplex (primeProduct p b.support b.leftExponent)‖^2≤ Z^(ell+eta) →
      ‖ringComplex (primeProduct p b.support b.rightExponent)‖^2≤ Z^(ell+eta) →
      (Ideal.absNorm f : ℝ)≤ Z^(V+eta) → primeProductNorm p divisor≤ Z^(delta+eta) →
      Z^(B-eta)≤ primeProductNorm p common →
      Z^(j-eta)≤‖ringComplex (jLabel p b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit)‖^2 →
      let residualPool := pool\(b.support∪common)
      let C₁ := canonicalCubeResidual p hg b common true Ψ₁ m₁ (cubicIdealGenerator f)
        (wholeMarkedTest slots lists a test₁)
      let C₂ := canonicalCubeResidual p hg b common false Ψ₂ m₂ (cubicIdealGenerator f)
        (wholeMarkedTest slots lists a test₂)
      let U₁ := Z^(r+eta)/(‖ringComplex (aLabel p b.support b.rightBit)‖^2*primeProductNorm p common)
      let U₂ := Z^(r+eta)/(‖ringComplex (aLabel p b.support b.leftBit)‖^2*primeProductNorm p common)
      let G₁' := Cm*(Z^(r+eta))^ε*G₁
      let G₂' := Cm*(Z^(r+eta))^ε*G₂
      let active := cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      let slow := Z^M/(primeProductNorm p divisor*primeProductNorm p active*U₁*U₂)
      let T := childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f)
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau))
      ‖∑' h : {h : O // h∉T},actualFirstKernel p hp hg residualPool b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit C₁ C₂ W
        (fun _=>1) (fun _=>1) 1 1 (Z^M)
        ((∏ i ∈ divisor,p i)) h.val‖ ≤
      ((1+diagonalControl sieveCutoff)*U₁)*((1+diagonalControl sieveCutoff)*U₂)*(G₁'*G₂'*Z^M)*
        ((Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 slow)^2*(1+Z^tau)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_first_physical_tail order
  obtain ⟨Cm,hCm,hmark⟩ := whole_marked_test_uniform ε hε
  refine ⟨s,Ct,Cm,hCt,hCm,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hchar pool b hb common divisor hcommon f hf0 Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m₁ m₂ slots lists a hslots ha test₁ test₂ W G₁ G₂ Z M r ell V delta B j eta tau hG₁ hG₂ hZ
    htest₁ htest₂ hs₁ hs₂ hb₁ hb₂ hf hd hc hj residualPool C₁ C₂ U₁ U₂ G₁' G₂' active slow T
  have hdis : Disjoint residualPool (b.support∪common) := by
    apply Finset.disjoint_left.mpr
    intro i hi hi2
    exact (Finset.mem_sdiff.mp hi).2 hi2
  apply htail p hp hinj hcop hg hchar residualPool b.support common divisor b.leftExponent b.rightExponent
    b.leftBit b.rightBit b.support_pos (hdis.mono_right Finset.subset_union_left) f hf0 C₁ C₂ W
    G₁' G₂' Z M r ell V delta B j eta tau (by dsimp [G₁']; positivity) (by dsimp [G₂']; positivity) hZ
  · intro N hN
    exact (canonical_residual_norm p hg b common true Ψ₁ hΨ₁ m₁ _ _ N).trans
      (hmark p hp hcop slots lists a hslots ha test₁ G₁ (Z^(r+eta)) hG₁
        (Real.rpow_pos_of_pos hZ _).le htest₁ hs₁ _)
  · intro N hN
    exact (canonical_residual_norm p hg b common false Ψ₂ hΨ₂ m₂ _ _ N).trans
      (hmark p hp hcop slots lists a hslots ha test₂ G₂ (Z^(r+eta)) hG₂
        (Real.rpow_pos_of_pos hZ _).le htest₂ hs₂ _)
  · exact hb₁
  · exact hb₂
  · exact hf
  · exact hd
  · exact hc
  · exact hj
  · intro N hN hn
    exact canonical_marked_residual_support p hg b hb common N hcommon
      (hdis.mono_left (Finset.mem_powerset.mp hN)) true Ψ₁ m₁ _ slots lists a test₁ _ hs₁ hn
  · intro N hN hn
    exact canonical_marked_residual_support p hg b hb common N hcommon
      (hdis.mono_left (Finset.mem_powerset.mp hN)) false Ψ₂ m₂ _ slots lists a test₂ _ hs₂ hn

end
end InverseMoment

namespace InverseMoment
open SecondPassArithmetic
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment

lemma first_tail_fixed_cap (K D E U₁ U₂ B G₁ G₂ P H : ℝ) (A : ℕ)
    (hK : 0<K) (hD : 0<D) (hE : 0<E) (hU₁ : 0<U₁) (hU₂ : 0<U₂) (hB : 1≤ B)
    (hG₁ : 0≤ G₁) (hG₂ : 0≤ G₂) (hP : 0≤ P) (hH : 0≤ H)
    (hKb : K≤ B) (hKi : K⁻¹≤ B) (hDb : D≤ B) (hEb : E≤ B) (h₁ : U₁≤ B) (h₂ : U₂≤ B) :
    ((1+diagonalControl sieveCutoff)*U₁)*((1+diagonalControl sieveCutoff)*U₂)*(G₁*G₂*K)*
      (P/((min 1 (K/(D*E*U₁*U₂)))^2*(1+H)^A)) ≤
    (4*(1+diagonalControl sieveCutoff)^2)*G₁*G₂*P*B^19/(1+H)^A := by
  have hdc := diagonalControl_nonneg sieveCutoff
  have hB0 : 0≤ B := zero_le_one.trans hB
  have hB2 : B≤ B^2 := by nlinarith
  have hB3 : B≤ B*B^2 := le_mul_of_one_le_right hB0 (one_le_pow₀ hB)
  have hb := firstTail_scalar_bound K D E U₁ U₂ B B G₁ G₂ P H A hK hD hE hU₁ hU₂
    hB0 hG₁ hG₂ hP hH (hDb.trans hB3) (hEb.trans hB2) h₁ h₂
  have hscale : 1+B^3*B^4/K≤2*B^8 := by
    calc
      _ ≤ 1+B^3*B^4*B := by rw [div_eq_mul_inv]; gcongr
      _ ≤ 2*B^8 := by have hh : 1≤ B^8 := one_le_pow₀ hB; nlinarith [hh]
  apply hb.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ((1+diagonalControl sieveCutoff)*B)^2*(G₁*G₂*B)*P*(2*B^8)^2 := by gcongr
    _ = _ := by ring

theorem choose_first_tail_order (Lcap tau saving : ℝ) (hL : 0≤ Lcap) (htau : 0<tau) :
    ∃ A : ℕ, ∀ (Z K D E U₁ U₂ G₁ G₂ P : ℝ),1≤ Z →
      0<K → 0<D → 0<E → 0<U₁ → 0<U₂ → 0≤ G₁ → 0≤ G₂ → 0≤ P →
      K≤ Z^Lcap → K⁻¹≤ Z^Lcap → D≤ Z^Lcap → E≤ Z^Lcap → U₁≤ Z^Lcap → U₂≤ Z^Lcap →
      ((1+diagonalControl sieveCutoff)*U₁)*((1+diagonalControl sieveCutoff)*U₂)*(G₁*G₂*K)*
        (P/((min 1 (K/(D*E*U₁*U₂)))^2*(1+Z^tau)^A)) ≤
      (4*(1+diagonalControl sieveCutoff)^2)*G₁*G₂*P*Z^(-saving) := by
  have hdc := diagonalControl_nonneg sieveCutoff
  obtain ⟨A,hA⟩ := exists_nat_gt ((19*Lcap+saving)/tau)
  refine ⟨A,?_⟩
  intro Z K D E U₁ U₂ G₁ G₂ P hZ hK hD hE hU₁ hU₂ hG₁ hG₂ hP hKb hKi hDb hEb h₁ h₂
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hb := first_tail_fixed_cap K D E U₁ U₂ (Z^Lcap) G₁ G₂ P (Z^tau) A
    hK hD hE hU₁ hU₂ (Real.one_le_rpow hZ hL) hG₁ hG₂ hP
    (Real.rpow_pos_of_pos hz _).le hKb hKi hDb hEb h₁ h₂
  have hdecay : (Z^Lcap)^19/(1+Z^tau)^A≤ Z^(-saving) := by
    calc
      _ ≤ (Z^Lcap)^19/(Z^tau)^A := div_le_div_of_nonneg_left (by positivity)
        (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) A)
      _ = Z^(19*Lcap-tau*(A:ℝ)) := by
        rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_mul_natCast hz.le,←Real.rpow_sub hz]
        congr 1
        norm_num
        ring
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hZ
        have hh := (div_lt_iff₀ htau).mp hA
        nlinarith
  apply hb.trans
  calc
    _ = ((4*(1+diagonalControl sieveCutoff)^2)*G₁*G₂*P)*((Z^Lcap)^19/(1+Z^tau)^A) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (by positivity)

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι : Type*} (p : ι→O) (hp : ∀i,p i≠0)

include hp in
theorem first_nonempty_column_center (U : Finset ι) (Z r eta : ℝ) (hZ : 1<Z)
    (hU : primeProductNorm p U≤ Z^(r+eta)) : -eta≤ r := by
  have hh : Z^(0:ℝ)≤ Z^(r+eta) := by
    rw [Real.rpow_zero]
    exact (primeProductNorm_ge_one p hp U).trans hU
  have := (Real.rpow_le_rpow_left_iff hZ).mp hh
  linarith

variable [DecidableEq ι]

include hp in

theorem first_source_divisor_center (b : CubeCoordinates ι) (C D : Finset ι)
    (hCB : Disjoint C b.support)
    (hD : D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)
    (Z r ell delta eta : ℝ) (hZ : 1<Z)
    (h1 : ‖ringComplex (primeProduct p b.support b.leftExponent)‖^2≤ Z^(ell+eta))
    (h2 : ‖ringComplex (primeProduct p b.support b.rightExponent)‖^2≤ Z^(ell+eta))
    (hC : primeProductNorm p C≤ Z^(r+eta))
    (hd : Z^(delta-eta)≤ primeProductNorm p D) : delta≤ r+2*ell+4*eta := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hh := hd.trans (cubeSourceDivisor_norm_bound p hp b C D (Z^(ell+eta)) (Z^(r+eta))
    (Real.rpow_pos_of_pos hz _).le (Real.rpow_pos_of_pos hz _).le hCB h1 h2 hC hD)
  rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz] at hh
  have := (Real.rpow_le_rpow_left_iff hZ).mp hh
  norm_num at this
  linarith

include hp in
theorem first_source_scalar_caps (b : CubeCoordinates ι) (C D : Finset ι)
    (hCB : Disjoint C b.support)
    (hD : D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)
    (Z M Mmax Fmax r ell V eta : ℝ) (hZ : 1≤ Z)
    (hM : 0≤ M) (hMm : M≤ Mmax) (hF : 0≤ Fmax) (hell : 0≤ ell) (hV : 0≤ V)
    (heta : 0≤ eta) (hr : -eta≤ r) (hwhole : r+3*ell+V≤ Fmax)
    (h1 : ‖ringComplex (primeProduct p b.support b.leftExponent)‖^2≤ Z^(ell+eta))
    (h2 : ‖ringComplex (primeProduct p b.support b.rightExponent)‖^2≤ Z^(ell+eta))
    (hC : primeProductNorm p C≤ Z^(r+eta)) :
    let cap := Mmax+Fmax+3*eta
    Z^M≤ Z^cap ∧ (Z^M)⁻¹≤ Z^cap ∧ primeProductNorm p D≤ Z^cap ∧
    primeProductNorm p (cubeActiveSupport b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)≤ Z^cap ∧
    (∀ eps : ι→Bool,Z^(r+eta)/(‖ringComplex (aLabel p b.support eps)‖^2*primeProductNorm p C)≤ Z^cap) := by
  dsimp only
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hcap : 0≤ Mmax+Fmax+3*eta := by linarith
  refine ⟨Real.rpow_le_rpow_of_exponent_le hZ (by linarith),?_,?_,?_,?_⟩
  · calc
      _ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_rpow hZ hM)
      _ ≤ _ := Real.one_le_rpow hZ hcap
  · have hd := cubeSourceDivisor_norm_bound p hp b C D (Z^(ell+eta)) (Z^(r+eta))
      (Real.rpow_pos_of_pos hz _).le (Real.rpow_pos_of_pos hz _).le hCB h1 h2 hC hD
    apply hd.trans
    rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    norm_num
    linarith
  · apply (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans
    apply (cubeCoordinates_radical_bound p hp b (Z^(ell+eta)) (Real.rpow_pos_of_pos hz _).le h1 h2).trans
    rw [←Real.rpow_mul_natCast hz.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    norm_num
    linarith
  · intro eps
    have ha := element_norm_ge_one (aLabel p b.support eps) (primeProduct_ne_zero p hp _ _)
    have hc := primeProductNorm_ge_one p hp C
    calc
      _ ≤ Z^(r+eta) := div_le_self (Real.rpow_pos_of_pos hz _).le (one_le_mul_of_one_le_of_one_le ha hc)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

theorem choose_actual_first_tail_order (Mmax Fmax eta tau saving : ℝ)
    (hMm : 0≤ Mmax) (hFm : 0≤ Fmax) (heta : 0≤ eta) (htau : 0<tau) :
    ∃ order : ℕ,∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (b : CubeCoordinates ι) (C D : Finset ι),Disjoint C b.support →
      D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit →
      ∀ (Z M r ell V G₁ G₂ P : ℝ),1≤ Z → 0≤ M → M≤ Mmax → 0≤ ell → 0≤ V → -eta≤ r →
      r+3*ell+V≤ Fmax → 0≤ G₁ → 0≤ G₂ → 0≤ P →
      ‖ringComplex (primeProduct p b.support b.leftExponent)‖^2≤ Z^(ell+eta) →
      ‖ringComplex (primeProduct p b.support b.rightExponent)‖^2≤ Z^(ell+eta) →
      primeProductNorm p C≤ Z^(r+eta) →
      let U₁ := Z^(r+eta)/(‖ringComplex (aLabel p b.support b.rightBit)‖^2*primeProductNorm p C)
      let U₂ := Z^(r+eta)/(‖ringComplex (aLabel p b.support b.leftBit)‖^2*primeProductNorm p C)
      let active := cubeActiveSupport b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      let slow := Z^M/(primeProductNorm p D*primeProductNorm p active*U₁*U₂)
      ((1+diagonalControl sieveCutoff)*U₁)*((1+diagonalControl sieveCutoff)*U₂)*(G₁*G₂*Z^M)*(P/((min 1 slow)^2*(1+Z^tau)^order))≤
        (4*(1+diagonalControl sieveCutoff)^2)*G₁*G₂*P*Z^(-saving) := by
  obtain ⟨order,he⟩ := choose_first_tail_order (Mmax+Fmax+3*eta) tau saving (by linarith) htau
  refine ⟨order,?_⟩
  intro ι _ p hp _ b C D hCB hD Z M r ell V G₁ G₂ P hZ hM hMmax hell hV hr hwhole hG₁ hG₂ hP h1 h2 hC
  dsimp only
  have hz : 0<Z := zero_lt_one.trans_le hZ
  obtain ⟨hk,hki,hd,ha,hu⟩ := first_source_scalar_caps p hp b C D hCB hD
    Z M Mmax Fmax r ell V eta hZ hM hMmax hFm hell hV heta hr hwhole h1 h2 hC
  have hapos (eps : ι→Bool) : 0<‖ringComplex (aLabel p b.support eps)‖^2 :=
    SecondPassIntegration.elementNorm_pos _ (primeProduct_ne_zero p hp _ _)
  exact he Z (Z^M) (primeProductNorm p D)
    (primeProductNorm p (cubeActiveSupport b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit))
    (Z^(r+eta)/(‖ringComplex (aLabel p b.support b.rightBit)‖^2*primeProductNorm p C))
    (Z^(r+eta)/(‖ringComplex (aLabel p b.support b.leftBit)‖^2*primeProductNorm p C))
    G₁ G₂ P hZ (Real.rpow_pos_of_pos hz _) (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _)
    (div_pos (Real.rpow_pos_of_pos hz _) (mul_pos (hapos _) (primeProductNorm_pos p hp _)))
    (div_pos (Real.rpow_pos_of_pos hz _) (mul_pos (hapos _) (primeProductNorm_pos p hp _)))
    hG₁ hG₂ hP hk hki hd ha (hu _) (hu _)

end
end InverseMoment

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

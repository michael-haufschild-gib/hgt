/-
Marked completed cube sums adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.FirstDyadicRadius

/-!
# Marked completed cube sums

The marked completed sum `markedCompletedT` and its series form; live joint keys and physical
scales; finite support, reopening and inverse splitting of marked large cubes.
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
open InverseMomentFirstChildWindows InverseSecondSourceBlocks
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

abbrev JointKey := SourceIndex × ℕ × ℕ

def jointKey (x : OriginalIndex ι) (j : FirstCommonIndex ι) : JointKey :=
  (sourceIndex (originalNorms p) x,dyadIndex (primeProductNorm p j.2.1),
    dyadIndex (InverseFirstGlobalCaps.jNorm p x.1))

def liveJointKeys (S : Finset (OriginalIndex ι)) (pool : Finset ι)
    (term : OriginalIndex ι→FirstCommonIndex ι→ℂ) : Finset JointKey :=
  ((S×ˢfirstCommonIndices pool).filter (fun x=>term x.1 x.2≠0)).image
    (fun x=>jointKey p x.1 x.2)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma sum_live_joint_cells (S : Finset (OriginalIndex ι)) (pool : Finset ι)
    (term : OriginalIndex ι→FirstCommonIndex ι→ℂ) :
    (∑x∈S,∑j∈firstCommonIndices pool,term x j)=
      ∑k∈liveJointKeys p S pool term,∑x∈S,∑j∈firstCommonIndices pool,
        if jointKey p x j=k then term x j else 0 := by
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hz : term x j=0
  · simp [hz]
  · have hk : jointKey p x j∈liveJointKeys p S pool term :=
      Finset.mem_image.mpr ⟨(x,j),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hj⟩,hz⟩,rfl⟩
    simp [hk]

lemma sourceSummand_zero_of_weight (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,lambda∉Ideal.span {p i})
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (x : OriginalIndex ι) (j : FirstCommonIndex ι) (hx : firstOriginalWeight p β cutoff x.1 x.2=0) :
    sourceSummand p hp hg β cutoff Ψ m mark W Φ K x j=0 := by
  simp [sourceSummand,weight,retainedCubeWeight,hx]

lemma joint_cell_eq_refined (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,lambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (k : JointKey) :
    let S := firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y
    let term := sourceSummand p hp hg β cutoff Ψ m mark W Φ K
    (∑x∈S,∑j∈firstCommonIndices pool,if jointKey p x j=k then term x j else 0)=
      ∑x∈refinedSource p pool Q labels β cutoff Y k.1 (labelGate p k.2.2),
        ∑j∈firstCommonIndices pool,commonSelector p (fun _=>1) k.2.1 j.2.1*term x j := by
  intro S term
  simp only [refinedSource,sourceCell,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hw : firstOriginalWeight p β cutoff x.1 x.2=0
  · have ht : ∀j,term x j=0 := fun j=>sourceSummand_zero_of_weight p hp hcop hg β cutoff Ψ m mark W Φ K x j hw
    simp [ht,hw]
  · by_cases hs : sourceIndex (originalNorms p) x=k.1
    · by_cases hj : dyadIndex (InverseFirstGlobalCaps.jNorm p x.1)=k.2.2
      · simp [jointKey,hs,hj,labelGate,hw,Prod.ext_iff,commonSelector,ite_mul]
      · simp [jointKey,hs,hj,labelGate,Prod.ext_iff]
    · simp [jointKey,hs,Prod.ext_iff]

theorem original_retained_joint_partition (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,lambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (s : Fin 9→ℝ) (hs : ∀i,0<s i) :
    let S := firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y
    let term := sourceSummand p hp hg β cutoff Ψ m mark W Φ K
    originalRetainedFamily p hp hg pool Q labels β Ψ m mark W Φ K Y cutoff s=
      ∑k∈liveJointKeys p S pool term,
        ∑x∈refinedSource p pool Q labels β cutoff Y k.1 (labelGate p k.2.2),
          ∑j∈firstCommonIndices pool,commonSelector p (fun _=>1) k.2.1 j.2.1*term x j := by
  intro S term
  rw [original_retained_sum p hp hg pool Q labels β Ψ m mark W Φ K Y cutoff s hs,
    sum_live_joint_cells p S pool term]
  apply Finset.sum_congr rfl
  intro k hk
  exact joint_cell_eq_refined p hp hcop hg pool Q labels β cutoff Ψ m mark W Φ K Y k

end InverseMomentFirstOriginalProfile
end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile
open Eisenstein (ringComplex)
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O"=>Eisenstein.O
variable {ι:Type*}[DecidableEq ι]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem first_dyadic_original_cap (pool:Finset ι)(Q:Finset (ι→₀ℕ))
    (Z M r ell V eta tau Fmax:ℝ)(hZ:1<Z)(hbin:2≤ Z^eta)(hM:0≤ M)
    (hF:r+3*ell+V≤ Fmax)
    (hQ:∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta)):
    ∀x∈firstOriginalOuter pool Q,firstDyadicRadius p x.1 x.2.1 x.2.2 Z M r ell V eta tau≤ Z^(2*Fmax+15*eta+tau):=by
  intro x hx
  have hm:=(mem_firstOriginalOuter pool Q x).mp hx
  have hb:=reopenedCubeFamily_cube_norms p Q _ hQ x.1 hm.1
  exact first_dyadic_radius_global_cap p hp x.1 x.2.1 x.2.2 (Finset.mem_powerset.mp hm.2.2)
    Z M r ell V eta tau Fmax hZ hbin hM hF hb.1 hb.2

include hp in
theorem first_live_cell_radius_cap (pool:Finset ι)(Q:Finset (ι→₀ℕ))
    (labels:Finset (Ideal O))(Y:ℝ)(term:OriginalIndex ι→FirstCommonIndex ι→ℂ)
    (Z M r ell V eta tau Fmax:ℝ)(hZ:1<Z)(hbin:2≤ Z^eta)(hM:0≤ M)
    (hF:r+3*ell+V≤ Fmax)
    (hQ:∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta))
    (k:JointKey)(hk:k∈liveJointKeys p
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) pool term):
    firstCellRadius Z M r ell V eta tau k.1 k.2.2≤ Z^(2*Fmax+15*eta+tau):=by
  obtain ⟨⟨x,j⟩,hx,rfl⟩:=Finset.mem_image.mp hk
  have hm:=Finset.mem_product.mp (Finset.mem_filter.mp hx).1
  have ho: x.1∈firstOriginalOuter pool Q:=(Finset.mem_sigma.mp hm.1).1
  have href:x.1∈refinedOuter p pool Q (sourceIndex (InverseMomentFirstOriginalProfile.originalNorms p) x)
      (labelGate p (dyadIndex (InverseFirstGlobalCaps.jNorm p x.1))):=by
    rw [refinedOuter_label]
    apply Finset.mem_filter.mpr
    refine ⟨?_,rfl⟩
    apply InverseFirstGlobalCaps.sourceCell_outer p pool Q labels Y
    exact Finset.mem_filter.mpr ⟨hm.1,rfl⟩
  change firstCellRadius Z M r ell V eta tau (sourceIndex (InverseMomentFirstOriginalProfile.originalNorms p) x)
    (dyadIndex (InverseFirstGlobalCaps.jNorm p x.1))≤_
  rw [←first_dyadic_radius_cell p pool Q _ _ x.1 href]
  exact first_dyadic_original_cap p hp pool Q Z M r ell V eta tau Fmax hZ hbin hM hF hQ x.1 ho

end InverseMoment

end

noncomputable section
namespace InverseMomentFirstOriginalProfile
open InverseMoment Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseMomentFirstProfileUniform CompletedHeight
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg : ∀i,lambda∉Ideal.span {p i})

theorem original_refined_cell_profile_identity (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (β : Ideal O→(ι→₀ℕ)→ℂ)
    (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hsom : Function.support om⊆Set.Icc a b)
    (Φ : 𝓢(ℝ,ℂ)) (K Y X theta : ℝ) (hX : 0<X)
    (k : SourceIndex) (l : ℕ) (gate : FirstOriginalOuter ι→Prop) (s : Fin 9→ℝ) (hs : ∀i,0<s i)
    (hleft : s 0*s 2*s 5*s 7=X) (hright : s 1*s 2*s 5*s 8=X) :
    let source := refinedSource p pool Q labels β cutoff Y k gate
    (∑x∈source,∑j∈firstCommonIndices pool,commonSelector p (fun _=>1) l j.2.1*
      sourceSummand p hp hg β cutoff Ψ m mark
        (fun y=>normTwistedSource om theta (y/X)) Φ K x j)=
    refinedCellRows p hp hcop hg pool Q labels β cutoff Ψ m mark k l gate
      (positiveSource (priorityLogWindow om a b ha hsom true) 1 (-theta))
      (positiveSource (priorityLogWindow om a b ha hsom false) 1 theta) Φ K Y s := by
  intro source
  let W₁ := fun y=>star (normTwistedSource om theta ((s 0*s 2*s 5*s 7)*y/X))
  let W₂ := fun y=>normTwistedSource om theta ((s 1*s 2*s 5*s 8)*y/X)
  have he := original_family_profiles p hp hg source pool (fun _=>commonSelector p (fun _=>1) l)
    (coefficient p hg Ψ m mark true) (coefficient p hg Ψ m mark false)
    (weight p hp hg β cutoff Ψ m) om a b ha hsom Φ
    (leftNorm p) (rightNorm p) (commonNorm p) (activeNorm p) K X theta
    (fun x=>divisorElement p x.1) (fun x=>x.2.2) s hs
    (by intro x hx;have hh:=original_source_positive p hp pool Q labels Y x (Finset.mem_filter.mp (refinedSource_subset p pool Q labels β cutoff Y k gate hx)).1
        exact ⟨hh.1,hh.2.1,hh.2.2.1⟩) hX hleft hright
  change _=firstFamilyPhysicalRows p hg source pool _ _ _ _ _ _ Φ _ _ _ _ K _ _ s
  rw [←he]
  have hl : s 0*s 2*s 5*s 7≠0 := hleft.trans_ne (ne_of_gt hX)
  have hr : s 1*s 2*s 5*s 8≠0 := hright.trans_ne (ne_of_gt hX)
  simp only [firstFamilyPhysicalRows,firstBlockedPhysicalRows,sourceSummand,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro j hj
  simp only [firstNormProfile,mul_div_cancel₀ _ hl,mul_div_cancel₀ _ hr]
  ring

end InverseMomentFirstOriginalProfile
end

noncomputable section
namespace InverseMomentFirstOriginalProfile
open InverseMoment Eisenstein FirstPassCubeLabels SecondPassArithmetic InverseMomentFirstChildWindows InverseSecondSourceBlocks
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem liveJointKeys_card (S : Finset (OriginalIndex ι)) (pool : Finset ι)
    (term : OriginalIndex ι→FirstCommonIndex ι→ℂ) (B : ℕ)
    (hcap : ∀x∈S,∀j∈firstCommonIndices pool,term x j≠0→
      (∀i,sourceIndex (originalNorms p) x i≤ B) ∧
      dyadIndex (primeProductNorm p j.2.1)≤ B ∧
      dyadIndex (InverseFirstGlobalCaps.jNorm p x.1)≤ B) :
    (liveJointKeys p S pool term).card≤(B+1)^8 := by
  let box := (Fintype.piFinset (fun _ : Fin 6=>Finset.range (B+1))) ×ˢ
    (Finset.range (B+1) ×ˢ Finset.range (B+1))
  have hsub : liveJointKeys p S pool term⊆box := by
    intro k hk
    obtain ⟨⟨x,j⟩,hm,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hm,hn⟩ := Finset.mem_filter.mp hm
    obtain ⟨hx,hj⟩ := Finset.mem_product.mp hm
    obtain ⟨h₁,h₂,h₃⟩ := hcap x hx j hj hn
    exact Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr
      (fun i=>Finset.mem_range.mpr (Nat.lt_succ_of_le (h₁ i))),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le h₂),
        Finset.mem_range.mpr (Nat.lt_succ_of_le h₃)⟩⟩
  have hc : box.card=(B+1)^8 := by
    simp only [box,Finset.card_product,Fintype.card_piFinset,Finset.card_range,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    ring
  exact hc ▸ Finset.card_le_card hsub

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem liveJointKeys_card_of_norm_cap (S : Finset (OriginalIndex ι)) (pool : Finset ι)
    (term : OriginalIndex ι→FirstCommonIndex ι→ℂ) (R : ℝ)
    (hcap : ∀x∈S,∀j∈firstCommonIndices pool,term x j≠0→
      (∀i,0<originalNorms p x i ∧ originalNorms p x i≤ R) ∧
      (0<primeProductNorm p j.2.1 ∧ primeProductNorm p j.2.1≤ R) ∧
      (0<InverseFirstGlobalCaps.jNorm p x.1 ∧ InverseFirstGlobalCaps.jNorm p x.1≤ R)) :
    (liveJointKeys p S pool term).card≤(dyadIndex R+1)^8 := by
  apply liveJointKeys_card
  intro x hx j hj hn
  obtain ⟨h₁,h₂,h₃⟩ := hcap x hx j hj hn
  have hm : ∀a : ℝ,0<a→a≤ R→dyadIndex a≤ dyadIndex R := fun a ha haR=>
    Nat.floor_mono (Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) ha haR)
  exact ⟨fun i=>hm _ (h₁ i).1 (h₁ i).2,hm _ h₂.1 h₂.2,hm _ h₃.1 h₃.2⟩

end InverseMomentFirstOriginalProfile
end

noncomputable section
namespace InverseMomentFirstOriginalProfile
open InverseMoment InverseMomentFirstChildWindows InverseSecondSourceBlocks

def physicalScales (X : ℝ) (k : SourceIndex) (l : ℕ) : Fin 9→ℝ :=
  rawScales k l (X/(dyadScale (k 0)*dyadScale (k 2)*dyadScale l))
    (X/(dyadScale (k 1)*dyadScale (k 2)*dyadScale l))

lemma physicalScales_pos (X : ℝ) (hX : 0<X) (k : SourceIndex) (l : ℕ) :
    ∀i,0<physicalScales X k l i := by
  apply rawScales_pos
  · exact div_pos hX (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _))
  · exact div_pos hX (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _))

lemma physicalScales_products (X : ℝ) (k : SourceIndex) (l : ℕ) :
    physicalScales X k l 0*physicalScales X k l 2*physicalScales X k l 5*physicalScales X k l 7=X ∧
    physicalScales X k l 1*physicalScales X k l 2*physicalScales X k l 5*physicalScales X k l 8=X := by
  constructor
  · change (dyadScale (k 0)*dyadScale (k 2)*dyadScale l)*(X/(dyadScale (k 0)*dyadScale (k 2)*dyadScale l))=X
    exact mul_div_cancel₀ X (ne_of_gt (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _)))
  · change (dyadScale (k 1)*dyadScale (k 2)*dyadScale l)*(X/(dyadScale (k 1)*dyadScale (k 2)*dyadScale l))=X
    exact mul_div_cancel₀ X (ne_of_gt (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _)))

theorem physicalScales_rpow (Z r : ℝ) (hZ : 1<Z) (k : SourceIndex) (l : ℕ) :
    physicalScales (Z^r) k l=fun i=>Z^(![Real.logb Z (dyadScale (k 0)),
      Real.logb Z (dyadScale (k 1)),Real.logb Z (dyadScale (k 2)),
      Real.logb Z (dyadScale (k 3)),Real.logb Z (dyadScale (k 4)),Real.logb Z (dyadScale l),
      Real.logb Z (dyadScale (k 5)),
      r-Real.logb Z (dyadScale (k 0))-Real.logb Z (dyadScale (k 2))-Real.logb Z (dyadScale l),
      r-Real.logb Z (dyadScale (k 1))-Real.logb Z (dyadScale (k 2))-Real.logb Z (dyadScale l)] i) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have he (n : ℕ) : Z^(Real.logb Z (dyadScale n))=dyadScale n :=
    Real.rpow_logb hz (ne_of_gt hZ) (dyadScale_pos n)
  funext i
  fin_cases i <;> simp [physicalScales,rawScales,he,Real.rpow_sub hz,div_div]

end InverseMomentFirstOriginalProfile
end

noncomputable section
namespace InverseMomentFirstOriginalProfile
open InverseMoment Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseMomentFirstProfileUniform CompletedHeight
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg : ∀i,lambda∉Ideal.span {p i})

theorem original_retained_joint_profile_bound (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (β : Ideal O→(ι→₀ℕ)→ℂ)
    (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hsom : Function.support om⊆Set.Icc a b)
    (Φ : 𝓢(ℝ,ℂ)) (K Y X theta : ℝ) (hX : 0<X)
    (reference : Fin 9→ℝ) (href : ∀i,0<reference i) :
    let source := firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y
    let W := fun y=>normTwistedSource om theta (y/X)
    let term := sourceSummand p hp hg β cutoff Ψ m mark W Φ K
    ‖originalRetainedFamily p hp hg pool Q labels β Ψ m mark W Φ K Y cutoff reference‖≤
      ∑k∈liveJointKeys p source pool term,
        ‖refinedCellRows p hp hcop hg pool Q labels β cutoff Ψ m mark k.1 k.2.1 (labelGate p k.2.2)
          (positiveSource (priorityLogWindow om a b ha hsom true) 1 (-theta))
          (positiveSource (priorityLogWindow om a b ha hsom false) 1 theta) Φ K Y (physicalScales X k.1 k.2.1)‖ := by
  intro source W term
  rw [original_retained_joint_partition p hp hcop hg pool Q labels β cutoff Ψ m mark W Φ K Y reference href]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  have hp₁ := (physicalScales_products X k.1 k.2.1).1
  have hp₂ := (physicalScales_products X k.1 k.2.1).2
  rw [original_refined_cell_profile_identity p hp hcop hg pool Q labels β cutoff Ψ m mark om a b ha hsom
    Φ K Y X theta hX k.1 k.2.1 (labelGate p k.2.2) (physicalScales X k.1 k.2.1) (physicalScales_pos X hX k.1 k.2.1) hp₁ hp₂]

end InverseMomentFirstOriginalProfile
end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstProfileUniform
open InverseAmbientProfileTower JointLogSeparation CompletedHeight
open Eisenstein (ringComplex)
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O"=>Eisenstein.O

theorem original_dyadic_retained_energy
    (om Φ:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support om⊆Set.Icc a b):
    ∃(omega₁ omega₂:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo ∧ lo≤ hi ∧
      HasCompactSupport (omega₁:ℝ→ℂ) ∧ HasCompactSupport (omega₂:ℝ→ℂ) ∧
      tsupport (omega₁:ℝ→ℂ)⊆Set.Icc lo hi ∧ tsupport (omega₂:ℝ→ℂ)⊆Set.Icc lo hi ∧
    ∀eps:ℝ,0<eps→∀J:ℕ,∃C:ℝ,0≤ C ∧
    ∀{ι:Type}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,lambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)
      (Z M r ell V eta tau Fmax Γ K theta Benergy:ℝ)
      (_hZ:1<Z)(_hbin:2≤ Z^eta)(_hM:0≤ M)(_hF:r+3*ell+V≤ Fmax)
      (_hQ:∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta))
      (_hΨ:∀u,‖Ψ u‖≤1)(_hΓ:0≤Γ)(_hK:0<K)(_hB:0≤ Benergy)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)(_hβ:∀I∈labels,∀v∈Q,‖β I v‖≤Γ),
      let Y:=Z^(2*Fmax+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource om theta (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hg β cutoff Ψ m mark W Φ K);
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 0))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        refinedChildEnergy p hp hg hinj pool Q k.1 k.2.1 (labelGate p k.2.2) true Ψ m mark omega₁
          ((physicalScales (Z^r) k.1 k.2.1) 7)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤ Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 1))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        refinedChildEnergy p hp hg hinj pool Q k.1 k.2.1 (labelGate p k.2.2) false Ψ m mark omega₂
          ((physicalScales (Z^r) k.1 k.2.1) 8)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤ Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (Z^(-r-2*ell-V)*Z^M)*‖originalRetainedFamily p hp hg pool Q labels β Ψ m mark W Φ K Y cutoff (fun _=>1)‖≤
        C*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*
          Z^((2*Fmax+15*eta+tau)*eps)*(keys.card:ℝ):=by
  let g₁:=priorityLogWindow om a b ha hs true
  let g₂:=priorityLogWindow om a b ha hs false
  let M₀:=|Real.log a|+|Real.log b|
  have hm:0≤ M₀:=by dsimp [M₀];positivity
  obtain ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,he⟩:=original_refined_cell_physical_budget
    g₁ g₂ Φ M₀ M₀ hm hm (priorityLogWindow_support om a b ha hs true) (priorityLogWindow_support om a b ha hs false)
  refine ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro eps heps J
  obtain ⟨Cp,Kp,hCp,hKp,hcell⟩:=he eps heps 0 J
  refine ⟨Cp*Kp,mul_nonneg hCp hKp.le,?_⟩
  intro ι _ p hp _ hg hinj hcop hc hpr pool Q labels β Ψ m mark Z M r ell V eta tau Fmax Γ K theta Benergy
    hZ hbin hM hF hQ hΨ hΓ hK hB hsf hn hβ Y cutoff W source keys hleft hright
  have hz:0<Z:=zero_lt_one.trans hZ
  have hsum:=original_retained_joint_profile_bound p hp hcop hg pool Q labels β cutoff Ψ m mark
    om a b ha hs Φ K Y (Z^r) theta (Real.rpow_pos_of_pos hz _) (fun _=>1) (by intro i;norm_num)
  have hnrm:0≤ Z^(-r-2*ell-V)*Z^M:=mul_nonneg (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _)
  apply (mul_le_mul_of_nonneg_left hsum hnrm).trans
  rw [Finset.mul_sum]
  have hpoint:∀k∈keys,
      (Z^(-r-2*ell-V)*Z^M)*‖refinedCellRows p hp hcop hg pool Q labels β cutoff Ψ m mark k.1 k.2.1 (labelGate p k.2.2)
        (positiveSource g₁ 1 (-theta)) (positiveSource g₂ 1 theta) Φ K Y (physicalScales (Z^r) k.1 k.2.1)‖≤
      (Cp*Kp)*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*Z^((2*Fmax+15*eta+tau)*eps):=by
    intro k hk
    let T₁:=(physicalScales (Z^r) k.1 k.2.1) 7
    let T₂:=(physicalScales (Z^r) k.1 k.2.1) 8
    have hT₁:0<T₁:=physicalScales_pos _ (Real.rpow_pos_of_pos hz _) _ _ 7
    have hT₂:0<T₂:=physicalScales_pos _ (Real.rpow_pos_of_pos hz _) _ _ 8
    have hY:0<firstCellRadius Z M r ell V eta tau k.1 k.2.2:=Real.rpow_pos_of_pos hz _
    have hl:=hleft k hk
    have hr:=hright k hk
    have heta:0≤ eta:=by
      apply (Real.rpow_le_rpow_left_iff hZ).mp
      rw [Real.rpow_zero]
      linarith
    have hL:0≤ eta*Real.log Z:=mul_nonneg heta (Real.log_nonneg hZ.le)
    have he' := hcell p hp hg hinj hcop hc hpr pool Q labels β cutoff Ψ m mark Γ Y
      (firstCellRadius Z M r ell V eta tau k.1 k.2.2) hΨ hΓ hY hsf hn hβ k.1 k.2.1 (labelGate p k.2.2)
      (fun x hx I _=>first_dyadic_refined_cutoff p pool Q k.1 k.2.2 Z M r ell V eta tau x hx I)
      T₁ T₂ K theta (eta*Real.log Z) hT₁ hT₂ hK hL Benergy Z M r ell V (dyadicExponent Z (k.1 3))
      (dyadicExponent Z (k.1 0)) (dyadicExponent Z (k.1 1)) (dyadicExponent Z (k.1 2))
      (dyadicExponent Z (k.1 4)) (dyadicExponent Z k.2.1) (dyadicExponent Z (k.1 5)) eta
      hB hz (physicalScales_rpow Z r hZ k.1 k.2.1) rfl hl hr
    have hrad:=first_live_cell_radius_cap p hp pool Q labels Y _ Z M r ell V eta tau Fmax hZ hbin hM hF hQ k hk
    have hpow:=Real.rpow_le_rpow hY.le hrad heps.le
    rw [←Real.rpow_mul hz.le] at hpow
    simp only [pow_zero,div_one,norm_neg] at he'
    calc
      _≤(Γ^2*Kp*(firstCellRadius Z M r ell V eta tau k.1 k.2.2)^eps*Benergy)*
          (Cp*((1+‖theta‖)^InverseClippingProfiles.momentOrder J*(1+‖theta‖)^InverseClippingProfiles.momentOrder J)):=he'
      _≤(Γ^2*Kp*Z^((2*Fmax+15*eta+tau)*eps)*Benergy)*
          (Cp*((1+‖theta‖)^InverseClippingProfiles.momentOrder J*(1+‖theta‖)^InverseClippingProfiles.momentOrder J)):=by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) hB
      _=_:=by rw [show 2*InverseClippingProfiles.momentOrder J=InverseClippingProfiles.momentOrder J+InverseClippingProfiles.momentOrder J by omega,pow_add];ring
  calc
    _≤∑_k∈keys,(Cp*Kp)*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*Z^((2*Fmax+15*eta+tau)*eps):=
      Finset.sum_le_sum hpoint
    _=_:=by simp [mul_comm]

end InverseMoment

end

noncomputable section
namespace InverseMomentFirstOriginalProfile
open InverseMoment Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseSecondSourceBlocks
open Eisenstein (ringComplex)
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg : ∀i,lambda∉Ideal.span {p i})

def liveNormCap (L B Y : ℝ) : ℝ := max Y (max L (max (L*B^2) (B^2)))

theorem original_live_joint_card (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) (β : Ideal O→(ι→₀ℕ)→ℂ)
    (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K L B : ℝ)
    (hB : 0≤ B) (hQ : ∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ B)
    (hlabels : ∀I∈labels,I≠0) (hW : ∀y,W y≠0→y≤ L) :
    (liveJointKeys p
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) pool
      (sourceSummand p hp hg β cutoff Ψ m mark W Φ K)).card≤
        (dyadIndex (liveNormCap L B Y)+1)^8 := by
  apply liveJointKeys_card_of_norm_cap
  intro x hx j hj hn
  obtain ⟨h₁,h₂,h₃⟩ := InverseMomentFirstLiveCaps.original_live_norm_caps p hp hg
    pool Q labels Y β cutoff Ψ m mark W Φ K L B hB hQ hlabels hW x hx j hn
  have hc : ∀i : Fin 6,(![L,L,L,L*B^2,B^2,Y] : Fin 6→ℝ) i≤ liveNormCap L B Y := by
    intro i
    fin_cases i <;> simp [liveNormCap,le_max_iff]
  refine ⟨fun i=>⟨lt_of_lt_of_le zero_lt_one (original_source_norms_ge_one p hp pool Q labels Y x hx i),(h₁ i).trans (hc i)⟩,?_,?_⟩
  · exact ⟨primeProductNorm_pos p hp _,h₂.trans (le_max_of_le_right (le_max_left _ _))⟩
  · refine ⟨lt_of_lt_of_le zero_lt_one (element_norm_ge_one _ (primeProduct_ne_zero p hp _ _)),?_⟩
    exact h₃.trans (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))

theorem original_twisted_live_joint_card (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) (β : Ideal O→(ι→₀ℕ)→ℂ)
    (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K b B X theta : ℝ)
    (hX : 0<X) (hB : 0≤ B) (hQ : ∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ B)
    (hlabels : ∀I∈labels,I≠0) (hW : ∀y,W y≠0→y≤ b) :
    (liveJointKeys p
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) pool
      (sourceSummand p hp hg β cutoff Ψ m mark
        (fun y=>CompletedHeight.normTwistedSource W theta (y/X)) Φ K)).card≤
        (dyadIndex (liveNormCap (b*X) B Y)+1)^8 := by
  apply original_live_joint_card p hp hg pool Q labels Y β cutoff Ψ m mark _ Φ K (b*X) B hB hQ hlabels
  intro y hy
  have hwy : W (y/X)≠0 := by
    intro hz
    exact hy (by simp [CompletedHeight.normTwistedSource,hz])
  exact (div_le_iff₀ hX).mp (hW _ hwy)

end InverseMomentFirstOriginalProfile
end

noncomputable section
namespace InverseMomentFirstOriginalProfile
open InverseMoment Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseSecondSourceBlocks
open Eisenstein (ringComplex)
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

lemma liveNormCap_power_bound (b Lcap Z r ell F eta tau : ℝ)
    (_hb : 0 ≤ b) (hcap : 0 ≤ Lcap) (hZ : 2 ≤ Z)
    (hr : r ≤ Lcap) (hell : ell ≤ Lcap) (hF : 0 ≤ F) (hFcap : F ≤ Lcap)
    (heta : 0 ≤ eta) (heta1 : eta ≤ 1) (htau : 0 ≤ tau) (htau1 : tau ≤ 1) :
    1 ≤ liveNormCap (b*Z^r) (Z^(ell+eta)) (Z^(2*F+15*eta+tau)) ∧
    liveNormCap (b*Z^r) (Z^(ell+eta)) (Z^(2*F+15*eta+tau)) ≤
      max 1 b * Z^(3*Lcap+16) := by
  have hz : 0<Z := by linarith
  have hz1 : 1 ≤ Z := by linarith
  have hb1 : 1 ≤ max 1 b := le_max_left _ _
  have hbmax : b ≤ max 1 b := le_max_right _ _
  have hpow (a : ℝ) (ha : a ≤ 3*Lcap+16) : Z^a ≤ max 1 b*Z^(3*Lcap+16) :=
    (Real.rpow_le_rpow_of_exponent_le hz1 ha).trans (le_mul_of_one_le_left (Real.rpow_nonneg hz.le _) hb1)
  have hsq : (Z^(ell+eta))^2=Z^(2*(ell+eta)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
    congr 1
    ring
  refine ⟨(Real.one_le_rpow hz1 (by linarith : 0 ≤ 2*F+15*eta+tau)).trans (le_max_left _ _),?_⟩
  unfold liveNormCap
  apply max_le (hpow _ (by linarith))
  apply max_le
  · exact mul_le_mul hbmax (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith))
      (Real.rpow_nonneg hz.le _) (by linarith)
  apply max_le
  · rw [hsq,mul_assoc,←Real.rpow_add hz]
    exact mul_le_mul hbmax (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith))
      (Real.rpow_nonneg hz.le _) (by linarith)
  · rw [hsq]
    exact hpow _ (by linarith)

lemma dyadIndex_power_log_bound (b A : ℝ) (hb : 1 ≤ b) (hA : 0 ≤ A) :
    ∃ C : ℝ,0<C ∧ ∀ Z R : ℝ,2 ≤ Z → 1 ≤ R → R ≤ b*Z^A →
      ((dyadIndex R+1:ℕ):ℝ)^8 ≤ C*(1+Real.log Z)^8 := by
  let c := 1+Real.log b/Real.log 2+A/Real.log 2
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hcb : 0 ≤ Real.log b/Real.log 2 := div_nonneg (Real.log_nonneg hb) hl2.le
  have hcA : 0 ≤ A/Real.log 2 := div_nonneg hA hl2.le
  have hc : 0<c := by dsimp [c];linarith
  refine ⟨c^8,pow_pos hc _,?_⟩
  intro Z R hZ hR hbound
  have hz : 0<Z := by linarith
  have hr : 0<R := by linarith
  have hb0 : 0<b := by linarith
  have hlz : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
  have hf := Nat.floor_le (Real.logb_nonneg (by norm_num : (1:ℝ)<2) hR)
  have hl := Real.log_le_log hr hbound
  rw [Real.log_mul (ne_of_gt hb0) (ne_of_gt (Real.rpow_pos_of_pos hz _)),Real.log_rpow hz] at hl
  have hstep : ((dyadIndex R+1:ℕ):ℝ) ≤ c*(1+Real.log Z) := by
    simp only [Nat.cast_add,Nat.cast_one,dyadIndex,Real.logb] at *
    have hd := div_le_div_of_nonneg_right hl hl2.le
    have hmul : 0 ≤ (Real.log b/Real.log 2)*Real.log Z := mul_nonneg hcb hlz
    dsimp [c]
    have he : (Real.log b+A*Real.log Z)/Real.log 2=Real.log b/Real.log 2+(A/Real.log 2)*Real.log Z := by ring
    rw [he] at hd
    nlinarith
  calc
    _ ≤ (c*(1+Real.log Z))^8 := pow_le_pow_left₀ (by positivity) hstep 8
    _= _ := by rw [mul_pow]

theorem live_joint_scalar_log_budget (b Lcap : ℝ) (hb : 0 ≤ b) (hcap : 0 ≤ Lcap) :
    ∃ C : ℝ,0<C ∧ ∀ Z r ell F eta tau : ℝ,2 ≤ Z → r ≤ Lcap → ell ≤ Lcap →
      0 ≤ F → F ≤ Lcap → 0 ≤ eta → eta ≤ 1 → 0 ≤ tau → tau ≤ 1 →
      ((dyadIndex (liveNormCap (b*Z^r) (Z^(ell+eta)) (Z^(2*F+15*eta+tau)))+1:ℕ):ℝ)^8 ≤
        C*(1+Real.log Z)^8 := by
  obtain ⟨C,hC,hcount⟩ := dyadIndex_power_log_bound (max 1 b) (3*Lcap+16) (le_max_left _ _) (by linarith)
  refine ⟨C,hC,?_⟩
  intro Z r ell F eta tau hZ hr hell hF hFcap heta heta1 htau htau1
  have hc := liveNormCap_power_bound b Lcap Z r ell F eta tau hb hcap hZ hr hell hF hFcap heta heta1 htau htau1
  exact hcount Z _ hZ hc.1 hc.2

lemma log_eighth_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ Z : ℝ,1 ≤ Z → (1+Real.log Z)^8 ≤ C*Z^ε := by
  let δ := ε/8
  have hd : 0<δ := by dsimp [δ];positivity
  refine ⟨(1+1/δ)^8,by positivity,?_⟩
  intro Z hZ
  have hz : 0<Z := by linarith
  have h1 := Real.one_le_rpow hZ hd.le
  have hl := Real.log_le_rpow_div hz.le hd
  have hb : 1+Real.log Z ≤ (1+1/δ)*Z^δ := by
    calc
      _ ≤ Z^δ+Z^δ/δ := add_le_add h1 hl
      _=_ := by ring
  calc
    _ ≤ ((1+1/δ)*Z^δ)^8 := pow_le_pow_left₀ (by linarith [Real.log_nonneg hZ]) hb 8
    _=(1+1/δ)^8*Z^ε := by
      have he : (Z^δ)^8=Z^ε := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
        congr 1
        dsimp [δ]
        ring
      rw [mul_pow,he]

theorem live_joint_scalar_small_power (b Lcap ε : ℝ) (hb : 0 ≤ b) (hcap : 0 ≤ Lcap) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ Z r ell F eta tau : ℝ,2 ≤ Z → r ≤ Lcap → ell ≤ Lcap →
      0 ≤ F → F ≤ Lcap → 0 ≤ eta → eta ≤ 1 → 0 ≤ tau → tau ≤ 1 →
      ((dyadIndex (liveNormCap (b*Z^r) (Z^(ell+eta)) (Z^(2*F+15*eta+tau)))+1:ℕ):ℝ)^8 ≤ C*Z^ε := by
  obtain ⟨C₁,hC₁,h₁⟩ := live_joint_scalar_log_budget b Lcap hb hcap
  obtain ⟨C₂,hC₂,h₂⟩ := log_eighth_small_power ε hε
  refine ⟨C₁*C₂,mul_pos hC₁ hC₂,?_⟩
  intro Z r ell F eta tau hZ hr hell hF hFcap heta heta1 htau htau1
  exact (h₁ Z r ell F eta tau hZ hr hell hF hFcap heta heta1 htau htau1).trans
    ((mul_le_mul_of_nonneg_left (h₂ Z (by linarith)) hC₁.le).trans_eq (mul_assoc _ _ _).symm)

theorem original_live_joint_small_power (b Lcap ε : ℝ) (hb : 0 ≤ b) (hcap : 0 ≤ Lcap) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι → O)(hp : ∀i,p i≠0)
      [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i})
      (pool : Finset ι)(Q : Finset (ι→₀ℕ))(labels : Finset (Ideal O))
      (β : Ideal O → (ι→₀ℕ) → ℂ)(cutoff : CubeCoordinates ι → Finset ι → Ideal O → Finset ι → ℝ)
      (Ψ : O→*ℂ)(m : O)(mark : (ι→₀ℕ) → Finset ι → ℂ)(W : ℝ → ℂ)(Φ : 𝓢(ℝ,ℂ))
      (K Z r ell F eta tau theta : ℝ),
      2 ≤ Z → r ≤ Lcap → ell ≤ Lcap → 0 ≤ F → F ≤ Lcap → 0 ≤ eta → eta ≤ 1 → 0 ≤ tau → tau ≤ 1 →
      (∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2 ≤ Z^(ell+eta)) →
      (∀I∈labels,I≠0) → (∀y,W y≠0 → y ≤ b) →
      ((liveJointKeys p
        (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1)
          (Z^(2*F+15*eta+tau))) pool
        (sourceSummand p hp hg β cutoff Ψ m mark
          (fun y=>CompletedHeight.normTwistedSource W theta (y/Z^r)) Φ K)).card:ℝ) ≤ C*Z^ε := by
  obtain ⟨C,hC,hcount⟩ := live_joint_scalar_small_power b Lcap ε hb hcap hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hcop hg pool Q labels β cutoff Ψ m mark W Φ K Z r ell F eta tau theta
    hZ hr hell hF hFcap heta heta1 htau htau1 hQ hlabels hW
  have hz : 0<Z := by linarith
  have he := original_twisted_live_joint_card p hp hg pool Q labels (Z^(2*F+15*eta+tau))
    β cutoff Ψ m mark W Φ K b (Z^(ell+eta)) (Z^r) theta
    (Real.rpow_pos_of_pos hz _) (Real.rpow_nonneg hz.le _) hQ hlabels hW
  have he' : ((liveJointKeys p
        (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1)
          (Z^(2*F+15*eta+tau))) pool
        (sourceSummand p hp hg β cutoff Ψ m mark
          (fun y=>CompletedHeight.normTwistedSource W theta (y/Z^r)) Φ K)).card:ℝ) ≤
      (((dyadIndex (liveNormCap (b*Z^r) (Z^(ell+eta)) (Z^(2*F+15*eta+tau))))+1:ℕ):ℝ)^8 := by exact_mod_cast he
  exact he'.trans (hcount Z r ell F eta tau hZ hr hell hF hFcap heta heta1 htau htau1)

end InverseMomentFirstOriginalProfile
end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstProfileUniform
open InverseAmbientProfileTower JointLogSeparation CompletedHeight
open Eisenstein (ringComplex)
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O"=>Eisenstein.O

theorem original_dyadic_retained_budget
    (om Φ:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support om⊆Set.Icc a b) (Lcap:ℝ)(hcap:0≤ Lcap)(hb:0≤ b):
    ∃(omega₁ omega₂:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo ∧ lo≤ hi ∧
      HasCompactSupport (omega₁:ℝ→ℂ) ∧ HasCompactSupport (omega₂:ℝ→ℂ) ∧
      tsupport (omega₁:ℝ→ℂ)⊆Set.Icc lo hi ∧ tsupport (omega₂:ℝ→ℂ)⊆Set.Icc lo hi ∧
    ∀eps:ℝ,0<eps→∀J:ℕ,∃C:ℝ,0≤ C ∧
    ∀{ι:Type}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,lambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)
      (Z M r ell V eta tau Fmax Γ K theta Benergy:ℝ)
      (_hZ:2≤ Z)(_hbin:2≤ Z^eta)(_hM:0≤ M)(_hF:r+3*ell+V≤ Fmax)
      (_hQ:∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta))
      (_hrcap:r≤ Lcap)(_hellcap:ell≤ Lcap)(_hF0:0≤ Fmax)(_hFcap:Fmax≤ Lcap)
      (_heta:0≤ eta)(_heta1:eta≤1)(_htau:0≤ tau)(_htau1:tau≤1)
      (_hΨ:∀u,‖Ψ u‖≤1)(_hΓ:0≤Γ)(_hK:0<K)(_hB:0≤ Benergy)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)(_hβ:∀I∈labels,∀v∈Q,‖β I v‖≤Γ),
      let Y:=Z^(2*Fmax+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource om theta (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hg β cutoff Ψ m mark W Φ K);
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 0))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        refinedChildEnergy p hp hg hinj pool Q k.1 k.2.1 (labelGate p k.2.2) true Ψ m mark omega₁
          ((physicalScales (Z^r) k.1 k.2.1) 7)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤ Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 1))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        refinedChildEnergy p hp hg hinj pool Q k.1 k.2.1 (labelGate p k.2.2) false Ψ m mark omega₂
          ((physicalScales (Z^r) k.1 k.2.1) 8)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤ Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (Z^(-r-2*ell-V)*Z^M)*‖originalRetainedFamily p hp hg pool Q labels β Ψ m mark W Φ K Y cutoff (fun _=>1)‖≤
        C*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*
          Z^((2*Fmax+15*eta+tau)*eps+eps) :=by
  obtain ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,he⟩:=original_dyadic_retained_energy om Φ a b ha hs
  refine ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro eps heps J
  obtain ⟨C,hC,henergy⟩:=he eps heps J
  obtain ⟨Cc,hCc,hcount⟩:=original_live_joint_small_power b Lcap eps hb hcap heps
  refine ⟨C*Cc,mul_nonneg hC hCc.le,?_⟩
  intro ι _ p hp _ hg hinj hcop hc hpr pool Q labels β Ψ m mark Z M r ell V eta tau Fmax Γ K theta Benergy
    hZ hbin hM hF hQ hrcap hellcap hF0 hFcap heta heta1 htau htau1 hΨ hΓ hK hB hsf hn hβ
    Y cutoff W source keys hleft hright
  have hz:0<Z:=by linarith
  have hZ1:1<Z:=by linarith
  have he':=henergy p hp hg hinj hcop hc hpr pool Q labels β Ψ m mark Z M r ell V eta tau Fmax Γ K theta Benergy
    hZ1 hbin hM hF hQ hΨ hΓ hK hB hsf hn hβ hleft hright
  have hnkey:=hcount p hp hcop hg pool Q labels β cutoff Ψ m mark om Φ K Z r ell Fmax eta tau theta
    hZ hrcap hellcap hF0 hFcap heta heta1 htau htau1 hQ hn (fun y hy=>(hs hy).2)
  apply he'.trans
  calc
    _≤ C*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*
        Z^((2*Fmax+15*eta+tau)*eps)*(Cc*Z^eps):=
      mul_le_mul_of_nonneg_left hnkey (by positivity)
    _=_:=by rw [Real.rpow_add hz];ring

end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

theorem full_first_dyadic_marked_rapid_tail (Mmax Fmax eta tau saving:ℝ)
    (hMm:0≤ Mmax) (hFm:0≤ Fmax) (heta:0≤ eta) (htau:0<tau) :
    ∃(s:Finset (ℕ×ℕ)) (Ctail:ℝ),0<Ctail ∧
    ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i})
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
      (slots:Finset σ) (lists:σ→Finset ι) (weights:σ→ι→ℂ)
      (extra₁ extra₂:CubeCoordinates ι→Finset ι)
      (test₁ test₂:CubeCoordinates ι→Finset ι→ℂ) (W:𝓢(ℝ,ℂ))
      (Z M r ell V Γ G₁ G₂:ℝ),
      1<Z → 2≤ Z^eta → 0≤ M → M≤ Mmax → 0≤ ell → 0≤ V → -eta≤ r → r+3*ell+V≤ Fmax →
      0≤Γ → 0≤ G₁ → 0≤ G₂ →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖ringComplex (primeProduct p b.support b.leftExponent)‖^2≤ Z^(ell+eta)) →
      (∀b∈bs,‖ringComplex (primeProduct p b.support b.rightExponent)‖^2≤ Z^(ell+eta)) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤ Z^(V+eta)) →
      (∀b∈bs,∀C∈(pool\b.support).powerset,∀I∈labels,‖a b C I‖≤Γ) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖weights i k‖≤1) →
      (∀b∈bs,extra₁ b⊆b.support) → (∀b∈bs,extra₂ b⊆b.support) →
      (∀b∈bs,∀U,‖test₁ b U‖≤ G₁) → (∀b∈bs,∀U,‖test₂ b U‖≤ G₂) →
      (∀b∈bs,∀U,test₁ b U≠0→primeProductNorm p U≤ Z^(r+eta)) →
      (∀b∈bs,∀U,test₂ b U≠0→primeProductNorm p U≤ Z^(r+eta)) →
      ‖∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*
        canonicalCubeDualTail p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂
          (cubicIdealGenerator I)
          (fun U=>primeMark slots lists weights (extra₁ b∪U)*test₁ b U)
          (fun U=>primeMark slots lists weights (extra₂ b∪U)*test₂ b U) W (Z^M)
          (firstDyadicPhysicalCutoff p b C I Z M r ell V eta tau)‖≤
      Ctail*Γ*G₁*G₂*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*Z^(-saving) := by
  have hdc := diagonalControl_nonneg sieveCutoff
  let saving':=saving+4*Fmax+14*eta
  obtain ⟨s,Ct,Cm,hCt,hCm,hloc⟩:=first_whole_cube_rapid_physical_tail 1 (by norm_num)
    Mmax Fmax eta tau saving' hMm hFm heta htau
  obtain ⟨Ca,hCa,hagg⟩:=full_first_tail_from_local 1 (by norm_num)
  refine ⟨s,Ca*(4*(1+diagonalControl sieveCutoff)^2)*Cm^2*Ct,by positivity,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ slots lists weights extra₁ extra₂
    test₁ test₂ W Z M r ell V Γ G₁ G₂ hZ hbin hM hMmax hell hV hr hwhole hΓ hG₁ hG₂ hΨ₁ hΨ₂
    hadm hb₁ hb₂ hI0 hIF ha hslots hw he₁ he₂ ht₁ ht₂ hs₁ hs₂
  have hz:0<Z:=zero_lt_one.trans hZ
  let B:=Z^(ell+eta)
  let L:=Z^(r+eta)
  let E:=(4*(1+diagonalControl sieveCutoff)^2)*(Cm*(B^2*L)*G₁)*(Cm*(B^2*L)*G₂)*
    (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*Z^(-saving')
  have hB:1≤ B:=Real.one_le_rpow hZ.le (by linarith)
  have hL:0<L:=Real.rpow_pos_of_pos hz _
  have hE:0≤ E:=by dsimp [E,B,L];positivity
  have hextra (extra:CubeCoordinates ι→Finset ι) (he:∀b∈bs,extra b⊆b.support)
      (b:CubeCoordinates ι) (hb:b∈bs):primeProductNorm p (extra b)≤ B^2:=
    (primeProductNorm_mono p hp (he b hb)).trans
      (cube_whole_support_dyad p hp b B (zero_le_one.trans hB) (hb₁ b hb) (hb₂ b hb))
  have hlocal (b:CubeCoordinates ι) (hb:b∈bs) (C:Finset ι)
      (hC:C∈boundedPrimeSupports p (pool\b.support) L) (I:Ideal O) (hI:I∈labels)
      (D:Finset ι) (hD:D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset):
      ‖firstLocalPhysicalTail p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂ (cubicIdealGenerator I)
        (fun U=>primeMark slots lists weights (extra₁ b∪U)*test₁ b U)
        (fun U=>primeMark slots lists weights (extra₂ b∪U)*test₂ b U) W (Z^M)
        (firstDyadicPhysicalCutoff p b C I Z M r ell V eta tau) D‖≤ E:=by
    have hCB:Disjoint C b.support:=Finset.disjoint_left.mpr (fun i hi hib=>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hC).1) hi)).2 hib)
    have hupper (x:ℝ) (hx:1≤ x):x≤ Z^(firstDyadicExponent Z x+eta):=
      (first_dyadic_bounds Z eta x hZ hbin hx).2.2
    have hlower (x:ℝ) (hx:1≤ x):Z^(firstDyadicExponent Z x-eta)≤ x:=by
      exact (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith : firstDyadicExponent Z x-eta≤ firstDyadicExponent Z x)).trans
        (first_dyadic_bounds Z eta x hZ hbin hx).2.1
    have hjpos:0<‖ringComplex (jLabel p b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2:=
      SecondPassIntegration.elementNorm_pos _ (primeProduct_ne_zero p hp _ _)
    have he:=hloc p hp hinj hcop hg hc pool b C D (extra₁ b) (extra₂ b) I Ψ₁ Ψ₂ m₁ m₂
      slots lists weights (test₁ b) (test₂ b) W (B^2) G₁ G₂ Z M r ell V
      (firstDyadicExponent Z (primeProductNorm p C))
      (firstDyadicExponent Z (‖ringComplex (jLabel p b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2))
      (fun D=>firstDyadicExponent Z (primeProductNorm p D))
      (hadm b hb) hCB (Finset.mem_powerset.mp hD) (hI0 I hI) (sq_nonneg _) hG₁ hG₂ hZ.le hM hMmax
      hell hV hr hwhole (Finset.mem_filter.mp hC).2 (hextra extra₁ he₁ b hb) (hextra extra₂ he₂ b hb)
      hΨ₁ hΨ₂ hslots hw (ht₁ b hb) (ht₂ b hb) (hs₁ b hb) (hs₂ b hb) (hb₁ b hb) (hb₂ b hb) (hIF I hI)
      (hupper _ (primeProductNorm_ge_one p hp D)) (hlower _ (primeProductNorm_ge_one p hp C))
      (hlower _ (SchwartzPlanePoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _)))
    simpa only [firstLocalPhysicalTail,firstDyadicPhysicalCutoff,firstDyadicRadius,Real.rpow_one,E,L] using he
  have he:=hagg p hp hinj hcop hg hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂
    (fun b U=>primeMark slots lists weights (extra₁ b∪U)*test₁ b U)
    (fun b U=>primeMark slots lists weights (extra₂ b∪U)*test₂ b U) W (Z^M) B L (Z^(V+eta)) Γ E
    (fun b C I=>firstDyadicPhysicalCutoff p b C I Z M r ell V eta tau)
    hB hL (Real.one_le_rpow hZ.le (by linarith)) hΓ hE hΨ₁ hΨ₂ hadm hb₁ hb₂ hI0 hIF ha
    (fun b hb U hU=>hs₁ b hb U (mul_ne_zero_iff.mp hU).2) hlocal
  apply he.trans
  have hexp:B^9*L^4*Z^(V+eta)*Z^(-saving')≤ Z^(-saving):=by
    dsimp [B,L]
    rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_mul_natCast hz.le,
      ←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [saving']
    norm_num
    linarith
  have hm:=mul_le_mul_of_nonneg_left hexp
    (show 0≤ Ca*(4*(1+diagonalControl sieveCutoff)^2)*Cm^2*Ct*Γ*G₁*G₂*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) from by positivity)
  convert hm using 1
  · dsimp only [E]
    norm_num
    ring

end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic SchwartzPlanePoisson
open Eisenstein (ringComplex)
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,lambda∉Ideal.span {p i})
  (hinj : Function.Injective (fun i=>Ideal.span {p i}))
  (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
include hinj hc in
theorem first_variable_zero_common_bound
    (pool : Finset ι) (b : CubeCoordinates ι) (labels : Finset (Ideal O))
    (a : Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂ : O→*ℂ)
    (hΨ₁ : ∀u,‖Ψ₁ u‖≤1) (hΨ₂ : ∀u,‖Ψ₂ u‖≤1)
    (m₁ m₂ : O) (H₁ H₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ))
    (Γ G₁ G₂ L K : ℝ) (hΓ : 0≤Γ) (hG₁ : 0≤ G₁) (hG₂ : 0≤ G₂) (hL : 0<L)
    (ha : ∀C∈(pool\b.support).powerset,∀I∈labels,‖a C I‖≤Γ)
    (hH₁ : ∀U,‖H₁ U‖≤ G₁) (hH₂ : ∀U,‖H₂ U‖≤ G₂) (hsupp : ∀U,H₁ U≠0→primeProductNorm p U≤ L) :
    ‖∑C∈(pool\b.support).powerset,∑I∈labels,a C I*
      canonicalCubeDualZero p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂
        (cubicIdealGenerator I)
        H₁ H₂ W K‖≤
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        ((1+diagonalControl sieveCutoff)*(L))*(labels.card:ℝ)*(Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)) else 0 := by
  let z (C:Finset ι) (I:Ideal O):ℂ:=canonicalCubeDualZero p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂
    (cubicIdealGenerator I)
    H₁ H₂ W K
  let Q:ℝ:=Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)
  have hQ:0≤ Q:=by dsimp [Q];positivity
  have heq : (∑C∈(pool\b.support).powerset,∑I∈labels,a C I*z C I)=
      ∑C∈boundedPrimeSupports p (pool\b.support) (L),∑I∈labels,a C I*z C I := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro C hC hnot
    have hbnd : ¬primeProductNorm p C≤ L:=fun h=>hnot (Finset.mem_filter.mpr ⟨hC,h⟩)
    apply Finset.sum_eq_zero
    intro I hI
    have hz : H₁ (b.rightDivisor∪C)=0 := by
      by_contra hh
      exact hbnd ((primeProductNorm_mono p hp Finset.subset_union_right).trans (hsupp _ hh))
    have hz' : z C I=0 := by
      dsimp only [z]
      rw [canonicalCubeDualZero_eq_density p hp hg hinj]
      split_ifs <;> simp [hz]
    rw [hz',mul_zero]
  change ‖∑C∈(pool\b.support).powerset,∑I∈labels,a C I*z C I‖≤_
  rw [heq]
  by_cases hb : cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅
  · rw [if_pos hb]
    have hpnt (C:Finset ι) (hC:C∈boundedPrimeSupports p (pool\b.support) (L)) (I:Ideal O) (hI:I∈labels):‖a C I*z C I‖≤ Q:=by
      rw [norm_mul]
      have hz:=canonicalCubeDualZero_norm_le_of_good p hp hg hinj hc pool b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂
        (cubicIdealGenerator I) H₁ H₂ W K
      rw [if_pos hb] at hz
      have hz' : ‖z C I‖≤ G₁*G₂ * |K| * ‖paperRadialFourier W 0‖ := by
        apply hz.trans
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul (hH₁ _) (hH₂ _) (norm_nonneg _) hG₁) (abs_nonneg _)) (norm_nonneg _)
      exact mul_le_mul (ha C (Finset.mem_filter.mp hC).1 I hI) hz' (norm_nonneg _) hΓ
    calc
      _ ≤ ∑C∈boundedPrimeSupports p (pool\b.support) (L),∑I∈labels,‖a C I*z C I‖:=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun C hC=>norm_sum_le _ _))
      _ ≤ ∑C∈boundedPrimeSupports p (pool\b.support) (L),∑I∈labels,Q:=
        Finset.sum_le_sum (fun C hC=>Finset.sum_le_sum (fun I hI=>hpnt C hC I hI))
      _ = ((boundedPrimeSupports p (pool\b.support) (L)).card:ℝ)*(labels.card:ℝ)*Q:=by simp;ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (boundedPrimeSupports_card_positive p hp hinj _ _ hL) (Nat.cast_nonneg _)) hQ
  · rw [if_neg hb]
    have hz (C:Finset ι) (I:Ideal O):z C I=0:=by
      dsimp [z]
      rw [canonicalCubeDualZero_eq_density p hp hg hinj,if_neg hb]
    simp only [hz,mul_zero,Finset.sum_const_zero,norm_zero,le_refl]

end
theorem full_variable_first_zero_bound (ε : ℝ) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ)
      (m₁ m₂:O) (H₁ H₂:CubeCoordinates ι→Finset ι→ℂ) (W:𝓢(ℝ,ℂ)) (Γ G₁ G₂ L K B F:ℝ),
      0≤Γ → 0≤ G₁ → 0≤ G₂ → 0<L → 1≤ B → 1≤ F →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖ringComplex (primeProduct p b.support b.leftExponent)‖^2≤ B) →
      (∀b∈bs,‖ringComplex (primeProduct p b.support b.rightExponent)‖^2≤ B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤ F) →
      (∀b∈bs,∀D∈(pool\b.support).powerset,∀I∈labels,‖a b D I‖≤Γ) →
      (∀b∈bs,∀U,‖H₁ b U‖≤ G₁) → (∀b∈bs,∀U,‖H₂ b U‖≤ G₂) → (∀b∈bs,∀U,H₁ b U≠0→primeProductNorm p U≤ L) →
      ‖∑b∈bs,∑D∈(pool\b.support).powerset,∑I∈labels,a b D I*
        canonicalCubeDualZero p hp hg pool b D Ψ₁ Ψ₂ m₁ m₂
          (cubicIdealGenerator I)
          (H₁ b) (H₂ b) W K‖≤
      C*B^(1+ε)*(L)*F*(Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)) := by
  have hdc := diagonalControl_nonneg sieveCutoff
  obtain ⟨C,hC,hcount⟩:=cube_coordinates_parity_count ε hε
  refine ⟨C*(1+diagonalControl sieveCutoff)*(1+diagonalControl sieveCutoff),by positivity,?_⟩
  intro ι _ p hp _ hcop hg hinj hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ H₁ H₂ W Γ G₁ G₂ L K B F hΓ hG₁ hG₂ hL hB hF hΨ₁ hΨ₂ hadm hb1 hb2 hI0 hIF ha hH₁ hH₂ hsupp
  let Q:=Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)
  let good:=fun b:CubeCoordinates ι=>cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅
  have hQ:0≤ Q:=by dsimp [Q];positivity
  have hlabel:(labels.card:ℝ)≤(1+diagonalControl sieveCutoff)*F:=
    (SchwartzPlanePoisson.finite_ideal_card_bound labels F hF hIF).trans
      (mul_le_mul_of_nonneg_right (by linarith) (zero_le_one.trans hF))
  have hbcount:((bs.filter good).card:ℝ)≤ C*B^(1+ε):=by
    have h:=hcount p hp hinj (bs.filter good) B 1 hB (by norm_num)
      (fun b hb=>hadm b (Finset.mem_filter.mp hb).1)
      (fun b hb=>hb1 b (Finset.mem_filter.mp hb).1)
      (fun b hb=>hb2 b (Finset.mem_filter.mp hb).1)
      (fun b hb=>by
        have he : cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ := (Finset.mem_filter.mp hb).2
        rw [he]
        simp)
    simpa only [mul_one] using h
  calc
    _ ≤ ∑b∈bs,‖∑D∈(pool\b.support).powerset,∑I∈labels,a b D I*
        canonicalCubeDualZero p hp hg pool b D Ψ₁ Ψ₂ m₁ m₂
          (cubicIdealGenerator I)
          (H₁ b) (H₂ b) W K‖:=norm_sum_le _ _
    _ ≤ ∑b∈bs,if good b then ((1+diagonalControl sieveCutoff)*(L))*(labels.card:ℝ)*Q else 0:=by
      apply Finset.sum_le_sum
      intro b hb
      exact first_variable_zero_common_bound p hp hg hinj hc pool b labels (a b) Ψ₁ Ψ₂ hΨ₁ hΨ₂
        m₁ m₂ (H₁ b) (H₂ b) W Γ G₁ G₂ L K hΓ hG₁ hG₂ hL (ha b hb) (hH₁ b hb) (hH₂ b hb) (hsupp b hb)
    _ = ((bs.filter good).card:ℝ)*(((1+diagonalControl sieveCutoff)*(L))*(labels.card:ℝ)*Q):=by
      rw [←Finset.sum_filter];simp
    _ ≤ (C*B^(1+ε))*(((1+diagonalControl sieveCutoff)*(L))*((1+diagonalControl sieveCutoff)*F)*Q):=by
      apply mul_le_mul hbcount _ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlabel (by positivity)) hQ
    _ = _ := by dsimp [Q];ring

end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic SchwartzPlanePoisson
open Eisenstein (ringComplex)
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

theorem full_marked_first_zero_bound (ε : ℝ) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (coeff:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ)
      (m₁ m₂:O) (test₁ test₂:CubeCoordinates ι→Finset ι→ℂ)
      (extra₁ extra₂ : CubeCoordinates ι→Finset ι)
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
      (W:𝓢(ℝ,ℂ)) (Γ G₁ G₂ L K B F:ℝ),
      0≤Γ → 0≤ G₁ → 0≤ G₂ → 0<L → 1≤ B → 1≤ F →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖ringComplex (primeProduct p b.support b.leftExponent)‖^2≤ B) →
      (∀b∈bs,‖ringComplex (primeProduct p b.support b.rightExponent)‖^2≤ B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤ F) →
      (∀b∈bs,∀D∈(pool\b.support).powerset,∀I∈labels,‖coeff b D I‖≤Γ) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀b∈bs,extra₁ b⊆b.support) → (∀b∈bs,extra₂ b⊆b.support) →
      (∀b∈bs,∀U,‖test₁ b U‖≤ G₁) → (∀b∈bs,∀U,‖test₂ b U‖≤ G₂) →
      (∀b∈bs,∀U,test₁ b U≠0→primeProductNorm p U≤ L) →
      (∀b∈bs,∀U,test₂ b U≠0→primeProductNorm p U≤ L) →
      ‖∑b∈bs,∑D∈(pool\b.support).powerset,∑I∈labels,coeff b D I*
        canonicalCubeDualZero p hp hg pool b D Ψ₁ Ψ₂ m₁ m₂
          (cubicIdealGenerator I)
          (fun U=>primeMark slots lists a (extra₁ b∪U)*test₁ b U)
          (fun U=>primeMark slots lists a (extra₂ b∪U)*test₂ b U) W K‖≤
      C*B^(1+ε)*L*F*Γ*((B^2*L)^ε)^2*(G₁*G₂ * |K| * ‖paperRadialFourier W 0‖) := by
  obtain ⟨Cz,hCz,hzero⟩ := full_variable_first_zero_bound ε hε
  obtain ⟨Cm,hCm,hmark⟩ := whole_cube_marked_test_uniform ε hε
  refine ⟨Cz*Cm^2,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc pool bs labels coeff Ψ₁ Ψ₂ m₁ m₂
    test₁ test₂ extra₁ extra₂ slots lists a W Γ G₁ G₂ L K B F
    hΓ hG₁ hG₂ hL hB hF hΨ₁ hΨ₂ hadm hb₁ hb₂ hI0 hIF hcoeff hslots ha
    he₁ he₂ htest₁ htest₂ hs₁ hs₂
  have hB0 : 0≤ B := le_trans zero_le_one hB
  have hextra (extra : CubeCoordinates ι→Finset ι) (he : ∀b∈bs,extra b⊆b.support)
      (b : CubeCoordinates ι) (hb : b∈bs) : primeProductNorm p (extra b)≤ B^2 :=
    (primeProductNorm_mono p hp (he b hb)).trans (cube_whole_support_dyad p hp b B hB0 (hb₁ b hb) (hb₂ b hb))
  have ht₁ (b : CubeCoordinates ι) (hb : b∈bs) :
      ∀U,‖primeMark slots lists a (extra₁ b∪U)*test₁ b U‖≤ Cm*(B^2*L)^ε*G₁ :=
    hmark p hp hcop slots lists a hslots ha (extra₁ b) (test₁ b) (B^2) G₁ L
      (sq_nonneg _) hG₁ hL.le (hextra extra₁ he₁ b hb) (htest₁ b hb) (hs₁ b hb)
  have ht₂ (b : CubeCoordinates ι) (hb : b∈bs) :
      ∀U,‖primeMark slots lists a (extra₂ b∪U)*test₂ b U‖≤ Cm*(B^2*L)^ε*G₂ :=
    hmark p hp hcop slots lists a hslots ha (extra₂ b) (test₂ b) (B^2) G₂ L
      (sq_nonneg _) hG₂ hL.le (hextra extra₂ he₂ b hb) (htest₂ b hb) (hs₂ b hb)
  have hh := hzero p hp hcop hg hinj hc pool bs labels coeff Ψ₁ Ψ₂ m₁ m₂
    (fun b U=>primeMark slots lists a (extra₁ b∪U)*test₁ b U)
    (fun b U=>primeMark slots lists a (extra₂ b∪U)*test₂ b U) W
    Γ (Cm*(B^2*L)^ε*G₁) (Cm*(B^2*L)^ε*G₂) L K B F
    hΓ (by positivity) (by positivity) hL hB hF hΨ₁ hΨ₂ hadm hb₁ hb₂ hI0 hIF hcoeff ht₁ ht₂
    (fun b hb U hU=>hs₁ b hb U (mul_ne_zero_iff.mp hU).2)
  exact hh.trans_eq (by ring)

end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic SchwartzPlanePoisson
open Eisenstein (ringComplex)
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

theorem original_reopened_marked_zero_bound (ε : ℝ) (hε : 0<ε) :
    ∃ C:ℝ,0<C ∧ ∀ {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (Q:Finset (ι→₀ℕ)) (labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ) (Ψ:O→*ℂ) (m:O)
      (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
      (W:ℝ→ℂ) (Φ:𝓢(ℝ,ℂ)) (Γ G L K B F:ℝ),
      0≤Γ → 0≤ G → 0<L → 1≤ B → 1≤ F →
      (∀u,‖Ψ u‖≤1) →
      (∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤ F) →
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀U,‖W (primeProductNorm p U)‖≤ G) →
      (∀U,W (primeProductNorm p U)≠0→primeProductNorm p U≤ L) →
      ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
        canonicalCubeDualZero p hp hg pool b C Ψ Ψ m m
          (cubicIdealGenerator I)
          (fun U=>primeMark slots lists a (U∪b.rightExponent.support)*W (primeProductNorm p U))
          (fun U=>primeMark slots lists a (U∪b.leftExponent.support)*W (primeProductNorm p U)) Φ K)‖≤
      C*B^(1+ε)*L*F*Γ^2*((B^2*L)^ε)^2*(G^2*|K| *‖paperRadialFourier Φ 0‖) := by
  obtain ⟨C,hC,he⟩ := full_marked_first_zero_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc pool Q labels β Ψ m slots lists a W Φ Γ G L K B F
    hΓ hG hL hB hF hΨ hQ hn hFlabels hβ hslots ha hW hs
  have hb := reopenedCubeFamily_cube_norms p Q B hQ
  have hcoeff := reopenedPairCoefficient_bound Q labels β Γ hΓ hβ
  have hh := he p hp hcop hg hinj hc pool (reopenedCubeFamily Q) labels
    (reopenedPairCoefficient β) Ψ Ψ m m (fun _ U=>W (primeProductNorm p U))
    (fun _ U=>W (primeProductNorm p U))
    (fun b=>b.rightExponent.support) (fun b=>b.leftExponent.support)
    slots lists a Φ (Γ^2) G G L K B F (sq_nonneg _) hG hG hL hB hF hΨ hΨ
    (reopenedCubeFamily_admissible Q) (fun b hb'=> (hb b hb').1) (fun b hb'=> (hb b hb').2)
    hn hFlabels (fun b hb C hC I hI=>hcoeff b hb C I hI) hslots ha
    (fun _ _=>Finset.subset_union_right) (fun _ _=>Finset.subset_union_left)
    (fun _ _=>hW) (fun _ _=>hW) (fun _ _=>hs) (fun _ _=>hs)
  simpa only [reopenedPhysicalSourceSum,Finset.union_comm,pow_two] using hh

end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic SchwartzPlanePoisson
open Eisenstein (ringComplex)
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O"=>Eisenstein.O

theorem original_first_zero_physical (ε:ℝ)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
      (Z M r ell V eta Γ G:ℝ),1<Z→0≤ ell+eta→0≤ V+eta→0≤Γ→0≤ G→
      (∀u,‖Ψ u‖≤1)→
      (∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta))→
      (∀I∈labels,I≠0)→(∀I∈labels,(Ideal.absNorm I:ℝ)≤ Z^(V+eta))→
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ)→
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀k∈lists i,‖a i k‖≤1)→
      (∀U,‖W (primeProductNorm p U)‖≤ G)→
      (∀U,W (primeProductNorm p U)≠0→primeProductNorm p U≤ Z^(r+eta))→
      Z^(-r-2*ell-V)*‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
        canonicalCubeDualZero p hp hg pool b C Ψ Ψ m m (cubicIdealGenerator I)
          (fun U=>primeMark slots lists a (U∪b.rightExponent.support)*W (primeProductNorm p U))
          (fun U=>primeMark slots lists a (U∪b.leftExponent.support)*W (primeProductNorm p U)) Φ (Z^M))‖≤
        C*Γ^2*G^2*‖paperRadialFourier Φ 0‖*Z^(M-ell+3*eta+ε*(5*ell+2*r+7*eta)):=by
  obtain ⟨C,hC,he⟩:=original_reopened_marked_zero_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc pool Q labels β Ψ m slots lists a W Φ Z M r ell V eta Γ G
    hZ hell hV hΓ hG hΨ hQ hn hlabels hβ hslots ha hW hs
  have hz:0<Z:=zero_lt_one.trans hZ
  have hb:=he p hp hcop hg hinj hc pool Q labels β Ψ m slots lists a W Φ Γ G
    (Z^(r+eta)) (Z^M) (Z^(ell+eta)) (Z^(V+eta)) hΓ hG
    (Real.rpow_pos_of_pos hz _) (Real.one_le_rpow hZ.le hell) (Real.one_le_rpow hZ.le hV)
    hΨ hQ hn hlabels hβ hslots ha hW hs
  apply (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hz.le _)).trans
  apply le_of_eq
  rw [abs_of_pos (Real.rpow_pos_of_pos hz M)]
  have hp2 (x:ℝ):(Z^x)^2=Z^(2*x):=by rw [←Real.rpow_natCast,←Real.rpow_mul hz.le];congr 1;ring
  rw [hp2,←Real.rpow_add hz,←Real.rpow_mul hz.le,←Real.rpow_mul hz.le,hp2]
  calc
    _=(C*Γ^2*G^2*‖paperRadialFourier Φ 0‖)*
      (Z^(-r-2*ell-V)*Z^((ell+eta)*(1+ε))*Z^(r+eta)*Z^(V+eta)*
        Z^(2*((2*(ell+eta)+(r+eta))*ε))*Z^M):=by ring
    _=_:=by
      rw [←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz]
      congr 2
      ring

end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic SchwartzPlanePoisson
open Eisenstein (ringComplex)
open CompletedHeight SecondPassIntegration
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O"=>Eisenstein.O

theorem original_dyadic_zero_tail
    (om:𝓢(ℝ,ℂ))(b Mmax Fmax eta tau saving eps:ℝ)
    (hs:∀y,om y≠0→y≤ b)(hMm:0≤ Mmax)(hFm:0≤ Fmax)(heta:0≤ eta)(htau:0<tau)(heps:0<eps):
    ∃Czero Ctail:ℝ,0≤ Czero ∧ 0≤ Ctail ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V Γ theta:ℝ),
      1<Z→2≤ Z^eta→0≤ M→M≤ Mmax→0≤ ell→0≤ V→ (-eta≤ r) → (r+3*ell+V≤ Fmax)→0≤Γ→b≤ Z^eta→
      (∀u,‖Ψ u‖≤1)→(∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta))→
      (∀I∈labels,I≠0)→(∀I∈labels,(Ideal.absNorm I:ℝ)≤ Z^(V+eta))→
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ)→
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀q∈lists i,‖weights i q‖≤1)→
      let W:=fun y=>normTwistedSource om theta (y/Z^r);
      let mark:=fun (v:ι→₀ℕ) U=>primeMark slots lists weights (v.support∪U);
      Z^(-r-2*ell-V)*‖reopenedPhysicalSourceSum pool Q labels β (fun q C I=>
        canonicalCubeDualZero p hp hg pool q C Ψ Ψ m m (cubicIdealGenerator I)
          (fun U=>mark q.rightExponent U*W (primeProductNorm p U))
          (fun U=>mark q.leftExponent U*W (primeProductNorm p U)) rowMajorant (Z^M))‖≤
          Czero*Γ^2*Z^(M-ell+3*eta+eps*(5*ell+2*r+7*eta)) ∧
      ‖reopenedPhysicalSourceSum pool Q labels β (fun q C I=>
        canonicalCubeDualTail p hp hg pool q C Ψ Ψ m m (cubicIdealGenerator I)
          (fun U=>mark q.rightExponent U*W (primeProductNorm p U))
          (fun U=>mark q.leftExponent U*W (primeProductNorm p U)) rowMajorant (Z^M)
          (firstDyadicPhysicalCutoff p q C I Z M r ell V eta tau))‖≤ Ctail*Γ^2*Z^(-saving):=by
  obtain ⟨Cz,hCz,hzero⟩:=original_first_zero_physical eps heps
  obtain ⟨s,Ct,hCt,htail⟩:=full_first_dyadic_marked_rapid_tail Mmax Fmax eta tau saving hMm hFm heta htau
  let G:=SchwartzMap.seminorm ℝ 0 0 om
  let Cz':=Cz*G^2*‖paperRadialFourier rowMajorant 0‖
  let Ct':=Ct*G^2*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)
  refine ⟨Cz',Ct',by dsimp [Cz'];positivity,by dsimp [Ct'];positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc pool Q labels β Ψ m slots lists weights Z M r ell V Γ theta
    hZ hbin hM hMmax hell hV hr hF hΓ hb hΨ hQ hn hlabels hβ hslots hw W mark
  have hz:0<Z:=zero_lt_one.trans hZ
  have hG:0≤ G:=apply_nonneg _ _
  have hW:∀U,‖W (primeProductNorm p U)‖≤ G:=by
    intro U
    simp only [W,normTwistedSource,norm_mul,kernelLogPhase_norm,one_mul]
    exact om.norm_le_seminorm ℝ _
  have hsupport:∀U,W (primeProductNorm p U)≠0→primeProductNorm p U≤ Z^(r+eta):=by
    intro U hU
    have hnon:om (primeProductNorm p U/Z^r)≠0:=by
      intro hh
      exact hU (by simp [W,normTwistedSource,hh])
    have hle:primeProductNorm p U≤ b*Z^r:=(div_le_iff₀ (Real.rpow_pos_of_pos hz _)).mp (hs _ hnon)
    apply hle.trans
    calc
      b*Z^r≤ Z^eta*Z^r:=mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hz.le _)
      _=Z^(r+eta):=by rw [←Real.rpow_add hz];congr 1;ring
  have hzero':=hzero p hp hcop hg hinj hc pool Q labels β Ψ m slots lists weights W rowMajorant
    Z M r ell V eta Γ G hZ (by linarith) (by linarith) hΓ hG hΨ hQ hn hlabels hβ hslots hw hW hsupport
  have hcb:=reopenedCubeFamily_cube_norms p Q _ hQ
  have htail':=htail p hp hinj hcop hg hc pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
    Ψ Ψ m m slots lists weights (fun q=>q.rightExponent.support) (fun q=>q.leftExponent.support)
    (fun _ U=>W (primeProductNorm p U)) (fun _ U=>W (primeProductNorm p U)) rowMajorant Z M r ell V
    (Γ^2) G G hZ hbin hM hMmax hell hV hr hF (sq_nonneg _) hG hG hΨ hΨ
    (reopenedCubeFamily_admissible Q) (fun q hq=>(hcb q hq).1) (fun q hq=>(hcb q hq).2)
    hn hlabels (fun q hq C _ I hI=>reopenedPairCoefficient_bound Q labels β Γ hΓ hβ q hq C I hI)
    hslots hw (fun _ _=>Finset.subset_union_right) (fun _ _=>Finset.subset_union_left)
    (fun _ _=>hW) (fun _ _=>hW) (fun _ _=>hsupport) (fun _ _=>hsupport)
  constructor
  · simpa only [mark,Finset.union_comm,Cz',G,mul_assoc,mul_left_comm,mul_comm] using hzero'
  · simpa only [mark,reopenedPhysicalSourceSum,Ct',pow_two,mul_assoc,mul_left_comm,mul_comm] using htail'

end InverseMoment

end

namespace InverseMoment

noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment

open scoped BigOperators Classical
open Eisenstein CompletedGauss

open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O

def markedCompletedT (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d : Ideal Eis → ℂ) : ℂ :=
  ∑' I : Ideal Eis, ∑' J : Ideal Eis, CompletedGauss.summand Ψ W X I J * d (I * J ^ 3)

theorem markedCompletedT_one (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ) :
    markedCompletedT Ψ W X (fun _ => 1) = completedIdealT Ψ W X := by
  simp only [markedCompletedT, mul_one, completedIdealT]

theorem markedCompletedT_congr_nonzero (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d e : Ideal Eis → ℂ) (h : ∀ A ≠ 0, d A = e A) :
    markedCompletedT Ψ W X d = markedCompletedT Ψ W X e := by
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  by_cases hI : I = 0
  · simp only [hI, summand_zero_left, zero_mul]
  by_cases hJ : J = 0
  · simp only [hJ, summand_zero_right, zero_mul]
  rw [h (I * J ^ 3) (mul_ne_zero hI (pow_ne_zero 3 hJ))]

theorem markedCompletedT_summable (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    Summable (fun p : Ideal Eis × Ideal Eis =>
      CompletedGauss.summand Ψ W X p.1 p.2 * d (p.1 * p.2 ^ 3)) := by
  apply summable_of_hasFiniteSupport
  apply (completedIdealT_finite_support Ψ W hW X hX).subset
  intro p hp hz
  exact hp (by simp only [hz, zero_mul])

theorem markedCompletedT_eq_tsum (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    markedCompletedT Ψ W X d = ∑' p : Ideal Eis × Ideal Eis,
      CompletedGauss.summand Ψ W X p.1 p.2 * d (p.1 * p.2 ^ 3) :=
  (markedCompletedT_summable Ψ W hW X hX d).tsum_prod.symm

theorem markedCompletedT_const_mul (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (c : ℂ) (d : Ideal Eis → ℂ) :
    markedCompletedT Ψ W X (fun A => c * d A) = c * markedCompletedT Ψ W X d := by
  simp only [markedCompletedT, mul_left_comm _ c, tsum_mul_left]

theorem markedCompletedT_finset_sum {ι : Type*} (s : Finset ι)
    (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (X : ℝ) (hX : 0 < X) (d : ι → Ideal Eis → ℂ) :
    markedCompletedT Ψ W X (fun A => ∑ i ∈ s, d i A) =
      ∑ i ∈ s, markedCompletedT Ψ W X (d i) := by
  simp only [markedCompletedT_eq_tsum Ψ W hW X hX, Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun i _ => markedCompletedT_summable Ψ W hW X hX (d i))

def markedExpandedTerm (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d : Ideal Eis → ℂ) (I H J : Ideal Eis) : ℂ :=
  expandedTerm Ψ W X I H J * d (I * (H * J) ^ 3)

theorem markedExpandedTerm_finite_support (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    (Function.support (fun p : Ideal Eis × Ideal Eis × Ideal Eis =>
      markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2)).Finite := by
  apply (finite_support_expandedTerm Ψ W hW X hX).subset
  intro p hp hz
  apply hp
  simp only [markedExpandedTerm, hz, zero_mul]

theorem markedExpandedTerm_scale (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d : Ideal Eis → ℂ) (I H J : Ideal Eis) :
    (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      (CompletedGauss.summand Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) I J * d (H ^ 3 * (I * J ^ 3))) =
      markedExpandedTerm Ψ W X d I H J := by
  rw [← mul_assoc, expandedTerm_scale]
  unfold markedExpandedTerm
  congr 2
  ring

theorem weighted_markedCompletedT_reopen (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d : Ideal Eis → ℂ) (H : Ideal Eis) :
    (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      markedCompletedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) (fun A => d (H ^ 3 * A)) =
      ∑' I : Ideal Eis, ∑' J : Ideal Eis, markedExpandedTerm Ψ W X d I H J := by
  simp only [markedCompletedT, ← tsum_mul_left, markedExpandedTerm_scale]

theorem marked_cube_inner_inverse (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X)
    (d : Ideal Eis → ℂ) (I : Ideal Eis) :
    (∑' H : Ideal Eis, ∑' J : Ideal Eis, markedExpandedTerm Ψ W X d I H J) =
      (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
        Vstar W ((Ideal.absNorm I : ℝ) / X)) * d I := by
  let f : Ideal Eis → ℂ := fun B =>
    columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm B : ℝ) ^ 3 / X) * d (I * B ^ 3)
  have heq (H J : Ideal Eis) :
      (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ (H * J) * f (H * J) =
        markedExpandedTerm Ψ W X d I H J := by
    simp only [f, markedExpandedTerm, expandedTerm, map_mul, Nat.cast_mul, mul_pow,
      mul_assoc]
  have hf := markedExpandedTerm_finite_support Ψ W hW X hX d
  have hp : (Function.support (fun p : Ideal Eis × Ideal Eis =>
      markedExpandedTerm Ψ W X d I p.1 p.2)).Finite := by
    change ((fun p : Ideal Eis × Ideal Eis => (I, p)) ⁻¹'
      Function.support (fun p : Ideal Eis × Ideal Eis × Ideal Eis =>
        markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2)).Finite
    exact Set.Finite.preimage (fun a _ b _ hab => (Prod.mk.inj hab).2) hf
  have hgeneric := ideal_cube_convolution (cubeWeight Ψ) (cubeWeight_zero Ψ) f
    (by simpa only [heq] using hp)
  simpa only [heq, f, map_one, Nat.cast_one, one_pow, mul_one] using hgeneric

theorem marked_cube_inverse_vstar (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    (∑' H : Ideal Eis, (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      markedCompletedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) (fun A => d (H ^ 3 * A))) =
    ∑' I : Ideal Eis, (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) / X)) * d I := by
  let F : Ideal Eis × Ideal Eis × Ideal Eis → ℂ :=
    fun p => markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2
  have hF : Summable F :=
    summable_of_hasFiniteSupport (markedExpandedTerm_finite_support Ψ W hW X hX d)
  let e : (Ideal Eis × Ideal Eis × Ideal Eis) ≃ (Ideal Eis × Ideal Eis × Ideal Eis) := {
    toFun := fun p => (p.2.1, p.1, p.2.2)
    invFun := fun p => (p.2.1, p.1, p.2.2)
    left_inv := by rintro ⟨I, H, J⟩; rfl
    right_inv := by rintro ⟨I, H, J⟩; rfl }
  have hswap : Summable (fun p => F (e p)) := e.summable_iff.mpr hF
  calc
    _ = ∑' H : Ideal Eis, ∑' I : Ideal Eis, ∑' J : Ideal Eis,
        markedExpandedTerm Ψ W X d I H J := by
      simp only [weighted_markedCompletedT_reopen]
    _ = ∑' p : Ideal Eis × Ideal Eis × Ideal Eis, F (e p) := by
      rw [hswap.tsum_prod]
      apply tsum_congr
      intro H
      exact (hswap.prod_factor H).tsum_prod.symm
    _ = ∑' p : Ideal Eis × Ideal Eis × Ideal Eis, F p := e.tsum_eq F
    _ = ∑' I : Ideal Eis, ∑' H : Ideal Eis, ∑' J : Ideal Eis,
        markedExpandedTerm Ψ W X d I H J := by
      rw [hF.tsum_prod]
      apply tsum_congr
      intro I
      exact (hF.prod_factor I).tsum_prod
    _ = _ := tsum_congr (marked_cube_inner_inverse Ψ W hW X hX d)

theorem marked_cube_inverse (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    (Real.sqrt X : ℂ)⁻¹ *
      (∑' I : Ideal Eis, columnWeight Ψ I * d I * W ((Ideal.absNorm I : ℝ) / X)) =
    ∑' H : Ideal Eis, (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      markedCompletedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) (fun A => d (H ^ 3 * A)) := by
  rw [marked_cube_inverse_vstar Ψ W hW X hX d, ← tsum_mul_left]
  apply tsum_congr
  intro I
  rw [vstar_source_normalization Ψ W X hX I]
  ring

end

end InverseMoment

namespace InverseMoment
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open scoped BigOperators Classical
open Eisenstein CompletedGauss
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic CanonicalRowCompletion IdealDivisorBound
local notation "O" => Eisenstein.O

theorem marked_cube_inverse_finite_support (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal O → ℂ) :
    (Function.support (fun H : Ideal O =>
      (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
        markedCompletedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) (fun A => d (H^3*A)))).Finite := by
  have hf := markedExpandedTerm_finite_support Ψ W hW X hX d
  apply (hf.image (fun p => p.2.1)).subset
  intro H hH
  by_contra hn
  have hzero : ∀ I J, markedExpandedTerm Ψ W X d I H J = 0 := by
    intro I J
    by_contra hz
    exact hn ⟨(I, H, J), hz, rfl⟩
  apply hH
  dsimp only
  rw [weighted_markedCompletedT_reopen]
  simp only [hzero, tsum_zero]

theorem marked_large_cube_inner_reopen (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0 < X) (d : Ideal O → ℂ) (I : Ideal O) :
    (∑' H : Ideal O,∑' J : Ideal O,
      if H₀ ≤ (Ideal.absNorm H : ℝ) then markedExpandedTerm Ψ W X d I H J else 0) =
    ∑' B : Ideal O,largeCubeCoefficient H₀ B*CompletedGauss.summand Ψ W X I B*d (I*B^3) := by
  let f : Ideal O → ℂ := fun B =>
    columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I : ℝ) : ℂ)*
      Vstar W ((Ideal.absNorm I : ℝ)*(Ideal.absNorm B : ℝ)^3/X)*d (I*B^3)
  have heq (H J : Ideal O) :
      (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ (H*J)*f (H*J)=markedExpandedTerm Ψ W X d I H J := by
    simp only [f,markedExpandedTerm,expandedTerm,map_mul,Nat.cast_mul,mul_pow,mul_assoc]
  have hf := markedExpandedTerm_finite_support Ψ W hW X hX d
  have hp : (Function.support (fun p : Ideal O × Ideal O => markedExpandedTerm Ψ W X d I p.1 p.2)).Finite := by
    change ((fun p : Ideal O × Ideal O => (I,p)) ⁻¹'
      Function.support (fun p : Ideal O × Ideal O × Ideal O => markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2)).Finite
    exact Set.Finite.preimage (fun a _ b _ hab => (Prod.mk.inj hab).2) hf
  have hg := large_cube_convolution H₀ (cubeWeight Ψ) (cubeWeight_zero Ψ) f (by simpa only [heq] using hp)
  rw [show (∑' H : Ideal O, ∑' J : Ideal O,
      if H₀ ≤ (Ideal.absNorm H : ℝ) then markedExpandedTerm Ψ W X d I H J else 0)=
      ∑' B : Ideal O,largeCubeCoefficient H₀ B*cubeWeight Ψ B*f B by simpa only [heq] using hg]
  apply tsum_congr
  intro B
  dsimp [f,CompletedGauss.summand]
  ring

theorem marked_large_cube_reopen (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0 < X) (d : Ideal O → ℂ) :
    (∑' H : Ideal O, if H₀ ≤ (Ideal.absNorm H : ℝ) then
      (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
        markedCompletedT Ψ W (X/(Ideal.absNorm H : ℝ)^3) (fun A => d (H^3*A)) else 0) =
    ∑' I : Ideal O,∑' B : Ideal O,largeCubeCoefficient H₀ B*CompletedGauss.summand Ψ W X I B*d (I*B^3) := by
  let F : Ideal O × Ideal O × Ideal O → ℂ := fun p =>
    if H₀ ≤ (Ideal.absNorm p.2.1 : ℝ) then markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2 else 0
  have hF : Summable F := summable_of_hasFiniteSupport
    ((markedExpandedTerm_finite_support Ψ W hW X hX d).subset (by
      intro p hp
      by_contra hn
      have he : markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2=0 := not_ne_iff.mp hn
      exact hp (by simp [F,he])))
  let e : (Ideal O × Ideal O × Ideal O) ≃ (Ideal O × Ideal O × Ideal O) := {
    toFun := fun p => (p.2.1,p.1,p.2.2)
    invFun := fun p => (p.2.1,p.1,p.2.2)
    left_inv := by rintro ⟨I,H,J⟩;rfl
    right_inv := by rintro ⟨I,H,J⟩;rfl }
  have hswap : Summable (fun p => F (e p)) := e.summable_iff.mpr hF
  calc
    _ = ∑' H : Ideal O,∑' I : Ideal O,∑' J : Ideal O,
        if H₀ ≤ (Ideal.absNorm H : ℝ) then markedExpandedTerm Ψ W X d I H J else 0 := by
      apply tsum_congr
      intro H
      by_cases h : H₀ ≤ (Ideal.absNorm H : ℝ)
      · simp only [if_pos h,weighted_markedCompletedT_reopen]
      · simp only [if_neg h,tsum_zero]
    _ = ∑' p : Ideal O × Ideal O × Ideal O,F (e p) := by
      rw [hswap.tsum_prod]
      apply tsum_congr
      intro H
      exact (hswap.prod_factor H).tsum_prod.symm
    _ = ∑' p : Ideal O × Ideal O × Ideal O,F p := e.tsum_eq F
    _ = ∑' I : Ideal O,∑' H : Ideal O,∑' J : Ideal O,
        if H₀ ≤ (Ideal.absNorm H : ℝ) then markedExpandedTerm Ψ W X d I H J else 0 := by
      rw [hF.tsum_prod]
      apply tsum_congr
      intro I
      exact (hF.prod_factor I).tsum_prod
    _ = _ := tsum_congr (marked_large_cube_inner_reopen Ψ W hW X H₀ hX d)

theorem marked_completed_cube_inverse_split (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0 < X) (d : Ideal O → ℂ) :
    (Real.sqrt X : ℂ)⁻¹*(∑' I : Ideal O,columnWeight Ψ I*d I*W ((Ideal.absNorm I : ℝ)/X)) =
    (∑' H : Ideal O, if (Ideal.absNorm H : ℝ)<H₀ then
      (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
        markedCompletedT Ψ W (X/(Ideal.absNorm H : ℝ)^3) (fun A => d (H^3*A)) else 0) +
    ∑' I : Ideal O,∑' B : Ideal O,largeCubeCoefficient H₀ B*CompletedGauss.summand Ψ W X I B*d (I*B^3) := by
  let f := fun H : Ideal O => (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
    markedCompletedT Ψ W (X/(Ideal.absNorm H : ℝ)^3) (fun A => d (H^3*A))
  have hf := marked_cube_inverse_finite_support Ψ W hW X hX d
  have hs : Summable (fun H : Ideal O => if (Ideal.absNorm H : ℝ)<H₀ then f H else 0) :=
    summable_of_hasFiniteSupport (hf.subset (by
      intro H hH
      by_contra hn
      have he : f H=0 := not_ne_iff.mp hn
      exact hH (by simp only [he,ite_self])))
  have hl : Summable (fun H : Ideal O => if H₀ ≤ (Ideal.absNorm H : ℝ) then f H else 0) :=
    summable_of_hasFiniteSupport (hf.subset (by
      intro H hH
      by_contra hn
      have he : f H=0 := not_ne_iff.mp hn
      exact hH (by simp only [he,ite_self])))
  rw [marked_cube_inverse Ψ W hW X hX d,←marked_large_cube_reopen Ψ W hW X H₀ hX d]
  change (∑' H,f H)=(∑' H,if (Ideal.absNorm H : ℝ)<H₀ then f H else 0)+
    ∑' H,if H₀ ≤ (Ideal.absNorm H : ℝ) then f H else 0
  rw [← hs.tsum_add hl]
  apply tsum_congr
  intro H
  by_cases h : (Ideal.absNorm H : ℝ)<H₀
  · simp [h,not_le.mpr h]
  · simp [h,le_of_not_gt h]

end
end InverseMoment

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

/-
Second cell physical partition adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Inversion.SecondSourceBlocks

/-!
# Second cell physical partition

Second cell exponents and scales; source indices, selectors and cells of the first child
windows; the original physical partition of the whole retained source.
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
namespace InverseMomentWholePriorityPhysical
open Eisenstein SecondPassArithmetic FirstPassCubeLabels
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents
open InverseMomentWholePriorityParents InversePrioritySecondSource
open InversePrincipalEnergy InverseSecondPrincipalCaller RayFourExpansion
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ] [Fintype κ]
variable {Jo : ℕ} (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,lambda∉Ideal.span {p i})

def fullPhysical (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : 𝓢(ℝ,ℂ)) (X Y : ℝ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ)
    (y : SecondParentSource ι Jo) : ℂ :=
  let Ψ₀ := firstCoreTwist negative (if negative then r.1 else r.2) Ψ core
  let ll := fun i=>lists i\extra y.cube
  let H := markedRadial p (slots\J) (residualLists p negative ll y) a ∅ V X
  let K := secondVariableCutoff p y R
  truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K +
    (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈(secondDyadicSector pool K residual label j).image (attachSecondExpansion y),
          retainedRow p hg pool negative Ψ₀ m slots J ll a V X Y ray x) +
    secondSourceTail p hp hg pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K

include hcop in
theorem whole_parent_full
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,lambda^2∣p i-1)
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ)
    (y : SecondParentSource ι Jo) (hq : y.quotient=sourceIdeal p (quotientSupport p y)) :
    parentPoisson p hp hg hinj pool negative Ψ m slots J
      (fun i=>lists i\extra y.cube) a om X t Y r core y =
    fullPhysical p hp hg hinj extra pool negative Ψ m slots J lists a
      (principalWindow om lo hi hlo hs negative t) X Y r core R label y :=
  parentPoisson_full p hp hcop hg hinj hc hpr y pool hq negative Ψ m slots J
    (fun i=>lists i\extra y.cube) a om lo hi hlo hs X t Y hX hY r core R label

omit [DecidableEq σ] in
theorem whole_residual_lists_attach
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι)
    (q : Source ι Jo×((∀ i∈J,ι)×(∀ i∈J,ι))) :
    residualLists p negative (fun i=>lists i\extra (attach p J q).cube) (attach p J q)=
      fun i=>lists i\wholeExtractedSupport (fun x=>extra x.cube) negative q.1 := by
  rw [residualLists_attach p hinj]
  funext i
  ext k
  simp only [Finset.mem_sdiff,wholeExtractedSupport,Finset.mem_union]
  change (k ∈ lists i ∧ k ∉ extra q.1.cube) ∧ k ∉ extractedSupport negative q.1 ↔ _
  tauto

include hcop in
theorem whole_signed_source_full
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,lambda^2∣p i-1)
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (source : Finset (Source ι Jo)) (w : Source ι Jo→ℂ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ) :
    (∑ x∈source,w x*(‖primeMark J lists a
      (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots J
        (fun i=>lists i\extra x.cube) a om X t Y r core (parent p x)) =
    ∑ y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
      coefficient p J a w y *
        fullPhysical p hp hg hinj extra pool negative Ψ m slots J lists a
          (principalWindow om lo hi hlo hs negative t) X Y r core R label y := by
  have he := wholePaired_parent_sq_sum p (fun x=>extra x.cube) hinj source negative J lists a w
    (fun y=>parentPoisson p hp hg hinj pool negative Ψ m slots J
      (fun i=>lists i\extra y.cube) a om X t Y r core y)
  refine he.trans ?_
  apply Finset.sum_congr rfl
  intro y hy
  obtain ⟨x,hx,q,hq,rfl⟩ :=
    (mem_wholeAssignedParents p (fun x=>extra x.cube) source negative J lists y).mp hy
  rw [forget_attach]
  apply congrArg (coefficient p J a w (attach p J (x,q))* ·)
  have hquot : (attach p J (x,q)).quotient=sourceIdeal p (quotientSupport p (attach p J (x,q))) := by
    rw [quotientSupport_attach p hinj];rfl
  exact whole_parent_full p hp hcop hg hinj hc hpr extra pool negative Ψ m slots J lists a
    om lo hi hlo hs X t Y hX hY r core R label (attach p J (x,q)) hquot

end InverseMomentWholePriorityPhysical

end

noncomputable section
namespace InverseMomentWholeRetainedSource
open Eisenstein SecondPassArithmetic InverseMoment InverseInitialArithmetic
open InverseFirstPriorityParents InversePrioritySecondSource InverseMomentWholePriorityParents
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable {Jo : ℕ} (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

def deleted (extra : CubeCoordinates ι→Finset ι) (negative : Bool)
    (x : MarkedSecondSource ι Jo 0) : Finset ι :=
  extra x.cube∪(((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon)∪
    quotientSupport p (secondParentOf x))

theorem retained_conditions (hp : ∀ i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι)
    (source : Finset (Source ι Jo)) (hs : ∀ x∈source,SourceValid p x)
    (hextra : ∀ x∈source,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) :
    ActualSecondSourceConditions p
      (retainedPool p pool (wholeAssignedParents p (fun x=>extra x.cube) source negative J lists)
        R label residual j) := by
  apply whole_assigned_family_conditions p hp (fun x=>extra x.cube) source hs hextra negative J lists
  intro y hy x hx
  exact (second_variable_original_support p y pool residual (R y) (label y) j x hx).2.1

theorem retained_deleted_support
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι)
    (source : Finset (Source ι Jo)) (hs : ∀ x∈source,SourceValid p x)
    (hextra : ∀ x∈source,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx : x∈retainedPool p pool (wholeAssignedParents p (fun x=>extra x.cube) source negative J lists)
      R label residual j) :
    ∀ i∈deleted p extra negative x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient := by
  have hy := ((mem_retainedPool p pool _ R label residual j x).mp hx).1
  obtain ⟨s,hs₀,q,hq,he⟩ := (mem_wholeAssignedParents p (fun x=>extra x.cube) source negative J lists _).mp hy
  have hc : x.cube=s.cube := (congrArg SecondParentSource.cube he).symm
  have hC : x.firstCommon=s.firstCommon := (congrArg SecondParentSource.firstCommon he).symm
  have ht : x.quotient=sourceIdeal p s.quotientSupport := (congrArg SecondParentSource.quotient he).symm
  have hqs : quotientSupport p (secondParentOf x)=s.quotientSupport := by
    rw [←he,quotientSupport_attach p hinj]
  intro i hi
  change i∈extra x.cube∪(((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon)∪
    quotientSupport p (secondParentOf x)) at hi
  rw [hc,hC,hqs] at hi
  rcases Finset.mem_union.mp hi with hi|hi
  · exact Or.inl (Finset.mem_union_left _ (hc.symm ▸ hextra s hs₀ hi))
  · rcases Finset.mem_union.mp hi with hi|hi
    · left
      rw [hc,hC]
      rcases Finset.mem_union.mp hi with hi|hi
      · apply Finset.mem_union_left
        cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hi
        · exact (hs s hs₀).admissible.1 hi
        · exact (hs s hs₀).admissible.2 hi
      · exact Finset.mem_union_right _ hi
    · right
      rw [ht]
      exact source_prime_dvd p _ i hi

theorem whole_coefficient_norm
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : Source ι Jo→Finset ι) (source : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (B : ℝ)
    (ha : ∀ i∈J,∀ k∈lists i,‖a i k‖≤1) (hw : ∀ x∈source,‖w x‖≤ B)
    (y : SecondParentSource ι (Jo+(J.card+J.card)))
    (hy : y∈wholeAssignedParents p extra source negative J lists) :
    ‖coefficient p J a w y‖≤ B := by
  obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
  rw [coefficient_attach p hinj,norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (pairedSlotWeight_norm_le_one J J lists lists a a
    _ q hq ha ha)).trans (hw x hx)

end InverseMomentWholeRetainedSource

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open CompletedHeight SecondPassIntegration
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

def secondCellColumnExponent (Z X:ℝ) (d:BlockIndex):ℝ :=
  Real.logb Z (X/(scales d 0*scales d 2))

theorem second_cell_column_scale (Z X:ℝ) (d:BlockIndex) (hZ:1<Z) (hX:0<X) :
    Z^(secondCellColumnExponent Z X d)=X/(scales d 0*scales d 2) := by
  exact Real.rpow_logb (by linarith) (ne_of_gt hZ)
    (div_pos hX (mul_pos (dyadScale_pos _) (dyadScale_pos _)))

theorem second_cell_physical_scale (Z X:ℝ) (d:BlockIndex) (hZ:1<Z) (hX:0<X) :
    scales d 0*scales d 2*Z^(secondCellColumnExponent Z X d)=X := by
  rw [second_cell_column_scale Z X d hZ hX]
  field_simp [scales,ne_of_gt (dyadScale_pos (d 0)),ne_of_gt (dyadScale_pos (d 2))]

theorem second_cell_clipping_ratio (Z X b:ℝ) (d:BlockIndex) (hZ:1<Z) (hX:0<X)
    (hb:1≤ b) (hsource:scales d 0*scales d 2≤ b*X) :
    1≤ Z^(max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d) ∧
    Z^(max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d)≤ b := by
  let N:=secondCellColumnExponent Z X d
  have hz:0<Z:=lt_trans zero_lt_one hZ
  have hn:Z^N=X/(scales d 0*scales d 2):=second_cell_column_scale Z X d hZ hX
  constructor
  · exact Real.one_le_rpow hZ.le (sub_nonneg.mpr (le_max_right _ _))
  · by_cases hN:0≤ N
    · rw [max_eq_right hN,sub_self,Real.rpow_zero];exact hb
    · have hN':N≤0:=le_of_not_ge hN
      rw [max_eq_left hN',zero_sub,Real.rpow_neg hz.le,hn,inv_div]
      exact (div_le_iff₀ hX).mpr hsource

theorem actual_priority_cell_profile {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i})
    (pool:Finset ι) (x:SecondProfileData ι) (slots₁ slots₂:Finset σ)
    (lists₁ lists₂:σ→Finset ι) (a₁ a₂:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (negative:Bool) (t:ℝ) (Φ:𝓢(ℝ,ℂ)) (Y X Z:ℝ) (hX:0<X) (hZ:1<Z) (d:BlockIndex) :
    let g:=priorityLogWindow om lo hi hlo hs negative
    let θ:=priorityHeight negative t
    actualSecondProfileRow p hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂
      (principalWindow om lo hi hlo hs negative t) (principalWindow om lo hi hlo hs negative t) Φ Y X =
      actualSecondProfileRow p hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂
        (fun y=>star (positiveSource (conjugateProfile g) 1 (-θ) y)) (positiveSource g 1 θ) Φ Y
        (scales d 0*scales d 2*Z^(secondCellColumnExponent Z X d)) := by
  rw [second_cell_physical_scale Z X d hZ hX]
  exact actual_priority_profile_common p hp hcop hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂
    om lo hi hlo hs negative t Φ Y X hX

theorem actual_priority_cells {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i})
    {Jo:ℕ} (source:Finset (MarkedSecondSource ι Jo 0))
    (pool:Finset ι) (Ψ:O→*ℂ) (m:O) (ray:SecondRayIndex)
    (slots₁ slots₂:Finset σ) (lists₁ lists₂:σ→Finset ι) (a₁ a₂:σ→ι→ℂ)
    (deleted₁ deleted₂:MarkedSecondSource ι Jo 0→Finset ι)
    (w:MarkedSecondSource ι Jo 0→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (negative:Bool) (t:ℝ) (Φ:𝓢(ℝ,ℂ)) (Y X Z:ℝ) (hX:0<X) (hZ:1<Z) :
    let g:=priorityLogWindow om lo hi hlo hs negative
    let θ:=priorityHeight negative t
    (Y:ℂ)*secondRayCoefficient ray *
      (∑x∈source,(w x*actualSecondSignedWeight p hg Ψ
        (m*cubicIdealGenerator x.quotient) ray x)*
        actualSecondProfileRow p hg pool (secondInheritedProfile p x Ψ m ray)
          slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
          (principalWindow om lo hi hlo hs negative t) (principalWindow om lo hi hlo hs negative t) Φ Y X) =
    ∑d∈keys p source,(Y:ℂ)*secondRayCoefficient ray *
      (∑x∈cell p source d,(w x*actualSecondSignedWeight p hg Ψ
        (m*cubicIdealGenerator x.quotient) ray x)*
        actualSecondProfileRow p hg pool (secondInheritedProfile p x Ψ m ray)
          slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
          (fun y=>star (positiveSource (conjugateProfile g) 1 (-θ) y)) (positiveSource g 1 θ) Φ Y
          (scales d 0*scales d 2*Z^(secondCellColumnExponent Z X d))) := by
  intro g θ
  refine (physical_source_partition p hp hcop hg source pool Ψ m ray slots₁ slots₂ lists₁ lists₂
    a₁ a₂ deleted₁ deleted₂ w (principalWindow om lo hi hlo hs negative t)
    (principalWindow om lo hi hlo hs negative t) Φ Y X).trans ?_
  apply Finset.sum_congr rfl
  intro d hd
  apply congrArg ((Y : ℂ) * secondRayCoefficient ray * ·)
  apply Finset.sum_congr rfl
  intro x hx
  exact congrArg ((w x * actualSecondSignedWeight p hg Ψ
    (m * cubicIdealGenerator x.quotient) ray x) * ·)
    (actual_priority_cell_profile p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
      slots₁ slots₂ _ _ a₁ a₂ om lo hi hlo hs negative t Φ Y X Z hX hZ d)

theorem actual_source_block_ratios {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn)) (d:BlockIndex)
    (hcell:∀x∈source,index p x=d) (hk:∀x∈source,x.second.frequency≠0) :
    ∀x∈source,∀i,InverseSecondChildWindows.actualOuterRatios p x
      (scales d 0) (scales d 1) (scales d 2) (scales d 3) i∈Set.Icc 1 2 := by
  intro x hx i
  have hxcell:x∈cell p source d:=(mem_cell p source d x).mpr ⟨hx,hcell x hx⟩
  have hr:=cell_ratios p hp source hk d x hxcell i
  have he:InverseSecondChildWindows.actualOuterRatios p x
      (scales d 0) (scales d 1) (scales d 2) (scales d 3) i=outerNorms p x i/scales d i := by
    fin_cases i <;> simp [InverseSecondChildWindows.actualOuterRatios,outerNorms,
      primeProductNorm]
  rw [he]
  exact ⟨hr.1,hr.2.le⟩

end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ cubic_units_finite
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem actual_priority_cell_recursive
    (om Φ:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (B₀:Fin 6→ℝ) (hB₀:∀i,0≤ B₀ i) (Aker J K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (omega₁ omega₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤ hiFresh ∧ HasCompactSupport (omega₁:ℝ→ℂ) ∧ HasCompactSupport (omega₂:ℝ→ℂ) ∧
      tsupport (omega₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (omega₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∃ C : ℝ,0 ≤ C ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, lambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (_hs : ActualSecondSourceConditions p source) (d:InverseSecondSourceBlocks.BlockIndex)
    (_hcell:∀x∈source,InverseSecondSourceBlocks.index p x=d),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (Y R L Z X Vlabel εchild : ℝ)
        (ell Ractive j tcount gcount theta eta : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ringComplex (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ x∈source,primeProductNorm p x.second.sourceCommon ≤ Z^(gcount+eta)) →
      (∀ x∈source,Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest omega₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+Vlabel) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest omega₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+Vlabel) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hg Ψ
            (m*cubicIdealGenerator x.quotient) z x) *
          actualSecondProfileRow p hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t) Φ Y X)‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*(((scales d 1)*(scales d 2)*(Z^(secondCellColumnExponent Z X d)) : ℝ):ℂ)⁻¹‖)*
        (((Fintype.card (Eisˣ × Eisˣ) : ℝ)*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 (secondCellColumnExponent Z X d)+Vlabel)+εchild))*
          Z^((ell+Ractive/2-j+tcount+gcount-theta+11*eta/2)*(1+εmass)))*
          (C*((1+‖(-priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J *
            (1+‖(priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*(scales d 3)/((scales d 1)*(scales d 2)^2*(Z^(secondCellColumnExponent Z X d))^2))^Aker)) := by
  let g:=priorityLogWindow om lo hi hlo hsupport negative
  let mg:=|Real.log lo|+|Real.log hi|
  have hm:0≤ mg:=add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hg:Function.support g⊆Set.Icc (-mg) mg:=priorityLogWindow_support om lo hi hlo hsupport negative
  have hcg:Function.support (conjugateProfile g)⊆Set.Icc (-mg) mg:=by
    intro x hx
    apply hg
    simpa only [Function.mem_support,conjugateProfile_apply,star_ne_zero] using hx
  obtain ⟨omega₁,omega₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,hC,henergy⟩:=
    actual_second_fixed_block_recursive (ι:=ι) (σ:=σ) (conjugateProfile g) g Φ mg mg 1
      (fun _=>1) (fun _=>2) B₀ hm hm (le_refl 1) (fun _=>zero_lt_one)
      (fun _=>by norm_num) hB₀ hcg hg Aker J K εmass hεmass
  refine ⟨omega₁,omega₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,hC,?_⟩
  intro p hp _ hcop hg₀ hpr hinj hc Jo source hs d hcell pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X Vlabel εchild ell Ractive j tcount gcount theta eta ρ t w labels A
    hd₁ hd₂ hρ hL hZ hX hY hrows hcube₁ hcube₂ hactive hj hquot hcommon hdiv
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  have hblock:=actual_source_block_ratios p hp source d hcell
    (fun x hx=>frequency_ne_zero_of_gate _ _ (hrows x hx))
  have he:=henergy p hp hcop hg₀ hpr hinj hc source hs pool Ψ m z
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
    (scales d 0) (scales d 1) (scales d 2) (scales d 3) Y R L Z
    (secondCellColumnExponent Z X d) Vlabel εchild ell Ractive j tcount gcount theta eta ρ
    1 1 (-priorityHeight negative t) (priorityHeight negative t) w labels A
    hd₁ hd₂ hρ (le_refl 1) (le_refl 1) (le_refl 1) (le_refl 1) hL (lt_trans zero_lt_one hZ)
    (dyadScale_pos _) (dyadScale_pos _) (dyadScale_pos _) (dyadScale_pos _)
    (Real.rpow_pos_of_pos (lt_trans zero_lt_one hZ) _) hY hrows hblock
    hcube₁ hcube₂ hactive hj hquot hcommon hdiv hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  rw [second_cell_physical_scale Z X d hZ hX] at he
  refine le_trans (le_of_eq (congrArg (fun v : ℂ => ‖(Y : ℂ) * secondRayCoefficient z * v‖) ?_)) he
  apply Finset.sum_congr rfl
  intro x _hx
  exact congrArg (fun v : ℂ => (w x * actualSecondSignedWeight p hg₀ Ψ
    (m * cubicIdealGenerator x.quotient) z x) * v)
    (actual_priority_profile_common p hp hcop hg₀ pool (secondInheritedProfile p x Ψ m z)
      slots₁ slots₂ _ _ a₁ a₂ om lo hi hlo hsupport negative t Φ Y X hX)

end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseInitialArithmetic
open Eisenstein (ringComplex)
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

def secondCellExponent (Z:ℝ) (d:BlockIndex) (i:Fin 4):ℝ:=Real.logb Z (scales d i)

theorem secondCellExponent_nonneg (Z:ℝ) (d:BlockIndex) (i:Fin 4) (hZ:1<Z):
    0≤ secondCellExponent Z d i := by
  apply Real.logb_nonneg hZ
  exact one_le_pow₀ (by norm_num : (1:ℝ)≤2)

theorem second_cell_scale_rpow (Z:ℝ) (d:BlockIndex) (i:Fin 4) (hZ:1<Z):
    Z^(secondCellExponent Z d i)=scales d i :=
  Real.rpow_logb (by linarith) (ne_of_gt hZ) (dyadScale_pos _)

theorem second_cell_formal_column (Z r A B t:ℝ) (d:BlockIndex) (hZ:1<Z):
    secondCellColumnExponent Z (Z^(r-A-B-t)) d=
      secondFormalColumn r A B t (secondCellExponent Z d 0) (secondCellExponent Z d 2) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  apply (Real.rpow_right_inj hz (ne_of_gt hZ)).mp
  rw [second_cell_column_scale Z _ d hZ (Real.rpow_pos_of_pos hz _)]
  rw [←second_cell_scale_rpow Z d 0 hZ,←second_cell_scale_rpow Z d 2 hZ,
    ←Real.rpow_add hz,←Real.rpow_sub hz]
  congr 1
  unfold secondFormalColumn
  ring

theorem actual_second_child_label_norm {ι:Type*} [DecidableEq ι]
    (p:ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (x:MarkedSecondSource ι Jo Jn) (u v:Oˣ):
    (Ideal.absNorm (actualSecondChild p u v x).2.1:ℝ)=
      ‖ringComplex (jLabel p x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2*
      primeProductNorm p x.firstCommon*primeProductNorm p x.second.divisor*
      primeProductNorm p x.second.overlap := by
  have hn(S:Finset ι):(Ideal.absNorm (sourceIdeal p S):ℝ)=primeProductNorm p S:=by
    simpa only [sourceIdeal,primeProductNorm,map_prod] using
      (ringComplex_norm_sq_eq_absNorm_span (∏i∈S,p i)).symm
  change (Ideal.absNorm (Ideal.span {jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit} *
      sourceIdeal p x.firstCommon * sourceIdeal p x.second.divisor * sourceIdeal p x.second.overlap):ℝ)=_
  simp only [map_mul,Nat.cast_mul,hn,←ringComplex_norm_sq_eq_absNorm_span]

theorem actual_cell_child_label_bound {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn))
    (hk:∀x∈source,x.second.frequency≠0) (d:BlockIndex)
    (x:MarkedSecondSource ι Jo Jn) (hx:x∈cell p source d) (u v:Oˣ):
    (Ideal.absNorm (actualSecondChild p u v x).2.1:ℝ)≤
      4*‖ringComplex (jLabel p x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2*
      primeProductNorm p x.firstCommon*scales d 1*scales d 2 := by
  have hE:= (cell_ratios p hp source hk d x hx 1).2.le
  have hV:= (cell_ratios p hp source hk d x hx 2).2.le
  have he:primeProductNorm p x.second.divisor≤2*scales d 1:=
    (div_le_iff₀ (dyadScale_pos _)).mp hE
  have hv:primeProductNorm p x.second.overlap≤2*scales d 2:=
    (div_le_iff₀ (dyadScale_pos _)).mp hV
  rw [actual_second_child_label_norm]
  calc
    _ ≤ ‖ringComplex (jLabel p x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2*
      primeProductNorm p x.firstCommon*(2*scales d 1)*(2*scales d 2) := by
      have hc0 := (primeProductNorm_pos p hp x.firstCommon).le
      have hv0 := (primeProductNorm_pos p hp x.second.overlap).le
      have hs0 := (dyadScale_pos (d 1)).le
      gcongr
    _ = _ := by ring

theorem actual_cell_child_label_power {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn))
    (hk:∀x∈source,x.second.frequency≠0) (d:BlockIndex)
    (x:MarkedSecondSource ι Jo Jn) (hx:x∈cell p source d) (u v:Oˣ)
    (Z B j eta:ℝ) (hZ:1<Z) (hbin:2≤ Z^eta)
    (hC:primeProductNorm p x.firstCommon≤ Z^(B+eta))
    (hJ:‖ringComplex (jLabel p x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2≤ Z^(j+eta)) :
    (Ideal.absNorm (actualSecondChild p u v x).2.1:ℝ)≤
      Z^(secondFormalLabel B (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hfour:(4:ℝ)≤ Z^(2*eta):=by
    have hh:=mul_le_mul hbin hbin (by norm_num) (Real.rpow_nonneg hz.le _)
    norm_num only [←Real.rpow_add hz,show eta+eta=2*eta by ring] at hh
    exact hh
  apply (actual_cell_child_label_bound p hp source hk d x hx u v).trans
  calc
    _≤ Z^(2*eta)*Z^(j+eta)*Z^(B+eta)*scales d 1*scales d 2:=by
      have hc0:0≤ primeProductNorm p x.firstCommon:=(primeProductNorm_pos p hp _).le
      have hs1:0≤ scales d 1:=(dyadScale_pos _).le
      have hs2:0≤ scales d 2:=(dyadScale_pos _).le
      gcongr
    _= _:=by
      rw [←second_cell_scale_rpow Z d 1 hZ,←second_cell_scale_rpow Z d 2 hZ,
        ←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz]
      congr 1
      unfold secondFormalLabel
      ring

theorem second_cell_clipping_width (Z X b eta:ℝ) (d:BlockIndex)
    (hZ:1<Z) (hX:0<X) (hb:1≤ b)
    (hsource:scales d 0*scales d 2≤ b*X) (hthreshold:b≤ Z^(6*eta)) :
    max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d≤6*eta := by
  exact (Real.rpow_le_rpow_left_iff hZ).mp
    ((second_cell_clipping_ratio Z X b d hZ hX hb hsource).2.trans hthreshold)

end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ cubic_units_finite
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem actual_priority_source_moving_radius
    (om Φ:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (B₀:Fin 6→ℝ) (hB₀:∀i,0≤ B₀ i) (J K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (omega₁ omega₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤ hiFresh ∧ HasCompactSupport (omega₁:ℝ→ℂ) ∧ HasCompactSupport (omega₂:ℝ→ℂ) ∧
      tsupport (omega₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (omega₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∃ C : ℝ,0 ≤ C ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, lambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (_hs : ActualSecondSourceConditions p source),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤ eta → 2≤ Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R (index p x))) →
      (∀ x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ringComplex (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest omega₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest omega₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hg Ψ
            (m*cubicIdealGenerator x.quotient) z x) *
          actualSecondProfileRow p hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t) Φ Y X)‖ ≤
      ∑d∈keys p source,(Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*(((scales d 1)*(scales d 2)*(Z^(secondCellColumnExponent Z X d)) : ℝ):ℂ)⁻¹‖)*
        (((Fintype.card (Eisˣ × Eisˣ) : ℝ)*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 (secondCellColumnExponent Z X d)+(Vlabel d))+εchild))*
          Z^((ell+Ractive/2-j+tcount+(secondCellExponent Z d 0)-(secondCellExponent Z d 1)+11*eta/2)*(1+εmass)))*
          (C*((1+‖(-priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J *
            (1+‖(priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*(scales d 3)/((scales d 1)*(scales d 2)^2*(Z^(secondCellColumnExponent Z X d))^2))^0)) := by
  obtain ⟨omega₁,omega₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,hC,henergy⟩:=
    actual_priority_cell_recursive (ι:=ι) (σ:=σ) om Φ lo hi hlo hsupport negative B₀ hB₀ 0 J K εmass hεmass
  refine ⟨omega₁,omega₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,hC,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X εchild Vlabel ell Ractive j tcount eta ρ t w labels A
    hd₁ hd₂ hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  have hz:0<Z:=zero_lt_one.trans hZ
  have hk:∀x∈source,x.second.frequency≠0:=fun x hx=>frequency_ne_zero_of_gate _ _ (hrows x hx)
  rw [physical_source_partition p hp hcop hg source pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ w]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  have hin : cell p source d⊆source:=cell_subset p source d
  have hcommon:∀x∈cell p source d,primeProductNorm p x.second.sourceCommon≤ Z^(secondCellExponent Z d 0+eta):=by
    intro x hx
    have hr:primeProductNorm p x.second.sourceCommon≤2*scales d 0:=
      (div_le_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 0).2.le
    apply hr.trans
    rw [Real.rpow_add hz,second_cell_scale_rpow Z d 0 hZ]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hbin (show 0≤ scales d 0 from (dyadScale_pos _).le)
  have hdiv:∀x∈cell p source d,Z^(secondCellExponent Z d 1-eta)≤ primeProductNorm p x.second.divisor:=by
    intro x hx
    have hr:scales d 1≤ primeProductNorm p x.second.divisor:=by
      simpa [outerNorms,scales] using (le_div_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 1).1
    have hh:Z^(secondCellExponent Z d 1-eta)≤ Z^(secondCellExponent Z d 1):=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    rw [second_cell_scale_rpow Z d 1 hZ] at hh
    exact hh.trans hr
  exact henergy p hp hcop hg hpr hinj hc (cell p source d) (cell_conditions p source hs d) d
    (fun x hx=>(mem_cell p source d x).mp hx |>.2) pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y (R d) L Z X (Vlabel d) εchild ell Ractive j tcount
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) eta ρ t w (labels d) A
    (fun x hx=>hd₁ x (hin hx)) (fun x hx=>hd₂ x (hin hx)) hρ hL hZ hX hY
    (fun x hx=>by simpa only [(mem_cell p source d x).mp hx |>.2] using hrows x (hin hx)) (fun x hx=>hcube₁ x (hin hx)) (fun x hx=>hcube₂ x (hin hx))
    (fun x hx=>hactive x (hin hx)) (fun x hx=>hj x (hin hx)) (fun x hx=>hquot x (hin hx))
    hcommon hdiv hΨ (fun x hx=>hw x (hin hx)) ha₁ ha₂ (hlabels d hd) ho hslots₁ hslots₂ hA
    (hleft d hd) (hright d hd)

end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseSecondSourceBlocks

theorem priority_cell_physical_budget
    (Z:ℝ) (hZ:1<Z) (d:BlockIndex)
    (M r ell V delta A B R j t eta tau pi eps epsmass b C:ℝ)
    (ray:ℂ) (hC:0≤ C) (hb:1≤ b)
    (hsource:scales d 0*scales d 2≤ b*Z^(r-A-B-t))
    (hthreshold:b≤ Z^(6*eta))
    (hmass:epsmass*(secondCount ell R j t (secondCellExponent Z d 0)
      (secondCellExponent Z d 1)+11*eta/2)≤ pi) :
    let N:=secondCellColumnExponent Z (Z^(r-A-B-t)) d
    let Vchild:=secondFormalLabel B (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta
    C*Z^(firstKappa M r ell V delta A B R)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))*
      (Real.exp (6*(eta*Real.log Z))*
        ‖((Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau):ℝ):ℂ)*ray*
          ((scales d 1*scales d 2*Z^N:ℝ):ℂ)⁻¹‖)*
      Z^((secondCount ell R j t (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2)*(1+epsmass))*
      Z^(2*(max 0 N+Vchild)+eps)≤
    C*‖ray‖*Z^(r+3*ell+V+48*eta+tau+pi+eps) := by
  intro N Vchild
  have hz:0<Z:=zero_lt_one.trans hZ
  have hclip:=second_cell_clipping_width Z (Z^(r-A-B-t)) b eta d hZ
    (Real.rpow_pos_of_pos hz _) hb hsource hthreshold
  rw [second_cell_formal_column Z r A B t d hZ] at hclip
  have he:=physical_block_scalar_budget Z hZ.le M r ell V delta A B R j t
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) (secondCellExponent Z d 2)
    eta tau pi (eps+8*eta) epsmass ray C hC hclip hmass
  dsimp only [N,Vchild]
  rw [second_cell_formal_column Z r A B t d hZ]
  rw [second_cell_scale_rpow Z d 1 hZ,second_cell_scale_rpow Z d 2 hZ] at he
  convert he using 1 <;> congr 1 <;> ring_nf

end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O"=>Eisenstein.O

def priorityCellScalar (Z Y L X ell Ractive j t eta eps epsmass B:ℝ) (ray:ℂ) (d:BlockIndex):ℝ :=
  (Real.exp (6*L)*‖(Y:ℂ)*ray*((scales d 1*scales d 2*Z^(secondCellColumnExponent Z X d):ℝ):ℂ)⁻¹‖)*
    Z^((secondCount ell Ractive j t (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2)*(1+epsmass))*
    Z^(2*(max 0 (secondCellColumnExponent Z X d)+
      (secondFormalLabel B (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta))+eps)

theorem source_cell_joint_bound {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn)) (hk:∀x∈source,x.second.frequency≠0)
    (b X:ℝ) (hgeom:∀x∈source,primeProductNorm p x.second.sourceCommon*
      primeProductNorm p x.second.overlap≤ b*X) (d:BlockIndex) (hd:d∈keys p source):
    scales d 0*scales d 2≤ b*X := by
  obtain ⟨x,hx⟩:=(mem_keys_iff p source d).mp hd
  have h0:scales d 0≤ primeProductNorm p x.second.sourceCommon:=by
    simpa [outerNorms,scales] using (le_div_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 0).1
  have h2:scales d 2≤ primeProductNorm p x.second.overlap:=by
    simpa [outerNorms,scales] using (le_div_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 2).1
  exact (mul_le_mul h0 h2 (dyadScale_pos _).le (primeProductNorm_pos p hp _).le).trans
    (hgeom x (cell_subset p source d hx))

theorem priority_source_scalar_budget (caps:Fin 4→ℝ) (hcaps:∀i,0≤ caps i) :
    ∃ Cbin:ℝ,0≤ Cbin ∧ ∀ {ι:Type*} [DecidableEq ι]
    (p:ι→O) (_hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn))
    (Z M r ell V delta A B Ractive j t eta tau pi eps epsmass b C:ℝ)
    (ray:ℂ), 2≤ Z → 0≤ C → 1≤ b → b≤ Z^(6*eta) →
    (∀x∈source,x.second.frequency≠0) →
    (∀x∈source,∀i,outerNorms p x i≤ Z^(caps i)) →
    (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤ b*Z^(r-A-B-t)) →
    (∀d∈keys p source,epsmass*(secondCount ell Ractive j t (secondCellExponent Z d 0)
      (secondCellExponent Z d 1)+11*eta/2)≤ pi) →
    C*Z^(firstKappa M r ell V delta A B Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))*
      (∑d∈keys p source,priorityCellScalar Z (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau))
        (eta*Real.log Z) (Z^(r-A-B-t)) ell Ractive j t eta eps epsmass B ray d) ≤
    C*‖ray‖*(1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+eps) := by
  refine ⟨capConstant caps,capConstant_nonneg caps hcaps,?_⟩
  intro ι _ p hp _ Jo Jn source Z M r ell V delta A B Ractive j t eta tau pi eps epsmass b C
    ray hZ hC hb hthreshold hk hnorm hgeom hmass
  have hZ':1<Z:=lt_of_lt_of_le (by norm_num) hZ
  have hz:0<Z:=zero_lt_one.trans hZ'
  have hcard:((keys p source).card:ℝ)≤(1+capConstant caps*Real.log Z)^4:=by
    have h:=keys_card_le_product p hp source hk caps Z hnorm
    have hr:((keys p source).card:ℝ)≤∏i:Fin 4,((dyadIndex (Z^(caps i)):ℝ)+1):=by exact_mod_cast h
    apply hr.trans
    calc
      _≤∏_i:Fin 4,(1+capConstant caps*Real.log Z):=
        Finset.prod_le_prod (fun _ _=>by positivity) (fun i _=>cap_bin_bound caps hcaps Z hZ i)
      _= _:=by simp
  rw [Finset.mul_sum]
  calc
    _≤∑_d∈keys p source,C*‖ray‖*Z^(r+3*ell+V+48*eta+tau+pi+eps):=by
      apply Finset.sum_le_sum
      intro d hd
      have he:=priority_cell_physical_budget Z hZ' d M r ell V delta A B Ractive j t eta tau pi eps epsmass b C
        ray hC hb (source_cell_joint_bound p hp source hk b _ hgeom d hd) hthreshold (hmass d hd)
      simpa only [priorityCellScalar,mul_assoc] using he
    _= ((keys p source).card:ℝ)*(C*‖ray‖*Z^(r+3*ell+V+48*eta+tau+pi+eps)):=by simp
    _≤ (1+capConstant caps*Real.log Z)^4*(C*‖ray‖*Z^(r+3*ell+V+48*eta+tau+pi+eps)):=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _= _:=by ring

end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ cubic_units_finite
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem actual_priority_retained_moving_radius
    (om Φ:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤ caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤ B₀ i) (J K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (omega₁ omega₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤ hiFresh ∧ HasCompactSupport (omega₁:ℝ→ℂ) ∧ HasCompactSupport (omega₂:ℝ→ℂ) ∧
      tsupport (omega₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (omega₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤ Cbin ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, lambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (_hs : ActualSecondSourceConditions p source),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤ eta → 2≤ Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R (index p x))) →
      (∀ x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ringComplex (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) →
      X=Z^(r-Acol-Bfirst-tcount) → L=eta*Real.log Z →
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) →
      2≤ Z → 1≤ b → b≤ Z^(6*eta) →
      (∀x∈source,∀i,outerNorms p x i≤ Z^(caps i)) →
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤ b*X) →
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤ pi) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest omega₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest omega₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hg Ψ
            (m*cubicIdealGenerator x.quotient) z x) *
          actualSecondProfileRow p hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t) Φ Y X)‖ ≤
      C*A*‖secondRayCoefficient z‖*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨omega₁,omega₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,hC,henergy⟩:=
    actual_priority_source_moving_radius (ι:=ι) (σ:=σ) om Φ lo hi hlo hsupport negative B₀ hB₀ J K εmass hεmass
  obtain ⟨Cbin,hCbin,hbudget⟩:=priority_source_scalar_budget caps hcaps
  refine ⟨omega₁,omega₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,(Fintype.card (Eisˣ × Eisˣ) : ℝ)*(2:ℝ)^(2*K)*C,Cbin,by positivity,hCbin,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b
    ρ t w labels A hd₁ hd₂ hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have he:=henergy p hp hcop hg hpr hinj hc source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X εchild Vlabel ell Ractive j tcount eta ρ t w labels A
    hd₁ hd₂ hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  let H:ℝ:=(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)
  have hheight:(1+‖-priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J*
      (1+‖priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J=H:=by
    cases negative <;> simp [priorityHeight,H,two_mul,pow_add]
  let D:ℝ:=(Fintype.card (Eisˣ × Eisˣ) : ℝ)*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*C*H
  have hD:0≤ D:=by dsimp [D,H];positivity
  let S:ℝ:=∑d∈keys p source,priorityCellScalar Z Y L X ell Ractive j tcount eta εchild εmass Bfirst (secondRayCoefficient z) d
  have hfactor:
      (∑d∈keys p source,(Real.exp (6*L)*‖(Y:ℂ)*secondRayCoefficient z*
          ((scales d 1*scales d 2*Z^(secondCellColumnExponent Z X d):ℝ):ℂ)⁻¹‖)*
        (((Fintype.card (Eisˣ × Eisˣ) : ℝ)*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 (secondCellColumnExponent Z X d)+Vlabel d)+εchild))*
          Z^((ell+Ractive/2-j+tcount+secondCellExponent Z d 0-secondCellExponent Z d 1+11*eta/2)*(1+εmass)))*
          (C*((1+‖-priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J*
            (1+‖priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J))))=D*S:=by
    dsimp only [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [hheight,hVe d]
    dsimp only [D,priorityCellScalar,secondCount]
    ring
  simp only [pow_zero,div_one] at he
  rw [hfactor] at he
  have hbnd:=hbudget p hp source Z M r ell V delta Acol Bfirst Ractive j tcount eta tau pi εchild εmass b D
    (secondRayCoefficient z) hZ2 hD hb hthreshold
    (fun x hx=>frequency_ne_zero_of_gate _ _ (hrows x hx)) hnorm
    (by simpa only [hXe] using hgeom) hmass
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  have hP:0≤ P:=by dsimp [P];positivity
  have hconst:D≤((Fintype.card (Eisˣ × Eisˣ) : ℝ)*(2:ℝ)^(2*K)*C)*A*H:=by
    have h1:(2:ℝ)^slots₁.card≤2^K:=pow_le_pow_right₀ (by norm_num) hslots₁
    have h2:(2:ℝ)^slots₂.card≤2^K:=pow_le_pow_right₀ (by norm_num) hslots₂
    calc
      _≤(Fintype.card (Eisˣ × Eisˣ) : ℝ)*(2:ℝ)^K*(2:ℝ)^K*A*C*H:=by dsimp only [D];gcongr
      _= _:=by rw [show 2*K=K+K by omega,pow_add];ring
  calc
    _≤ P*(D*S):=mul_le_mul_of_nonneg_left he hP
    _≤ D*‖secondRayCoefficient z‖*(1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild):=by
      convert hbnd using 1 ; dsimp only [P,S] ; rw [hYe,hXe,hLe] ; ring
    _≤(((Fintype.card (Eisˣ × Eisˣ) : ℝ)*(2:ℝ)^(2*K)*C)*A*H)*‖secondRayCoefficient z‖*(1+Cbin*Real.log Z)^4*
        Z^(r+3*ell+V+48*eta+tau+pi+εchild):=by gcongr
    _= _:=by dsimp only [H];ring

end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseFirstPriorityParents
variable {ι:Type*} [DecidableEq ι] {Jo:ℕ}
def eraseFirstQuotient (x:Source ι Jo):Source ι Jo:= {x with quotientSupport:=∅}
def fillFirstQuotient (x:Source ι Jo)(D:Finset ι):Source ι Jo:={x with quotientSupport:=D}
omit [DecidableEq ι] in
@[simp] theorem erase_fillFirstQuotient (x:Source ι Jo)(D:Finset ι):
    eraseFirstQuotient (fillFirstQuotient x D)=eraseFirstQuotient x:=rfl
omit [DecidableEq ι] in
@[simp] theorem eraseFirstQuotient_eq (x:Source ι Jo)(hx:x.quotientSupport=∅):
    eraseFirstQuotient x=x:=by cases x;simpa [eraseFirstQuotient] using hx.symm

def globalParentSource (outer:Finset (Source ι Jo))(pool:Finset ι)
    (selector:Source ι Jo→Finset ι→ℂ):Finset (Source ι Jo):=
  outer.biUnion (fun x=>(pool.powerset.filter (fun D=>selector x D≠0)).image (fillFirstQuotient x))

omit [DecidableEq ι] in
theorem sum_globalParentSource {A:Type*}[AddCommMonoid A]
    (outer:Finset (Source ι Jo))(pool:Finset ι)(selector:Source ι Jo→Finset ι→ℂ)
    (houter:∀x∈outer,x.quotientSupport=∅)(H:Source ι Jo→A):
    ∑x∈globalParentSource outer pool selector,H x=
      ∑x∈outer,∑D∈pool.powerset.filter (fun D=>selector x D≠0),H (fillFirstQuotient x D):=by
  unfold globalParentSource
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro x hx
    exact Finset.sum_image (fun D hD E hE he=>congrArg Source.quotientSupport he)
  · intro x hx y hy hxy
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨D,hD,rfl⟩:=Finset.mem_image.mp hz
    obtain ⟨E,hE,he⟩:=Finset.mem_image.mp hz'
    have he':=congrArg eraseFirstQuotient he
    simp only [erase_fillFirstQuotient,eraseFirstQuotient_eq _ (houter x hx),
      eraseFirstQuotient_eq _ (houter y hy)] at he'
    exact hxy he'.symm

omit [DecidableEq ι] in
theorem mem_globalParentSource
    (outer:Finset (Source ι Jo))(pool:Finset ι)(selector:Source ι Jo→Finset ι→ℂ)
    (houter:∀x∈outer,x.quotientSupport=∅)(x:Source ι Jo):
    x∈globalParentSource outer pool selector ↔
      eraseFirstQuotient x∈outer ∧ x.quotientSupport⊆pool ∧
        selector (eraseFirstQuotient x) x.quotientSupport≠0:=by
  constructor
  · intro hx
    obtain ⟨y,hy,hyx⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨D,hD,rfl⟩:=Finset.mem_image.mp hyx
    simp only [erase_fillFirstQuotient,eraseFirstQuotient_eq _ (houter y hy)]
    exact ⟨hy,Finset.mem_powerset.mp (Finset.mem_filter.mp hD).1,(Finset.mem_filter.mp hD).2⟩
  · rintro ⟨hx,hD,hs⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨eraseFirstQuotient x,hx,Finset.mem_image.mpr ⟨x.quotientSupport,?_,?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hD,hs⟩
    · cases x;rfl
end InverseMoment

end

noncomputable section
namespace InverseMomentFirstChildWindows
open InverseMoment InverseMomentFirstProfileUniform Eisenstein
open FirstPassCubeLabels RayFourExpansion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

def actualOuterRatios {ι : Type*} (p : ι→O) (A₁ A₂ C R : ℝ) (d h : O)
    (j : FirstCommonIndex ι) (s : Fin 9→ℝ) (i : Fin 7) : ℝ :=
  firstCommonNorms p A₁ A₂ C R d h j (outerIndex i)/s (outerIndex i)

theorem actual_first_child_windows (g₁ g₂ : 𝓢(ℝ,ℂ)) (m₁ m₂ bcap : ℝ)
    (lo hi : Fin 7→ℝ) (Bρ : Fin 9→ℝ)
    (hm₁ : 0≤ m₁) (hm₂ : 0≤ m₂)
    (hg₁ : Function.support g₁⊆Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂⊆Set.Icc (-m₂) m₂)
    (hlo : ∀i,0<lo i) (hhi : ∀i,lo i≤ hi i) (hBρ : ∀i,0≤ Bρ i) :
    ∃(w₁ w₂ : 𝓢(ℝ,ℂ))(U₀ : Fin 9→𝓢(ℝ,ℂ))(M₀ : Fin 9→ℝ)(a b : ℝ),
      0<a ∧ a≤ b ∧ HasCompactSupport (w₁ : ℝ→ℂ) ∧ HasCompactSupport (w₂ : ℝ→ℂ) ∧
      tsupport (w₁ : ℝ→ℂ)⊆Set.Icc a b ∧ tsupport (w₂ : ℝ→ℂ)⊆Set.Icc a b ∧
      (∀i,0≤ M₀ i) ∧ (∀i,HasCompactSupport (U₀ i : ℝ→ℂ)) ∧
      (∀i,Function.support (U₀ i)⊆Set.Icc (-M₀ i) (M₀ i)) ∧
      ∀{ι κ : Type*}[DecidableEq ι][DecidableEq κ]
      (p : ι→O)(_hp : ∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (source : Finset κ)(F : Finset ι)(selector C₁ C₂ : κ→Finset ι→ℂ)
      (A₁ A₂ C R : κ→ℝ)(d h : κ→O)(s : Fin 9→ℝ)
      (ρ : Fin 9→ℝ)(c₁ c₂ θ₁ θ₂ : ℝ),
      (∀i,0<s i) → (∀i,|ρ i|≤ Bρ i) →
      1≤ c₁ → c₁≤ bcap → 1≤ c₂ → c₂≤ bcap →
      (∀x∈source,∀j∈firstCommonIndices F,
        selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j≠0 →
        ∀i,actualOuterRatios p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j s i∈Set.Icc (lo i) (hi i)) →
      (∀x∈source,∀j∈firstCommonIndices F,
        selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j≠0 →
        positiveSource g₁ c₁ θ₁ (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7))≠0 →
        w₁ (primeProductNorm p j.2.2.1/s 7)=1) ∧
      (∀x∈source,∀j∈firstCommonIndices F,
        selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j≠0 →
        positiveSource g₂ c₂ θ₂ (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8))≠0 →
        w₂ (primeProductNorm p j.2.2.2/s 8)=1) ∧
      (∀x∈source,∀j∈firstCommonIndices F,
        selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j≠0 →
        w₁ (primeProductNorm p j.2.2.1/s 7)≠0 → w₂ (primeProductNorm p j.2.2.2/s 8)≠0 →
        ∀i,U₀ i (firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j) s i+ρ i)=1) := by
  obtain ⟨w₁,w₂,U,M,a,b,ha,hab,hwc₁,hwc₂,hws₁,hws₂,hM,hUc,hUs,hfresh₁,hfresh₂,hcut⟩ :=
    fixed_windows g₁ g₂ m₁ m₂ bcap lo hi Bρ hm₁ hm₂ hg₁ hg₂ hlo hhi hBρ
  refine ⟨w₁,w₂,U,M,a,b,ha,hab,hwc₁,hwc₂,hws₁,hws₂,hM,hUc,hUs,?_⟩
  intro ι κ _ _ p hp _ hg source F selector C₁ C₂ A₁ A₂ C R d h s ρ c₁ c₂ θ₁ θ₂
    hs hρ hc₁ hcb₁ hc₂ hcb₂ hblock
  refine ⟨?_,?_,?_⟩
  · intro x hx j hj hn hg₁n
    apply hfresh₁ c₁ θ₁ (A₁ x/s 0) (C x/s 2) (primeProductNorm p j.2.1/s 5) _
      hc₁ hcb₁ (hblock x hx j hj hn 0) (hblock x hx j hj hn 2) (hblock x hx j hj hn 5)
      (div_pos (primeProductNorm_pos p hp _) (hs 7))
    convert hg₁n using 2 ; ring
  · intro x hx j hj hn hg₂n
    apply hfresh₂ c₂ θ₂ (A₂ x/s 1) (C x/s 2) (primeProductNorm p j.2.1/s 5) _
      hc₂ hcb₂ (hblock x hx j hj hn 1) (hblock x hx j hj hn 2) (hblock x hx j hj hn 5)
      (div_pos (primeProductNorm_pos p hp _) (hs 8))
    convert hg₂n using 2 ; ring
  · intro x hx j hj hn hw₁ hw₂ i
    exact hcut (fun i=>firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j i/s i)
      ρ hρ (hblock x hx j hj hn) hw₁ hw₂ i

end InverseMomentFirstChildWindows
end

noncomputable section
namespace InverseMomentFirstChildWindows
open InverseMoment Eisenstein FirstPassCubeLabels
open InverseSecondSourceBlocks (dyadIndex dyadScale dyadScale_pos dyadIndex_bounds)
open Eisenstein (ringComplex)
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

abbrev SourceIndex := Fin 6→ℕ

def sourceNorms {κ : Type*} (A₁ A₂ C R : κ→ℝ) (d h : κ→O) (x : κ) : Fin 6→ℝ :=
  ![A₁ x,A₂ x,C x,‖ringComplex (d x)‖^2,R x,‖ringComplex (h x)‖^2]

def sourceIndex {κ : Type*} (q : κ→Fin 6→ℝ) (x : κ) : SourceIndex := fun i=>dyadIndex (q x i)
def sourceKeys {κ : Type*} [DecidableEq κ] (q : κ→Fin 6→ℝ) (S : Finset κ) := S.image (sourceIndex q)
def sourceCell {κ : Type*} [DecidableEq κ] (q : κ→Fin 6→ℝ) (S : Finset κ) (k : SourceIndex) :=
  S.filter (fun x=>sourceIndex q x=k)

def commonKeys {ι : Type*} [DecidableEq ι] (p : ι→O) (F : Finset ι) : Finset ℕ :=
  F.powerset.image (fun D=>dyadIndex (primeProductNorm p D))

def commonSelector {ι : Type*} [DecidableEq ι] (p : ι→O) (selector : Finset ι→ℂ) (l : ℕ) (D : Finset ι) : ℂ :=
  if dyadIndex (primeProductNorm p D)=l then selector D else 0

def rawScales (k : SourceIndex) (l : ℕ) (T₁ T₂ : ℝ) : Fin 9→ℝ :=
  ![dyadScale (k 0),dyadScale (k 1),dyadScale (k 2),dyadScale (k 3),dyadScale (k 4),
    dyadScale l,dyadScale (k 5),T₁,T₂]

lemma rawScales_pos (k : SourceIndex) (l : ℕ) (T₁ T₂ : ℝ) (h₁ : 0<T₁) (h₂ : 0<T₂) :
    ∀i,0<rawScales k l T₁ T₂ i := by
  intro i
  fin_cases i <;> first | exact dyadScale_pos _ | exact h₁ | exact h₂

lemma sourceNorms_ge_one {κ : Type*} (A₁ A₂ C R : κ→ℝ) (d h : κ→O) (x : κ)
    (hA₁ : 1≤ A₁ x) (hA₂ : 1≤ A₂ x) (hC : 1≤ C x) (hR : 1≤ R x)
    (hd : d x≠0) (hh : h x≠0) : ∀i,1≤ sourceNorms A₁ A₂ C R d h x i := by
  intro i
  fin_cases i
  · exact hA₁
  · exact hA₂
  · exact hC
  · exact SecondPassArithmetic.element_norm_ge_one _ hd
  · exact hR
  · exact SecondPassArithmetic.element_norm_ge_one _ hh

lemma sourceCell_ratios {κ : Type*} [DecidableEq κ] (q : κ→Fin 6→ℝ) (S : Finset κ)
    (hq : ∀x∈S,∀i,1≤ q x i) (k : SourceIndex) (x : κ) (hx : x∈sourceCell q S k) (i : Fin 6) :
    q x i/dyadScale (k i)∈Set.Icc 1 2 := by
  obtain ⟨hxs,hindex⟩ := Finset.mem_filter.mp hx
  have hh := dyadIndex_bounds (q x i) (hq x hxs i)
  have he : dyadIndex (q x i)=k i := congrFun hindex i
  rw [he] at hh
  exact ⟨(le_div_iff₀ (dyadScale_pos _)).mpr (by simpa using hh.1),
    (div_le_iff₀ (dyadScale_pos _)).mpr hh.2.le⟩

theorem actual_original_cell_ratios {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,lambda∉Ideal.span {p i})
    (S : Finset κ) (selector C₁ C₂ : κ→Finset ι→ℂ)
    (A₁ A₂ C R : κ→ℝ) (d h : κ→O)
    (hq : ∀x∈S,∀i,1≤ sourceNorms A₁ A₂ C R d h x i)
    (k : SourceIndex) (l : ℕ) (T₁ T₂ : ℝ) (x : κ)
    (hx : x∈sourceCell (sourceNorms A₁ A₂ C R d h) S k) (j : FirstCommonIndex ι)
    (hn : commonSelector p (selector x) l j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j≠0) :
    ∀i,actualOuterRatios p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j (rawScales k l T₁ T₂) i∈Set.Icc 1 2 := by
  have hl : dyadIndex (primeProductNorm p j.2.1)=l := by
    by_contra he
    exact hn (by simp [commonSelector,he])
  have hh := dyadIndex_bounds _ (SecondPassArithmetic.primeProductNorm_ge_one p hp j.2.1)
  rw [hl] at hh
  have hD : primeProductNorm p j.2.1/dyadScale l∈Set.Icc 1 2 :=
    ⟨(le_div_iff₀ (dyadScale_pos _)).mpr (by simpa using hh.1),
      (div_le_iff₀ (dyadScale_pos _)).mpr hh.2.le⟩
  intro i
  fin_cases i
  · exact sourceCell_ratios _ S hq k x hx 0
  · exact sourceCell_ratios _ S hq k x hx 1
  · exact sourceCell_ratios _ S hq k x hx 2
  · exact sourceCell_ratios _ S hq k x hx 3
  · exact sourceCell_ratios _ S hq k x hx 4
  · exact hD
  · exact sourceCell_ratios _ S hq k x hx 5

lemma sum_source_cells {κ β : Type*} [DecidableEq κ] [AddCommMonoid β]
    (q : κ→Fin 6→ℝ) (S : Finset κ) (f : κ→β) :
    (∑x∈S,f x)=∑k∈sourceKeys q S,∑x∈sourceCell q S k,f x := by
  exact (Finset.sum_fiberwise_of_maps_to (fun x hx=>Finset.mem_image_of_mem (sourceIndex q) hx) f).symm

lemma common_key_of_index {ι : Type*} [DecidableEq ι] (p : ι→O) (F : Finset ι)
    (j : FirstCommonIndex ι) (hj : j∈firstCommonIndices F) :
    dyadIndex (primeProductNorm p j.2.1)∈commonKeys p F := by
  apply Finset.mem_image_of_mem
  exact (Finset.mem_sigma.mp (Finset.mem_product.mp hj).2).1

lemma sum_common_cells {ι : Type*} [DecidableEq ι] (p : ι→O) (F : Finset ι)
    (selector : Finset ι→ℂ) (G : FirstCommonIndex ι→ℂ) :
    (∑j∈firstCommonIndices F,selector j.2.1*G j)=
      ∑l∈commonKeys p F,∑j∈firstCommonIndices F,commonSelector p selector l j.2.1*G j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hkey := common_key_of_index p F j hj
  simp [commonSelector,ite_mul,hkey]

theorem original_signed_partition {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) (F : Finset ι) (S : Finset κ) (q : κ→Fin 6→ℝ)
    (selector : κ→Finset ι→ℂ) (G : κ→FirstCommonIndex ι→ℂ) :
    (∑x∈S,∑j∈firstCommonIndices F,selector x j.2.1*G x j)=
      ∑k∈sourceKeys q S,∑l∈commonKeys p F,∑x∈sourceCell q S k,
        ∑j∈firstCommonIndices F,commonSelector p (selector x) l j.2.1*G x j := by
  rw [sum_source_cells q S]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    _ = ∑x∈sourceCell q S k,∑l∈commonKeys p F,
        ∑j∈firstCommonIndices F,commonSelector p (selector x) l j.2.1*G x j := by
      apply Finset.sum_congr rfl
      intro x hx
      exact sum_common_cells p F (selector x) (G x)
    _ = _ := Finset.sum_comm

end InverseMomentFirstChildWindows
end

noncomputable section
namespace InverseMomentFirstChildWindows
open InverseMoment Eisenstein FirstPassCubeLabels
open InverseSecondSourceBlocks (dyadIndex)
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

def liveCommonKeys {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) (F : Finset ι) (S : Finset κ)
    (selector : κ→Finset ι→ℂ) (G : κ→FirstCommonIndex ι→ℂ) : Finset ℕ :=
  (((S×ˢfirstCommonIndices F).filter (fun x=>selector x.1 x.2.2.1*G x.1 x.2≠0)).image
    (fun x=>dyadIndex (primeProductNorm p x.2.2.1)))

lemma sum_live_common_cells {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) (F : Finset ι) (S : Finset κ)
    (selector : κ→Finset ι→ℂ) (G : κ→FirstCommonIndex ι→ℂ) (x : κ) (hx : x∈S) :
    (∑j∈firstCommonIndices F,selector x j.2.1*G x j)=
      ∑l∈liveCommonKeys p F S selector G,∑j∈firstCommonIndices F,commonSelector p (selector x) l j.2.1*G x j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hz : selector x j.2.1*G x j=0
  · rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro l hl
    by_cases he : dyadIndex (primeProductNorm p j.2.1)=l
    · simpa only [commonSelector,he,ite_true] using hz
    · simp only [commonSelector,he,ite_false,zero_mul]
  · have hkey : dyadIndex (primeProductNorm p j.2.1)∈liveCommonKeys p F S selector G := by
      exact Finset.mem_image.mpr ⟨(x,j),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hj⟩,hz⟩,rfl⟩
    simp [commonSelector,ite_mul,hkey]

theorem original_live_signed_partition {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) (F : Finset ι) (S : Finset κ) (q : κ→Fin 6→ℝ)
    (selector : κ→Finset ι→ℂ) (G : κ→FirstCommonIndex ι→ℂ) :
    (∑x∈S,∑j∈firstCommonIndices F,selector x j.2.1*G x j)=
      ∑k∈sourceKeys q S,∑l∈liveCommonKeys p F S selector G,∑x∈sourceCell q S k,
        ∑j∈firstCommonIndices F,commonSelector p (selector x) l j.2.1*G x j := by
  rw [sum_source_cells q S]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    _ = ∑x∈sourceCell q S k,∑l∈liveCommonKeys p F S selector G,
        ∑j∈firstCommonIndices F,commonSelector p (selector x) l j.2.1*G x j := by
      apply Finset.sum_congr rfl
      intro x hx
      exact sum_live_common_cells p F S selector G x (Finset.mem_filter.mp hx).1
    _ = _ := Finset.sum_comm

theorem liveCommonKeys_card {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (F : Finset ι) (S : Finset κ) (selector : κ→Finset ι→ℂ)
    (G : κ→FirstCommonIndex ι→ℂ) (R : ℝ)
    (hcap : ∀x∈S,∀j∈firstCommonIndices F,selector x j.2.1*G x j≠0 → primeProductNorm p j.2.1≤ R) :
    (liveCommonKeys p F S selector G).card≤ dyadIndex R+1 := by
  have hsub : liveCommonKeys p F S selector G⊆Finset.range (dyadIndex R+1) := by
    intro l hl
    obtain ⟨⟨x,j⟩,hmem,rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨hxj,hn⟩ := Finset.mem_filter.mp hmem
    obtain ⟨hx,hj⟩ := Finset.mem_product.mp hxj
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    exact Nat.floor_mono (Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (primeProductNorm_pos p hp _) (hcap x hx j hj hn))
  simpa only [Finset.card_range] using Finset.card_le_card hsub

theorem original_live_norm_bound {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) (F : Finset ι) (S : Finset κ) (q : κ→Fin 6→ℝ)
    (selector : κ→Finset ι→ℂ) (G : κ→FirstCommonIndex ι→ℂ) :
    ‖∑x∈S,∑j∈firstCommonIndices F,selector x j.2.1*G x j‖≤
      ∑k∈sourceKeys q S,∑l∈liveCommonKeys p F S selector G,
        ‖∑x∈sourceCell q S k,∑j∈firstCommonIndices F,commonSelector p (selector x) l j.2.1*G x j‖ := by
  rw [original_live_signed_partition p F S q selector G]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k hk=>norm_sum_le _ _))

end InverseMomentFirstChildWindows
end

noncomputable section
namespace InverseMomentFirstChildWindows
open InverseMoment InverseMomentFirstProfileUniform Eisenstein FirstPassCubeLabels
open InverseSecondSourceBlocks (dyadScale dyadScale_pos)
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

def columnScales (k : SourceIndex) (l : ℕ) (X₁ X₂ : ℝ) : Fin 9→ℝ :=
  rawScales k l (X₁/(dyadScale (k 0)*dyadScale (k 2)*dyadScale l))
    (X₂/(dyadScale (k 1)*dyadScale (k 2)*dyadScale l))

lemma columnScales_pos (k : SourceIndex) (l : ℕ) (X₁ X₂ : ℝ) (h₁ : 0<X₁) (h₂ : 0<X₂) :
    ∀i,0<columnScales k l X₁ X₂ i := by
  apply rawScales_pos
  · exact div_pos h₁ (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _))
  · exact div_pos h₂ (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _))

lemma columnScales_left (k : SourceIndex) (l : ℕ) (X₁ X₂ : ℝ) :
    let s := columnScales k l X₁ X₂
    s 0*s 2*s 5*s 7=X₁ := by
  dsimp [columnScales,rawScales]
  exact mul_div_cancel₀ _ (mul_ne_zero (mul_ne_zero (dyadScale_pos _).ne' (dyadScale_pos _).ne') (dyadScale_pos _).ne')

lemma columnScales_right (k : SourceIndex) (l : ℕ) (X₁ X₂ : ℝ) :
    let s := columnScales k l X₁ X₂
    s 1*s 2*s 5*s 8=X₂ := by
  dsimp [columnScales,rawScales]
  exact mul_div_cancel₀ _ (mul_ne_zero (mul_ne_zero (dyadScale_pos _).ne' (dyadScale_pos _).ne') (dyadScale_pos _).ne')

lemma physical_scales_congr {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,lambda∉Ideal.span {p i})
    (source : Finset κ) (F : Finset ι) (selector C₁ C₂ : κ→Finset ι→ℂ) (w : κ→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R : κ→ℝ) (K : ℝ)
    (d h : κ→O) (s t : Fin 9→ℝ)
    (hleft : s 0*s 2*s 5*s 7=t 0*t 2*t 5*t 7)
    (hright : s 1*s 2*s 5*s 8=t 1*t 2*t 5*t 8) :
    firstFamilyPhysicalRows p hg source F selector C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h s=
      firstFamilyPhysicalRows p hg source F selector C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h t := by
  unfold firstFamilyPhysicalRows
  rw [hleft,hright]

theorem original_physical_partition {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,lambda∉Ideal.span {p i})
    (S : Finset κ) (F : Finset ι) (selector C₁ C₂ : κ→Finset ι→ℂ) (w : κ→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R : κ→ℝ) (K : ℝ)
    (d h : κ→O) (s : Fin 9→ℝ) :
    firstFamilyPhysicalRows p hg S F selector C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h s=
      ∑k∈sourceKeys (sourceNorms A₁ A₂ C R d h) S,∑l∈commonKeys p F,
        firstFamilyPhysicalRows p hg (sourceCell (sourceNorms A₁ A₂ C R d h) S k) F
          (fun x=>commonSelector p (selector x) l) C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h s := by
  let G (x : κ) (j : FirstCommonIndex ι) := w x*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j*
    firstNormProfile (fun y=>W₁ (y/(s 0*s 2*s 5*s 7)))
      (fun y=>W₂ (y/(s 1*s 2*s 5*s 8))) Φ (fun _ _=>1) K
      (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j)
  have rows (T : Finset κ) (sel : κ → Finset ι → ℂ) :
      firstFamilyPhysicalRows p hg T F sel C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h s =
        ∑ x ∈ T, ∑ j ∈ firstCommonIndices F, sel x j.2.1 * G x j := by
    unfold firstFamilyPhysicalRows firstBlockedPhysicalRows
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [G]
    ring
  have he := original_signed_partition p F S (sourceNorms A₁ A₂ C R d h) selector G
  simpa only [rows] using he

theorem original_physical_partition_raw {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,lambda∉Ideal.span {p i})
    (S : Finset κ) (F : Finset ι) (selector C₁ C₂ : κ→Finset ι→ℂ) (w : κ→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R : κ→ℝ) (K : ℝ)
    (d h : κ→O) (s : Fin 9→ℝ) :
    firstFamilyPhysicalRows p hg S F selector C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h s=
      ∑k∈sourceKeys (sourceNorms A₁ A₂ C R d h) S,∑l∈commonKeys p F,
        firstFamilyPhysicalRows p hg (sourceCell (sourceNorms A₁ A₂ C R d h) S k) F
          (fun x=>commonSelector p (selector x) l) C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h
          (columnScales k l (s 0*s 2*s 5*s 7) (s 1*s 2*s 5*s 8)) := by
  rw [original_physical_partition p hg S F selector C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h s]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  apply physical_scales_congr
  · exact (columnScales_left k l _ _).symm
  · exact (columnScales_right k l _ _).symm

end InverseMomentFirstChildWindows
end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

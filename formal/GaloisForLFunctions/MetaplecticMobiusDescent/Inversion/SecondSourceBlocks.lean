/-
Second source blocks adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.PriorityLogWindows

/-!
# Second source blocks

Block indices, keys and cells of the second source blocks; dyadic outer norms, retained cell
ratios and polynomial key counts.
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
namespace InversePrioritySecondSource
open Eisenstein SecondPassArithmetic FirstPassCubeLabels
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents
open InversePrincipalEnergy InverseSecondPrincipalCaller RayFourExpansion
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable {Jo : ℕ} (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

def quotientSupport (y : SecondParentSource ι Jo) : Finset ι :=
  Function.extend (sourceIdeal p) id (fun _=>∅) y.quotient

theorem quotientSupport_parent (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (x : Source ι Jo) : quotientSupport p (parent p x)=x.quotientSupport :=
  (sourceIdeal_injective p hinj).extend_apply _ _ _

omit [DecidableEq σ] in
theorem quotientSupport_attach (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (J : Finset σ) (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    quotientSupport p (attach p J q)=q.1.quotientSupport :=
  quotientSupport_parent p hinj q.1

def residualLists (negative : Bool) (lists : σ→Finset ι)
    (y : SecondParentSource ι Jo) (i : σ) : Finset ι :=
  lists i \ (((if negative then y.cube.rightDivisor else y.cube.leftDivisor)∪y.firstCommon)∪
    quotientSupport p y)

omit [DecidableEq σ] in
theorem residualLists_attach (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    residualLists p negative lists (attach p J q)=
      fun i=>lists i\extractedSupport negative q.1 := by
  funext i
  unfold residualLists
  rw [quotientSupport_attach p hinj]
  rfl

omit [DecidableEq σ] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem residualLists_disjoint (negative : Bool) (lists : σ→Finset ι)
    (y : SecondParentSource ι Jo) (i : σ) :
    Disjoint (residualLists p negative lists y i) (quotientSupport p y) := by
  apply Finset.disjoint_left.mpr
  intro q hq hd
  exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_union_right _ hd)

theorem assigned_quotient (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (y : SecondParentSource ι (Jo+(J.card+J.card)))
    (hy : y∈assignedParents p source negative J lists) :
    y.quotient=sourceIdeal p (quotientSupport p y) := by
  obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
  rw [quotientSupport_attach p hinj]
  rfl

def retainedPool (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) : Finset (MarkedSecondSource ι Jo 0) :=
  attachedSecondFamily parents (fun y=>secondDyadicSector pool (secondVariableCutoff p y (R y))
    residual (label y) j)

omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem mem_retainedPool (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) (x : MarkedSecondSource ι Jo 0) :
    x∈retainedPool p pool parents R label residual j ↔
      secondParentOf x∈parents ∧ x.second∈secondDyadicSector pool
        (secondVariableCutoff p (secondParentOf x) (R (secondParentOf x))) residual
        (label (secondParentOf x)) j := mem_attachedSecondFamily _ _ _

theorem retainedPool_conditions (hp : ∀ i,p i≠0)
    (source : Finset (Source ι Jo)) (hs : ∀ x∈source,SourceValid p x)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) :
    ActualSecondSourceConditions p
      (retainedPool p pool (assignedParents p source negative J lists) R label residual j) := by
  apply assigned_family_conditions p hp source hs negative J lists
  intro y hy x hx
  exact (second_variable_original_support p y pool residual (R y) (label y) j x hx).2.1

omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem retainedPool_original_support
    (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) (x : MarkedSecondSource ι Jo 0)
    (hx : x∈retainedPool p pool parents R label residual j) :
    x.second.sourceCommon⊆pool ∧ x.second.divisor⊆x.second.sourceCommon ∧
    x.second.overlap⊆pool ∧ x.second.frequency∈nonzeroChildFrequencyBall
      (actualSecondMultiplier p x) (R (secondParentOf x) x.second.sourceCommon x.second.divisor) := by
  have hh := (mem_retainedPool p pool parents R label residual j x).mp hx
  simpa only [attachSecondExpansion_recover] using
    second_variable_original_support p (secondParentOf x) pool residual (R (secondParentOf x))
      (label (secondParentOf x)) j x.second hh.2

def attachOriginal (J : Finset σ)
    (q : (Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) × SecondExpansionData ι) :
    MarkedSecondSource ι (Jo+(J.card+J.card)) 0 :=
  attachSecondExpansion (attach p J q.1) q.2

omit [DecidableEq σ] in
theorem attachOriginal_injective (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (J : Finset σ) : Function.Injective (attachOriginal p (Jo:=Jo) J) := by
  intro q r he
  apply Prod.ext
  · apply attach_injective p hinj J
    exact congrArg secondParentOf he
  · exact congrArg MarkedSecondSource.second he

theorem retainedPool_iff_original
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (pool : Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0) :
    x∈retainedPool p pool (assignedParents p source negative J lists) R label residual j ↔
      ∃ s∈source,∃ q∈(J.pi (fun i=>lists i∩extractedSupport negative s))×ˢ
        (J.pi (fun i=>lists i∩extractedSupport negative s)),
        ∃ e∈secondDyadicSector pool (secondVariableCutoff p (attach p J (s,q)) (R (attach p J (s,q))))
          residual (label (attach p J (s,q))) j,attachOriginal p J ((s,q),e)=x := by
  constructor
  · intro hx
    obtain ⟨hy,he⟩ := (mem_retainedPool p _ _ _ _ _ _ x).mp hx
    obtain ⟨s,hs,q,hq,ha⟩ := (mem_assignedParents p source negative J lists (secondParentOf x)).mp hy
    refine ⟨s,hs,q,hq,x.second,?_,?_⟩
    · simpa only [ha] using he
    · unfold attachOriginal
      rw [ha,attachSecondExpansion_recover]
  · rintro ⟨s,hs,q,hq,e,he,rfl⟩
    apply (mem_retainedPool p _ _ _ _ _ _ _).mpr
    refine ⟨?_,he⟩
    exact (mem_assignedParents p source negative J lists _).mpr ⟨s,hs,q,hq,rfl⟩

omit [DecidableEq σ] in
theorem attached_coefficient (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (J : Finset σ) (a : σ→ι→ℂ) (w : Source ι Jo→ℂ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) (e : SecondExpansionData ι) :
    coefficient p J a w (secondParentOf (attachOriginal p J (q,e)))=
      w q.1*pairedSlotWeight J J a a q.2 := coefficient_attach p hinj J a w q

variable (hp : ∀ i,p i≠0)
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,lambda∉Ideal.span {p i})

include hp hcop in
theorem varying_lists_parent_family
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀ i,lambda^2∣p i-1)
    (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo→Finset (SecondExpansionData ι))
    (hE : ∀ y∈parents,∀ x∈source y,x.divisor⊆x.sourceCommon)
    (w : SecondParentSource ι Jo→ℂ) (pool : Finset ι) (Ψ : O→*ℂ) (m : O) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : SecondParentSource ι Jo→σ→Finset ι)
    (a₁ a₂ : σ→ι→ℂ) (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) :
    (∑ y∈parents,w y*secondExpansionSource p hg pool Ψ
      (secondParentPuncture p m y) (secondParentLabel p y) (secondParentDivisor p y) z (source y)
      (fun U=>primeMark slots₁ (lists₁ y) a₁ U*W₁ (primeProductNorm p U/X))
      (fun U=>primeMark slots₂ (lists₂ y) a₂ U*W₂ (primeProductNorm p U/X)) Φ Y) =
    (Y:ℂ)*secondRayCoefficient z * ∑ x∈attachedSecondFamily parents source,
      (w (secondParentOf x)*actualSecondSignedWeight p hg Ψ
        (m*cubicIdealGenerator x.quotient) z x)*
      actualSecondProfileRow p hg pool (secondInheritedProfile p x Ψ m z)
        slots₁ slots₂ (lists₁ (secondParentOf x)) (lists₂ (secondParentOf x)) a₁ a₂ W₁ W₂ Φ Y X := by
  rw [sum_attachedSecondFamily]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [secondExpansionSource_attached p hp hg hinj hpr y (source y) (hE y hy)]
  rw [Finset.sum_image (fun x hx z hz he=>attachSecondExpansion_injective y he)]
  simp only [Finset.mul_sum,secondParentOf_attach]
  apply Finset.sum_congr rfl
  intro x hx
  ring

def parentPoisson (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (omega : ℝ→ℂ) (X t Y : ℝ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (y : SecondParentSource ι Jo) : ℂ :=
  firstFreshSecondPoisson p hp hg hinj pool (quotientSupport p y) y.cube.support
    (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit negative
    (if negative then r.1 else r.2) Ψ m
    (primeMark (slots\J) (residualLists p negative lists y) a) omega X
    (∏ i∈y.firstCommon,p i) (secondParentDivisor p y) core t Y

theorem parentPoisson_attach (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (omega : ℝ→ℂ) (X t Y : ℝ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    parentPoisson p hp hg hinj pool negative Ψ m slots J lists a omega X t Y r core (attach p J q)=
      priorityPoisson p hp hg hinj pool q.1.cube q.1.firstCommon negative Ψ m
        ((∏ i ∈ q.1.firstDivisor,p i))
        slots J lists a omega X t Y r core q.1.quotientSupport := by
  unfold parentPoisson
  rw [quotientSupport_attach p hinj,residualLists_attach p hinj]
  rfl

def retainedRow (pool : Finset ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : ℝ→ℂ) (X Y : ℝ) (ray : SecondRayIndex) (x : MarkedSecondSource ι Jo 0) : ℂ :=
  actualSecondSignedWeight p hg Ψ
    (m*cubicIdealGenerator x.quotient) ray x *
    actualSecondProfileRow p hg pool (secondInheritedProfile p x Ψ m ray)
      (slots\J) (slots\J) (residualLists p negative lists (secondParentOf x))
      (residualLists p negative lists (secondParentOf x)) a a V V rowMajorant Y X

include hcop in
theorem parentPoisson_full [Fintype κ]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,lambda^2∣p i-1)
    (y : SecondParentSource ι Jo) (pool : Finset ι)
    (hq : y.quotient=sourceIdeal p (quotientSupport p y))
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ) :
    let Ψ₀ := firstCoreTwist negative (if negative then r.1 else r.2) Ψ core
    let V := principalWindow om lo hi hlo hs negative t
    let H := markedRadial p (slots\J) (residualLists p negative lists y) a ∅ V X
    let K := secondVariableCutoff p y R
    parentPoisson p hp hg hinj pool negative Ψ m slots J lists a om X t Y r core y =
      truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
        (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K +
      (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
        (Y:ℂ)*secondRayCoefficient ray *
          ∑ x∈(secondDyadicSector pool K residual label j).image (attachSecondExpansion y),
            retainedRow p hg pool negative Ψ₀ m slots J lists a V X Y ray x) +
      secondSourceTail p hp hg pool Ψ₀ (secondParentPuncture p m y)
        (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K := by
  intro Ψ₀ V H K
  have hsum : (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈(secondDyadicSector pool K residual label j).image (attachSecondExpansion y),
          actualSecondSignedWeight p hg Ψ₀
            (m*cubicIdealGenerator x.quotient) ray x *
          actualSecondProfileRow p hg pool (secondInheritedProfile p x Ψ₀ m ray)
            (slots\J) (slots\J) (residualLists p negative lists y) (residualLists p negative lists y)
            a a V V rowMajorant Y X) =
    ∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈(secondDyadicSector pool K residual label j).image (attachSecondExpansion y),
          retainedRow p hg pool negative Ψ₀ m slots J lists a V X Y ray x := by
    apply Finset.sum_congr rfl
    intro ray hray
    apply Finset.sum_congr rfl
    intro residual hresidual
    apply Finset.sum_congr rfl
    intro j hj
    apply congrArg ((Y:ℂ)*secondRayCoefficient ray * ·)
    apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    rfl
  have he := first_parent_full_second_source p hp hcop hg hinj hc hpr y pool (quotientSupport p y) hq
    negative (if negative then r.1 else r.2) Ψ m (slots\J) (residualLists p negative lists y) a
    (fun i _=>residualLists_disjoint p negative lists y i) om lo hi hlo hs X t Y hX hY core R label
  exact he.trans (congrArg (fun z : ℂ=>truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K + z +
    secondSourceTail p hp hg pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K) hsum)

omit [∀ i,(Ideal.span {p i}).IsMaximal] in

theorem retained_sum
    (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) (w : SecondParentSource ι Jo→ℂ)
    (H : MarkedSecondSource ι Jo 0→ℂ) :
    (∑ y∈parents,w y*∑ x∈(secondDyadicSector pool (secondVariableCutoff p y (R y))
      residual (label y) j).image (attachSecondExpansion y),H x) =
    ∑ x∈retainedPool p pool parents R label residual j,w (secondParentOf x)*H x := by
  rw [retainedPool,sum_attachedSecondFamily]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.sum_image (fun _ _ _ _ h=>attachSecondExpansion_injective y h),Finset.mul_sum]
  rfl

omit [DecidableEq ι] [DecidableEq κ] in
private theorem commute_parent_sectors [Fintype κ]
    (parents : Finset (SecondParentSource ι Jo)) (pool : Finset ι)
    (H : SecondParentSource ι Jo→SecondRayIndex→Finset ι→κ→ℂ) :
    (∑ y∈parents,∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,H y ray residual j) =
    ∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,∑ y∈parents,H y ray residual j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ray hray
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro residual hresidual
  rw [Finset.sum_comm]

include hcop in
theorem parent_family_full [Fintype κ]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,lambda^2∣p i-1)
    (parents : Finset (SecondParentSource ι Jo)) (pool : Finset ι)
    (hq : ∀ y∈parents,y.quotient=sourceIdeal p (quotientSupport p y))
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (w : SecondParentSource ι Jo→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ) :
    let Ψ₀ := firstCoreTwist negative (if negative then r.1 else r.2) Ψ core
    let V := principalWindow om lo hi hlo hs negative t
    let H := fun y=>markedRadial p (slots\J) (residualLists p negative lists y) a ∅ V X
    let K := fun y=>secondVariableCutoff p y (R y)
    (∑ y∈parents,w y*parentPoisson p hp hg hinj pool negative Ψ m slots J lists a om X t Y r core y) =
    (∑ y∈parents,w y*truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y)) +
    (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈retainedPool p pool parents R label residual j,
          w (secondParentOf x)*retainedRow p hg pool negative Ψ₀ m slots J lists a V X Y ray x) +
    (∑ y∈parents,w y*secondSourceTail p hp hg pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y)) := by
  intro Ψ₀ V H K
  have he : (∑ y∈parents,w y*parentPoisson p hp hg hinj pool negative Ψ m slots J lists a om X t Y r core y) =
    ∑ y∈parents,w y*(truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y) +
      (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
        (Y:ℂ)*secondRayCoefficient ray *
          ∑ x∈(secondDyadicSector pool (K y) residual (label y) j).image (attachSecondExpansion y),
            retainedRow p hg pool negative Ψ₀ m slots J lists a V X Y ray x) +
      secondSourceTail p hp hg pool Ψ₀ (secondParentPuncture p m y)
        (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y)) := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [parentPoisson_full p hp hcop hg hinj hc hpr y pool (hq y hy) negative Ψ m slots J lists a
      om lo hi hlo hs X t Y hX hY r core (R y) (label y)]
  rw [he]
  simp only [mul_add,Finset.sum_add_distrib]
  congr 1
  congr 1
  simp only [Finset.mul_sum]
  rw [commute_parent_sectors]
  apply Finset.sum_congr rfl
  intro ray hray
  apply Finset.sum_congr rfl
  intro residual hresidual
  apply Finset.sum_congr rfl
  intro j hj
  rw [retainedPool,sum_attachedSecondFamily]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.sum_image (fun _ _ _ _ h=>attachSecondExpansion_injective y h)]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [secondParentOf_attach]
  ring

def fullSource [Fintype κ]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (parents : Finset (SecondParentSource ι Jo)) (pool : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (w : SecondParentSource ι Jo→ℂ)
    (V : 𝓢(ℝ,ℂ)) (X Y : ℝ)
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ) : ℂ :=
  let H := fun y=>markedRadial p (slots\J) (residualLists p negative lists y) a ∅ V X
  let K := fun y=>secondVariableCutoff p y (R y)
  (∑ y∈parents,w y*truncatedSecondZero p hg pool Ψ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y)) +
  (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
    (Y:ℂ)*secondRayCoefficient ray *
      ∑ x∈retainedPool p pool parents R label residual j,
        w (secondParentOf x)*retainedRow p hg pool negative Ψ m slots J lists a V X Y ray x) +
  (∑ y∈parents,w y*secondSourceTail p hp hg pool Ψ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y))

include hcop in
theorem first_priority_physical_source [Fintype κ]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,lambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→InverseInitialFibers.PrimeIdeal) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ) :
    (∑ D∈pool.powerset,
      priorityOuter p hg b negative Ψ m selector r core D *
      ‖primeMark J lists a (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)‖^2 *
      (priorityPoisson p hp hg hinj pool b C negative Ψ m
        ((∏ i ∈ E,p i))
        slots J lists a om X t Y r core D).re) =
    (fullSource p hp hg hinj
      (assignedParents p (fixedSource pool b C E old) negative J lists) pool negative
      (firstCoreTwist negative (if negative then r.1 else r.2) Ψ core) m slots J lists a
      (coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)))
      (principalWindow om lo hi hlo hs negative t) X Y R label).re := by
  rw [first_priority_physical_slice p hp hg hinj]
  have hfun (y : SecondParentSource ι (Jo+(J.card+J.card)))
      (hy : y∈assignedParents p (fixedSource pool b C E old) negative J lists) :
      parentFunction p (fun x=>priorityPoisson p hp hg hinj pool b C negative Ψ m
        ((∏ i ∈ E,p i))
        slots J lists a om X t Y r core x.quotientSupport) (forgetAppended y) =
      parentPoisson p hp hg hinj pool negative Ψ m slots J lists a om X t Y r core y := by
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p _ negative J lists y).mp hy
    obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hx
    rw [forget_attach,parentFunction_parent p hinj,parentPoisson_attach p hp hg hinj]
    rfl
  have he := parent_family_full p hp hcop hg hinj hc hpr
    (assignedParents p (fixedSource pool b C E old) negative J lists) pool
    (fun y hy=>assigned_quotient p hinj _ negative J lists y hy)
    negative Ψ m slots J lists a
    (coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)))
    om lo hi hlo hs X t Y hX hY r core R label
  apply congrArg Complex.re
  calc
    _ = ∑ y∈assignedParents p (fixedSource pool b C E old) negative J lists,
      coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)) y *
        parentPoisson p hp hg hinj pool negative Ψ m slots J lists a om X t Y r core y := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [hfun y hy]
    _ = _ := he

include hp in

theorem fixed_retained_conditions
    (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→InverseInitialFibers.PrimeIdeal)
    (hb : b.Admissible) (hC : Disjoint C b.support) (hE : E⊆C∪b.support)
    (hold : ∀ D∈pool.powerset,∀ i,(old i).val∣sourceIdeal p b.support*sourceIdeal p C*sourceIdeal p D)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) :
    ActualSecondSourceConditions p (retainedPool p pool
      (assignedParents p (fixedSource pool b C E old) negative J lists) R label residual j) := by
  apply retainedPool_conditions p hp
  intro x hx
  obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hx
  exact ⟨hb,hC,hE,hold D hD⟩

end InversePrioritySecondSource

end

noncomputable section
namespace InverseSecondSourceBlocks
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson InverseSecondFibers InversePrioritySecondSource
open Eisenstein (ringComplex)
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]

abbrev BlockIndex := Fin 4 → ℕ

def outerNorms (p : ι → O) {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : Fin 4 → ℝ :=
  ![primeProductNorm p x.second.sourceCommon, primeProductNorm p x.second.divisor,
    primeProductNorm p x.second.overlap, ‖ringComplex x.second.frequency‖^2]

theorem outerNorms_eq_actual (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (Ψ : O →* ℂ) (m : O)
    (ray : SecondRayIndex) (N M : Finset ι) (i : Fin 4) :
    outerNorms p x i = secondActualNorms p (secondInheritedProfile p x Ψ m ray) N M
      (Fin.castLE (by decide : 4 ≤ 6) i) := by
  fin_cases i <;> simp [outerNorms,secondActualNorms,secondInheritedProfile,
    actualMarkedSecondProfileData,expansionProfileData,primeProductNorm]

omit [DecidableEq ι] in
theorem outerNorms_ge_one (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (hk : x.second.frequency ≠ 0) :
    ∀ i,1 ≤ outerNorms p x i := by
  intro i
  fin_cases i
  · exact primeProductNorm_ge_one p hp _
  · exact primeProductNorm_ge_one p hp _
  · exact primeProductNorm_ge_one p hp _
  · exact element_norm_ge_one _ hk

theorem frequency_ne_zero_of_gate (a : O) (R : ℝ) {k : O}
    (hk : k ∈ nonzeroChildFrequencyBall a R) : k ≠ 0 :=
  (Finset.mem_erase.mp hk).1

theorem retained_frequency_ne_zero (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]
    {Jo : ℕ} (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo → Finset ι → Finset ι → ℝ)
    (label : SecondParentSource ι Jo → Finset ι → SecondExpansionData ι → κ)
    (residual : Finset ι) (j : κ) (x : MarkedSecondSource ι Jo 0)
    (hx : x ∈ retainedPool p pool parents R label residual j) : x.second.frequency ≠ 0 :=
  frequency_ne_zero_of_gate _ _ (retainedPool_original_support p pool parents R label residual j x hx).2.2.2

def dyadIndex (r : ℝ) : ℕ := ⌊Real.logb 2 r⌋₊
def dyadScale (n : ℕ) : ℝ := 2^n

theorem dyadScale_pos (n : ℕ) : 0 < dyadScale n := by unfold dyadScale; positivity

theorem dyadIndex_bounds (r : ℝ) (hr : 1 ≤ r) :
    dyadScale (dyadIndex r) ≤ r ∧ r < 2*dyadScale (dyadIndex r) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hlog : 0 ≤ Real.logb 2 r := Real.logb_nonneg (by norm_num) hr
  constructor
  · have h := (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) hr0).mp (Nat.floor_le hlog)
    simpa only [dyadScale,dyadIndex,Real.rpow_natCast] using h
  · have h := (Real.logb_lt_iff_lt_rpow (by norm_num : (1:ℝ)<2) hr0).mp
      (Nat.lt_floor_add_one (Real.logb 2 r))
    have ht : r < (2:ℝ)^(dyadIndex r+1) := by
      rw [←Real.rpow_natCast]
      simpa only [Nat.cast_add,Nat.cast_one,dyadIndex] using h
    simpa only [dyadScale,pow_succ,mul_comm] using ht

def index (p : ι → O) {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : BlockIndex :=
  fun i => dyadIndex (outerNorms p x i)

def keys (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) : Finset BlockIndex :=
  source.image (index p)

def cell (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) : Finset (MarkedSecondSource ι Jo Jn) := source.filter (fun x => index p x = d)

omit [DecidableEq ι] in
@[simp] theorem mem_cell (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) :
    x ∈ cell p source d ↔ x ∈ source ∧ index p x = d := Finset.mem_filter

omit [DecidableEq ι] in
theorem cell_subset (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) : cell p source d ⊆ source := Finset.filter_subset _ _

omit [DecidableEq ι] in
theorem cell_inherits (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) (P : MarkedSecondSource ι Jo Jn → Prop) (hP : ∀ x∈source,P x) :
    ∀ x∈cell p source d,P x := fun x hx => hP x (cell_subset p source d hx)

theorem cell_conditions (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (d : BlockIndex) :
    ActualSecondSourceConditions p (cell p source d) := ActualSecondSourceConditions.mono p hs (cell_subset p source d)

omit [DecidableEq ι] in
theorem mem_keys_iff (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) : d ∈ keys p source ↔ (cell p source d).Nonempty := by
  simp only [keys,Finset.mem_image,Finset.nonempty_iff_ne_empty]
  constructor
  · rintro ⟨x,hx,he⟩
    exact Finset.nonempty_iff_ne_empty.mp ⟨x,(mem_cell p source d x).mpr ⟨hx,he⟩⟩
  · intro h
    obtain ⟨x,hx⟩ := Finset.nonempty_iff_ne_empty.mpr h
    exact ⟨x,(mem_cell p source d x).mp hx⟩

omit [DecidableEq ι] in
theorem cells_disjoint (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    {d e : BlockIndex} (h : d ≠ e) : Disjoint (cell p source d) (cell p source e) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact h (((mem_cell p source d x).mp hx).2.symm.trans ((mem_cell p source e x).mp hy).2)

omit [DecidableEq ι] in
theorem cell_ratios (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀ x∈source,x.second.frequency ≠ 0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d) (i : Fin 4) :
    1 ≤ outerNorms p x i / dyadScale (d i) ∧ outerNorms p x i / dyadScale (d i) < 2 := by
  obtain ⟨hxs,he⟩ := (mem_cell p source d x).mp hx
  have hb := dyadIndex_bounds _ (outerNorms_ge_one p hp x (hk x hxs) i)
  have hi : dyadIndex (outerNorms p x i) = d i := congrFun he i
  rw [hi] at hb
  exact ⟨(le_div_iff₀ (dyadScale_pos _)).mpr (by simpa using hb.1),
    (div_lt_iff₀ (dyadScale_pos _)).mpr hb.2⟩

omit [DecidableEq ι] in
theorem sum_cells (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    {β : Type*} [AddCommMonoid β] (f : MarkedSecondSource ι Jo Jn → β) :
    (∑ x∈source,f x) = ∑ d∈keys p source,∑ x∈cell p source d,f x := by
  exact (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem (index p) hx) f).symm

def scales (d : BlockIndex) : Fin 4 → ℝ := fun i => dyadScale (d i)

theorem actual_cell_ratios (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀ x∈source,x.second.frequency ≠ 0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex) (N M : Finset ι) (i : Fin 4) :
    1 ≤ secondActualNorms p (secondInheritedProfile p x Ψ m ray) N M
      (Fin.castLE (by decide : 4 ≤ 6) i) / scales d i ∧
    secondActualNorms p (secondInheritedProfile p x Ψ m ray) N M
      (Fin.castLE (by decide : 4 ≤ 6) i) / scales d i < 2 := by
  rw [←outerNorms_eq_actual p x Ψ m ray N M i]
  exact cell_ratios p hp source hk d x hx i

theorem physical_source_partition
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0 → Finset ι)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y X : ℝ) :
    (Y:ℂ)*secondRayCoefficient ray *
      (∑ x∈source,(w x * actualSecondSignedWeight p hg Ψ
        (m*cubicIdealGenerator x.quotient) ray x) *
        actualSecondProfileRow p hg pool (secondInheritedProfile p x Ψ m ray)
          slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x)
          a₁ a₂ W₁ W₂ Φ Y X) =
    ∑ d∈keys p source,(Y:ℂ)*secondRayCoefficient ray *
      (∑ x∈cell p source d,(w x * actualSecondSignedWeight p hg Ψ
        (m*cubicIdealGenerator x.quotient) ray x) *
        actualSecondProfileRow p hg pool (secondInheritedProfile p x Ψ m ray)
          slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x)
          a₁ a₂ W₁ W₂ Φ Y X) := by
  rw [sum_cells p source]
  exact Finset.mul_sum _ _ _

def capBox (A : Fin 4 → ℝ) (Z : ℝ) : Finset BlockIndex :=
  Fintype.piFinset (fun i => Finset.range (dyadIndex (Z^(A i))+1))

omit [DecidableEq ι] in
theorem keys_subset_capBox (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀ x∈source,x.second.frequency ≠ 0)
    (A : Fin 4 → ℝ) (Z : ℝ) (hcaps : ∀ x∈source,∀ i,outerNorms p x i ≤ Z^(A i)) :
    keys p source ⊆ capBox A Z := by
  intro d hd
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hd
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  exact Nat.floor_mono (Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (lt_of_lt_of_le zero_lt_one (outerNorms_ge_one p hp x (hk x hx) i)) (hcaps x hx i))

omit [DecidableEq ι] in
theorem keys_card_le_product (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀ x∈source,x.second.frequency ≠ 0)
    (A : Fin 4 → ℝ) (Z : ℝ) (hcaps : ∀ x∈source,∀ i,outerNorms p x i ≤ Z^(A i)) :
    (keys p source).card ≤ ∏ i : Fin 4,(dyadIndex (Z^(A i))+1) := by
  have h := Finset.card_le_card (keys_subset_capBox p hp source hk A Z hcaps)
  simpa [capBox,Fintype.card_piFinset] using h

def capConstant (A : Fin 4 → ℝ) : ℝ := (∑ i,A i)/Real.log 2

theorem capConstant_nonneg (A : Fin 4 → ℝ) (hA : ∀ i,0 ≤ A i) :
    0 ≤ capConstant A := by
  unfold capConstant
  exact div_nonneg (Finset.sum_nonneg (fun i _ => hA i)) (Real.log_pos (by norm_num)).le

theorem cap_bin_bound (A : Fin 4 → ℝ) (hA : ∀ i,0 ≤ A i) (Z : ℝ) (hZ : 2 ≤ Z)
    (i : Fin 4) : (dyadIndex (Z^(A i)) : ℝ)+1 ≤ 1+capConstant A*Real.log Z := by
  have hZ0 : 0 < Z := by linarith
  have hZi : 1 ≤ Z^(A i) := Real.one_le_rpow (by linarith) (hA i)
  have hf := Nat.floor_le (Real.logb_nonneg (by norm_num : (1:ℝ)<2) hZi)
  have hAi : A i ≤ ∑ j,A j := Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ i)
  have hc := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hAi
    (Real.log_pos (by norm_num : (1:ℝ)<2)).le) (Real.log_nonneg (by linarith : 1 ≤ Z))
  dsimp [dyadIndex,capConstant]
  calc
    _ ≤ 1+Real.logb 2 (Z^(A i)) := by linarith
    _ = 1+(A i/Real.log 2)*Real.log Z := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos hZ0,Real.logb]
      ring
    _ ≤ _ := by linarith

omit [DecidableEq ι] in
theorem keys_card_polynomial (A : Fin 4 → ℝ) (hA : ∀ i,0 ≤ A i) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (p : ι → O) (_hp : ∀ i,p i ≠ 0)
      [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ}
      (source : Finset (MarkedSecondSource ι Jo Jn)) (Z : ℝ), 2 ≤ Z →
      (∀ x∈source,x.second.frequency ≠ 0) →
      (∀ x∈source,∀ i,outerNorms p x i ≤ Z^(A i)) →
      ((keys p source).card : ℝ) ≤ (1+C*Real.log Z)^4 := by
  refine ⟨capConstant A,capConstant_nonneg A hA,?_⟩
  intro p hp _ Jo Jn source Z hZ hk hcaps
  have h := keys_card_le_product p hp source hk A Z hcaps
  have hr : ((keys p source).card:ℝ) ≤ ∏ i : Fin 4,((dyadIndex (Z^(A i)):ℝ)+1) := by
    exact_mod_cast h
  apply hr.trans
  calc
    _ ≤ ∏ _i : Fin 4,(1+capConstant A*Real.log Z) :=
      Finset.prod_le_prod (fun _ _ => by positivity) (fun i _ => cap_bin_bound A hA Z hZ i)
    _ = (1+capConstant A*Real.log Z)^4 := by simp

omit [DecidableEq ι] in
@[simp] theorem keys_empty (p : ι → O) (Jo Jn : ℕ) :
    keys p (∅ : Finset (MarkedSecondSource ι Jo Jn)) = ∅ := by simp [keys]

omit [DecidableEq ι] in
@[simp] theorem cell_empty (p : ι → O) (Jo Jn : ℕ) (d : BlockIndex) :
    cell p (∅ : Finset (MarkedSecondSource ι Jo Jn)) d = ∅ := by simp [cell]

omit [DecidableEq ι] in
theorem cell_empty_of_not_mem (p : ι → O) {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (d : BlockIndex) (hd : d ∉ keys p source) :
    cell p source d = ∅ := by
  exact Finset.not_nonempty_iff_eq_empty.mp (fun h => hd ((mem_keys_iff p source d).mpr h))

theorem retained_cell_ratios (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] {Jo : ℕ}
    (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo → Finset ι → Finset ι → ℝ)
    (label : SecondParentSource ι Jo → Finset ι → SecondExpansionData ι → κ)
    (residual : Finset ι) (j : κ) (d : BlockIndex) (x : MarkedSecondSource ι Jo 0)
    (hx : x∈cell p (retainedPool p pool parents R label residual j) d)
    (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex) (N M : Finset ι) (i : Fin 4) :
    1 ≤ secondActualNorms p (secondInheritedProfile p x Ψ m ray) N M
      (Fin.castLE (by decide : 4 ≤ 6) i)/scales d i ∧
    secondActualNorms p (secondInheritedProfile p x Ψ m ray) N M
      (Fin.castLE (by decide : 4 ≤ 6) i)/scales d i < 2 :=
  actual_cell_ratios p hp _ (retained_frequency_ne_zero p pool parents R label residual j)
    d x hx Ψ m ray N M i

theorem retained_keys_card_polynomial (A : Fin 4 → ℝ) (hA : ∀ i,0 ≤ A i) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (p : ι → O) (_hp : ∀ i,p i ≠ 0)
      [∀ i,(Ideal.span {p i}).IsMaximal] {Jo : ℕ}
      (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
      (R : SecondParentSource ι Jo → Finset ι → Finset ι → ℝ)
      (label : SecondParentSource ι Jo → Finset ι → SecondExpansionData ι → κ)
      (residual : Finset ι) (j : κ) (Z : ℝ), 2 ≤ Z →
      (∀ x∈retainedPool p pool parents R label residual j,∀ i,outerNorms p x i ≤ Z^(A i)) →
      ((keys p (retainedPool p pool parents R label residual j)).card:ℝ) ≤
        (1+C*Real.log Z)^4 := by
  obtain ⟨C,hC,h⟩ := keys_card_polynomial (ι:=ι) A hA
  refine ⟨C,hC,?_⟩
  intro p hp _ Jo pool parents R label residual j Z hZ hcaps
  exact h p hp _ Z hZ (retained_frequency_ne_zero p pool parents R label residual j) hcaps

end InverseSecondSourceBlocks

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

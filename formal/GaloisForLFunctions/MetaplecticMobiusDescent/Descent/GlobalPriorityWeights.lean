/-
Global priority weights adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.FirstOriginalProfiles
import GaloisForLFunctions.MetaplecticMobiusDescent.Inversion.WholePriorityRetainedSource

/-!
# Global priority weights

Outer data and normalized weights of the global priority family; the global second energy of
the source, rapid physical tails of the whole cube, and original cell windows and child
energies of the first original profile.
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
namespace InverseMoment
open Eisenstein SecondPassArithmetic FirstPassCubeLabels RayFourExpansion
open InverseFirstPriorityParents InverseMomentWholePriorityParents InverseWholePriorityRetainedSource
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O"=>Eisenstein.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→O)[∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,lambda∉Ideal.span {p i})

def globalPriorityOuter (negative:Bool)(Ψ:O→*ℂ)(m:O)
    (ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(w:Source ι Jo→ℂ)(x:Source ι Jo):ℂ:=
  w x*(priorityOuter p hg x.cube negative Ψ m (fun _=>1) ray core x.quotientSupport:ℂ)

def globalPriorityWeight (negative:Bool)(Ψ:O→*ℂ)(m:O)
    (ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(w:Source ι Jo→ℂ)
    (J:Finset σ)(a:σ→ι→ℂ)(x:MarkedSecondSource ι (Jo+(J.card+J.card)) 0):ℂ:=
  coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) (secondParentOf x)

def normalizedGlobalPriorityWeight (negative:Bool)(Ψ:O→*ℂ)(m:O)
    (ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(w:Source ι Jo→ℂ)
    (J:Finset σ)(a:σ→ι→ℂ)(x:MarkedSecondSource ι (Jo+(J.card+J.card)) 0):ℂ:=
  globalPriorityWeight p hg negative Ψ m ray core w J a x/(coefficientBound:ℂ)

theorem globalPriorityWeight_norm
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι)(original:Finset (Source ι Jo))(pool:Finset ι)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)
    (w:Source ι Jo→ℂ)(hw:∀x∈original,‖w x‖≤1)(hΨ:∀u,‖Ψ u‖≤1)
    (J:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(ha:∀i∈J,∀k∈lists i,‖a i k‖≤1)
    (R:SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (x:MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx:x∈unifiedSource p pool (wholeAssignedParents p (fun x=>extra x.cube) original negative J lists) R):
    ‖globalPriorityWeight p hg negative Ψ m ray core w J a x‖≤ coefficientBound:=by
  apply InverseMomentWholeRetainedSource.whole_coefficient_norm p hinj (fun x=>extra x.cube)
    original negative J lists a _ coefficientBound ha
  · intro y hy
    rw [globalPriorityOuter,norm_mul]
    have hn:=priorityOuter_norm p hg y.cube negative Ψ m (fun _=>1) ray core y.quotientSupport
      (by simp) (hΨ _)
    exact (mul_le_mul (hw y hy) hn (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · exact ((mem_unifiedSource p pool _ R x).mp hx).1

theorem normalizedGlobalPriorityWeight_norm
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι)(original:Finset (Source ι Jo))(pool:Finset ι)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)
    (w:Source ι Jo→ℂ)(hw:∀x∈original,‖w x‖≤1)(hΨ:∀u,‖Ψ u‖≤1)
    (J:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(ha:∀i∈J,∀k∈lists i,‖a i k‖≤1)
    (R:SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (x:MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx:x∈unifiedSource p pool (wholeAssignedParents p (fun x=>extra x.cube) original negative J lists) R):
    ‖normalizedGlobalPriorityWeight p hg negative Ψ m ray core w J a x‖≤1:=by
  rw [normalizedGlobalPriorityWeight,norm_div,Complex.norm_real,Real.norm_of_nonneg coefficientBound_pos.le]
  exact (div_le_one coefficientBound_pos).mpr
    (globalPriorityWeight_norm p hg hinj extra original pool negative Ψ m ray core w hw hΨ J lists a ha R x hx)

omit [DecidableEq σ] in
theorem globalPriority_sum_normalized
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)
    (w:Source ι Jo→ℂ)(J:Finset σ)(a:σ→ι→ℂ)
    (source:Finset (MarkedSecondSource ι (Jo+(J.card+J.card)) 0))
    (H:MarkedSecondSource ι (Jo+(J.card+J.card)) 0→ℂ):
    (∑x∈source,globalPriorityWeight p hg negative Ψ m ray core w J a x*H x)=
      (coefficientBound:ℂ)*∑x∈source,normalizedGlobalPriorityWeight p hg negative Ψ m ray core w J a x*H x:=by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  unfold normalizedGlobalPriorityWeight
  have hn:(coefficientBound:ℂ)≠0:=by exact_mod_cast coefficientBound_pos.ne'
  field_simp
end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseWholePriorityRetainedSource RayFourExpansion
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "Eis"=>Eisenstein.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem global_priority_retained_moving_radius
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
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
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis) (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:SecondParentSource ι (Jo+(assigned.card+assigned.card))→Finset ι→Finset ι→ℝ)
,
    let source:=unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) cutoff
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    ∀(z:SecondRayIndex)
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) →
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
      (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo+(assigned.card+assigned.card) ≤ 2*K → (slots\assigned).card ≤ K → (slots\assigned).card ≤ K → 0 ≤ A →
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) →
      X=Z^(r-Acol-Bfirst-tcount) → L=eta*Real.log Z →
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) →
      2≤ Z → 1≤ b → b≤ Z^(6*eta) →
      (∀x∈source,∀i,outerNorms p x i≤ Z^(caps i)) →
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤ b*X) →
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤ pi) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest omega₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest omega₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖(Y:ℂ)*secondRayCoefficient z *
        ∑x∈source,globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖ ≤
      C*A*‖secondRayCoefficient z‖*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨omega₁,omega₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,Cbin,hC,hCbin,he⟩:=
    actual_priority_retained_moving_radius (ι:=ι) (σ:=σ) om rowMajorant lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ J K εmass hεmass
  refine ⟨omega₁,omega₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,coefficientBound*C,Cbin,mul_nonneg coefficientBound_pos.le hC,hCbin,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
    Ψ m ray core slots assigned lists a cutoff source Ψ₀ z
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A
    haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have hsource:ActualSecondSourceConditions p source:=
    unified_conditions p hp extra original hvalid hextra negative assigned lists pool cutoff
  have hd:∀x∈source,∀i∈InverseMomentWholeRetainedSource.deleted p extra negative x,
      i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient:=
    unified_deleted_support p hinj extra original hvalid hextra negative assigned lists pool cutoff
  have hw:∀x∈source,‖normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a x‖≤1:=
    fun x hx=>normalizedGlobalPriorityWeight_norm p hg hinj extra original pool negative Ψ m ray core w hwOriginal hΨ
      assigned lists a haassigned cutoff x hx
  have hΨ₀:∀n,‖Ψ₀ n‖≤1:=fun n=>(firstCoreTwist_norm_le negative (if negative then ray.1 else ray.2)
    Ψ core n).trans (hΨ n)
  have he₀:=he p hp hcop hg hpr hinj hc source hsource pool Ψ₀ m z (slots\assigned) (slots\assigned)
    lists lists a a (InverseMomentWholeRetainedSource.deleted p extra negative)
    (InverseMomentWholeRetainedSource.deleted p extra negative)
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t
    (normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a) labels A
    hd hd hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ₀ hw
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have hrow:∀x:MarkedSecondSource ι (Jo+(assigned.card+assigned.card)) 0,wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
      (principalWindow om lo hi hlo hsupport negative t) X Y z x=
      actualSecondSignedWeight p hg Ψ₀ (m*cubicIdealGenerator x.quotient) z x*
      actualSecondProfileRow p hg pool (secondInheritedProfile p x Ψ₀ m z)
        (slots\assigned) (slots\assigned)
        (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x)
        (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x) a a
        (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t)
        rowMajorant Y X:=fun x=>wholeRow_eq p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a _ X Y z x
  rw [globalPriority_sum_normalized p hg negative Ψ m ray core w assigned a source]
  rw [show (Y:ℂ)*secondRayCoefficient z*((coefficientBound:ℂ)*
      ∑x∈source,normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a x*
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
          (principalWindow om lo hi hlo hsupport negative t) X Y z x)=
      (coefficientBound:ℂ)*((Y:ℂ)*secondRayCoefficient z*
        ∑x∈source,normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a x*
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x) by ring]
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg coefficientBound_pos.le]
  simp_rw [hrow,←mul_assoc]
  convert mul_le_mul_of_nonneg_left he₀ coefficientBound_pos.le using 1 <;> first | rfl | ring

end InverseMoment

end

noncomputable section
namespace InverseMoment
open Eisenstein SecondPassArithmetic FirstPassCubeLabels RayFourExpansion
open InverseFirstPriorityParents InverseMomentWholePriorityParents InverseWholePriorityRetainedSource
open InverseMomentWholePriorityPhysical InversePrioritySecondSource InversePrincipalEnergy InverseSecondPrincipalCaller
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O"=>Eisenstein.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

theorem global_priority_physical_source
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,lambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)
    (w:Source ι Jo→ℂ)(slots J:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ)(hX:0<X)(hY:0<Y)(R:Finset ι→Finset ι→ℝ):
    let parents:=wholeAssignedParents p (fun x=>extra x.cube) original negative J lists
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    let V:=principalWindow om lo hi hlo hs negative t
    let H:=fun y:SecondParentSource ι (Jo+(J.card+J.card))=>markedRadial p (slots\J)
      (residualLists p negative (fun i=>lists i\extra y.cube) y) a ∅ V X
    let K:=fun y:SecondParentSource ι (Jo+(J.card+J.card))=>secondVariableCutoff p y R
    let coeff:=coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w)
    (∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra x.cube)
        a om X t Y ray core (parent p x))=
    (∑y∈parents,coeff y*truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y))+
    (∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z*
      ∑x∈unifiedSource p pool parents (fun _=>R),globalPriorityWeight p hg negative Ψ m ray core w J a x*
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots J lists a V X Y z x)+
    (∑y∈parents,coeff y*secondSourceTail p hp hg pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y)):=by
  intro parents Ψ₀ V H K coeff
  rw [whole_signed_source_full p hp hcop hg hinj hc hpr extra pool original
    (globalPriorityOuter p hg negative Ψ m ray core w) negative Ψ m slots J lists a
    om lo hi hlo hs X t Y hX hY ray core R (fun _ _=>())]
  exact fullPhysical_unified p hg hp hcop hinj extra pool parents coeff negative Ψ m slots J lists a
    V X Y ray core R (fun _ _=>())
end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InverseFirstPriorityParents InverseMomentWholePriorityParents InverseWholePriorityValidSource
open InversePrioritySecondSource
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O"=>Eisenstein.O
variable {ι σ:Type*}[DecidableEq ι][DecidableEq σ]{Jo:ℕ}
variable (p:ι→O)[∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,lambda∉Ideal.span {p i})

theorem global_original_priority_slice
    (outer:Finset (Source ι Jo))(pool:Finset ι)(selector:Source ι Jo→Finset ι→ℂ)
    (houter:∀x∈outer,x.quotientSupport=∅)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)
    (H:Source ι Jo→ℂ):
    (∑x∈globalParentSource outer pool selector,
      globalPriorityOuter p hg negative Ψ m ray core
        (fun x=>(‖selector (eraseFirstQuotient x) x.quotientSupport‖:ℂ)) x*H x)=
    ∑x∈outer,∑D∈pool.powerset,
      (priorityOuter p hg x.cube negative Ψ m (selector x) ray core D:ℂ)*H (fillFirstQuotient x D):=by
  rw [sum_globalParentSource outer pool selector houter]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro D hD
  by_cases hs:selector x D≠0
  · rw [if_pos hs]
    simp only [globalPriorityOuter,erase_fillFirstQuotient,eraseFirstQuotient_eq _ (houter x hx)]
    dsimp only [fillFirstQuotient,priorityOuter]
    simp only [norm_one,mul_one,Complex.ofReal_mul]
    ring
  · rw [if_neg hs,priorityOuter_zero p hg x.cube negative Ψ m (selector x) ray core D (not_ne_iff.mp hs)]
    simp

theorem global_second_energy_source
    (hp:∀i,p i≠0)(hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (outer:Finset (Source ι Jo))(pool:Finset ι)(selector:Source ι Jo→Finset ι→ℂ)
    (houter:∀x∈outer,x.quotientSupport=∅)(extra:CubeCoordinates ι→Finset ι)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:ℝ→ℂ)(X t Y:ℝ):
    (∑x∈outer,firstWholePrioritySecondEnergy p hp hg hinj pool x.cube x.firstCommon
      (extra x.cube) negative Ψ m ((∏ i ∈ x.firstDivisor,p i))
      slots lists a (selector x) om X t Y)=
    firstCoreMassBound*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
      (∑x∈globalParentSource outer pool selector,
        globalPriorityOuter p hg negative Ψ m ray core
          (fun x=>(‖selector (eraseFirstQuotient x) x.quotientSupport‖:ℂ)) x*
        (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
        parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra x.cube)
          a om X t Y ray core (parent p x)).re:=by
  have hs (ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(J:Finset σ):
      (∑x∈globalParentSource outer pool selector,
        globalPriorityOuter p hg negative Ψ m ray core
          (fun x=>(‖selector (eraseFirstQuotient x) x.quotientSupport‖:ℂ)) x*
        (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
        parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra x.cube)
          a om X t Y ray core (parent p x))=
      ∑x∈outer,∑D∈pool.powerset,(priorityOuter p hg x.cube negative Ψ m (selector x) ray core D:ℂ)*
        (‖primeMark J lists a ((extra x.cube∪((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon))∪D)‖^2:ℝ)*
        wholePriorityPoisson p hp hg hinj pool x.cube x.firstCommon x.firstDivisor (extra x.cube)
          negative Ψ m slots J lists a om X t Y ray core D:=by
    simp_rw [mul_assoc]
    rw [global_original_priority_slice p hg outer pool selector houter negative Ψ m ray core]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro D hD
    have hm : wholeExtractedSupport (fun x=>extra x.cube) negative (fillFirstQuotient x D)=
        ((extra x.cube∪((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon))∪D) := by
      simp only [wholeExtractedSupport,extractedSupport,fillFirstQuotient,Finset.union_assoc]
    rw [hm]
    have hf : fillFirstQuotient x D = fixedPoint x.cube x.firstCommon x.firstDivisor x.oldAssigned D := by
      cases x;rfl
    rw [hf]
    change (priorityOuter p hg x.cube negative Ψ m (selector x) ray core D:ℂ)*
      ((‖primeMark J lists a ((extra x.cube∪((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon))∪D)‖^2:ℝ)*
        parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra x.cube)
          a om X t Y ray core (parent p (fixedPoint x.cube x.firstCommon x.firstDivisor x.oldAssigned D))) = _
    rw [parentPoisson_fixed_whole p hp hg hinj]
  simp_rw [hs]
  simp only [Complex.re_sum,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
  unfold firstWholePrioritySecondEnergy
  simp only [Finset.mul_sum,wholePriorityPoisson,priorityOuter]
  rw [Finset.sum_comm (s:=outer)]
  apply Finset.sum_congr rfl
  intro ray hray
  simp_rw [Finset.sum_comm (s:=pool.powerset) (t:=(Finset.univ : Finset FirstCoreIndex))]
  rw [Finset.sum_comm (s:=outer)]
  apply Finset.sum_congr rfl
  intro core hcore
  simp_rw [Finset.sum_comm (s:=pool.powerset) (t:=slots.powerset)]
  rw [Finset.sum_comm (s:=outer)]
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro D hD
  ring
end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

theorem first_whole_cube_rapid_physical_tail (ε:ℝ) (hε:0<ε)
    (Mmax Fmax eta tau saving:ℝ) (hMm:0≤ Mmax) (hFm:0≤ Fmax)
    (heta:0≤ eta) (htau:0<tau) :
    ∃ (s:Finset (ℕ×ℕ)) (Ct Cm:ℝ),0<Ct ∧ 0<Cm ∧
    ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i})
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (b:CubeCoordinates ι) (C D extra₁ extra₂:Finset ι)
      (f:Ideal O) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
      (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
      (test₁ test₂:Finset ι→ℂ) (W:𝓢(ℝ,ℂ))
      (E G₁ G₂ Z M r ell V B j:ℝ) (delta:Finset ι→ℝ),
      b.Admissible → Disjoint C b.support →
      D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit →
      f≠0 → 0≤ E → 0≤ G₁ → 0≤ G₂ → 1≤ Z → 0≤ M → M≤ Mmax →
      0≤ ell → 0≤ V → -eta≤ r → r+3*ell+V≤ Fmax →
      primeProductNorm p C≤ Z^(r+eta) →
      primeProductNorm p extra₁≤ E → primeProductNorm p extra₂≤ E →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀U,‖test₁ U‖≤ G₁) → (∀U,‖test₂ U‖≤ G₂) →
      (∀U,test₁ U≠0→primeProductNorm p U≤ Z^(r+eta)) →
      (∀U,test₂ U≠0→primeProductNorm p U≤ Z^(r+eta)) →
      ‖ringComplex (primeProduct p b.support b.leftExponent)‖^2≤ Z^(ell+eta) →
      ‖ringComplex (primeProduct p b.support b.rightExponent)‖^2≤ Z^(ell+eta) →
      (Ideal.absNorm f:ℝ)≤ Z^(V+eta) → primeProductNorm p D≤ Z^(delta D+eta) →
      Z^(B-eta)≤ primeProductNorm p C →
      Z^(j-eta)≤‖ringComplex (jLabel p b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2 →
      ‖firstLocalPhysicalTail p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂
        (cubicIdealGenerator f)
        (fun U=>primeMark slots lists a (extra₁∪U)*test₁ U)
        (fun U=>primeMark slots lists a (extra₂∪U)*test₂ U) W (Z^M)
        (fun D=>childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent
          b.rightExponent b.leftBit b.rightBit f)
          (Z^(firstPhysicalHeight M r ell V (delta D) B j+12*eta+tau))) D‖≤
      (4*(1+diagonalControl sieveCutoff)^2)*(Cm*(E*Z^(r+eta))^ε*G₁)*(Cm*(E*Z^(r+eta))^ε*G₂)*
        (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*Z^(-saving) := by
  have hdc := diagonalControl_nonneg sieveCutoff
  obtain ⟨order,horder⟩:=choose_actual_first_tail_order Mmax Fmax eta tau saving hMm hFm heta htau
  obtain ⟨s,Ct,Cm,hCt,hCm,htail⟩:=first_whole_cube_canonical_tail ε hε order
  refine ⟨s,Ct,Cm,hCt,hCm,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hc pool b C D extra₁ extra₂ f Ψ₁ Ψ₂ m₁ m₂ slots lists a
    test₁ test₂ W E G₁ G₂ Z M r ell V B j delta hb hCB hD hf hE hG₁ hG₂ hZ hM hMmax
    hell hV hr hwhole hC he₁ he₂ hΨ₁ hΨ₂ hslots ha ht₁ ht₂ hs₁ hs₂ hb₁ hb₂ hF hdelta hBlo hj
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hlocal:=htail p hp hinj hcop hg hc pool b hb C D hCB f hf Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m₁ m₂ extra₁ extra₂ E slots lists a hE he₁ he₂ hslots ha test₁ test₂ W G₁ G₂ Z M r ell V
    (delta D) B j eta tau hG₁ hG₂ hz ht₁ ht₂ hs₁ hs₂ hb₁ hb₂ hF hdelta hBlo hj
  dsimp only at hlocal
  apply hlocal.trans
  exact horder p hp b C D hCB hD Z M r ell V
    (Cm*(E*Z^(r+eta))^ε*G₁) (Cm*(E*Z^(r+eta))^ε*G₂)
    (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
    hZ hM hMmax hell hV hr hwhole (by positivity) (by positivity) (by positivity) hb₁ hb₂ hC

end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

def firstExactPhysicalCutoff {ι:Type*} [DecidableEq ι] (p:ι→O)
    (b:CubeCoordinates ι) (C:Finset ι) (I:Ideal O) (Z M r ell V eta tau:ℝ) (D:Finset ι):Finset O :=
  childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit I)
    (Z^(firstPhysicalHeight M r ell V (Real.logb Z (primeProductNorm p D))
      (Real.logb Z (primeProductNorm p C))
      (Real.logb Z (‖ringComplex (jLabel p b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2))+12*eta+tau))

theorem full_first_whole_marked_rapid_tail (Mmax Fmax eta tau saving:ℝ)
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
      1<Z → 0≤ M → M≤ Mmax → 0≤ ell → 0≤ V → -eta≤ r → r+3*ell+V≤ Fmax →
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
          (firstExactPhysicalCutoff p b C I Z M r ell V eta tau)‖≤
      Ctail*Γ*G₁*G₂*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*Z^(-saving) := by
  have hdc := diagonalControl_nonneg sieveCutoff
  let saving':=saving+4*Fmax+14*eta
  obtain ⟨s,Ct,Cm,hCt,hCm,hloc⟩:=first_whole_cube_rapid_physical_tail 1 (by norm_num)
    Mmax Fmax eta tau saving' hMm hFm heta htau
  obtain ⟨Ca,hCa,hagg⟩:=full_first_tail_from_local 1 (by norm_num)
  refine ⟨s,Ca*(4*(1+diagonalControl sieveCutoff)^2)*Cm^2*Ct,by positivity,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ slots lists weights extra₁ extra₂
    test₁ test₂ W Z M r ell V Γ G₁ G₂ hZ hM hMmax hell hV hr hwhole hΓ hG₁ hG₂ hΨ₁ hΨ₂
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
        (firstExactPhysicalCutoff p b C I Z M r ell V eta tau) D‖≤ E:=by
    have hCB:Disjoint C b.support:=Finset.disjoint_left.mpr (fun i hi hib=>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hC).1) hi)).2 hib)
    have hupper (x:ℝ) (hx:0<x):x≤ Z^(Real.logb Z x+eta):=by
      conv_lhs=>rw [←Real.rpow_logb hz (ne_of_gt hZ) hx]
      exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    have hlower (x:ℝ) (hx:0<x):Z^(Real.logb Z x-eta)≤ x:=by
      conv_rhs=>rw [←Real.rpow_logb hz (ne_of_gt hZ) hx]
      exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    have hjpos:0<‖ringComplex (jLabel p b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2:=
      SecondPassIntegration.elementNorm_pos _ (primeProduct_ne_zero p hp _ _)
    have he:=hloc p hp hinj hcop hg hc pool b C D (extra₁ b) (extra₂ b) I Ψ₁ Ψ₂ m₁ m₂
      slots lists weights (test₁ b) (test₂ b) W (B^2) G₁ G₂ Z M r ell V
      (Real.logb Z (primeProductNorm p C))
      (Real.logb Z (‖ringComplex (jLabel p b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2))
      (fun D=>Real.logb Z (primeProductNorm p D))
      (hadm b hb) hCB (Finset.mem_powerset.mp hD) (hI0 I hI) (sq_nonneg _) hG₁ hG₂ hZ.le hM hMmax
      hell hV hr hwhole (Finset.mem_filter.mp hC).2 (hextra extra₁ he₁ b hb) (hextra extra₂ he₂ b hb)
      hΨ₁ hΨ₂ hslots hw (ht₁ b hb) (ht₂ b hb) (hs₁ b hb) (hs₂ b hb) (hb₁ b hb) (hb₂ b hb) (hIF I hI)
      (hupper _ (primeProductNorm_pos p hp D)) (hlower _ (primeProductNorm_pos p hp C)) (hlower _ hjpos)
    simpa only [firstLocalPhysicalTail,firstExactPhysicalCutoff,Real.rpow_one,E,L] using he
  have he:=hagg p hp hinj hcop hg hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂
    (fun b U=>primeMark slots lists weights (extra₁ b∪U)*test₁ b U)
    (fun b U=>primeMark slots lists weights (extra₂ b∪U)*test₂ b U) W (Z^M) B L (Z^(V+eta)) Γ E
    (fun b C I=>firstExactPhysicalCutoff p b C I Z M r ell V eta tau)
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

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open JointLogSeparation MeasureTheory
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
open InverseMomentFirstProfileUniform InverseAmbientProfileTower
theorem actual_first_moving_family_two_energies_uniform
    (U₀ : Fin 9 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 9 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J : ℕ) :
    ∃ Cprofile : ℝ,0 ≤ Cprofile ∧ ∀ {ι κ : Type*} [DecidableEq ι] (p : ι → Eis) (_hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (source : Finset κ) (F : Finset ι) (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (omega₁ omega₂ : ℝ → ℂ) (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
    (A₁ A₂ C R : κ → ℝ) (K L : ℝ) (_hK : 0 < K) (d h : κ → Eis) (s : Fin 9 → ℝ)
    (_hpos : ∀ x∈source,0 < A₁ x ∧ 0 < A₂ x ∧ 0 < C x ∧ 0 < R x ∧ d x ≠ 0 ∧ h x ≠ 0)
    (_hs : ∀ i,0 < s i)
    (_hρ : ∀ i,|ρ i| ≤ B₀ i) (_hc₁ : 1 ≤ c₁) (_hc₂ : 1 ≤ c₂)
    (_hc₁b : c₁ ≤ bcap) (_hc₂b : c₂ ≤ bcap) (_hL : 0 ≤ L)
    (_homega₁ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      (positiveSource g₁ c₁ θ₁) (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      omega₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (_homega₂ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      (positiveSource g₂ c₂ θ₂) (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      omega₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (_hcut : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      omega₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → omega₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,U₀ i ((firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j) s i)+ρ i) = 1)
    (B₁ B₂ : ℝ) (_hB₁ : 0 ≤ B₁) (_hB₂ : 0 ≤ B₂)
    (_hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₁ w true omega₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) h ≤
        B₁*(tripleHeight J z.1*coordinateHeight J z.2))
    (_hright : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₂ w false omega₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) h ≤
        B₂*(tripleHeight J z.1*coordinateHeight J z.2)),
    ‖firstFamilyPhysicalRows p hg source F selector C₁ C₂ w (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂) Φ A₁ A₂ C R K d h s‖ ≤
      (Real.exp ((9/2:ℝ)*L)/firstRootScale s)*
        ((Real.sqrt B₁*Real.sqrt B₂)*(Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
          (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker)) := by
  obtain ⟨Cprofile,hCprofile,hmeasure⟩ := InverseMomentFirstProfileUniform.first_profile_common_measure
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  refine ⟨Cprofile,hCprofile,?_⟩
  intro ι κ _ p hp _ hg source F selector C₁ C₂ w omega₁ omega₂ ρ c₁ c₂ θ₁ θ₂
    A₁ A₂ C R K L hK d h s hpos hs hρ hc₁ hc₂ hc₁b hc₂b hL
    homega₁ homega₂ hcut B₁ B₂ hB₁ hB₂ hleft hright
  have hRad : 0 < K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8) := by
    exact div_pos (mul_pos hK (hs 6))
      (mul_pos (mul_pos (mul_pos (mul_pos (hs 3) (hs 4)) (sq_pos_of_pos (hs 5))) (hs 7)) (hs 8))
  obtain ⟨b₃,hb₃⟩ := hmeasure (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) hRad
  obtain ⟨hsep,hWeighted,hMoment⟩ := hb₃ ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  let g := fun i => rooted (U₀ i) (M₀ i) (InverseClippingProfiles.firstBalancedSlope i) (hU i)
  let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) hg₁
  let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) hg₂
  let den := density g f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L
  have hden : Integrable den := first_balanced_density_integrable g f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L
  have he := actual_first_family_two_energies p hg hp source F selector C₁ C₂ w
    (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂) omega₁ omega₂ Φ (fun i y => U₀ i (y+ρ i))
    A₁ A₂ C R K L d h s hpos hs den hden hsep homega₁ homega₂ hcut
    J B₁ B₂ hB₁ hB₂ hWeighted hleft hright
  have hd : (∫ z : Frequency × (Fin 9 → ℝ),tripleHeight J z.1*coordinateHeight J z.2*‖den z‖) ≤
      Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
        (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
        (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker := by
    apply (le_div_iff₀ (pow_pos (by linarith : 0 < 1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) Aker)).mpr
    exact (mul_comm _ _).le.trans hMoment
  exact he.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
    (by have := firstRootScale_pos s hs; positivity))

theorem first_global_retained_push_uniform (ε:ℝ)(hε:0<ε):
    ∃ K:ℝ,0<K ∧ ∀ {ι κ:Type*} [DecidableEq ι] [DecidableEq κ] (p:ι→Eis)(hp:∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i})
    (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (_hpr:∀i,lambda^2∣p i-1)
    (F:Finset ι)(outer:Finset κ)(cube:κ→CubeCoordinates ι)(common:κ→Finset ι)
    (Ψ₁ Ψ₂:Eis→*ℂ)(m₁ m₂:Eis)(d:κ→Eis)
    (labels:κ→Finset (Ideal Eis))(a:κ→Ideal Eis×Eis→ℂ)(Γ Y:ℝ),
    (∀u,‖Ψ₁ u‖≤1)→(∀u,‖Ψ₂ u‖≤1)→0≤Γ→0<Y→
    (∀k∈outer,∀f∈labels k,Squarefree f)→(∀k∈outer,∀f∈labels k,f≠0)→
    (∀k∈outer,∀x∈firstRetainedSource p (labels k) (cube k) Y,‖a k x‖≤Γ)→
    ∀(negative:Bool)(H selector:κ→Finset ι→ℂ)(omega:ℝ→ℂ)(X t:ℝ),0<X→
    firstFamilyEnergy p hg (firstGlobalRetainedSource p outer labels cube Y) F
      (fun x=>selector x.1)
      (fun x=>firstCanonicalCoefficient p hg (cube x.1) (common x.1) negative
        (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂) (d x.1) (H x.1) x.2)
      (fun x=>retainedCubeWeight p hp hg (cube x.1) (common x.1) Ψ₁ Ψ₂ m₁ m₂
        (d x.1) (a x.1) x.2)
      negative omega X t (fun x=>x.2.2) ≤
    Γ*K*Y^ε*∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj F (cube k) (common k)
      negative (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂) (d k)
      (H k) (selector k) omega X t Y := by
  obtain ⟨K,hK,hpush⟩:=first_retained_actual_second_energy ε hε
  refine ⟨K,hK,?_⟩
  intro ι κ _ _ p hp _ hinj hcop hg hc hpr F outer cube common Ψ₁ Ψ₂ m₁ m₂ d labels a Γ Y
    hΨ₁ hΨ₂ hΓ hY hs hn ha negative H selector omega X t hX
  simp only [firstFamilyEnergy,firstGlobalRetainedSource,Finset.sum_sigma]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  exact hpush p hp hinj hcop hg hc hpr F (cube k) (common k) Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂
    (d k) (labels k) (a k) Γ Y hΓ hY (hs k hk) (hn k hk) (ha k hk)
    negative (H k) (selector k) omega X t hX

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels RayFourExpansion
open JointLogSeparation MeasureTheory
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
open InverseMomentFirstProfileUniform InverseAmbientProfileTower
theorem actual_first_original_subset_two_energies (ε : ℝ) (hε : 0<ε)
    (U₀ : Fin 9 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 9 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J : ℕ) :
    ∃ Cprofile Kpush : ℝ,0 ≤ Cprofile ∧ 0<Kpush ∧ ∀ {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (_hc : ∀ i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (_hpr : ∀ i,lambda^2∣p i-1)
    (F : Finset ι) (outer:Finset κ) (b : κ→SecondPassArithmetic.CubeCoordinates ι) (common : κ→Finset ι)
    (Ψ₁ Ψ₂ : Eis→*ℂ) (mleft mright : Eis) (dd:κ→Eis) (H₁ H₂ selector : κ→Finset ι→ℂ)
    (labels : κ→Finset (Ideal Eis)) (a : κ→Ideal Eis×Eis→ℂ) (Γ Y : ℝ)
    (_hΨ₁ : ∀ u,‖Ψ₁ u‖≤1) (_hΨ₂ : ∀ u,‖Ψ₂ u‖≤1)
    (_hΓ : 0≤Γ) (_hY : 0<Y)
    (_hlabels : ∀k∈outer,∀ f∈labels k,Squarefree f) (_hn : ∀k∈outer,∀ f∈labels k,f≠0)
    (_ha : ∀k∈outer,∀ x∈firstRetainedSource p (labels k) (b k) Y,‖a k x‖≤Γ)
    (omega₁ omega₂ : ℝ → ℂ) (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
    (A₁ A₂ C R : (Σ _ : κ,Ideal Eis×Eis) → ℝ) (K L : ℝ) (_hK : 0<K) (s : Fin 9→ℝ)
    (_hs : ∀ i,0<s i)
    (selected : Finset (Σ _ : κ,Ideal Eis×Eis))
    (_hselected : selected⊆firstGlobalRetainedSource p outer labels b Y),
    let source := selected
    let C₁ := fun x : (Σ _ : κ,Ideal Eis×Eis) => firstCanonicalCoefficient p hg (b x.1) (common x.1) true Ψ₁ mleft (dd x.1) (H₁ x.1) x.2
    let C₂ := fun x : (Σ _ : κ,Ideal Eis×Eis) => firstCanonicalCoefficient p hg (b x.1) (common x.1) false Ψ₂ mright (dd x.1) (H₂ x.1) x.2
    let w := fun x : (Σ _ : κ,Ideal Eis×Eis) => retainedCubeWeight p hp hg (b x.1) (common x.1) Ψ₁ Ψ₂ mleft mright (dd x.1) (a x.1) x.2
    ∀ (_hpos : ∀ x∈source,0<A₁ x ∧ 0<A₂ x ∧ 0<C x ∧ 0<R x ∧ dd x.1≠0 ∧ x.2.2≠0)
    (_hρ : ∀ i,|ρ i| ≤ B₀ i) (_hc₁ : 1 ≤ c₁) (_hc₂ : 1 ≤ c₂)
    (_hc₁b : c₁ ≤ bcap) (_hc₂b : c₂ ≤ bcap) (_hL : 0 ≤ L)
    (_homega₁ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x.1 j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j ≠ 0 →
      (positiveSource g₁ c₁ θ₁) (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      omega₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (_homega₂ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x.1 j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j ≠ 0 →
      (positiveSource g₂ c₂ θ₂) (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      omega₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (_hcut : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x.1 j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j ≠ 0 →
      omega₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → omega₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,U₀ i ((firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (dd x.1) x.2.2 j) s i)+ρ i) = 1)
    (B₁ B₂ : ℝ) (_hB₁ : 0 ≤ B₁) (_hB₂ : 0 ≤ B₂)
    (_hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      (∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj F (b k) (common k) true Ψ₁ mleft (dd k) (H₁ k) (selector k) omega₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) Y) ≤
        B₁*(tripleHeight J z.1*coordinateHeight J z.2))
    (_hright : ∀ z : Frequency × (Fin 9 → ℝ),
      (∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj F (b k) (common k) false Ψ₂ mright (dd k) (H₂ k) (selector k) omega₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) Y) ≤
        B₂*(tripleHeight J z.1*coordinateHeight J z.2)),
    ‖firstFamilyPhysicalRows p hg source F (fun x=>selector x.1) C₁ C₂ w (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂) Φ A₁ A₂ C R K (fun x=>dd x.1) (fun x=>x.2.2) s‖ ≤
      (Real.exp ((9/2:ℝ)*L)/firstRootScale s)*
        ((Γ*Kpush*Y^ε*(Real.sqrt B₁*Real.sqrt B₂))*(Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
          (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker)) := by
  obtain ⟨Cprofile,hCprofile,hprofile⟩ := actual_first_moving_family_two_energies_uniform
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  obtain ⟨Kpush,hKpush,hpush⟩ := first_global_retained_push_uniform ε hε
  refine ⟨Cprofile,Kpush,hCprofile,hKpush,?_⟩
  intro ι κ _ _ p hp _ hg hinj hcop hc hpr F outer b common Ψ₁ Ψ₂ mleft mright dd H₁ H₂ selector labels a Γ Y
    hΨ₁ hΨ₂ hΓ hY hlabels hn ha omega₁ omega₂ ρ c₁ c₂ θ₁ θ₂ A₁ A₂ C R K L hK s hs selected hselected
    source C₁ C₂ w hpos hρ hc₁ hc₂ hc₁b hc₂b hL homega₁ homega₂ hcut B₁ B₂ hB₁ hB₂ hleft hright
  have hweight : 0≤Γ*Kpush*Y^ε := by positivity
  have hroot:Real.sqrt (Γ*Kpush*Y^ε*B₁)*Real.sqrt (Γ*Kpush*Y^ε*B₂)=Γ*Kpush*Y^ε*(Real.sqrt B₁*Real.sqrt B₂):=by
    rw [Real.sqrt_mul hweight,Real.sqrt_mul hweight]
    calc
      _=(Real.sqrt (Γ*Kpush*Y^ε))^2*(Real.sqrt B₁*Real.sqrt B₂):=by ring
      _= _:=by rw [Real.sq_sqrt hweight]
  rw [←hroot]
  apply hprofile p hp hg source F (fun x=>selector x.1) C₁ C₂ w omega₁ omega₂ ρ c₁ c₂ θ₁ θ₂
    A₁ A₂ C R K L hK (fun x=>dd x.1) (fun x=>x.2.2) s hpos hs hρ hc₁ hc₂ hc₁b hc₂b hL
    homega₁ homega₂ hcut (Γ*Kpush*Y^ε*B₁) (Γ*Kpush*Y^ε*B₂) (mul_nonneg hweight hB₁) (mul_nonneg hweight hB₂)
  · intro z
    have he := hpush p hp hinj hcop hg hc hpr F outer b common Ψ₁ Ψ₂ mleft mright dd
      labels a Γ Y hΨ₁ hΨ₂ hΓ hY hlabels hn ha true H₁ selector omega₁ (s 7)
      (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) (hs 7)
    simp only [ite_true,] at he
    have hm1 : firstFamilyEnergy p hg source F (fun x=>selector x.1) C₁ w true omega₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) (fun x=>x.2.2) ≤
        firstFamilyEnergy p hg (firstGlobalRetainedSource p outer labels b Y) F
        (fun x=>selector x.1) C₁ w true omega₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) (fun x=>x.2.2) := by
      unfold firstFamilyEnergy
      exact Finset.sum_le_sum_of_subset_of_nonneg hselected (fun x hx hn=>
        mul_nonneg (norm_nonneg _) (firstBlockEnergy_nonneg p hg _ _ _ _ _ _ _ _))
    apply (hm1.trans he).trans
    simpa only [mul_assoc,ite_true,ite_false,Bool.false_eq_true] using mul_le_mul_of_nonneg_left (hleft z) hweight
  · intro z
    have he := hpush p hp hinj hcop hg hc hpr F outer b common Ψ₁ Ψ₂ mleft mright dd
      labels a Γ Y hΨ₁ hΨ₂ hΓ hY hlabels hn ha false H₂ selector omega₂ (s 8)
      (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) (hs 8)
    simp only [ite_false,Bool.false_eq_true] at he
    have hm2 : firstFamilyEnergy p hg source F (fun x=>selector x.1) C₂ w false omega₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) (fun x=>x.2.2) ≤
        firstFamilyEnergy p hg (firstGlobalRetainedSource p outer labels b Y) F
        (fun x=>selector x.1) C₂ w false omega₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) (fun x=>x.2.2) := by
      unfold firstFamilyEnergy
      exact Finset.sum_le_sum_of_subset_of_nonneg hselected (fun x hx hn=>
        mul_nonneg (norm_nonneg _) (firstBlockEnergy_nonneg p hg _ _ _ _ _ _ _ _))
    apply (hm2.trans he).trans
    simpa only [mul_assoc,ite_true,ite_false,Bool.false_eq_true] using mul_le_mul_of_nonneg_left (hright z) hweight

end
end InverseMoment

noncomputable section
namespace InverseMoment
open JointLogSeparation InverseAmbientProfileTower

theorem first_left_height_budget (J:ℕ)(p:Ambient (Fin 9)):
    (1+‖profileHeight firstLeftSlope firstRightSlope firstKernelSlope p.1 p.2 7‖)^J≤
      tripleHeight J p.1*coordinateHeight J p.2:=by
  have h:=pow_le_pow_left₀ (by positivity : 0≤1+‖inheritedLeft 7 p‖) (inheritedLeft_bound 7 p) J
  rw [←ambientWeight_eq_pow] at h
  simpa only [first_inherited_left_eq,ambientWeight,tripleHeight,coordinateHeight] using h

theorem first_right_height_budget (J:ℕ)(p:Ambient (Fin 9)):
    (1+‖profileHeight firstLeftSlope firstRightSlope firstKernelSlope p.1 p.2 8‖)^J≤
      tripleHeight J p.1*coordinateHeight J p.2:=by
  have h:=pow_le_pow_left₀ (by positivity : 0≤1+‖inheritedRight 8 p‖) (inheritedRight_bound 8 p) J
  rw [←ambientWeight_eq_pow] at h
  simpa only [first_inherited_right_eq,norm_neg,ambientWeight,tripleHeight,coordinateHeight] using h

theorem first_unequal_prefactor (Z:ℝ)(hZ:0<Z)
    (M r ell V delta A₁ A₂ B R t h eta:ℝ):
    (Z^(-r-2*ell-V)*Z^M/firstRootScale
      (fun i=>Z^(![A₁,A₂,B,delta,R,t,h,r-A₁-B-t,r-A₂-B-t] i)))*
      Real.exp ((9/2:ℝ)*(eta*Real.log Z))*
      (Real.sqrt ((Z^(firstKappa M r ell V delta A₁ B R)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))⁻¹)*
       Real.sqrt ((Z^(firstKappa M r ell V delta A₂ B R)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))⁻¹))=1:=by
  rw [first_physical_scalar Z hZ]
  have he:Real.exp ((9/2:ℝ)*(eta*Real.log Z))=Z^((9/2:ℝ)*eta):=by
    rw [Real.rpow_def_of_pos hZ];congr 1;ring
  rw [he,←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  rw [←Real.rpow_neg hZ.le,←Real.rpow_neg hZ.le,Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,
    ←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  convert Real.rpow_zero Z using 1
  congr 1
  ring
end InverseMoment

end

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels RayFourExpansion
open JointLogSeparation MeasureTheory
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
open InverseMomentFirstProfileUniform InverseAmbientProfileTower
theorem actual_first_original_subset_physical_budget (ε : ℝ) (hε : 0<ε)
    (U₀ : Fin 9 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 9 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J : ℕ) :
    ∃ Cprofile Kpush : ℝ,0 ≤ Cprofile ∧ 0<Kpush ∧ ∀ {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (_hc : ∀ i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (_hpr : ∀ i,lambda^2∣p i-1)
    (F : Finset ι) (outer:Finset κ) (b : κ→SecondPassArithmetic.CubeCoordinates ι) (common : κ→Finset ι)
    (Ψ₁ Ψ₂ : Eis→*ℂ) (mleft mright : Eis) (dd:κ→Eis) (H₁ H₂ selector : κ→Finset ι→ℂ)
    (labels : κ→Finset (Ideal Eis)) (a : κ→Ideal Eis×Eis→ℂ) (Γ Y : ℝ)
    (_hΨ₁ : ∀ u,‖Ψ₁ u‖≤1) (_hΨ₂ : ∀ u,‖Ψ₂ u‖≤1)
    (_hΓ : 0≤Γ) (_hY : 0<Y)
    (_hlabels : ∀k∈outer,∀ f∈labels k,Squarefree f) (_hn : ∀k∈outer,∀ f∈labels k,f≠0)
    (_ha : ∀k∈outer,∀ x∈firstRetainedSource p (labels k) (b k) Y,‖a k x‖≤Γ)
    (omega₁ omega₂ : ℝ → ℂ) (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
    (A₁ A₂ C R : (Σ _ : κ,Ideal Eis×Eis) → ℝ) (K L : ℝ) (_hK : 0<K) (s : Fin 9→ℝ)
    (_hs : ∀ i,0<s i)
    (selected : Finset (Σ _ : κ,Ideal Eis×Eis))
    (_hselected : selected⊆firstGlobalRetainedSource p outer labels b Y),
    let source := selected
    let C₁ := fun x : (Σ _ : κ,Ideal Eis×Eis) => firstCanonicalCoefficient p hg (b x.1) (common x.1) true Ψ₁ mleft (dd x.1) (H₁ x.1) x.2
    let C₂ := fun x : (Σ _ : κ,Ideal Eis×Eis) => firstCanonicalCoefficient p hg (b x.1) (common x.1) false Ψ₂ mright (dd x.1) (H₂ x.1) x.2
    let w := fun x : (Σ _ : κ,Ideal Eis×Eis) => retainedCubeWeight p hp hg (b x.1) (common x.1) Ψ₁ Ψ₂ mleft mright (dd x.1) (a x.1) x.2
    ∀ (_hpos : ∀ x∈source,0<A₁ x ∧ 0<A₂ x ∧ 0<C x ∧ 0<R x ∧ dd x.1≠0 ∧ x.2.2≠0)
    (_hρ : ∀ i,|ρ i| ≤ B₀ i) (_hc₁ : 1 ≤ c₁) (_hc₂ : 1 ≤ c₂)
    (_hc₁b : c₁ ≤ bcap) (_hc₂b : c₂ ≤ bcap) (_hL : 0 ≤ L)
    (_homega₁ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x.1 j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j ≠ 0 →
      (positiveSource g₁ c₁ θ₁) (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      omega₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (_homega₂ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x.1 j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j ≠ 0 →
      (positiveSource g₂ c₂ θ₂) (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      omega₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (_hcut : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x.1 j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j ≠ 0 →
      omega₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → omega₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,U₀ i ((firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (dd x.1) x.2.2 j) s i)+ρ i) = 1)
    (Benergy : ℝ) (_hBenergy : 0 ≤ Benergy)
    (Z M r ell V delta aa₁ aa₂ bb rr tq hh eta:ℝ) (_hZ:0<Z)
    (_hscale:s=fun i=>Z^(![aa₁,aa₂,bb,delta,rr,tq,hh,r-aa₁-bb-tq,r-aa₂-bb-tq] i))
    (_hLe:L=eta*Real.log Z)
    (_hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      (Z^(firstKappa M r ell V delta aa₁ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      (∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj F (b k) (common k) true Ψ₁ mleft (dd k) (H₁ k) (selector k) omega₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) Y) ≤
        Benergy*(tripleHeight J z.1*coordinateHeight J z.2))
    (_hright : ∀ z : Frequency × (Fin 9 → ℝ),
      (Z^(firstKappa M r ell V delta aa₂ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      (∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj F (b k) (common k) false Ψ₂ mright (dd k) (H₂ k) (selector k) omega₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) Y) ≤
        Benergy*(tripleHeight J z.1*coordinateHeight J z.2)),
    (Z^(-r-2*ell-V)*Z^M)*‖firstFamilyPhysicalRows p hg source F (fun x=>selector x.1) C₁ C₂ w (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂) Φ A₁ A₂ C R K (fun x=>dd x.1) (fun x=>x.2.2) s‖ ≤
      ((Γ*Kpush*Y^ε*Benergy)*(Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
          (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker)) := by
  obtain ⟨Cprofile,Kpush,hCprofile,hKpush,he⟩:=actual_first_original_subset_two_energies ε hε
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  refine ⟨Cprofile,Kpush,hCprofile,hKpush,?_⟩
  intro ι κ _ _ p hp _ hg hinj hcop hc hpr F outer b common Ψ₁ Ψ₂ mleft mright dd H₁ H₂ selector labels a Γ Y
    hΨ₁ hΨ₂ hΓ hY hlabels hn ha omega₁ omega₂ ρ c₁ c₂ θ₁ θ₂ A₁ A₂ C R K L hK s hs selected hselected
    source C₁ C₂ w hpos hρ hc₁ hc₂ hc₁b hc₂b hL homega₁ homega₂ hcut Benergy hBenergy
    Z M r ell V delta aa₁ aa₂ bb rr tq hh eta hZ hscale hLe hleft hright
  let P₁:=Z^(firstKappa M r ell V delta aa₁ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let P₂:=Z^(firstKappa M r ell V delta aa₂ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  have hp₁:0<P₁:=by dsimp [P₁];positivity
  have hp₂:0<P₂:=by dsimp [P₂];positivity
  have hb:=he p hp hg hinj hcop hc hpr F outer b common Ψ₁ Ψ₂ mleft mright dd H₁ H₂ selector labels a Γ Y
    hΨ₁ hΨ₂ hΓ hY hlabels hn ha omega₁ omega₂ ρ c₁ c₂ θ₁ θ₂ A₁ A₂ C R K L hK s hs selected hselected
    hpos hρ hc₁ hc₂ hc₁b hc₂b hL homega₁ homega₂ hcut (Benergy/P₁) (Benergy/P₂) (by positivity) (by positivity)
    (by intro z;rw [div_mul_eq_mul_div];apply (le_div_iff₀ hp₁).mpr;simpa only [P₁,mul_assoc,mul_comm,mul_left_comm] using hleft z)
    (by intro z;rw [div_mul_eq_mul_div];apply (le_div_iff₀ hp₂).mpr;simpa only [P₂,mul_assoc,mul_comm,mul_left_comm] using hright z)
  have hroot:Real.sqrt (Benergy/P₁)*Real.sqrt (Benergy/P₂)=Benergy*(Real.sqrt P₁⁻¹*Real.sqrt P₂⁻¹):=by
    simp only [div_eq_mul_inv,Real.sqrt_mul hBenergy]
    calc
      _=(Real.sqrt Benergy)^2*(Real.sqrt P₁⁻¹*Real.sqrt P₂⁻¹):=by ring
      _= _:=by rw [Real.sq_sqrt hBenergy]
  rw [hroot] at hb
  have hcancel:(Z^(-r-2*ell-V)*Z^M/firstRootScale s)*Real.exp ((9/2:ℝ)*L)*
      (Real.sqrt P₁⁻¹*Real.sqrt P₂⁻¹)=1:=by
    rw [hscale,hLe]
    exact first_unequal_prefactor Z hZ M r ell V delta aa₁ aa₂ bb rr tq hh eta
  have hnorm:0≤ Z^(-r-2*ell-V)*Z^M:=by positivity
  apply (mul_le_mul_of_nonneg_left hb hnorm).trans_eq
  calc
    _=((Z^(-r-2*ell-V)*Z^M/firstRootScale s)*Real.exp ((9/2:ℝ)*L)*
      (Real.sqrt P₁⁻¹*Real.sqrt P₂⁻¹))*
      ((Γ*Kpush*Y^ε*Benergy)*(Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
          (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker)):=by ring
    _= _:=by rw [hcancel,one_mul]
end
end InverseMoment

noncomputable section
namespace InverseMomentFirstOriginalProfile
open InverseMoment Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseMomentFirstProfileUniform
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
theorem original_cell_windows (g₁ g₂ : 𝓢(ℝ,ℂ)) (m₁ m₂ bcap : ℝ)
    (Bρ : Fin 9→ℝ)
    (hm₁ : 0≤ m₁) (hm₂ : 0≤ m₂)
    (hg₁ : Function.support g₁⊆Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂⊆Set.Icc (-m₂) m₂)
    (hBρ : ∀i,0≤ Bρ i) :
    ∃(w₁ w₂ : 𝓢(ℝ,ℂ))(U₀ : Fin 9→𝓢(ℝ,ℂ))(M₀ : Fin 9→ℝ)(a b : ℝ),
      0<a ∧ a≤ b ∧ HasCompactSupport (w₁ : ℝ→ℂ) ∧ HasCompactSupport (w₂ : ℝ→ℂ) ∧
      tsupport (w₁ : ℝ→ℂ)⊆Set.Icc a b ∧ tsupport (w₂ : ℝ→ℂ)⊆Set.Icc a b ∧
      (∀i,0≤ M₀ i) ∧ (∀i,HasCompactSupport (U₀ i : ℝ→ℂ)) ∧
      (∀i,Function.support (U₀ i)⊆Set.Icc (-M₀ i) (M₀ i)) ∧
      ∀{ι : Type*}[DecidableEq ι]
      (p : ι→O)(_hp : ∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O)) (Y : ℝ)
      (C₁ C₂ : OriginalIndex ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ) (T₁ T₂ : ℝ)
      (ρ : Fin 9→ℝ)(c₁ c₂ θ₁ θ₂ : ℝ),
      0<T₁ → 0<T₂ → (∀i,|ρ i|≤ Bρ i) →
      1≤ c₁ → c₁≤ bcap → 1≤ c₂ → c₂≤ bcap →
      let source := sourceCell (originalNorms p)
        (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) k
      let F := pool
      let selector : OriginalIndex ι→Finset ι→ℂ := fun _=>commonSelector p (fun _=>1) l
      let A₁ := leftNorm p
      let A₂ := rightNorm p
      let C := commonNorm p
      let R := activeNorm p
      let d := fun x : OriginalIndex ι=>divisorElement p x.1
      let h := fun x : OriginalIndex ι=>x.2.2
      let s := rawScales k l T₁ T₂
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
  obtain ⟨w₁,w₂,U,M,a,b,ha,hab,hwc₁,hwc₂,hws₁,hws₂,hM,hUc,hUs,he⟩ :=
    actual_first_child_windows g₁ g₂ m₁ m₂ bcap (fun _=>1) (fun _=>2) Bρ
      hm₁ hm₂ hg₁ hg₂ (by intro i;norm_num) (by intro i;norm_num) hBρ
  refine ⟨w₁,w₂,U,M,a,b,ha,hab,hwc₁,hwc₂,hws₁,hws₂,hM,hUc,hUs,?_⟩
  intro ι _ p hp _ hg pool Q labels Y C₁ C₂ k l T₁ T₂ ρ c₁ c₂ θ₁ θ₂
    hT₁ hT₂ hρ hc₁ hcb₁ hc₂ hcb₂ source F selector A₁ A₂ C R d h s
  apply he p hp hg source F selector C₁ C₂ A₁ A₂ C R d h s ρ c₁ c₂ θ₁ θ₂
    (rawScales_pos k l T₁ T₂ hT₁ hT₂) hρ hc₁ hcb₁ hc₂ hcb₂
  intro x hx j hj hn
  exact actual_original_cell_ratios p hp hg _ (fun _ _=>1) C₁ C₂
    (leftNorm p) (rightNorm p) (commonNorm p) (activeNorm p)
    (fun x=>divisorElement p x.1) (fun x=>x.2.2)
    (original_source_norms_ge_one p hp pool Q labels Y) k l T₁ T₂ x hx j hn

end InverseMomentFirstOriginalProfile
end

noncomputable section
namespace InverseMomentFirstOriginalProfile
open InverseMoment Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseMomentFirstProfileUniform
open InverseAmbientProfileTower JointLogSeparation
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]

def originalChildEnergy (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,lambda∉Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l : ℕ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (omega : ℝ→ℂ) (T t Y : ℝ) : ℝ :=
  ∑x∈originalOuterCell p pool Q k,
    firstCanonicalSecondEnergy p hp hg hinj pool x.1 x.2.1 negative Ψ m (divisorElement p x)
      (mark (if negative then x.1.rightExponent else x.1.leftExponent))
      (commonSelector p (fun _=>1) l) omega T t Y

def originalCellRows (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,lambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (k : SourceIndex) (l : ℕ) (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ) (s : Fin 9→ℝ) : ℂ :=
  firstFamilyPhysicalRows p hg
    (sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) k)
    pool (fun _=>commonSelector p (fun _=>1) l)
    (coefficient p hg Ψ m mark true) (coefficient p hg Ψ m mark false)
    (weight p hp hg β cutoff Ψ m) W₁ W₂ Φ
    (leftNorm p) (rightNorm p) (commonNorm p) (activeNorm p) K
    (fun x=>divisorElement p x.1) (fun x=>x.2.2) s

theorem original_cell_physical_budget (g₁ g₂ Φ : 𝓢(ℝ,ℂ)) (m₁ m₂ : ℝ)
    (hm₁ : 0≤ m₁) (hm₂ : 0≤ m₂)
    (hg₁ : Function.support g₁⊆Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂⊆Set.Icc (-m₂) m₂) :
    ∃(omega₁ omega₂ : 𝓢(ℝ,ℂ))(lo hi : ℝ),0<lo ∧ lo≤ hi ∧
      HasCompactSupport (omega₁ : ℝ→ℂ) ∧ HasCompactSupport (omega₂ : ℝ→ℂ) ∧
      tsupport (omega₁ : ℝ→ℂ)⊆Set.Icc lo hi ∧ tsupport (omega₂ : ℝ→ℂ)⊆Set.Icc lo hi ∧
    ∀(ε : ℝ),0<ε→∀(Aker J : ℕ),∃ Cprofile Kpush : ℝ,0≤ Cprofile ∧ 0<Kpush ∧
    ∀{ι : Type*}[DecidableEq ι](p : ι→O)(hp : ∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr : ∀i,lambda^2∣p i-1)
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
      (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
      (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (Γ Y : ℝ)
      (_hΨ : ∀u,‖Ψ u‖≤1) (_hΓ : 0≤Γ) (_hY : 0<Y)
      (_hsf : ∀I∈labels,Squarefree I) (_hn : ∀I∈labels,I≠0)
      (_hβ : ∀I∈labels,∀v∈Q,‖β I v‖≤Γ)
      (k : SourceIndex) (l : ℕ) (T₁ T₂ K theta L : ℝ)
      (_hT₁ : 0<T₁) (_hT₂ : 0<T₂) (_hK : 0<K) (_hL : 0≤ L)
      (Benergy Z M r ell V delta aa₁ aa₂ bb rr tq hh eta : ℝ)
      (_hB : 0≤ Benergy) (_hZ : 0<Z)
      (_hscale : rawScales k l T₁ T₂=fun i=>Z^(![aa₁,aa₂,bb,delta,rr,tq,hh,r-aa₁-bb-tq,r-aa₂-bb-tq] i))
      (_hLe : L=eta*Real.log Z)
      (_hleft : ∀z : Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V delta aa₁ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
          originalChildEnergy p hp hg hinj pool Q k l true Ψ m mark omega₁ T₁
            (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) Y≤
          Benergy*(tripleHeight J z.1*coordinateHeight J z.2))
      (_hright : ∀z : Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V delta aa₂ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
          originalChildEnergy p hp hg hinj pool Q k l false Ψ m mark omega₂ T₂
            (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) Y≤
          Benergy*(tripleHeight J z.1*coordinateHeight J z.2)),
      (Z^(-r-2*ell-V)*Z^M)*‖originalCellRows p hp hcop hg pool Q labels β cutoff Ψ m mark k l
        (positiveSource g₁ 1 (-theta)) (positiveSource g₂ 1 theta) Φ K Y (rawScales k l T₁ T₂)‖≤
        ((Γ^2*Kpush*Y^ε*Benergy)*(Cprofile*((1+‖-theta‖)^InverseClippingProfiles.momentOrder J*
          (1+‖theta‖)^InverseClippingProfiles.momentOrder J)/
          (1+K*(rawScales k l T₁ T₂) 6/((rawScales k l T₁ T₂) 3*(rawScales k l T₁ T₂) 4*
            ((rawScales k l T₁ T₂) 5)^2*T₁*T₂))^Aker)) := by
  obtain ⟨w₁,w₂,U,M₀,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,hM,hUc,hUs,hwin⟩ :=
    original_cell_windows g₁ g₂ m₁ m₂ 1 (fun _=>0) hm₁ hm₂ hg₁ hg₂ (fun _=>le_rfl)
  refine ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro ε hε Aker J
  obtain ⟨Cprofile,Kpush,hC,hKp,he⟩ := actual_first_original_subset_physical_budget
    ε hε U g₁ g₂ Φ M₀ (fun _=>0) m₁ m₂ 1
    hM (fun _=>le_rfl) hUs hg₁ hg₂ Aker J
  refine ⟨Cprofile,Kpush,hC,hKp,?_⟩
  intro ι _ p hp _ hg hinj hcop hc hpr pool Q labels β cutoff Ψ m mark Γ Y hΨ hΓ hY hsf hn hβ
    k l T₁ T₂ K theta L hT₁ hT₂ hK hL Benergy Z M r ell V delta aa₁ aa₂ bb rr tq hh eta hB hZ hscale hLe hleft hright
  let source := sourceCell (originalNorms p)
    (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) k
  have hgates := hwin p hp hg pool Q labels Y (coefficient p hg Ψ m mark true)
    (coefficient p hg Ψ m mark false) k l T₁ T₂ (fun _=>0) 1 1 (-theta) theta
    hT₁ hT₂ (by intro i;simp) le_rfl le_rfl le_rfl le_rfl
  have hb := he p hp hg hinj hcop hc hpr pool (originalOuterCell p pool Q k) (fun x=>x.1) (fun x=>x.2.1)
    Ψ Ψ m m (divisorElement p) (fun x=>mark x.1.rightExponent) (fun x=>mark x.1.leftExponent)
    (fun _=>commonSelector p (fun _=>1) l) (fun _=>labels) (firstOriginalWeight p β cutoff) (Γ^2) Y
    hΨ hΨ (sq_nonneg _) hY (fun _ _=>hsf) (fun _ _=>hn)
    (fun x hx=>original_weight_bound p pool Q labels β cutoff Γ Y hΓ hβ x (original_outer_cell_subset p pool Q k hx))
    w₁ w₂ (fun _=>0) 1 1 (-theta) theta (leftNorm p) (rightNorm p) (commonNorm p) (activeNorm p)
    K L hK (rawScales k l T₁ T₂) (rawScales_pos k l T₁ T₂ hT₁ hT₂)
    source (original_cell_subset p pool Q labels Y k)
    (fun x hx=>original_source_positive p hp pool Q labels Y x (Finset.mem_filter.mp hx).1)
    (by intro i;simp) le_rfl le_rfl le_rfl le_rfl hL hgates.1 hgates.2.1 hgates.2.2
    Benergy hB Z M r ell V delta aa₁ aa₂ bb rr tq hh eta hZ hscale hLe
    (by simpa [originalChildEnergy,rawScales] using hleft)
    (by simpa [originalChildEnergy,rawScales] using hright)
  unfold originalCellRows
  unfold InverseMomentFirstOriginalProfile.coefficient InverseMomentFirstOriginalProfile.weight
  simpa [source,rawScales] using hb

end InverseMomentFirstOriginalProfile
end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

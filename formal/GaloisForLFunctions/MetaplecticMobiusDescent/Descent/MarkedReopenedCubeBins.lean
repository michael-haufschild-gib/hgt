/-
Marked reopened cube bins adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.MarkedCompletedCubeSums
import GaloisForLFunctions.MetaplecticMobiusDescent.Inversion.WholePriorityRapidTail

/-!
# Marked reopened cube bins

Marked reopened cube bins, indexed ideal marks and outside canonical marked rows; zero and tail
aggregates of the global priority energy; separated canonical family energies.
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
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InverseSecondPrincipalCaller InversePrincipalEnergy InversePrioritySecondSource
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O"=>Eisenstein.O

variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

omit [DecidableEq σ] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem parent_residual_lists_subset {Jo:ℕ} (extra:CubeCoordinates ι→Finset ι)
    (negative:Bool) (lists:σ→Finset ι) (y:SecondParentSource ι Jo) (i:σ):
    residualLists p negative (fun i=>lists i\extra y.cube) y i⊆lists i:=
by
  intro k hk
  exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hk).1).1

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem parent_residual_lists_pairwise {Jo:ℕ} (extra:CubeCoordinates ι→Finset ι)
    (negative:Bool) (slots assigned:Finset σ) (lists:σ→Finset ι) (y:SecondParentSource ι Jo)
    (hslots:(slots:Set σ).PairwiseDisjoint lists):
    ((slots\assigned:Finset σ):Set σ).PairwiseDisjoint (residualLists p negative (fun i=>lists i\extra y.cube) y):=by
  intro i hi j hj hij
  exact (hslots (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hij).mono
    (parent_residual_lists_subset p extra negative lists y i)
    (parent_residual_lists_subset p extra negative lists y j)

theorem priority_zero_parent_uniform (ε:ℝ) (hε:0<ε):
    ∃(s:Finset (ℕ×ℕ))(C:ℝ),0<C ∧
    ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (_hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,lambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι) (negative:Bool)
      (Ψ:O→*ℂ) (m:O) (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) → (∀u,‖Ψ u‖≤1) →
    ∀(om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
      (X M Y t:ℝ)(R:Finset ι→Finset ι→ℝ),
      0<X → hi≤ Real.exp M → 1≤ Y → (∀G E,0≤ R G E) →
    ∀{Jo:ℕ}(y:SecondParentSource ι Jo),
      ‖priorityZeroParent p hg extra pool negative Ψ m slots assigned lists a
        (principalWindow om lo hi hlo hs negative t) X Y R y‖≤
      C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2*
        Y*(X*Real.exp M)^(1+ε):=by
  obtain ⟨s,C,hC,hbound⟩:=marked_principal_energy ε hε
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop extra pool negative Ψ m slots assigned lists a hslots ha hΨ
    om lo hi hlo hs X M Y t R hX hhi hY hR Jo y
  have hpair:=parent_residual_lists_pairwise p extra negative slots assigned lists y hslots
  have hcoeff:∀i∈slots\assigned,∀k∈residualLists p negative (fun i=>lists i\extra y.cube) y i,‖a i k‖≤1:=by
    intro i hi k hk
    exact ha i (Finset.mem_sdiff.mp hi).1 k (parent_residual_lists_subset p extra negative lists y i hk)
  have hz:∀G∈pool.powerset,∀E∈G.powerset,(0:O)∈secondVariableCutoff p y R G E:=by
    intro G hG E hE
    exact zero_mem_childFrequencyBall _
      (mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))) _ (hR G E)
  have hb:=hbound p hp hg hinj hcop (slots\assigned)
    (residualLists p negative (fun i=>lists i\extra y.cube) y) a hpair hcoeff ∅ pool Ψ hΨ
    (secondParentPuncture p m y) (secondParentLabel p y) (secondParentDivisor p y)
    (principalWindow om lo hi hlo hs negative t) rowMajorant X M Y hX hY
    (principalWindow_upper om lo hi hlo hs M hhi negative t) (secondVariableCutoff p y R) hz
    (fun _ _ _=>0) (by intros; simp)
  have hb':‖priorityZeroParent p hg extra pool negative Ψ m slots assigned lists a
      (principalWindow om lo hi hlo hs negative t) X Y R y‖≤_:=
    (le_add_of_nonneg_right (norm_nonneg _)).trans hb
  simpa only [Finset.card_empty,pow_zero,mul_one,principalWindow_seminorm_zero,mul_assoc] using hb'

theorem priority_tail_parent_uniform (Lcap tau saving:ℝ)(hLcap:0≤ Lcap)(htau:0<tau):
    ∃(s:Finset (ℕ×ℕ))(C:ℝ),0<C ∧
    ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,lambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι) (negative:Bool)
      (Ψ:O→*ℂ) (m:O) (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) → (∀u,‖Ψ u‖≤1) →
    ∀(om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
      (X M Y Z t:ℝ)(R:Finset ι→Finset ι→ℝ),
      0<X → hi≤ Real.exp M → 1≤ Z → 0<Y → 1≤ X*Real.exp M →
      Y≤ Z^Lcap → Y⁻¹≤ Z^Lcap → X*Real.exp M≤ Z^Lcap →
    ∀{Jo:ℕ}(y:SecondParentSource ι Jo),
      (∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p y) G E.val (X*Real.exp M) Y (Z^tau)≤ R G E.val) →
      ‖priorityTailParent p hg hp hinj extra pool negative Ψ m slots assigned lists a
        (principalWindow om lo hi hlo hs negative t) X Y R y‖≤
      C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving):=by
  obtain ⟨s,C,hC,hbound⟩:=InverseWholePriorityRapidTail.marked_rapid_tail Lcap tau saving hLcap htau
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc extra pool negative Ψ m slots assigned lists a hslots ha hΨ
    om lo hi hlo hs X M Y Z t R hX hhi hZ hY hscale hy hyi hx Jo y hR
  have hpair:=parent_residual_lists_pairwise p extra negative slots assigned lists y hslots
  have hcoeff:∀i∈slots\assigned,∀k∈residualLists p negative (fun i=>lists i\extra y.cube) y i,‖a i k‖≤1:=by
    intro i hi k hk
    exact ha i (Finset.mem_sdiff.mp hi).1 k (parent_residual_lists_subset p extra negative lists y i hk)
  exact hbound p hp hcop hg hinj hc pool Ψ hΨ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
    (slots\assigned) _ a hpair hcoeff om rowMajorant lo hi hlo hs negative t X M Y Z R
    hX hhi hZ hY hscale hy hyi hx hR

end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InverseSecondPrincipalCaller InversePrioritySecondSource InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O"=>Eisenstein.O
variable {ι σ:Type*}[DecidableEq ι][DecidableEq σ]{Jo:ℕ}
def globalPriorityZeroAggregate
    (p:ι→O)[∀i,(Ideal.span {p i}).IsMaximal](hg:∀i,lambda∉Ideal.span {p i})
    (extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (V:𝓢(ℝ,ℂ))(X Y:ℝ)(R:Finset ι→Finset ι→ℝ):ℝ:=
  firstCoreMassBound*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
    ∑x∈original,‖globalPriorityOuter p hg negative Ψ m ray core w x‖*
      ‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*
      ‖priorityZeroParent p hg extra pool negative
        (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots J lists a V X Y R (parent p x)‖

theorem global_priority_zero_aggregate (ε:ℝ)(hε:0<ε):
    ∃(s:Finset (ℕ×ℕ))(Czero:ℝ),0<Czero ∧
    ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,lambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      {Jo:ℕ}(extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)
      (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀k∈lists i,‖a i k‖≤1)→(∀u,‖Ψ u‖≤1)→
      (∀x∈original,‖w x‖≤1)→
    ∀(om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
      (X M Y t:ℝ)(R:Finset ι→Finset ι→ℝ),
      0<X→hi≤ Real.exp M→1≤ Y→(∀G E,0≤ R G E)→
      globalPriorityZeroAggregate p hg extra pool original w negative Ψ m slots lists a
        (principalWindow om lo hi hlo hs negative t) X Y R≤
      Czero*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
        (SchwartzMap.seminorm ℝ 0 0 om)^2*Y*(X*Real.exp M)^(1+ε)*
        ∑x∈original,(primeProductNorm p (wholeExtractedSupport (fun x=>extra x.cube) negative x))^(2*ε):=by
  obtain ⟨s,Cp,hCp,hprincipal⟩:=priority_zero_parent_uniform ε hε
  obtain ⟨Cb,hCb,hmass⟩:=global_priority_weighted_branch ε hε
  refine ⟨s,Cb*Cp,mul_pos hCb hCp,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop Jo extra pool original w negative Ψ m slots lists a
    hslots ha hΨ hw om lo hi hlo hs X M Y t R hX hhi hY hR
  let B:=Cp*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2*
    Y*(X*Real.exp M)^(1+ε)
  have hB:0≤ B:=by dsimp [B];positivity
  have hh:=hmass p hp hg hcop original extra negative Ψ m w slots lists a B hslots ha hΨ hw hB
    (fun ray core J x=>‖priorityZeroParent p hg extra pool negative
      (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots J lists a
      (principalWindow om lo hi hlo hs negative t) X Y R (parent p x)‖)
    (by intros;positivity)
    (fun ray core J hJ x hx=>hprincipal p hp hg hinj hcop extra pool negative
      (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots J lists a hslots ha
      (fun u=>(firstCoreTwist_norm_le negative _ Ψ core u).trans (hΨ u))
      om lo hi hlo hs X M Y t R hX hhi hY hR (parent p x))
  convert hh using 1 <;> dsimp only [globalPriorityZeroAggregate,B] ; ring
end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InverseSecondPrincipalCaller InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseMomentGlobalPrincipalMass
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O"=>Eisenstein.O

theorem global_priority_zero_physical (ε:ℝ)(hε:0<ε)(Jmax:ℕ)(dsmall:ℝ)(hdsmall:0<dsmall):
    ∃(s:Finset (ℕ×ℕ))(Czero:ℝ),0<Czero ∧
    ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,lambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (Jo:ℕ),Jo≤ Jmax→∀(extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)
      (original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)(negative:Bool)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀k∈lists i,‖a i k‖≤1)→(∀u,‖Ψ u‖≤1)→
      (∀x∈original,‖w x‖≤1)→
    ∀(om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
      (Z M r ell V delta A B Ractive j t eta tau window pi height:ℝ)(R:Finset ι→Finset ι→ℝ),
      1≤ Z→0≤ ell+eta→0≤ B→0≤ j→
      ε*(r-A-B-t)+7*eta/2+dsmall*(3*ell+B+t+5*eta)+2*ε*(2*ell+B+t+4*eta)≤ pi+eta/2→
      (∀x∈original,SourceValid p x)→
      (∀x∈original,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤ Z^(ell+eta))→
      (∀x∈original,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤ Z^(ell+eta))→
      (∀x∈original,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤ Z^(Ractive+eta))→
      (∀x∈original,primeProductNorm p x.firstCommon≤ Z^(B+eta))→
      (∀x∈original,primeProductNorm p x.quotientSupport≤ Z^(t+eta))→
      (∀x∈original,extra x.cube⊆x.cube.support)→
      hi≤ Real.exp window→1≤ Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)→(∀G E,0≤ R G E)→
      (Z^(firstKappa M r ell V delta A B Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      globalPriorityZeroAggregate p hg extra pool original w negative Ψ m slots lists a
        (principalWindow om lo hi hlo hs negative height) (Z^(r-A-B-t))
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) R≤
      Czero*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
        (SchwartzMap.seminorm ℝ 0 0 om)^2*Real.exp (window*(1+ε))*
        Z^(r+3*ell+V+17*eta+tau+pi):=by
  obtain ⟨s,Cp,hCp,hprincipal⟩:=global_priority_zero_aggregate ε hε
  obtain ⟨Cm,hCm,hmass⟩:=original_physical_weighted_source Jmax dsmall hdsmall
  refine ⟨s,Cp*Cm,mul_pos hCp hCm,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop Jo hJo extra pool original w negative Ψ m slots lists a
    hslots ha hΨ hw om lo hi hlo hs Z M r ell V delta A B Ractive j t eta tau window pi height R
    hZ hell hB hj hcost hsource hc₁ hc₂ hactive hcommon hquot hextra hhi hY hR
  have hz:0<Z:=zero_lt_one.trans_le hZ
  let P:=Z^(firstKappa M r ell V delta A B Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let Q:=Cp*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
    (SchwartzMap.seminorm ℝ 0 0 om)^2
  have hP:0≤ P:=by dsimp [P];positivity
  have hQ:0≤ Q:=by dsimp [Q];positivity
  have he:=mul_le_mul_of_nonneg_left (hprincipal p hp hg hinj hcop extra pool original w negative Ψ m slots lists a
    hslots ha hΨ hw om lo hi hlo hs (Z^(r-A-B-t)) window
    (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) height R (by positivity) hhi hY hR) hP
  have hm:=hmass p hp hinj Jo hJo original Z M r ell V delta A B Ractive j t eta tau ε window pi
    hZ hell hε.le hB hj hcost hsource hc₁ hc₂ hactive hcommon hquot extra negative hextra
  have hsupp(x:Source ι Jo):wholeExtractedSupport (fun x=>extra x.cube) negative x=principalSupport extra negative x:=by
    simp only [wholeExtractedSupport,extractedSupport,principalSupport,Finset.union_assoc]
  simp_rw [hsupp] at he
  apply he.trans
  calc
    _=Q*(physicalPrincipalFactor Z M r ell V delta A B Ractive j t eta tau ε window*
      ∑x∈original,(primeProductNorm p (principalSupport extra negative x))^(2*ε)):=by
      dsimp [Q,P,physicalPrincipalFactor];ring
    _≤ Q*(Cm*Real.exp (window*(1+ε))*Z^(r+3*ell+V+17*eta+tau+pi)):=mul_le_mul_of_nonneg_left hm hQ
    _= _:=by dsimp [Q];ring
end InverseMoment

end

noncomputable section
namespace InverseMomentGlobalPriorityTail
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseMomentGlobalPrincipalMass InverseInitialArithmetic
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InversePrioritySecondSource InverseSecondPrincipalCaller InversePrincipalEnergy
open InverseWholePriorityRetainedSource
open Eisenstein (ringComplex)
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

theorem global_parent_tail_rapid (Jmax : ℕ) (Lcap tau saving : ℝ)
    (hLcap : 0≤ Lcap) (htau : 0<tau) :
    ∃(s : Finset (ℕ×ℕ))(C : ℝ),0<C ∧
    ∀{ι σ : Type*}[DecidableEq ι][DecidableEq σ]
      (p : ι→O)(hp : ∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Jo : ℕ),Jo≤ Jmax → ∀(extra : CubeCoordinates ι→Finset ι)(pool : Finset ι)
      (source : Finset (Source ι Jo))(negative : Bool)(Ψ : O→*ℂ)(m : O)
      (ray : RayCharacter×RayCharacter)(core : FirstCoreIndex)
      (w : Source ι Jo→ℂ)(slots J : Finset σ)(lists : σ→Finset ι)(a : σ→ι→ℂ),
      J⊆slots → (slots:Set σ).PairwiseDisjoint lists →
      (∀i∈slots,∀k∈lists i,‖a i k‖≤1) → (∀u,‖Ψ u‖≤1) → (∀x∈source,‖w x‖≤1) →
      ∀(om : 𝓢(ℝ,ℂ))(lo hi : ℝ)(hlo : 0<lo)(hs : Function.support om⊆Set.Icc lo hi)
      (X M Y Z height : ℝ)(R : Finset ι→Finset ι→ℝ),
      0<X → hi≤ Real.exp M → 1≤ Z → 0<Y → 1≤ X*Real.exp M →
      Y≤ Z^Lcap → Y⁻¹≤ Z^Lcap → X*Real.exp M≤ Z^Lcap →
      (∀x∈source,SourceValid p x) → (∀x∈source,extra x.cube⊆x.cube.support) →
      (∀x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤ Z^Lcap) →
      (∀x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤ Z^Lcap) →
      (∀x∈source,‖ringComplex (∏i∈cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤ Z^Lcap) →
      (∀x∈source,primeProductNorm p x.firstCommon≤ Z^Lcap) →
      (∀x∈source,primeProductNorm p x.quotientSupport≤ Z^Lcap) →
      (∀x∈source,∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p (parent p x)) G E.val
          (X*Real.exp M) Y (Z^tau)≤ R G E.val) →
      ‖∑y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
        coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) y*
        priorityTailParent p hg hp hinj extra pool negative
          (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
          m slots J lists a (principalWindow om lo hi hlo hs negative height) X Y R y‖≤
      C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
        (SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving) := by
  obtain ⟨s,Ct,hCt,htail⟩ := priority_tail_parent_uniform Lcap tau (saving+13*Lcap) hLcap htau
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_small_power (1/2) (by norm_num)
  obtain ⟨Cs,hCs,hmass⟩ := original_tail_mass Jmax
  have hCb : 0<coefficientBound := coefficientBound_pos
  refine ⟨s,coefficientBound*Cm^2*Ct*Cs,by positivity,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc Jo hJo extra pool source negative Ψ m ray core w slots J lists a
    hJ hslots ha hΨ hw om lo hi hlo hs X M Y Z height R hX hhi hZ hY hscale hy hyi hXcap
    hsource hextra hb₁ hb₂ hactive hcommon hquot hR
  have hz : 0<Z := zero_lt_one.trans_le hZ
  let Ψ₀ := firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
  let V := principalWindow om lo hi hlo hs negative height
  let Q := (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2
  let T := Ct*Q*Z^(-(saving+13*Lcap))
  have hT : 0≤ T := by dsimp [T,Q];positivity
  have hΨ₀ : ∀u,‖Ψ₀ u‖≤1 := fun u=>(firstCoreTwist_norm_le negative _ Ψ core u).trans (hΨ u)
  have hout (x : Source ι Jo) (hx : x∈source) :
      ‖globalPriorityOuter p hg negative Ψ m ray core w x‖≤ coefficientBound := by
    rw [globalPriorityOuter,norm_mul]
    exact (mul_le_mul (hw x hx)
      (priorityOuter_norm p hg x.cube negative Ψ m (fun _=>1) ray core x.quotientSupport
        (by simp) (hΨ _)) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hm (x : Source ι Jo) :
      ‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2≤
        Cm^2*primeProductNorm p (principalSupport extra negative x) := by
    have hh := hmark p hp hcop J lists a
      (fun i hi j hj hij=>hslots (hJ hi) (hJ hj) hij) (fun i hi=>ha i (hJ hi))
      (principalSupport extra negative x)
    have he : ((primeProductNorm p (principalSupport extra negative x))^(1/2:ℝ))^2=
        primeProductNorm p (principalSupport extra negative x) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (primeProductNorm_pos p hp _).le]
      norm_num
    have hsupp : wholeExtractedSupport (fun x=>extra x.cube) negative x=principalSupport extra negative x := by
      simp only [wholeExtractedSupport,extractedSupport,principalSupport,Finset.union_assoc]
    rw [hsupp]
    exact (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans_eq (by rw [mul_pow,he])
  have ht (x : Source ι Jo) (hx : x∈source) :
      ‖priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots J lists a V X Y R (parent p x)‖≤ T := by
    simpa only [T,Q,mul_assoc] using htail p hp hg hinj hcop hc extra pool negative Ψ₀ m slots J lists a
      hslots ha hΨ₀ om lo hi hlo hs X M Y Z height R hX hhi hZ hY hscale hy hyi hXcap
      (parent p x) (hR x hx)
  have hmass₀ := hmass p hp hinj Jo hJo source Z Lcap hZ hLcap hsource hb₁ hb₂ hactive hcommon hquot extra negative hextra
  rw [original_paired_tail p hg hp hinj]
  calc
    _ ≤ ∑x∈source,‖globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots J lists a V X Y R (parent p x)‖ := norm_sum_le _ _
    _ ≤ ∑x∈source,coefficientBound*(Cm^2*primeProductNorm p (principalSupport extra negative x))*T := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
      exact mul_le_mul (mul_le_mul (hout x hx) (hm x) (sq_nonneg _) coefficientBound_pos.le)
        (ht x hx) (norm_nonneg _)
        (mul_nonneg hCb.le (mul_nonneg (sq_nonneg _) (primeProductNorm_pos p hp _).le))
    _ = coefficientBound*Cm^2*T*(∑x∈source,primeProductNorm p (principalSupport extra negative x)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros
      ring
    _ ≤ coefficientBound*Cm^2*T*(Cs*Z^(13*Lcap)) :=
      mul_le_mul_of_nonneg_left hmass₀ (by positivity)
    _ = _ := by
      have he : Z^(-(saving+13*Lcap))*Z^(13*Lcap)=Z^(-saving) := by
        rw [←Real.rpow_add hz]
        congr 1
        ring
      dsimp only [T,Q]
      calc
        _ = coefficientBound*Cm^2*Ct*Cs*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
          (SchwartzMap.seminorm ℝ 0 0 om)^2*(Z^(-(saving+13*Lcap))*Z^(13*Lcap)) := by ring
        _ = _ := by rw [he]

end InverseMomentGlobalPriorityTail
end

noncomputable section
namespace InverseMomentGlobalPriorityTail
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseMomentGlobalPrincipalMass InverseInitialArithmetic
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InversePrioritySecondSource InverseSecondPrincipalCaller InversePrincipalEnergy
open InverseWholePriorityRetainedSource
open Eisenstein (ringComplex)
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

theorem global_parent_tail_aggregate_rapid (Jmax : ℕ) (Lcap tau saving : ℝ)
    (hLcap : 0≤ Lcap) (htau : 0<tau) :
    ∃(s : Finset (ℕ×ℕ))(C : ℝ),0<C ∧
    ∀{ι σ : Type*}[DecidableEq ι][DecidableEq σ]
      (p : ι→O)(hp : ∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Jo : ℕ),Jo≤ Jmax → ∀(extra : CubeCoordinates ι→Finset ι)(pool : Finset ι)
      (source : Finset (Source ι Jo))(negative : Bool)(Ψ : O→*ℂ)(m : O)
      (w : Source ι Jo→ℂ)(slots : Finset σ)(lists : σ→Finset ι)(a : σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists →
      (∀i∈slots,∀k∈lists i,‖a i k‖≤1) → (∀u,‖Ψ u‖≤1) → (∀x∈source,‖w x‖≤1) →
      ∀(om : 𝓢(ℝ,ℂ))(lo hi : ℝ)(hlo : 0<lo)(hs : Function.support om⊆Set.Icc lo hi)
      (X M Y Z height : ℝ)(R : Finset ι→Finset ι→ℝ),
      0<X → hi≤ Real.exp M → 1≤ Z → 0<Y → 1≤ X*Real.exp M →
      Y≤ Z^Lcap → Y⁻¹≤ Z^Lcap → X*Real.exp M≤ Z^Lcap →
      (∀x∈source,SourceValid p x) → (∀x∈source,extra x.cube⊆x.cube.support) →
      (∀x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤ Z^Lcap) →
      (∀x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤ Z^Lcap) →
      (∀x∈source,‖ringComplex (∏i∈cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤ Z^Lcap) →
      (∀x∈source,primeProductNorm p x.firstCommon≤ Z^Lcap) →
      (∀x∈source,primeProductNorm p x.quotientSupport≤ Z^Lcap) →
      (∀x∈source,∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p (parent p x)) G E.val
          (X*Real.exp M) Y (Z^tau)≤ R G E.val) →
      firstCoreMassBound*(2:ℝ)^slots.card*
      (∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
        ‖∑y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
        coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) y*
        priorityTailParent p hg hp hinj extra pool negative
          (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
          m slots J lists a (principalWindow om lo hi hlo hs negative height) X Y R y‖)≤
      C*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
        (SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving) := by
  obtain ⟨s,C,hC,hbound⟩ := global_parent_tail_rapid Jmax Lcap tau saving hLcap htau
  let N : ℝ := (Fintype.card (RayCharacter×RayCharacter):ℝ)*(Fintype.card FirstCoreIndex:ℝ)
  have hN : 0<N := by dsimp [N];positivity
  refine ⟨s,max (firstCoreMassBound*N*C) 1,zero_lt_one.trans_le (le_max_right _ _),?_⟩
  have hmass := firstCoreMassBound_nonneg
  intro ι σ _ _ p hp _ hg hinj hcop hc Jo hJo extra pool source negative Ψ m w slots lists a
    hslots ha hΨ hw om lo hi hlo hs X M Y Z height R hX hhi hZ hY hscale hy hyi hXcap
    hsource hextra hb₁ hb₂ hactive hcommon hquot hR
  let B := C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
    (SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving)
  have hsum : (∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
      ‖∑y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
        coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) y*
        priorityTailParent p hg hp hinj extra pool negative
          (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
          m slots J lists a (principalWindow om lo hi hlo hs negative height) X Y R y‖)
      ≤ N*(2:ℝ)^slots.card*B := by
    calc
      _ ≤ ∑_ray:RayCharacter×RayCharacter,∑_core:FirstCoreIndex,∑_J∈slots.powerset,B := by
        apply Finset.sum_le_sum
        intro ray hr
        apply Finset.sum_le_sum
        intro core hc₀
        apply Finset.sum_le_sum
        intro J hJ
        exact hbound p hp hg hinj hcop hc Jo hJo extra pool source negative Ψ m ray core w slots J lists a
          (Finset.mem_powerset.mp hJ) hslots ha hΨ hw om lo hi hlo hs X M Y Z height R
          hX hhi hZ hY hscale hy hyi hXcap hsource hextra hb₁ hb₂ hactive hcommon hquot hR
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_powerset,Finset.card_univ,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
        dsimp [N]
        ring
  apply (mul_le_mul_of_nonneg_left hsum (by positivity : 0≤firstCoreMassBound*(2:ℝ)^slots.card)).trans
  have he : ((2:ℝ)^slots.card)^2=(4:ℝ)^slots.card := by
    rw [←pow_mul,pow_mul']
    norm_num
  dsimp [B]
  calc
    _ = firstCoreMassBound*N*C*((2:ℝ)^slots.card)^2*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
      (SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving) := by ring
    _ ≤ _ := by
      rw [he]
      gcongr
      exact le_max_left _ _

end InverseMomentGlobalPriorityTail
end

noncomputable section
namespace InverseMomentGlobalPriorityTail
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseMomentGlobalPrincipalMass InverseInitialArithmetic
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InversePrioritySecondSource InverseSecondPrincipalCaller InversePrincipalEnergy
open InverseWholePriorityRetainedSource
open Eisenstein (ringComplex)
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

theorem global_physical_tail_rapid (Jmax : ℕ) (Lcap tau saving : ℝ)
    (hLcap : 0≤ Lcap) (htau : 0<tau) :
    ∃(s : Finset (ℕ×ℕ))(C : ℝ),0<C ∧
    ∀{ι σ : Type*}[DecidableEq ι][DecidableEq σ]
      (p : ι→O)(hp : ∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Jo : ℕ),Jo≤ Jmax → ∀(extra : CubeCoordinates ι→Finset ι)(pool : Finset ι)
      (source : Finset (Source ι Jo))(negative : Bool)(Ψ : O→*ℂ)(m : O)
      (w : Source ι Jo→ℂ)(slots : Finset σ)(lists : σ→Finset ι)(a : σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists →
      (∀i∈slots,∀k∈lists i,‖a i k‖≤1) → (∀u,‖Ψ u‖≤1) → (∀x∈source,‖w x‖≤1) →
      ∀(om : 𝓢(ℝ,ℂ))(lo hi : ℝ)(hlo : 0<lo)(hs : Function.support om⊆Set.Icc lo hi)
      (X M Y Z height kappa eta : ℝ)(R : Finset ι→Finset ι→ℝ),
      kappa+(9/2:ℝ)*eta≤ Lcap →
      0<X → hi≤ Real.exp M → 1≤ Z → 0<Y → 1≤ X*Real.exp M →
      Y≤ Z^Lcap → Y⁻¹≤ Z^Lcap → X*Real.exp M≤ Z^Lcap →
      (∀x∈source,SourceValid p x) → (∀x∈source,extra x.cube⊆x.cube.support) →
      (∀x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤ Z^Lcap) →
      (∀x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤ Z^Lcap) →
      (∀x∈source,‖ringComplex (∏i∈cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤ Z^Lcap) →
      (∀x∈source,primeProductNorm p x.firstCommon≤ Z^Lcap) →
      (∀x∈source,primeProductNorm p x.quotientSupport≤ Z^Lcap) →
      (∀x∈source,∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p (parent p x)) G E.val
          (X*Real.exp M) Y (Z^tau)≤ R G E.val) →
      (Z^kappa*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*(firstCoreMassBound*(2:ℝ)^slots.card*
      (∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
        ‖∑y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
        coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) y*
        priorityTailParent p hg hp hinj extra pool negative
          (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
          m slots J lists a (principalWindow om lo hi hlo hs negative height) X Y R y‖))≤
      C*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
        (SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving) := by
  obtain ⟨s,C,hC,hbound⟩ := global_parent_tail_aggregate_rapid Jmax Lcap tau (saving+Lcap) hLcap htau
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc Jo hJo extra pool source negative Ψ m w slots lists a
    hslots ha hΨ hw om lo hi hlo hs X M Y Z height kappa eta R hkappa hX hhi hZ hY hscale hy hyi hXcap
    hsource hextra hb₁ hb₂ hactive hcommon hquot hR
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hh := hbound p hp hg hinj hcop hc Jo hJo extra pool source negative Ψ m w slots lists a
    hslots ha hΨ hw om lo hi hlo hs X M Y Z height R hX hhi hZ hY hscale hy hyi hXcap
    hsource hextra hb₁ hb₂ hactive hcommon hquot hR
  have he : Z^kappa*Real.exp ((9/2:ℝ)*(eta*Real.log Z))=Z^(kappa+(9/2:ℝ)*eta) := by
    rw [Real.rpow_add hz,Real.rpow_def_of_pos hz ((9/2:ℝ)*eta)]
    congr 2
    ring
  have hP : Z^kappa*Real.exp ((9/2:ℝ)*(eta*Real.log Z))≤ Z^Lcap := by
    rw [he]
    exact Real.rpow_le_rpow_of_exponent_le hZ hkappa
  apply (mul_le_mul_of_nonneg_left hh (by positivity)).trans
  calc
    _ ≤ Z^Lcap*(C*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
      (SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-(saving+Lcap))) :=
      mul_le_mul_of_nonneg_right hP (by positivity)
    _ = _ := by
      have he₂ : Z^Lcap*Z^(-(saving+Lcap))=Z^(-saving) := by
        rw [←Real.rpow_add hz]
        congr 1
        ring
      calc
        _ = C*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
          (SchwartzMap.seminorm ℝ 0 0 om)^2*(Z^Lcap*Z^(-(saving+Lcap))) := by ring
        _ = _ := by rw [he₂]

end InverseMomentGlobalPriorityTail
end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InverseSecondPrincipalCaller InversePrioritySecondSource InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InverseMomentGlobalPriorityTail
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O"=>Eisenstein.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]{Jo:ℕ}
variable (p:ι→O)[∀i,(Ideal.span {p i}).IsMaximal](hg:∀i,lambda∉Ideal.span {p i})
def globalPriorityOriginalEnergy (hp:∀i,p i≠0)(hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:ℝ→ℂ)(X t Y:ℝ):ℝ:=
  firstCoreMassBound*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
    (∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra x.cube)
        a om X t Y ray core (parent p x)).re

def globalPriorityTailAggregate (hp:∀i,p i≠0)(hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (V:𝓢(ℝ,ℂ))(X Y:ℝ)(R:Finset ι→Finset ι→ℝ):ℝ:=
  firstCoreMassBound*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
    ‖∑y∈wholeAssignedParents p (fun x=>extra x.cube) original negative J lists,
      coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) y*
      priorityTailParent p hg hp hinj extra pool negative
        (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
        m slots J lists a V X Y R y‖

theorem global_priority_three_branches
    (hp:∀i,p i≠0)(hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)(hpr:∀i,lambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ)(hX:0<X)(hY:0<Y)(R:Finset ι→Finset ι→ℝ):
    let V:=principalWindow om lo hi hlo hs negative t;
    globalPriorityOriginalEnergy p hg hp hinj extra pool original w negative Ψ m slots lists a om X t Y≤
      globalPriorityZeroAggregate p hg extra pool original w negative Ψ m slots lists a V X Y R+
      globalPriorityRetainedAggregate p hg hp hcop extra pool original w negative Ψ m slots lists a V X Y R+
      globalPriorityTailAggregate p hg hp hinj extra pool original w negative Ψ m slots lists a V X Y R:=by
  have hmass := firstCoreMassBound_nonneg
  dsimp only
  unfold globalPriorityOriginalEnergy globalPriorityZeroAggregate globalPriorityRetainedAggregate globalPriorityTailAggregate
  rw [←mul_add,←mul_add]
  simp only [←Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro ray hray
  apply Finset.sum_le_sum
  intro core hcore
  apply Finset.sum_le_sum
  intro J hJ
  have hb:=global_priority_slice_full_tail p hg hp hcop hinj hc hpr extra pool original w negative Ψ m
    ray core slots J lists a om lo hi hlo hs X t Y hX hY R
  dsimp only at hb
  rw [original_paired_tail p hg hp hinj]
  exact (Complex.re_le_norm _).trans hb
end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InverseFirstPriorityParents
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O"=>Eisenstein.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]{Jo:ℕ}
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,lambda∉Ideal.span {p i})

theorem global_canonical_to_original_priority
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (outer:Finset (Source ι Jo))(pool:Finset ι)(selector:Source ι Jo→Finset ι→ℂ)
    (houter:∀x∈outer,x.quotientSupport=∅)(extra:CubeCoordinates ι→Finset ι)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:ℝ→ℂ)(X t Y:ℝ)(hY:0<Y):
    (∑x∈outer,firstCanonicalSecondEnergy p hp hg hinj pool x.cube x.firstCommon
      negative Ψ m ((∏ i ∈ x.firstDivisor,p i))
      (fun U=>primeMark slots lists a (extra x.cube∪U)) (selector x) om X t Y) ≤
    globalPriorityOriginalEnergy p hg hp hinj extra pool (globalParentSource outer pool selector)
      (fun x=>(‖selector (eraseFirstQuotient x) x.quotientSupport‖:ℂ))
      negative Ψ m slots lists a om X t Y := by
  apply le_trans (Finset.sum_le_sum (fun x hx=>
    first_actual_second_whole_cube_priority p hp hg hinj hc pool x.cube x.firstCommon (extra x.cube)
      negative Ψ m ((∏ i ∈ x.firstDivisor,p i))
      slots lists a (selector x) om X t Y hY))
  exact le_of_eq (global_second_energy_source p hg hp hinj outer pool selector houter extra
    negative Ψ m slots lists a om X t Y)

theorem original_canonical_to_global_priority
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(selector:FirstOriginalOuter ι→Finset ι→ℂ)
    (extra:CubeCoordinates ι→Finset ι)(negative:Bool)(Ψ:O→*ℂ)(m:O)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:ℝ→ℂ)(X t Y:ℝ)(hY:0<Y):
    (∑k∈firstOriginalOuter pool Q,firstCanonicalSecondEnergy p hp hg hinj pool k.1 k.2.1
      negative Ψ m ((∏ i ∈ k.2.2,p i))
      (fun U=>primeMark slots lists a (extra k.1∪U)) (selector k) om X t Y) ≤
    globalPriorityOriginalEnergy p hg hp hinj extra pool
      (InverseFirstGlobalParents.originalParentSource pool Q selector)
      (fun x=>(‖selector (InverseFirstGlobalParents.toOriginal x) x.quotientSupport‖:ℂ))
      negative Ψ m slots lists a om X t Y := by
  apply le_trans (Finset.sum_le_sum (fun k hk=>
    first_actual_second_whole_cube_priority p hp hg hinj hc pool k.1 k.2.1 (extra k.1)
      negative Ψ m ((∏ i ∈ k.2.2,p i))
      slots lists a (selector k) om X t Y hY))
  exact le_of_eq (InverseFirstGlobalParents.original_second_energy_source p hg hp hinj pool Q
    selector extra negative Ψ m slots lists a om X t Y)

end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseFirstPriorityParents InverseFirstGlobalParents
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O"=>Eisenstein.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]

def originalSubsetSource (outer:Finset (FirstOriginalOuter ι)):Finset (Source ι 0):=
  outer.image ofOriginal

theorem original_subset_canonical_priority
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,lambda∉Ideal.span {p i})
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (outer:Finset (FirstOriginalOuter ι))(pool:Finset ι)
    (selector:FirstOriginalOuter ι→Finset ι→ℂ)(extra:CubeCoordinates ι→Finset ι)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:ℝ→ℂ)(X t Y:ℝ)(hY:0<Y):
    (∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj pool k.1 k.2.1
      negative Ψ m ((∏ i ∈ k.2.2,p i))
      (fun U=>primeMark slots lists a (extra k.1∪U)) (selector k) om X t Y) ≤
    globalPriorityOriginalEnergy p hg hp hinj extra pool
      (globalParentSource (originalSubsetSource outer) pool (originalSelector selector))
      (fun x=>(‖selector (toOriginal x) x.quotientSupport‖:ℂ))
      negative Ψ m slots lists a om X t Y:=by
  have hempty:∀x∈originalSubsetSource outer,x.quotientSupport=∅:=by
    intro x hx
    obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp hx
    rfl
  have he:=global_canonical_to_original_priority p hp hg hinj hc
    (originalSubsetSource outer) pool (originalSelector selector) hempty extra
    negative Ψ m slots lists a om X t Y hY
  rw [show originalSubsetSource outer=outer.image ofOriginal from rfl,
    Finset.sum_image (fun _ _ _ _ h=>ofOriginal_injective h)] at he
  have hs (k:FirstOriginalOuter ι): originalSelector selector (ofOriginal k)=selector k :=
    originalSelector_ofOriginal_fun selector k
  simp_rw [hs] at he
  simpa only [originalSubsetSource,ofOriginal,originalSelector,toOriginal,eraseFirstQuotient] using he

theorem original_cell_parent_source
    (p:ι→O)(pool:Finset ι)(Q:Finset (ι→₀ℕ))
    (selector:FirstOriginalOuter ι→Finset ι→ℂ)
    (k:InverseMomentFirstChildWindows.SourceIndex)(l:ℕ):
    globalParentSource (originalSubsetSource (InverseFirstGlobalCaps.outerCell p pool Q k))
      pool (originalSelector (fun x=>InverseMomentFirstChildWindows.commonSelector p (selector x) l))=
      InverseFirstGlobalCaps.parentCell p pool Q selector k l:=by
  ext x
  rw [InverseFirstGlobalCaps.mem_parentCell]
  simp only [globalParentSource,Finset.mem_biUnion,originalSubsetSource,Finset.mem_image,
    Finset.mem_filter]
  constructor
  · rintro ⟨y,⟨o,ho,rfl⟩,D,⟨hD,hs⟩,he⟩
    exact ⟨o,ho,D,hD,by simpa using hs,he⟩
  · rintro ⟨o,ho,D,hD,hs,he⟩
    exact ⟨ofOriginal o,⟨o,ho,rfl⟩,D,⟨hD,by simpa using hs⟩,he⟩

theorem original_cell_canonical_priority
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,lambda∉Ideal.span {p i})
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(selector:FirstOriginalOuter ι→Finset ι→ℂ)
    (k:InverseMomentFirstChildWindows.SourceIndex)(l:ℕ)
    (extra:CubeCoordinates ι→Finset ι)(negative:Bool)(Ψ:O→*ℂ)(m:O)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(om:ℝ→ℂ)(X t Y:ℝ)(hY:0<Y):
    (∑o∈InverseFirstGlobalCaps.outerCell p pool Q k,
      firstCanonicalSecondEnergy p hp hg hinj pool o.1 o.2.1 negative Ψ m
        ((∏ i ∈ o.2.2,p i))
        (fun U=>primeMark slots lists a (extra o.1∪U))
        (InverseMomentFirstChildWindows.commonSelector p (selector o) l) om X t Y)≤
    globalPriorityOriginalEnergy p hg hp hinj extra pool
      (InverseFirstGlobalCaps.parentCell p pool Q selector k l)
      (fun x=>(‖InverseMomentFirstChildWindows.commonSelector p (selector (toOriginal x)) l x.quotientSupport‖:ℂ))
      negative Ψ m slots lists a om X t Y:=by
  have he:=original_subset_canonical_priority p hp hg hinj hc
    (InverseFirstGlobalCaps.outerCell p pool Q k) pool
    (fun x=>InverseMomentFirstChildWindows.commonSelector p (selector x) l) extra negative Ψ m slots lists a om X t Y hY
  rwa [original_cell_parent_source] at he

end InverseMoment

end

noncomputable section
namespace InverseMomentFirstOriginalProfile
open InverseMoment Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι σ : Type} [DecidableEq ι] [DecidableEq σ]

lemma refined_parent_source (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l j : ℕ) :
    globalParentSource (originalSubsetSource (refinedOuter p pool Q k (labelGate p j)))
      pool (originalSelector (fun x=>commonSelector p (selector x) l))=
      InverseFirstGlobalCaps.labelParentCell p pool Q selector k l j := by
  ext x
  rw [InverseFirstGlobalCaps.labelParentCell,Finset.mem_filter,InverseFirstGlobalCaps.mem_parentCell]
  simp only [globalParentSource,Finset.mem_biUnion,originalSubsetSource,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨y,⟨o,ho,rfl⟩,D,⟨hD,hs⟩,rfl⟩
    have ho' := Finset.mem_filter.mp ho
    refine ⟨⟨o,?_,D,hD,by simpa using hs,rfl⟩,?_⟩
    · simpa only [originalOuterCell_eq_caps] using ho'.1
    · simpa [labelGate,fillFirstQuotient,toOriginal,ofOriginal] using ho'.2
  · rintro ⟨⟨o,ho,D,hD,hs,rfl⟩,hj⟩
    refine ⟨ofOriginal o,⟨o,?_,rfl⟩,D,⟨hD,by simpa using hs⟩,rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_,?_⟩
    · simpa only [originalOuterCell_eq_caps] using ho
    · simpa [labelGate,fillFirstQuotient,toOriginal,ofOriginal] using hj

theorem refined_child_priority (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,lambda∉Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : ℝ→ℂ) (X t Y : ℝ) (hY : 0<Y) :
    refinedChildEnergy p hp hg hinj pool Q k l (labelGate p j) negative Ψ m
      (fun v U=>primeMark slots lists a (v.support∪U)) om X t Y ≤
    globalPriorityOriginalEnergy p hg hp hinj
      (fun b=>if negative then b.rightExponent.support else b.leftExponent.support) pool
      (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j)
      (fun x=>(‖commonSelector p (fun _=>1) l x.quotientSupport‖:ℂ))
      negative Ψ m slots lists a om X t Y := by
  have he := original_subset_canonical_priority p hp hg hinj hc
    (refinedOuter p pool Q k (labelGate p j)) pool (fun _=>commonSelector p (fun _=>1) l)
    (fun b=>if negative then b.rightExponent.support else b.leftExponent.support)
    negative Ψ m slots lists a om X t Y hY
  rw [refined_parent_source] at he
  cases negative <;> simpa [refinedChildEnergy,divisorElement] using he

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

theorem original_dyadic_priority_budget
    (om Φ:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support om⊆Set.Icc a b) (Lcap:ℝ)(hcap:0≤ Lcap)(hb:0≤ b):
    ∃(omega₁ omega₂:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo ∧ lo≤ hi ∧
      HasCompactSupport (omega₁:ℝ→ℂ) ∧ HasCompactSupport (omega₂:ℝ→ℂ) ∧
      tsupport (omega₁:ℝ→ℂ)⊆Set.Icc lo hi ∧ tsupport (omega₂:ℝ→ℂ)⊆Set.Icc lo hi ∧
    ∀eps:ℝ,0<eps→∀J:ℕ,∃C:ℝ,0≤ C ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,lambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V eta tau Fmax Γ K theta Benergy:ℝ)
      (_hZ:2≤ Z)(_hbin:2≤ Z^eta)(_hM:0≤ M)(_hF:r+3*ell+V≤ Fmax)
      (_hQ:∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta))
      (_hrcap:r≤ Lcap)(_hellcap:ell≤ Lcap)(_hF0:0≤ Fmax)(_hFcap:Fmax≤ Lcap)
      (_heta:0≤ eta)(_heta1:eta≤1)(_htau:0≤ tau)(_htau1:tau≤1)
      (_hΨ:∀u,‖Ψ u‖≤1)(_hΓ:0≤Γ)(_hK:0<K)(_hB:0≤ Benergy)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)(_hβ:∀I∈labels,∀v∈Q,‖β I v‖≤Γ),
      let mark:=fun v U=>primeMark slots lists weights (v.support∪U);
      let Y:=Z^(2*Fmax+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource om theta (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hg β cutoff Ψ m mark W Φ K);
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 0))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj (fun q=>q.rightExponent.support) pool
          (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2)
          (fun x=>(‖commonSelector p (fun _=>1) k.2.1 x.quotientSupport‖:ℂ))
          true Ψ m slots lists weights omega₁
          ((physicalScales (Z^r) k.1 k.2.1) 7)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤ Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 1))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj (fun q=>q.leftExponent.support) pool
          (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2)
          (fun x=>(‖commonSelector p (fun _=>1) k.2.1 x.quotientSupport‖:ℂ))
          false Ψ m slots lists weights omega₂
          ((physicalScales (Z^r) k.1 k.2.1) 8)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤ Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (Z^(-r-2*ell-V)*Z^M)*‖originalRetainedFamily p hp hg pool Q labels β Ψ m mark W Φ K Y cutoff (fun _=>1)‖≤
        C*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*
          Z^((2*Fmax+15*eta+tau)*eps+eps) :=by
  obtain ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,he⟩:=original_dyadic_retained_budget om Φ a b ha hs Lcap hcap hb
  refine ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro eps heps J
  obtain ⟨C,hC,henergy⟩:=he eps heps J
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc hpr pool Q labels β Ψ m slots lists weights Z M r ell V eta tau Fmax Γ K theta Benergy
    hZ hbin hM hF hQ hrcap hellcap hF0 hFcap heta heta1 htau htau1 hΨ hΓ hK hB hsf hn hβ
    mark Y cutoff W source keys hleft hright
  have hz:0<Z:=by linarith
  apply henergy p hp hg hinj hcop hc hpr pool Q labels β Ψ m mark Z M r ell V eta tau Fmax Γ K theta Benergy
    hZ hbin hM hF hQ hrcap hellcap hF0 hFcap heta heta1 htau htau1 hΨ hΓ hK hB hsf hn hβ
  · intro k hk z
    have he':=refined_child_priority p hp hg hinj hc pool Q k.1 k.2.1 k.2.2 true Ψ m slots lists weights w₁
      ((physicalScales (Z^r) k.1 k.2.1) 7)
      (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
      (firstCellRadius Z M r ell V eta tau k.1 k.2.2) (Real.rpow_pos_of_pos hz _)
    exact (mul_le_mul_of_nonneg_left he' (mul_nonneg (Real.rpow_nonneg hz.le _) (Real.exp_pos _).le)).trans (hleft k hk z)
  · intro k hk z
    have he':=refined_child_priority p hp hg hinj hc pool Q k.1 k.2.1 k.2.2 false Ψ m slots lists weights w₂
      ((physicalScales (Z^r) k.1 k.2.1) 8)
      (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
      (firstCellRadius Z M r ell V eta tau k.1 k.2.2) (Real.rpow_pos_of_pos hz _)
    exact (mul_le_mul_of_nonneg_left he' (mul_nonneg (Real.rpow_nonneg hz.le _) (Real.exp_pos _).le)).trans (hright k hk z)

end InverseMoment

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

theorem original_dyadic_full_energy
    (om:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support om⊆Set.Icc a b) (Lcap Mmax eta tau saving:ℝ)(hcap:0≤ Lcap)(hMmax:0≤ Mmax)(hb:0≤ b)
    (heta:0≤ eta)(heta1:eta≤1)(htau:0<tau)(htau1:tau≤1):
    ∃(omega₁ omega₂:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo ∧ lo≤ hi ∧
      HasCompactSupport (omega₁:ℝ→ℂ) ∧ HasCompactSupport (omega₂:ℝ→ℂ) ∧
      tsupport (omega₁:ℝ→ℂ)⊆Set.Icc lo hi ∧ tsupport (omega₂:ℝ→ℂ)⊆Set.Icc lo hi ∧
    ∀eps:ℝ,0<eps→∀J:ℕ,∃C Czero Ctail:ℝ,0≤ C ∧ 0≤ Czero ∧ 0≤ Ctail ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,lambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V Γ theta Benergy:ℝ)
      (_hZ:2≤ Z)(_hbin:2≤ Z^eta)(_hM:0≤ M)(_hF:r+3*ell+V≤ Lcap)(_hMcap:M≤ Mmax)(_hell:0≤ ell)(_hV:0≤ V)(_hr: -eta≤ r)
      (_hbZ:b≤ Z^eta)(_hQpool:∀v∈Q,v.support⊆pool)
      (_hQ:∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta))
      (_hrcap:r≤ Lcap)(_hellcap:ell≤ Lcap)

      (_hΨ:∀u,‖Ψ u‖≤1)(_hΓ:0≤Γ)(_hB:0≤ Benergy)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)(_hβ:∀I∈labels,∀v∈Q,‖β I v‖≤Γ)
      (_hlabels:∀I∈labels,(Ideal.absNorm I:ℝ)≤ Z^(V+eta))
      (_hslots:(slots:Set σ).PairwiseDisjoint lists)(_hweights:∀i∈slots,∀q∈lists i,‖weights i q‖≤1),
      let mark:=fun v U=>primeMark slots lists weights (v.support∪U);
      let Y:=Z^(2*Lcap+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource om theta (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hg β cutoff Ψ m mark W rowMajorant (Z^M));
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 0))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj (fun q=>q.rightExponent.support) pool
          (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2)
          (fun x=>(‖commonSelector p (fun _=>1) k.2.1 x.quotientSupport‖:ℂ))
          true Ψ m slots lists weights omega₁
          ((physicalScales (Z^r) k.1 k.2.1) 7)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤ Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 1))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj (fun q=>q.leftExponent.support) pool
          (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2)
          (fun x=>(‖commonSelector p (fun _=>1) k.2.1 x.quotientSupport‖:ℂ))
          false Ψ m slots lists weights omega₂
          ((physicalScales (Z^r) k.1 k.2.1) 8)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤ Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      Z^(-r-2*ell-V)*CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
        varyingReopenedRow p hg pool Q (β I) Ψ m (cubicIdealGenerator I)
          (fun v U=>mark v U*W (primeProductNorm p U)) z) (Z^M)≤
        Czero*Γ^2*Z^(M-ell+3*eta+eps*(5*ell+2*r+7*eta))+
        C*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*
          Z^((2*Lcap+15*eta+tau)*eps+eps)+Ctail*Γ^2*Z^(-saving) :=by
  obtain ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,he⟩:=original_dyadic_priority_budget om rowMajorant a b ha hs Lcap hcap hb
  refine ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro eps heps J
  obtain ⟨C,hC,hret⟩:=he eps heps J
  obtain ⟨Cz,Ct,hCz,hCt,hbranches⟩:=original_dyadic_zero_tail om b Mmax Lcap eta tau (saving+eta) eps
    (fun y hy=>(hs hy).2) hMmax hcap heta htau heps
  refine ⟨C,Cz,Ct,hC,hCz,hCt,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc hpr pool Q labels β Ψ m slots lists weights Z M r ell V Γ theta Benergy
    hZ hbin hM hF hMcap hell hV hr hbZ hQpool hQ hrcap hellcap hΨ hΓ hB hsf hn hβ hlabels hslots hweights
    mark Y cutoff W source keys hleft hright
  have hz:0<Z:=by linarith
  have hZ1:1<Z:=by linarith
  have hK:0<Z^M:=Real.rpow_pos_of_pos hz _
  have he':=original_global_physical_energy p hp hcop hg hinj hc hpr pool Q hQpool labels hn β Ψ m mark W
    (Z^M) Y hK cutoff (fun _ _ _ _ _ _ _=>Real.rpow_nonneg hz.le _)
    (fun x hx _ _=>first_dyadic_original_cap p hp pool Q Z M r ell V eta tau Lcap hZ1 hbin hM hF hQ x hx)
    (fun _=>1) (by intro i;norm_num)
  have hret':=hret p hp hg hinj hcop hc hpr pool Q labels β Ψ m slots lists weights Z M r ell V eta tau Lcap Γ
    (Z^M) theta Benergy hZ hbin hM hF hQ hrcap hellcap hcap le_rfl heta heta1 htau.le htau1 hΨ hΓ hK hB hsf hn hβ hleft hright
  obtain ⟨hz',ht'⟩:=hbranches p hp hcop hg hinj hc pool Q labels β Ψ m slots lists weights Z M r ell V Γ theta
    hZ1 hbin hM hMcap hell hV hr hF hΓ hbZ hΨ hQ hn hlabels hβ hslots hweights
  have hfactor:Z^(-r-2*ell-V)≤ Z^eta:=Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith)
  have htail:Z^(-r-2*ell-V)*‖reopenedPhysicalSourceSum pool Q labels β (fun q D I=>
        canonicalCubeDualTail p hp hg pool q D Ψ Ψ m m (cubicIdealGenerator I)
          (fun U=>mark q.rightExponent U*W (primeProductNorm p U))
          (fun U=>mark q.leftExponent U*W (primeProductNorm p U)) rowMajorant (Z^M)
          (reopenedPhysicalCutoff p q I (cutoff q D I)))‖≤ Ct*Γ^2*Z^(-saving):=by
    have ht'':_≤ Ct*Γ^2*Z^(-(saving+eta)):=ht'
    apply (mul_le_mul hfactor ht'' (norm_nonneg _) (Real.rpow_nonneg hz.le _)).trans
    apply le_of_eq
    rw [show Z^eta*(Ct*Γ^2*Z^(-(saving+eta)))=(Ct*Γ^2)*(Z^eta*Z^(-(saving+eta))) by ring,
      ←Real.rpow_add hz]
    congr 2
    ring
  have hall:=mul_le_mul_of_nonneg_left he' (Real.rpow_nonneg hz.le (-r-2*ell-V))
  simp only [mul_add] at hall
  apply hall.trans
  have hr':Z^(-r-2*ell-V)*((Z^M)*‖originalRetainedFamily p hp hg pool Q labels β Ψ m mark W rowMajorant (Z^M) Y cutoff (fun _=>1)‖)≤
      C*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*Z^((2*Lcap+15*eta+tau)*eps+eps):=by
    simpa only [mul_assoc] using hret'
  exact add_le_add (add_le_add hz' hr') htail

end InverseMoment

end

namespace InverseMoment
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open scoped BigOperators Classical
open Eisenstein CompletedGauss CanonicalRowCompletion
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic CanonicalRowCompletion IdealDivisorBound
local notation "O" => Eisenstein.O

theorem marked_large_cube_sum_comm (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0<X) (d : Ideal O → ℂ) :
    (∑'I:Ideal O,∑'B:Ideal O,largeCubeCoefficient H₀ B*CompletedGauss.summand Ψ W X I B*d (I*B^3)) =
      ∑'B:Ideal O,∑'I:Ideal O,largeCubeCoefficient H₀ B*CompletedGauss.summand Ψ W X I B*d (I*B^3) := by
  let a : Ideal O×Ideal O → ℂ := fun p=>largeCubeCoefficient H₀ p.2*CompletedGauss.summand Ψ W X p.1 p.2*d (p.1*p.2^3)
  have hf : (Function.support a).Finite :=
    (completedIdealT_finite_support Ψ W hW X hX).subset (by
      intro p hp
      exact fun h=>hp (by simp only [a,h,mul_zero,zero_mul]))
  have hs : Summable a := summable_of_hasFiniteSupport hf
  let e := Equiv.prodComm (Ideal O) (Ideal O)
  have ht : Summable (fun p=>a (e p)) := e.summable_iff.mpr hs
  calc
    _ = ∑'p:Ideal O×Ideal O,a p := hs.tsum_prod.symm
    _ = ∑'p:Ideal O×Ideal O,a (e p) := (e.tsum_eq a).symm
    _ = _ := ht.tsum_prod

theorem marked_large_cube_sum_finite (S : Finset (Ideal O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P) (Ψ : O →* ℂ) (m f z : O) (hm : ∀P∈S,m∈P)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ : ℝ) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤ b) (hD : b*X ≤ D) (d : Ideal O → ℂ) :
    (∑'I:Ideal O,∑'B:Ideal O,largeCubeCoefficient H₀ B*CompletedGauss.summand (rowTwist Ψ m f z) W X I B*d (I*B^3)) =
      ∑B∈outsideIdealsUpTo S D,largeCubeCoefficient H₀ B*
        ∑'I:Ideal O,CompletedGauss.summand (rowTwist Ψ m f z) W X I B*d (I*B^3) := by
  rw [marked_large_cube_sum_comm _ W hWc X H₀ hX d]
  simp only [mul_assoc, tsum_mul_left]
  apply tsum_eq_sum
  intro B hB
  have hz : ∀I:Ideal O,CompletedGauss.summand (rowTwist Ψ m f z) W X I B=0 := by
    intro I
    by_contra hn
    exact hB (summand_cube_support S D hSp Ψ m f z hm W b X hX hW hD I B hn)
  simp only [hz,tsum_zero,mul_zero,zero_mul]

theorem marked_inner_completed_sum (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (hX : 0<X)
    (B : Ideal O) (hB : B≠0) (d : Ideal O → ℂ) :
    (∑'I:Ideal O,CompletedGauss.summand Ψ W X I B*d (I*B^3)) =
      (cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) *
        ∑'I:Ideal O,columnWeight Ψ I * W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))*d (I*B^3) := by
  have hN : 0 < (Ideal.absNorm B:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one B hB)
  have hY : 0 < X/(Ideal.absNorm B:ℝ)^3 := div_pos hX (pow_pos hN _)
  have ht (I:Ideal O) : CompletedGauss.summand Ψ W X I B =
      (cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) *
        (columnWeight Ψ I * W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))) := by
    have harg : (Ideal.absNorm I:ℝ)*(Ideal.absNorm B:ℝ)^3/X =
        (Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3) := by
      rw [div_div_eq_mul_div]
    have hn := vstar_source_normalization Ψ W (X/(Ideal.absNorm B:ℝ)^3) hY I
    calc
      _ = cubeWeight Ψ B * (columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I:ℝ):ℂ) *
          Vstar W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))) := by
        rw [CompletedGauss.summand,harg]
        ring
      _ = _ := by rw [hn]; ring
  simp_rw [ht]
  simp only [mul_assoc, tsum_mul_left]

end
end InverseMoment

namespace InverseMoment
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open scoped BigOperators Classical
open Eisenstein CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic CanonicalRowCompletion IdealDivisorBound
local notation "O" => Eisenstein.O

theorem marked_selected_column_sum (F : Finset (Ideal O))
    (hF : ∀I∈F,quadraticIdealAdmissible I)
    (Ψ : O →* ℂ) (m f z : O) (W : ℕ → ℂ) (d : Ideal O → ℂ) :
    let p := CanonicalRowCompletion.poolPrimary F
    let hp := CanonicalRowCompletion.poolPrimary_ne_zero F hF
    letI : ∀i:primePool F,(Ideal.span {p i}).IsMaximal :=
      fun i=>by rw [CanonicalRowCompletion.poolPrimary_span F hF i]; infer_instance
    let hcop := CanonicalRowCompletion.poolPrimary_coprime F hF
    let hg := CanonicalRowCompletion.poolPrimary_good F hF
    (∑I∈F,columnWeight (rowTwist Ψ m f z) I * W (Ideal.absNorm I)*d I) =
      ∑S∈(Finset.univ:Finset (primePool F)).powerset,
        canonicalSourceCoefficient p hg Ψ m f (fun T=>CanonicalRowCompletion.selectedIdealTest F W T*d (∏i∈T,i.val)) S *
          primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S z := by
  dsimp only
  let : ∀i:primePool F,
      (Ideal.span {CanonicalRowCompletion.poolPrimary F i}).IsMaximal :=
    fun i=>by rw [CanonicalRowCompletion.poolPrimary_span F hF i]; infer_instance
  rw [CanonicalRowCompletion.sum_selected_ideals F (fun I hI=>(hF I hI).2.1)]
  apply Finset.sum_congr rfl
  intro S hS
  have hspan : (Ideal.span {∏i∈S,CanonicalRowCompletion.poolPrimary F i}) = ∏i∈S,i.val := by
    rw [span_finset_prime_product]
    exact Finset.prod_congr rfl (fun i _=>CanonicalRowCompletion.poolPrimary_span F hF i)
  have hpr (i:primePool F) :
      lambda^2∣CanonicalRowCompletion.poolPrimary F i-1 :=
    (primaryIdealPrime_spec i.val (CanonicalRowCompletion.poolPrimary_ne_zero F hF i)).2.2.2
  have h := columnWeight_finset (CanonicalRowCompletion.poolPrimary F)
    (CanonicalRowCompletion.poolPrimary_ne_zero F hF)
    (CanonicalRowCompletion.poolPrimary_coprime F hF)
    (CanonicalRowCompletion.poolPrimary_good F hF) hpr S Ψ m f z
    (fun T=>CanonicalRowCompletion.selectedIdealTest F W T*d (∏i∈T,i.val))
  rw [hspan] at h
  rw [←h]
  unfold CanonicalRowCompletion.selectedIdealTest
  split_ifs <;> simp ; ring

theorem marked_weighted_column_tsum_eq (S : Finset (Ideal O)) (D : ℕ)
    (hSp : ∀ P∈S,Prime P) (Ψ : O →* ℂ) (m f z : O) (hm : ∀ P∈S,m∈P)
    (W : ℝ → ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀ t,W t≠0 → t≤ b) (hD : b*X≤ D) (d : Ideal O → ℂ) :
    (∑' I:Ideal O,columnWeight (rowTwist Ψ m f z) I*W ((Ideal.absNorm I:ℝ)/X)*d I) =
      ∑ I∈CanonicalRowCompletion.outsideSquarefreeIdeals S D,
        columnWeight (rowTwist Ψ m f z) I*W ((Ideal.absNorm I:ℝ)/X)*d I := by
  apply tsum_eq_sum
  intro I hI
  have hz : columnWeight (rowTwist Ψ m f z) I*W ((Ideal.absNorm I:ℝ)/X)=0 := by
    by_contra hn
    exact hI (weighted_column_support S D hSp Ψ m f z hm W b X hX hW hD hn)
  rw [hz,zero_mul]

theorem marked_complete_pool_eq_global (S : Finset (Ideal O)) (D : ℕ)
    (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ → ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀ t,W t≠0 → t≤ b) (hD : b*X≤ D) (d : Ideal O → ℂ) :
    let F := CanonicalRowCompletion.outsideSquarefreeIdeals S D
    let hF := CanonicalRowCompletion.outsideSquarefree_admissible S D hbad
    letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    fixedChildRow (poolPrimary F)
      (poolPrimary_good F hF) Finset.univ Ψ m
      (fun T=>W (primeProductNorm (poolPrimary F) T/X)*d (∏i∈T,i.val)) f z =
    ∑' I:Ideal O,columnWeight (rowTwist Ψ (m*excludedGenerator S) f z) I*
      W ((Ideal.absNorm I:ℝ)/X)*d I := by
  let F := CanonicalRowCompletion.outsideSquarefreeIdeals S D
  have hF := CanonicalRowCompletion.outsideSquarefree_admissible S D hbad
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  symm
  rw [marked_weighted_column_tsum_eq S D hSp Ψ (m*excludedGenerator S) f z
    (fun P hP=>P.mul_mem_left m (excludedGenerator_mem S hP)) W b X hX hW hD d]
  have he := marked_selected_column_sum F hF Ψ (m*excludedGenerator S) f z (fun n=>W (n/X)) d
  dsimp only at he
  rw [he]
  unfold fixedChildRow
  apply Finset.sum_congr rfl
  intro T hT
  rw [canonicalSourceCoefficient_fixed_mask _ _ Ψ m (excludedGenerator S) f _ T
    (outside_pool_fixed_mask S D hbad hSp T)]
  have ht := CanonicalRowCompletion.selectedIdealTest_outside S D hbad hSp W b X hX hW hD T
  simp only [canonicalSourceCoefficient,secondChildColumn]
  rw [ht]
  ring

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic CanonicalRowCompletion IdealDivisorBound
local notation "O" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i=>Ideal.span {p i}))

omit [DecidableEq σ] in
include hinj in
theorem prime_dvd_span_primeProduct (S : Finset ι) (v : ι→ℕ) (i : ι) :
    (Ideal.span {p i}:Ideal O)∣Ideal.span {primeProduct p S v} ↔ i∈S ∧ 0<v i := by
  simp only [primeProduct,span_finset_prime_product,←Ideal.span_singleton_pow]
  rw [←dvd_iff_emultiplicity_pos,primeIdealProduct_emultiplicity (fun i=>Ideal.span {p i}) hinj]
  by_cases hi : i∈S <;> simp [hi]

omit [DecidableEq σ] in
include hinj in
theorem prime_dvd_reopened_index (S : Finset ι) (v : ι→₀ℕ) (i : ι) :
    (Ideal.span {p i}:Ideal O)∣(Ideal.span {∏k∈S,p k})*(Ideal.span {primeProduct p v.support v})^3 ↔
      i∈S∪v.support := by
  have hi : Prime (Ideal.span {p i}:Ideal O) := Ideal.prime_of_isPrime (NeZero.ne _) inferInstance
  have hs := prime_dvd_span_primeProduct p hinj S (fun _=>1) i
  simp only [primeProduct,pow_one,Nat.zero_lt_one,and_true] at hs
  rw [hi.dvd_mul,hi.dvd_pow_iff_dvd (by decide : (3:ℕ)≠0),hs,
    prime_dvd_span_primeProduct p hinj v.support v i,Finset.mem_union]
  have hv : i∈v.support ↔ 0<v i := by rw [Finsupp.mem_support_iff]; omega
  tauto

include hinj in

omit [DecidableEq σ] in
theorem reopened_whole_mark_divisibility (slots : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (S : Finset ι) (v : ι→₀ℕ) :
    primeMark slots lists a (S∪v.support) =
    ∏j∈slots,∑i∈lists j,if (Ideal.span {p i}:Ideal O)∣
      (Ideal.span {∏k∈S,p k})*(Ideal.span {primeProduct p v.support v})^3 then a j i else 0 := by
  unfold primeMark primeSlot
  simp_rw [prime_dvd_reopened_index p hinj]

theorem reopened_mark_priority (slots : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (S : Finset ι) (v : ι→₀ℕ) :
    primeMark slots lists a (S∪v.support) =
      ∑J∈slots.powerset,primeMark J lists a v.support *
        primeMark (slots\J) (fun j=>lists j\v.support) a S := by
  rw [Finset.union_comm,primeMark_priority]
  simp only [primeMark_residual_lists]

end
end InverseMoment

namespace InverseMoment
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open scoped BigOperators Classical
open Eisenstein CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic CanonicalRowCompletion IdealDivisorBound
local notation "O" => Eisenstein.O

def indexedIdealMark {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (primes : ι→Ideal O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (I : Ideal O) : ℂ :=
  ∏j∈slots,∑i∈lists j,if primes i∣I then a j i else 0

theorem complete_pool_mark {σ : Type*} [DecidableEq σ]
    (F : Finset (Ideal O)) (hF : ∀ I∈F,quadraticIdealAdmissible I)
    (slots : Finset σ) (lists : σ→Finset (primePool F)) (a : σ→primePool F→ℂ)
    (T : Finset (primePool F)) :
    indexedIdealMark (fun i:primePool F=>i.val) slots lists a (∏i∈T,i.val) =
      primeMark slots lists a T := by
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have hinj : Function.Injective (fun i:primePool F=>Ideal.span {poolPrimary F i}) := by
    intro i j h
    dsimp only at h
    rw [poolPrimary_span F hF i,poolPrimary_span F hF j] at h
    exact Subtype.ext h
  have he := reopened_whole_mark_divisibility (poolPrimary F) hinj slots lists a T 0
  simp only [Finsupp.support_zero,Finset.union_empty,primeProduct,Finset.prod_empty,
    Ideal.span_singleton_one,←Ideal.one_eq_top,one_pow,mul_one] at he
  have hspan : Ideal.span {∏i∈T,poolPrimary F i}=∏i∈T,i.val := by
    rw [span_finset_prime_product]
    exact Finset.prod_congr rfl (fun i _=>poolPrimary_span F hF i)
  rw [hspan] at he
  simpa only [indexedIdealMark,poolPrimary_span F hF] using he.symm

theorem finiteCanonicalMarkedRow_complete_global {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ→ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀ t,W t≠0→t≤ b) (hD : b*X≤ D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→ℂ) :
    let F := CanonicalRowCompletion.outsideSquarefreeIdeals S D
    let hF := CanonicalRowCompletion.outsideSquarefree_admissible S D hbad
    letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    finiteCanonicalMarkedRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ Ψ m f z slots lists a W X =
    ∑' I:Ideal O,columnWeight (rowTwist Ψ (m*excludedGenerator S) f z) I*
      indexedIdealMark (fun i:primePool F=>i.val) slots lists a I*W ((Ideal.absNorm I:ℝ)/X) := by
  let F := CanonicalRowCompletion.outsideSquarefreeIdeals S D
  have hF := CanonicalRowCompletion.outsideSquarefree_admissible S D hbad
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  have he := marked_complete_pool_eq_global S D hbad hSp Ψ m f z W b X hX hW hD
    (indexedIdealMark (fun i:primePool F=>i.val) slots lists a)
  dsimp only at he
  have hmark : (fun T:Finset (primePool F)=>W (primeProductNorm (poolPrimary F) T/X)*
      indexedIdealMark (fun i:primePool F=>i.val) slots lists a (∏i∈T,i.val)) =
      (fun T=>primeMark slots lists a T*W (primeProductNorm (poolPrimary F) T/X)) := by
    funext T
    rw [complete_pool_mark F hF slots lists a T,mul_comm]
  rw [hmark] at he
  unfold finiteCanonicalMarkedRow
  calc
    _ = _ := he
    _ = _ := tsum_congr (fun I=>by ring)

end
end InverseMoment

namespace InverseMoment
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open scoped BigOperators Classical
open Eisenstein CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic CanonicalRowCompletion IdealDivisorBound
local notation "O" => Eisenstein.O

def outsideCanonicalMarkedRow {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (Ψ : O →* ℂ) (m f z : O) (slots : Finset σ)
    (lists : σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→ℂ)
    (W : ℝ→ℂ) (X : ℝ) : ℂ :=
  let F := CanonicalRowCompletion.outsideSquarefreeIdeals S D
  let hF := CanonicalRowCompletion.outsideSquarefree_admissible S D hbad
  letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  finiteCanonicalMarkedRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ Ψ m f z slots lists a W X

theorem outsideCanonicalMarkedRow_cube_split {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ→ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hX : 0<X) (hW : ∀ t,W t≠0→t≤ b) (hD : b*X≤ D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→ℂ) :
    let Ψrow := rowTwist Ψ (m*excludedGenerator S) f z
    let mark := indexedIdealMark (fun i:primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)=>i.val) slots lists a
    (Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X =
      (∑' H:Ideal O,if (Ideal.absNorm H:ℝ)<H₀ then
        (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψrow H*
          markedCompletedT Ψrow W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark (H^3*I)) else 0) +
      ∑ B∈outsideIdealsUpTo S D,largeCubeCoefficient H₀ B*
        ∑' I:Ideal O,CompletedGauss.summand Ψrow W X I B*mark (I*B^3) := by
  dsimp only
  unfold outsideCanonicalMarkedRow
  rw [finiteCanonicalMarkedRow_complete_global S D hbad hSp Ψ m f z W b X hX hW hD]
  rw [marked_completed_cube_inverse_split _ W hWc X H₀ hX]
  rw [marked_large_cube_sum_finite S D hSp Ψ (m*excludedGenerator S) f z
    (fun P hP=>P.mul_mem_left m (excludedGenerator_mem S hP)) W hWc b X H₀ hX hW hD]

theorem outsideCanonicalMarkedRow_reopened {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ→ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hX : 0<X) (hW : ∀ t,W t≠0→t≤ b) (hD : b*X≤ D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→ℂ) :
    let Ψrow := rowTwist Ψ (m*excludedGenerator S) f z
    let mark := indexedIdealMark (fun i:primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)=>i.val) slots lists a
    (Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X =
      (∑' H:Ideal O,if (Ideal.absNorm H:ℝ)<H₀ then
        (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψrow H*
          markedCompletedT Ψrow W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark (H^3*I)) else 0) +
      ∑ B∈outsideIdealsUpTo S D,
        (largeCubeCoefficient H₀ B*cubeWeight Ψrow B*
          (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹)*
        ∑' I:Ideal O,columnWeight Ψrow I*W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))*mark (I*B^3) := by
  rw [outsideCanonicalMarkedRow_cube_split S D hbad hSp Ψ m f z W hWc b X H₀ hX hW hD]
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro B hB
  rw [marked_inner_completed_sum _ W X hX B (outsideIdealsUpTo_ne_bot S D B hB)]
  ring

end
end InverseMoment

namespace InverseMoment
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open scoped BigOperators Classical
open Eisenstein CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic CanonicalRowCompletion IdealDivisorBound
local notation "O" => Eisenstein.O

theorem complete_pool_whole_cube_mark {σ : Type*} [DecidableEq σ]
    (F : Finset (Ideal O)) (hF : ∀ I∈F,quadraticIdealAdmissible I)
    (slots : Finset σ) (lists : σ→Finset (primePool F)) (a : σ→primePool F→ℂ)
    (T : Finset (primePool F)) (v : primePool F→₀ℕ) :
    indexedIdealMark (fun i:primePool F=>i.val) slots lists a
      ((∏i∈T,i.val)*cubeIdeal F v^3) = primeMark slots lists a (T∪v.support) := by
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have hinj : Function.Injective (fun i:primePool F=>Ideal.span {poolPrimary F i}) := by
    intro i j h
    dsimp only at h
    rw [poolPrimary_span F hF i,poolPrimary_span F hF j] at h
    exact Subtype.ext h
  have he := reopened_whole_mark_divisibility (poolPrimary F) hinj slots lists a T v
  have hspan : Ideal.span {∏i∈T,poolPrimary F i}=∏i∈T,i.val := by
    rw [span_finset_prime_product]
    exact Finset.prod_congr rfl (fun i _=>poolPrimary_span F hF i)
  rw [hspan,cubeIdeal_eq_primeProduct_span F hF v] at he
  simpa only [indexedIdealMark,poolPrimary_span F hF] using he.symm

theorem reopened_marked_global_column {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (b X : ℝ) (hb : 0≤ b) (hX : 0<X)
    (hW : ∀ t,W t≠0→t≤ b) (hD : b*X≤ D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→ℂ)
    (v : primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→₀ℕ) :
    let F := CanonicalRowCompletion.outsideSquarefreeIdeals S D
    let hF := CanonicalRowCompletion.outsideSquarefree_admissible S D hbad
    letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    let Y := X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3
    (∑' I:Ideal O,columnWeight (rowTwist Ψ (m*excludedGenerator S) f z) I*W ((Ideal.absNorm I:ℝ)/Y)*
      indexedIdealMark (fun i:primePool F=>i.val) slots lists a (I*cubeIdeal F v^3)) =
    fixedChildRow (poolPrimary F)
      (poolPrimary_good F hF) Finset.univ Ψ m
      (fun T=>primeMark slots lists a (T∪v.support)*W (primeProductNorm (poolPrimary F) T/Y)) f z := by
  let F := CanonicalRowCompletion.outsideSquarefreeIdeals S D
  have hF := CanonicalRowCompletion.outsideSquarefree_admissible S D hbad
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  let Y := X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3
  have hN := norm_at_least_one (cubeIdeal F v) (cubeIdeal_ne_zero F v)
  have hY : 0<Y := by dsimp [Y];positivity
  have hYD : b*Y≤ D := (mul_le_mul_of_nonneg_left
    (div_le_self hX.le (one_le_pow₀ hN)) hb).trans hD
  have he := marked_complete_pool_eq_global S D hbad hSp Ψ m f z W b Y hY hW hYD
    (fun I=>indexedIdealMark (fun i:primePool F=>i.val) slots lists a (I*cubeIdeal F v^3))
  dsimp only at he ⊢
  rw [←he]
  congr 1
  funext T
  rw [complete_pool_whole_cube_mark F hF slots lists a T v,mul_comm]

end
end InverseMoment

namespace InverseMoment
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open scoped BigOperators Classical
open Eisenstein CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic CanonicalRowCompletion IdealDivisorBound
local notation "O" => Eisenstein.O

def markedReopenedCubeBin {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ)
    (Q : Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (X H₀ : ℝ)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→ℂ) : ℂ :=
  let F := CanonicalRowCompletion.outsideSquarefreeIdeals S D
  let Ψrow := rowTwist Ψ (m*excludedGenerator S) f z
  ∑ v∈Q,(largeCubeCoefficient H₀ (cubeIdeal F v)*cubeWeight Ψrow (cubeIdeal F v)*
    (Real.sqrt (X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3):ℂ)⁻¹)*
    ∑' I:Ideal O,columnWeight Ψrow I*W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3))*
      indexedIdealMark (fun i:primePool F=>i.val) slots lists a (I*cubeIdeal F v^3)

theorem original_marked_split_to_bins {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hX : 0<X) (hW : ∀ t,W t≠0→t≤ b) (hD : b*X≤ D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→ℂ) :
    let F := CanonicalRowCompletion.outsideSquarefreeIdeals S D
    let Ψrow := rowTwist Ψ (m*excludedGenerator S) f z
    let mark := indexedIdealMark (fun i:primePool F=>i.val) slots lists a
    (Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X =
      (∑' H:Ideal O,if (Ideal.absNorm H:ℝ)<H₀ then
        (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψrow H*
          markedCompletedT Ψrow W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark (H^3*I)) else 0) +
      markedReopenedCubeBin S D ((outsideIdealsUpTo S D).image (cubeIndex F)) Ψ m f z W X H₀ slots lists a := by
  rw [outsideCanonicalMarkedRow_reopened S D hbad hSp Ψ m f z W hWc b X H₀ hX hW hD]
  dsimp only
  rw [sum_outside_cubeIndex S D]
  rfl

theorem markedReopenedCubeBin_eq_varying {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Q : Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (b X H₀ : ℝ) (hb : 0≤ b) (hX : 0<X)
    (hW : ∀ t,W t≠0→t≤ b) (hD : b*X≤ D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→ℂ) :
    let F := CanonicalRowCompletion.outsideSquarefreeIdeals S D
    let hF := CanonicalRowCompletion.outsideSquarefree_admissible S D hbad
    letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    let β := fun v=>largeCubeCoefficient H₀ (cubeIdeal F v)*
      cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)*
      (Real.sqrt (X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3):ℂ)⁻¹
    markedReopenedCubeBin S D Q Ψ m f z W X H₀ slots lists a =
      varyingReopenedRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ Q β Ψ m f
        (fun v T=>primeMark slots lists a (T∪v.support)*
          W (primeProductNorm (poolPrimary F) T/(X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3))) z := by
  let F := CanonicalRowCompletion.outsideSquarefreeIdeals S D
  have hF := CanonicalRowCompletion.outsideSquarefree_admissible S D hbad
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  unfold markedReopenedCubeBin varyingReopenedRow
  dsimp only
  apply Finset.sum_congr rfl
  intro v hv
  rw [reopened_marked_global_column S D hbad hSp Ψ m f z W b X hb hX hW hD slots lists a v]
  rw [cubeWeight_row_factor,cubeIdeal_row F hF v z]
  unfold fixedChildRow
  simp only [Finset.mul_sum,secondChildColumn,canonicalSourceCoefficient]
  apply Finset.sum_congr rfl
  intro T hT
  ring

end
end InverseMoment

namespace InverseMoment
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Eisenstein CompletedGauss CanonicalRowCompletion
open CanonicalCubeSeparation JointLogSeparation FirstPassCubeLabels SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic CanonicalRowCompletion IdealDivisorBound
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem varyingReopenedRow_integrand
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (β : (ι →₀ ℕ) → ℂ)
    (Ψ : O →* ℂ) (m f z : O) (H : (ι→₀ℕ)→Finset ι → ℂ) :
    varyingReopenedRow p hg pool Q β Ψ m f H z =
      ∑ v ∈ Q, ∑ T ∈ pool.powerset,
        β v * (multiplicityRow p hg pool v z ^ 3 *
          canonicalSourceCoefficient p hg Ψ m f (fun _ => 1) T *
          primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) T z) * H v T := by
  unfold varyingReopenedRow
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro T hT
  simp only [canonicalSourceCoefficient]
  ring

include hp in
theorem varying_canonical_bin_separation
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (β : (ι →₀ ℕ) → ℂ)
    (n : (ι →₀ ℕ) → ℝ) (mark : (ι→₀ℕ)→Finset ι→ℂ) (Ψ : O →* ℂ) (m f z : O) (B ell X : ℝ)
    (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : ∀ v ∈ Q, B ≤ n v) (hn' : ∀ v ∈ Q, n v ≤ Real.exp 1*B) :
    (∑ v ∈ Q, (β v * (n v : ℂ)⁻¹ * (Real.sqrt (X/(n v)^3) : ℂ)⁻¹) *
      multiplicityRow p hg pool v z ^ 3 *
      fixedChildRow p hg pool Ψ m
        (fun T => mark v T*W (primeProductNorm p T/(X/(n v)^3))) f z) =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
        ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
          varyingReopenedRow p hg pool Q
            (separatedCubeCoefficient β n B ξ) Ψ m f
            (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z := by
  let A : (ι →₀ ℕ) → Finset ι → ℂ := fun v T =>
    multiplicityRow p hg pool v z ^ 3 *
      canonicalSourceCoefficient p hg Ψ m f (fun _ => 1) T *
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) T z*mark v T
  have hsep := reopening_finite_sum W a b ha hs hW V hV Q pool.powerset β A n
    (primeProductNorm p) B ell X hB hell hX hn hn'
    (fun T _ => primeProductNorm_pos p hp T)
  calc
    _ = ∑ v ∈ Q, ∑ T ∈ pool.powerset, (β v * A v T) *
        ((n v : ℂ)⁻¹ * (Real.sqrt (X/(n v)^3) : ℂ)⁻¹ *
          W (primeProductNorm p T/(X/(n v)^3))) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [fixedChildRow_coefficient_expansion p hg, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      dsimp only [A]
      ring
    _ = _ := by
      rw [hsep]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [varyingReopenedRow_integrand p hg]
      simp only [A, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro T hT
      dsimp only [columnLog]
      ring

end
end InverseMoment

namespace InverseMoment
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Eisenstein CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
open CanonicalCubeSeparation JointLogSeparation
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic CanonicalRowCompletion IdealDivisorBound
local notation "O" => Eisenstein.O

theorem markedReopenedCubeBin_separated {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Q : Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ)
    (a b : ℝ) (ha : 0<a) (hb : 0≤ b) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (V : 𝓢(ℝ,ℂ))
    (hV : ∀ u,|u|≤ columnWindowRadius a b→V u=1)
    (B ell X H₀ : ℝ) (hB : 0<B) (hell : 0<ell) (hX : X=B^3*ell)
    (hD : b*X≤ D)
    (hn : ∀ v∈Q,B≤(Ideal.absNorm (cubeIdeal (CanonicalRowCompletion.outsideSquarefreeIdeals S D) v):ℝ))
    (hn' : ∀ v∈Q,(Ideal.absNorm (cubeIdeal (CanonicalRowCompletion.outsideSquarefreeIdeals S D) v):ℝ)≤ Real.exp 1*B)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)))
    (weights : σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→ℂ) :
    let F := CanonicalRowCompletion.outsideSquarefreeIdeals S D
    let hF := CanonicalRowCompletion.outsideSquarefree_admissible S D hbad
    letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    let β := fun v=>reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)
    let n := fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)
    markedReopenedCubeBin S D Q Ψ m f z W X H₀ slots lists weights =
      ((B*Real.sqrt ell:ℝ):ℂ)⁻¹ * ∫ ξ:ℝ,reopeningCoefficient W a b ha hs hW ξ*
        varyingReopenedRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ Q
          (separatedCubeCoefficient β n B ξ) Ψ m f
          (fun v T=>primeMark slots lists weights (T∪v.support)*frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z := by
  let F := CanonicalRowCompletion.outsideSquarefreeIdeals S D
  have hF := CanonicalRowCompletion.outsideSquarefree_admissible S D hbad
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  let β := fun v=>reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)
  let n := fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)
  have hXp : 0<X := hX ▸ mul_pos (pow_pos hB _) hell
  have hupper : ∀ t,W t≠0→t≤ b := fun t ht=>(hs ht).2
  dsimp only
  rw [←varying_canonical_bin_separation (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_good F hF) W a b ha hs hW V hV
    Finset.univ Q β n (fun v T=>primeMark slots lists weights (T∪v.support))
    Ψ m f z B ell X hB hell hX hn hn']
  unfold markedReopenedCubeBin
  dsimp only
  apply Finset.sum_congr rfl
  intro v hv
  rw [reopened_marked_global_column S D hbad hSp Ψ m f z W b X hb hXp hupper hD slots lists weights v]
  rw [cubeWeight_row_factor,cubeIdeal_row F hF v z]
  have hc := cube_coefficient_restore H₀ (rowTwist Ψ (m*excludedGenerator S) f 1)
    (cubeIdeal F v) (cubeIdeal_ne_zero F v)
  have hc' : β v*(n v:ℂ)⁻¹=largeCubeCoefficient H₀ (cubeIdeal F v)*
      cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v) := by
    simpa only [β,n,Complex.ofReal_natCast] using hc
  rw [hc']
  ring

end
end InverseMoment

namespace InverseMoment
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Eisenstein CompletedGauss CanonicalRowCompletion
open CanonicalCubeSeparation JointLogSeparation FirstPassCubeLabels SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic CanonicalRowCompletion IdealDivisorBound
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem varying_separated_canonical_integrable
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (β : (ι →₀ ℕ) → ℂ)
    (n : (ι →₀ ℕ) → ℝ) (mark : (ι→₀ℕ)→Finset ι→ℂ) (Ψ : O →* ℂ) (m f z : O)
    (b V : 𝓢(ℝ,ℂ)) (B ell : ℝ) :
    Integrable (fun ξ : ℝ => b ξ *
      varyingReopenedRow p hg pool Q (separatedCubeCoefficient β n B ξ)
        Ψ m f (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z) := by
  let A : (ι →₀ ℕ) → Finset ι → ℂ := fun v T =>
    multiplicityRow p hg pool v z ^ 3 *
      canonicalSourceCoefficient p hg Ψ m f (fun _ => 1) T *
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) T z*mark v T
  have hi := reopening_finite_sum_integrable Q pool.powerset β A n (primeProductNorm p) B ell b V
  convert hi using 1
  funext ξ
  rw [varyingReopenedRow_integrand p hg]
  simp only [A,Finset.mul_sum,columnLog]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro T hT
  ring

theorem varying_separated_canonical_family_energy
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O → (ι →₀ ℕ) → ℂ) (n : (ι →₀ ℕ) → ℝ) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (Ψ : O →* ℂ) (m : O) (b V : 𝓢(ℝ,ℂ))
    (B ell K E : ℝ) (d : ℕ) (hB : 0 < B) (hell : 0 < ell) (hK : 0 < K) (hE : 0 ≤ E)
    (hbound : ∀ ξ : ℝ,
      rowFamilyEnergy labels (fun I z =>
        varyingReopenedRow p hg pool Q (separatedCubeCoefficient (β I) n B ξ)
          Ψ m (cubicIdealGenerator I) (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z) K ≤
        E*(1+|ξ|)^(2*d)) :
    rowFamilyEnergy labels (fun I z => ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
      ∫ ξ : ℝ, b ξ *
        varyingReopenedRow p hg pool Q (separatedCubeCoefficient (β I) n B ξ)
          Ψ m (cubicIdealGenerator I) (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z) K ≤
      (B^2*ell)⁻¹ * E*(∫ ξ : ℝ, ‖b ξ‖*(1+|ξ|)^d)^2 := by
  have hb : Integrable (fun ξ : ℝ => ‖b ξ‖*(1+|ξ|)^d) := by
    simpa only [Real.norm_eq_abs,mul_comm] using weighted_schwartz_integrable b d
  have hφ (I : Ideal O) (z : O) : Integrable (fun ξ : ℝ => b ξ *
      varyingReopenedRow p hg pool Q (separatedCubeCoefficient (β I) n B ξ)
        Ψ m (cubicIdealGenerator I) (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z) :=
    varying_separated_canonical_integrable p hg pool Q (β I) n mark Ψ m (cubicIdealGenerator I) z b V B ell
  have hm := rowFamilyEnergy_integral_polynomial labels K hK b
    (fun I z ξ => varyingReopenedRow p hg pool Q (separatedCubeCoefficient (β I) n B ξ)
      Ψ m (cubicIdealGenerator I) (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z)
    d E hE hb hφ hbound
  have hn : ‖((B*Real.sqrt ell : ℝ) : ℂ)⁻¹‖^2 = (B^2*ell)⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (mul_pos hB (Real.sqrt_pos.mpr hell)),inv_pow,mul_pow,Real.sq_sqrt hell.le]
  rw [rowFamilyEnergy_const_mul labels _ K hK, hn]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ (B^2*ell)⁻¹)

end
end InverseMoment

namespace InverseMoment
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Eisenstein CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
open CanonicalCubeSeparation JointLogSeparation
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic CanonicalRowCompletion IdealDivisorBound
local notation "O" => Eisenstein.O

theorem markedReopenedCubeBin_energy
    {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Q : Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D) →₀ ℕ))
    (labels : Finset (Ideal O)) (Ψ : O →* ℂ) (m : O) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hb : 0≤ b) (hs : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (V : 𝓢(ℝ,ℂ))
    (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (B ell X H₀ K E : ℝ) (d : ℕ)
    (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell) (hD : b*X≤ D) (hK : 0 < K) (hE : 0 ≤ E)
    (hn : ∀ v ∈ Q, B ≤ (Ideal.absNorm (cubeIdeal (CanonicalRowCompletion.outsideSquarefreeIdeals S D) v) : ℝ))
    (hn' : ∀ v ∈ Q, (Ideal.absNorm (cubeIdeal (CanonicalRowCompletion.outsideSquarefreeIdeals S D) v) : ℝ) ≤ Real.exp 1*B)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)))
    (weights : σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→ℂ) :
    let F := CanonicalRowCompletion.outsideSquarefreeIdeals S D
    let hF := CanonicalRowCompletion.outsideSquarefree_admissible S D hbad
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    let β := fun I v => reopenedCubeCoefficient H₀
      (rowTwist Ψ (m*excludedGenerator S) (cubicIdealGenerator I) 1) (cubeIdeal F v)
    let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
    (∀ ξ : ℝ, rowFamilyEnergy labels (fun I z =>
      varyingReopenedRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ Q
        (separatedCubeCoefficient (β I) n B ξ) Ψ m (cubicIdealGenerator I)
        (fun v T => primeMark slots lists weights (T∪v.support)*frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z) K ≤
      E*(1+|ξ|)^(2*d)) →
    rowFamilyEnergy labels (fun I z =>
      markedReopenedCubeBin S D Q Ψ m (cubicIdealGenerator I) z W X H₀ slots lists weights) K ≤
      (B^2*ell)⁻¹ * E *
        (∫ ξ : ℝ, ‖reopeningCoefficient W a b ha hs hW ξ‖*(1+|ξ|)^d)^2 := by
  dsimp only
  let F := CanonicalRowCompletion.outsideSquarefreeIdeals S D
  have hF := CanonicalRowCompletion.outsideSquarefree_admissible S D hbad
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  let β := fun I v => reopenedCubeCoefficient H₀
    (rowTwist Ψ (m*excludedGenerator S) (cubicIdealGenerator I) 1) (cubeIdeal F v)
  let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
  intro hbound
  have hrows : (fun I z => markedReopenedCubeBin S D Q Ψ m (cubicIdealGenerator I) z W X H₀ slots lists weights) =
      (fun I z => ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * ∫ ξ : ℝ,
        reopeningCoefficient W a b ha hs hW ξ *
          varyingReopenedRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ Q
            (separatedCubeCoefficient (β I) n B ξ) Ψ m (cubicIdealGenerator I)
            (fun v T => primeMark slots lists weights (T∪v.support)*frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z) := by
    funext I z
    exact markedReopenedCubeBin_separated S D hbad hSp Q Ψ m (cubicIdealGenerator I) z W a b ha hb hs hW V hV
      B ell X H₀ hB hell hX hD hn hn' slots lists weights
  rw [hrows]
  exact varying_separated_canonical_family_energy (poolPrimary F) (poolPrimary_good F hF) Finset.univ Q labels β n (fun v T=>primeMark slots lists weights (T∪v.support)) Ψ m
    (reopeningCoefficient W a b ha hs hW) V B ell K E d hB hell hK hE hbound

end
end InverseMoment

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

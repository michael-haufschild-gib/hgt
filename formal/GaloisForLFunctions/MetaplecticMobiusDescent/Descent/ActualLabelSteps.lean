/-
Actual label steps adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Inversion.InitialCallerWindows

/-!
# Actual label steps

Child bounds of label cells, long-bin geometry and complete short finite sums; uniform physical
and fixed-child steps of the filtered global priority family; live label steps.
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
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open SchwartzPlanePoisson.CanonicalQuadraticSieve
open InverseInitialRayAttachment InverseFirstRayAttachment
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseCanonicalShortAttachment
open Eisenstein CompletedGauss CanonicalRowCompletion 
open CanonicalQuadraticSieve InverseMoment InverseReflectedPhase InverseTerminalWidths CompletedHeight
local notation "Eis"=> Eisenstein.O
universe u v
theorem actual_complete_short_finite_uniform_degree
    (lo hi : ℝ) (hlo : 0< lo) (W : ℝ→ℂ)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar eta : ℝ) (hL : 0≤ L) (hcstar : 0< cstar) (heta : 0< eta)
    (heta1 : eta≤1) (hetac : eta≤ cstar/100000) (rmax K : ℕ) :
    ∃ (degree : ℕ), ∀ (q:ℕ)(_hq:q≠0), ∃ (C Z₀ : ℝ),0< C ∧ 1< Z₀ ∧
    ∀ {σ : Type v} [DecidableEq σ],
    ∀ (m : Eis),m≠0 → ∀ (Z N V M z₀ margin hcut d : ℝ),
      Z₀≤ Z → 0≤ N → 0≤ V → 0≤ M → M≤ L → V≤ L → z₀≤ L → 0≤ hcut → hcut≤ L →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤ Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤ margin →
      V≤ d → hcut≤ d+eta → d≤ cstar/200 →
    ∀ (labels : Finset (Ideal Eis)),
      (∀f∈labels,quadraticSupported f ∧ Squarefree f ∧ (Ideal.absNorm f:ℝ)≤ Z^V) →
    ∀ (T : Finset Eis),(∀k∈T,k≠0 ∧ (Ideal.absNorm (Ideal.span {k}):ℝ)≤ Z^M) →
    ∀ D : ℕ,hi*Z^N≤ D → ∀ slots : Finset σ,slots.card≤ rmax →
    ∀ (lists : σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
      (H : σ→ℝ),
      (slots:Set σ).Pairwise (fun j k=> Disjoint (lists j) (lists k)) →
      (∀j∈slots,1≤ H j) → (∀j∈slots,∀i∈lists j,(Ideal.absNorm i.val:ℝ)≤ H j) →
      (∏j∈slots,H j)≤ Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀n,‖Ψ n‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (θ : ℝ)
      (a : σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ),
      (∀j∈slots,∀i∈lists j,‖a j i‖≤1) →
      let S:=reflectionExcludedPrimes q
      let F:=CanonicalRowCompletion.outsideSquarefreeIdeals S D
      let mark:=indexedIdealMark (fun i:primePool F=> i.val) slots lists a
      Z^(-V)*(∑f∈labels,secondLabelWeight K f*∑k∈T,
        ‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (cubicIdealGenerator f) k)
          (normTwistedSource W θ) (Z^N) (Z^hcut) mark‖^2)≤
        C*(1+‖θ‖)^degree*Z^(N+V-cstar/256) := by
  obtain ⟨degree,hu⟩:=InverseShortCanonicalNormalization.canonical_short_normalized_energy_uniform_degree
    lo hi hlo W hWs hW L cstar eta hL hcstar heta heta1 hetac rmax K
  refine ⟨degree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,he⟩:=hu q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro σ _ m hm Z N V M z₀ margin hcut d hZ hN hV hM hMc hVc hzc hcut0 hcutc
    hRn hmargin hreserve hVd hcutd hd labels hlabels T hT D hD slots hcard lists H hdis hH1 hH hprod
    Ψ hΨ hperiod θ a ha
  dsimp only
  let S:=reflectionExcludedPrimes q
  let F:=CanonicalRowCompletion.outsideSquarefreeIdeals S D
  have hF : ∀I∈F,quadraticIdealAdmissible I:=CanonicalRowCompletion.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q)
  let ilists:slots→Finset (Ideal Eis):=fun j=> idealLists F lists j.val
  let iw:∀j,ilists j→ℂ:=fun j=> idealWeights F lists a j.val
  have hp (j:slots) (P:Ideal Eis) (hP:P∈ilists j) := idealLists_prime_data F hF lists j.val P hP
  have hcap : ∀j:slots,∀P∈ilists j,(Ideal.absNorm P:ℝ)≤ H j.val := by
    intro j P hP
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hP
    exact hH j.val j.property i hi
  have hw : ∀j:slots,∀P:ilists j,‖iw j P‖≤1 := by
    intro j P
    obtain ⟨i,hi,hh⟩:=Finset.mem_image.mp P.property
    change ‖transportCoeff F a j.val P.val‖≤1
    rw [←hh,transportCoeff_val]
    exact ha j.val j.property i hi
  have henergy:=he (σ:=slots) m hm Z N V M z₀ margin hcut d hZ hN hV hM hMc hVc hzc hcut0 hcutc
    hRn hmargin hreserve hVd hcutd hd labels (fun f hf=>(hlabels f hf).2) T hT (by simpa using hcard)
    ilists (fun j:slots=> H j.val) (idealLists_disjoint F slots lists hdis)
    (fun j P hP=>(hp j P hP).1) (fun j P hP=>(hp j P hP).2.1)
    (fun j P hP=>(hp j P hP).2.2.1) (fun j P hP=>(hp j P hP).2.2.2)
    (fun j=> hH1 j.val j.property) hcap (by simpa only [Finset.prod_coe_sort] using hprod)
    Ψ hΨ hperiod θ iw hw
  have hz:0< Z:=zero_lt_one.trans (lt_of_lt_of_le hZ₀ hZ)
  have hn:‖((Z^(-(N+V)/2):ℝ):ℂ)*((Real.sqrt (Z^N):ℝ):ℂ)‖^2=Z^(-V) := by
    rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hz _),Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (Real.rpow_nonneg hz.le _),
      ←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz]
    congr 1
    ring
  have hmark:indexedIdealMark (fun i:primePool F=> i.val) slots lists a=tupleDivisibilityMark ilists iw:=
    funext (indexed_mark_eq_tuple F slots lists a)
  rw [hmark]
  change Z^(-V)*(∑f∈labels,secondLabelWeight K f*∑k∈T,
    ‖markedShortCompletedSum (rowTwist Ψ (ActualFiber.maskElement q m) (cubicIdealGenerator f) k)
      (normTwistedSource W θ) (Z^N) (Z^hcut) (tupleDivisibilityMark ilists iw)‖^2)≤ _
  simp only [norm_mul,mul_pow] at henergy
  have hn':‖((Z^(-(N+V)/2):ℝ):ℂ)‖^2*‖((Real.sqrt (Z^N):ℝ):ℂ)‖^2=Z^(-V):=by
    simpa only [norm_mul,mul_pow] using hn
  simp only [←mul_assoc,hn',←Finset.mul_sum] at henergy
  convert henergy using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros
  ring

end InverseCanonicalShortAttachment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open JointLogSeparation CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseFirstPriorityParents InversePrioritySecondSource InverseMomentGlobalPriorityTail
open InverseWholePriorityRetainedSource RayFourExpansion
local notation "Eis"=> Eisenstein.O
theorem global_priority_filtered_physical_step_uniform_types
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0< lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (window Lcap tau saving:ℝ)(hhi:hi≤ Real.exp window)(hLcap:0≤ Lcap)(htau:0< tau)
    (Jmax:ℕ)(dsmall:ℝ)(hdsmall:0< dsmall)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤ caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤ B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0< loFresh ∧ loFresh≤ hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin Czero Ctail : ℝ,0 ≤ C ∧ 0≤ Cbin ∧ 0≤ Czero ∧ 0≤ Ctail ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, lambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis)
    (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:Finset ι→Finset ι→ℝ)
,
    ∀
        (Y:ℝ) (R:Finset σ→BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : Finset σ→BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      hi≤ b → (slots:Set σ).PairwiseDisjoint lists→slots.card≤ K → 0≤ A → (∀(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ), assigned⊆slots →
    let source:=InverseMomentGlobalRetainedGates.geometrySource p (unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=> extra x.cube) original negative assigned lists) (fun _=> cutoff)) b X;
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core;
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) ∧
      (∀ i,|ρ i| ≤ B₀ i) ∧
      0 ≤ L ∧
      1 < Z ∧
      0 < X ∧
      0 < Y ∧
      0≤ eta ∧
      2≤ Z^eta ∧
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R assigned (index p x))) ∧
      (∀ x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) ∧
      (∀ x∈source,Z^(j-eta) ≤ ‖ringComplex (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) ∧
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) ∧
      (∀ a,‖Ψ a‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels assigned d) ∧
      Jo+(assigned.card+assigned.card) ≤ 2*K ∧
      (slots\assigned).card ≤ K ∧
      (slots\assigned).card ≤ K ∧
      0 ≤ A ∧
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) ∧
      X=Z^(r-Acol-Bfirst-tcount) ∧
      L=eta*Real.log Z ∧
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) ∧
      2≤ Z ∧
      1≤ b ∧
      b≤ Z^(6*eta) ∧
      (∀x∈source,∀i,outerNorms p x i≤ Z^(caps i)) ∧
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤ b*X) ∧
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤ pi) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6→ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6→ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2))) →
      Jo≤ Jmax→0≤ ell+eta→0≤ Bfirst→0≤ j→
      εmass*(r-Acol-Bfirst-tcount)+7*eta/2+dsmall*(3*ell+Bfirst+tcount+5*eta)+
        2*εmass*(2*ell+Bfirst+tcount+4*eta)≤ pi+eta/2→
      (∀x∈original,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤ Z^(ell+eta))→
      (∀x∈original,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤ Z^(ell+eta))→
      (∀x∈original,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=> x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤ Z^(Ractive+eta))→
      (∀x∈original,primeProductNorm p x.firstCommon≤ Z^(Bfirst+eta))→
      (∀x∈original,primeProductNorm p x.quotientSupport≤ Z^(tcount+eta))→
      1≤ Y→1≤ X*Real.exp window→Y≤ Z^Lcap→Y⁻¹≤ Z^Lcap→X*Real.exp window≤ Z^Lcap→
      firstKappa M r ell V delta Acol Bfirst Ractive+(9/2:ℝ)*eta≤ Lcap→
      (∀x∈original,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤ Z^Lcap)→
      (∀x∈original,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤ Z^Lcap)→
      (∀x∈original,‖ringComplex (∏i∈cubeActiveSupport x.cube.support
        (fun i=> x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤ Z^Lcap)→
      (∀x∈original,primeProductNorm p x.firstCommon≤ Z^Lcap)→
      (∀x∈original,primeProductNorm p x.quotientSupport≤ Z^Lcap)→
      (∀G E,0≤ cutoff G E)→
      (∀x∈original,∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p (parent p x)) G E.val
          (X*Real.exp window) Y (Z^tau)≤ cutoff G E.val)→
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj extra pool original w negative Ψ m slots lists a om X t Y ≤
      Czero*Z^(r+3*ell+V+17*eta+tau+pi)+
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild)+Ctail*Z^(-saving) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    global_priority_filtered_aggregate_uniform_types  om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,Cbin,hC,hCbin,he⟩:=hordered J
  obtain ⟨sz,Cz,hCz,hzero⟩:=global_priority_zero_physical εmass hεmass Jmax dsmall hdsmall
  obtain ⟨st,Ct,hCt,htail⟩:=global_physical_tail_rapid Jmax Lcap tau saving hLcap htau
  let Cz':=Cz*(4:ℝ)^K*(sz.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2*Real.exp (window*(1+εmass))
  let Ct':=Ct*(4:ℝ)^K*(st.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2
  refine ⟨C,Cbin,Cz',Ct',hC,hCbin,by dsimp [Cz'];positivity,by dsimp [Ct'];positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hw Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst pi b ρ t labels A
    hhib hdisj hslots hA hdata hJo hell hBfirst hj hcost hcube₁ hcube₂ hactive hcommon hquotient
    hYone hscale hy hyi hx hPcap hcubeCap₁ hcubeCap₂ hactiveCap hcommonCap hquotCap hrad hcutoff
  have hh:=hdata 1 1 ∅ (Finset.empty_subset _)
  obtain ⟨_,hρ,hL,hZ,hX,hY,heta,hbin,_,_,_,_,_,_,hΨall,_,_,_,_,_,_,_,hYe,hXe,hLe,_,hZ2,_,_,_,_,_,_,_⟩:=hh
  have hz:0< Z:=zero_lt_one.trans hZ
  have haall:∀i∈slots,∀q∈lists i,‖a i q‖≤1:=by
    have hh':=hdata 1 1 slots (Finset.Subset.refl _)
    exact hh'.1
  have hpow:(4:ℝ)^slots.card≤4^K:=pow_le_pow_right₀ (by norm_num) hslots
  have hzn:=hzero p hp hg hinj hcop Jo hJo extra pool original w negative Ψ m slots lists a
    hdisj haall hΨall hw om lo hi hlo hsupport Z M r ell V delta Acol Bfirst Ractive j tcount eta tau window pi t cutoff
    hZ.le hell hBfirst hj hcost hvalid hcube₁ hcube₂ hactive hcommon hquotient hextra hhi (by rwa [←hYe]) hrad
  rw [←hXe,←hYe] at hzn
  have hzbound : _ ≤ Cz'*Z^(r+3*ell+V+17*eta+tau+pi):=hzn.trans (by dsimp [Cz'];gcongr)
  have htn:=htail p hp hg hinj hcop hc Jo hJo extra pool original negative Ψ m w slots lists a
    hdisj haall hΨall hw om lo hi hlo hsupport X window Y Z t
    (firstKappa M r ell V delta Acol Bfirst Ractive) eta cutoff hPcap hX hhi hZ.le hY hscale hy hyi hx
    hvalid hextra hcubeCap₁ hcubeCap₂ hactiveCap hcommonCap hquotCap hcutoff
  have htbound : _ ≤ Ct'*Z^(-saving):=htn.trans (by dsimp [Ct'];gcongr)
  have hrbound:=he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hw Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A hhib hslots hA hdata
  have hb:=global_priority_three_branches p hg hp hcop hinj hc hpr extra pool original w negative Ψ m slots lists a
    om lo hi hlo hsupport X t Y hX hY cutoff
  have hP:0≤ Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)):=by positivity
  have hb':=mul_le_mul_of_nonneg_left hb hP
  simp only [mul_add] at hb'
  exact hb'.trans (add_le_add (add_le_add hzbound hrbound) htbound)
end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open InverseInitialClippedColumns JointLogSeparation InverseAmbientProfileTower
open InverseSecondSourceBlocks
local notation "O"=> Eisenstein.O

def secondChildHeight (right:Bool)(t:Ambient (Fin 6)):ℝ :=
  if right then profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2 5
  else -profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2 4

theorem second_child_height_budget (J:ℕ)(right:Bool)(t:Ambient (Fin 6)):
    (1+‖secondChildHeight right t‖)^J≤ tripleHeight J t.1*coordinateHeight J t.2:=by
  cases right
  · have h:=pow_le_pow_left₀ (by positivity : 0≤1+‖inheritedLeft 4 t‖) (inheritedLeft_bound 4 t) J
    rw [←ambientWeight_eq_pow] at h
    simpa only [secondChildHeight,Bool.false_eq_true,ite_false,norm_neg,
      second_inherited_left_eq,ambientWeight,tripleHeight,coordinateHeight] using h
  · have h:=pow_le_pow_left₀ (by positivity : 0≤1+‖inheritedRight 5 t‖) (inheritedRight_bound 5 t) J
    rw [←ambientWeight_eq_pow] at h
    simpa only [secondChildHeight,ite_true,second_inherited_right_eq,norm_neg,
      ambientWeight,tripleHeight,coordinateHeight] using h

theorem canonical_actual_child_uniform
    (W:ℝ→ℂ)(lo hi b:ℝ)(hlo:0< lo)(hb:1≤ b)
    (hs:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W):
    ∃(wFresh:𝓢(ℝ,ℂ))(af bf:ℝ),0< af ∧ af≤ bf ∧ HasCompactSupport (wFresh:ℝ→ℂ) ∧
      tsupport (wFresh:ℝ→ℂ)⊆Set.Icc af bf ∧
      ∀J:ℕ,∃C:ℝ,0< C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i})
      (_hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (labels:Finset (Ideal O))(rows:Finset O)(D:Ideal O→ℝ)(_hD:∀f∈labels,0≤ D f)
      (Z X F E:ℝ)(d:BlockIndex)(right:Bool)(t:Ambient (Fin 6)),
      1< Z→0< X→scales d 0*scales d 2≤ b*X→0≤ E→
      (∀s,normalizedColumnEnergy p hg pool Ψ m slots lists a labels rows D
        (childLogTest wFresh s) (Z^(max 0 (secondCellColumnExponent Z X d))) Z F≤ E*(1+‖s‖)^(2*J))→
      normalizedColumnEnergy p hg pool Ψ m slots lists a labels rows D
        (clippedTest W (Z^(max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d))
          (secondChildHeight right t)) (Z^(max 0 (secondCellColumnExponent Z X d))) Z F≤
        C*E*(tripleHeight (2*J) t.1*coordinateHeight (2*J) t.2):=by
  obtain ⟨wFresh,af,bf,haf,hab,hc,hsf,he⟩:=canonical_clipped_uniform W lo hi b hlo hb hs hW
  refine ⟨wFresh,af,bf,haf,hab,hc,hsf,?_⟩
  intro J
  obtain ⟨C,hC,hbound⟩:=he J
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr pool Ψ m slots lists a labels rows D hD Z X F E d right t hZ hX hgeom hE hmoment
  obtain ⟨hc1,hcb⟩:=second_cell_clipping_ratio Z X b d hZ hX hb hgeom
  have hz:0< Z:=zero_lt_one.trans hZ
  exact (hbound p hp hcop hg hpr pool Ψ m slots lists a labels rows D hD
    _ (secondChildHeight right t) _ Z F E hc1 hcb (Real.rpow_pos_of_pos hz _) hE hmoment).trans
      (mul_le_mul_of_nonneg_left (second_child_height_budget (2*J) right t) (mul_nonneg hC.le hE))

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open JointLogSeparation CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseFirstPriorityParents InversePrioritySecondSource InverseMomentGlobalPriorityTail
open InverseWholePriorityRetainedSource RayFourExpansion
local notation "Eis"=> Eisenstein.O
theorem global_priority_fixed_child_step_uniform_types
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0< lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (window Lcap tau saving:ℝ)(hhi:hi≤ Real.exp window)(hLcap:0≤ Lcap)(htau:0< tau)
    (bcap:ℝ)(hbcap:1≤ bcap)
    (Jmax:ℕ)(dsmall:ℝ)(hdsmall:0< dsmall)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤ caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤ B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0< loFresh ∧ loFresh≤ hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin Czero Ctail : ℝ,0 ≤ C ∧ 0≤ Cbin ∧ 0≤ Czero ∧ 0≤ Ctail ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, lambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis)
    (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:Finset ι→Finset ι→ℝ)
,
    ∀
        (Y:ℝ) (R:Finset σ→BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : Finset σ→BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      hi≤ b → b≤ bcap → (slots:Set σ).PairwiseDisjoint lists→slots.card≤ K → 0≤ A → (∀(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ), assigned⊆slots →
    let source:=InverseMomentGlobalRetainedGates.geometrySource p (unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=> extra x.cube) original negative assigned lists) (fun _=> cutoff)) b X;
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core;
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) ∧
      (∀ i,|ρ i| ≤ B₀ i) ∧
      0 ≤ L ∧
      1 < Z ∧
      0 < X ∧
      0 < Y ∧
      0≤ eta ∧
      2≤ Z^eta ∧
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R assigned (index p x))) ∧
      (∀ x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) ∧
      (∀ x∈source,Z^(j-eta) ≤ ‖ringComplex (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) ∧
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) ∧
      (∀ a,‖Ψ a‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels assigned d) ∧
      Jo+(assigned.card+assigned.card) ≤ 2*K ∧
      (slots\assigned).card ≤ K ∧
      (slots\assigned).card ≤ K ∧
      0 ≤ A ∧
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) ∧
      X=Z^(r-Acol-Bfirst-tcount) ∧
      L=eta*Real.log Z ∧
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) ∧
      2≤ Z ∧
      1≤ b ∧
      b≤ Z^(6*eta) ∧
      (∀x∈source,∀i,outerNorms p x i≤ Z^(caps i)) ∧
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤ b*X) ∧
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤ pi) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ s:ℝ,∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (childLogTest ω₁ s)
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(1+‖s‖)^(2*J)) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ s:ℝ,∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (childLogTest ω₂ s)
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(1+‖s‖)^(2*J))) →
      Jo≤ Jmax→0≤ ell+eta→0≤ Bfirst→0≤ j→
      εmass*(r-Acol-Bfirst-tcount)+7*eta/2+dsmall*(3*ell+Bfirst+tcount+5*eta)+
        2*εmass*(2*ell+Bfirst+tcount+4*eta)≤ pi+eta/2→
      (∀x∈original,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤ Z^(ell+eta))→
      (∀x∈original,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤ Z^(ell+eta))→
      (∀x∈original,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=> x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤ Z^(Ractive+eta))→
      (∀x∈original,primeProductNorm p x.firstCommon≤ Z^(Bfirst+eta))→
      (∀x∈original,primeProductNorm p x.quotientSupport≤ Z^(tcount+eta))→
      1≤ Y→1≤ X*Real.exp window→Y≤ Z^Lcap→Y⁻¹≤ Z^Lcap→X*Real.exp window≤ Z^Lcap→
      firstKappa M r ell V delta Acol Bfirst Ractive+(9/2:ℝ)*eta≤ Lcap→
      (∀x∈original,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤ Z^Lcap)→
      (∀x∈original,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤ Z^Lcap)→
      (∀x∈original,‖ringComplex (∏i∈cubeActiveSupport x.cube.support
        (fun i=> x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤ Z^Lcap)→
      (∀x∈original,primeProductNorm p x.firstCommon≤ Z^Lcap)→
      (∀x∈original,primeProductNorm p x.quotientSupport≤ Z^Lcap)→
      (∀G E,0≤ cutoff G E)→
      (∀x∈original,∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p (parent p x)) G E.val
          (X*Real.exp window) Y (Z^tau)≤ cutoff G E.val)→
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj extra pool original w negative Ψ m slots lists a om X t Y ≤
      Czero*Z^(r+3*ell+V+17*eta+tau+pi)+
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder (2*J))*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild)+Ctail*Z^(-saving) := by
  obtain ⟨v₁,v₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hstep⟩:=
    global_priority_filtered_physical_step_uniform_types  om lo hi hlo hsupport negative
      window Lcap tau saving hhi hLcap htau Jmax dsmall hdsmall caps hcaps B₀ hB₀ K εmass hεmass
  obtain ⟨w₁,a₁,b₁,ha₁,hab₁,hw₁,hsw₁,hfixed₁⟩:=canonical_actual_child_uniform
    v₁ af bf bcap haf hbcap ((subset_tsupport _).trans hs₁) (v₁.smooth ⊤)
  obtain ⟨w₂,a₂,b₂,ha₂,hab₂,hw₂,hsw₂,hfixed₂⟩:=canonical_actual_child_uniform
    v₂ af bf bcap haf hbcap ((subset_tsupport _).trans hs₂) (v₂.smooth ⊤)
  refine ⟨w₁,w₂,min a₁ a₂,max b₁ b₂,lt_min ha₁ ha₂,
    (min_le_left _ _).trans (hab₁.trans (le_max_left _ _)),hw₁,hw₂,
    hsw₁.trans (Set.Icc_subset_Icc (min_le_left _ _) (le_max_left _ _)),
    hsw₂.trans (Set.Icc_subset_Icc (min_le_right _ _) (le_max_right _ _)),?_⟩
  intro J
  obtain ⟨C₁,hC₁,he₁⟩:=hfixed₁ J
  obtain ⟨C₂,hC₂,he₂⟩:=hfixed₂ J
  obtain ⟨C,Cbin,Czero,Ctail,hC,hCbin,hCzero,hCtail,he⟩:=hstep (2*J)
  let Cmax:=max C₁ C₂
  have hmax:0≤ Cmax:=hC₁.le.trans (le_max_left _ _)
  refine ⟨C*Cmax,Cbin,Czero,Ctail,mul_nonneg hC hmax,hCbin,hCzero,hCtail,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hw Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst pi b ρ t labels A
    hhib hbcap' hdisj hslots hA hdata hJo hell hBfirst hj hcost hcube₁ hcube₂ hactive hcommon hquotient
    hYone hscale hy hyi hx hPcap hcubeCap₁ hcubeCap₂ hactiveCap hcommonCap hquotCap hrad hcutoff
  have hout:=he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hw Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst pi b ρ t labels (Cmax*A)
    hhib hdisj hslots (mul_nonneg hmax hA)
  have hnew:
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj extra pool original w negative Ψ m slots lists a om X t Y ≤
      Czero*Z^(r+3*ell+V+17*eta+tau+pi)+
      C*(Cmax*A)*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder (2*J))*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild)+Ctail*Z^(-saving) := by
    apply hout
    · intro ray core assigned hassigned
      obtain ⟨haa,hρ,hL,hZ,hX,hY,heta,hbin,hrows,hb₁,hb₂,hactive',hj',hq,hΨ,
        hal,har,hlabels,ho,hsl,hsr,hA',hYe,hXe,hLe,hVe,hZ2,hb,hthreshold,hnorm,hgeom,hmass,hleft,hright⟩:=hdata ray core assigned hassigned
      refine ⟨haa,hρ,hL,hZ,hX,hY,heta,hbin,hrows,hb₁,hb₂,hactive',hj',hq,hΨ,
        hal,har,hlabels,ho,hsl,hsr,mul_nonneg hmax hA',hYe,hXe,hLe,hVe,hZ2,hb,hthreshold,hnorm,hgeom,hmass,?_,?_⟩
      · intro z d hd u J₁ hJ₁ γ hγ
        have hgeomcell:=source_cell_joint_bound p hp _ (fun x hx=>(Finset.mem_erase.mp (hrows x hx)).1) b X hgeom d hd
        have hh:=he₁ p hp hcop hg hpr pool _ _ ((slots\assigned)\J₁) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (fun f hf=> pow_nonneg (Nat.cast_nonneg _) _) Z X _
          (A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel d+εchild)) d false u hZ hX
          (hgeomcell.trans (mul_le_mul_of_nonneg_right hbcap' hX.le)) (mul_nonneg hA (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
          (fun s=> hleft z d hd s J₁ hJ₁ γ hγ)
        change _≤(Cmax*A)*Z^(_)*_
        apply hh.trans
        have hH:0≤ tripleHeight (2*J) u.1*coordinateHeight (2*J) u.2:=by
          unfold tripleHeight coordinateHeight
          positivity
        have hE:0≤ A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel d+εchild):=
          mul_nonneg hA (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
        convert mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hE) hH using 1 ; ring
      · intro z d hd u J₂ hJ₂ γ hγ
        have hgeomcell:=source_cell_joint_bound p hp _ (fun x hx=>(Finset.mem_erase.mp (hrows x hx)).1) b X hgeom d hd
        have hh:=he₂ p hp hcop hg hpr pool _ _ ((slots\assigned)\J₂) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (fun f hf=> pow_nonneg (Nat.cast_nonneg _) _) Z X _
          (A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel d+εchild)) d true u hZ hX
          (hgeomcell.trans (mul_le_mul_of_nonneg_right hbcap' hX.le)) (mul_nonneg hA (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
          (fun s=> hright z d hd s J₂ hJ₂ γ hγ)
        change _≤(Cmax*A)*Z^(_)*_
        apply hh.trans
        have hH:0≤ tripleHeight (2*J) u.1*coordinateHeight (2*J) u.2:=by
          unfold tripleHeight coordinateHeight
          positivity
        have hE:0≤ A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel d+εchild):=
          mul_nonneg hA (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
        convert mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hE) hH using 1 ; ring
    all_goals assumption
  convert hnew using 1 ; ring
end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMomentFirstLabelCell
open InverseMoment Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open InverseSecondFibers InverseInitialClippedColumns RayFourExpansion
open InverseWholePriorityRetainedSource
open Eisenstein (ringComplex)
local notation "O" => Eisenstein.O

def ChildBounds {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
    (hg : ∀i,lambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (Z M r ell V eta tau window b epschild A : ℝ) (K degree : ℕ) : Prop :=
  ∀(ray : RayCharacter×RayCharacter)(core : FirstCoreIndex)(assigned : Finset σ),assigned⊆slots→
  let S := source p pool Q k l j negative assigned lists Z M r ell V eta tau window b
  let Ψ₀ := firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
  (∀z : SecondRayIndex,∀d∈keys p S,∀s : ℝ,∀J₁∈(slots\assigned).powerset,∀γ∈actualSecondTriples p 1 1 (cell p S d),
    normalizedColumnEnergy p hg pool (secondRayMinus Ψ₀ z)
      (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
      ((actualCellLabels p S d).filter Squarefree)
      (nonzeroChildFrequencyBall 1 (actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d))
      (secondLabelWeight K) (childLogTest ω₁ s)
      (Z^(max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d))) Z
      (actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d)≤
      A*Z^(actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d+epschild)*
        (1+‖s‖)^(2*degree)) ∧
  (∀z : SecondRayIndex,∀d∈keys p S,∀s : ℝ,∀J₂∈(slots\assigned).powerset,∀γ∈actualSecondTriples p 1 1 (cell p S d),
    normalizedColumnEnergy p hg pool (secondRayPlus Ψ₀ z)
      (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
      ((actualCellLabels p S d).filter Squarefree)
      (nonzeroChildFrequencyBall 1 (actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d))
      (secondLabelWeight K) (childLogTest ω₂ s)
      (Z^(max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d))) Z
      (actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d)≤
      A*Z^(actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d+epschild)*
        (1+‖s‖)^(2*degree))

theorem actual_label_cell_step (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0< lo)
    (hsupport : Function.support om⊆Set.Icc lo hi) (negative : Bool)
    (window Ltail Lgate tau saving : ℝ) (hhi : hi≤ Real.exp window)
    (hLtail : 0≤ Ltail) (hLgate : 0≤ Lgate) (htau : 0< tau)
    (bcap : ℝ) (hbcap : 1≤ bcap) (dsmall : ℝ) (hdsmall : 0< dsmall)
    (B₀ : Fin 6→ℝ) (hB₀ : ∀i,0≤ B₀ i) (K : ℕ) (epsmass : ℝ) (hepsmass : 0< epsmass) :
    ∃(ω₁ ω₂ : 𝓢(ℝ,ℂ))(loFresh hiFresh : ℝ),0< loFresh ∧ loFresh≤ hiFresh ∧
      HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
    ∀degree : ℕ,∃C Cbin Czero Ctail : ℝ,0≤ C ∧ 0≤ Cbin ∧ 0≤ Czero ∧ 0≤ Ctail ∧
    ∀{ι σ : Type}[DecidableEq ι][DecidableEq σ](p : ι→O)(hp : ∀i,p i≠0)
      [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hpr : ∀i,lambda^2∣p i-1)
      (hinj : Function.Injective (fun i=> Ideal.span {p i})) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι)(Q : Finset (ι→₀ℕ))(k : SourceIndex)(l j : ℕ)
      (Ψ : O→*ℂ)(m : O)(slots : Finset σ)(lists : σ→Finset ι)(a : σ→ι→ℂ)
      (Z M r ell V eta pi b Lcol LY epschild A t : ℝ)(ρ : Fin 6→ℝ),
      2≤ Z→0≤ eta→2≤ Z^eta→0≤ ell+eta→
      (∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta))→
      (slots:Set σ).PairwiseDisjoint lists→slots.card≤ K→(∀i∈slots,∀q∈lists i,‖a i q‖≤1)→
      (∀u,‖Ψ u‖≤1)→(∀i,|ρ i|≤ B₀ i)→hi≤ b→b≤ bcap→1≤ b→b≤ Z^(6*eta)→
      Real.exp window≤ Z^(4*eta)→0≤ A→
      columnScale Z r k l negative*Real.exp window≤ Z^Lcol→
      (firstCellRadius Z M r ell V eta tau k j)⁻¹≤ Z^LY→
      b*columnScale Z r k l negative≤ Z^Lgate→exponent Z (k 3)+eta+2*Lcol+tau+LY≤ Lgate→
      epsmass*(ell+exponent Z (k 4)/2+exponent Z l+Lgate+11*eta/2)≤ pi→
      epsmass*(r-columnA Z k negative-exponent Z (k 2)-exponent Z l)+7*eta/2+
        dsmall*(3*ell+exponent Z (k 2)+exponent Z l+5*eta)+
        2*epsmass*(2*ell+exponent Z (k 2)+exponent Z l+4*eta)≤ pi+eta/2→
      1≤ firstCellRadius Z M r ell V eta tau k j→1≤ columnScale Z r k l negative*Real.exp window→
      firstCellRadius Z M r ell V eta tau k j≤ Z^Ltail→
      (firstCellRadius Z M r ell V eta tau k j)⁻¹≤ Z^Ltail→
      columnScale Z r k l negative*Real.exp window≤ Z^Ltail→
      firstKappa M r ell V (exponent Z (k 3)) (columnA Z k negative) (exponent Z (k 2)) (exponent Z (k 4))+
        (9/2:ℝ)*eta≤ Ltail→
      ell+eta≤ Ltail→exponent Z (k 4)+eta≤ Ltail→exponent Z (k 2)+eta≤ Ltail→exponent Z l+eta≤ Ltail→
      ChildBounds p hp hcop hg pool Q k l j negative Ψ m slots lists a ω₁ ω₂
        Z M r ell V eta tau window b epschild A K degree→
      (Z^(firstKappa M r ell V (exponent Z (k 3)) (columnA Z k negative) (exponent Z (k 2)) (exponent Z (k 4)))*
        Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      globalPriorityOriginalEnergy p hg hp hinj (extra negative) pool
        (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j) (parentWeight p l)
        negative Ψ m slots lists a om (columnScale Z r k l negative) t (firstCellRadius Z M r ell V eta tau k j)≤
      Czero*Z^(r+3*ell+V+17*eta+tau+pi)+
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder (2*degree))*(1+Cbin*Real.log Z)^4*
        Z^(r+3*ell+V+48*eta+tau+pi+epschild)+Ctail*Z^(-saving) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hw₁,hw₂,hs₁,hs₂,hstep⟩ := global_priority_fixed_child_step_uniform_types
    om lo hi hlo hsupport negative window Ltail tau saving hhi hLtail htau bcap hbcap
    0 dsmall hdsmall (fun _=> Lgate) (fun _=> hLgate) B₀ hB₀ K epsmass hepsmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro degree
  obtain ⟨C,Cbin,Czero,Ctail,hC,hCbin,hCzero,hCtail,he⟩ := hstep degree
  refine ⟨C,Cbin,Czero,Ctail,hC,hCbin,hCzero,hCtail,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc pool Q k l j Ψ m slots lists a
    Z M r ell V eta pi b Lcol LY epschild A t ρ hZ2 heta hbin hell hQ hdisj hslots ha hΨ hρ hhib hbb hb1 hb6
    hwindow hA hcol hYi hgeom hphysical hbudget hcost hY1 hX1 hYcap hYicap hXcap hPcap hellcap hactivecap hcommoncap hquotcap hchild
  have hZ : 1< Z := by linarith
  have hz : 0< Z := zero_lt_one.trans hZ
  have hX : 0< columnScale Z r k l negative := Real.rpow_pos_of_pos hz _
  have hY : 0< firstCellRadius Z M r ell V eta tau k j := Real.rpow_pos_of_pos hz _
  have hparent := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ
  have htail := parent_tail_caps p hp pool Q k l j Z ell eta Ltail hZ heta hbin hLtail hQ
    hellcap hactivecap hcommoncap hquotcap
  apply he p hp hcop hg hpr hinj hc (extra negative) pool
    (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j)
    (label_parent_valid p pool Q k l j) (fun y hy=> extra_subset negative y.cube)
    (parentWeight p l) (fun y hy=> parentWeight_norm p l y) Ψ m slots lists a
    (secondCutoff p Z M r ell V eta tau window k l j negative)
    (firstCellRadius Z M r ell V eta tau k j)
    (fun _ d=> actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d)
    (eta*Real.log Z) Z (columnScale Z r k l negative) epschild
    (actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta)
    ell (exponent Z (k 4)) (exponent Z j) (exponent Z l) eta M r V
    (exponent Z (k 3)) (columnA Z k negative) (exponent Z (k 2)) pi b ρ t
    (fun assigned d=> actualCellLabels p (source p pool Q k l j negative assigned lists Z M r ell V eta tau window b) d) A
    hhib hbb hdisj hslots hA
  · intro ray core assigned hassigned
    obtain ⟨_,_,hrows,_,hn,hlabels,_,hcaps,hgeometry,hmass⟩ := source_step_arithmetic p hp pool Q k l j
      negative assigned lists Z M r ell V eta tau window b Lcol LY Lgate epsmass pi
      hZ heta hbin hepsmass.le hwindow hQ hcol hYi hgeom hphysical hbudget
    have hJ : assigned.card≤ K := (Finset.card_le_card hassigned).trans hslots
    have hrest : (slots\assigned).card≤ K := (Finset.card_le_card Finset.sdiff_subset).trans hslots
    have hbchild := hchild ray core assigned hassigned
    refine ⟨(fun i hi q hq=> ha i (hassigned hi) q hq),hρ,mul_nonneg heta (Real.log_nonneg hZ.le),hZ,hX,hY,heta,hbin,
      hrows,(fun x hx=>(hn x hx).1),(fun x hx=>(hn x hx).2.1),(fun x hx=>(hn x hx).2.2.1),
      (fun x hx=>(hn x hx).2.2.2.2.2.1),(fun x hx=>(hn x hx).2.2.2.2.1),hΨ,
      (fun i hi q hq=> ha i (Finset.mem_sdiff.mp hi).1 q hq),
      (fun i hi q hq=> ha i (Finset.mem_sdiff.mp hi).1 q hq),
      (fun d hd x hx=> hlabels d x hx),by omega,hrest,hrest,hA,rfl,rfl,rfl,(fun _=> rfl),hZ2,hb1,hb6,
      hcaps,hgeometry,hmass,hbchild.1,hbchild.2⟩
  · exact Nat.zero_le _
  · exact hell
  · exact dyadic_exponent_nonneg Z hZ _
  · exact dyadic_exponent_nonneg Z hZ _
  · exact hcost
  · exact fun y hy=>(hparent y hy).1
  · exact fun y hy=>(hparent y hy).2.1
  · exact fun y hy=>(hparent y hy).2.2.1
  · exact fun y hy=>(hparent y hy).2.2.2.1
  · exact fun y hy=>(hparent y hy).2.2.2.2.1
  · exact hY1
  · exact hX1
  · exact hYcap
  · exact hYicap
  · exact hXcap
  · exact hPcap
  · exact fun y hy=>(htail y hy).1
  · exact fun y hy=>(htail y hy).2.1
  · exact fun y hy=>(htail y hy).2.2.1
  · exact fun y hy=>(htail y hy).2.2.2.1
  · exact fun y hy=>(htail y hy).2.2.2.2
  · exact fun G E=> secondCutoff_nonneg p Z M r ell V eta tau window k l j negative hz G E
  · exact fun y hy G hG E=> secondCutoff_dominates p hp pool Q k l j negative Z M r ell V eta tau window hZ hbin y hy G E.val

end InverseMomentFirstLabelCell
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMomentFirstLabelCell
open InverseMoment Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstGlobalCaps InverseSecondSourceBlocks
open Eisenstein (ringComplex)
local notation "O" => Eisenstein.O
variable {ι σ:Type*}[DecidableEq ι][DecidableEq σ]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem source_total_cap (pool:Finset ι)(Q:Finset (ι→₀ℕ))(k:SourceIndex)(l j:ℕ)
    (negative:Bool)(J:Finset σ)(lists:σ→Finset ι)(Z M r ell V eta tau window b:ℝ)
    (hZ:1< Z)(heta:0≤ eta)(hbin:2≤ Z^eta)(hell:0≤ ell)(hV:0≤ V)
    (hb:1≤ b)(hbt:b≤ Z^(6*eta))
    (hQ:∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta)):
    let S:=source p pool Q k l j negative J lists Z M r ell V eta tau window b;
    ∀d∈keys p S,actualCellTotalExponent Z (columnScale Z r k l negative)
      (exponent Z (k 2)) (exponent Z j) eta d≤ r+3*ell+V+15*eta :=by
  intro S d hd
  obtain ⟨x,hx⟩:=(mem_keys_iff p S d).mp hd
  have hn:=retained_label_numeric p hp pool Q k l j Z ell eta hZ heta hbin hQ negative J lists
    (secondCutoff p Z M r ell V eta tau window k l j negative) b (columnScale Z r k l negative)
    x (cell_subset p S d hx)
  have he:=actual_cell_child_total_upper p hp S
    (source_valid p hp pool Q k l j negative J lists Z M r ell V eta tau window b)
    (source_frequency_ne_zero p pool Q k l j negative J lists Z M r ell V eta tau window b)
    d x hx Z r ell V (columnA Z k negative) (exponent Z (k 2)) (exponent Z l) (exponent Z j) eta b hZ
    (dyadic_exponent_nonneg Z hZ _) (dyadic_exponent_nonneg Z hZ _) hell hV heta hbin hb hbt
    (source_geometry p pool Q k l j negative J lists Z M r ell V eta tau window b)
    hn.1 hn.2.1 hn.2.2.2.2.2.1
  exact he

include hp in
theorem source_state_bounds (pool:Finset ι)(Q:Finset (ι→₀ℕ))(k:SourceIndex)(l j:ℕ)
    (negative:Bool)(J:Finset σ)(lists:σ→Finset ι)(Z M r ell V eta tau window b cutoff:ℝ)
    (hZ:1< Z)(heta:0≤ eta)(hbin:2≤ Z^eta)(hell:0≤ ell)(hV:0≤ V)
    (hb:1≤ b)(hbt:b≤ Z^(6*eta))(hwindow:Real.exp window≤ Z^(4*eta))
    (hterminal:cutoff≤ ell+V)(hsmall:eta≤ cutoff/16)
    (hQ:∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta)):
    let S:=source p pool Q k l j negative J lists Z M r ell V eta tau window b;
    ∀d∈keys p S,
      0≤ max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d) ∧
      0≤ actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d ∧
      actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d≤ r+3*ell+V+15*eta ∧
      0≤ actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d ∧
      actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d+3*cutoff/2≤ M :=by
  intro S d hd
  refine ⟨le_max_left _ _,actual_cell_label_nonneg Z _ _ eta d hZ
    (dyadic_exponent_nonneg Z hZ _) (dyadic_exponent_nonneg Z hZ _) heta,?_,?_,?_⟩
  · exact source_total_cap p hp pool Q k l j negative J lists Z M r ell V eta tau window b hZ heta hbin hell hV hb hbt hQ d hd
  · exact (source_row_gates p hp pool Q k l j negative J lists Z M r ell V eta tau window b hZ heta hbin hwindow).2 d hd
  · exact source_row_decrease p hp pool Q k l j negative J lists Z M r ell V eta tau window b cutoff hZ heta hbin hterminal hsmall hQ d hd

end InverseMomentFirstLabelCell

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve
open InverseInitialArithmetic InverseSecondSourceBlocks InverseSecondFibers
local notation "O"=> Eisenstein.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
variable (hg:∀i,lambda∉Ideal.span {p i})
variable (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)

include hp hg hc in
omit [DecidableEq ι] in
lemma canonical_source_prime_supported (i:ι):Supported (Ideal.span {p i}) :=by
  have hn:(Ideal.span {p i}:Ideal O)≠0:=Ideal.span_singleton_eq_bot.not.mpr (hp i)
  refine ⟨hn,?_⟩
  intro P hP
  obtain ⟨hprime,hle⟩:=(Ideal.mem_normalizedFactors_iff hn).mp hP
  have he:Ideal.span {p i}=P:=(inferInstance:(Ideal.span {p i}:Ideal O).IsMaximal).eq_of_le hprime.ne_top hle
  subst P
  exact ⟨hg i,hc i⟩

lemma canonical_supported_prod {α:Type*}(S:Finset α)(f:α→Ideal O)
    (hf:∀i∈S,Supported (f i)):Supported (∏i∈S,f i) :=by
  classical
  induction S using Finset.induction_on with
  | empty =>
    change Supported (1:Ideal O)
    refine ⟨one_ne_zero,?_⟩
    intro P hP
    rw [UniqueFactorizationMonoid.normalizedFactors_one] at hP
    exact (Multiset.notMem_zero P hP).elim
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi,supported_mul_iff]
    exact ⟨hf i (Finset.mem_insert_self _ _),ih (fun j hj=> hf j (Finset.mem_insert_of_mem hj))⟩

include hp hg hc in
omit [DecidableEq ι] in
lemma canonical_source_ideal_supported (S:Finset ι):Supported (sourceIdeal p S) :=by
  rw [sourceIdeal,SchwartzPlanePoisson.span_finset_prime_product]
  exact canonical_supported_prod S (fun i=> Ideal.span {p i}) (fun i _=> canonical_source_prime_supported p hp hg hc i)

include hp hg hc in
omit [DecidableEq ι] in
lemma canonical_prime_product_supported (S:Finset ι)(v:ι→ℕ):Supported (Ideal.span {primeProduct p S v}) :=by
  rw [primeProduct,SchwartzPlanePoisson.span_finset_prime_product]
  apply canonical_supported_prod
  intro i hi
  rw [←Ideal.span_singleton_pow]
  exact supported_pow (canonical_source_prime_supported p hp hg hc i) _

include hp hg hc in
lemma actual_second_label_supported {Jo Jn:ℕ}(x:MarkedSecondSource ι Jo Jn):
    Supported (actualSecondChild p 1 1 x).2.1 :=by
  change Supported ((Ideal.span {jLabel p x.cube.support
    (fun i=> x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit})*
    sourceIdeal p x.firstCommon*sourceIdeal p x.second.divisor*sourceIdeal p x.second.overlap)
  simp only [supported_mul_iff]
  exact ⟨⟨⟨canonical_prime_product_supported p hp hg hc _ _,canonical_source_ideal_supported p hp hg hc _⟩,
    canonical_source_ideal_supported p hp hg hc _⟩,canonical_source_ideal_supported p hp hg hc _⟩

include hp hg hc in
theorem actual_cell_labels_supported {Jo Jn:ℕ}(S:Finset (MarkedSecondSource ι Jo Jn))(d:BlockIndex):
    ∀I∈actualCellLabels p S d,Supported I :=by
  intro I hI
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hI
  exact actual_second_label_supported p hp hg hc x

include hp hg hc in
theorem actual_cell_labels_admissible {Jo Jn:ℕ}(S:Finset (MarkedSecondSource ι Jo Jn))(d:BlockIndex):
    ∀I∈(actualCellLabels p S d).filter Squarefree,CanonicalQuadraticSieve.Admissible I :=by
  intro I hI
  obtain ⟨hm,hs⟩:=Finset.mem_filter.mp hI
  have hh:=actual_cell_labels_supported p hp hg hc S d I hm
  exact ⟨hh.1,hs,hh.2⟩

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve
open InverseInitialClippedColumns InverseSecondFibers InverseSecondSourceBlocks
open CanonicalCoefficientClass InverseMomentFirstLabelCell InverseMomentFirstChildWindows InverseFirstGlobalCaps
local notation "O"=> Eisenstein.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop:Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
variable (hg:∀i,lambda∉Ideal.span {p i})

include hp in
theorem canonical_rank_moments_children
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,lambda^2∣p i-1)
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(k:SourceIndex)(l j:ℕ)(negative:Bool)
    (base Ψ:O→*ℂ)(hΨ:IsBaseRayTwist base Ψ)(m:O)(hm:m≠0)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(ω₁ ω₂:𝓢(ℝ,ℂ))
    (Z M r ell V eta tau window b cutoff Qwidth z c eps A:ℝ)(K degree:ℕ)
    (hZ:1< Z)(heta:0≤ eta)(hbin:2≤ Z^eta)(hell:0≤ ell)(hV:0≤ V)
    (hb:1≤ b)(hbt:b≤ Z^(6*eta))(hwindow:Real.exp window≤ Z^(4*eta))
    (_hd:0< cutoff)(hterminal:cutoff≤ ell+V)(hsmall:eta≤ cutoff/16)
    (hparent:CanonicalMargins (r+3*ell+V) M Qwidth z c)
    (hpuncture:(Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤ Z^Qwidth)
    (hQ:∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta))
    (h₁:CanonicalRankMoments p hg pool base slots lists a ω₁ Z (M-3*cutoff/2) (r+3*ell+V+15*eta) z (c-7*eta) eps A K degree)
    (h₂:CanonicalRankMoments p hg pool base slots lists a ω₂ Z (M-3*cutoff/2) (r+3*ell+V+15*eta) z (c-7*eta) eps A K degree):
    ChildBounds p hp hcop hg pool Q k l j negative Ψ m slots lists a ω₁ ω₂
      Z M r ell V eta tau window b eps A K degree :=by
  intro ray core assigned hass
  let S:=source p pool Q k l j negative assigned lists Z M r ell V eta tau window b
  let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
  have hbase:IsBaseRayTwist base Ψ₀:=hΨ.firstCore _ _ _
  have hstate:=source_state_bounds p hp pool Q k l j negative assigned lists Z M r ell V eta tau window b cutoff
    hZ heta hbin hell hV hb hbt hwindow hterminal hsmall hQ
  have hmargin:=source_child_margins p hp hpr pool Q k l j negative assigned lists Z M r ell V eta tau window b
    m hm Qwidth z c hZ heta hbin hV hparent hpuncture hQ
  have hlabels:=source_labels p hp pool Q k l j negative assigned lists Z M r ell V eta tau window b hZ heta hbin hQ
  constructor
  · intro zz d hdcell s J hJ γ hγ
    have st:=hstate d hdcell
    have mg:=hmargin d γ hγ
    apply h₁ (secondRayMinus Ψ₀ zz) (hbase.secondMinus zz) (actualSecondInheritedRadicalPuncture m γ) mg.1
      (max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d))
      (actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d)
      (actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d)
      (actualSecondPunctureWidth Z m γ) st.1 st.2.1 st.2.2.2.1 mg.2.1 (by linarith [st.2.2.2.2]) st.2.2.1 mg.2.2.2 mg.2.2.1
      ((slots\assigned)\J) (Finset.sdiff_subset.trans Finset.sdiff_subset)
      ((actualCellLabels p S d).filter Squarefree) ?_ s
    intro I hI
    exact ⟨actual_cell_labels_admissible p hp hg hc S d I hI,(hlabels.2 d I hI).2.2⟩
  · intro zz d hdcell s J hJ γ hγ
    have st:=hstate d hdcell
    have mg:=hmargin d γ hγ
    apply h₂ (secondRayPlus Ψ₀ zz) (hbase.secondPlus zz) (actualSecondInheritedRadicalPuncture m γ) mg.1
      (max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d))
      (actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d)
      (actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d)
      (actualSecondPunctureWidth Z m γ) st.1 st.2.1 st.2.2.2.1 mg.2.1 (by linarith [st.2.2.2.2]) st.2.2.1 mg.2.2.2 mg.2.2.1
      ((slots\assigned)\J) (Finset.sdiff_subset.trans Finset.sdiff_subset)
      ((actualCellLabels p S d).filter Squarefree) ?_ s
    intro I hI
    exact ⟨actual_cell_labels_admissible p hp hg hc S d I hI,(hlabels.2 d I hI).2.2⟩

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve
open InverseMomentFirstLabelCell InverseMomentFirstChildWindows InverseFirstGlobalCaps
local notation "O"=> Eisenstein.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop:Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
variable (hg:∀i,lambda∉Ideal.span {p i})

theorem canonical_rank_cap_children
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,lambda^2∣p i-1)
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(k:SourceIndex)(l j:ℕ)(negative:Bool)
    (base Ψ:O→*ℂ)(hΨ:CanonicalCoefficientClass.IsBaseRayTwist base Ψ)(m:O)(hm:m≠0)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(ω₁ ω₂:𝓢(ℝ,ℂ))
    (Z M r ell V eta tau window b cutoff Qwidth z c eps A Mnext Fnext cnext:ℝ)(K degree:ℕ)
    (hZ:1< Z)(heta:0≤ eta)(hbin:2≤ Z^eta)(hell:0≤ ell)(hV:0≤ V)
    (hb:1≤ b)(hbt:b≤ Z^(6*eta))(hwindow:Real.exp window≤ Z^(4*eta))
    (hd:0< cutoff)(hterminal:cutoff≤ ell+V)(hsmall:eta≤ cutoff/16)
    (hparent:CanonicalMargins (r+3*ell+V) M Qwidth z c)
    (hpuncture:(Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤ Z^Qwidth)
    (hQ:∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta))
    (hMc:M-3*cutoff/2≤ Mnext)(hFc:r+3*ell+V+15*eta≤ Fnext)(hcc:cnext≤ c-7*eta)
    (h₁:CanonicalRankMoments p hg pool base slots lists a ω₁ Z Mnext Fnext z cnext eps A K degree)
    (h₂:CanonicalRankMoments p hg pool base slots lists a ω₂ Z Mnext Fnext z cnext eps A K degree):
    ChildBounds p hp hcop hg pool Q k l j negative Ψ m slots lists a ω₁ ω₂
      Z M r ell V eta tau window b eps A K degree :=by
  exact canonical_rank_moments_children p hp hcop hg hc hpr pool Q k l j negative base Ψ hΨ m hm
    slots lists a ω₁ ω₂ Z M r ell V eta tau window b cutoff Qwidth z c eps A K degree
    hZ heta hbin hell hV hb hbt hwindow hd hterminal hsmall hparent hpuncture hQ
    (canonical_rank_restrict p hg pool base slots lists a ω₁ Z _ _ _ _ z _ _ eps A K degree hMc hFc hcc h₁)
    (canonical_rank_restrict p hg pool base slots lists a ω₂ Z _ _ _ _ z _ _ eps A K degree hMc hFc hcc h₂)

theorem canonical_depth_ceilings (n:ℕ)(cutoff Fbase cbase eta:ℝ)(M F c:ℝ)
    (hM:M≤3*(n:ℝ)*cutoff/2)(hF:F≤ Fbase-15*(n:ℝ)*eta)
    (hc:cbase+7*((n:ℝ)+1)*eta≤ c):
    M-3*cutoff/2≤3*((n:ℝ)-1)*cutoff/2 ∧
    F+15*eta≤ Fbase-15*((n:ℝ)-1)*eta ∧
    cbase+7*(n:ℝ)*eta≤ c-7*eta :=by
  constructor
  · linarith
  constructor <;> linarith

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein CompletedGauss CanonicalRowCompletion 
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
local notation "O"=> Eisenstein.O

def actualCubeLength (Z:ℝ)(j:ℕ):ℝ:=Real.logb Z (normLogScale j)

theorem actualCubeLength_power (Z:ℝ)(hZ:1< Z)(j:ℕ) :
    Z^(actualCubeLength Z j)=normLogScale j :=
  Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (normLogScale_pos j)

theorem actual_long_bin_geometry
    (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)
    (b Z N V cutoff eta L:ℝ)(j:ℕ)(hZ:1< Z)(hL:1≤ L)(heta:eta≤1)
    (hV:0≤ V)(hparent:N+V≤ L)(hb:b≤ Z^eta)(hlog:1≤ eta*Real.log Z)
    (hne:(progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D b (Z^N) j)).Nonempty) :
    let ell:=actualCubeLength Z j;
    let r:=N-3*ell;
    let F:=CanonicalRowCompletion.outsideSquarefreeIdeals S D;
    let Q:=progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D b (Z^N) j);
    0≤ ell ∧ -eta≤ r ∧ r≤ L ∧ ell≤ L ∧ r+3*ell+V≤ L ∧ cutoff-eta≤ ell+V ∧
      ∀v∈Q,Z^ell≤‖ringComplex (primeProduct (poolPrimary F) v.support v)‖^2 ∧
        ‖ringComplex (primeProduct (poolPrimary F) v.support v)‖^2≤ Real.exp 1*Z^ell := by
  dsimp only
  have hz:0< Z:=zero_lt_one.trans hZ
  have hp:Z^(actualCubeLength Z j)=normLogScale j:=actualCubeLength_power Z hZ j
  have hel:0≤ actualCubeLength Z j:=Real.logb_nonneg hZ (normLogScale_ge_one j)
  have hnorm (v:primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→₀ℕ)
      (hv:v∈activeCubeLogBin S D b (Z^N) j) :
      Z^(actualCubeLength Z j)≤(Ideal.absNorm (cubeIdeal (CanonicalRowCompletion.outsideSquarefreeIdeals S D) v):ℝ) ∧
      (Ideal.absNorm (cubeIdeal (CanonicalRowCompletion.outsideSquarefreeIdeals S D) v):ℝ)≤ Real.exp 1*Z^(actualCubeLength Z j) := by
    rw [hp]
    exact activeCubeLogBin_norms S D b (Z^N) j v hv
  obtain ⟨v,hv⟩:=hne
  have hvbin: v∈activeCubeLogBin S D b (Z^N) j := (Finset.mem_filter.mp hv).1
  have hactive:= (Finset.mem_filter.mp hvbin).1
  have hcube:(Ideal.absNorm (cubeIdeal (CanonicalRowCompletion.outsideSquarefreeIdeals S D) v):ℝ)^3≤ b*Z^N :=
    (Finset.mem_filter.mp hactive).2
  have hsc:(Z^(actualCubeLength Z j))^3≤ Z^(N+eta) := by
    calc
      _≤(Ideal.absNorm (cubeIdeal (CanonicalRowCompletion.outsideSquarefreeIdeals S D) v):ℝ)^3 :=
        pow_le_pow_left₀ (Real.rpow_nonneg hz.le _) (hnorm v hvbin).1 3
      _≤ b*Z^N:=hcube
      _≤ Z^eta*Z^N:=mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hz.le _)
      _=Z^(N+eta):=by rw [Real.rpow_add hz];ring
  rw [←Real.rpow_mul_natCast hz.le] at hsc
  have hscale:actualCubeLength Z j*3≤ N+eta := (Real.rpow_le_rpow_left_iff hZ).mp hsc
  have hprogress:=long_cube_progress_with_slack S D (activeCubeLogBin S D b (Z^N) j)
    Z cutoff V (actualCubeLength Z j) eta hZ hlog ⟨v,hv⟩ (fun v hv=>(hnorm v hv).2)
  refine ⟨hel,by linarith,by linarith,by linarith,by linarith,hprogress,?_⟩
  intro u hu
  rw [cubeIdeal_primeProduct_norm _ (CanonicalRowCompletion.outsideSquarefree_admissible S D hbad)]
  exact hnorm u (Finset.mem_filter.mp hu).1

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile CompletedHeight
open Eisenstein (ringComplex)
local notation "O"=> Eisenstein.O

lemma actual_dyadic_exponent_cap (Z eta x A:ℝ)(hZ:1< Z)(hbin:2≤ Z^eta)(hx:1≤ x)(hcap:x≤ Z^A):
    0≤ dyadicExponent Z (dyadIndex x) ∧ dyadicExponent Z (dyadIndex x)≤ A:=by
  have h:=first_dyadic_bounds Z eta x hZ hbin hx
  exact ⟨h.1,(Real.rpow_le_rpow_left_iff hZ).mp (h.2.1.trans hcap)⟩

theorem original_live_exponent_caps {ι:Type}[DecidableEq ι]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
    (β:Ideal O→(ι→₀ℕ)→ℂ)(cutoff:CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)(om:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (K Z r ell F eta tau theta b:ℝ)(hZ:1< Z)(hbin:2≤ Z^eta)
    (hF:0≤ F)(hr:r≤ F)(hell:ell≤ F)(heta:0≤ eta)(htau:0≤ tau)(hb:b≤ Z^eta)
    (hQ:∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta))
    (hlabels:∀I∈labels,I≠0)(hs:∀y,om y≠0→y≤ b):
    let Y:=Z^(2*F+15*eta+tau);
    let W:=fun y=> normTwistedSource om theta (y/Z^r);
    let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=> labels) (fun x=> x.1) Y;
    ∀k∈liveJointKeys p source pool (sourceSummand p hp hg β cutoff Ψ m mark W Φ K),
      (∀i,0≤ dyadicExponent Z (k.1 i) ∧ dyadicExponent Z (k.1 i)≤3*F+15*eta+tau) ∧
      (0≤ dyadicExponent Z k.2.1 ∧ dyadicExponent Z k.2.1≤3*F+15*eta+tau) ∧
      (0≤ dyadicExponent Z k.2.2 ∧ dyadicExponent Z k.2.2≤3*F+15*eta+tau):=by
  intro Y W source k hk
  have hz:0< Z:=zero_lt_one.trans hZ
  have hW:∀y,W y≠0→y≤ Z^(r+eta):=by
    intro y hy
    have hh:om (y/Z^r)≠0:=by intro hh;exact hy (by simp [W,normTwistedSource,hh])
    calc
      y≤ b*Z^r:=(div_le_iff₀ (Real.rpow_pos_of_pos hz _)).mp (hs _ hh)
      _≤ Z^eta*Z^r:=mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hz.le _)
      _=Z^(r+eta):=by rw [←Real.rpow_add hz];congr 1;ring
  obtain ⟨⟨x,j⟩,hmem,rfl⟩:=Finset.mem_image.mp hk
  obtain ⟨hm,hnon⟩:=Finset.mem_filter.mp hmem
  obtain ⟨hx,hj⟩:=Finset.mem_product.mp hm
  obtain ⟨h₁,h₂,h₃⟩:=InverseMomentFirstLiveCaps.original_live_norm_caps p hp hg pool Q labels Y β cutoff Ψ m mark W Φ K
    (Z^(r+eta)) (Z^(ell+eta)) (Real.rpow_nonneg hz.le _) hQ hlabels hW x hx j hnon
  have hlow:=original_source_norms_ge_one p hp pool Q labels Y x hx
  have hsq:(Z^(ell+eta))^2=Z^(2*ell+2*eta):=by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le];congr 1;norm_num;ring
  have hA:Z^(r+eta)≤ Z^(3*F+15*eta+tau):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hB:(Z^(ell+eta))^2≤ Z^(3*F+15*eta+tau):=by
    rw [hsq]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith
  have hAB:Z^(r+eta)*(Z^(ell+eta))^2≤ Z^(3*F+15*eta+tau):=by
    rw [hsq,←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith
  have hY:Y≤ Z^(3*F+15*eta+tau):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  refine ⟨?_,?_,?_⟩
  · intro i
    apply actual_dyadic_exponent_cap Z eta _ _ hZ hbin (hlow i)
    apply (h₁ i).trans
    fin_cases i <;> first | exact hA | exact hAB | exact hB | exact hY
  · exact actual_dyadic_exponent_cap Z eta _ _ hZ hbin (primeProductNorm_ge_one p hp _) (h₂.trans hA)
  · exact actual_dyadic_exponent_cap Z eta _ _ hZ hbin
      (SchwartzPlanePoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _)) (h₃.trans hB)

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile CompletedHeight
open Eisenstein (ringComplex)
local notation "O"=> Eisenstein.O

theorem first_profile_live_products (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(K L:ℝ)(q:Fin 9→ℝ)
    (hq:∀i,1≤ q i)(hW:∀x,W x≠0→x≤ L)
    (hn:firstNormProfile (fun y=> star (W y)) W Φ (fun _ _=>1) K q≠0):
    q 0*q 2*q 5≤ L ∧ q 1*q 2*q 5≤ L:=by
  have h₁:W (q 0*q 2*q 5*q 7)≠0:=by intro h;apply hn;simp [firstNormProfile,h]
  have h₂:W (q 1*q 2*q 5*q 8)≠0:=by intro h;apply hn;simp [firstNormProfile,h]
  constructor
  · exact (le_mul_of_one_le_right (mul_nonneg (mul_nonneg (zero_le_one.trans (hq 0)) (zero_le_one.trans (hq 2))) (zero_le_one.trans (hq 5))) (hq 7)).trans (hW _ h₁)
  · exact (le_mul_of_one_le_right (mul_nonneg (mul_nonneg (zero_le_one.trans (hq 1)) (zero_le_one.trans (hq 2))) (zero_le_one.trans (hq 5))) (hq 8)).trans (hW _ h₂)

private theorem dyadic_column_scale {a c z X b : ℝ}
    (ha : 1 ≤ a) (hc : 1 ≤ c) (hz : 1 ≤ z) (hprod : a * c * z ≤ b * X) :
    1 ≤ X / (dyadScale (dyadIndex a) * dyadScale (dyadIndex c) *
      dyadScale (dyadIndex z)) * b := by
  have hscale : dyadScale (dyadIndex a) * dyadScale (dyadIndex c) *
      dyadScale (dyadIndex z) ≤ a * c * z :=
    mul_le_mul
      (mul_le_mul (dyadIndex_bounds a ha).1 (dyadIndex_bounds c hc).1
        (dyadScale_pos _).le (zero_le_one.trans ha))
      (dyadIndex_bounds z hz).1 (dyadScale_pos _).le
      (mul_nonneg (zero_le_one.trans ha) (zero_le_one.trans hc))
  rw [div_mul_eq_mul_div,
    le_div_iff₀ (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _)),
    one_mul, mul_comm X b]
  exact hscale.trans hprod

theorem original_live_column_scale {ι:Type}[DecidableEq ι]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))(Y:ℝ)
    (β:Ideal O→(ι→₀ℕ)→ℂ)(cutoff:CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(K X b:ℝ)
    (_hX:0< X)(hW:∀y,W y≠0→y≤ b*X)
    (k:JointKey)(hk:k∈liveJointKeys p
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=> labels) (fun x=> x.1) Y) pool
      (sourceSummand p hp hg β cutoff Ψ m mark W Φ K)):
    1≤ physicalScales X k.1 k.2.1 7*b ∧ 1≤ physicalScales X k.1 k.2.1 8*b:=by
  obtain ⟨⟨x,j⟩,hm,rfl⟩:=Finset.mem_image.mp hk
  obtain ⟨hm,hnon⟩:=Finset.mem_filter.mp hm
  obtain ⟨hx,hj⟩:=Finset.mem_product.mp hm
  have hs:=original_source_norms_ge_one p hp pool Q labels Y x hx
  have hq:∀i,1≤ firstCommonNorms p (leftNorm p x) (rightNorm p x) (commonNorm p x) (activeNorm p x)
      (divisorElement p x.1) x.2.2 j i:=by
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
  have hprof:firstNormProfile (fun y=> star (W y)) W Φ (fun _ _=>1) K
      (firstCommonNorms p (leftNorm p x) (rightNorm p x) (commonNorm p x) (activeNorm p x)
        (divisorElement p x.1) x.2.2 j)≠0:=by
    intro hzero
    exact hnon (by unfold sourceSummand;rw [hzero,mul_zero])
  have hb:=first_profile_live_products W Φ K (b*X) _ hq hW hprof
  constructor
  · change 1 ≤ X / (dyadScale (dyadIndex (leftNorm p x)) *
        dyadScale (dyadIndex (commonNorm p x)) *
        dyadScale (dyadIndex (primeProductNorm p j.2.1))) * b
    exact dyadic_column_scale (hs 0) (hs 2) (primeProductNorm_ge_one p hp _) hb.1
  · change 1 ≤ X / (dyadScale (dyadIndex (rightNorm p x)) *
        dyadScale (dyadIndex (commonNorm p x)) *
        dyadScale (dyadIndex (primeProductNorm p j.2.1))) * b
    exact dyadic_column_scale (hs 1) (hs 2) (primeProductNorm_ge_one p hp _) hb.2

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile
open Eisenstein (ringComplex)
local notation "O"=> Eisenstein.O

theorem first_live_cell_radius_one {ι:Type}[DecidableEq ι]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))(Y Z M r ell V eta tau:ℝ)
    (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(K:ℝ)
    (hlabels:∀I∈labels,I≠0):
    let cutoff:=fun (q:CubeCoordinates ι)(C:Finset ι)(_I:Ideal O)(D:Finset ι)=> firstDyadicRadius p q C D Z M r ell V eta tau;
    ∀k∈liveJointKeys p
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=> labels) (fun x=> x.1) Y) pool
      (sourceSummand p hp hg β cutoff Ψ m mark W Φ K),1≤ firstCellRadius Z M r ell V eta tau k.1 k.2.2:=by
  intro cutoff k hk
  obtain ⟨⟨x,j⟩,hm,rfl⟩:=Finset.mem_image.mp hk
  obtain ⟨hm,hnon⟩:=Finset.mem_filter.mp hm
  have hx:=(Finset.mem_product.mp hm).1
  have hweight:firstOriginalWeight p β cutoff x.1 x.2≠0:=by
    intro hh
    exact hnon (sourceSummand_zero_of_weight p hp hcop hg β cutoff Ψ m mark W Φ K x j hh)
  have hrow:=original_weight_frequency p β cutoff x hweight
  obtain ⟨ho,hf⟩:=Finset.mem_sigma.mp hx
  obtain ⟨hI,hfreq⟩:=(mem_firstRetainedSource p labels x.1.1 Y x.2).mp hf
  have hfreq0:x.2.2≠0:=(Finset.mem_erase.mp hfreq).1
  have hE:=firstPhysicalMultiplier_ne_zero p hp x.1.1.support x.1.1.leftExponent x.1.1.rightExponent
    x.1.1.leftBit x.1.1.rightBit x.2.1 (hlabels _ hI)
  have hn:= (mem_childFrequencyBall _ hE _ _).mp hrow
  have hone:=SchwartzPlanePoisson.one_le_eisenstein_norm_sq _ (mul_ne_zero hE hfreq0)
  have href:x.1∈refinedOuter p pool Q (sourceIndex (InverseMomentFirstOriginalProfile.originalNorms p) x)
      (labelGate p (dyadIndex (InverseFirstGlobalCaps.jNorm p x.1))):=by
    rw [refinedOuter_label]
    refine Finset.mem_filter.mpr ⟨?_,rfl⟩
    exact InverseFirstGlobalCaps.sourceCell_outer p pool Q labels Y _ _ (Finset.mem_filter.mpr ⟨hx,rfl⟩)
  change 1≤ firstCellRadius Z M r ell V eta tau (sourceIndex (InverseMomentFirstOriginalProfile.originalNorms p) x)
    (dyadIndex (InverseFirstGlobalCaps.jNorm p x.1))
  rw [←first_dyadic_radius_cell p pool Q _ _ x.1 href]
  exact hone.trans hn

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment

 theorem first_step_scalar_caps (Z A M r ell V delta aa bb rr t j eta tau window b:ℝ)
    (hZ:1< Z)(hA:0≤ A)(hM:0≤ M)(hMcap:M≤ A)(hr: -1≤ r)(hrcap:r≤ A)
    (hell:0≤ ell)(hellcap:ell≤ A)(hV:0≤ V)(hVcap:V≤ A)
    (hd:0≤ delta)(hdcap:delta≤ A)(haa:0≤ aa)(haacap:aa≤ A)
    (hbb:0≤ bb)(hbbcap:bb≤ A)(hrr:0≤ rr)(_hrrcap:rr≤ A)
    (ht:0≤ t)(_htcap:t≤ A)(hj:0≤ j)(hjcap:j≤ A)
    (heta:0≤ eta)(heta1:eta≤1)(htau:0≤ tau)(htau1:tau≤1)
    (hwindow:Real.exp window≤ Z^eta)(hb:b≤ Z^eta):
    let X:=Z^(r-aa-bb-t);
    let Y:=Z^(firstPhysicalHeight M r ell V delta bb j+12*eta+tau);
    X*Real.exp window≤ Z^(A+1) ∧ Y≤ Z^(16*A+20) ∧ Y⁻¹≤ Z^(4*A+2) ∧
    b*X≤ Z^(16*A+20) ∧ delta+eta+2*(A+1)+tau+(4*A+2)≤16*A+20 ∧
    firstKappa M r ell V delta aa bb rr+(9/2:ℝ)*eta≤16*A+20 ∧
    (∀e:ℝ,e≤ A→Z^(e+eta)≤ Z^(16*A+20)):=by
  intro X Y
  have hz:0< Z:=zero_lt_one.trans hZ
  have hX:X≤ Z^A:=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hX0:0≤ X:=Real.rpow_nonneg hz.le _
  have hxy:X*Real.exp window≤ Z^(A+1):=by
    calc
      _≤ Z^A*Z^eta:=mul_le_mul hX hwindow (Real.exp_pos _).le (Real.rpow_nonneg hz.le _)
      _=Z^(A+eta):=(Real.rpow_add hz A eta).symm
      _≤ Z^(A+1):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  refine ⟨hxy,?_,?_,?_,by linarith,?_,?_⟩
  · apply Real.rpow_le_rpow_of_exponent_le hZ.le
    unfold firstPhysicalHeight
    linarith
  · rw [show Y⁻¹=Z^(-(firstPhysicalHeight M r ell V delta bb j+12*eta+tau)) by
      dsimp [Y];rw [Real.rpow_neg hz.le]]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    unfold firstPhysicalHeight
    linarith
  · calc
      b*X≤ Z^eta*Z^A:=mul_le_mul hb hX hX0 (Real.rpow_nonneg hz.le _)
      _=Z^(eta+A):=(Real.rpow_add hz eta A).symm
      _≤ Z^(16*A+20):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  · unfold firstKappa
    linarith
  · intro e he
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith

theorem first_step_scalar_losses (A r ell aa bb rr t eta pi em ed:ℝ)
    (hA:0≤ A)(hr:r≤ A)(hell:ell≤ A)(haa:0≤ aa)(_hbb:0≤ bb)(hbbA:bb≤ A)
    (hrr:rr≤ A)(_ht:0≤ t)(htA:t≤ A)(_heta:0≤ eta)(heta1:eta≤1)
    (he:0≤ em)(hd:0≤ ed)(hpi:0≤ pi)(hetaPi:6*eta≤ pi)
    (hem:em*(20*A+30)≤ pi/4)(hed:ed*(20*A+30)≤ pi/4):
    em*(ell+rr/2+t+(16*A+20)+11*eta/2)≤ pi ∧
    em*(r-aa-bb-t)+7*eta/2+ed*(3*ell+bb+t+5*eta)+
      2*em*(2*ell+bb+t+4*eta)≤ pi+eta/2:=by
  have hm:=mul_le_mul_of_nonneg_left (show ell+rr/2+t+(16*A+20)+11*eta/2≤20*A+30 by linarith) he
  have h1:=mul_le_mul_of_nonneg_left (show r-aa-bb-t+2*(2*ell+bb+t+4*eta)≤20*A+30 by linarith) he
  have h2:=mul_le_mul_of_nonneg_left (show 3*ell+bb+t+5*eta≤20*A+30 by linarith) hd
  constructor <;> nlinarith

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstLabelCell CompletedHeight
open Eisenstein (ringComplex)
local notation "O"=> Eisenstein.O

lemma columnScale_physical (Z r:ℝ)(hZ:1< Z)(k:SourceIndex)(l:ℕ)(negative:Bool):
    columnScale Z r k l negative=physicalScales (Z^r) k l (if negative then 7 else 8):=by
  rw [physicalScales_rpow Z r hZ k l]
  cases negative <;> rfl

 theorem original_live_step_scalars {ι:Type}[DecidableEq ι]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
    (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)(om:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (K Z M r ell V F eta tau theta oldb b window em ed pi:ℝ)
    (hZ:1< Z)(hbin:2≤ Z^eta)(hF:0≤ F)(hM:0≤ M)(hMF:M≤ F)
    (hr: -eta≤ r)(hrF:r≤ F)(hell:0≤ ell)(hellF:ell≤ F)(hV:0≤ V)(hVF:V≤ F)
    (heta:0≤ eta)(heta1:eta≤1)(htau:0≤ tau)(htau1:tau≤1)
    (hwindow:Real.exp window≤ Z^eta)(hold:oldb≤ Real.exp window)(hb:b≤ Real.exp window)
    (hem:0≤ em)(hed:0≤ ed)(hpi:0≤ pi)(hetapi:6*eta≤ pi)
    (hsmall:em*(20*(3*F+16)+30)≤ pi/4)(hsmall':ed*(20*(3*F+16)+30)≤ pi/4)
    (hQ:∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta))
    (hlabels:∀I∈labels,I≠0)(hs:∀y,om y≠0→y≤ oldb):
    let A:=3*F+16;
    let cutoff:=fun (q:CubeCoordinates ι)(C:Finset ι)(_I:Ideal O)(D:Finset ι)=> firstDyadicRadius p q C D Z M r ell V eta tau;
    let W:=fun y=> normTwistedSource om theta (y/Z^r);
    let S:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=> labels) (fun x=> x.1) (Z^(2*F+15*eta+tau));
    ∀k∈liveJointKeys p S pool (sourceSummand p hp hg β cutoff Ψ m mark W Φ K),∀negative:Bool,
      let X:=columnScale Z r k.1 k.2.1 negative;
      let Y:=firstCellRadius Z M r ell V eta tau k.1 k.2.2;
      1≤ Y ∧ 1≤ X*Real.exp window ∧ X*Real.exp window≤ Z^(A+1) ∧ Y≤ Z^(16*A+20) ∧ Y⁻¹≤ Z^(4*A+2) ∧
      b*X≤ Z^(16*A+20) ∧ exponent Z (k.1 3)+eta+2*(A+1)+tau+(4*A+2)≤16*A+20 ∧
      firstKappa M r ell V (exponent Z (k.1 3)) (columnA Z k.1 negative) (exponent Z (k.1 2)) (exponent Z (k.1 4))+
        (9/2:ℝ)*eta≤16*A+20 ∧
      em*(ell+exponent Z (k.1 4)/2+exponent Z k.2.1+(16*A+20)+11*eta/2)≤ pi ∧
      em*(r-columnA Z k.1 negative-exponent Z (k.1 2)-exponent Z k.2.1)+7*eta/2+
        ed*(3*ell+exponent Z (k.1 2)+exponent Z k.2.1+5*eta)+
        2*em*(2*ell+exponent Z (k.1 2)+exponent Z k.2.1+4*eta)≤ pi+eta/2 ∧
      ell+eta≤16*A+20 ∧ exponent Z (k.1 4)+eta≤16*A+20 ∧
      exponent Z (k.1 2)+eta≤16*A+20 ∧ exponent Z k.2.1+eta≤16*A+20:=by
  intro A cutoff W S k hk negative X Y
  have hz:0< Z:=zero_lt_one.trans hZ
  have hA:0≤ A:=by dsimp [A];linarith
  have hFA:F≤ A:=by dsimp [A];linarith
  obtain ⟨hcoords,ht,hj⟩:=original_live_exponent_caps p hp hcop hg pool Q labels β cutoff Ψ m mark om Φ K Z r ell F eta tau theta oldb
    hZ hbin hF hrF hellF heta htau (hold.trans hwindow) hQ hlabels hs k hk
  have hecap:3*F+15*eta+tau≤ A:=by dsimp [A];linarith
  have hkcap:∀i,0≤ exponent Z (k.1 i) ∧ exponent Z (k.1 i)≤ A:=fun i=>⟨(hcoords i).1,(hcoords i).2.trans hecap⟩
  have hacap:0≤ columnA Z k.1 negative ∧ columnA Z k.1 negative≤ A:=hkcap (if negative then 0 else 1)
  have htcap:exponent Z k.2.1≤ A:=ht.2.trans hecap
  have hjcap:exponent Z k.2.2≤ A:=hj.2.trans hecap
  have hscl:=first_step_scalar_caps Z A M r ell V (exponent Z (k.1 3)) (columnA Z k.1 negative)
    (exponent Z (k.1 2)) (exponent Z (k.1 4)) (exponent Z k.2.1) (exponent Z k.2.2) eta tau window b
    hZ hA hM (hMF.trans hFA) (by linarith) (hrF.trans hFA) hell (hellF.trans hFA) hV (hVF.trans hFA)
    (hkcap 3).1 (hkcap 3).2 hacap.1 hacap.2 (hkcap 2).1 (hkcap 2).2 (hkcap 4).1 (hkcap 4).2
    ht.1 htcap hj.1 hjcap heta heta1 htau htau1 hwindow (hb.trans hwindow)
  have hloss:=first_step_scalar_losses A r ell (columnA Z k.1 negative) (exponent Z (k.1 2)) (exponent Z (k.1 4))
    (exponent Z k.2.1) eta pi em ed hA (hrF.trans hFA) (hellF.trans hFA) hacap.1 (hkcap 2).1 (hkcap 2).2
    (hkcap 4).2 ht.1 htcap heta heta1 hem hed hpi hetapi hsmall hsmall'
  have hYone:=first_live_cell_radius_one p hp hcop hg pool Q labels _ Z M r ell V eta tau β Ψ m mark W Φ K hlabels k hk
  have hW:∀y,W y≠0→y≤ oldb*Z^r:=by
    intro y hy
    have hnon:om (y/Z^r)≠0:=by intro h;exact hy (by simp [W,normTwistedSource,h])
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hz _)).mp (hs _ hnon)
  have hcol:=original_live_column_scale p hp hcop hg pool Q labels _ β cutoff Ψ m mark W Φ K (Z^r) oldb
    (Real.rpow_pos_of_pos hz _) hW k hk
  have hXone:1≤ X*Real.exp window:=by
    have hpos:0≤ X:=Real.rpow_nonneg hz.le _
    apply le_trans _ (mul_le_mul_of_nonneg_left hold hpos)
    dsimp [X]
    rw [columnScale_physical Z r hZ]
    cases negative
    · exact hcol.2
    · exact hcol.1
  refine ⟨hYone,hXone,hscl.1,hscl.2.1,hscl.2.2.1,hscl.2.2.2.1,hscl.2.2.2.2.1,
    hscl.2.2.2.2.2.1,hloss.1,hloss.2,?_,?_,?_,?_⟩ <;> linarith [(hkcap 4).2,(hkcap 2).2]

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstLabelCell CompletedHeight
open Eisenstein (ringComplex)
local notation "O"=> Eisenstein.O

theorem actual_live_label_step
    (old:ℝ → ℂ)(oldb:ℝ)(hsold:∀y,old y≠0 → y≤ oldb)
    (om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0< lo)(hs:Function.support om⊆Set.Icc lo hi)(negative:Bool)
    (F tau saving window b em ed:ℝ)(hF:0≤ F)(htau:0< tau)(hb:1≤ b)
    (hhib:hi≤ b)(hwindow: b≤ Real.exp window)(hold:oldb≤ Real.exp window)(hem:0< em)(hed:0< ed)(K:ℕ):
    ∃(ω₁ ω₂:𝓢(ℝ,ℂ))(af bf:ℝ),0< af ∧ af≤ bf ∧ HasCompactSupport (ω₁:ℝ → ℂ) ∧ HasCompactSupport (ω₂:ℝ → ℂ) ∧
      tsupport (ω₁:ℝ → ℂ)⊆Set.Icc af bf ∧ tsupport (ω₂:ℝ → ℂ)⊆Set.Icc af bf ∧
    ∀degree:ℕ,∃C Cbin Cz Ct:ℝ,0≤ C ∧ 0≤ Cbin ∧ 0≤ Cz ∧ 0≤ Ct ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι → O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i})
      (_hpr:∀i,lambda^2∣p i-1)(hinj:Function.Injective (fun i=> Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι)(Q:Finset (ι →₀ ℕ))(labels:Finset (Ideal O))(β:Ideal O → (ι →₀ ℕ) → ℂ)
      (Ψ:O →* ℂ)(m:O)(slots:Finset σ)(lists:σ → Finset ι)(weights:σ → ι → ℂ)
      (Φ:𝓢(ℝ,ℂ))(Z M r ell V eta pi epschild A theta t Kphysical:ℝ),
      2≤ Z → 2≤ Z^eta → 0≤ M → M≤ F →  (-eta≤ r)  → r≤ F → 0≤ ell → ell≤ F → 0≤ V → V≤ F →
      0≤ eta → eta≤1 → tau≤1 → Real.exp window≤ Z^eta → 0≤ pi → 6*eta≤ pi →
      em*(20*(3*F+16)+30)≤ pi/4 → ed*(20*(3*F+16)+30)≤ pi/4 →
      (∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta)) →
      (∀I∈labels,I≠0) → (∀u,‖Ψ u‖≤1) → (slots:Set σ).PairwiseDisjoint lists → slots.card≤ K →
      (∀i∈slots,∀q∈lists i,‖weights i q‖≤1) → 0≤ A →
      let cutoff:=fun (q:CubeCoordinates ι)(C:Finset ι)(_I:Ideal O)(D:Finset ι)=> firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=> normTwistedSource old theta (y/Z^r);
      let mark:=fun v U=> primeMark slots lists weights (v.support∪U);
      let S:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=> labels) (fun x=> x.1) (Z^(2*F+15*eta+tau));
      ∀k∈liveJointKeys p S pool (sourceSummand p hp hg β cutoff Ψ m mark W Φ Kphysical),
      ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 negative Ψ m slots lists weights ω₁ ω₂
        Z M r ell V eta tau window b epschild A K degree →
      (Z^(firstKappa M r ell V (exponent Z (k.1 3)) (columnA Z k.1 negative) (exponent Z (k.1 2)) (exponent Z (k.1 4)))*
        Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      globalPriorityOriginalEnergy p hg hp hinj (extra negative) pool
        (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2) (parentWeight p k.2.1)
        negative Ψ m slots lists weights om (columnScale Z r k.1 k.2.1 negative) t (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤
      Cz*Z^(r+3*ell+V+17*eta+tau+pi)+
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder (2*degree))*(1+Cbin*Real.log Z)^4*
        Z^(r+3*ell+V+48*eta+tau+pi+epschild)+Ct*Z^(-saving):=by
  let cap:=3*F+16
  have hcap:0≤ cap:=by dsimp [cap];linarith
  have hbig:0≤16*cap+20:=by positivity
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hw₁,hw₂,hs₁,hs₂,he⟩:=actual_label_cell_step om lo hi hlo hs negative
    window (16*cap+20) (16*cap+20) tau saving (hhib.trans hwindow) hbig hbig htau b hb ed hed (fun _=>0) (by intro i;norm_num) K em hem
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro degree
  obtain ⟨C,Cbin,Cz,Ct,hC,hCb,hCz,hCt,hstep⟩:=he degree
  refine ⟨C,Cbin,Cz,Ct,hC,hCb,hCz,hCt,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc pool Q labels β Ψ m slots lists weights Φ
    Z M r ell V eta pi epschild A theta t Kphysical hZ hbin hM hMF hr hrF hell hellF hV hVF heta heta1 htau1
    hwin hpi hetapi hsmall hsmall' hQ hn hΨ hslots hcard hw hA cutoff W mark S k hk hchild
  have hZ1:1< Z:=by linarith
  have hz:0< Z:=by linarith
  obtain ⟨hY1,hX1,hcol,hYcap,hYi,hgeom,hphysical,hPcap,hbudget,hcost,hellcap,hactivecap,hcommoncap,hquotcap⟩:=
    original_live_step_scalars p hp hcop hg pool Q labels β Ψ m mark old Φ Kphysical Z M r ell V F eta tau theta oldb b window em ed pi
      hZ1 hbin hF hM hMF hr hrF hell hellF hV hVF heta heta1 htau.le htau1 hwin hold hwindow hem.le hed.le hpi hetapi
      hsmall hsmall' hQ hn hsold k hk negative
  apply hstep p hp hcop hg hpr hinj hc pool Q k.1 k.2.1 k.2.2 Ψ m slots lists weights
    Z M r ell V eta pi b (cap+1) (4*cap+2) epschild A t (fun _=>0)
    hZ heta hbin (by linarith) hQ hslots hcard hw hΨ (by intro i;simp) hhib le_rfl hb
  · exact (hwindow.trans hwin).trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))
  · exact hwin.trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))
  · exact hA
  · exact hcol
  · exact hYi
  · exact hgeom
  · exact hphysical
  · exact hbudget
  · exact hcost
  · exact hY1
  · exact hX1
  · exact hYcap
  · exact hYi.trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))
  · exact hcol.trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))
  · exact hPcap
  · exact hellcap
  · exact hactivecap
  · exact hcommoncap
  · exact hquotcap
  · exact hchild

end InverseMoment

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

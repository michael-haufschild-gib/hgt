/-
Existence of rank energies adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.TwoPassHeightCost

/-!
# Existence of rank energies

Rank energy existence `RankEnergyExists` with row and total caps, margins and losses; actual
depth and first-pass epsilon; existence of canonical rank and marked energies.
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
open Eisenstein CompletedGauss CanonicalRowCompletion 
open CanonicalQuadraticSieve InverseInitialClippedColumns
local notation "Eis" => Eisenstein.O

theorem outside_pool_redundant_energy {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal Eis)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (hSp : ∀P∈S,Prime P)
    (pool : Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)))
    (Ψ : Eis →* ℂ) (m : Eis) (slots : Finset σ)
    (lists : σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (weight : Ideal Eis→ℝ)
    (W : ℝ→ℂ) (X Z Fexp : ℝ) :
    let F:=CanonicalRowCompletion.outsideSquarefreeIdeals S D
    let hF:=CanonicalRowCompletion.outsideSquarefree_admissible S D hbad
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_good F hF) pool Ψ
      (m*excludedGenerator S) slots lists a labels rows weight W X Z Fexp=
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_good F hF) pool Ψ
      m slots lists a labels rows weight W X Z Fexp := by
  let F:=CanonicalRowCompletion.outsideSquarefreeIdeals S D
  have hF:=CanonicalRowCompletion.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  apply normalizedColumnEnergy_redundant_puncture
  intro i hi hc
  rw [poolPrimary_span F hF i] at hc
  exact False.elim (excludedGenerator_not_mem_pool S D hSp i hc)

theorem reflection_pool_mask_energy {σ : Type*} [DecidableEq σ]
    (q D : ℕ)
    (pool : Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
    (Ψ : Eis →* ℂ) (m : Eis) (slots : Finset σ)
    (lists : σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
    (a : σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (weight : Ideal Eis→ℝ)
    (W : ℝ→ℂ) (X Z Fexp : ℝ) :
    let S:=reflectionExcludedPrimes q
    let F:=CanonicalRowCompletion.outsideSquarefreeIdeals S D
    let hF:=CanonicalRowCompletion.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q)
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_good F hF) pool Ψ
      (ActualFiber.maskElement q m) slots lists a labels rows weight W X Z Fexp=
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_good F hF) pool Ψ
      m slots lists a labels rows weight W X Z Fexp :=
  outside_pool_redundant_energy (reflectionExcludedPrimes q) D
    (reflectionExcludedPrimes_bad q) (reflectionExcludedPrimes_prime q)
    pool Ψ m slots lists a labels rows weight W X Z Fexp


end InverseMoment
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein CompletedGauss CanonicalRowCompletion 
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic InverseInitialClippedColumns
local notation "O"=> Eisenstein.O

theorem normalizedColumnEnergy_eq_generator_sum {ι σ:Type*}[DecidableEq ι][DecidableEq σ]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i})
    (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(hlabels:∀I∈labels,primaryIdealGenerator I≠0)
    (weight:Ideal O→ℝ)(W:ℝ→ℂ)(X Z F R:ℝ)(hZ:0< Z) :
    normalizedColumnEnergy p hg pool Ψ m slots lists a labels
      (nonzeroChildFrequencyBall 1 R) weight W X Z F=
    Z^(-F)*(∑I∈labels,weight I*∑k∈nonzeroChildFrequencyBall 1 R,
      ‖finiteCanonicalMarkedRow p hg pool Ψ m (cubicIdealGenerator I) k slots lists a W X‖^2) := by
  have hn:‖((Z^(-F/2):ℝ):ℂ)‖^2=Z^(-F) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hZ _),
      ←Real.rpow_mul_natCast hZ.le]
    congr 1
    ring
  unfold normalizedColumnEnergy
  simp only [norm_mul,mul_pow,hn,←Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [canonical_ball_generator_energy p hg pool Ψ m I (hlabels I hI)]
  ring

theorem outside_complete_normalized_energy {σ:Type*}[DecidableEq σ]
    (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)
    (Ψ:O→*ℂ)(m:O)(slots:Finset σ)
    (lists:σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)))
    (a:σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→ℂ)
    (labels:Finset (Ideal O))(hlabels:∀I∈labels,Supported I)
    (weight:Ideal O→ℝ)(W:ℝ→ℂ)(X Z Fexp R:ℝ)(hZ:0< Z) :
    let F:=CanonicalRowCompletion.outsideSquarefreeIdeals S D
    let hF:=CanonicalRowCompletion.outsideSquarefree_admissible S D hbad
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=> by rw [poolPrimary_span F hF i];infer_instance
    Z^(-Fexp)*(∑I∈labels,weight I*∑k∈nonzeroChildFrequencyBall 1 R,
      ‖outsideCanonicalMarkedRow S D hbad Ψ m (cubicIdealGenerator I) k slots lists a W X‖^2)=
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_good F hF) Finset.univ Ψ m slots lists a labels
      (nonzeroChildFrequencyBall 1 R) weight W X Z Fexp := by
  let F:=CanonicalRowCompletion.outsideSquarefreeIdeals S D
  have hF:=CanonicalRowCompletion.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=> by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  exact (normalizedColumnEnergy_eq_generator_sum (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Ψ m slots lists a labels
    (fun I hI=> primaryIdealGenerator_ne_zero_of_good_factors I (hlabels I hI).1
      (fun P hP => ((hlabels I hI).2 P hP).1)) weight W X Z Fexp R hZ).symm

theorem reflection_complete_normalized_energy {σ:Type*}[DecidableEq σ]
    (q D:ℕ)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)
    (lists:σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
    (a:σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ)
    (labels:Finset (Ideal O))(hlabels:∀I∈labels,Supported I)
    (weight:Ideal O→ℝ)(W:ℝ→ℂ)(X Z Fexp R:ℝ)(hZ:0< Z) :
    let S:=reflectionExcludedPrimes q
    let F:=CanonicalRowCompletion.outsideSquarefreeIdeals S D
    let hF:=CanonicalRowCompletion.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q)
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=> by rw [poolPrimary_span F hF i];infer_instance
    Z^(-Fexp)*(∑I∈labels,weight I*∑k∈nonzeroChildFrequencyBall 1 R,
      ‖outsideCanonicalMarkedRow S D (reflectionExcludedPrimes_bad q) Ψ m (cubicIdealGenerator I) k
        slots lists a W X‖^2)=
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_good F hF) Finset.univ Ψ
      (ActualFiber.maskElement q m) slots lists a labels
      (nonzeroChildFrequencyBall 1 R) weight W X Z Fexp := by
  have h:=outside_complete_normalized_energy (reflectionExcludedPrimes q) D
    (reflectionExcludedPrimes_bad q) Ψ m slots lists a labels hlabels weight W X Z Fexp R hZ
  exact h.trans (reflection_pool_mask_energy q D Finset.univ Ψ m slots lists a labels
    (nonzeroChildFrequencyBall 1 R) weight W X Z Fexp).symm

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open MeasureTheory Eisenstein CompletedGauss CanonicalRowCompletion 
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstLabelCell InverseMomentFirstSecondHeightCost CompletedHeight
open InverseInitialClippedColumns JointLogSeparation JointLogSeparation InverseReflectedPhase InverseTerminalWidths InverseSecondFibers
local notation "O"=> Eisenstein.O

theorem actual_complete_normalized_rank_step
    (lo hi:ℝ)(hlo:0< lo)(hhi:0≤ hi)(W:ℝ→ℂ)
    (hsW:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W)
    (Vlog:𝓢(ℝ,ℂ))(Alog:ℝ)(hbox:∀x,Vlog x≠0 → |x|≤ Alog)
    (hone:∀x,|x|≤ columnWindowRadius lo hi → Vlog x=1)
    (L cstar eta tau saving em ed eps:ℝ)(hL:1≤ L)(hcstar:0< cstar)(heta:0< eta)
    (heta1:eta≤1)(hetac:eta≤ cstar/100000)(htau:0< tau)(htau1:tau≤1)
    (hem:0< em)(hed:0< ed)(heps:0< eps)(K:ℕ):
    ∃(ω₁₁ ω₁₂ ω₂₁ ω₂₂:𝓢(ℝ,ℂ))(af₁ bf₁ af₂ bf₂ window bw:ℝ)(shortDegree:ℕ),
      0< af₁ ∧ af₁≤ bf₁ ∧ 0< af₂ ∧ af₂≤ bf₂ ∧
      HasCompactSupport (ω₁₁:ℝ→ℂ) ∧ HasCompactSupport (ω₁₂:ℝ→ℂ) ∧
      HasCompactSupport (ω₂₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂₂:ℝ→ℂ) ∧
      tsupport (ω₁₁:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧ tsupport (ω₁₂:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧
      tsupport (ω₂₁:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧ tsupport (ω₂₂:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧
      1≤ bw ∧ Real.exp Alog≤ bw ∧ bw=Real.exp window ∧
    ∀epsFirst epsSecond:ℝ,0< epsFirst → 0< epsSecond → ∀degree:ℕ,
    ∀(q:ℕ)(hq:q≠0),∃Cs Cb Z₀:ℝ,0< Cs ∧ 0≤ Cb ∧ 1< Z₀ ∧
    ∀{σ:Type}[DecidableEq σ](m:O),m≠0 →
    ∀Z N V M z₀ margin cutoff pi epschild A loss lossFinal theta:ℝ,
      Z₀≤ Z → 2≤ Z → 2≤ Z^eta → Real.exp 1≤ Z^eta → 1≤ eta*Real.log Z →
      0≤ N → 0≤ V → 0≤ M → N+V≤ L → M≤ N+V → z₀≤ L →
      hi≤ Z^eta → Real.exp Alog≤ Z^eta → Real.exp window≤ Z^eta →
      0< cutoff → cutoff≤ L → cutoff≤ cstar/200 → eta≤ cutoff/32 →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤ Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤ margin →
      (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤ Z^(normWidth Z (Ideal.span {m})) →
      0≤ pi → 6*eta≤ pi → em*(20*(3*L+16)+30)≤ pi/4 → ed*(20*(3*L+16)+30)≤ pi/4 →
      0≤ epschild → -saving≤48*eta+tau+pi+epschild+epsSecond →
      48*eta+tau+pi+epschild+epsSecond≤ loss →
      3*eta+epsFirst*(2*L+7*eta)≤ lossFinal →
      loss+(2*L+15*eta+tau)*epsFirst+epsFirst≤ lossFinal → -saving≤ lossFinal →
      0≤ A →
    ∀labels:Finset (Ideal O),(∀I∈labels,Supported I ∧ Squarefree I ∧ (I.absNorm:ℝ)≤ Z^V) →
    ∀D:ℕ,hi*Z^N≤ D → ∀slots:Finset σ,slots.card≤ K →
    ∀(lists:σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))(H:σ→ℝ),
      (slots:Set σ).PairwiseDisjoint lists →
      (∀i∈slots,1≤ H i) → (∀i∈slots,∀P∈lists i,(Ideal.absNorm P.val:ℝ)≤ H i) → (∏i∈slots,H i)≤ Z^z₀ →
    ∀(base Ψ:O→*ℂ),CanonicalCoefficientClass.IsBaseRayTwist base Ψ → (∀u,‖Ψ u‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀a:σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ,
      (∀i∈slots,∀P∈lists i,‖a i P‖≤1) →
      let S:=reflectionExcludedPrimes q;
      let F:=CanonicalRowCompletion.outsideSquarefreeIdeals S D;
      let hF:=CanonicalRowCompletion.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q);
      letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=> by rw [poolPrimary_span F hF i];infer_instance;
      let _om:=radialFromLog Vlog (Vlog.smooth ⊤) Alog hbox;
      CanonicalRankMoments (poolPrimary F)
        (poolPrimary_good F hF) Finset.univ base slots lists a ω₁₁
        Z (M-3*(cutoff/2)/2) (N+V+15*eta) z₀ (margin-7*eta) epschild A K degree →
      CanonicalRankMoments (poolPrimary F)
        (poolPrimary_good F hF) Finset.univ base slots lists a ω₁₂
        Z (M-3*(cutoff/2)/2) (N+V+15*eta) z₀ (margin-7*eta) epschild A K degree →
      CanonicalRankMoments (poolPrimary F)
        (poolPrimary_good F hF) Finset.univ base slots lists a ω₂₁
        Z (M-3*(cutoff/2)/2) (N+V+15*eta) z₀ (margin-7*eta) epschild A K degree →
      CanonicalRankMoments (poolPrimary F)
        (poolPrimary_good F hF) Finset.univ base slots lists a ω₂₂
        Z (M-3*(cutoff/2)/2) (N+V+15*eta) z₀ (margin-7*eta) epschild A K degree →
      normalizedColumnEnergy (poolPrimary F) (poolPrimary_good F hF) Finset.univ Ψ m slots lists a labels
        (nonzeroChildFrequencyBall 1 (Z^M)) (secondLabelWeight K) (normTwistedSource W theta)
        (Z^N) Z (N+V)≤
      Cs*(1+‖theta‖)^shortDegree*Z^(N+V-cstar/256)+
      Cb*(1+A)*(1+‖theta‖)^(2*(InverseClippingProfiles.momentOrder (firstDegree degree)+(volume:Measure ℝ).integrablePower))*
        Z^(N+V+lossFinal+2*L*epsFirst+eps) := by
  obtain ⟨w11,w12,w21,w22,af1,bf1,af2,bf2,window,bw,ds,ha1,hab1,ha2,hab2,
    hw11,hw12,hw21,hw22,hs11,hs12,hs21,hs22,hbw,hbA,hbexp,hstep⟩:=
    actual_complete_state_from_rank_moments lo hi hlo hhi W hsW hW Vlog Alog hbox hone
      L cstar eta tau saving em ed eps hL hcstar heta heta1 hetac htau htau1 hem hed heps K
  refine ⟨w11,w12,w21,w22,af1,bf1,af2,bf2,window,bw,ds,ha1,hab1,ha2,hab2,
    hw11,hw12,hw21,hw22,hs11,hs12,hs21,hs22,hbw,hbA,hbexp,?_⟩
  intro epsFirst epsSecond heF heS degree q hq
  obtain ⟨Cs,Cb,Z₀,hCs,hCb,hZ₀,hstep⟩:=hstep epsFirst epsSecond heF heS degree q hq
  refine ⟨Cs,Cb,Z₀,hCs,hCb,hZ₀,?_⟩
  intro σ _ m hm Z N V M z₀ margin cutoff pi epschild A loss lossFinal theta hZ hZ2 h2 hExp hlog
    hN hV hM hFcap hMF hzcap hbZ hAZ hwin hcut hcutL hcutc hsmall hmN hmargin hreserve hpuncture
    hpi hpieta hemc hedc hechild hsave hloss hprincipal hretained htail hA
    labels hlabels D hD slots hcard lists H hdis hH1 hH hprod base Ψ hbase hΨ hperiod a ha
  dsimp only
  intro h11 h12 h21 h22
  have hh:=hstep m hm Z N V M z₀ margin cutoff pi epschild A loss lossFinal theta hZ hZ2 h2 hExp hlog
    hN hV hM hFcap hMF hzcap hbZ hAZ hwin hcut hcutL hcutc hsmall hmN hmargin hreserve hpuncture
    hpi hpieta hemc hedc hechild hsave hloss hprincipal hretained htail hA
    labels hlabels D hD slots hcard lists H hdis hH1 hH hprod base Ψ hbase hΨ hperiod a ha h11 h12 h21 h22
  rw [outside_complete_normalized_energy (reflectionExcludedPrimes q) D (reflectionExcludedPrimes_bad q)
    Ψ m slots lists a labels (fun I hI=>(hlabels I hI).1) (secondLabelWeight K)
    (normTwistedSource W theta) (Z^N) Z (N+V) (Z^M) (by linarith)] at hh
  exact hh

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment

def actualDepth (Mmax cutoff : ℝ) : ℕ := ⌈2*Mmax/(3*cutoff)⌉₊+1

lemma actualDepth_pos (Mmax cutoff : ℝ) : 0< actualDepth Mmax cutoff := by
  exact Nat.succ_pos _

lemma actualDepth_strict (Mmax cutoff : ℝ) :
    2*Mmax/(3*cutoff)<(actualDepth Mmax cutoff:ℝ) := by
  have h := Nat.le_ceil (2*Mmax/(3*cutoff))
  unfold actualDepth
  push_cast
  linarith


end InverseMoment
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment

def firstPassEpsilon (F eta:ℝ):ℝ:=eta/(10*F+32)
def sourceMassEpsilon (F eta:ℝ):ℝ:=2*eta/(20*(3*F+16)+30)

theorem actual_step_parameters (F eta r ell epsChild:ℝ)
    (hF:0≤ F)(heta:0< eta)(heta1:eta≤1)(hr:r≤ F)(hell:ell≤ F)(heps:0≤ epsChild):
    0< firstPassEpsilon F eta ∧ 0< sourceMassEpsilon F eta ∧
    6*eta≤8*eta ∧
    sourceMassEpsilon F eta*(20*(3*F+16)+30)≤(8*eta)/4 ∧
    48*eta+eta+8*eta+epsChild+eta≤ epsChild+58*eta ∧
    3*eta+firstPassEpsilon F eta*(5*ell+2*r+7*eta)≤ epsChild+60*eta ∧
    (epsChild+58*eta)+(2*F+15*eta+eta)*firstPassEpsilon F eta+firstPassEpsilon F eta≤ epsChild+60*eta :=by
  have hd:0<10*F+32:=by positivity
  have hm:0<20*(3*F+16)+30:=by positivity
  have he:0< firstPassEpsilon F eta:=div_pos heta hd
  have heq:firstPassEpsilon F eta*(10*F+32)=eta:=by unfold firstPassEpsilon;field_simp
  have heq':sourceMassEpsilon F eta*(20*(3*F+16)+30)=2*eta:=by unfold sourceMassEpsilon;field_simp
  refine ⟨he,div_pos (by positivity) hm,by linarith,by linarith,by ring_nf;linarith,?_,?_⟩
  · have hcap:5*ell+2*r+7*eta≤10*F+32:=by linarith
    have hh:=mul_le_mul_of_nonneg_left hcap he.le
    nlinarith
  · have hcap:2*F+15*eta+eta+1≤10*F+32:=by linarith
    have hh:=mul_le_mul_of_nonneg_left hcap he.le
    nlinarith

theorem actual_long_rank_slack (cutoff eta ell V:ℝ)(hd:0< cutoff)(_he:0≤ eta)
    (hsmall:eta≤ cutoff/32)(hprogress:cutoff-eta≤ ell+V):
    0< cutoff/2 ∧ cutoff/2≤ ell+V ∧ eta≤(cutoff/2)/16 ∧ 17*eta≤ cutoff :=by
  constructor
  · positivity
  constructor
  · linarith
  constructor <;> linarith

theorem actual_recursion_parameters (Mcap Fcap c eps:ℝ)(_hM:0≤ Mcap)(_hF:0≤ Fcap)(hc:0< c)(heps:0< eps):
    ∃cutoff eta:ℝ,0< cutoff ∧ 0< eta ∧ eta≤1 ∧ eta≤ cutoff/32 ∧
      cutoff≤(c/2)/200 ∧ eta≤(c/2)/100000 ∧
      let depth:=actualDepth Mcap (cutoff/2);
      (depth:ℝ)*7*eta≤ c/2 ∧ (depth:ℝ)*15*eta≤1 ∧
      (depth:ℝ)*100*eta≤ eps/4 :=by
  let cutoff:=c/1000
  have hd:0< cutoff:=by dsimp[cutoff];positivity
  let depth:=actualDepth Mcap (cutoff/2)
  let D:ℝ:=(depth:ℝ)+1
  have hD:0< D:=by dsimp[D];positivity
  let eta:=min 1 (min (cutoff/32) (min (c/200000) (min (c/(28*D)) (min (1/(30*D)) (eps/(800*D))))))
  have he:0< eta:=by dsimp[eta];positivity
  have he1:eta≤1:=min_le_left _ _
  have he2:eta≤ cutoff/32:=(min_le_right _ _).trans (min_le_left _ _)
  have he3:eta≤ c/200000:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have he4:eta≤ c/(28*D):=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have he5:eta≤1/(30*D):=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have he6:eta≤ eps/(800*D):=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  refine ⟨cutoff,eta,hd,he,he1,he2,by dsimp[cutoff];linarith,by linarith,?_⟩
  have h4:eta*(28*D)≤ c:=(le_div_iff₀ (by positivity)).mp he4
  have h5:eta*(30*D)≤1:=(le_div_iff₀ (by positivity)).mp he5
  have h6:eta*(800*D)≤ eps:=(le_div_iff₀ (by positivity)).mp he6
  have hn:(depth:ℝ)*eta≤ D*eta:=mul_le_mul_of_nonneg_right (by dsimp[D];linarith) he.le
  change (depth:ℝ)*7*eta≤ c/2 ∧ (depth:ℝ)*15*eta≤1 ∧ (depth:ℝ)*100*eta≤ eps/4
  constructor <;> first | nlinarith | constructor <;> nlinarith

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment

theorem actual_complete_step_cost (L eta epsChild:ℝ)(hL:0≤ L)(heta:0< eta)
    (heta1:eta≤1)(heps:0≤ epsChild):
    3*eta+firstPassEpsilon L eta*(2*L+7*eta)≤ epsChild+60*eta ∧
    2*L*firstPassEpsilon L eta≤ eta ∧
    (epsChild+60*eta)+2*L*firstPassEpsilon L eta+eta≤ epsChild+62*eta := by
  have hd:0<10*L+32:=by positivity
  have hp:0< firstPassEpsilon L eta:=div_pos heta hd
  have he:firstPassEpsilon L eta*(10*L+32)=eta:=by unfold firstPassEpsilon;field_simp
  have hb:2*L+7*eta≤10*L+32:=by linarith
  have hc:=mul_le_mul_of_nonneg_left hb hp.le
  have hl:=mul_le_mul_of_nonneg_left (show 2*L≤10*L+32 by linarith) hp.le
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem actual_complete_height_merge (dshort dlong:ℕ)(Z F cstar loss Cs Cb A theta:ℝ)
    (hZ:1≤ Z)(hcstar:0≤ cstar)(hloss:0≤ loss)(hCs:0≤ Cs)(hCb:0≤ Cb)(hA:0≤ A):
    Cs*(1+‖theta‖)^dshort*Z^(F-cstar/256)+
      Cb*(1+A)*(1+‖theta‖)^dlong*Z^(F+loss)≤
    (Cs+Cb)*(1+A)*(1+‖theta‖)^(max dshort dlong)*Z^(F+loss) := by
  have hp:1≤1+‖theta‖:=by linarith [norm_nonneg theta]
  have hshort:(1+‖theta‖)^dshort≤(1+‖theta‖)^(max dshort dlong):=
    pow_le_pow_right₀ hp (le_max_left _ _)
  have hlong:(1+‖theta‖)^dlong≤(1+‖theta‖)^(max dshort dlong):=
    pow_le_pow_right₀ hp (le_max_right _ _)
  have hz:0< Z:=zero_lt_one.trans_le hZ
  have hs:Z^(F-cstar/256)≤ Z^(F+loss):=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hs':Cs*(1+‖theta‖)^dshort*Z^(F-cstar/256)≤
      Cs*(1+A)*(1+‖theta‖)^(max dshort dlong)*Z^(F+loss):=by
    calc
      _≤ Cs*(1+‖theta‖)^(max dshort dlong)*Z^(F+loss):=by gcongr
      _≤ _:=by
        have hh:Cs≤ Cs*(1+A):=by nlinarith
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (by positivity)) (by positivity)
  have hl':Cb*(1+A)*(1+‖theta‖)^dlong*Z^(F+loss)≤
      Cb*(1+A)*(1+‖theta‖)^(max dshort dlong)*Z^(F+loss):=by gcongr
  have hh:=add_le_add hs' hl'
  simpa only [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, one_mul, mul_one, add_assoc, add_left_comm, add_comm] using hh

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein InverseTerminalWidths
local notation "O"=> Eisenstein.O

theorem actual_rank_parent_puncture (m:O)(hm:m≠0)(Z:ℝ)(hZ:1< Z):
    (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤ Z^(normWidth Z (Ideal.span {m})) :=by
  have hi:(Ideal.span {m}:Ideal O)≠0:=Ideal.span_singleton_eq_bot.not.mpr hm
  have hn:0<(Ideal.absNorm (Ideal.span {m}:Ideal O):ℝ):=actual_ideal_norm_pos _ hi
  have hle:Ideal.absNorm (Ideal.span {m}:Ideal O).radical≤ Ideal.absNorm (Ideal.span {m}:Ideal O):=
    Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hi))
      (Ideal.absNorm_dvd_absNorm_of_le Ideal.le_radical)
  unfold normWidth
  rw [Real.rpow_logb (by linarith:0< Z) (ne_of_gt hZ) hn]
  exact_mod_cast hle

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein CanonicalCoefficientClass InverseTerminalWidths
open  CompletedGauss
local notation "O"=> Eisenstein.O

theorem actual_rank_family_period (q:ℕ)(base Ψ:O→*ℂ)
    (hbase:FactorsModulo (fixedBaseConductor q) base)
    (hΨ:IsBaseRayTwist base Ψ):
    FactorsModulo (fixedBaseConductor q) Ψ := by
  intro x y hxy
  rcases hΨ with rfl|⟨χ,rfl⟩
  · exact hbase x y hxy
  · simp only [MonoidHom.mul_apply]
    rw [hbase x y hxy]
    congr 1
    change χ (Ideal.Quotient.mk (Ideal.span {(4 : O)}) x) =
      χ (Ideal.Quotient.mk (Ideal.span {(4 : O)}) y)
    apply congrArg χ
    apply Ideal.Quotient.eq.mpr
    exact (Ideal.mul_le_left : fixedBaseConductor q ≤ Ideal.span {(4 : O)}) hxy

theorem actual_rank_family_gates (q:ℕ)(base:O→*ℂ)
    (hbase:∀x,‖base x‖≤1)(hperiod:FactorsModulo (fixedBaseConductor q) base):
    ∀Ψ:O→*ℂ,IsBaseRayTwist base Ψ→
      (∀x,‖Ψ x‖≤1) ∧ FactorsModulo (fixedBaseConductor q) Ψ := by
  intro Ψ hΨ
  exact ⟨hΨ.norm_le hbase,actual_rank_family_period q base Ψ hperiod hΨ⟩

theorem actual_rank_norm_width (m:O)(Z Q:ℝ)(hZ:1< Z)
    (hn:‖ringComplex m‖^2=Z^Q):
    normWidth Z (Ideal.span {m})=Q := by
  rw [ringComplex_norm_sq_eq_absNorm_span] at hn
  rw [normWidth,hn,Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)]

theorem actual_rank_state_gates (m:O)(hm:m≠0)(Z N V M Q z c L:ℝ)
    (hZ:1< Z)(hN:0≤ N)(hV:0≤ V)(hM:0≤ M)(hQ:0≤ Q)(hz:0≤ z)(hc:0≤ c)
    (hcap:N+V≤ L)(hmargin:CanonicalMargins (N+V) M Q z c)
    (hn:‖ringComplex m‖^2=Z^Q):
    N≤ L ∧ V≤ L ∧ M≤ N+V ∧ Q≤ L ∧ z≤ L ∧
      normWidth Z (Ideal.span {m})=Q ∧
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z c ∧
      (Ideal.absNorm (Ideal.span {m}:Ideal O):ℝ)≤ Z^L ∧
      (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤ Z^Q := by
  have hfirst:=hmargin.1
  have hQcap:Q≤ L:=by linarith
  have he:=actual_rank_norm_width m Z Q hZ hn
  refine ⟨by linarith,by linarith,by linarith,hQcap,by linarith,he,?_,?_,?_⟩
  · rwa [he]
  · rw [ringComplex_norm_sq_eq_absNorm_span] at hn
    rw [hn]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le hQcap
  · simpa only [he] using actual_rank_parent_puncture m hm Z hZ

theorem canonical_rank_subslots {ι σ:Type}[DecidableEq ι][DecidableEq σ]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i})
    (pool:Finset ι)(base:O→*ℂ)(slots subslots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z M F z c eps A:ℝ)(K degree:ℕ)(hsub:subslots⊆slots)
    (h:CanonicalRankMoments p hg pool base slots lists a W Z M F z c eps A K degree):
    CanonicalRankMoments p hg pool base subslots lists a W Z M F z c eps A K degree := by
  intro Ψ hΨ m hm N V Mr Qwidth hN hV hM hQ hMc hFc hmargin hnorm ss hss labels hlabels s
  exact h Ψ hΨ m hm N V Mr Qwidth hN hV hM hQ hMc hFc hmargin hnorm ss
    (hss.trans hsub) labels hlabels s

theorem canonical_rank_subslot_product {σ:Type*}[DecidableEq σ]
    (slots subslots:Finset σ)(H:σ→ℝ)(hsub:subslots⊆slots)
    (hH:∀i∈slots,1≤ H i):
    (∏i∈subslots,H i)≤∏i∈slots,H i :=
  Finset.prod_le_prod_of_subset_of_one_le hsub
    (fun i hi=>(zero_le_one: (0:ℝ)≤1).trans (hH i (hsub hi)))
    (fun i hi _=> hH i hi)

theorem canonical_rank_subslot_cap {σ:Type*}[DecidableEq σ]
    (slots subslots:Finset σ)(H:σ→ℝ)(Z z:ℝ)(hsub:subslots⊆slots)
    (hH:∀i∈slots,1≤ H i)(hcap:(∏i∈slots,H i)≤ Z^z):
    (∏i∈subslots,H i)≤ Z^z :=
  (canonical_rank_subslot_product slots subslots H hsub hH).trans hcap

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein CompletedGauss  CanonicalQuadraticSieve
open CanonicalRowCompletion InverseInitialClippedColumns InverseReflectedPhase
local notation "O"=> Eisenstein.O

def CompletePoolRankMoments (q D:ℕ) {σ:Type}[DecidableEq σ]
    (slots:Finset σ)
    (lists:σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
    (a:σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ)
    (base:O→*ℂ)(W:𝓢(ℝ,ℂ))(Z Mmax Fcap z c eps A:ℝ)(K degree:ℕ):Prop :=
  let F:=CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D;
  let hF:=CanonicalRowCompletion.outsideSquarefree_admissible (reflectionExcludedPrimes q) D (reflectionExcludedPrimes_bad q);
  letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=> by rw [poolPrimary_span F hF i];infer_instance;
  CanonicalRankMoments (poolPrimary F) (poolPrimary_good F hF) Finset.univ base slots lists a W
    Z Mmax Fcap z c eps A K degree

def rankRowCap (n:ℕ)(cutoff:ℝ):ℝ:=3*((n:ℝ)-1)*cutoff/4

def rankTotalCap (n:ℕ)(L eta:ℝ):ℝ:=L-15*(n:ℝ)*eta

def rankMargin (n:ℕ)(cstar eta:ℝ):ℝ:=cstar/2+7*(n:ℝ)*eta

def rankLoss (n:ℕ)(eta:ℝ):ℝ:=62*(n:ℝ)*eta

def RankEnergyExists (n:ℕ)(L cstar cutoff eta:ℝ)(K:ℕ)(W:𝓢(ℝ,ℂ)):Prop :=
  ∃degree:ℕ,∃B:ℝ,1≤ B ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0< C ∧ 1< Z₀ ∧
    ∀Z:ℝ,Z₀≤ Z→∀D:ℕ,B*Z^L≤ D→
    ∀{σ:Type}[DecidableEq σ](slots:Finset σ),slots.card≤ K→
    ∀(lists:σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
      (H:σ→ℝ)(a:σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→
      (∀i∈slots,1≤ H i)→(∀i∈slots,∀P∈lists i,(Ideal.absNorm P.val:ℝ)≤ H i)→
      (∀i∈slots,∀P∈lists i,‖a i P‖≤1)→
    ∀z:ℝ,0≤ z→(∏i∈slots,H i)≤ Z^z→
    ∀base:O→*ℂ,(∀u,‖base u‖≤1)→
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) base→
      CompletePoolRankMoments q D slots lists a base W Z (rankRowCap n cutoff)
        (rankTotalCap n L eta) z (rankMargin n cstar eta) (rankLoss n eta) C K degree

theorem rank_energy_exists_zero (L cstar cutoff eta:ℝ)(hcut:0< cutoff)(K:ℕ)(W:𝓢(ℝ,ℂ)):
    RankEnergyExists 0 L cstar cutoff eta K W :=by
  refine ⟨0,1,le_rfl,?_⟩
  intro q hq
  refine ⟨1,2,by norm_num,by norm_num,?_⟩
  intro Z hZ D hD σ _ slots hslots lists H a hdis hH hP ha z hz hprod base hb hp
  dsimp only [CompletePoolRankMoments]
  let F:=CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D
  have hF:=CanonicalRowCompletion.outsideSquarefree_admissible (reflectionExcludedPrimes q) D (reflectionExcludedPrimes_bad q)
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=> by rw [poolPrimary_span F hF i];infer_instance
  apply canonical_rank_negative
  simp only [rankRowCap,Nat.cast_zero]
  linarith

theorem actual_rank_successor_caps (n:ℕ)(L cstar cutoff eta M F c:ℝ)
    (hM:M≤ rankRowCap (n+1) cutoff)(hF:F≤ rankTotalCap (n+1) L eta)
    (hc:rankMargin (n+1) cstar eta≤ c):
    M-3*cutoff/4≤ rankRowCap n cutoff ∧ F+15*eta≤ rankTotalCap n L eta ∧
      rankMargin n cstar eta≤ c-7*eta :=by
  unfold rankRowCap rankTotalCap rankMargin at *
  push_cast at *
  constructor <;> first | linarith | constructor <;> linarith

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open MeasureTheory Eisenstein CompletedGauss  CanonicalQuadraticSieve
open CanonicalRowCompletion InverseInitialClippedColumns InverseReflectedPhase InverseTerminalWidths
open CanonicalCubeSeparation CompletedHeight InverseMomentFirstSecondHeightCost
local notation "O"=> Eisenstein.O

theorem rank_energy_exists_succ_of_reference
    (n:ℕ)(L cstar cutoff eta:ℝ)(K:ℕ)
    (hL:1≤ L)(hcstar:0< cstar)(hcut:0< cutoff)(hcutL:cutoff≤ L)
    (hcutc:cutoff≤ cstar/200)(heta:0< eta)(heta1:eta≤1)
    (hetac:eta≤ cstar/100000)(hetad:eta≤ cutoff/32)
    (hIH:∀(W:𝓢(ℝ,ℂ))(lo hi:ℝ),0< lo→0≤ hi→
      Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi→RankEnergyExists n L cstar cutoff eta K W)
    (W:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0< lo)(hhi:0≤ hi)
    (hsW:Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi)
    (Vlog:𝓢(ℝ,ℂ))(Alog:ℝ)(hbox:∀x,Vlog x≠0→|x|≤ Alog)
    (hone:∀x,|x|≤ columnWindowRadius lo hi→Vlog x=1)
    (hlarge:∀window:ℝ,∃Zt:ℝ,1< Zt ∧ ∀Z:ℝ,Zt≤ Z→
      2≤ Z ∧ 2≤ Z^eta ∧ Real.exp 1≤ Z^eta ∧ 1≤ eta*Real.log Z ∧
      hi≤ Z^eta ∧ Real.exp Alog≤ Z^eta ∧ Real.exp window≤ Z^eta):
    RankEnergyExists (n+1) L cstar cutoff eta K W :=by
  have hL0:0≤ L:=by linarith
  have heF:0< firstPassEpsilon L eta:=by unfold firstPassEpsilon;positivity
  have hem:0< sourceMassEpsilon L eta:=by unfold sourceMassEpsilon;positivity
  obtain ⟨w11,w12,w21,w22,af1,bf1,af2,bf2,window,bw,ds,ha1,hab1,ha2,hab2,
    hw11,hw12,hw21,hw22,hs11,hs12,hs21,hs22,hbw,hbA,hbexp,hstep⟩:=
    actual_complete_normalized_rank_step lo hi hlo hhi W hsW (W.smooth ⊤) Vlog Alog hbox hone
      L cstar eta eta 1 (sourceMassEpsilon L eta) (sourceMassEpsilon L eta) eta
      hL hcstar heta heta1 hetac heta heta1 hem hem heta K
  obtain ⟨J11,B11,hB11,ih11⟩:=hIH w11 af1 bf1 ha1 (by linarith) (subset_closure.trans hs11)
  obtain ⟨J12,B12,hB12,ih12⟩:=hIH w12 af1 bf1 ha1 (by linarith) (subset_closure.trans hs12)
  obtain ⟨J21,B21,hB21,ih21⟩:=hIH w21 af2 bf2 ha2 (by linarith) (subset_closure.trans hs21)
  obtain ⟨J22,B22,hB22,ih22⟩:=hIH w22 af2 bf2 ha2 (by linarith) (subset_closure.trans hs22)
  let J:=J11+J12+J21+J22
  let dl:=2*(InverseClippingProfiles.momentOrder (firstDegree J)+(volume:Measure ℝ).integrablePower)
  let Jout:=max ds dl
  let B:=1+hi+B11+B12+B21+B22
  have hB:1≤ B:=by dsimp [B];linarith
  have hb0:0≤ B:=by linarith
  have hhiB:hi≤ B:=by dsimp [B];linarith
  have hBB11:B11≤ B:=by dsimp [B];linarith
  have hBB12:B12≤ B:=by dsimp [B];linarith
  have hBB21:B21≤ B:=by dsimp [B];linarith
  have hBB22:B22≤ B:=by dsimp [B];linarith
  have hj11:J11≤ J:=by dsimp [J];omega
  have hj12:J12≤ J:=by dsimp [J];omega
  have hj21:J21≤ J:=by dsimp [J];omega
  have hj22:J22≤ J:=by dsimp [J];omega
  obtain ⟨Zt,hZt,hlarge⟩:=hlarge window
  refine ⟨Jout,B,hB,?_⟩
  intro q hq
  obtain ⟨C11,Z11,hC11,hZ11,ih11⟩:=ih11 q hq
  obtain ⟨C12,Z12,hC12,hZ12,ih12⟩:=ih12 q hq
  obtain ⟨C21,Z21,hC21,hZ21,ih21⟩:=ih21 q hq
  obtain ⟨C22,Z22,hC22,hZ22,ih22⟩:=ih22 q hq
  obtain ⟨Cs,Cb,Zs,hCs,hCb,hZs,hstep⟩:=hstep (firstPassEpsilon L eta) eta heF heta J q hq
  let A:=C11+C12+C21+C22
  have hA:0≤ A:=by dsimp [A];linarith
  have hCA11:C11≤ A:=by dsimp [A];linarith
  have hCA12:C12≤ A:=by dsimp [A];linarith
  have hCA21:C21≤ A:=by dsimp [A];linarith
  have hCA22:C22≤ A:=by dsimp [A];linarith
  let C:=(Cs+Cb)*(1+A)
  let Z₀:=Zs+Zt+Z11+Z12+Z21+Z22
  have hC:0< C:=by dsimp [C];positivity
  have hZ₀:1< Z₀:=by dsimp [Z₀];linarith
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ D hD σ _ slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
  have hZs':Zs≤ Z:=by dsimp [Z₀] at hZ;linarith
  have hZt':Zt≤ Z:=by dsimp [Z₀] at hZ;linarith
  have hZ11':Z11≤ Z:=by dsimp [Z₀] at hZ;linarith
  have hZ12':Z12≤ Z:=by dsimp [Z₀] at hZ;linarith
  have hZ21':Z21≤ Z:=by dsimp [Z₀] at hZ;linarith
  have hZ22':Z22≤ Z:=by dsimp [Z₀] at hZ;linarith
  obtain ⟨hZ2,h2,hExp,hlog,hhiZ,hAZ,hwin⟩:=hlarge Z hZt'
  have hZ1:1< Z:=by linarith
  have hZ0:0< Z:=by linarith
  have hD11:B11*Z^L≤ D:=(mul_le_mul_of_nonneg_right hBB11 (Real.rpow_nonneg hZ0.le _)).trans hD
  have hD12:B12*Z^L≤ D:=(mul_le_mul_of_nonneg_right hBB12 (Real.rpow_nonneg hZ0.le _)).trans hD
  have hD21:B21*Z^L≤ D:=(mul_le_mul_of_nonneg_right hBB21 (Real.rpow_nonneg hZ0.le _)).trans hD
  have hD22:B22*Z^L≤ D:=(mul_le_mul_of_nonneg_right hBB22 (Real.rpow_nonneg hZ0.le _)).trans hD
  have m11:=ih11 Z hZ11' D hD11 slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
  have m12:=ih12 Z hZ12' D hD12 slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
  have m21:=ih21 Z hZ21' D hD21 slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
  have m22:=ih22 Z hZ22' D hD22 slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
  let F:=CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D
  have hF:=CanonicalRowCompletion.outsideSquarefree_admissible (reflectionExcludedPrimes q) D (reflectionExcludedPrimes_bad q)
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=> by rw [poolPrimary_span F hF i];infer_instance
  dsimp only [CompletePoolRankMoments] at m11 m12 m21 m22 ⊢
  intro Ψ hΨ m hm N V M Qwidth hN hV hM hQ hMc hFc hmargin hnorm ss hss labels hlabels theta
  have hcap:N+V≤ L:=by
    unfold rankTotalCap at hFc
    have hh:0≤15*((n+1:ℕ):ℝ)*eta:=by positivity
    linarith
  have hcm:0≤ rankMargin (n+1) cstar eta:=by unfold rankMargin;positivity
  obtain ⟨hNL,hVL,hMF,hQL,hzL,hwidth,hmargin',hmL,hpuncture⟩:=
    actual_rank_state_gates m hm Z N V M Qwidth z (rankMargin (n+1) cstar eta) L
      hZ1 hN hV hM hQ hz hcm hcap hmargin hnorm
  obtain ⟨hΨnorm,hΨperiod⟩:=actual_rank_family_gates q base hbase hperiod Ψ hΨ
  have hDparent:hi*Z^N≤ D:=by
    calc
      _≤ B*Z^L:=mul_le_mul hhiB (Real.rpow_le_rpow_of_exponent_le hZ1.le hNL)
        (Real.rpow_nonneg hZ0.le _) hb0
      _≤ D:=hD
  have hsscard:ss.card≤ K:=(Finset.card_le_card hss).trans hslots
  have hssdis:(ss:Set σ).PairwiseDisjoint lists:=by
    intro i hi j hj hij
    exact hdis (hss hi) (hss hj) hij
  have hssH:∀i∈ss,1≤ H i:=fun i hi=> hH i (hss hi)
  have hssP:∀i∈ss,∀P∈lists i,(Ideal.absNorm P.val:ℝ)≤ H i:=fun i hi=> hP i (hss hi)
  have hssa:∀i∈ss,∀P∈lists i,‖a i P‖≤1:=fun i hi=> ha i (hss hi)
  have hssprod:(∏i∈ss,H i)≤ Z^z:=canonical_rank_subslot_cap slots ss H Z z hss hH hprod
  obtain ⟨hsmallM,hsmallF,hsmallc⟩:=actual_rank_successor_caps n L cstar cutoff eta M (N+V)
    (rankMargin (n+1) cstar eta) hMc hFc le_rfl
  have lift (w:𝓢(ℝ,ℂ))(Cw:ℝ)(Jw:ℕ)(hCw:0≤ Cw)(hCwA:Cw≤ A)(hJw:Jw≤ J)
      (mw:CanonicalRankMoments (poolPrimary F)
        (poolPrimary_good F hF) Finset.univ base slots lists a w Z (rankRowCap n cutoff)
        (rankTotalCap n L eta) z (rankMargin n cstar eta) (rankLoss n eta) Cw K Jw):
      CanonicalRankMoments (poolPrimary F)
        (poolPrimary_good F hF) Finset.univ base ss lists a w Z (M-3*(cutoff/2)/2)
        (N+V+15*eta) z (rankMargin (n+1) cstar eta-7*eta) (rankLoss n eta) A K J:=by
    apply canonical_rank_subslots (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ base slots ss lists a w Z _ _ z _ _ A K J hss
    apply canonical_rank_restrict (poolPrimary F)
      (poolPrimary_good F hF) Finset.univ base slots lists a w Z
      (M-3*(cutoff/2)/2) (rankRowCap n cutoff) (N+V+15*eta) (rankTotalCap n L eta)
      z (rankMargin (n+1) cstar eta-7*eta) (rankMargin n cstar eta) (rankLoss n eta) A K J
      (by linarith) hsmallF hsmallc
    exact canonical_rank_height_constant (poolPrimary F)
      (poolPrimary_good F hF) Finset.univ base slots lists a w Z _ _ z _ _ Cw A K Jw J
      hZ0 hCw hCwA hJw mw
  have hechild:0≤ rankLoss n eta:=by unfold rankLoss;positivity
  obtain ⟨_,_,hpieta,hmass,hret,hprincipal0,hcost⟩:=actual_step_parameters L eta 0 0 (rankLoss n eta)
    hL0 heta heta1 (by linarith) (by linarith) hechild
  obtain ⟨hprincipal,hFirst,hFinal⟩:=actual_complete_step_cost L eta (rankLoss n eta) hL0 heta heta1 hechild
  have hreserve:cstar/2≤ rankMargin (n+1) cstar eta:=by
    unfold rankMargin
    exact le_add_of_nonneg_right (by positivity)
  have hbound:=hstep m hm Z N V M z (rankMargin (n+1) cstar eta) cutoff (8*eta)
    (rankLoss n eta) A (rankLoss n eta+58*eta) (rankLoss n eta+60*eta) theta
    hZs' hZ2 h2 hExp hlog hN hV hM hcap hMF hzL hhiZ hAZ hwin hcut hcutL hcutc hetad hmL hmargin'
    hreserve (by simpa only [hwidth] using hpuncture) (by positivity) hpieta hmass hmass hechild
    (by linarith) hret hprincipal hcost (by linarith) hA
    labels (fun I hI=>⟨⟨(hlabels I hI).1.1,(hlabels I hI).1.2.2⟩,(hlabels I hI).1.2.1,(hlabels I hI).2⟩)
    D hDparent ss hsscard lists H hssdis hssH hssP hssprod base Ψ hΨ hΨnorm hΨperiod a hssa
    (lift w11 C11 J11 hC11.le hCA11 hj11 m11) (lift w12 C12 J12 hC12.le hCA12 hj12 m12)
    (lift w21 C21 J21 hC21.le hCA21 hj21 m21) (lift w22 C22 J22 hC22.le hCA22 hj22 m22)
  have hnextLoss:rankLoss n eta+62*eta=rankLoss (n+1) eta:=by unfold rankLoss;push_cast;ring
  have hlongexp:(rankLoss n eta+60*eta)+2*L*firstPassEpsilon L eta+eta≤ rankLoss (n+1) eta:=by
    simpa only [hnextLoss] using hFinal
  have hloss0:0≤ rankLoss (n+1) eta:=by unfold rankLoss;positivity
  have hlong:Cb*(1+A)*(1+‖theta‖)^dl*
      Z^(N+V+(rankLoss n eta+60*eta)+2*L*firstPassEpsilon L eta+eta)≤
      Cb*(1+A)*(1+‖theta‖)^dl*Z^(N+V+rankLoss (n+1) eta):=by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hZ1.le
    linarith
  have hh:=hbound.trans (add_le_add le_rfl hlong)
  have hmrg:=actual_complete_height_merge ds dl Z (N+V) cstar (rankLoss (n+1) eta) Cs Cb A theta
    hZ1.le hcstar.le hloss0 hCs.le hCb hA
  have hpow:(1+‖theta‖)^Jout≤(1+‖theta‖)^(2*Jout):=
    pow_le_pow_right₀ (by linarith [norm_nonneg theta]) (by omega)
  have hf:childLogTest W theta=normTwistedSource W theta:=by
    funext y
    simp only [childLogTest,normTwistedSource,mul_comm]
  rw [hf]
  apply (hh.trans hmrg).trans
  dsimp only [C,Jout]
  have hx:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (show 0≤(Cs+Cb)*(1+A) by positivity))
    (Real.rpow_nonneg hZ0.le (N+V+rankLoss (n+1) eta))
  convert hx using 1 ; ring

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment

theorem actual_rank_depth_covers (Mmax cutoff:ℝ)(hcut:0< cutoff):
    Mmax≤ rankRowCap (actualDepth Mmax (cutoff/2)) cutoff := by
  have hceil:=Nat.le_ceil (2*Mmax/(3*(cutoff/2)))
  have hscaled:2*Mmax≤(⌈2*Mmax/(3*(cutoff/2))⌉₊:ℝ)*(3*(cutoff/2)):=
    (div_le_iff₀ (by positivity:0<3*(cutoff/2))).mp hceil
  unfold rankRowCap actualDepth
  push_cast
  nlinarith

theorem actual_rank_depth_parameters (Mmax Fmax c eps:ℝ)
    (hM:0≤ Mmax)(hF:0≤ Fmax)(hc:0< c)(heps:0< eps):
    ∃cutoff eta:ℝ,0< cutoff ∧ 0< eta ∧ eta≤1 ∧ eta≤ cutoff/32 ∧
      cutoff≤ Fmax+1 ∧ cutoff≤ c/200 ∧ eta≤ c/100000 ∧
      let n:=actualDepth Mmax (cutoff/2);
      0< n ∧ Mmax≤ rankRowCap n cutoff ∧
      ∀k:ℕ,k≤ n→Fmax≤ rankTotalCap k (Fmax+1) eta ∧
        c/2≤ rankMargin k c eta ∧ rankMargin k c eta≤ c ∧
        0≤ rankLoss k eta ∧ rankLoss k eta≤ eps/4 := by
  let csmall:=min c 1
  have hcs:0< csmall:=lt_min hc (by norm_num)
  have hcc:csmall≤ c:=min_le_left _ _
  have hc1:csmall≤1:=min_le_right _ _
  obtain ⟨cutoff,eta,hcut,heta,heta1,hetacut,hcutc,hetac,hbudgets⟩:=
    actual_recursion_parameters Mmax Fmax csmall eps hM hF hcs heps
  dsimp only at hbudgets
  refine ⟨cutoff,eta,hcut,heta,heta1,hetacut,by linarith,by linarith,by linarith,?_⟩
  dsimp only
  refine ⟨actualDepth_pos _ _,actual_rank_depth_covers Mmax cutoff hcut,?_⟩
  intro k hk
  have hk':(k:ℝ)≤(actualDepth Mmax (cutoff/2):ℝ):=by exact_mod_cast hk
  have hmono:=mul_le_mul_of_nonneg_right hk' heta.le
  have hk0:0≤(k:ℝ):=Nat.cast_nonneg _
  have hkE:0≤(k:ℝ)*eta:=mul_nonneg hk0 heta.le
  rcases hbudgets with ⟨hmargin,hsize,hloss⟩
  unfold rankTotalCap rankMargin rankLoss
  refine ⟨?_,?_,?_,?_,?_⟩ <;> nlinarith

theorem actual_rank_top_parameters (Mmax Fmax c eps:ℝ)
    (hM:0≤ Mmax)(hF:0≤ Fmax)(hc:0< c)(heps:0< eps):
    ∃(n:ℕ)(cutoff eta:ℝ),n=actualDepth Mmax (cutoff/2) ∧
      0< n ∧ 0< cutoff ∧ 0< eta ∧ eta≤1 ∧ eta≤ cutoff/32 ∧
      cutoff≤ Fmax+1 ∧ cutoff≤ c/200 ∧ eta≤ c/100000 ∧
      Mmax≤ rankRowCap n cutoff ∧ Fmax≤ rankTotalCap n (Fmax+1) eta ∧
      c/2≤ rankMargin n c eta ∧ rankMargin n c eta≤ c ∧
      0≤ rankLoss n eta ∧ rankLoss n eta< eps := by
  obtain ⟨cutoff,eta,hcut,heta,heta1,hetacut,hcutL,hcutc,hetac,hn,hrow,hall⟩:=
    actual_rank_depth_parameters Mmax Fmax c eps hM hF hc heps
  have htop:=hall (actualDepth Mmax (cutoff/2)) le_rfl
  refine ⟨actualDepth Mmax (cutoff/2),cutoff,eta,rfl,hn,hcut,heta,heta1,hetacut,
    hcutL,hcutc,hetac,hrow,htop.1,htop.2.1,htop.2.2.1,htop.2.2.2.1,?_⟩
  linarith [htop.2.2.2.2]

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein CompletedGauss  CanonicalQuadraticSieve
open CanonicalRowCompletion InverseReflectedPhase
local notation "O"=> Eisenstein.O

def CanonicalEnergyExists (Mcap Fcap c eps L:ℝ)(K:ℕ)(W:𝓢(ℝ,ℂ)):Prop :=
  ∃degree:ℕ,∃B:ℝ,1≤ B ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0< C ∧ 1< Z₀ ∧
    ∀Z:ℝ,Z₀≤ Z→∀D:ℕ,B*Z^L≤ D→
    ∀{σ:Type}[DecidableEq σ](slots:Finset σ),slots.card≤ K→
    ∀(lists:σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
      (H:σ→ℝ)(a:σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→
      (∀i∈slots,1≤ H i)→(∀i∈slots,∀P∈lists i,(Ideal.absNorm P.val:ℝ)≤ H i)→
      (∀i∈slots,∀P∈lists i,‖a i P‖≤1)→
    ∀z:ℝ,0≤ z→(∏i∈slots,H i)≤ Z^z→
    ∀base:O→*ℂ,(∀u,‖base u‖≤1)→
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) base→
      CompletePoolRankMoments q D slots lists a base W Z Mcap Fcap z c eps C K degree

theorem canonical_energy_of_rank (n:ℕ)(L cstar cutoff eta Mcap Fcap c eps:ℝ)(K:ℕ)(W:𝓢(ℝ,ℂ))
    (hM:Mcap≤ rankRowCap n cutoff)(hF:Fcap≤ rankTotalCap n L eta)
    (hc:rankMargin n cstar eta≤ c)(he:rankLoss n eta≤ eps)
    (h:RankEnergyExists n L cstar cutoff eta K W):
    CanonicalEnergyExists Mcap Fcap c eps L K W :=by
  obtain ⟨degree,B,hB,h⟩:=h
  refine ⟨degree,B,hB,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,h⟩:=h q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ D hD σ _ slots hslots lists H a hdis hH hP ha z hz hprod base hb hp
  have hmom:=h Z hZ D hD slots hslots lists H a hdis hH hP ha z hz hprod base hb hp
  dsimp only [CompletePoolRankMoments] at hmom ⊢
  let F:=CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D
  have hFa:=CanonicalRowCompletion.outsideSquarefree_admissible (reflectionExcludedPrimes q) D (reflectionExcludedPrimes_bad q)
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=> by rw [poolPrimary_span F hFa i];infer_instance
  apply canonical_rank_loss_le (poolPrimary F) (poolPrimary_ne_zero F hFa) (poolPrimary_coprime F hFa)
    (poolPrimary_good F hFa) Finset.univ base slots lists a W Z Mcap Fcap z c (rankLoss n eta) eps C K degree
    (by linarith) hC.le he
  exact canonical_rank_restrict (poolPrimary F)
    (poolPrimary_good F hFa) Finset.univ base slots lists a W Z Mcap (rankRowCap n cutoff)
    Fcap (rankTotalCap n L eta) z c (rankMargin n cstar eta) (rankLoss n eta) C K degree hM hF hc hmom

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open CanonicalCubeSeparation

def RankReferenceCutoffs:Prop :=
  ∀lo hi:ℝ,0< lo→0≤ hi→∃(Vlog:𝓢(ℝ,ℂ))(Alog:ℝ),
    (∀x,Vlog x≠0→|x|≤ Alog) ∧
    (∀x,|x|≤ columnWindowRadius lo hi→Vlog x=1)

def RankReferenceThresholds:Prop :=
  ∀eta:ℝ,0< eta→∀hi Alog window:ℝ,∃Zt:ℝ,1< Zt ∧ ∀Z:ℝ,Zt≤ Z→
    2≤ Z ∧ 2≤ Z^eta ∧ Real.exp 1≤ Z^eta ∧ 1≤ eta*Real.log Z ∧
    hi≤ Z^eta ∧ Real.exp Alog≤ Z^eta ∧ Real.exp window≤ Z^eta

theorem rank_energy_exists_all_of_references
    (href:RankReferenceCutoffs)(hthreshold:RankReferenceThresholds)
    (L cstar cutoff eta:ℝ)(K:ℕ)
    (hL:1≤ L)(hcstar:0< cstar)(hcut:0< cutoff)(hcutL:cutoff≤ L)
    (hcutc:cutoff≤ cstar/200)(heta:0< eta)(heta1:eta≤1)
    (hetac:eta≤ cstar/100000)(hetad:eta≤ cutoff/32):
    ∀n:ℕ,∀(W:𝓢(ℝ,ℂ))(lo hi:ℝ),0< lo→0≤ hi→
      Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi→RankEnergyExists n L cstar cutoff eta K W :=by
  intro n
  induction n with
  | zero =>
      intro W lo hi hlo hhi hsW
      exact rank_energy_exists_zero L cstar cutoff eta hcut K W
  | succ n ih =>
      intro W lo hi hlo hhi hsW
      obtain ⟨Vlog,Alog,hbox,hone⟩:=href lo hi hlo hhi
      exact rank_energy_exists_succ_of_reference n L cstar cutoff eta K hL hcstar hcut hcutL
        hcutc heta heta1 hetac hetad ih W lo hi hlo hhi hsW Vlog Alog hbox hone
        (fun window=> hthreshold eta heta hi Alog window)

theorem canonical_energy_exists_of_references
    (href:RankReferenceCutoffs)(hthreshold:RankReferenceThresholds)
    (Mcap Fcap c eps:ℝ)(hM:0≤ Mcap)(hF:0≤ Fcap)(hc:0< c)(heps:0< eps)
    (K:ℕ)(W:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0< lo)(hhi:0≤ hi)
    (hsW:Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi):
    CanonicalEnergyExists Mcap Fcap c eps (Fcap+1) K W :=by
  obtain ⟨n,cutoff,eta,hn,hpos,hcut,heta,heta1,hetad,hcutL,hcutc,hetac,hrow,hcap,hmargin0,hmargin,hloss0,hloss⟩:=
    actual_rank_top_parameters Mcap Fcap c eps hM hF hc heps
  have he:=rank_energy_exists_all_of_references href hthreshold (Fcap+1) c cutoff eta K
    (by linarith) hc hcut hcutL hcutc heta heta1 hetac hetad n W lo hi hlo hhi hsW
  exact canonical_energy_of_rank n (Fcap+1) c cutoff eta Mcap Fcap c eps K W
    hrow hcap hmargin hloss.le he

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment

theorem exists_canonical_reference_cutoff (lo hi : ℝ) :
    ∃ Vlog : SchwartzMap ℝ ℂ, ∃ Alog : ℝ, 0 < Alog ∧
      Alog = CanonicalCubeSeparation.columnWindowRadius lo hi + 1 ∧
      HasCompactSupport Vlog ∧
      tsupport Vlog ⊆ Set.Icc (-Alog) Alog ∧
      (∀ x, Vlog x ≠ 0 → |x| ≤ Alog) ∧
      (∀ x, |x| ≤ CanonicalCubeSeparation.columnWindowRadius lo hi → Vlog x = 1) ∧
      Vlog 0 = 1 := by
  obtain ⟨v, hvc, hvs, hvone, hvbox, hvzero⟩ :=
    JointLogSeparation.exists_complex_smooth_cutoff
      (CanonicalCubeSeparation.columnWindowRadius lo hi)
      (CanonicalCubeSeparation.columnWindowRadius_nonneg lo hi)
  let Vlog : SchwartzMap ℝ ℂ := hvc.toSchwartzMap hvs
  refine ⟨Vlog, CanonicalCubeSeparation.columnWindowRadius lo hi + 1,
    by linarith [CanonicalCubeSeparation.columnWindowRadius_nonneg lo hi],
    rfl, hvc, hvbox, ?_, hvone, hvone 0 (by simpa using CanonicalCubeSeparation.columnWindowRadius_nonneg lo hi)⟩
  intro x hx
  exact abs_le.mpr (hvbox (subset_tsupport v hx))

theorem eventually_canonical_reference_gates (hi Alog window eta : ℝ)
    (heta : 0 < eta) :
    ∃ Z0 : ℝ, 1 < Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      2 ≤ Z ∧ 2 ≤ Z ^ eta ∧ Real.exp 1 ≤ Z ^ eta ∧
      1 ≤ eta * Real.log Z ∧ hi ≤ Z ^ eta ∧
      Real.exp Alog ≤ Z ^ eta ∧ Real.exp window ≤ Z ^ eta := by
  let R : ℝ := 2 + |hi| + |Alog| + |window|
  have hR : 1 ≤ R := by
    dsimp [R]
    linarith [abs_nonneg hi, abs_nonneg Alog, abs_nonneg window]
  refine ⟨2 + Real.exp (R / eta), by linarith [Real.exp_pos (R / eta)], ?_⟩
  intro Z hZ
  have hZtwo : 2 ≤ Z := by linarith [Real.exp_pos (R / eta)]
  have hZpos : 0 < Z := by linarith
  have hZexp : Real.exp (R / eta) ≤ Z := by linarith
  have hlog := Real.log_le_log (Real.exp_pos (R / eta)) hZexp
  rw [Real.log_exp] at hlog
  have hRlog : R ≤ Real.log Z * eta := (div_le_iff₀ heta).mp hlog
  have hpow : Real.exp R ≤ Z ^ eta := by
    rw [Real.rpow_def_of_pos hZpos]
    exact Real.exp_le_exp.mpr hRlog
  have hexp : Real.exp 1 ≤ Z ^ eta :=
    (Real.exp_le_exp.mpr hR).trans hpow
  refine ⟨hZtwo, (by linarith [Real.add_one_le_exp (1 : ℝ)] : 2 ≤ Real.exp 1).trans
    hexp, hexp, by nlinarith, ?_, ?_, ?_⟩
  · have hhi : hi ≤ R := by
      dsimp [R]
      linarith [le_abs_self hi, abs_nonneg Alog, abs_nonneg window]
    exact hhi.trans ((by linarith [Real.add_one_le_exp R] : R ≤ Real.exp R).trans hpow)
  · apply (Real.exp_le_exp.mpr ?_).trans hpow
    dsimp [R]
    linarith [le_abs_self Alog, abs_nonneg hi, abs_nonneg window]
  · apply (Real.exp_le_exp.mpr ?_).trans hpow
    dsimp [R]
    linarith [le_abs_self window, abs_nonneg hi, abs_nonneg Alog]

theorem canonical_reference_pool_coverage (hi B Z N L D : ℝ)
    (hB : 0 ≤ B) (hhi : hi ≤ B) (hZ : 1 ≤ Z) (hNL : N ≤ L)
    (hD : B * Z ^ L ≤ D) : hi * Z ^ N ≤ D := by
  calc
    hi * Z ^ N ≤ B * Z ^ N :=
      mul_le_mul_of_nonneg_right hhi (Real.rpow_nonneg (by linarith) _)
    _ ≤ B * Z ^ L :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hNL) hB
    _ ≤ D := hD

theorem exists_canonical_reference_family_gates {ι : Type*} (s : Finset ι)
    (hi Alog window : ι → ℝ) (eta : ℝ) (heta : 0 < eta) :
    ∃ B : ℝ, 0 < B ∧ ∃ Z0 : ℝ, 1 < Z0 ∧
      (∀ i ∈ s, hi i ≤ B ∧ Real.exp (Alog i) ≤ B ∧ Real.exp (window i) ≤ B) ∧
      ∀ Z : ℝ, Z0 ≤ Z →
        2 ≤ Z ∧ 2 ≤ Z ^ eta ∧ Real.exp 1 ≤ Z ^ eta ∧
        1 ≤ eta * Real.log Z ∧ B ≤ Z ^ eta ∧
        (∀ i ∈ s, hi i ≤ Z ^ eta ∧ Real.exp (Alog i) ≤ Z ^ eta ∧
          Real.exp (window i) ≤ Z ^ eta) ∧
        (∀ i ∈ s, ∀ N L D : ℝ, N ≤ L → B * Z ^ L ≤ D → hi i * Z ^ N ≤ D) := by
  let mass : ι → ℝ := fun i => |hi i| + Real.exp (Alog i) + Real.exp (window i)
  have hm : ∀ i, 0 ≤ mass i := by intro i; dsimp [mass]; positivity
  let B : ℝ := 1 + ∑ i ∈ s, mass i
  have hB : 0 < B := by dsimp [B]; positivity
  have hbound : ∀ i ∈ s, hi i ≤ B ∧ Real.exp (Alog i) ≤ B ∧
      Real.exp (window i) ≤ B := by
    intro i hiS
    have hsum : mass i ≤ ∑ j ∈ s, mass j := Finset.single_le_sum (fun j _ => hm j) hiS
    dsimp [mass, B] at *
    constructor
    · linarith [le_abs_self (hi i), Real.exp_pos (Alog i), Real.exp_pos (window i)]
    constructor
    · linarith [abs_nonneg (hi i), Real.exp_pos (window i)]
    · linarith [abs_nonneg (hi i), Real.exp_pos (Alog i)]
  obtain ⟨Z0, hZ0, hgate⟩ := eventually_canonical_reference_gates B 0 0 eta heta
  refine ⟨B, hB, Z0, hZ0, hbound, ?_⟩
  intro Z hZ
  obtain ⟨hZtwo, htwo, hexp, hlog, hBpow, _, _⟩ := hgate Z hZ
  refine ⟨hZtwo, htwo, hexp, hlog, hBpow, ?_, ?_⟩
  · intro i hiS
    obtain ⟨hhi, hA, hw⟩ := hbound i hiS
    exact ⟨hhi.trans hBpow, hA.trans hBpow, hw.trans hBpow⟩
  · intro i hiS N L D hNL hD
    exact canonical_reference_pool_coverage (hi i) B Z N L D hB.le
      (hbound i hiS).1 (by linarith) hNL hD

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment

theorem actual_rank_reference_cutoffs : RankReferenceCutoffs :=by
  intro lo hi hlo hhi
  obtain ⟨Vlog,Alog,hA,hAe,hcompact,hsupport,hbox,hone,hzero⟩:=
    exists_canonical_reference_cutoff lo hi
  exact ⟨Vlog,Alog,hbox,hone⟩

theorem actual_rank_reference_thresholds : RankReferenceThresholds :=by
  intro eta heta hi Alog window
  exact eventually_canonical_reference_gates hi Alog window eta heta

theorem canonical_rank_energy_exists
    (L cstar cutoff eta:ℝ)(K:ℕ)
    (hL:1≤ L)(hcstar:0< cstar)(hcut:0< cutoff)(hcutL:cutoff≤ L)
    (hcutc:cutoff≤ cstar/200)(heta:0< eta)(heta1:eta≤1)
    (hetac:eta≤ cstar/100000)(hetad:eta≤ cutoff/32)
    (n:ℕ)(W:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0< lo)(hhi:0≤ hi)
    (hsW:Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi):
    RankEnergyExists n L cstar cutoff eta K W :=
  rank_energy_exists_all_of_references actual_rank_reference_cutoffs actual_rank_reference_thresholds
    L cstar cutoff eta K hL hcstar hcut hcutL hcutc heta heta1 hetac hetad n W lo hi hlo hhi hsW

theorem canonical_marked_energy_exists
    (Mcap Fcap c eps:ℝ)(hM:0≤ Mcap)(hF:0≤ Fcap)(hc:0< c)(heps:0< eps)
    (K:ℕ)(W:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0< lo)(hhi:0≤ hi)
    (hsW:Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi):
    CanonicalEnergyExists Mcap Fcap c eps (Fcap+1) K W :=
  canonical_energy_exists_of_references actual_rank_reference_cutoffs actual_rank_reference_thresholds
    Mcap Fcap c eps hM hF hc heps K W lo hi hlo hhi hsW

end InverseMoment

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

/-
First label cells adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.GlobalRetainedGates
import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.CompletedFiberEnergies

/-!
# First label cells

Sources, exponents and column scales of the first label cells; supported retained sources of
the global gates; uniform types of the filtered global priority aggregates.
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
namespace InverseMoment
open Eisenstein CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open InverseTerminalWidths InverseReflectedPhase CompletedHeight
local notation "Eis"=> Eisenstein.O
universe u v

theorem canonical_short_completed_energy_uniform_degree
    (lo hi:ℝ) (hlo:0< lo) (W:ℝ→ℂ)
    (hWs:Function.support W⊆Set.Icc lo hi) (hW:ContDiff ℝ ∞ W)
    (L cstar eta:ℝ) (hL:0≤ L) (hcstar:0< cstar) (heta:0< eta)
    (heta1:eta≤1) (hetac:eta≤ cstar/100000) (rmax:ℕ):
    ∃ (degree : ℕ), ∀ (q : ℕ) (_hq : q≠0), ∃ (C Z₀ : ℝ),0< C ∧ 1< Z₀ ∧
    ∀{σ:Type v} [Fintype σ] [DecidableEq σ],∀(F:Ideal Eis)(_hF:Squarefree F)
      (m:Eis)(_hm:m≠0)(Z N V M z₀ margin hcut d:ℝ),
      Z₀≤ Z → 0≤ N → 0≤ M → M≤ L → V≤ L → z₀≤ L → hcut≤ L →
      (Ideal.absNorm F:ℝ)≤ Z^V → (Ideal.absNorm (Ideal.span {m}):ℝ)≤ Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤ margin →
      V≤ d → hcut≤ d+eta → d≤ cstar/200 →
    ∀(parents:Finset (Ideal Eis)),(∀I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤ Z^M) →
      Fintype.card σ≤ rmax → ∀(lists:σ→Finset (Ideal Eis))(H:σ→ℝ),
      Pairwise (fun i j=> Disjoint (lists i) (lists j)) →
      (∀i,∀P∈lists i,P.IsMaximal) →
      (∀i,∀P∈lists i,lambda∉P) →
      (∀i,∀P∈lists i,Prime P) → (∀i,∀P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀i,1≤ H i) → (∀i,∀P∈lists i,(Ideal.absNorm P:ℝ)≤ H i) → (∏i,H i)≤ Z^z₀ →
    ∀(Ψ:Eis→*ℂ),(∀n,‖Ψ n‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀(u:Eisˣ)(θ:ℝ)(w:∀i,lists i→ℂ),(∀i P,‖w i P‖≤1) →
      (∑I∈parents,‖markedShortCompletedSum
        (rowTwist Ψ (ActualFiber.maskElement q m) (cubicIdealGenerator F)
          (u.val*cubicIdealGenerator I)) (normTwistedSource W θ)
        (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/64)*((2*(1+diagonalControl sieveCutoff))*(columnDyadicLength (Z^hcut)+1:ℝ))^2 := by
  obtain ⟨degree,hu⟩ := canonical_cube_shifted_completed_energy_uniform_degree lo hi hlo W hWs hW L cstar eta hL hcstar heta heta1 hetac rmax
  refine ⟨degree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,he⟩ := hu q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ F hF m hm Z N V M z₀ margin hcut d hZ hN hM hMc hVc hzc hcutc hFn hRn
    hmargin hreserve hVd hcutd hd parents hparents hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod
    Ψ hΨ hperiod u θ w hw
  have hZ1:1< Z:=lt_of_lt_of_le hZ₀ hZ
  have hz:0< Z:=zero_lt_one.trans hZ1
  have htw:HasCompactSupport (normTwistedSource W θ):=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((normTwistedSource_support W θ).trans hWs)
  have hcompleted (J:Ideal Eis) (hJ:J∈shortCubeRange (Z^hcut)):
      (∑I∈parents,‖markedCompletedT
        (rowTwist Ψ (ActualFiber.maskElement q m) (cubicIdealGenerator F)
          (u.val*cubicIdealGenerator I)) (normTwistedSource W θ)
        (Z^N/(Ideal.absNorm J:ℝ)^3) (fun A=> tupleDivisibilityMark lists w (J^3*A))‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/64):=by
    obtain ⟨hJ0,hJnorm⟩:=(mem_shortCubeRange _ J).mp hJ
    have hn:0<(Ideal.absNorm J:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (fun hn=> hJ0 (Ideal.absNorm_eq_zero_iff.mp hn))
    have hc:Real.logb Z (Ideal.absNorm J:ℝ)≤ hcut:=
      (Real.logb_le_iff_le_rpow hZ1 hn).mpr hJnorm.le
    have hjpow:(Ideal.absNorm J:ℝ)≤ Z^(Real.logb Z (Ideal.absNorm J:ℝ)):=by
      rw [Real.rpow_logb hz (ne_of_gt hZ1) hn]
    have h:=he F hF m hm Z N V M z₀ margin (Real.logb Z (Ideal.absNorm J:ℝ)) d
      hZ hN hM hMc hVc hzc (hc.trans hcutc) hFn hRn hmargin hreserve hVd (hc.trans hcutd) hd
      parents hparents hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod Ψ hΨ hperiod J hJ0 hjpow u θ w hw
    rw [short_cube_exact_scale Z N hZ1 J hJ0] at h
    simpa only [completed_tuple_mark lists w _ _ htw _ (div_pos (Real.rpow_pos_of_pos hz _) (pow_pos hn _)) J] using h
  have hh:=marked_short_completed_energy
    (fun I:parents=> rowTwist Ψ (ActualFiber.maskElement q m) (cubicIdealGenerator F)
      (u.val*cubicIdealGenerator I.val))
    (fun I n=> rowTwist_norm Ψ hΨ _ _ _ n) (fun _=> tupleDivisibilityMark lists w)
    (normTwistedSource W θ) (Z^N) (Z^hcut) (C*(1+‖θ‖)^degree*Z^(N+V-cstar/64))
    (by positivity) (fun J hJ=> by
      rw [Finset.sum_coe_sort parents (fun I:Ideal Eis=>‖markedCompletedT
        (rowTwist Ψ (ActualFiber.maskElement q m) (cubicIdealGenerator F)
          (u.val*cubicIdealGenerator I)) (normTwistedSource W θ)
        (Z^N/(Ideal.absNorm J:ℝ)^3) (fun A=> tupleDivisibilityMark lists w (J^3*A))‖^2)]
      exact hcompleted J hJ)
  rw [Finset.sum_coe_sort parents (fun I:Ideal Eis=>‖markedShortCompletedSum
        (rowTwist Ψ (ActualFiber.maskElement q m) (cubicIdealGenerator F)
          (u.val*cubicIdealGenerator I)) (normTwistedSource W θ)
        (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)] at hh
  exact hh

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open SchwartzPlanePoisson.CanonicalQuadraticSieve
open InverseInitialRayAttachment InverseFirstRayAttachment
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open InverseTerminalWidths InverseReflectedPhase CompletedHeight
local notation "Eis"=> Eisenstein.O
universe u v

theorem canonical_short_completed_power_energy_uniform_degree
    (lo hi:ℝ) (hlo:0< lo) (W:ℝ→ℂ)
    (hWs:Function.support W⊆Set.Icc lo hi) (hW:ContDiff ℝ ∞ W)
    (L cstar eta:ℝ) (hL:0≤ L) (hcstar:0< cstar) (heta:0< eta)
    (heta1:eta≤1) (hetac:eta≤ cstar/100000) (rmax:ℕ):
    ∃ (degree : ℕ), ∀ (q : ℕ) (_hq : q≠0), ∃ (C Z₀ : ℝ),0< C ∧ 1< Z₀ ∧
    ∀{σ:Type v} [Fintype σ] [DecidableEq σ],∀(F:Ideal Eis)(_hF:Squarefree F)
      (m:Eis)(_hm:m≠0)(Z N V M z₀ margin hcut d:ℝ),
      Z₀≤ Z → 0≤ N → 0≤ M → M≤ L → V≤ L → z₀≤ L → 0≤ hcut → hcut≤ L →
      (Ideal.absNorm F:ℝ)≤ Z^V → (Ideal.absNorm (Ideal.span {m}):ℝ)≤ Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤ margin →
      V≤ d → hcut≤ d+eta → d≤ cstar/200 →
    ∀(parents:Finset (Ideal Eis)),(∀I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤ Z^M) →
      Fintype.card σ≤ rmax → ∀(lists:σ→Finset (Ideal Eis))(H:σ→ℝ),
      Pairwise (fun i j=> Disjoint (lists i) (lists j)) →
      (∀i,∀P∈lists i,P.IsMaximal) →
      (∀i,∀P∈lists i,lambda∉P) →
      (∀i,∀P∈lists i,Prime P) → (∀i,∀P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀i,1≤ H i) → (∀i,∀P∈lists i,(Ideal.absNorm P:ℝ)≤ H i) → (∏i,H i)≤ Z^z₀ →
    ∀(Ψ:Eis→*ℂ),(∀n,‖Ψ n‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀(u:Eisˣ)(θ:ℝ)(w:∀i,lists i→ℂ),(∀i P,‖w i P‖≤1) →
      (∑I∈parents,‖markedShortCompletedSum
        (rowTwist Ψ (ActualFiber.maskElement q m) (cubicIdealGenerator F)
          (u.val*cubicIdealGenerator I)) (normTwistedSource W θ)
        (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/128) := by
  obtain ⟨degree,hu⟩ := canonical_short_completed_energy_uniform_degree lo hi hlo W hWs hW L cstar eta hL hcstar heta heta1 hetac rmax
  refine ⟨degree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,he⟩ := hu q hq
  obtain ⟨B,hB,hbound⟩:=short_harmonic_small_power L (cstar/128) hL (by positivity)
  refine ⟨C*B,Z₀,mul_pos hC hB,hZ₀,?_⟩
  intro σ _ _ F hF m hm Z N V M z₀ margin hcut d hZ hN hM hMc hVc hzc hcut0 hcutc hFn hRn
    hmargin hreserve hVd hcutd hd parents hparents hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod
    Ψ hΨ hperiod u θ w hw
  have hz:0< Z:=zero_lt_one.trans (lt_of_lt_of_le hZ₀ hZ)
  have hh:=he F hF m hm Z N V M z₀ margin hcut d hZ hN hM hMc hVc hzc hcutc hFn hRn
    hmargin hreserve hVd hcutd hd parents hparents hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod
    Ψ hΨ hperiod u θ w hw
  apply hh.trans
  calc
    _≤ C*(1+‖θ‖)^degree*Z^(N+V-cstar/64)*(B*Z^(cstar/128)):=
      mul_le_mul_of_nonneg_left (hbound Z hcut (lt_of_lt_of_le hZ₀ hZ).le hcut0 hcutc) (by positivity)
    _=(C*B)*(1+‖θ‖)^degree*Z^(N+V-cstar/128):=by
      rw [show N+V-cstar/128=(N+V-cstar/64)+cstar/128 by ring,Real.rpow_add hz]
      ring

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open InverseSecondUniformCutoff
open Eisenstein FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open Eisenstein (ringComplex)
local notation "O" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

def supportedRetainedSource (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ) : Finset (MarkedSecondSource ι (Jo+(J.card+J.card)) 0) :=
  geometrySource p (retainedSource p extra original negative J lists pool cutoff) b X

lemma supported_subset (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ) :
    supportedRetainedSource p extra original negative J lists pool cutoff b X⊆
      retainedSource p extra original negative J lists pool cutoff := geometrySource_subset p _ b X

lemma supported_conditions (hp : ∀i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (hvalid : ∀x∈original,SourceValid p x) (hextra : ∀x∈original,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ) :
    ActualSecondSourceConditions p (supportedRetainedSource p extra original negative J lists pool cutoff b X) :=
  ActualSecondSourceConditions.mono p (retained_conditions p hp extra original hvalid hextra negative J lists pool cutoff)
    (supported_subset p extra original negative J lists pool cutoff b X)

lemma supported_frequency_ne_zero
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ) :
    ∀x∈supportedRetainedSource p extra original negative J lists pool cutoff b X,x.second.frequency≠0 := by
  intro x hx
  exact unified_frequency_ne_zero p pool _ (fun _=> cutoff) x
    (supported_subset p extra original negative J lists pool cutoff b X hx)

lemma supported_uniform_frequency_gate
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (Z delta eta L Y tau b X : ℝ) :
    ∀x∈supportedRetainedSource p extra original negative J lists pool
      (fun G E=> uniformSecondRadius p Z delta eta G E L Y (Z^tau)) b X,
      x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
        (uniformSecondRadius p Z delta eta x.second.sourceCommon x.second.divisor L Y (Z^tau)) := by
  intro x hx
  exact ((mem_unifiedSource p pool _ _ x).mp
    (supported_subset p extra original negative J lists pool _ b X hx)).2.2.2.2

theorem supported_cell_row_gates (hp : ∀i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (Z M r ell V delta A B j t eta tau L b X : ℝ)
    (hZ : 1< Z) (heta : 0≤ eta) (hbin : 2≤ Z^eta) (hL0 : 0≤ L)
    (hL : L≤ Z^(r-A-B-t+4*eta)) :
    let source := supportedRetainedSource p extra original negative J lists pool
      (fun G E=> uniformSecondRadius p Z delta eta G E L
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau)) b X
    (∀x∈source,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell A t V j eta (index p x))) ∧
    (∀d∈keys p source,0≤ actualCellRowExponent Z M ell A t V j eta d) := by
  intro source
  have hgates := actual_cell_uniform_source_gates p hp source Z M r ell V delta A B j t eta tau L
    hZ heta hbin hL0 hL (supported_uniform_frequency_gate p extra original negative J lists pool Z delta eta L _ tau b X)
  refine ⟨?_,actual_cell_radius_nonnegative_on_keys p source Z M ell A t V j eta hZ hgates⟩
  intro x hx
  exact hgates (index p x) x (Finset.mem_filter.mpr ⟨hx,rfl⟩)

end InverseMomentGlobalRetainedGates
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open Eisenstein FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open Eisenstein (ringComplex)
local notation "O" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

lemma supported_original_property
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ)
    (F : CubeCoordinates ι→Finset ι→Finset ι→Ideal O→Prop)
    (hF : ∀y∈original,F y.cube y.firstCommon y.firstDivisor (sourceIdeal p y.quotientSupport)) :
    ∀x∈supportedRetainedSource p extra original negative J lists pool cutoff b X,
      F x.cube x.firstCommon x.firstDivisor x.quotient := by
  intro x hx
  obtain ⟨y,hy,hb,hc,hd,hq,ho⟩ := original_coordinates p extra original negative J lists pool cutoff x
    (supported_subset p extra original negative J lists pool cutoff b X hx)
  rw [hb,hc,hd,hq]
  exact hF y hy

theorem supported_label_gates (hp : ∀i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X Z B j eta : ℝ) (hZ : 1< Z) (hbin : 2≤ Z^eta)
    (hC : ∀y∈original,primeProductNorm p y.firstCommon≤ Z^(B+eta))
    (hJ : ∀y∈original,‖ringComplex (jLabel p y.cube.support
      (fun i=> y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit)‖^2≤ Z^(j+eta)) :
    let source := supportedRetainedSource p extra original negative J lists pool cutoff b X
    (∀d,∀x∈cell p source d,(actualSecondChild p 1 1 x).2.1∈actualCellLabels p source d) ∧
    (∀d,∀I∈(actualCellLabels p source d).filter Squarefree,
      Squarefree I ∧ I≠0 ∧ (Ideal.absNorm I:ℝ)≤ Z^(actualCellLabelExponent Z B j eta d)) := by
  intro source
  have hc := supported_original_property p extra original negative J lists pool cutoff b X
    (fun _ C _ _=> primeProductNorm p C≤ Z^(B+eta)) hC
  have hj := supported_original_property p extra original negative J lists pool cutoff b X
    (fun q _ _ _=>‖ringComplex (jLabel p q.support
      (fun i=> q.leftExponent i+q.rightExponent i) q.leftBit q.rightBit)‖^2≤ Z^(j+eta)) hJ
  exact ⟨fun d x hx=> actual_cell_labels_cover p source d x hx,
    fun d=> actual_cell_squarefree_labels p hp source
      (supported_frequency_ne_zero p extra original negative J lists pool cutoff b X) d Z B j eta hZ hbin hc hj⟩

theorem supported_child_margins (hp : ∀i,p i≠0)
    (hpr : ∀i,lambda^2∣p i-1)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (hvalid : ∀x∈original,SourceValid p x) (hextra : ∀x∈original,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b : ℝ) (m : O) (hm : m≠0)
    (Z r ell V M Q z c A B t j eta : ℝ) (hZ : 1< Z)
    (hparent : CanonicalMargins (r+3*ell+V) M Q z c)
    (hA : 0≤ A) (ht : 0≤ t) (hV : 0≤ V) (hj : 0≤ j) (heta : 0≤ eta) (hbin : 2≤ Z^eta)
    (hQ : (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤ Z^Q)
    (h1 : ∀y∈original,‖ringComplex (primeProduct p y.cube.support y.cube.leftExponent)‖^2≤ Z^(ell+eta))
    (h2 : ∀y∈original,‖ringComplex (primeProduct p y.cube.support y.cube.rightExponent)‖^2≤ Z^(ell+eta))
    (hT : ∀y∈original,primeProductNorm p y.quotientSupport≤ Z^(t+eta)) :
    let source := supportedRetainedSource p extra original negative J lists pool cutoff b (Z^(r-A-B-t))
    ∀d,∀γ∈actualSecondTriples p 1 1 (cell p source d),
      actualSecondInheritedRadicalPuncture m γ≠0 ∧ 0≤ actualSecondPunctureWidth Z m γ ∧
      ‖ringComplex (actualSecondInheritedRadicalPuncture m γ)‖^2=Z^(actualSecondPunctureWidth Z m γ) ∧
      CanonicalMargins (actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d)
        (childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta)
        (actualSecondPunctureWidth Z m γ) z (c-7*eta) := by
  intro source d γ hγ
  have hs := supported_conditions p hp extra original hvalid hextra negative J lists pool cutoff b (Z^(r-A-B-t))
  have hk := supported_frequency_ne_zero p extra original negative J lists pool cutoff b (Z^(r-A-B-t))
  have hb₁ := supported_original_property p extra original negative J lists pool cutoff b (Z^(r-A-B-t))
    (fun q _ _ _=>‖ringComplex (primeProduct p q.support q.leftExponent)‖^2≤ Z^(ell+eta)) h1
  have hb₂ := supported_original_property p extra original negative J lists pool cutoff b (Z^(r-A-B-t))
    (fun q _ _ _=>‖ringComplex (primeProduct p q.support q.rightExponent)‖^2≤ Z^(ell+eta)) h2
  have hq := supported_original_property p extra original negative J lists pool cutoff b (Z^(r-A-B-t))
    (fun _ _ _ I=>(Ideal.absNorm I:ℝ)≤ Z^(t+eta)) (by
      intro y hy
      simpa only [sourceIdeal,←ringComplex_norm_sq_eq_absNorm_span,primeProductNorm] using hT y hy)
  exact actual_cell_triple_margins p hp hpr source hs hk d m hm
    Z r ell V M Q z c A B t j eta hZ hparent hA ht hV hj heta hbin hQ hb₁ hb₂ hq γ hγ

end InverseMomentGlobalRetainedGates
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open InverseSecondUniformCutoff
open Eisenstein FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open Eisenstein (ringComplex)
local notation "O" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma uniform_radius_cap (G E : Finset ι) (hEG : E⊆G)
    (Z delta eta L Y tau Lcol LY : ℝ) (hZ : 0< Z) (hL : 0≤ L) (hY : 0< Y)
    (hLc : L≤ Z^Lcol) (hYi : Y⁻¹≤ Z^LY) :
    uniformSecondRadius p Z delta eta G E L Y (Z^tau)≤
      Z^(delta+eta+2*Lcol+tau+LY) := by
  have hr : primeProductNorm p E/primeProductNorm p G≤1 :=
    (div_le_one (primeProductNorm_pos p hp G)).mpr (primeProductNorm_mono p hp hEG)
  have hr0 : 0≤ primeProductNorm p E/primeProductNorm p G := by
    exact div_nonneg (primeProductNorm_pos p hp E).le (primeProductNorm_pos p hp G).le
  have hs : (primeProductNorm p E/primeProductNorm p G)^2≤1 := pow_le_one₀ hr0 hr
  unfold uniformSecondRadius
  rw [div_eq_mul_inv]
  calc
    _ ≤ Z^(delta+eta)*1*(Z^Lcol)^2*Z^tau*Z^LY := by gcongr
    _ = _ := by
      rw [mul_one,←Real.rpow_mul_natCast hZ.le]
      repeat rw [←Real.rpow_add hZ]
      congr 1
      norm_num
      ring

lemma bare_frequency_norm_le (a k : O) (ha : a≠0) :
    ‖ringComplex k‖^2≤‖ringComplex (a*k)‖^2 := by
  have hh := element_norm_ge_one a ha
  rw [map_mul,norm_mul,mul_pow]
  exact le_mul_of_one_le_left (sq_nonneg _) hh

include hp in

theorem supported_outer_caps
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (Z delta eta L Y tau b X Lcol LY Lcap : ℝ)
    (hZ : 1≤ Z) (hL : 0≤ L) (hY : 0< Y) (hLc : L≤ Z^Lcol) (hYi : Y⁻¹≤ Z^LY)
    (hgeom : b*X≤ Z^Lcap) (hphysical : delta+eta+2*Lcol+tau+LY≤ Lcap) :
    ∀x∈supportedRetainedSource p extra original negative J lists pool
      (fun G E=> uniformSecondRadius p Z delta eta G E L Y (Z^tau)) b X,
      ∀i,outerNorms p x i≤ Z^Lcap := by
  intro x hx i
  have hret := supported_subset p extra original negative J lists pool _ b X hx
  have hm := (mem_unifiedSource p pool _ _ x).mp hret
  have hg : primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤ Z^Lcap :=
    (geometrySource_gate p _ b X x hx).trans hgeom
  have hG : primeProductNorm p x.second.sourceCommon≤ Z^Lcap :=
    (le_mul_of_one_le_right (primeProductNorm_pos p hp _).le (primeProductNorm_ge_one p hp _)).trans hg
  have hV : primeProductNorm p x.second.overlap≤ Z^Lcap :=
    (le_mul_of_one_le_left (primeProductNorm_pos p hp _).le (primeProductNorm_ge_one p hp _)).trans hg
  fin_cases i
  · exact hG
  · exact (primeProductNorm_mono p hp hm.2.2.1).trans hG
  · exact hV
  · have hb := (mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p hp x) _ _).mp hm.2.2.2.2
    exact (bare_frequency_norm_le _ _ (actualSecondMultiplier_ne_zero p hp x)).trans
      (hb.2.trans ((uniform_radius_cap p hp _ _ hm.2.2.1 Z delta eta L Y tau Lcol LY
        (zero_lt_one.trans_le hZ) hL hY hLc hYi).trans
        (Real.rpow_le_rpow_of_exponent_le hZ hphysical)))

end InverseMomentGlobalRetainedGates
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open Eisenstein FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open Eisenstein (ringComplex)
local notation "O" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

theorem supported_row_rank_decrease (hp : ∀i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (hvalid : ∀x∈original,SourceValid p x) (hextra : ∀x∈original,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X Z M ell A t V j eta shortCutoff : ℝ)
    (hZ : 1< Z) (hA : 0≤ A) (ht : 0≤ t) (heta : 0≤ eta) (hbin : 2≤ Z^eta)
    (hterminal : shortCutoff≤ ell+V) (hsmall : eta≤ shortCutoff/16)
    (h1 : ∀y∈original,‖ringComplex (primeProduct p y.cube.support y.cube.leftExponent)‖^2≤ Z^(ell+eta))
    (h2 : ∀y∈original,‖ringComplex (primeProduct p y.cube.support y.cube.rightExponent)‖^2≤ Z^(ell+eta))
    (hJ : ∀y∈original,Z^(j-eta)≤‖ringComplex (jLabel p y.cube.support
      (fun i=> y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit)‖^2) :
    let source := supportedRetainedSource p extra original negative J lists pool cutoff b X
    ∀d∈keys p source,actualCellRowExponent Z M ell A t V j eta d+3*shortCutoff/2≤ M := by
  intro source d hd
  obtain ⟨x,hx⟩ := (mem_keys_iff p source d).mp hd
  have hxs := cell_subset p source d hx
  have hs := supported_conditions p hp extra original hvalid hextra negative J lists pool cutoff b X
  have hk := supported_frequency_ne_zero p extra original negative J lists pool cutoff b X
  have hb₁ := supported_original_property p extra original negative J lists pool cutoff b X
    (fun q _ _ _=>‖ringComplex (primeProduct p q.support q.leftExponent)‖^2≤ Z^(ell+eta)) h1
  have hb₂ := supported_original_property p extra original negative J lists pool cutoff b X
    (fun q _ _ _=>‖ringComplex (primeProduct p q.support q.rightExponent)‖^2≤ Z^(ell+eta)) h2
  have hj := supported_original_property p extra original negative J lists pool cutoff b X
    (fun q _ _ _=> Z^(j-eta)≤‖ringComplex (jLabel p q.support
      (fun i=> q.leftExponent i+q.rightExponent i) q.leftBit q.rightBit)‖^2) hJ
  exact actual_cell_row_decrease p hp source hs hk d x hx Z M ell A t V j eta shortCutoff
    hZ hA ht heta hbin hterminal hsmall (hb₁ x hxs) (hb₂ x hxs) (hj x hxs)

end InverseMomentGlobalRetainedGates
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMomentFirstLabelCell
open InverseMoment Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open Eisenstein (ringComplex)
local notation "O" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

def extra (negative : Bool) (c : CubeCoordinates ι) : Finset ι :=
  if negative then c.rightExponent.support else c.leftExponent.support

lemma extra_subset (negative : Bool) (c : CubeCoordinates ι) : extra negative c⊆c.support := by
  cases negative
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

lemma dyadic_exponent_nonneg (Z : ℝ) (hZ : 1< Z) (n : ℕ) :
    0≤ InverseFirstGlobalCaps.dyadicExponent Z n :=
  Real.logb_nonneg hZ (by unfold dyadScale;exact one_le_pow₀ (by norm_num : (1:ℝ)≤2))

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma label_parent_valid (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (k : SourceIndex) (l j : ℕ) :
    ∀y∈InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j,SourceValid p y := by
  intro y hy
  obtain ⟨o,ho,D,hD,hs,rfl⟩ := (InverseFirstGlobalCaps.mem_parentCell p pool Q (fun _ _=>1) k l y).mp
    (Finset.mem_filter.mp hy).1
  exact original_fill_valid p pool Q o (Finset.mem_filter.mp ho).1 D

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem label_parent_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (k : SourceIndex) (l j : ℕ) (Z ell eta : ℝ) (hZ : 1< Z) (heta : 0≤ eta) (hbin : 2≤ Z^eta)
    (hQ : ∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta)) :
    ∀y∈InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j,
      ‖ringComplex (primeProduct p y.cube.support y.cube.leftExponent)‖^2≤ Z^(ell+eta) ∧
      ‖ringComplex (primeProduct p y.cube.support y.cube.rightExponent)‖^2≤ Z^(ell+eta) ∧
      primeProductNorm p (cubeActiveSupport y.cube.support
        (fun i=> y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit)
        ≤ Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 4)+eta) ∧
      primeProductNorm p y.firstCommon≤ Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 2)+eta) ∧
      primeProductNorm p y.quotientSupport≤ Z^(InverseFirstGlobalCaps.dyadicExponent Z l+eta) ∧
      Z^(InverseFirstGlobalCaps.dyadicExponent Z j-eta)≤ InverseFirstGlobalCaps.jNorm p (toOriginal y) ∧
      InverseFirstGlobalCaps.jNorm p (toOriginal y)≤ Z^(InverseFirstGlobalCaps.dyadicExponent Z j+eta) ∧
      primeProductNorm p y.firstDivisor≤ Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 3)+eta) := by
  intro y hy
  have hparent := (Finset.mem_filter.mp hy).1
  have hc := InverseFirstGlobalCaps.parentCell_cube_bounds p pool Q (fun _ _=>1) k l Z ell eta hQ y hparent
  have hn := InverseFirstGlobalCaps.parentCell_norm_bounds p hp pool Q (fun _ _=>1) k l Z eta hZ hbin y hparent
  have hi := InverseFirstGlobalCaps.parentCell_ideal_bounds p hp pool Q (fun _ _=>1) k l Z eta hZ hbin y hparent
  have hj := InverseFirstGlobalCaps.labelParentCell_bounds p hp pool Q (fun _ _=>1) k l j Z eta hZ hbin y hy
  refine ⟨hc.1,hc.2,?_,hi.1.2,?_,?_,hj.2.2,?_⟩
  · simpa only [InverseFirstGlobalCaps.sourceIdeal_norm] using hi.2.2.2
  · simpa only [hn.2.1] using hn.2.2.2
  · exact (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)).trans hj.2.1
  · simpa only [InverseFirstGlobalCaps.sourceIdeal_norm] using hi.2.1.2

include hp in

theorem retained_label_numeric (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (k : SourceIndex) (l j : ℕ) (Z ell eta : ℝ) (hZ : 1< Z) (heta : 0≤ eta) (hbin : 2≤ Z^eta)
    (hQ : ∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ) :
    let source := supportedRetainedSource p (extra negative)
      (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j) negative J lists pool cutoff b X
    ∀x∈source,
      ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤ Z^(ell+eta) ∧
      ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤ Z^(ell+eta) ∧
      primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=> x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)
        ≤ Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 4)+eta) ∧
      primeProductNorm p x.firstCommon≤ Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 2)+eta) ∧
      (Ideal.absNorm x.quotient:ℝ)≤ Z^(InverseFirstGlobalCaps.dyadicExponent Z l+eta) ∧
      Z^(InverseFirstGlobalCaps.dyadicExponent Z j-eta)≤
        ‖ringComplex (jLabel p x.cube.support (fun i=> x.cube.leftExponent i+x.cube.rightExponent i)
          x.cube.leftBit x.cube.rightBit)‖^2 ∧
      ‖ringComplex (jLabel p x.cube.support (fun i=> x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)‖^2≤ Z^(InverseFirstGlobalCaps.dyadicExponent Z j+eta) ∧
      primeProductNorm p x.firstDivisor≤ Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 3)+eta) := by
  intro source x hx
  have h := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ
  exact original_numeric_gates p (extra negative) _ negative J lists pool cutoff _ _ _ _ _ _ _
    (fun y hy=>(h y hy).1) (fun y hy=>(h y hy).2.1) (fun y hy=>(h y hy).2.2.1)
    (fun y hy=>(h y hy).2.2.2.1) (fun y hy=>(h y hy).2.2.2.2.1)
    (fun y hy=>⟨(h y hy).2.2.2.2.2.1,(h y hy).2.2.2.2.2.2.1⟩)
    (fun y hy=>(h y hy).2.2.2.2.2.2.2) x (supported_subset p _ _ negative J lists pool cutoff b X hx)

end InverseMomentFirstLabelCell
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMomentFirstLabelCell
open InverseMoment Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open InverseSecondUniformCutoff
open Eisenstein (ringComplex)
local notation "O" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

abbrev exponent := InverseFirstGlobalCaps.dyadicExponent

def columnA (Z : ℝ) (k : SourceIndex) (negative : Bool) : ℝ :=
  exponent Z (k (if negative then 0 else 1))

def columnScale (Z r : ℝ) (k : SourceIndex) (l : ℕ) (negative : Bool) : ℝ :=
  Z^(r-columnA Z k negative-exponent Z (k 2)-exponent Z l)

def secondCutoff (p : ι→O) (Z M r ell V eta tau window : ℝ) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (G E : Finset ι) : ℝ :=
  uniformSecondRadius p Z (exponent Z (k 3)) eta G E
    (columnScale Z r k l negative*Real.exp window) (firstCellRadius Z M r ell V eta tau k j) (Z^tau)

def source (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ) :=
  supportedRetainedSource p (extra negative)
    (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j)
    negative J lists pool (secondCutoff p Z M r ell V eta tau window k l j negative)
    b (columnScale Z r k l negative)

variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem source_valid (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ) :
    ActualSecondSourceConditions p (source p pool Q k l j negative J lists Z M r ell V eta tau window b) :=
  supported_conditions p hp _ _ (label_parent_valid p pool Q k l j) (fun y _hy=> extra_subset negative y.cube)
    negative J lists pool _ b _

lemma source_frequency_ne_zero (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ) :
    ∀x∈source p pool Q k l j negative J lists Z M r ell V eta tau window b,x.second.frequency≠0 :=
  supported_frequency_ne_zero p _ _ negative J lists pool _ b _

lemma source_geometry (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ) :
    ∀x∈source p pool Q k l j negative J lists Z M r ell V eta tau window b,
      primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤ b*columnScale Z r k l negative :=
  geometrySource_gate p _ b _

include hp in
theorem source_row_gates (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ)
    (hZ : 1< Z) (heta : 0≤ eta) (hbin : 2≤ Z^eta) (hwindow : Real.exp window≤ Z^(4*eta)) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    (∀x∈S,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta (index p x))) ∧
    (∀d∈keys p S,0≤ actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d) := by
  intro S
  have hz : 0< Z := zero_lt_one.trans hZ
  have hc : columnScale Z r k l negative*Real.exp window≤
      Z^(r-columnA Z k negative-exponent Z (k 2)-exponent Z l+4*eta) := by
    unfold columnScale
    rw [Real.rpow_add hz]
    exact mul_le_mul_of_nonneg_left hwindow (Real.rpow_nonneg hz.le _)
  exact supported_cell_row_gates p hp _ _ negative J lists pool Z M r ell V (exponent Z (k 3))
    (columnA Z k negative) (exponent Z (k 2)) (exponent Z j) (exponent Z l) eta tau
    (columnScale Z r k l negative*Real.exp window) b (columnScale Z r k l negative)
    hZ heta hbin (by unfold columnScale;positivity) hc

include hp in
theorem source_outer_caps (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b Lcol LY Lcap : ℝ)
    (hZ : 1< Z)
    (hcol : columnScale Z r k l negative*Real.exp window≤ Z^Lcol)
    (hYi : (firstCellRadius Z M r ell V eta tau k j)⁻¹≤ Z^LY)
    (hgeom : b*columnScale Z r k l negative≤ Z^Lcap)
    (hphysical : exponent Z (k 3)+eta+2*Lcol+tau+LY≤ Lcap) :
    ∀x∈source p pool Q k l j negative J lists Z M r ell V eta tau window b,
      ∀i,outerNorms p x i≤ Z^Lcap := by
  exact supported_outer_caps p hp _ _ negative J lists pool Z (exponent Z (k 3)) eta
    (columnScale Z r k l negative*Real.exp window) (firstCellRadius Z M r ell V eta tau k j)
    tau b (columnScale Z r k l negative) Lcol LY Lcap hZ.le
    (by unfold columnScale;positivity) (by unfold firstCellRadius;exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    hcol hYi hgeom hphysical

end InverseMomentFirstLabelCell
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMomentFirstLabelCell
open InverseMoment Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open Eisenstein (ringComplex)
local notation "O" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem source_labels (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ)
    (hZ : 1< Z) (heta : 0≤ eta) (hbin : 2≤ Z^eta)
    (hQ : ∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta)) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    (∀d,∀x∈cell p S d,(actualSecondChild p 1 1 x).2.1∈actualCellLabels p S d) ∧
    (∀d,∀I∈(actualCellLabels p S d).filter Squarefree,
      Squarefree I ∧ I≠0 ∧ (Ideal.absNorm I:ℝ)≤
        Z^(actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d)) := by
  intro S
  have hb := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ
  exact supported_label_gates p hp _ _ negative J lists pool _ b (columnScale Z r k l negative)
    Z (exponent Z (k 2)) (exponent Z j) eta hZ hbin
    (fun y hy=>(hb y hy).2.2.2.1) (fun y hy=>(hb y hy).2.2.2.2.2.2.1)

include hp in
theorem source_child_margins
    (hpr : ∀i,lambda^2∣p i-1)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ)
    (m : O) (hm : m≠0) (Qwidth z c : ℝ)
    (hZ : 1< Z) (heta : 0≤ eta) (hbin : 2≤ Z^eta) (hV : 0≤ V)
    (hparent : CanonicalMargins (r+3*ell+V) M Qwidth z c)
    (hpuncture : (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤ Z^Qwidth)
    (hQ : ∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta)) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    ∀d,∀γ∈actualSecondTriples p 1 1 (cell p S d),
      actualSecondInheritedRadicalPuncture m γ≠0 ∧ 0≤ actualSecondPunctureWidth Z m γ ∧
      ‖ringComplex (actualSecondInheritedRadicalPuncture m γ)‖^2=Z^(actualSecondPunctureWidth Z m γ) ∧
      CanonicalMargins (actualCellTotalExponent Z (columnScale Z r k l negative)
        (exponent Z (k 2)) (exponent Z j) eta d)
        (childM M ell (columnA Z k negative) (exponent Z l) (secondCellExponent Z d 0)
          (secondCellExponent Z d 1) V (exponent Z j) eta)
        (actualSecondPunctureWidth Z m γ) z (c-7*eta) := by
  intro S
  have hb := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ
  exact supported_child_margins p hp hpr _ _ (label_parent_valid p pool Q k l j)
    (fun y hy=> extra_subset negative y.cube) negative J lists pool _ b m hm
    Z r ell V M Qwidth z c (columnA Z k negative) (exponent Z (k 2)) (exponent Z l) (exponent Z j) eta
    hZ hparent (dyadic_exponent_nonneg Z hZ _) (dyadic_exponent_nonneg Z hZ _) hV
    (dyadic_exponent_nonneg Z hZ _) heta hbin hpuncture
    (fun y hy=>(hb y hy).1) (fun y hy=>(hb y hy).2.1) (fun y hy=>(hb y hy).2.2.2.2.1)

include hp in
theorem source_row_decrease (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b short : ℝ)
    (hZ : 1< Z) (heta : 0≤ eta) (hbin : 2≤ Z^eta)
    (hterminal : short≤ ell+V) (hsmall : eta≤ short/16)
    (hQ : ∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta)) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    ∀d∈keys p S,actualCellRowExponent Z M ell (columnA Z k negative)
      (exponent Z l) V (exponent Z j) eta d+3*short/2≤ M := by
  intro S
  have hb := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ
  exact supported_row_rank_decrease p hp _ _ (label_parent_valid p pool Q k l j)
    (fun y hy=> extra_subset negative y.cube) negative J lists pool _ b (columnScale Z r k l negative)
    Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta short hZ
    (dyadic_exponent_nonneg Z hZ _) (dyadic_exponent_nonneg Z hZ _) heta hbin hterminal hsmall
    (fun y hy=>(hb y hy).1) (fun y hy=>(hb y hy).2.1) (fun y hy=>(hb y hy).2.2.2.2.2.1)

include hp in
theorem source_mass_gate (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b Lcol LY Lcap eps pi : ℝ)
    (hZ : 1< Z) (heps : 0≤ eps)
    (hcol : columnScale Z r k l negative*Real.exp window≤ Z^Lcol)
    (hYi : (firstCellRadius Z M r ell V eta tau k j)⁻¹≤ Z^LY)
    (hgeom : b*columnScale Z r k l negative≤ Z^Lcap)
    (hphysical : exponent Z (k 3)+eta+2*Lcol+tau+LY≤ Lcap)
    (hbudget : eps*(ell+exponent Z (k 4)/2+exponent Z l+Lcap+11*eta/2)≤ pi) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    ∀d∈keys p S,eps*(secondCount ell (exponent Z (k 4)) (exponent Z j) (exponent Z l)
      (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2)≤ pi := by
  intro S
  exact source_cell_mass_gate p hp S (source_frequency_ne_zero p pool Q k l j negative J lists Z M r ell V eta tau window b)
    Z Lcap ell (exponent Z (k 4)) (exponent Z j) (exponent Z l) eta eps pi hZ
    (dyadic_exponent_nonneg Z hZ _) heps
    (source_outer_caps p hp pool Q k l j negative J lists Z M r ell V eta tau window b Lcol LY Lcap
      hZ hcol hYi hgeom hphysical) hbudget

end InverseMomentFirstLabelCell
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMomentFirstLabelCell
open InverseMoment Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open Eisenstein (ringComplex)
local notation "O" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem source_step_arithmetic (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b Lcol LY Lcap eps pi : ℝ)
    (hZ : 1< Z) (heta : 0≤ eta) (hbin : 2≤ Z^eta) (heps : 0≤ eps)
    (hwindow : Real.exp window≤ Z^(4*eta))
    (hQ : ∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta))
    (hcol : columnScale Z r k l negative*Real.exp window≤ Z^Lcol)
    (hYi : (firstCellRadius Z M r ell V eta tau k j)⁻¹≤ Z^LY)
    (hgeom : b*columnScale Z r k l negative≤ Z^Lcap)
    (hphysical : exponent Z (k 3)+eta+2*Lcol+tau+LY≤ Lcap)
    (hbudget : eps*(ell+exponent Z (k 4)/2+exponent Z l+Lcap+11*eta/2)≤ pi) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    ActualSecondSourceConditions p S ∧
    (∀x∈S,x.second.frequency≠0) ∧
    (∀x∈S,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta (index p x))) ∧
    (∀d∈keys p S,0≤ actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d) ∧
    (∀x∈S,
      ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤ Z^(ell+eta) ∧
      ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤ Z^(ell+eta) ∧
      primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=> x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)
        ≤ Z^(exponent Z (k 4)+eta) ∧
      primeProductNorm p x.firstCommon≤ Z^(exponent Z (k 2)+eta) ∧
      (Ideal.absNorm x.quotient:ℝ)≤ Z^(exponent Z l+eta) ∧
      Z^(exponent Z j-eta)≤
        ‖ringComplex (jLabel p x.cube.support (fun i=> x.cube.leftExponent i+x.cube.rightExponent i)
          x.cube.leftBit x.cube.rightBit)‖^2 ∧
      ‖ringComplex (jLabel p x.cube.support (fun i=> x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)‖^2≤ Z^(exponent Z j+eta) ∧
      primeProductNorm p x.firstDivisor≤ Z^(exponent Z (k 3)+eta)) ∧
    (∀d,∀x∈cell p S d,(actualSecondChild p 1 1 x).2.1∈actualCellLabels p S d) ∧
    (∀d,∀I∈(actualCellLabels p S d).filter Squarefree,
      Squarefree I ∧ I≠0 ∧ (Ideal.absNorm I:ℝ)≤ Z^(actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d)) ∧
    (∀x∈S,∀i,outerNorms p x i≤ Z^Lcap) ∧
    (∀x∈S,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤ b*columnScale Z r k l negative) ∧
    (∀d∈keys p S,eps*(secondCount ell (exponent Z (k 4)) (exponent Z j) (exponent Z l)
      (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2)≤ pi) := by
  intro S
  have hr := source_row_gates p hp pool Q k l j negative J lists Z M r ell V eta tau window b hZ heta hbin hwindow
  have hl := source_labels p hp pool Q k l j negative J lists Z M r ell V eta tau window b hZ heta hbin hQ
  exact ⟨source_valid p hp pool Q k l j negative J lists Z M r ell V eta tau window b,
    source_frequency_ne_zero p pool Q k l j negative J lists Z M r ell V eta tau window b,
    hr.1,hr.2,
    retained_label_numeric p hp pool Q k l j Z ell eta hZ heta hbin hQ negative J lists _ b _,
    hl.1,hl.2,
    source_outer_caps p hp pool Q k l j negative J lists Z M r ell V eta tau window b Lcol LY Lcap
      hZ hcol hYi hgeom hphysical,
    source_geometry p pool Q k l j negative J lists Z M r ell V eta tau window b,
    source_mass_gate p hp pool Q k l j negative J lists Z M r ell V eta tau window b Lcol LY Lcap eps pi
      hZ heps hcol hYi hgeom hphysical hbudget⟩

end InverseMomentFirstLabelCell
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMomentFirstLabelCell
open InverseMoment Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open InverseSecondUniformCutoff InversePrioritySecondSource
open Eisenstein (ringComplex)
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0)

def parentWeight (l : ℕ) (x : Source ι 0) : ℂ :=
  (‖commonSelector p (fun _=>1) l x.quotientSupport‖:ℂ)

lemma parentWeight_norm (l : ℕ) (x : Source ι 0) : ‖parentWeight p l x‖≤1 := by
  simp only [parentWeight,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  simpa using InverseFirstGlobalCaps.commonSelector_norm p (fun _=>1) l x.quotientSupport

lemma secondCutoff_nonneg (Z M r ell V eta tau window : ℝ) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (hZ : 0< Z) (G E : Finset ι) :
    0≤ secondCutoff p Z M r ell V eta tau window k l j negative G E := by
  apply uniformSecondRadius_nonneg _ _ _ _ _ _ _ _ _ hZ.le
  · unfold firstCellRadius
    positivity
  · exact Real.rpow_nonneg hZ.le _

include hp in
theorem secondCutoff_dominates (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (Z M r ell V eta tau window : ℝ) (hZ : 1< Z) (hbin : 2≤ Z^eta) :
    ∀y∈InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j,∀G E : Finset ι,
      correlatedSecondRadius p (secondParentDivisor p (parent p y)) G E
        (columnScale Z r k l negative*Real.exp window) (firstCellRadius Z M r ell V eta tau k j) (Z^tau)≤
      secondCutoff p Z M r ell V eta tau window k l j negative G E := by
  intro y hy G E
  have hd := (InverseFirstGlobalCaps.parentCell_ideal_bounds p hp pool Q (fun _ _=>1) k l
    Z eta hZ hbin y (Finset.mem_filter.mp hy).1).2.1.2
  apply correlated_le_uniform p Z (exponent Z (k 3)) eta _ G E _ _ _
    (by unfold firstCellRadius;exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  simpa [secondParentDivisor,parent,InverseFirstGlobalCaps.sourceIdeal_norm,
    primeProductNorm,map_prod] using hd

include hp in
theorem parent_tail_caps (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (Z ell eta Lcap : ℝ) (hZ : 1< Z) (heta : 0≤ eta) (hbin : 2≤ Z^eta) (hcap : 0≤ Lcap)
    (hQ : ∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta))
    (hell : ell+eta≤ Lcap) (hactive : exponent Z (k 4)+eta≤ Lcap)
    (hcommon : exponent Z (k 2)+eta≤ Lcap) (hquot : exponent Z l+eta≤ Lcap) :
    ∀y∈InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j,
      ‖ringComplex (primeProduct p y.cube.support y.cube.leftExponent)‖^2≤ Z^Lcap ∧
      ‖ringComplex (primeProduct p y.cube.support y.cube.rightExponent)‖^2≤ Z^Lcap ∧
      ‖ringComplex (∏i∈cubeActiveSupport y.cube.support
        (fun i=> y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit,p i)‖≤ Z^Lcap ∧
      primeProductNorm p y.firstCommon≤ Z^Lcap ∧ primeProductNorm p y.quotientSupport≤ Z^Lcap := by
  intro y hy
  have hb := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ y hy
  have hpw {a : ℝ} (ha : a≤ Lcap) : Z^a≤ Z^Lcap := Real.rpow_le_rpow_of_exponent_le hZ.le ha
  refine ⟨hb.1.trans (hpw hell),hb.2.1.trans (hpw hell),?_,
    hb.2.2.2.1.trans (hpw hcommon),hb.2.2.2.2.1.trans (hpw hquot)⟩
  have he := hb.2.2.1.trans (hpw hactive)
  have hone := Real.one_le_rpow hZ.le hcap
  change ‖ringComplex (∏i∈_,p i)‖^2≤ Z^Lcap at he
  have hn := norm_nonneg (ringComplex (∏i∈cubeActiveSupport y.cube.support
    (fun i=> y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit,p i))
  nlinarith

end InverseMomentFirstLabelCell
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
open InverseWholePriorityRetainedSource RayFourExpansion
local notation "Eis"=> Eisenstein.O
theorem global_priority_filtered_all_rays_uniform_types
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0< lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤ caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤ B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0< loFresh ∧ loFresh≤ hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤ Cbin ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
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
    let originalSource:=unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=> extra x.cube) original negative assigned lists) cutoff
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    ∀
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
    let source:=InverseMomentGlobalRetainedGates.geometrySource p originalSource b X;
      hi≤ b →
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
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z *
        ∑x∈originalSource,globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖ ≤
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    global_priority_filtered_moving_radius_uniform_types  om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,Cbin,hC,hCbin,he⟩:=hordered J
  refine ⟨C*(∑ z : SecondRayIndex, ‖secondRayCoefficient z‖),Cbin,by positivity,hCbin,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
    Ψ m ray core slots assigned lists a cutoff originalSource Ψ₀
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A source hhib
    haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let H:= (1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*(1+Cbin*Real.log Z)^4*
    Z^(r+3*ell+V+48*eta+tau+pi+εchild)
  let S:SecondRayIndex→ℂ:=fun z=>(Y:ℂ)*secondRayCoefficient z *
      ∑x∈originalSource,globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
          (principalWindow om lo hi hlo hsupport negative t) X Y z x
  have hP:0≤ P:=by dsimp [P];positivity
  have hH:0≤ H:=by dsimp [H];positivity
  have hz (z:SecondRayIndex):P*‖S z‖≤ C*A*H*‖secondRayCoefficient z‖:=by
    have h:=he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hwOriginal
      Ψ m ray core slots assigned lists a cutoff z
      Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A
      hhib haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
      ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass
      (hleft z) (hright z)
    convert h using 1 ; dsimp only [P,S,H] ; ring
  calc
    _≤ P*∑z:SecondRayIndex,‖S z‖:=mul_le_mul_of_nonneg_left (norm_sum_le _ _) hP
    _=∑z:SecondRayIndex,P*‖S z‖:=Finset.mul_sum _ _ _
    _≤∑z:SecondRayIndex,C*A*H*‖secondRayCoefficient z‖:=Finset.sum_le_sum (fun z _=> hz z)
    _=C*A*H*(∑z:SecondRayIndex,‖secondRayCoefficient z‖):=(Finset.mul_sum _ _ _).symm
    _= C*A*H*(∑ z : SecondRayIndex, ‖secondRayCoefficient z‖):=rfl
    _= _:=by dsimp [H];ring

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
open InverseWholePriorityRetainedSource RayFourExpansion
local notation "Eis"=> Eisenstein.O
theorem global_priority_filtered_aggregate_uniform_types
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0< lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤ caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤ B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0< loFresh ∧ loFresh≤ hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤ Cbin ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
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
    (Ψ:Eis→*ℂ) (m:Eis)
    (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:Finset ι→Finset ι→ℝ)
,
    ∀
        (Y:ℝ) (R:Finset σ→BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : Finset σ→BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      hi≤ b → slots.card≤ K → 0≤ A → (∀(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ), assigned⊆slots →
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
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityRetainedAggregate p hg hp hcop extra pool original w
          negative Ψ m slots lists a (principalWindow om lo hi hlo hsupport negative t) X Y cutoff ≤
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    global_priority_filtered_all_rays_uniform_types  om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,Cbin,hC,hCbin,he⟩:=hordered J
  have hcore : 0 ≤ firstCoreMassBound := by unfold firstCoreMassBound; positivity
  let Ctot:=firstCoreMassBound*(4:ℝ)^K*(Fintype.card (RayCharacter×RayCharacter):ℝ)*
    (Fintype.card FirstCoreIndex:ℝ)*C
  refine ⟨Ctot,Cbin,by dsimp [Ctot];positivity,hCbin,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
    Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A hhib hslots hA hdata
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let H:=C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild)
  have hb (ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ)(ha:assigned⊆slots):
    P*‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z *
      ∑x∈unifiedSource p pool (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=> extra x.cube) original negative assigned lists) (fun _=> cutoff),
        globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative
            (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖≤ H:=by
    obtain ⟨haassigned,hρ,hL,hZ,hX,hY,heta,hbin,hrows,hcube₁,hcube₂,hactive,hj,hquot,hΨ,
      ha₁,ha₂,hlabels,ho,hslots₁,hslots₂,hA',hYe,hXe,hLe,hVe,hZ2,hb,hthreshold,hnorm,hgeom,hmass,hleft,hright⟩:=hdata ray core assigned ha
    exact he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hwOriginal
      Ψ m ray core slots assigned lists a (fun _=> cutoff)
      Y (R assigned) L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t (labels assigned) A
      hhib haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
      ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA' hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have hZ:1< Z:=(hdata 1 1 ∅ (Finset.empty_subset _)).2.2.2.1
  have hH:0≤ H:=by dsimp [H];positivity
  have hpow:(4:ℝ)^slots.card≤4^K:=pow_le_pow_right₀ (by norm_num) hslots
  let S:(RayCharacter×RayCharacter)→FirstCoreIndex→Finset σ→ℝ:=fun ray core assigned=>‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z *
      ∑x∈unifiedSource p pool (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=> extra x.cube) original negative assigned lists) (fun _=> cutoff),
        globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative
            (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖
  change ∀ray core assigned, assigned⊆slots → P*S ray core assigned≤ H at hb
  change P*(firstCoreMassBound*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑assigned∈slots.powerset,S ray core assigned)≤ _
  calc
    _=firstCoreMassBound*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑assigned∈slots.powerset,P*S ray core assigned:=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ray hr
      apply Finset.sum_congr rfl
      intro core hc
      apply Finset.sum_congr rfl
      intro assigned ha
      ring
    _≤firstCoreMassBound*(2:ℝ)^slots.card*∑_ray:RayCharacter×RayCharacter,∑_core:FirstCoreIndex,∑_assigned∈slots.powerset,H:=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun ray _=> Finset.sum_le_sum fun core _=> Finset.sum_le_sum fun assigned ha=> hb ray core assigned (Finset.mem_powerset.mp ha)
    _=firstCoreMassBound*(4:ℝ)^slots.card*(Fintype.card (RayCharacter×RayCharacter):ℝ)*(Fintype.card FirstCoreIndex:ℝ)*H:=by
      simp only [Finset.sum_const,Finset.card_univ,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      rw [show (4:ℝ)^slots.card=(2:ℝ)^slots.card*(2:ℝ)^slots.card by rw [←mul_pow];norm_num]
      ring
    _≤firstCoreMassBound*(4:ℝ)^K*(Fintype.card (RayCharacter×RayCharacter):ℝ)*(Fintype.card FirstCoreIndex:ℝ)*H:=by gcongr
    _= _:=by dsimp [Ctot,H];ring
end InverseMoment

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

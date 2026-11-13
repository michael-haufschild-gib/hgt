/-
Marked second sources adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Inversion.AssignedCallersAndSecondFibers

/-!
# Marked second sources

Marked second sources and their source conditions, nonzero child frequency balls and divisor
multiplicity weights. Uniform marked-column moments at fixed caps; separated second columns.
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

namespace InverseMoment
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialClippedColumns InverseInitialOverlapFourier JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
/-- A compact smooth cutoff equal to one on a fixed positive interval. -/
theorem positive_cutoff (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ∃ w : 𝓢(ℝ,ℂ), HasCompactSupport (w : ℝ→ℂ) ∧
      (∀ x∈Set.Icc a b,w x=1) ∧ tsupport (w : ℝ→ℂ)⊆Set.Icc (a/2) (b+a/2) := by
  let f := CompletedHeight.positiveCutoff a b ha
  let v : ℝ→ℂ := fun x => (f x:ℂ)
  have hv : ContDiff ℝ ∞ v := Complex.ofRealCLM.contDiff.comp f.contDiff
  have hvs : Function.support v⊆Set.Icc (a/2) (b+a/2) := by
    intro x hx
    have hh : f x ≠ 0 := by simpa only [v,Function.mem_support,ne_eq,Complex.ofReal_eq_zero] using hx
    simpa only [max_eq_right hab] using CompletedHeight.positiveCutoff_support_bounds a b ha x hh
  have hvc := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hvs
  refine ⟨hvc.toSchwartzMap hv,hvc,?_,closure_minimal hvs isClosed_Icc⟩
  intro x hx
  change (f x:ℂ)=1
  rw [CompletedHeight.positiveCutoff_one a b ha x hx,Complex.ofReal_one]

theorem clipped_fixed_window (W:ℝ→ℂ) (lo hi b:ℝ) (hlo:0<lo) (hb:1≤b)
    (hW:Function.support W⊆Set.Icc lo hi):
    ∃(wFresh:𝓢(ℝ,ℂ))(af bf:ℝ),0<af ∧ af≤bf ∧ HasCompactSupport (wFresh:ℝ→ℂ) ∧
      tsupport (wFresh:ℝ→ℂ)⊆Set.Icc af bf ∧
      ∀c,1≤c→c≤b→∀y,0<y→wFresh y*W (c*y)=W (c*y):=by
  have hb0:0<b:=zero_lt_one.trans_le hb
  let a:=lo/b
  let B:=a+|hi|+1
  have ha:0<a:=div_pos hlo hb0
  obtain ⟨wFresh,hc,hone,hs⟩:=positive_cutoff a B ha (by dsimp [B];linarith [abs_nonneg hi])
  refine ⟨wFresh,a/2,B+a/2,half_pos ha,by dsimp [B];linarith [abs_nonneg hi],hc,hs,?_⟩
  intro c hc hcb y hy
  by_cases hz:W (c*y)=0
  · simp only [hz,mul_zero]
  have hw:=hW hz
  have hay:a≤y:=by
    apply (div_le_iff₀ hb0).mpr
    calc
      lo≤c*y:=hw.1
      _≤y*b:=by nlinarith
  have hyhi:y≤hi:=le_trans (by nlinarith) hw.2
  have hyB:y≤B:=by dsimp [B];linarith [le_abs_self hi]
  rw [hone y ⟨hay,hyB⟩,one_mul]

theorem clipped_test_fourier (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo)
    (hs:Function.support W⊆Set.Icc lo hi) (hW:ContDiff ℝ ∞ W)
    (wFresh:ℝ→ℂ)(c θ y:ℝ)(hc:0<c)(hy:0<y)(hwFresh:wFresh y*W (c*y)=W (c*y)):
    clippedTest W c θ y =
      ∫t:ℝ,density (CanonicalCubeSeparation.sourceLogProfile W lo hi hlo hs hW) (Real.log c) t *
        childLogTest wFresh (θ+t) y:=by
  let g:=CanonicalCubeSeparation.sourceLogProfile W lo hi hlo hs hW
  change clippedTest W c θ y=∫t:ℝ,density g (Real.log c) t*childLogTest wFresh (θ+t) y
  have he (t:ℝ):density g (Real.log c) t*childLogTest wFresh (θ+t) y=
      ((𝓕 g) t*kernelLogPhase t (Real.log c+Real.log y))*(wFresh y*kernelLogPhase θ (Real.log y)):=by
    simp only [density,childLogTest,kernelLogPhase_add_frequency,kernelLogPhase_add]
    ring
  simp_rw [he]
  rw [integral_mul_const]
  have hi':(∫t:ℝ,(𝓕 g) t*kernelLogPhase t (Real.log c+Real.log y))=W (c*y):=by
    calc
      _=(∫t:ℝ,kernelLogPhase t (Real.log c+Real.log y)*(𝓕 g) t):=by
        apply integral_congr_ae
        filter_upwards with t
        ring
      _=g (Real.log c+Real.log y):=(schwartz_phase_inversion g _).symm
      _= _:=by
        simp only [g,CanonicalCubeSeparation.sourceLogProfile_apply,Real.exp_add,Real.exp_log hc,Real.exp_log hy]
  rw [hi']
  unfold clippedTest childLogTest
  calc
    W (c*y)*kernelLogPhase θ (Real.log y)=(wFresh y*W (c*y))*kernelLogPhase θ (Real.log y):=by rw [hwFresh]
    _= _:=by ring


variable {ι σ : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda∉Ideal.span {p i})

theorem finiteCanonicalMarkedRow_test_sum
    (pool : Finset ι) (Ψ : O →* ℂ) (m f k : O)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (W : ℝ→ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hg pool Ψ m f k slots lists a W X =
      ∑ U∈pool.powerset,secondChildColumn p hg Ψ m f k (primeMark slots lists a) U *
        W (primeProductNorm p U/X) := by
  unfold finiteCanonicalMarkedRow fixedChildRow
  apply Finset.sum_congr rfl
  intro U hU
  simp only [secondChildColumn]
  ring

theorem canonical_clipped_mode_integrable
    (pool : Finset ι) (Ψ : O →* ℂ) (m f k : O)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (g : 𝓢(ℝ,ℂ)) (wFresh : ℝ→ℂ) (c θ X : ℝ) :
    Integrable (fun t : ℝ=>density g (Real.log c) t *
      finiteCanonicalMarkedRow p hg pool Ψ m f k slots lists a
        (childLogTest wFresh (θ+t)) X) := by
  simp_rw [finiteCanonicalMarkedRow_test_sum]
  simp only [Finset.mul_sum]
  apply integrable_finsetSum
  intro U hU
  convert fourier_phase_integrable g (Real.log c+Real.log (primeProductNorm p U/X))
    (secondChildColumn p hg Ψ m f k (primeMark slots lists a) U *
      wFresh (primeProductNorm p U/X)*kernelLogPhase θ (Real.log (primeProductNorm p U/X))) using 1 <;> first
  | rfl
  | (funext t; simp only [density,childLogTest,kernelLogPhase_add_frequency,kernelLogPhase_add]; ring)

include hp in
theorem canonical_clipped_fourier
    (pool : Finset ι) (Ψ : O →* ℂ) (m f k : O)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo)
    (hs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (wFresh : ℝ→ℂ) (c θ X : ℝ) (hc : 0<c) (hX : 0<X)
    (hwFresh : ∀ y,0<y→wFresh y*W (c*y)=W (c*y)) :
    finiteCanonicalMarkedRow p hg pool Ψ m f k slots lists a (clippedTest W c θ) X =
      ∫ t : ℝ,density (CanonicalCubeSeparation.sourceLogProfile W lo hi hlo hs hW) (Real.log c) t *
        finiteCanonicalMarkedRow p hg pool Ψ m f k slots lists a (childLogTest wFresh (θ+t)) X := by
  simp_rw [finiteCanonicalMarkedRow_test_sum]
  simp only [Finset.mul_sum]
  have hints (U : Finset ι) : Integrable (fun t : ℝ=>
      density (CanonicalCubeSeparation.sourceLogProfile W lo hi hlo hs hW) (Real.log c) t *
      (secondChildColumn p hg Ψ m f k (primeMark slots lists a) U *
        childLogTest wFresh (θ+t) (primeProductNorm p U/X))) := by
    convert fourier_phase_integrable (CanonicalCubeSeparation.sourceLogProfile W lo hi hlo hs hW)
      (Real.log c+Real.log (primeProductNorm p U/X))
      (secondChildColumn p hg Ψ m f k (primeMark slots lists a) U *
        wFresh (primeProductNorm p U/X)*kernelLogPhase θ (Real.log (primeProductNorm p U/X))) using 1 <;> first
    | rfl
    | (funext t; simp only [density,childLogTest,kernelLogPhase_add_frequency,kernelLogPhase_add]; ring)
  rw [integral_finsetSum _ (fun U _=>hints U)]
  apply Finset.sum_congr rfl
  intro U hU
  rw [clipped_test_fourier W lo hi hlo hs hW wFresh c θ _ hc
    (div_pos (primeProductNorm_pos p hp U) hX)
    (hwFresh _ (div_pos (primeProductNorm_pos p hp U) hX)),←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  ring

end InverseMoment

namespace InverseMoment
open Eisenstein SchwartzPlanePoisson CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialClippedColumns InverseInitialProfile InverseInitialOverlapFourier
open InverseInitialRayAttachment MeasureTheory JointLogSeparation
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
local notation "O"=>Eisenstein.O
variable {ι σ:Type*}[DecidableEq ι]
  (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

theorem normalized_energy_vector
    (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(rows:Finset O)(D:Ideal O→ℝ)(hD:∀f∈labels,0≤D f)
    (W:ℝ→ℂ)(X Z F:ℝ):
    (∑v:labels×rows,‖(Real.sqrt (D v.1):ℂ)*((Z^(-F/2):ℝ):ℂ)*
      finiteCanonicalMarkedRow p hg pool Ψ m (primaryIdealGenerator v.1) v.2 slots lists a W X‖^2)=
    normalizedColumnEnergy p hg pool Ψ m slots lists a labels rows D W X Z F:=by
  unfold normalizedColumnEnergy
  rw [Fintype.sum_prod_type,←Finset.sum_coe_sort labels]
  apply Finset.sum_congr rfl
  intro f hf
  rw [←Finset.sum_coe_sort rows,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [mul_assoc,norm_mul,mul_pow,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hD f f.property)]

include hp in
theorem canonical_clipped_energy
    (hpr:∀i,lambda^2∣p i-1)
    (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(rows:Finset O)(D:Ideal O→ℝ)(hD:∀f∈labels,0≤D f)
    (W:ℝ→ℂ)(lo hi:ℝ)(hlo:0<lo)(hs:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W)
    (wFresh:ℝ→ℂ)(c θ X Z F E:ℝ)(J:ℕ)(hc:0<c)(hX:0<X)(hE:0≤E)
    (hw:∀y,0<y→wFresh y*W (c*y)=W (c*y))
    (he:∀s,normalizedColumnEnergy p hg pool Ψ m slots lists a labels rows D
      (childLogTest wFresh s) X Z F≤E*(1+‖s‖)^(2*J)):
    normalizedColumnEnergy p hg pool Ψ m slots lists a labels rows D
      (clippedTest W c θ) X Z F≤
      E*(1+‖θ‖)^(2*J)*(∫t:ℝ,(1+‖t‖)^J*‖(𝓕 (CanonicalCubeSeparation.sourceLogProfile W lo hi hlo hs hW)) t‖)^2:=by
  let g:=CanonicalCubeSeparation.sourceLogProfile W lo hi hlo hs hW
  let b:=density g (Real.log c)
  let phi:labels×rows→ℝ→ℂ:=fun v t=>(Real.sqrt (D v.1):ℂ)*((Z^(-F/2):ℝ):ℂ)*
    finiteCanonicalMarkedRow p hg pool Ψ m (primaryIdealGenerator v.1) v.2 slots lists a
      (childLogTest wFresh (θ+t)) X
  have hint(v:labels×rows):Integrable (fun t:ℝ=>b t*phi v t):=by
    convert (canonical_clipped_mode_integrable p hg pool Ψ m (primaryIdealGenerator v.1) v.2
      slots lists a g wFresh c θ X).const_mul ((Real.sqrt (D v.1):ℂ)*((Z^(-F/2):ℝ):ℂ)) using 1 <;> first
    | rfl
    | (funext t; dsimp [b,phi]; ring)
  have hbound(t:ℝ):(∑v:labels×rows,‖phi v t‖^2)≤
      (E*(1+‖θ‖)^(2*J))*((1+‖t‖)^J)^2:=by
    dsimp only [phi]
    rw [normalized_energy_vector p hg pool Ψ m slots lists a labels rows D hD]
    apply (he (θ+t)).trans
    have hb:1+‖θ+t‖≤(1+‖θ‖)*(1+‖t‖):=by
      have hh:=norm_add_le θ t
      nlinarith [mul_nonneg (norm_nonneg θ) (norm_nonneg t)]
    calc
      _≤E*((1+‖θ‖)*(1+‖t‖))^(2*J):=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb _) hE
      _= _:=by rw [mul_pow,pow_mul];ring
  have hden:Integrable (fun t:ℝ=>(1+‖t‖)^J*‖b t‖):=by
    simpa only [b,density_norm] using CanonicalCubeSeparation.weighted_schwartz_integrable (𝓕 g) J
  have hden' : Integrable (fun t : ℝ=>‖b t‖*(1+|t|)^J) := by
    simpa only [Real.norm_eq_abs,mul_comm] using hden
  have hbound' (t : ℝ) : (∑v:labels×rows,‖phi v t‖^2) ≤
      (E*(1+‖θ‖)^(2*J))*(1+|t|)^(2*J) := by
    have hr : ((1+|t|)^J)^2=(1+|t|)^(2*J) := by rw [←pow_mul,Nat.mul_comm J 2]
    simpa only [Real.norm_eq_abs,hr] using hbound t
  have hh := CanonicalRowCompletion.finite_integral_energy_polynomial b phi J
    (E*(1+‖θ‖)^(2*J)) (by positivity) hden' hint hbound'
  have heq(v:labels×rows): (∫t:ℝ,b t*phi v t)=
      (Real.sqrt (D v.1):ℂ)*((Z^(-F/2):ℝ):ℂ)*
      finiteCanonicalMarkedRow p hg pool Ψ m (primaryIdealGenerator v.1) v.2 slots lists a
        (clippedTest W c θ) X:=by
    rw [canonical_clipped_fourier p hp hg pool Ψ m (primaryIdealGenerator v.1) v.2
      slots lists a W lo hi hlo hs hW wFresh c θ X hc hX hw,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    dsimp [b,phi,g]
    ring
  simp_rw [heq] at hh
  rw [normalized_energy_vector p hg pool Ψ m slots lists a labels rows D hD] at hh
  simpa only [b,density_norm,g,Real.norm_eq_abs,mul_comm] using hh


end InverseMoment

namespace InverseMoment
open Eisenstein SchwartzPlanePoisson CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialClippedColumns InverseInitialProfile InverseInitialOverlapFourier
open InverseInitialRayAttachment MeasureTheory JointLogSeparation
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
local notation "O"=>Eisenstein.O

theorem canonical_clipped_uniform
    (W:ℝ→ℂ)(lo hi b:ℝ)(hlo:0<lo)(hb:1≤b)
    (hs:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W):
    ∃(wFresh:𝓢(ℝ,ℂ))(af bf:ℝ),0<af ∧ af≤bf ∧ HasCompactSupport (wFresh:ℝ→ℂ) ∧
      tsupport (wFresh:ℝ→ℂ)⊆Set.Icc af bf ∧
      ∀J:ℕ,∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i})
      (_hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (labels:Finset (Ideal O))(rows:Finset O)(D:Ideal O→ℝ)(_hD:∀f∈labels,0≤D f)
      (c θ X Z F E:ℝ),1≤c→c≤b→0<X→0≤E→
      (∀s,normalizedColumnEnergy p hg pool Ψ m slots lists a labels rows D
        (childLogTest wFresh s) X Z F≤E*(1+‖s‖)^(2*J))→
      normalizedColumnEnergy p hg pool Ψ m slots lists a labels rows D
        (clippedTest W c θ) X Z F≤C*E*(1+‖θ‖)^(2*J):=by
  obtain ⟨wFresh,af,bf,haf,hab,hc,hsf,hagree⟩:=clipped_fixed_window W lo hi b hlo hb hs
  refine ⟨wFresh,af,bf,haf,hab,hc,hsf,?_⟩
  intro J
  let M:=(∫t:ℝ,(1+‖t‖)^J*‖(𝓕 (CanonicalCubeSeparation.sourceLogProfile W lo hi hlo hs hW)) t‖)^2
  refine ⟨M+1,by dsimp [M];positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr pool Ψ m slots lists a labels rows D hD c θ X Z F E hc1 hcb hX hE he
  have hh:=canonical_clipped_energy p hp hg hpr pool Ψ m slots lists a labels rows D hD
    W lo hi hlo hs hW wFresh c θ X Z F E J (zero_lt_one.trans_le hc1) hX hE
    (hagree c hc1 hcb) he
  apply hh.trans
  change E*(1+‖θ‖)^(2*J)*M≤(M+1)*E*(1+‖θ‖)^(2*J)
  have hn:0≤E*(1+‖θ‖)^(2*J):=by positivity
  nlinarith


end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
noncomputable section
local notation "Eis" => Eisenstein.O

def childFrequencyBall (a : Eis) (R : ℝ) : Finset Eis :=
  (secondFrequencyCutoff (‖ringComplex a‖^2) R).filter
    (fun k => ‖ringComplex (a*k)‖^2 ≤ R)

lemma mem_childFrequencyBall (a : Eis) (ha : a ≠ 0) (R : ℝ) (k : Eis) :
    k ∈ childFrequencyBall a R ↔ ‖ringComplex (a*k)‖^2 ≤ R := by
  have hn : 0 < ‖ringComplex a‖^2 := sq_pos_of_pos
    (norm_pos_iff.mpr (ringComplex_ne_zero ha))
  simp only [childFrequencyBall, Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_,h⟩⟩
  apply mem_secondFrequencyCutoff
  apply (le_div_iff₀ hn).mpr
  simpa only [map_mul, norm_mul, mul_pow, mul_comm] using h

lemma outside_childFrequencyBall (a : Eis) (ha : a ≠ 0) (R : ℝ) (k : Eis)
    (hk : k ∉ childFrequencyBall a R) : R < ‖ringComplex (a*k)‖^2 :=
  lt_of_not_ge (fun h => hk ((mem_childFrequencyBall a ha R k).mpr h))

def nonzeroChildFrequencyBall (a : Eis) (R : ℝ) : Finset Eis :=
  (childFrequencyBall a R).erase 0

lemma mem_nonzeroChildFrequencyBall (a : Eis) (ha : a ≠ 0) (R : ℝ) (k : Eis) :
    k ∈ nonzeroChildFrequencyBall a R ↔
      0 < ‖ringComplex (a*k)‖^2 ∧ ‖ringComplex (a*k)‖^2 ≤ R := by
  have hn : 0 < ‖ringComplex (a*k)‖^2 ↔ k ≠ 0 := by
    rw [sq_pos_iff, norm_ne_zero_iff]
    constructor
    · intro h hk; apply h; simp [hk]
    · intro hk; exact ringComplex_ne_zero (mul_ne_zero ha hk)
  simp only [nonzeroChildFrequencyBall, Finset.mem_erase,
    mem_childFrequencyBall a ha, hn]

lemma nonzeroChildFrequencyBall_empty (a : Eis) (ha : a ≠ 0) (R : ℝ) (hR : R < 1) :
    nonzeroChildFrequencyBall a R = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  have hm := (mem_nonzeroChildFrequencyBall a ha R k).mp hk
  have hk0 : k ≠ 0 := by intro hk; simp [hk] at hm
  exact (not_le_of_gt hR) ((SchwartzPlanePoisson.one_le_eisenstein_norm_sq
    (a*k) (mul_ne_zero ha hk0)).trans hm.2)

def childOuterRadius (Y A E X₁ X₂ H : ℝ) : ℝ := A*E*X₁*X₂*H/Y

theorem childFrequencyBall_raw_tail {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) (Y A E X₁ X₂ H : ℝ)
    (hY : 0 < Y) (hA : 0 < A) (hE : 0 < E)
    (hX₁ : 0 < X₁) (_hX₂ : 0 < X₂) (hH : 0 ≤ H)
    (a e : Eis) (ha : a ≠ 0) (he : e ≠ 0)
    (haA : ‖ringComplex a‖^2 ≤ A) (heE : ‖ringComplex e‖^2 ≤ E)
    (S T : Finset ι) (hd : Disjoint S T)
    (hS : primeProductNorm p S ≤ X₁) (hT : primeProductNorm p T ≤ X₂)
    (k : Eis) (hk : k ∉ childFrequencyBall a (childOuterRadius Y A E X₁ X₂ H)) :
    H ≤ (Y / (‖ringComplex e‖^2 *
      ‖ringComplex (∏ i : ↥((T \ S) ∪ (S \ T)), p i.val)‖^2)) * ‖ringComplex k‖^2 := by
  have haN : 0 < ‖ringComplex a‖^2 := sq_pos_of_pos
    (norm_pos_iff.mpr (ringComplex_ne_zero ha))
  have heN : 0 < ‖ringComplex e‖^2 := sq_pos_of_pos
    (norm_pos_iff.mpr (ringComplex_ne_zero he))
  have hden : ‖ringComplex a‖^2 * ‖ringComplex e‖^2 *
      primeProductNorm p S * primeProductNorm p T ≤ A*E*X₁*X₂ := by
    exact mul_le_mul (mul_le_mul (mul_le_mul haA heE heN.le hA.le)
      hS (primeProductNorm_pos p hp S).le (mul_pos hA hE).le)
      hT (primeProductNorm_pos p hp T).le (by positivity)
  have hchild := (outside_childFrequencyBall a ha _ k hk).le
  simp only [map_mul,norm_mul,mul_pow,childOuterRadius] at hchild
  have hbound : H * (‖ringComplex a‖^2 * ‖ringComplex e‖^2 *
      primeProductNorm p S * primeProductNorm p T) ≤
      Y * (‖ringComplex a‖^2 * ‖ringComplex k‖^2) := by
    calc
      _ ≤ H*(A*E*X₁*X₂) := mul_le_mul_of_nonneg_left hden hH
      _ ≤ _ := by nlinarith [(div_le_iff₀ hY).mp hchild]
  have hcancel : H * (‖ringComplex e‖^2 * primeProductNorm p S *
      primeProductNorm p T) ≤ Y * ‖ringComplex k‖^2 := by
    apply (mul_le_mul_iff_right₀ haN).mp
    nlinarith [hbound]
  rw [active_product_norm_disjoint p S T hd]
  have hdpos : 0 < ‖ringComplex e‖^2 * (primeProductNorm p S * primeProductNorm p T) :=
    mul_pos heN (mul_pos (primeProductNorm_pos p hp S) (primeProductNorm_pos p hp T))
  rw [div_mul_eq_mul_div, le_div_iff₀ hdpos]
  simpa only [mul_assoc] using hcancel

theorem childFrequencyBall_remainder {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2) (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (Y A E X₁ X₂ H : ℝ),
      0 < Y → 0 < A → 0 < E → 0 < X₁ → 0 < X₂ → 0 ≤ H →
      ∀ (a e : Eis), a ≠ 0 → e ≠ 0 →
      ‖ringComplex a‖^2 ≤ A → ‖ringComplex e‖^2 ≤ E →
      ∀ (S T : Finset ι), Disjoint S T →
      primeProductNorm p S ≤ X₁ → primeProductNorm p T ≤ X₂ →
      let n := ∏ i : ↥((T \ S) ∪ (S \ T)), p i.val
      let scale := Y / (‖ringComplex e‖^2 * ‖ringComplex n‖^2)
      ‖∑' k : {k : Eis // k ∉ childFrequencyBall a (childOuterRadius Y A E X₁ X₂ H)},
        secondPairRadialMode p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp S T e k.val W Y‖ ≤
      (Y / ‖ringComplex n‖) *
        ((C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 scale)^2 * (1+H)^order)) := by
  obtain ⟨s,C,hC,hb⟩ := full_uniform_secondPairRadialMode_remainder order
  have hb := hb p hp hg hinj
  refine ⟨s,C,hC,?_⟩
  intro W Y A E X₁ X₂ H hY hA hE hX₁ hX₂ hH a e ha he haA heE S T hd hS hT
  exact hb S T e he W Y H hY hH _
    (fun k hk => childFrequencyBall_raw_tail p hp Y A E X₁ X₂ H hY hA hE hX₁ hX₂ hH
      a e ha he haA heE S T hd hS hT k hk)

theorem nonzeroChildFrequencyBall_absolute_tail {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2) (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (Y A E X₁ X₂ H : ℝ),
      0 < Y → 0 < A → 0 < E → 0 < X₁ → 0 < X₂ → 0 ≤ H →
      ∀ (a e : Eis), a ≠ 0 → e ≠ 0 →
      ‖ringComplex a‖^2 ≤ A → ‖ringComplex e‖^2 ≤ E →
      ∀ (S T : Finset ι), Disjoint S T →
      primeProductNorm p S ≤ X₁ → primeProductNorm p T ≤ X₂ →
      let n := ∏ i : ↥((T \ S) ∪ (S \ T)), p i.val
      let scale := Y / (‖ringComplex e‖^2 * ‖ringComplex n‖^2)
      (∑' k : {k : Eis // k ≠ 0 ∧ k ∉ nonzeroChildFrequencyBall a (childOuterRadius Y A E X₁ X₂ H)},
        ‖secondPairRadialMode p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp S T e k.val W Y‖) ≤
      (Y / ‖ringComplex n‖) *
        ((C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 scale)^2 * (1+H)^order)) := by
  obtain ⟨s,C,hC,hb⟩ := full_uniform_secondPairRadialMode_tail order
  have hb := hb p hp hg hinj
  refine ⟨s,C,hC,?_⟩
  intro W Y A E X₁ X₂ H hY hA hE hX₁ hX₂ hH a e ha he haA heE S T hd hS hT
  dsimp only
  let n := ∏ i : ↥((T \ S) ∪ (S \ T)), p i.val
  let scale := Y / (‖ringComplex e‖^2 * ‖ringComplex n‖^2)
  let small : Set Eis := {k | k ≠ 0 ∧ k ∉ nonzeroChildFrequencyBall a (childOuterRadius Y A E X₁ X₂ H)}
  let large : Set Eis := {k | H ≤ scale * ‖ringComplex k‖^2}
  have hmap : ∀ k : small, k.val ∈ large := by
    intro k
    apply childFrequencyBall_raw_tail p hp Y A E X₁ X₂ H hY hA hE hX₁ hX₂ hH
      a e ha he haA heE S T hd hS hT k.val
    intro hk
    exact k.property.2 (Finset.mem_erase.mpr ⟨k.property.1,hk⟩)
  let f : small → large := fun k => ⟨k.val,hmap k⟩
  have hi : Function.Injective f := by
    intro x y h; exact Subtype.ext (congrArg (fun z : large => z.val) h)
  have hs := (secondPairRadialMode_summable p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp S T e he W Y hY).norm
  calc
    _ ≤ ∑' k : large, ‖secondPairRadialMode p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp S T e k.val W Y‖ :=
      (hs.subtype small).tsum_le_tsum_of_inj f hi (fun _ _ => norm_nonneg _)
        (fun _ => le_rfl) (hs.subtype large)
    _ ≤ _ := hb S T e he W Y H hY hH

end
end InverseMoment

namespace InverseMoment
open Eisenstein
open scoped BigOperators Classical
lemma child_ball_neg (R : ℝ) (k : O) :
    -k ∈ nonzeroChildFrequencyBall 1 R ↔ k ∈ nonzeroChildFrequencyBall 1 R := by
  simp only [mem_nonzeroChildFrequencyBall _ one_ne_zero,one_mul,map_neg,norm_neg]

lemma child_ball_sum_neg {β : Type*} [AddCommMonoid β] (R : ℝ) (F : O → β) :
    ∑ k ∈ nonzeroChildFrequencyBall 1 R,F (-k) =
      ∑ k ∈ nonzeroChildFrequencyBall 1 R,F k := by
  apply Finset.sum_bij (fun k _ => -k)
  · intro k hk
    exact (child_ball_neg R k).mpr hk
  · intro a ha b hb he
    exact neg_injective he
  · intro b hb
    exact ⟨-b,(child_ball_neg R b).mpr hb,neg_neg b⟩
  · intro k hk
    rfl


/-- Divisor multiplicity weight for the canonical marked energy. -/
def secondLabelWeight (K:ℕ) (f:Ideal O) : ℝ := ((idealDivisors f).card:ℝ)^(9+4*K)
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open Eisenstein FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve
open InverseInitialClippedColumns
open CanonicalCoefficientClass
local notation "O"=>Eisenstein.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg:∀i,lambda∉Ideal.span {p i})

/-- Uniform marked-column moments at a fixed row cap, total cap, and margin. -/
def CanonicalRankMoments (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z Mmax Fcap z c eps A:ℝ)(K degree:ℕ):Prop :=
  ∀(Ψ:O→*ℂ),IsBaseRayTwist base Ψ→∀(m:O),m≠0→∀N V M Qwidth:ℝ,
    0≤ N→0≤ V→0≤ M→0≤ Qwidth→M≤ Mmax→N+V≤ Fcap→
    CanonicalMargins (N+V) M Qwidth z c→
    ‖ringComplex m‖^2=Z^Qwidth→
    ∀(subslots:Finset σ),subslots⊆slots→∀labels:Finset (Ideal O),
      (∀I∈labels,Admissible I ∧ (Ideal.absNorm I:ℝ)≤ Z^V)→∀s:ℝ,
    normalizedColumnEnergy p hg pool Ψ m subslots lists a labels
      (nonzeroChildFrequencyBall 1 (Z^M)) (secondLabelWeight K) (childLogTest W s) (Z^N) Z (N+V)≤
      A*Z^(N+V+eps)*(1+‖s‖)^(2*degree)

end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open Eisenstein CanonicalQuadraticSieve InverseInitialClippedColumns
local notation "O"=>Eisenstein.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg:∀i,lambda∉Ideal.span {p i})

omit [DecidableEq σ] in
theorem canonical_rank_negative (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z Mmax Fcap z c eps A:ℝ)(K degree:ℕ)(hM:Mmax<0):
    CanonicalRankMoments p hg pool base slots lists a W Z Mmax Fcap z c eps A K degree :=by
  intro Ψ hΨ m hm N V M Qwidth hN hV hM0 hQ hMc
  exfalso
  linarith

omit [DecidableEq σ] in
theorem canonical_rank_restrict (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z M₁ M₂ F₁ F₂ z c₁ c₂ eps A:ℝ)(K degree:ℕ)
    (hM:M₁≤ M₂)(hF:F₁≤ F₂)(hc:c₂≤ c₁)
    (h:CanonicalRankMoments p hg pool base slots lists a W Z M₂ F₂ z c₂ eps A K degree):
    CanonicalRankMoments p hg pool base slots lists a W Z M₁ F₁ z c₁ eps A K degree :=by
  intro Ψ hΨ m hm N V M Qwidth hN hV hM0 hQ hMc hFc hmargin hnorm ss hss labels hlabels s
  have hmarg:CanonicalMargins (N+V) M Qwidth z c₂:=by
    unfold CanonicalMargins at *
    constructor <;> linarith [hmargin.1,hmargin.2]
  exact h Ψ hΨ m hm N V M Qwidth hN hV hM0 hQ (hMc.trans hM) (hFc.trans hF) hmarg hnorm ss hss labels hlabels s

omit [DecidableEq σ] in
theorem canonical_rank_height_constant (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z M F z c eps A B:ℝ)(K degree J:ℕ)
    (hZ:0<Z)(hA:0≤ A)(hAB:A≤ B)(hJ:degree≤ J)
    (h:CanonicalRankMoments p hg pool base slots lists a W Z M F z c eps A K degree):
    CanonicalRankMoments p hg pool base slots lists a W Z M F z c eps B K J :=by
  intro Ψ hΨ m hm N V Mr Qwidth hN hV hM0 hQ hMc hFc hmargin hnorm ss hss labels hlabels s
  apply (h Ψ hΨ m hm N V Mr Qwidth hN hV hM0 hQ hMc hFc hmargin hnorm ss hss labels hlabels s).trans
  have hB:0≤ B:=hA.trans hAB
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg hZ.le _)
  · exact pow_le_pow_right₀ (by linarith [norm_nonneg s]) (Nat.mul_le_mul_left 2 hJ)
  · positivity
  · positivity

end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open Eisenstein CanonicalQuadraticSieve InverseInitialClippedColumns
local notation "O"=>Eisenstein.O

theorem canonical_rank_loss_le {ι σ:Type}[DecidableEq ι][DecidableEq σ]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i})
    (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z M F z c eps eps' A:ℝ)(K degree:ℕ)
    (hZ:1≤ Z)(hA:0≤ A)(he:eps≤ eps')
    (h:CanonicalRankMoments p hg pool base slots lists a W Z M F z c eps A K degree):
    CanonicalRankMoments p hg pool base slots lists a W Z M F z c eps' A K degree :=by
  intro Ψ hΨ m hm N V Mr Q hN hV hM hQ hMc hFc hmargin hnorm ss hss labels hlabels s
  apply (h Ψ hΨ m hm N V Mr Q hN hV hM hQ hMc hFc hmargin hnorm ss hss labels hlabels s).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) hA

end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open Eisenstein CompletedGauss InverseSecondFibers
noncomputable section
local notation "Eis" => Eisenstein.O

abbrev SecondChild := OuterTriple × Ideal Eis × Eis

def secondChild {Jo Jn : ℕ} (x : SecondTuple Jo Jn) : SecondChild :=
  (x.outer, x.core 0 * x.core 1 * x.core 2 * x.commonResidual,
    primaryIdealGenerator (x.core 7) * primaryIdealGenerator (x.core 2) * x.frequency)

def secondDivisorWeight (K : ℕ) (c : SecondChild) : ℝ :=
  ((idealDivisors c.2.1).card : ℝ) ^ (9 + 4*K) *
    ((idealDivisors c.1.q0).card : ℝ) ^ (5 + 2*K) *
    ((idealDivisors c.1.quotient).card : ℝ) ^ (2*K) *
    ((idealDivisors c.1.residual).card : ℝ) ^ (2*K)

theorem secondChild_eq_iff_valid {Jo Jn : ℕ} (x : SecondTuple Jo Jn)
    (hx : Valid x (secondChild x).1 (secondChild x).2.1 (secondChild x).2.2)
    (c : SecondChild) : secondChild x = c ↔ Valid x c.1 c.2.1 c.2.2 := by
  constructor
  · intro he
    simpa only [he] using hx
  · intro hv
    apply Prod.ext hv.outer_eq
    exact Prod.ext hv.label hv.row_eq

theorem secondChild_fiber_weight {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset InverseInitialFibers.PrimeIdeal)
    (newLists : Fin Jn → Finset InverseInitialFibers.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop)
    (hvalid : ∀ x ∈ originalSource source oldLists newLists keep,
      Valid x (secondChild x).1 (secondChild x).2.1 (secondChild x).2.2)
    (c : SecondChild) (hf : c.2.1 ≠ 0) (hq : c.1.q0 ≠ 0)
    (ht : c.1.quotient ≠ 0) (hr : c.1.residual ≠ 0)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : SecondTuple Jo Jn → ℝ)
    (hw : ∀ x ∈ originalSource source oldLists newLists keep, w x ≤ 1) :
    (∑ x ∈ (originalSource source oldLists newLists keep).filter (fun x => secondChild x = c), w x) ≤
      secondDivisorWeight K c := by
  have hfilter : (originalSource source oldLists newLists keep).filter (fun x => secondChild x = c) =
      secondFiber source oldLists newLists keep c.1 c.2.1 c.2.2 := by
    apply Finset.filter_congr
    intro x hx
    exact secondChild_eq_iff_valid x (hvalid x hx) c
  calc
    _ ≤ ∑ _x ∈ (originalSource source oldLists newLists keep).filter (fun x => secondChild x = c), (1 : ℝ) :=
      Finset.sum_le_sum (fun x hx => hw x (Finset.mem_filter.mp hx).1)
    _ = ((secondFiber source oldLists newLists keep c.1 c.2.1 c.2.2).card : ℝ) := by rw [hfilter]; simp
    _ ≤ secondDivisorWeight K c := by
      have hh := secondFiber_card_le source oldLists newLists keep c.1 c.2.1 c.2.2 hf hq ht hr K ho hn
      dsimp only [secondDivisorWeight]
      exact_mod_cast hh

theorem second_energy_projection {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset InverseInitialFibers.PrimeIdeal)
    (newLists : Fin Jn → Finset InverseInitialFibers.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop)
    (hvalid : ∀ x ∈ originalSource source oldLists newLists keep,
      Valid x (secondChild x).1 (secondChild x).2.1 (secondChild x).2.2)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hf : ∀ f ∈ labels, f ≠ 0)
    (houter : ∀ γ ∈ sourceTriples source oldLists newLists keep,
      γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0)
    (hchild : ∀ x ∈ originalSource source oldLists newLists keep,
      (secondChild x).2.1 ∈ labels ∧ (secondChild x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : SecondTuple Jo Jn → ℝ)
    (hw : ∀ x ∈ originalSource source oldLists newLists keep, w x ≤ 1)
    (F : SecondChild → ℂ) :
    (∑ x ∈ originalSource source oldLists newLists keep, w x * ‖F (secondChild x)‖ ^ 2) ≤
      ∑ γ ∈ sourceTriples source oldLists newLists keep,
        ((idealDivisors γ.q0).card : ℝ) ^ (5 + 2*K) *
        ((idealDivisors γ.quotient).card : ℝ) ^ (2*K) *
        ((idealDivisors γ.residual).card : ℝ) ^ (2*K) *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ) ^ (9 + 4*K) *
          ∑ k ∈ rows, ‖F (γ, f, k)‖ ^ 2 := by
  have hmaps : ∀ x ∈ originalSource source oldLists newLists keep,
      secondChild x ∈ sourceTriples source oldLists newLists keep ×ˢ (labels ×ˢ rows) := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩,
      Finset.mem_product.mpr (hchild x hx)⟩
  have hfiber : ∀ c ∈ sourceTriples source oldLists newLists keep ×ˢ (labels ×ˢ rows),
      (∑ x ∈ (originalSource source oldLists newLists keep).filter (fun x => secondChild x = c), w x) ≤
        secondDivisorWeight K c := by
    intro c hc
    obtain ⟨hγ, hfk⟩ := Finset.mem_product.mp hc
    obtain ⟨hq, ht, hr⟩ := houter c.1 hγ
    exact secondChild_fiber_weight source oldLists newLists keep hvalid c
      (hf c.2.1 (Finset.mem_product.mp hfk).1) hq ht hr K ho hn w hw
  have he := fiber_energy_bound (originalSource source oldLists newLists keep)
    (sourceTriples source oldLists newLists keep ×ˢ (labels ×ˢ rows)) secondChild w
    (secondDivisorWeight K) (fun c => ‖F c‖ ^ 2) hmaps (fun _ _ => sq_nonneg _) hfiber
  apply he.trans_eq
  simp only [Finset.sum_product, secondDivisorWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  apply Finset.sum_congr rfl
  intro f hfm
  apply Finset.sum_congr rfl
  intro k hk
  ring

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open Eisenstein CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen sourceIdeal_ne_zero sourceIdeal_union sourceIdeal_injective sourcePrime source_prime_dvd)
noncomputable section
local notation "Eis" => Eisenstein.O

@[ext] structure SecondOriginalSource (ι : Type*) (Jo Jn : ℕ) where
  q0 : Ideal Eis
  quotient : Ideal Eis
  J : Ideal Eis
  C : Ideal Eis
  s : Ideal Eis
  b1 : Ideal Eis
  A1 : Ideal Eis
  A2 : Ideal Eis
  dK : Ideal Eis
  J2 : Ideal Eis
  b2 : Ideal Eis
  common : Finset ι
  divisor : Finset ι
  overlap : Finset ι
  frequency : Eis
  oldAssigned : Fin Jo → InverseInitialFibers.PrimeIdeal
  newAssigned : Fin Jn → ι

variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  [∀ i, (Ideal.span {p i}).IsMaximal]

def originalSecondTuple {Jo Jn : ℕ} (u v : Eisˣ) (x : SecondOriginalSource ι Jo Jn) : SecondTuple Jo Jn where
  outer := ⟨x.q0,x.quotient,sourceIdeal p (x.common \ x.divisor)⟩
  core := ![x.J,x.C,sourceIdeal p x.divisor,x.s,x.b1,x.A1,x.A2,x.dK]
  commonResidual := sourceIdeal p x.overlap
  cubeResidual := x.J2
  secondCube := x.b2
  extractedCommon := sourceIdeal p x.common
  frequency := secondUnitFrequency u v x.frequency
  oldAssigned := x.oldAssigned
  newAssigned := fun i => sourcePrime p (x.newAssigned i)

structure SecondOriginalValid {Jo Jn : ℕ} (x : SecondOriginalSource ι Jo Jn) : Prop where
  j_split : x.s*x.J2 = x.J
  b_split : x.b1*x.b2 = x.q0^2*x.J2^2*x.s
  a1 : x.A1 ∣ (x.b1*x.b2).radical
  a2 : x.A2 ∣ (x.b1*x.b2).radical
  first_divisor : x.dK ∣ x.C*(x.b1*x.b2).radical
  first_generator : primaryIdealGenerator x.dK ≠ 0
  second_subset : x.divisor ⊆ x.common
  old_support : ∀ i, (x.oldAssigned i).val ∣ x.q0*x.J*x.C*x.quotient
  new_support : ∀ i, x.newAssigned i ∈ x.common ∪ x.overlap

theorem originalSecondTuple_valid (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, lambda^2 ∣ p i - 1)
    {Jo Jn : ℕ} (u v : Eisˣ) (x : SecondOriginalSource ι Jo Jn) (hx : SecondOriginalValid x) :
    Valid (originalSecondTuple p u v x)
      (secondChild (originalSecondTuple p u v x)).1
      (secondChild (originalSecondTuple p u v x)).2.1
      (secondChild (originalSecondTuple p u v x)).2.2 := by
  have hproduct : sourceIdeal p x.divisor * sourceIdeal p (x.common \ x.divisor) =
      sourceIdeal p x.common := by
    rw [←sourceIdeal_union p x.divisor (x.common \ x.divisor)
      (Finset.disjoint_left.mpr (fun i hi hj => (Finset.mem_sdiff.mp hj).2 hi)),
      Finset.union_sdiff_of_subset hx.second_subset]
  refine ⟨rfl,rfl,hx.j_split,hx.b_split,hx.a1,hx.a2,hx.first_divisor,?_,hx.first_generator,?_,rfl,?_,?_⟩
  · exact hproduct
  · change primaryIdealGenerator (sourceIdeal p x.divisor) ≠ 0
    rw [sourceIdeal_gen p hp hpr]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  · intro i
    apply (hx.old_support i).trans
    change x.q0*x.J*x.C*x.quotient ∣
      x.q0*(x.J*x.C*sourceIdeal p x.divisor*sourceIdeal p x.overlap)*x.quotient
    refine ⟨sourceIdeal p x.divisor*sourceIdeal p x.overlap,?_⟩
    ring
  · intro i
    change (sourcePrime p (x.newAssigned i)).val ∣
      (x.J*x.C*sourceIdeal p x.divisor*sourceIdeal p x.overlap)*sourceIdeal p (x.common \ x.divisor)
    have hslot : (sourcePrime p (x.newAssigned i)).val ∣
        sourceIdeal p x.common*sourceIdeal p x.overlap := by
      rcases Finset.mem_union.mp (hx.new_support i) with hi|hi
      · exact dvd_mul_of_dvd_left (source_prime_dvd p x.common _ hi) _
      · exact dvd_mul_of_dvd_right (source_prime_dvd p x.overlap _ hi) _
    apply hslot.trans
    refine ⟨x.J*x.C,?_⟩
    rw [←hproduct]
    ring

theorem originalSecondTuple_injective
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) :
    Function.Injective (originalSecondTuple (Jo:=Jo) (Jn:=Jn) p u v) := by
  intro x y hxy
  have hi := sourceIdeal_injective p hinj
  have hcore (i : Fin 8) := congrArg (fun z : SecondTuple Jo Jn => z.core i) hxy
  apply SecondOriginalSource.ext
  · exact congrArg (fun z : SecondTuple Jo Jn => z.outer.q0) hxy
  · exact congrArg (fun z : SecondTuple Jo Jn => z.outer.quotient) hxy
  · exact hcore 0
  · exact hcore 1
  · exact hcore 3
  · exact hcore 4
  · exact hcore 5
  · exact hcore 6
  · exact hcore 7
  · exact congrArg SecondTuple.cubeResidual hxy
  · exact congrArg SecondTuple.secondCube hxy
  · exact hi (congrArg SecondTuple.extractedCommon hxy)
  · exact hi (hcore 2)
  · exact hi (congrArg SecondTuple.commonResidual hxy)
  · exact secondUnitFrequency_injective u v (congrArg SecondTuple.frequency hxy)
  · exact congrArg SecondTuple.oldAssigned hxy
  · funext i
    apply hinj
    exact congrArg (fun z : SecondTuple Jo Jn => (z.newAssigned i).val) hxy

theorem original_second_source_fiber_bound (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, lambda^2 ∣ p i - 1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) (source : Finset (SecondOriginalSource ι Jo Jn))
    (hs : ∀ x ∈ source, SecondOriginalValid x)
    (γ : OuterTriple) (f : Ideal Eis) (k : Eis)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K) :
    (source.filter (fun x => secondChild (originalSecondTuple p u v x) = (γ,f,k))).card ≤
      (idealDivisors f).card^(9+4*K) *
      (idealDivisors γ.q0).card^(5+2*K) *
      (idealDivisors γ.quotient).card^(2*K) *
      (idealDivisors γ.residual).card^(2*K) := by
  classical
  let S := source.filter (fun x => secondChild (originalSecondTuple p u v x) = (γ,f,k))
  have hv : ∀ y ∈ S.image (originalSecondTuple p u v), Valid y γ f k := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxs,he⟩ := Finset.mem_filter.mp hx
    have hh := originalSecondTuple_valid p hp hpr u v x (hs x hxs)
    simpa only [he] using hh
  have hb := valid_tuple_card_le_slot_cap (S.image (originalSecondTuple p u v))
    γ f k hf hq ht hr hv K ho hn
  rw [Finset.card_image_of_injective S (originalSecondTuple_injective p hinj u v)] at hb
  exact hb

theorem originalSecondTuple_row_norm {Jo Jn : ℕ} (u v : Eisˣ)
    (x : SecondOriginalSource ι Jo Jn) (d e : Eis)
    (hde : d*e = (v:Eis)*(primaryIdealGenerator x.dK*primaryIdealGenerator (sourceIdeal p x.divisor))) :
    ‖ringComplex (secondChild (originalSecondTuple p u v x)).2.2‖ =
      ‖ringComplex (d*e*x.frequency)‖ := by
  exact secondCanonical_row_norm x.dK (sourceIdeal p x.divisor) u v d e x.frequency hde

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open Eisenstein FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open Eisenstein SchwartzPlanePoisson InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen sourceIdeal_ne_zero sourceIdeal_union sourceIdeal_injective sourcePrime source_prime_dvd)
noncomputable section
local notation "Eis" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  [∀ i, (Ideal.span {p i}).IsMaximal]

lemma sourceIdeal_isRadical
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) (S : Finset ι) :
    (sourceIdeal p S).IsRadical := by
  change (Ideal.span {∏ i ∈ S,p i}).IsRadical
  rw [span_finset_prime_product]
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact fun _ _ => by simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha,Ideal.mul_eq_inf_of_isCoprime]
    · exact (inferInstance : (Ideal.span {p a}).IsPrime).isRadical.inf ih
    · apply IsCoprime.prod_right
      intro b hb
      exact hcop (fun he => ha (he.symm ▸ hb))

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma cubeRadical_span_dvd_product (B : Finset ι) (v : ι → ℕ)
    (hv : ∀ i ∈ B, 0 < v i) :
    sourceIdeal p B ∣ Ideal.span {primeProduct p B v} := by
  apply span_dvd_of_element_dvd
  change (∏ i ∈ B,p i) ∣ primeProduct p B v
  unfold primeProduct
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  exact dvd_pow_self _ (Nat.ne_of_gt (hv i hi))

theorem cubeSupport_dvd_radical
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    sourceIdeal p B ∣
      (Ideal.span {primeProduct p B v₁}*Ideal.span {primeProduct p B v₂}).radical := by
  apply Ideal.dvd_iff_le.mpr
  apply (sourceIdeal_isRadical p hcop B).radical_le_iff.mpr
  apply Ideal.dvd_iff_le.mp
  rw [Ideal.span_singleton_mul_span_singleton,←primeProduct_add]
  exact cubeRadical_span_dvd_product p B _ hv

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma aLabel_dvd_cubeSupport (B : Finset ι) (ε : ι → Bool) :
    Ideal.span {aLabel p B ε} ∣ sourceIdeal p B := by
  apply span_dvd_of_element_dvd
  unfold aLabel primeProduct
  change (∏ i ∈ B,p i^bit (ε i)) ∣ ∏ i ∈ B,p i
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  cases hh : ε i <;> simp [bit]

theorem firstMask_dvd_cube_radical
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (B C D : Finset ι) (hCB : Disjoint C B) (hD : D ⊆ C∪B)
    (v₁ v₂ : ι → ℕ) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    sourceIdeal p D ∣ sourceIdeal p C *
      (Ideal.span {primeProduct p B v₁}*Ideal.span {primeProduct p B v₂}).radical := by
  have hd := InverseInitialArithmetic.sourceIdeal_dvd p D (C∪B) hD
  rw [sourceIdeal_union p C B hCB] at hd
  exact hd.trans (mul_dvd_mul_left _ (cubeSupport_dvd_radical p hcop B v₁ v₂ hv))

def cubeSecondSource {Jo Jn : ℕ} (B C D G E V : Finset ι)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (t : Ideal Eis) (k : Eis)
    (oldAssigned : Fin Jo → InverseInitialFibers.PrimeIdeal) (newAssigned : Fin Jn → ι) :
    SecondOriginalSource ι Jo Jn where
  q0 := Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}
  quotient := t
  J := Ideal.span {jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂}
  C := sourceIdeal p C
  s := Ideal.span {squarefreeLabel p B (fun i => v₁ i+v₂ i)}
  b1 := Ideal.span {primeProduct p B v₁}
  A1 := Ideal.span {aLabel p B ε₁}
  A2 := Ideal.span {aLabel p B ε₂}
  dK := sourceIdeal p D
  J2 := Ideal.span {j2Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}
  b2 := Ideal.span {primeProduct p B v₂}
  common := G
  divisor := E
  overlap := V
  frequency := k
  oldAssigned := oldAssigned
  newAssigned := newAssigned

theorem cubeSecondSource_valid (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, lambda^2 ∣ p i - 1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    {Jo Jn : ℕ} (B C D G E V : Finset ι) (hCB : Disjoint C B)
    (hD : D ⊆ C∪B) (hE : E ⊆ G)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i)
    (t : Ideal Eis) (k : Eis)
    (oldAssigned : Fin Jo → InverseInitialFibers.PrimeIdeal) (newAssigned : Fin Jn → ι)
    (hold : ∀ i, (oldAssigned i).val ∣
      Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂} *
      Ideal.span {jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂} * sourceIdeal p C * t)
    (hnew : ∀ i, newAssigned i ∈ G∪V) :
    SecondOriginalValid (cubeSecondSource p B C D G E V v₁ v₂ ε₁ ε₂ t k oldAssigned newAssigned) := by
  constructor
  · change Ideal.span {squarefreeLabel p B (fun i => v₁ i+v₂ i)} *
        Ideal.span {j2Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂} = _
    rw [Ideal.span_singleton_mul_span_singleton,←jLabel_eq_squarefree_mul_j2]
    rfl
  · have hb := congrArg (fun a : Eis => (Ideal.span {a} : Ideal Eis))
      (cube_pair_product_decomposition p B v₁ v₂ ε₁ ε₂ hv)
    simpa only [cubeSecondSource,pow_two,←Ideal.span_singleton_mul_span_singleton] using hb
  · exact (aLabel_dvd_cubeSupport p B ε₁).trans (cubeSupport_dvd_radical p hcop B v₁ v₂ hv)
  · exact (aLabel_dvd_cubeSupport p B ε₂).trans (cubeSupport_dvd_radical p hcop B v₁ v₂ hv)
  · exact firstMask_dvd_cube_radical p hcop B C D hCB hD v₁ v₂ hv
  · change primaryIdealGenerator (sourceIdeal p D) ≠ 0
    rw [sourceIdeal_gen p hp hpr]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  · exact hE
  · exact hold
  · exact hnew

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem oldSlot_dvd_reconstructed_support
    (B C : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) (P t : Ideal Eis)
    (hP : P ∣ sourceIdeal p B*sourceIdeal p C*t) :
    P ∣ Ideal.span {b0Label p B v ε₁ ε₂}*
      Ideal.span {jLabel p B v ε₁ ε₂}*sourceIdeal p C*t := by
  have hb := span_dvd_of_element_dvd (cubeRadical_dvd_jLabel_b0 p B v ε₁ ε₂ hv)
  change sourceIdeal p B ∣ Ideal.span {jLabel p B v ε₁ ε₂*b0Label p B v ε₁ ε₂} at hb
  rw [←Ideal.span_singleton_mul_span_singleton,mul_comm (Ideal.span {jLabel p B v ε₁ ε₂})] at hb
  exact hP.trans (mul_dvd_mul_right (mul_dvd_mul_right hb _) _)

theorem cubeSecondSource_valid_original_slots (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, lambda^2 ∣ p i - 1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    {Jo Jn : ℕ} (B C D G E V : Finset ι) (hCB : Disjoint C B)
    (hD : D ⊆ C∪B) (hE : E ⊆ G)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i)
    (t : Ideal Eis) (k : Eis)
    (oldAssigned : Fin Jo → InverseInitialFibers.PrimeIdeal) (newAssigned : Fin Jn → ι)
    (hold : ∀ i, (oldAssigned i).val ∣ sourceIdeal p B*sourceIdeal p C*t)
    (hnew : ∀ i, newAssigned i ∈ G∪V) :
    SecondOriginalValid (cubeSecondSource p B C D G E V v₁ v₂ ε₁ ε₂ t k oldAssigned newAssigned) :=
  cubeSecondSource_valid p hp hpr hcop B C D G E V hCB hD hE v₁ v₂ ε₁ ε₂ hv t k
    oldAssigned newAssigned
    (fun i => oldSlot_dvd_reconstructed_support p B C _ ε₁ ε₂ hv _ t (hold i)) hnew

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open Eisenstein FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open Eisenstein SchwartzPlanePoisson InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_injective)
noncomputable section
local notation "Eis" => Eisenstein.O

@[ext] structure MarkedSecondSource (ι : Type*) (Jo Jn : ℕ) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  firstDivisor : Finset ι
  second : SecondExpansionData ι
  quotient : Ideal Eis
  oldAssigned : Fin Jo → InverseInitialFibers.PrimeIdeal
  newAssigned : Fin Jn → ι

variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  [∀ i, (Ideal.span {p i}).IsMaximal]

def markedSecondOriginal {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : SecondOriginalSource ι Jo Jn :=
  cubeSecondSource p x.cube.support x.firstCommon x.firstDivisor
    x.second.sourceCommon x.second.divisor x.second.overlap
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
    x.quotient x.second.frequency x.oldAssigned x.newAssigned

theorem markedSecondOriginal_injOn (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i})) {Jo Jn : ℕ} :
    Set.InjOn (markedSecondOriginal (Jo:=Jo) (Jn:=Jn) p) {x | x.cube.Admissible} := by
  intro x hx y hy hxy
  have hc : x.cube = y.cube := by
    apply cubeDivisorKey_injective_on_product p hp hinj hx hy
    · simpa only [markedSecondOriginal,cubeSecondSource,cubeProductIdeal] using
        congrArg (fun z : SecondOriginalSource ι Jo Jn => z.b1*z.b2) hxy
    · funext i
      fin_cases i
      · simpa [markedSecondOriginal,cubeSecondSource,cubeDivisorKey] using
          congrArg SecondOriginalSource.b1 hxy
      · simpa [markedSecondOriginal,cubeSecondSource,cubeDivisorKey] using
          congrArg SecondOriginalSource.A1 hxy
      · simpa [markedSecondOriginal,cubeSecondSource,cubeDivisorKey] using
          congrArg SecondOriginalSource.A2 hxy
  apply MarkedSecondSource.ext hc
  · exact sourceIdeal_injective p hinj (congrArg SecondOriginalSource.C hxy)
  · exact sourceIdeal_injective p hinj (congrArg SecondOriginalSource.dK hxy)
  · apply SecondExpansionData.ext
    · exact congrArg SecondOriginalSource.common hxy
    · exact congrArg SecondOriginalSource.divisor hxy
    · exact congrArg SecondOriginalSource.overlap hxy
    · exact congrArg SecondOriginalSource.frequency hxy
  · exact congrArg SecondOriginalSource.quotient hxy
  · exact congrArg SecondOriginalSource.oldAssigned hxy
  · exact congrArg SecondOriginalSource.newAssigned hxy

theorem markedSecondTuple_injOn (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i})) {Jo Jn : ℕ} (u v : Eisˣ) :
    Set.InjOn (fun x : MarkedSecondSource ι Jo Jn => originalSecondTuple p u v (markedSecondOriginal p x))
      {x | x.cube.Admissible} := by
  intro x hx y hy he
  exact markedSecondOriginal_injOn p hp hinj hx hy
    (originalSecondTuple_injective p hinj u v he)

theorem markedSecondOriginal_valid (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, lambda^2 ∣ p i - 1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hCB : Disjoint x.firstCommon x.cube.support)
    (hD : x.firstDivisor ⊆ x.firstCommon∪x.cube.support)
    (hE : x.second.divisor ⊆ x.second.sourceCommon)
    (hold : ∀ i, (x.oldAssigned i).val ∣
      sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*x.quotient)
    (hnew : ∀ i, x.newAssigned i ∈ x.second.sourceCommon∪x.second.overlap) :
    SecondOriginalValid (markedSecondOriginal p x) :=
  cubeSecondSource_valid_original_slots p hp hpr hcop x.cube.support x.firstCommon x.firstDivisor
    x.second.sourceCommon x.second.divisor x.second.overlap hCB hD hE
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit x.cube.support_pos
    x.quotient x.second.frequency x.oldAssigned x.newAssigned hold hnew

theorem actual_marked_second_source_fiber (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, lambda^2 ∣ p i - 1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo Jn))
    (ha : ∀ x ∈ source, x.cube.Admissible)
    (hCB : ∀ x ∈ source, Disjoint x.firstCommon x.cube.support)
    (hD : ∀ x ∈ source, x.firstDivisor ⊆ x.firstCommon∪x.cube.support)
    (hE : ∀ x ∈ source, x.second.divisor ⊆ x.second.sourceCommon)
    (hold : ∀ x ∈ source, ∀ i, (x.oldAssigned i).val ∣
      sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*x.quotient)
    (hnew : ∀ x ∈ source, ∀ i, x.newAssigned i ∈ x.second.sourceCommon∪x.second.overlap)
    (γ : OuterTriple) (f : Ideal Eis) (k : Eis)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K) :
    (source.filter (fun x => secondChild (originalSecondTuple p u v (markedSecondOriginal p x)) = (γ,f,k))).card ≤
      (idealDivisors f).card^(9+4*K) *
      (idealDivisors γ.q0).card^(5+2*K) *
      (idealDivisors γ.quotient).card^(2*K) *
      (idealDivisors γ.residual).card^(2*K) := by
  classical
  let encode := fun x : MarkedSecondSource ι Jo Jn => originalSecondTuple p u v (markedSecondOriginal p x)
  let S := source.filter (fun x => secondChild (encode x) = (γ,f,k))
  have hvalid : ∀ x ∈ source,
      Valid (encode x) (secondChild (encode x)).1 (secondChild (encode x)).2.1 (secondChild (encode x)).2.2 := by
    intro x hx
    exact originalSecondTuple_valid p hp hpr u v (markedSecondOriginal p x)
      (markedSecondOriginal_valid p hp hpr hcop x (hCB x hx) (hD x hx) (hE x hx) (hold x hx) (hnew x hx))
  have hv : ∀ y ∈ S.image encode, Valid y γ f k := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxs,he⟩ := Finset.mem_filter.mp hx
    simpa only [he] using hvalid x hxs
  have hi : Set.InjOn encode (S : Set (MarkedSecondSource ι Jo Jn)) := by
    intro x hx y hy he
    exact markedSecondTuple_injOn p hp hinj u v
      (ha x (Finset.mem_filter.mp hx).1) (ha y (Finset.mem_filter.mp hy).1) he
  have hb := valid_tuple_card_le_slot_cap (S.image encode) γ f k hf hq ht hr hv K ho hn
  rw [Finset.card_image_iff.mpr hi] at hb
  exact hb

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open Eisenstein SchwartzPlanePoisson InverseSecondFibers
noncomputable section
local notation "Eis" => Eisenstein.O

def tripleDivisorWeight (K : ℕ) (γ : OuterTriple) : ℝ :=
  ((idealDivisors γ.q0).card : ℝ)^(5+2*K) *
    ((idealDivisors γ.quotient).card : ℝ)^(2*K) *
    ((idealDivisors γ.residual).card : ℝ)^(2*K)

lemma tripleDivisorWeight_nonneg (K : ℕ) (γ : OuterTriple) :
    0 ≤ tripleDivisorWeight K γ := by unfold tripleDivisorWeight; positivity

theorem tripleDivisorWeight_small (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : OuterTriple,
      γ.q0 ≠ 0 → γ.quotient ≠ 0 → γ.residual ≠ 0 →
      tripleDivisorWeight K γ ≤
        C*((Ideal.absNorm γ.q0 : ℝ)*Ideal.absNorm γ.quotient*Ideal.absNorm γ.residual)^ε := by
  obtain ⟨Cq,hCq,hq⟩ := ideal_divisor_power_small (5+2*K) ε hε
  obtain ⟨Ct,hCt,ht⟩ := ideal_divisor_power_small (2*K) ε hε
  refine ⟨Cq*Ct*Ct, by positivity, ?_⟩
  intro γ hq0 ht0 hr0
  unfold tripleDivisorWeight
  calc
    _ ≤ (Cq*(Ideal.absNorm γ.q0 : ℝ)^ε) *
        (Ct*(Ideal.absNorm γ.quotient : ℝ)^ε) *
        (Ct*(Ideal.absNorm γ.residual : ℝ)^ε) := by
      gcongr
      · exact hq γ.q0 hq0
      · exact ht γ.quotient ht0
      · exact ht γ.residual hr0
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0 ≤ (Ideal.absNorm γ.q0 : ℝ)*Ideal.absNorm γ.quotient)
        (by positivity), Real.mul_rpow (by positivity) (by positivity)]
      ring

theorem outerTriple_card (Γ : Finset OuterTriple) (B T R : ℝ)
    (hB : 1 ≤ B) (hT : 1 ≤ T) (hR : 1 ≤ R)
    (hzero : ∀ γ ∈ Γ, γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0)
    (hnorm : ∀ γ ∈ Γ, (Ideal.absNorm γ.q0 : ℝ) ≤ B ∧
      (Ideal.absNorm γ.quotient : ℝ) ≤ T ∧ (Ideal.absNorm γ.residual : ℝ) ≤ R) :
    (Γ.card : ℝ) ≤ (diagonalControl sieveCutoff+1)^3*B*T*R := by
  let f : OuterTriple → Ideal Eis × Ideal Eis × Ideal Eis := fun γ => (γ.q0,γ.quotient,γ.residual)
  have hf : Function.Injective f := by
    intro γ δ h
    exact OuterTriple.ext (congrArg Prod.fst h)
      (congrArg (fun z => z.2.1) h) (congrArg (fun z => z.2.2) h)
  have hc := SecondPassArithmetic.fixed_triple_count (Γ.image f) B T R hB hT hR
    (fun x hx => by obtain ⟨γ,hγ,rfl⟩ := Finset.mem_image.mp hx; exact hnorm γ hγ)
  have hbase : (Γ.card:ℝ) ≤ (diagonalControl sieveCutoff)^3*B*T*R := by
    simpa only [Finset.card_image_of_injective _ hf] using hc
  have hd := diagonalControl_nonneg sieveCutoff
  apply hbase.trans
  gcongr
  linarith

theorem triple_normalized_mass (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Γ : Finset OuterTriple) (B T R : ℝ),
      1 ≤ B → 1 ≤ T → 1 ≤ R →
      (∀ γ ∈ Γ, γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0) →
      (∀ γ ∈ Γ, (Ideal.absNorm γ.q0 : ℝ) ≤ B ∧
        (Ideal.absNorm γ.quotient : ℝ) ≤ T ∧ (Ideal.absNorm γ.residual : ℝ) ≤ R) →
      (B*T*R)⁻¹ * (∑ γ ∈ Γ, tripleDivisorWeight K γ) ≤ C*(B*T*R)^ε := by
  obtain ⟨C,hC,hb⟩ := tripleDivisorWeight_small K ε hε
  have hd := diagonalControl_nonneg sieveCutoff
  refine ⟨(diagonalControl sieveCutoff+1)^3*C, by positivity, ?_⟩
  intro Γ B T R hB hT hR hz hn
  have hpos : 0 < B*T*R := by positivity
  have hw : ∀ γ ∈ Γ, tripleDivisorWeight K γ ≤ C*(B*T*R)^ε := by
    intro γ hγ
    obtain ⟨hq,ht,hr⟩ := hz γ hγ
    apply (hb γ hq ht hr).trans
    gcongr
    · exact (hn γ hγ).1
    · exact (hn γ hγ).2.1
    · exact (hn γ hγ).2.2
  have hs : (∑ γ ∈ Γ, tripleDivisorWeight K γ) ≤
      ((diagonalControl sieveCutoff+1)^3*B*T*R)*(C*(B*T*R)^ε) := by
    calc
      _ ≤ ∑ _γ ∈ Γ, C*(B*T*R)^ε := Finset.sum_le_sum hw
      _ = (Γ.card : ℝ)*(C*(B*T*R)^ε) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (outerTriple_card Γ B T R hB hT hR hz hn) (by positivity)
  apply (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hpos.le)).trans_eq
  field_simp

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open Eisenstein SchwartzPlanePoisson InverseSecondFibers CompletedGauss
noncomputable section
local notation "Eis" => Eisenstein.O

def secondLabelEnergy (K : ℕ) (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (F : SecondChild → ℂ) (γ : OuterTriple) : ℝ :=
  ∑ f ∈ labels, ((idealDivisors f).card : ℝ)^(9+4*K) *
    ∑ k ∈ rows, ‖F (γ,f,k)‖^2

lemma secondLabelEnergy_nonneg (K : ℕ) (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (F : SecondChild → ℂ) (γ : OuterTriple) : 0 ≤ secondLabelEnergy K labels rows F γ := by
  unfold secondLabelEnergy; positivity

theorem second_weighted_count {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset InverseInitialFibers.PrimeIdeal)
    (newLists : Fin Jn → Finset InverseInitialFibers.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop)
    (hvalid : ∀ x ∈ originalSource source oldLists newLists keep,
      Valid x (secondChild x).1 (secondChild x).2.1 (secondChild x).2.2)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hf : ∀ f ∈ labels, f ≠ 0)
    (houter : ∀ γ ∈ sourceTriples source oldLists newLists keep,
      γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0)
    (hchild : ∀ x ∈ originalSource source oldLists newLists keep,
      (secondChild x).2.1 ∈ labels ∧ (secondChild x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : SecondTuple Jo Jn → ℂ)
    (hw : ∀ x ∈ originalSource source oldLists newLists keep, ‖w x‖ ≤ 1)
    (F G : SecondChild → ℂ) :
    ‖∑ x ∈ originalSource source oldLists newLists keep,
      w x * F (secondChild x) * star (G (secondChild x))‖ ≤
      Real.sqrt (∑ γ ∈ sourceTriples source oldLists newLists keep,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows F γ) *
      Real.sqrt (∑ γ ∈ sourceTriples source oldLists newLists keep,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows G γ) := by
  have hF := second_energy_projection source oldLists newLists keep hvalid labels rows hf houter hchild
    K ho hn (fun x => ‖w x‖) hw F
  have hG := second_energy_projection source oldLists newLists keep hvalid labels rows hf houter hchild
    K ho hn (fun x => ‖w x‖) hw G
  apply (DescentWeightedCauchy.weighted_cauchy (originalSource source oldLists newLists keep)
    w (F ∘ secondChild) (G ∘ secondChild)).trans
  exact mul_le_mul (Real.sqrt_le_sqrt hF) (Real.sqrt_le_sqrt hG)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem second_weighted_count_of_child_bound {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset InverseInitialFibers.PrimeIdeal)
    (newLists : Fin Jn → Finset InverseInitialFibers.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop)
    (hvalid : ∀ x ∈ originalSource source oldLists newLists keep,
      Valid x (secondChild x).1 (secondChild x).2.1 (secondChild x).2.2)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hf : ∀ f ∈ labels, f ≠ 0)
    (houter : ∀ γ ∈ sourceTriples source oldLists newLists keep,
      γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0)
    (hchild : ∀ x ∈ originalSource source oldLists newLists keep,
      (secondChild x).2.1 ∈ labels ∧ (secondChild x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : SecondTuple Jo Jn → ℂ)
    (hw : ∀ x ∈ originalSource source oldLists newLists keep, ‖w x‖ ≤ 1)
    (F G : SecondChild → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hF : ∀ γ ∈ sourceTriples source oldLists newLists keep, secondLabelEnergy K labels rows F γ ≤ E)
    (hG : ∀ γ ∈ sourceTriples source oldLists newLists keep, secondLabelEnergy K labels rows G γ ≤ E) :
    ‖∑ x ∈ originalSource source oldLists newLists keep,
      w x * F (secondChild x) * star (G (secondChild x))‖ ≤
      E * ∑ γ ∈ sourceTriples source oldLists newLists keep, tripleDivisorWeight K γ := by
  have hb (P : SecondChild → ℂ)
      (hP : ∀ γ ∈ sourceTriples source oldLists newLists keep, secondLabelEnergy K labels rows P γ ≤ E) :
      (∑ γ ∈ sourceTriples source oldLists newLists keep,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows P γ) ≤
      E * ∑ γ ∈ sourceTriples source oldLists newLists keep, tripleDivisorWeight K γ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro γ hγ
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hP γ hγ) (tripleDivisorWeight_nonneg K γ)
  apply (second_weighted_count source oldLists newLists keep hvalid labels rows hf houter hchild K ho hn w hw F G).trans
  calc
    _ ≤ Real.sqrt (E * ∑ γ ∈ sourceTriples source oldLists newLists keep, tripleDivisorWeight K γ) *
      Real.sqrt (E * ∑ γ ∈ sourceTriples source oldLists newLists keep, tripleDivisorWeight K γ) :=
      mul_le_mul (Real.sqrt_le_sqrt (hb F hF)) (Real.sqrt_le_sqrt (hb G hG))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := Real.mul_self_sqrt (mul_nonneg hE (Finset.sum_nonneg (fun γ _ => tripleDivisorWeight_nonneg K γ)))

def secondCanonicalPolynomial {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (pool : Finset ι) (Ψ : OuterTriple → Eis →* ℂ) (puncture : OuterTriple → Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : OuterTriple → ℝ → ℂ) (X : ℝ) (c : SecondChild) : ℂ :=
  finiteCanonicalMarkedRow p hg pool (Ψ c.1) (puncture c.1)
    (primaryIdealGenerator c.2.1) c.2.2 slots lists a (W c.1) X


end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open Eisenstein FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open Eisenstein SchwartzPlanePoisson InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_ne_zero)
noncomputable section
local notation "Eis" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  [∀ i, (Ideal.span {p i}).IsMaximal]

def actualSecondChild {Jo Jn : ℕ} (u v : Eisˣ) (x : MarkedSecondSource ι Jo Jn) : SecondChild :=
  secondChild (originalSecondTuple p u v (markedSecondOriginal p x))

def actualSecondTriples {Jo Jn : ℕ} (u v : Eisˣ)
    (source : Finset (MarkedSecondSource ι Jo Jn)) : Finset OuterTriple :=
  source.image (fun x => (actualSecondChild p u v x).1)

theorem actualSecondChild_nonzero (hp : ∀ i, p i ≠ 0)
    {Jo Jn : ℕ} (u v : Eisˣ) (x : MarkedSecondSource ι Jo Jn) (ht : x.quotient ≠ 0) :
    (actualSecondChild p u v x).2.1 ≠ 0 ∧
    (actualSecondChild p u v x).1.q0 ≠ 0 ∧
    (actualSecondChild p u v x).1.quotient ≠ 0 ∧
    (actualSecondChild p u v x).1.residual ≠ 0 := by
  have hj : Ideal.span {jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit} ≠ (0 : Ideal Eis) :=
    Ideal.span_singleton_eq_bot.not.mpr (primeProduct_ne_zero p hp _ _)
  have hb : Ideal.span {b0Label p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit} ≠ (0 : Ideal Eis) :=
    Ideal.span_singleton_eq_bot.not.mpr (primeProduct_ne_zero p hp _ _)
  change _ ≠ 0 ∧ _ ≠ 0 ∧ x.quotient ≠ 0 ∧ _ ≠ 0
  refine ⟨?_,hb,ht,sourceIdeal_ne_zero p hp _⟩
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hj (sourceIdeal_ne_zero p hp _))
    (sourceIdeal_ne_zero p hp _)) (sourceIdeal_ne_zero p hp _)

structure ActualSecondSourceConditions {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) : Prop where
  admissible : ∀ x ∈ source, x.cube.Admissible
  common_disjoint : ∀ x ∈ source, Disjoint x.firstCommon x.cube.support
  first_divisor : ∀ x ∈ source, x.firstDivisor ⊆ x.firstCommon∪x.cube.support
  second_divisor : ∀ x ∈ source, x.second.divisor ⊆ x.second.sourceCommon
  old_support : ∀ x ∈ source, ∀ i, (x.oldAssigned i).val ∣
      sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*x.quotient
  new_support : ∀ x ∈ source, ∀ i, x.newAssigned i ∈ x.second.sourceCommon∪x.second.overlap
  quotient_nonzero : ∀ x ∈ source, x.quotient ≠ 0

theorem actual_second_fiber_weight (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (c : SecondChild)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : MarkedSecondSource ι Jo Jn → ℝ) (hw : ∀ x ∈ source, w x ≤ 1) :
    ∑ x ∈ source with actualSecondChild p u v x = c, w x ≤ secondDivisorWeight K c := by
  by_cases he : (source.filter (fun x => actualSecondChild p u v x = c)).Nonempty
  · obtain ⟨x,hx⟩ := he
    obtain ⟨hx,he⟩ := Finset.mem_filter.mp hx
    obtain ⟨hf,hq,ht,hr⟩ := actualSecondChild_nonzero p hp u v x (hs.quotient_nonzero x hx)
    rw [he] at hf hq ht hr
    have hcard := actual_marked_second_source_fiber p hp hpr hcop hinj u v source
      hs.admissible hs.common_disjoint hs.first_divisor hs.second_divisor hs.old_support hs.new_support
      c.1 c.2.1 c.2.2 hf hq ht hr K ho hn
    calc
      _ ≤ ∑ _x ∈ source with actualSecondChild p u v _x = c, (1 : ℝ) :=
        Finset.sum_le_sum (fun x hx => hw x (Finset.mem_filter.mp hx).1)
      _ = ((source.filter (fun x => actualSecondChild p u v x = c)).card : ℝ) := by simp
      _ ≤ _ := by
        dsimp only [secondDivisorWeight,actualSecondChild]
        exact_mod_cast hcard
  · rw [Finset.not_nonempty_iff_eq_empty.mp he]
    simp only [Finset.sum_empty]
    unfold secondDivisorWeight
    positivity

theorem actual_second_energy_projection (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : MarkedSecondSource ι Jo Jn → ℝ) (hw : ∀ x ∈ source, w x ≤ 1) (F : SecondChild → ℂ) :
    ∑ x ∈ source, w x * ‖F (actualSecondChild p u v x)‖^2 ≤
      ∑ γ ∈ actualSecondTriples p u v source,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows F γ := by
  have hm : ∀ x ∈ source, actualSecondChild p u v x ∈
      actualSecondTriples p u v source ×ˢ (labels ×ˢ rows) := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x,hx,rfl⟩,Finset.mem_product.mpr (hchild x hx)⟩
  have hb := fiber_energy_bound source (actualSecondTriples p u v source ×ˢ (labels ×ˢ rows))
    (actualSecondChild p u v) w (secondDivisorWeight K) (fun c => ‖F c‖^2) hm
    (fun _ _ => sq_nonneg _) (fun c _ => actual_second_fiber_weight p hp hpr hcop hinj u v source hs c K ho hn w hw)
  apply hb.trans_eq
  simp only [Finset.sum_product,secondDivisorWeight,tripleDivisorWeight,secondLabelEnergy,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem actual_second_weighted_count (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : MarkedSecondSource ι Jo Jn → ℂ) (hw : ∀ x ∈ source, ‖w x‖ ≤ 1)
    (F G : SecondChild → ℂ) :
    ‖∑ x ∈ source, w x * F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v source,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows F γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v source,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows G γ) := by
  apply (DescentWeightedCauchy.weighted_cauchy source w (F ∘ actualSecondChild p u v)
    (G ∘ actualSecondChild p u v)).trans
  exact mul_le_mul
    (Real.sqrt_le_sqrt (actual_second_energy_projection p hp hpr hcop hinj u v source hs labels rows hchild K ho hn (fun x => ‖w x‖) hw F))
    (Real.sqrt_le_sqrt (actual_second_energy_projection p hp hpr hcop hinj u v source hs labels rows hchild K ho hn (fun x => ‖w x‖) hw G))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end
end InverseMoment

namespace InverseMoment
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseInitialRayAttachment
open scoped BigOperators Classical
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})

/-- The child kernel with both column tests absorbed into its two-conductor kernel. -/
def secondChildKernelPair (F V:Finset ι) (Ψ₁ Ψ₂:O→*ℂ)
    (m r c d e k₁ k₂:O) (K:Finset ι→Finset ι→ℂ) : ℂ :=
  ∑ N∈(F\V).powerset, ∑ M∈(F\V).powerset,
    star (secondChildColumn p hg Ψ₁ (m*r) (c*e*∏i∈V,p i) (d*e*k₁) (fun _=>1) N)*
    secondChildColumn p hg Ψ₂ (m*r) (c*e*∏i∈V,p i) (d*e*k₂) (fun _=>1) M*K (V∪N) (V∪M)

/-- Character expansion of the full reflection weight, followed by overlap extraction. -/
def secondTotalWeight (Ψ₁ Ψ₂:O→*ℂ) (m r c d e k:O) (z:SecondRayIndex×Finset ι) : ℂ :=
  secondRayCoefficient z.1 * secondCommonWeight p hg
    (secondRayMinus Ψ₁ z.1) (secondRayPlus Ψ₂ z.1) m r c d e k (-k) z.2

theorem secondActualPair_character_children (hp : ∀i,p i≠0)
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2) (hpr : ∀i,lambda^2∣p i-1)
    (F:Finset ι) (Ψ₁ Ψ₂:O→*ℂ) (m r c d e k:O) (H₁ H₂:Finset ι→ℂ) :
    secondActualPair p hp hg F Ψ₁ Ψ₂ m r c d e k H₁ H₂ =
      ∑ z:SecondRayIndex, ∑ V∈F.powerset,
        secondTotalWeight p hg Ψ₁ Ψ₂ m r c d e k (z,V) *
        star (secondChildSum p hg F V (secondRayMinus Ψ₁ z) m r c d e k H₁) *
        secondChildSum p hg F V (secondRayPlus Ψ₂ z) m r c d e (-k) H₂ := by
  have hcop : Pairwise (Function.onFun IsCoprime p) := fun i j hij=>
    (Ideal.isCoprime_span_singleton_iff _ _).mp (Ideal.isCoprime_of_isMaximal (hinj.ne hij))
  have hex (S T:Finset ι) :
      (if Disjoint S T then
        star (supportMobius S*secondInputCoefficient p
          (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) Ψ₁ (m*(e*r)) c d H₁ S)*
        (supportMobius T*secondInputCoefficient p
          (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) Ψ₂ (m*(e*r)) c d H₂ T)*
        secondNormalizedGaussTerm p hp hg S T e k else 0) =
      ∑ z:SecondRayIndex, secondRayCoefficient z *
        (if Disjoint S T then
          star (secondPreColumn p hg (secondRayMinus Ψ₁ z) (m*(e*r)) c d e k H₁ S)*
          secondPreColumn p hg (secondRayPlus Ψ₂ z) (m*(e*r)) c d e (-k) H₂ T else 0) := by
    by_cases hd:Disjoint S T
    · simpa only [if_pos hd,mul_assoc] using
        initial_gauss_ray_expansion p hp hg hinj hc hpr Ψ₁ Ψ₂ (m*(e*r)) c d e k H₁ H₂ S T hd
    · simp only [if_neg hd,mul_zero,Finset.sum_const_zero]
  have hseparated : secondActualPair p hp hg F Ψ₁ Ψ₂ m r c d e k H₁ H₂ =
      ∑ z:SecondRayIndex, secondRayCoefficient z *
        SecondPassArithmetic.secondSeparatedPair p hg F (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
          m r c d e k (-k) H₁ H₂ := by
    unfold secondActualPair
    simp_rw [hex]
    conv_lhs => arg 2; ext S; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    simp only [SecondPassArithmetic.secondSeparatedPair,Finset.mul_sum]
  rw [hseparated]
  simp only [secondSeparatedPair_eq_children p hg hp hcop hpr,Finset.mul_sum,
    secondTotalWeight,mul_assoc]

def canonicalMarkedSplit (F V A:Finset ι) (Ψ:O→*ℂ) (m r c d e k:O)
    (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ) (W:ℝ→ℂ) (X:ℝ) : ℂ :=
  ∑ J∈slots.powerset,primeMark J lists a (A∪V)*
    finiteCanonicalMarkedRow p hg F Ψ (m*r) (c*e*∏i∈V,p i) (d*e*k)
      (slots\J) (fun i=>lists i\A) a W (X/primeProductNorm p V)

theorem secondActualPair_marked_children (hp : ∀i,p i≠0)
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2) (hpr : ∀i,lambda^2∣p i-1)
    (F A₁ A₂:Finset ι) (Ψ₁ Ψ₂:O→*ℂ) (m r c d e k:O)
    (slots₁ slots₂:Finset σ) (lists₁ lists₂:σ→Finset ι) (a₁ a₂:σ→ι→ℂ)
    (W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ) :
    secondActualPair p hp hg F Ψ₁ Ψ₂ m r c d e k
      (fun U=>primeMark slots₁ lists₁ a₁ (A₁∪U)*W₁ (primeProductNorm p U/X₁))
      (fun U=>primeMark slots₂ lists₂ a₂ (A₂∪U)*W₂ (primeProductNorm p U/X₂)) =
      ∑ z:SecondRayIndex, ∑ V∈F.powerset,
        secondTotalWeight p hg Ψ₁ Ψ₂ m r c d e k (z,V)*
        star (canonicalMarkedSplit p hg F V A₁ (secondRayMinus Ψ₁ z) m r c d e k slots₁ lists₁ a₁ W₁ X₁)*
        canonicalMarkedSplit p hg F V A₂ (secondRayPlus Ψ₂ z) m r c d e (-k) slots₂ lists₂ a₂ W₂ X₂ := by
  rw [secondActualPair_character_children p hg hp hinj hc hpr]
  simp only [secondChildSum_marked_fixed_pool,canonicalMarkedSplit]
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
noncomputable section
local notation "Eis" => Eisenstein.O

lemma secondSourcePairKernel_mark_factors {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (e k : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (A₁ A₂ : Finset ι) (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ,ℂ)) (Y : ℝ) (S T : Finset ι) :
    secondSourcePairKernel p e k
      (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ U)*H₁ U)
      (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ U)*H₂ U) W Y S T =
      star (primeMark slots₁ lists₁ a₁ (A₁ ∪ S)) * primeMark slots₂ lists₂ a₂ (A₂ ∪ T) *
        secondSourcePairKernel p e k H₁ H₂ W Y S T := by
  simp only [secondSourcePairKernel,star_mul]
  ring

theorem secondChildKernelPair_whole_profile {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F G V A₁ A₂ : Finset ι) (Ψ₁ Ψ₂ : Eis →* ℂ) (m r c d e k : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    (‖ringComplex e‖^2 : ℂ)⁻¹ * secondChildKernelPair p hg F V Ψ₁ Ψ₂
      m r c d e k (-k)
      (secondSourcePairKernel p e k
        (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ U)*W₁ (primeProductNorm p G*primeProductNorm p U))
        (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ U)*W₂ (primeProductNorm p G*primeProductNorm p U)) Φ Y) =
    ∑ N ∈ (F \ V).powerset, ∑ M ∈ (F \ V).powerset,
      (star (secondChildColumn p hg Ψ₁ (m*r) (c*e*∏ i ∈ V,p i)
        (d*e*k) (fun _ => 1) N) *
        secondChildColumn p hg Ψ₂ (m*r) (c*e*∏ i ∈ V,p i)
          (d*e*(-k)) (fun _ => 1) M) *
      (star (primeMark slots₁ lists₁ a₁ (A₁ ∪ (V ∪ N))) *
        primeMark slots₂ lists₂ a₂ (A₂ ∪ (V ∪ M))) *
      secondNormProfile (fun x => star (W₁ x)) W₂ Φ (fun _ _ => 1) Y
        ![primeProductNorm p G,‖ringComplex e‖^2,primeProductNorm p V,
          ‖ringComplex k‖^2,primeProductNorm p N,primeProductNorm p M] := by
  unfold secondChildKernelPair
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  have hVN : Disjoint V N := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hN) disjoint_sdiff_self_right
  have hVM : Disjoint V M := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hM) disjoint_sdiff_self_right
  rw [secondSourcePairKernel_mark_factors]
  have hp := secondSourcePairKernel_profile p hp G V N M hVN hVM e k W₁ W₂ Φ Y
  rw [← hp]
  ring

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
noncomputable section
local notation "Eis" => Eisenstein.O

structure SecondProfileData (ι : Type*) where
  common : Finset ι
  overlap : Finset ι
  extractedLeft : Finset ι
  extractedRight : Finset ι
  rayLeft : Eis →* ℂ
  rayRight : Eis →* ℂ
  puncture : Eis
  quotient : Eis
  oldLabel : Eis
  oldDivisor : Eis
  divisor : Eis
  frequency : Eis

def secondActualNorms {ι : Type*} (p : ι → Eis) (x : SecondProfileData ι)
    (N M : Finset ι) : Fin 6 → ℝ :=
  ![primeProductNorm p x.common, ‖ringComplex x.divisor‖^2,
    primeProductNorm p x.overlap, ‖ringComplex x.frequency‖^2,
    primeProductNorm p N, primeProductNorm p M]

lemma secondActualNorms_pos {ι : Type*} (p : ι → Eis) (hp : ∀ i, p i ≠ 0)
    (x : SecondProfileData ι) (he : x.divisor ≠ 0) (hk : x.frequency ≠ 0) (N M : Finset ι) :
    ∀ i, 0 < secondActualNorms p x N M i := by
  intro i
  fin_cases i
  · exact primeProductNorm_pos p hp x.common
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero he))
  · exact primeProductNorm_pos p hp x.overlap
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero hk))
  · exact primeProductNorm_pos p hp N
  · exact primeProductNorm_pos p hp M

def secondActualCoefficient {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
    (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ) (N M : Finset ι) : ℂ :=
  star (secondChildColumn p hg x.rayLeft (x.puncture*x.quotient)
    (x.oldLabel*x.divisor*∏ i ∈ x.overlap,p i) (x.oldDivisor*x.divisor*x.frequency) (fun _ => 1) N) *
  secondChildColumn p hg x.rayRight (x.puncture*x.quotient)
    (x.oldLabel*x.divisor*∏ i ∈ x.overlap,p i) (x.oldDivisor*x.divisor*(-x.frequency)) (fun _ => 1) M *
  (star (primeMark slots₁ lists₁ a₁ (x.extractedLeft ∪ (x.overlap ∪ N))) *
    primeMark slots₂ lists₂ a₂ (x.extractedRight ∪ (x.overlap ∪ M)))

def actualSecondProfileRow {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
    (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y X : ℝ) : ℂ :=
  (‖ringComplex x.divisor‖^2 : ℂ)⁻¹ *
  secondChildKernelPair p hg F x.overlap x.rayLeft x.rayRight x.puncture x.quotient
    x.oldLabel x.oldDivisor x.divisor x.frequency (-x.frequency)
    (secondSourcePairKernel p x.divisor x.frequency
      (fun U => primeMark slots₁ lists₁ a₁ (x.extractedLeft ∪ U)*
        W₁ (primeProductNorm p x.common*primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ (x.extractedRight ∪ U)*
        W₂ (primeProductNorm p x.common*primeProductNorm p U/X)) Φ Y)

theorem actualSecondProfileRow_eq_whole {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
    (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y X : ℝ) :
    actualSecondProfileRow p hg F x slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X =
      ∑ N ∈ (F \ x.overlap).powerset, ∑ M ∈ (F \ x.overlap).powerset,
        secondActualCoefficient p hg x slots₁ slots₂ lists₁ lists₂ a₁ a₂ N M *
          secondNormProfile (fun z => star (W₁ (z/X))) (fun z => W₂ (z/X)) Φ (fun _ _ => 1) Y
            (secondActualNorms p x N M) :=
  secondChildKernelPair_whole_profile p hp hg F x.common x.overlap x.extractedLeft x.extractedRight
    x.rayLeft x.rayRight x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor x.frequency
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ (fun z => W₁ (z/X)) (fun z => W₂ (z/X)) Φ Y

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory JointLogSeparation
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => Eisenstein.O

def secondProfileIndices {κ ι : Type*} [DecidableEq ι]
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) :
    Finset (Σ _ : κ, Finset ι × Finset ι) :=
  source.sigma (fun j => (F \ (x j).overlap).powerset ×ˢ (F \ (x j).overlap).powerset)

lemma mem_secondProfileIndices {κ ι : Type*} [DecidableEq ι]
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι)
    (j : Σ _ : κ, Finset ι × Finset ι) : j ∈ secondProfileIndices source F x ↔
      j.1 ∈ source ∧ j.2.1 ∈ (F \ (x j.1).overlap).powerset ∧
        j.2.2 ∈ (F \ (x j.1).overlap).powerset := by
  simp only [secondProfileIndices,Finset.mem_sigma,Finset.mem_product]

theorem actualSecondProfileRows_eq_indexed {κ ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y X : ℝ) :
    (∑ j ∈ source, w j * actualSecondProfileRow p hg F (x j)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X) =
    ∑ j ∈ secondProfileIndices source F x,
      (w j.1 * secondActualCoefficient p hg (x j.1)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ j.2.1 j.2.2) *
      secondNormProfile (fun z => star (W₁ (z/X))) (fun z => W₂ (z/X)) Φ (fun _ _ => 1) Y
        (secondActualNorms p (x j.1) j.2.1 j.2.2) := by
  simp only [actualSecondProfileRow_eq_whole p hp hg,secondProfileIndices,Finset.sum_sigma,
    Finset.sum_product,Finset.mul_sum,mul_assoc]

theorem actualSecondProfileRows_integral {κ ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y G₀ E₀ V₀ K₀ X₀ : ℝ)
    (g : Fin 6 → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ))
    (he : ∀ j ∈ secondProfileIndices source F x,
      secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
        (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (secondActualNorms p (x j.1) j.2.1 j.2.2) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : Fin 6 → ℝ,
          fullProfileDensity g b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
            (∏ i, kernelLogPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope
              (t₁,t₂,t₃) u i) (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2)
                G₀ E₀ V₀ K₀ X₀ i))) :
    (∑ j ∈ source, w j * actualSecondProfileRow p hg F (x j)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ v : Frequency × (Fin 6 → ℝ),
        fullProfileDensity g b₁ b₂ b₃ v *
          ∑ j ∈ secondProfileIndices source F x,
            (w j.1 * secondActualCoefficient p hg (x j.1)
              slots₁ slots₂ lists₁ lists₂ a₁ a₂ j.2.1 j.2.2) *
            pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
              (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2 := by
  rw [actualSecondProfileRows_eq_indexed p hp hg]
  rw [← full_density_finite_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [he j hj, full_density_mode_fubini]
  simp only [pureProfileMode_height]
  ring

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory JointLogSeparation
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => Eisenstein.O
universe u v w

def ActualSecondCommonMeasureAt (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 6 → ℝ → ℂ) (hV : ∀ i, ContDiff ℝ ∞ (V i))
    (hS : ∀ i, HasCompactSupport (V i))
    (G₀ E₀ V₀ K₀ X₀ Y : ℝ) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ)) : Prop :=
  ∀ {κ : Type u} {ι : Type v} {σ : Type w} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (weight : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ),
    (∀ j ∈ source, (x j).divisor ≠ 0 ∧ (x j).frequency ≠ 0) →
    (∀ j ∈ secondProfileIndices source F x, ∀ i,
      V i (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀ i) = 1) →
    (∑ j ∈ source, weight j * actualSecondProfileRow p hg F (x j)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ z : Frequency × (Fin 6 → ℝ),
        fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ z *
          ∑ j ∈ secondProfileIndices source F x,
            (weight j.1 * secondActualCoefficient p hg (x j.1)
              slots₁ slots₂ lists₁ lists₂ a₁ a₂ j.2.1 j.2.2) *
            pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
              (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) z.1 z.2

theorem actual_second_uniform_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ G₀ E₀ V₀ K₀ X₀ Y : ℝ,
      0 < G₀ → 0 < E₀ → 0 < V₀ → 0 < K₀ → 0 < X₀ → 0 < Y →
      ∃ b₃ : 𝓢(ℝ, ℂ),
      ActualSecondCommonMeasureAt.{u,v,w} W₁ W₂ Φ V hV hS G₀ E₀ V₀ K₀ X₀ Y b₁ b₂ b₃ ∧
      Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ∧
      (1 + Y*K₀/(E₀*V₀^2*X₀^2))^A * (∫ p : Frequency × (Fin 6 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ≤ C := by
  have hstar : ContDiff ℝ ∞ (fun t => star (W₁ t)) := Complex.conjCLE.contDiff.comp hW₁
  have hsstar : Function.support (fun t => star (W₁ t)) ⊆ Set.Icc a b := by
    intro t ht
    apply hs₁
    simpa only [Function.mem_support,star_ne_zero] using ht
  obtain ⟨b₁,b₂,C,hC,hsep⟩ := second_norm_kernel_common_measure
    (fun t => star (W₁ t)) W₂ a b ha hsstar hs₂ hstar hW₂ Φ V M hV hS hM hbox A J
  refine ⟨b₁,b₂,C,hC,?_⟩
  intro G₀ E₀ V₀ K₀ X₀ Y hG hE hV₀ hK hX hY
  obtain ⟨b₃,he,hi,hbound⟩ := hsep G₀ E₀ V₀ K₀ X₀ Y hG hE hV₀ hK hX hY
  refine ⟨b₃,?_,hi,hbound⟩
  intro κ ι σ _ _ p hp _ hcop hg source F x weight slots₁ slots₂ lists₁ lists₂ a₁ a₂ hn hcut
  apply actualSecondProfileRows_integral p hp hg source F x weight
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y G₀ E₀ V₀ K₀ X₀
    (secondRootSchwartz V hV hS) b₁ b₂ b₃
  intro j hj
  have hj0 := (mem_secondProfileIndices source F x j).mp hj
  exact he (secondActualNorms p (x j.1) j.2.1 j.2.2)
    (secondActualNorms_pos p hp (x j.1) (hn j.1 hj0.1).1 (hn j.1 hj0.1).2 j.2.1 j.2.2)
    (hcut j hj)

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => Eisenstein.O

theorem secondChildKernelPair_insert_fresh {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F V : Finset ι) (Ψ₁ Ψ₂ : Eis →* ℂ) (m r c d e k₁ k₂ : Eis)
    (K : Finset ι → Finset ι → ℂ) (ω₁ ω₂ : Finset ι → ℂ)
    (hω : ∀ N ∈ (F \ V).powerset, ∀ M ∈ (F \ V).powerset,
      K (V ∪ N) (V ∪ M) ≠ 0 → ω₁ (V ∪ N) = 1 ∧ ω₂ (V ∪ M) = 1) :
    secondChildKernelPair p hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ K =
    secondChildKernelPair p hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂
      (fun S T => star (ω₁ S)*ω₂ T*K S T) := by
  unfold secondChildKernelPair
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  by_cases hK : K (V ∪ N) (V ∪ M) = 0
  · simp only [hK,mul_zero]
  · obtain ⟨h1,h2⟩ := hω N hN M hM hK
    simp only [h1,h2,star_one,one_mul]

theorem secondChildKernelPair_separated_marked {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F V A₁ A₂ : Finset ι) (Ψ₁ Ψ₂ : Eis →* ℂ) (m r c d e k₁ k₂ : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) :
    secondChildKernelPair p hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂
      (fun S T => star (primeMark slots₁ lists₁ a₁ (A₁ ∪ S)*W₁ (primeProductNorm p S/X₁)) *
        (primeMark slots₂ lists₂ a₂ (A₂ ∪ T)*W₂ (primeProductNorm p T/X₂))) =
      star (canonicalMarkedSplit p hg F V A₁ Ψ₁ m r c d e k₁ slots₁ lists₁ a₁ W₁ X₁) *
        canonicalMarkedSplit p hg F V A₂ Ψ₂ m r c d e k₂ slots₂ lists₂ a₂ W₂ X₂ := by
  have hs (Ψ : Eis →* ℂ) (A : Finset ι) (k : Eis) (slots : Finset σ)
      (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) :=
    secondChildSum_marked_fixed_pool p hg F V A Ψ m r c d e k slots lists a W X
  calc
    _ = star (secondChildSum p hg F V Ψ₁ m r c d e k₁
        (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ U)*W₁ (primeProductNorm p U/X₁))) *
        secondChildSum p hg F V Ψ₂ m r c d e k₂
        (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ U)*W₂ (primeProductNorm p U/X₂)) := by
      unfold secondChildKernelPair secondChildSum
      rw [star_sum, Finset.sum_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N hN
      apply Finset.sum_congr rfl
      intro M hM
      simp only [secondChildColumn,star_mul,mul_one]
      ring
    _ = _ := congrArg₂ (· * ·)
      (congrArg star (hs Ψ₁ A₁ k₁ slots₁ lists₁ a₁ W₁ X₁))
      (hs Ψ₂ A₂ k₂ slots₂ lists₂ a₂ W₂ X₂)

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open JointLogSeparation Eisenstein FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => Eisenstein.O

theorem actual_second_columns_separated {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
    (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (X : ℝ) (h₁ h₂ : ℝ) :
    (∑ N ∈ (F \ x.overlap).powerset, ∑ M ∈ (F \ x.overlap).powerset,
      secondActualCoefficient p hg x slots₁ slots₂ lists₁ lists₂ a₁ a₂ N M *
        (star (ω₁ (primeProductNorm p N/X)) * ω₂ (primeProductNorm p M/X)) *
        kernelLogPhase h₁ (Real.log (primeProductNorm p N/X)) *
        kernelLogPhase h₂ (Real.log (primeProductNorm p M/X))) =
    star (canonicalMarkedSplit p hg F x.overlap x.extractedLeft x.rayLeft
      x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor x.frequency
      slots₁ lists₁ a₁ (childLogTest ω₁ (-h₁)) (primeProductNorm p x.overlap*X)) *
      canonicalMarkedSplit p hg F x.overlap x.extractedRight x.rayRight
      x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor (-x.frequency)
      slots₂ lists₂ a₂ (childLogTest ω₂ h₂) (primeProductNorm p x.overlap*X) := by
  rw [← secondChildKernelPair_separated_marked]
  unfold secondChildKernelPair
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  have hVN : Disjoint x.overlap N := by
    apply Finset.disjoint_left.mpr
    intro i hi hiN
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hN) hiN)).2 hi
  have hVM : Disjoint x.overlap M := by
    apply Finset.disjoint_left.mpr
    intro i hi hiM
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hM) hiM)).2 hi
  dsimp only
  rw [second_fresh_scale p hp x.overlap N hVN,second_fresh_scale p hp x.overlap M hVM]
  simp only [secondActualCoefficient,childLogTest,secondChildColumn,
    star_mul,JointLogSeparation.kernelLogPhase_conjugate,neg_neg,mul_one]
  ring

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory JointLogSeparation Eisenstein FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => Eisenstein.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondSeparatedPair (F : Finset ι) (x : SecondProfileData ι)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ : ℝ) (v : Frequency × (Fin 6 → ℝ)) : ℂ :=
  let h := profileHeight secondLeftSlope secondRightSlope secondKernelSlope v.1 v.2
  secondOuterPhase h
    (secondRelativeLog (secondActualNorms p x ∅ ∅) G₀ E₀ V₀ K₀ X₀) *
  star (canonicalMarkedSplit p hg F x.overlap x.extractedLeft x.rayLeft
    x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor x.frequency
    slots₁ lists₁ a₁ (childLogTest ω₁ (-h 4)) (primeProductNorm p x.overlap*X₀)) *
  canonicalMarkedSplit p hg F x.overlap x.extractedRight x.rayRight
    x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor (-x.frequency)
    slots₂ lists₂ a₂ (childLogTest ω₂ (h 5)) (primeProductNorm p x.overlap*X₀)

include hp in
theorem actual_second_full_mode_columns (F : Finset ι) (x : SecondProfileData ι)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ : ℝ) (v : Frequency × (Fin 6 → ℝ)) :
    (∑ N ∈ (F \ x.overlap).powerset, ∑ M ∈ (F \ x.overlap).powerset,
      secondActualCoefficient p hg x slots₁ slots₂ lists₁ lists₂ a₁ a₂ N M *
        (star (ω₁ (primeProductNorm p N/X₀)) * ω₂ (primeProductNorm p M/X₀)) *
        pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
          (secondRelativeLog (secondActualNorms p x N M) G₀ E₀ V₀ K₀ X₀) v.1 v.2) =
      secondSeparatedPair p hg F x slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v := by
  let h := profileHeight secondLeftSlope secondRightSlope secondKernelSlope v.1 v.2
  let O := secondOuterPhase h (secondRelativeLog (secondActualNorms p x ∅ ∅) G₀ E₀ V₀ K₀ X₀)
  calc
    _ = O * (∑ N ∈ (F \ x.overlap).powerset, ∑ M ∈ (F \ x.overlap).powerset,
        secondActualCoefficient p hg x slots₁ slots₂ lists₁ lists₂ a₁ a₂ N M *
          (star (ω₁ (primeProductNorm p N/X₀)) * ω₂ (primeProductNorm p M/X₀)) *
          kernelLogPhase (h 4) (Real.log (primeProductNorm p N/X₀)) *
          kernelLogPhase (h 5) (Real.log (primeProductNorm p M/X₀))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N hN
      apply Finset.sum_congr rfl
      intro M hM
      have hm : pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
          (secondRelativeLog (secondActualNorms p x N M) G₀ E₀ V₀ K₀ X₀) v.1 v.2 =
          O * kernelLogPhase (h 4) (Real.log (primeProductNorm p N/X₀)) *
            kernelLogPhase (h 5) (Real.log (primeProductNorm p M/X₀)) := by
        rw [second_mode_split]
        simp [secondOuterPhase,secondRelativeLog,secondRelativeNorm,secondActualNorms,O,h]
      rw [hm]
      ring
    _ = _ := by
      rw [actual_second_columns_separated p hp hg]
      simp only [secondSeparatedPair,h,O,mul_assoc]

include hp in
theorem actualSecondFreshRows_integral {κ : Type*}
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y G₀ E₀ V₀ K₀ X₀ : ℝ)
    (g : Fin 6 → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ))
    (he : ∀ j ∈ secondProfileIndices source F x,
      secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
        (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (secondActualNorms p (x j.1) j.2.1 j.2.2) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
        (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀)) *
        ∫ v : Frequency × (Fin 6 → ℝ), fullProfileDensity g b₁ b₂ b₃ v *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2) :
    (∑ j ∈ source, w j * actualSecondProfileRow p hg F (x j)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ v : Frequency × (Fin 6 → ℝ),
        fullProfileDensity g b₁ b₂ b₃ v *
          ∑ j ∈ source, w j * secondSeparatedPair p hg F (x j)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v := by
  rw [actualSecondProfileRows_eq_indexed p hp hg]
  have hc (v : Frequency × (Fin 6 → ℝ)) :
      (∑ j ∈ source, w j * secondSeparatedPair p hg F (x j)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v) =
      ∑ j ∈ secondProfileIndices source F x,
        ((w j.1 * secondActualCoefficient p hg (x j.1)
          slots₁ slots₂ lists₁ lists₂ a₁ a₂ j.2.1 j.2.2) *
          (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀))) *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2 := by
    simp_rw [← actual_second_full_mode_columns p hp hg]
    simp only [secondProfileIndices,Finset.sum_sigma,Finset.sum_product,Finset.mul_sum,mul_assoc]
  simp_rw [hc]
  rw [← full_density_finite_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [he j hj]
  ring

end
end InverseMoment

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

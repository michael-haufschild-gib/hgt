/-
The inverse raw dictionary adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Inversion.InitialDetectorSources

/-!
# The inverse raw dictionary

Excluded divisors, deleted bases and periods of the raw initial gates; uniform base profiles
and clipped reference windows; physical norms, energies and logarithmic bounds of raw fibers.
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
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory
namespace DetectorDictionaryInverseRawFourier
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge InverseInitialRawDictionary
open InverseMoment InverseInitialClippedColumns InverseInitialOverlapFourier JointLogSeparation

private theorem child_cover (Wref : ℝ→ℂ) (b D : ℝ) (hD : 0< D)
    (hWref : ∀x,Wref x≠0 → x≤ b) (s : ℝ) :
    ∀I : Ideal O,I≠0 → childLogTest Wref s ((I.absNorm:ℝ)/D)≠0 →
      I∈HeckeInverseAmplification.idealsUpTo ⌈D*b⌉₊ := by
  intro I hI hi
  apply finite_source_cover Wref D b hD hWref I hI
  intro hz
  exact hi (by simp [childLogTest,hz])

theorem polynomial_mode_integrable (χ : Character) (inv : Bool)
    (g : 𝓢(ℝ,ℂ)) (Wref : ℝ→ℂ) (b c θ D : ℝ) (hD : 0< D)
    (hWref : ∀x,Wref x≠0 → x≤ b) :
    Integrable (fun v:ℝ=> density g (Real.log c) v*
      polynomial χ inv (childLogTest Wref (θ+v)) D 0 0) := by
  simp_rw [polynomial_eq_finite χ inv (childLogTest Wref (θ+_)) D 0 0
    (HeckeInverseAmplification.idealsUpTo ⌈D*b⌉₊) (child_cover Wref b D hD hWref _)]
  simp only [HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_zero,
    neg_zero,Complex.cpow_zero,mul_one,Finset.mul_sum]
  apply integrable_finsetSum
  intro I hI
  convert fourier_phase_integrable g
    (Real.log c+Real.log ((I.absNorm:ℝ)/D))
    ((D:ℂ)^(-(1/2:ℂ))*HeckeDyadic.coefficient χ inv I*Wref ((I.absNorm:ℝ)/D)*
      kernelLogPhase θ (Real.log ((I.absNorm:ℝ)/D))) using 1 <;> first
  | rfl
  | (funext v; simp only [density,childLogTest,kernelLogPhase_add_frequency,kernelLogPhase_add]; ring)

theorem polynomial_clipped_fourier (χ : Character) (inv : Bool)
    (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0< lo)
    (hs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Wref : ℝ→ℂ) (b c θ D : ℝ) (hc : 0< c) (hD : 0< D)
    (hWref : ∀x,Wref x≠0 → x≤ b)
    (hagree : ∀y,0< y → Wref y*W (c*y)=W (c*y)) :
    polynomial χ inv (clippedTest W c θ) D 0 0=
      ∫v:ℝ,density (kernelLogSource W lo hi hlo hs hW) (Real.log c) v*
        polynomial χ inv (childLogTest Wref (θ+v)) D 0 0 := by
  let S:=HeckeInverseAmplification.idealsUpTo ⌈D*b⌉₊
  have hcover : ∀I : Ideal O,I≠0 → clippedTest W c θ ((I.absNorm:ℝ)/D)≠0 → I∈S := by
    intro I hI hi
    have hIp : 0<(I.absNorm:ℝ)/D:=div_pos (by exact_mod_cast (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))) hD
    apply finite_source_cover Wref D b hD hWref I hI
    intro hz
    have he:=hagree _ hIp
    rw [hz,zero_mul] at he
    exact hi (by simp [clippedTest,childLogTest,←he])
  rw [polynomial_eq_finite χ inv (clippedTest W c θ) D 0 0 S hcover]
  simp_rw [polynomial_eq_finite χ inv (childLogTest Wref (θ+_)) D 0 0 S
    (child_cover Wref b D hD hWref _)]
  simp only [HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_zero,
    neg_zero,Complex.cpow_zero,mul_one,Finset.mul_sum]
  have hint (I : Ideal O) : Integrable (fun v:ℝ=>
      density (kernelLogSource W lo hi hlo hs hW) (Real.log c) v*
        ((D:ℂ)^(-(1/2:ℂ))*(HeckeDyadic.coefficient χ inv I*childLogTest Wref (θ+v) ((I.absNorm:ℝ)/D)))) := by
    convert fourier_phase_integrable (kernelLogSource W lo hi hlo hs hW)
      (Real.log c+Real.log ((I.absNorm:ℝ)/D))
      ((D:ℂ)^(-(1/2:ℂ))*HeckeDyadic.coefficient χ inv I*Wref ((I.absNorm:ℝ)/D)*
        kernelLogPhase θ (Real.log ((I.absNorm:ℝ)/D))) using 1 <;> first
    | rfl
    | (funext v; simp only [density,childLogTest,kernelLogPhase_add_frequency,kernelLogPhase_add]; ring)
  rw [integral_finsetSum _ (fun I _=> hint I)]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hz : I=0
  · subst I
    simp only [coefficient_zero,zero_mul,mul_zero,integral_zero]
  have hIp : 0<(I.absNorm:ℝ)/D:=div_pos (by exact_mod_cast (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hz))) hD
  rw [clipped_test_fourier W lo hi hlo hs hW Wref c θ _ hc hIp (hagree _ hIp),
    ←integral_const_mul,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with v
  have hprofile : CanonicalCubeSeparation.sourceLogProfile W lo hi hlo hs hW =
      kernelLogSource W lo hi hlo hs hW := by
    ext x
    rfl
  rw [hprofile]
  ring

end DetectorDictionaryInverseRawFourier

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory
namespace DetectorDictionaryInverseRawFourier
open HeckeFamily HeckeDyadic InverseMoment InverseInitialClippedColumns
open InverseInitialOverlapFourier JointLogSeparation HeckeInverseAmplification

theorem polynomial_clipped_energy {ι : Type*} (rows : Finset ι)
    (χ : ι→Character) (inv : Bool) (A : ι→ℂ)
    (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0< lo)
    (hs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Wref : ℝ→ℂ) (b c θ D E : ℝ) (J : ℕ) (hc : 0< c) (hD : 0< D) (hE : 0≤ E)
    (hWref : ∀x,Wref x≠0 → x≤ b)
    (hagree : ∀y,0< y → Wref y*W (c*y)=W (c*y))
    (he : ∀s, (∑i∈rows,‖polynomial (χ i) inv (childLogTest Wref s) D 0 0*A i‖^2)
      ≤ E*(1+‖s‖)^(2*J)) :
    (∑i∈rows,‖polynomial (χ i) inv (clippedTest W c θ) D 0 0*A i‖^2)≤
      E*(1+‖θ‖)^(2*J)*
        (∫v:ℝ,(1+‖v‖)^J*‖(𝓕 (kernelLogSource W lo hi hlo hs hW)) v‖)^2 := by
  let g:=kernelLogSource W lo hi hlo hs hW
  let B:=density g (Real.log c)
  let φ : rows→ℝ→ℂ:=fun i v=> polynomial (χ i) inv (childLogTest Wref (θ+v)) D 0 0*A i
  have hint (i : rows) : Integrable (fun v:ℝ=> B v*φ i v) := by
    simpa only [B,φ,mul_assoc] using
      (polynomial_mode_integrable (χ i) inv g Wref b c θ D hD hWref).mul_const (A i)
  have hbound (v : ℝ) : (∑i:rows,‖φ i v‖^2)≤
      (E*(1+‖θ‖)^(2*J))*((1+‖v‖)^J)^2 := by
    dsimp only [φ]
    rw [Finset.sum_coe_sort rows (fun i=>‖polynomial (χ i) inv (childLogTest Wref (θ+v)) D 0 0*A i‖^2)]
    apply (he (θ+v)).trans
    have hh : 1+‖θ+v‖≤(1+‖θ‖)*(1+‖v‖) := by
      have hn:=norm_add_le θ v
      nlinarith [mul_nonneg (norm_nonneg θ) (norm_nonneg v)]
    calc
      _≤ E*((1+‖θ‖)*(1+‖v‖))^(2*J):=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hh _) hE
      _= _:=by rw [mul_pow,pow_mul];ring
  have hden : Integrable (fun v:ℝ=>(1+‖v‖)^J*‖B v‖) := by
    simpa only [B,density_norm] using JointLogSeparation.schwartz_fourier_one_plus_integrable g J
  have hh:=CenteredMomentHeckeWindowEnergy.finite_weighted_integral_energy B φ
    (fun v:ℝ=>(1+‖v‖)^J) (by intro v;positivity)
    (E*(1+‖θ‖)^(2*J)) (by positivity) hden hint hbound
  have heq (i : rows) : (∫v:ℝ,B v*φ i v)=
      polynomial (χ i) inv (clippedTest W c θ) D 0 0*A i := by
    rw [polynomial_clipped_fourier (χ i) inv W lo hi hlo hs hW Wref b c θ D hc hD hWref hagree,
      ←integral_mul_const]
    apply integral_congr_ae
    filter_upwards with v
    dsimp [B,φ,g]
    ring
  simp_rw [heq] at hh
  rw [Finset.sum_coe_sort rows (fun i=>‖polynomial (χ i) inv (clippedTest W c θ) D 0 0*A i‖^2)] at hh
  simpa only [B,density_norm,g] using hh

theorem rawMoment_reference (data : RowData)
    (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0< lo)
    (hs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Wref : ℝ→ℂ) (b c κ C : ℝ) (J : ℕ) (hC : 0≤ C)
    (hWref : ∀x,Wref x≠0 → x≤ b)
    (hagree : ∀y,0< y → Wref y*W y=W y)
    (he : ∀s,RawMoment data (childLogTest Wref s) c κ (C*(1+‖s‖)^(2*J))) :
    RawMoment data W c κ
      (C*(∫v:ℝ,(1+‖v‖)^J*‖(𝓕 (kernelLogSource W lo hi hlo hs hW)) v‖)^2) := by
  intro H D hH hD hHD rows hrows
  have hh:=polynomial_clipped_energy rows data.character true (fun _=>1)
    W lo hi hlo hs hW Wref b 1 0 D (C*H*(H*max 1 D)^κ) J (by norm_num) hD
    (by positivity) hWref (by simpa only [one_mul] using hagree) (by
      intro s
      have hb:=he s H D hH hD hHD rows hrows
      simpa only [mul_one,one_mul,mul_assoc,mul_left_comm,mul_comm] using hb)
  have heq : clippedTest W 1 0=W := by
    funext x
    simp [clippedTest,childLogTest,kernelLogPhase]
  rw [heq] at hh
  simpa only [mul_one,one_mul,norm_zero,add_zero,one_pow,mul_assoc,mul_left_comm,mul_comm] using hh

end DetectorDictionaryInverseRawFourier

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace DetectorDictionaryInverseRawGeometry
open InverseMoment InverseInitialCanonicalState

def capacityGap (c : ℝ) : ℝ:=c/(1+c)

theorem capacityGap_pos (c : ℝ) (hc : 0< c) : 0< capacityGap c :=
  div_pos hc (by linarith)

theorem capacityGap_lt_one (c : ℝ) (hc : 0< c) : capacityGap c<1 := by
  apply (div_lt_one (by linarith : 0<1+c)).mpr
  linarith

theorem raw_log_capacity (H D c : ℝ) (hH : 1< H) (hD : 1≤ D) (hc : 0< c)
    (hcap : D^(1+c)≤ H) :
    0≤ Real.logb H D ∧ Real.logb H D≤1-capacityGap c ∧
    2*Real.logb H D≤3-capacityGap c ∧ H^(Real.logb H D)=D := by
  have hHp : 0< H:=zero_lt_one.trans hH
  have hDp : 0< D:=zero_lt_one.trans_le hD
  have hlogH : 0< Real.log H:=Real.log_pos hH
  have hh:=Real.log_le_log (Real.rpow_pos_of_pos hDp (1+c)) hcap
  rw [Real.log_rpow hDp] at hh
  have hr : Real.logb H D≤1/(1+c) := by
    unfold Real.logb
    apply (le_div_iff₀ (by linarith : 0<1+c)).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hlogH).mpr
    simpa only [mul_div_assoc,mul_comm,mul_left_comm,one_mul] using hh
  have he : 1/(1+c)=1-capacityGap c := by
    unfold capacityGap
    field_simp
    ring
  have hg:=(capacityGap_pos c hc).le
  exact ⟨div_nonneg (Real.log_nonneg hD) hlogH.le,hr.trans_eq he,
    by linarith [hr.trans_eq he],Real.rpow_logb hHp (ne_of_gt hH) hDp⟩

theorem raw_fixed_reserves (c κ : ℝ) (hc : 0< c) (hκ : 0<κ) :
    ∃η τ π ε : ℝ,0<η ∧ 0<τ ∧ 0<π ∧ 0<ε ∧
      η≤1 ∧ η≤ capacityGap c/200 ∧ τ≤ capacityGap c/200 ∧
      40*η+π+ε≤κ := by
  let η:=min (capacityGap c/200) (min (κ/100) (1/100))
  have hg:=capacityGap_pos c hc
  have hη : 0<η:=lt_min (by positivity)
    (lt_min (by positivity) (by norm_num))
  have hηg : η≤ capacityGap c/200:=min_le_left _ _
  have hηκ : η≤κ/100:=(min_le_right _ _).trans (min_le_left _ _)
  have hη1 : η≤1/100:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨η,η,κ/4,κ/4,hη,hη,by positivity,by positivity,by linarith,hηg,hηg,?_⟩
  linarith

theorem raw_retained_margins (H D c B θ v Hfreq η τ Q : ℝ)
    (hH : 1< H) (hD : 1≤ D) (hc : 0< c) (hcap : D^(1+c)≤ H)
    (hP : -2*η≤ B-θ) (hQ : Q≤ B-θ+3*η) (hη : 0≤η)
    (hηsmall : η≤ capacityGap c/100) (hτ : τ≤ capacityGap c/100)
    (hcut : InverseInitialProfile.radialCenter 1 Hfreq θ (Real.logb H D) B≤4*η+τ) :
    CanonicalMargins
      (max 0 (Real.logb H D-B-v)+(θ+v+2*η)) (θ+Hfreq+2*η) Q 0
      (3*capacityGap c/4) := by
  obtain ⟨hr,hfirst,hsecond,_⟩:=raw_log_capacity H D c hH hD hc hcap
  have hh:=enlarged_initial_margins 1 (Real.logb H D) 0 0 B θ v Hfreq η τ Q
    (capacityGap c) (capacityGap c)
    (by simpa using hfirst) (by simpa using hsecond) (by norm_num) hP
    (by simpa using hQ) (by simpa using (capacityGap_pos c hc).le) hη
    (by simpa using hηsmall) (by simpa using hτ) (by simpa using hcut)
  simpa using hh

theorem raw_output_budget (H D κ e : ℝ) (hH : 1≤ H) (hκ : 0≤κ) (he : e≤κ) :
    H^(1+e)≤ H*(H*max 1 D)^κ := by
  have hHp : 0< H:=zero_lt_one.trans_le hH
  rw [Real.rpow_add hHp,Real.rpow_one]
  apply mul_le_mul_of_nonneg_left _ hHp.le
  calc
    H^e≤ H^κ:=Real.rpow_le_rpow_of_exponent_le hH he
    _≤(H*max 1 D)^κ:=Real.rpow_le_rpow hHp.le (by nlinarith [le_max_left 1 D]) hκ

end DetectorDictionaryInverseRawGeometry

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace DetectorDictionaryInverseRawRadial
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialConjugateEnergy CanonicalQuadraticSieve
open  Eisenstein
local notation "O"=> Eisenstein.O

theorem exists_raw_radial_majorant :
    ∃Φ : 𝓢(ℝ,ℂ),HasCompactSupport (Φ:ℝ→ℂ) ∧
      (∀x,0≤(Φ x).re) ∧ (∀x∈Set.Icc (0:ℝ) 1,Φ x=1) := by
  refine ⟨sieveCutoff,?_,?_,?_⟩
  · exact sieveBump.hasCompactSupport.comp_left Complex.ofReal_zero
  · intro x
    exact sieveBump.nonneg
  · intro x hx
    rw [sieveCutoff_apply,sieveBump_eq_one hx.1 hx.2,Complex.ofReal_one]

private theorem admissible_one : Admissible (1:Ideal O) := by
  refine ⟨one_ne_zero,squarefree_one,?_⟩
  simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero,false_implies,forall_const]

theorem finite_raw_le_initial_smoothed (Φ : 𝓢(ℝ,ℂ))
    (hΦ : ∀x,0≤(Φ x).re) (hone : ∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (data : RowData) (W : ℝ→ℂ) (b Z r σ t H : ℝ)
    (hZ : 0< Z) (hH : 0< H) (hW : ∀x,W x≠0 → x≤ b)
    (rows : Finset NonzeroElement)
    (hrows : ∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤ H) :
    (∑u∈rows,‖polynomial (data.character u) true W (Z^r) σ t‖^2)≤
      smoothedEnergy Φ H
        (originalTotalPolynomial
          ((HeckeInverseAmplification.idealsUpTo ⌈Z^r*b⌉₊).filter Supported)
          1 (fixedBase data.η data.m data.f) (fun _=>1)
          (twistedProfile W σ t) Z r 0) := by
  let S:=(HeckeInverseAmplification.idealsUpTo ⌈Z^r*b⌉₊).filter Supported
  let f:=originalTotalPolynomial S 1 (fixedBase data.η data.m data.f) (fun _=>1)
    (twistedProfile W σ t) Z r 0
  have hsum : Summable (fun u:O=> radialWeight Φ H u*‖f u‖^2) :=
    (original_smoothed_overlap_triangle S admissible_one
      (fun n hn _=>(Finset.mem_filter.mp hn).2) (fixedBase data.η data.m data.f)
      (fun _=>1) (twistedProfile W σ t) hZ r 0 (fun _=>0) Φ (fun x _=> hΦ x) hH).1
  have he (u : NonzeroElement) (hu : u∈rows) :
      ‖polynomial (data.character u) true W (Z^r) σ t‖^2=
        radialWeight Φ H u.val*‖f u.val‖^2 := by
    have hn : ‖ringComplex u.val‖^2/H∈Set.Icc (0:ℝ) 1 := by
      refine ⟨div_nonneg (sq_nonneg _) hH.le,?_⟩
      apply (div_le_one hH).mpr
      rw [ringComplex_norm_sq_eq_absNorm_span]
      exact hrows u hu
    rw [character_eq_initial data u W Z r σ t b hZ hW]
    change ‖f u.val‖^2=(Φ (‖ringComplex u.val‖^2/H)).re*‖f u.val‖^2
    rw [hone _ hn,Complex.one_re,one_mul]
  calc
    _=∑u∈rows,radialWeight Φ H u.val*‖f u.val‖^2:=Finset.sum_congr rfl he
    _=∑u∈rows.image Subtype.val,radialWeight Φ H u*‖f u‖^2:=by
      rw [Finset.sum_image (fun a _ b _ hab=> Subtype.val_injective hab)]
    _≤∑'u:O,radialWeight Φ H u*‖f u‖^2:=hsum.sum_le_tsum _
      (fun u _=> mul_nonneg (hΦ _) (sq_nonneg _))
    _= _:=rfl

end DetectorDictionaryInverseRawRadial

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace DetectorDictionaryInverseRawRealRadial
open InverseInitialConjugateEnergy 
local notation "O"=> Eisenstein.O

theorem exists_real_raw_radial_majorant:
    ∃Φ:𝓢(ℝ,ℂ),HasCompactSupport (Φ:ℝ→ℂ) ∧
      (∀x,0≤(Φ x).re) ∧ (∀x,(Φ x).im=0) ∧
      (∀x∈Set.Icc (0:ℝ) 1,Φ x=1):=by
  refine ⟨sieveCutoff,?_,?_,?_,?_⟩
  · exact sieveBump.hasCompactSupport.comp_left Complex.ofReal_zero
  · intro x
    exact sieveBump.nonneg
  · intro x
    exact Complex.ofReal_im _
  · intro x hx
    rw [sieveCutoff_apply,sieveBump_eq_one hx.1 hx.2,Complex.ofReal_one]

theorem smoothedEnergy_eq_complex_norm (Φ:𝓢(ℝ,ℂ))
    (hΦ:∀x,0≤(Φ x).re)(hreal:∀x,(Φ x).im=0)
    (H:ℝ)(hH:0< H)(f:O→ℂ):
    smoothedEnergy Φ H f=
      ‖∑'u:O,Φ (‖ringComplex u‖^2/H)*(‖f u‖^2:ℝ)‖:=by
  rw [real_smoothed_sum_eq Φ (fun x _=> hreal x) hH,
    Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (smoothedEnergy_nonneg Φ (fun x _=> hΦ x) hH f)]

end DetectorDictionaryInverseRawRealRadial

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace DetectorDictionaryInverseRawCompact
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment JointLogSeparation HeckePrimeAnnular
open CenteredMomentOriginalReflectionErrorMass CenteredMomentCounting
open Eisenstein 

local notation "O" => Eisenstein.O

lemma inverse_polynomial_all_ideals (χ : Character) (W : ℝ→ℂ) (D freq : ℝ) :
    polynomial χ true W D 0 freq =
      (D:ℂ)^(-(1/2:ℂ))*∑'I:Ideal O,HeckeDyadic.coefficient χ true I*annularWeight W D 0 freq I := by
  unfold polynomial
  congr 1
  have he : (∑'I:HeckeDyadic.NonzeroIdeal,HeckeDyadic.coefficient χ true I.val*annularWeight W D 0 freq I.val)=
      ∑'I:Ideal O,HeckeDyadic.coefficient χ true I*annularWeight W D 0 freq I := by
    apply tsum_subtype_eq_of_support_subset (s:={I:Ideal O|I≠0})
      (f:=fun I:Ideal O=> HeckeDyadic.coefficient χ true I*annularWeight W D 0 freq I)
    intro I hI hz
    subst I
    exact hI (by simp only [coefficient_zero,zero_mul])
  simpa only [HeckeDyadic.summand,HeckeDyadic.norm,annularWeight,mul_assoc] using he

theorem inverse_polynomial_bound (χ : Character) (W : ℝ→ℂ) (b B D freq : ℝ)
    (hB : 0≤ B) (hD : 0< D) (hW : ∀x,‖W x‖≤ B)
    (hs : Function.support W⊆Set.Iic b) :
    ‖polynomial χ true W D 0 freq‖≤(128*max 1 b*B)*Real.sqrt D := by
  rw [inverse_polynomial_all_ideals]
  apply normalized_linear_bound D _ hD
  have hh:=norm_tsum_ideal_ball (fun I:Ideal O=> HeckeDyadic.coefficient χ true I*annularWeight W D 0 freq I)
    (max 1 b*D) B (by positivity) hB (by
      change HeckeDyadic.coefficient χ true (0:Ideal O)*_ = 0
      rw [coefficient_zero,zero_mul])
    (by
      intro I
      by_cases hI:I=0
      · subst I
        simpa only [coefficient_zero,zero_mul,norm_zero] using hB
      rw [norm_mul,annularWeight_zero_norm W D freq hD I hI]
      exact (mul_le_mul (coefficient_norm_le χ true I) (hW _) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul B))
    (by
      intro I hne
      have hw : W ((I.absNorm:ℝ)/D)≠0 := by
        intro hz
        exact hne (by simp only [annularWeight,hz,zero_mul,mul_zero])
      exact ((div_le_iff₀ hD).mp (hs hw)).trans
        (mul_le_mul_of_nonneg_right (le_max_right 1 b) hD.le))
  convert hh using 1 <;> first | rfl | ring

lemma childLogTest_norm (W : ℝ→ℂ) (s x : ℝ) :
    ‖childLogTest W s x‖=‖W x‖ := by
  simp only [childLogTest,norm_mul,kernelLogPhase_norm,mul_one]

theorem inverse_reference_bound (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a)
    (hs : Function.support W⊆Set.Icc a b) :
    ∃A:ℝ,0< A ∧ ∀(χ:Character) (s D:ℝ),0< D →
      ‖polynomial χ true (childLogTest W s) D 0 0‖≤ A*Real.sqrt D := by
  have hc : HasCompactSupport (W : ℝ → ℂ) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs
  obtain ⟨x₀,hx₀⟩ := W.continuous.norm.exists_forall_ge_of_hasCompactSupport hc.norm
  let B : ℝ := ‖W x₀‖ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hbound (x : ℝ) : ‖W x‖ ≤ B :=
    (hx₀ x).trans (le_add_of_nonneg_right zero_le_one)
  refine ⟨128*max 1 b*B,by positivity,?_⟩
  intro χ s D hD
  apply inverse_polynomial_bound χ (childLogTest W s) b B D 0 hB.le hD
  · intro x
    simpa only [childLogTest_norm] using hbound x
  · intro x hx
    have hw : W x≠0 := by
      intro hz
      exact hx (by simp only [childLogTest,hz,zero_mul])
    exact (hs hw).2

theorem nonzero_element_rows_card (rows : Finset NonzeroElement) (H : ℝ) (hH : 1≤ H)
    (hrows : ∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤ H) :
    (rows.card:ℝ)≤128*H := by
  have hh:=EisensteinLatticeCount.finite_element_count_real (rows.image Subtype.val) H hH (by
    intro z hz
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hz
    rw [ringComplex_norm_sq_eq_absNorm_span]
    exact hrows v hv)
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
  exact hh

theorem reference_energy_linear (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a)
    (hs : Function.support W⊆Set.Icc a b) :
    ∃K:ℝ,0< K ∧ ∀(χ:NonzeroElement→Character) (rows:Finset NonzeroElement)
      (s H D:ℝ),1≤ H → 0< D →
      (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤ H) →
      (∑v∈rows,‖polynomial (χ v) true (childLogTest W s) D 0 0‖^2)≤ K*H*D := by
  obtain ⟨A,hA,hbound⟩:=inverse_reference_bound W a b ha hs
  refine ⟨128*A^2,by positivity,?_⟩
  intro χ rows s H D hH hD hrows
  calc
    _≤∑v∈rows,A^2*D := by
      apply Finset.sum_le_sum
      intro v _
      have hh:=pow_le_pow_left₀ (norm_nonneg _) (hbound (χ v) s D hD) 2
      simpa only [mul_pow,Real.sq_sqrt hD.le] using hh
    _=(rows.card:ℝ)*(A^2*D) := by simp
    _≤(128*H)*(A^2*D) := mul_le_mul_of_nonneg_right
      (nonzero_element_rows_card rows H hH hrows) (by positivity)
    _=(128*A^2)*H*D := by ring

theorem subunit_rows_reference_energy (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a)
    (hs : Function.support W⊆Set.Icc a b) :
    ∃C0:ℝ,0< C0 ∧ ∀(χ:NonzeroElement→Character) (rows:Finset NonzeroElement)
      (s H D:ℝ),1≤ H → 0< D → D≤1 →
      (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤ H) →
      (∑v∈rows,‖polynomial (χ v) true (childLogTest W s) D 0 0‖^2)≤ C0*H := by
  obtain ⟨K,hK,hbound⟩:=reference_energy_linear W a b ha hs
  refine ⟨K,hK,?_⟩
  intro χ rows s H D hH hD hD1 hrows
  exact (hbound χ rows s H D hH hD hrows).trans
    (mul_le_of_le_one_right (by positivity) hD1)

lemma scale_le_rows (c H D : ℝ) (hc : 0≤ c) (hH : 1≤ H)
    (_hD : 0< D) (hDH : D^(1+c)≤ H) : D≤ H := by
  by_cases hD1:D≤1
  · exact hD1.trans hH
  · have hd : 1≤ D := le_of_not_ge hD1
    calc
      D=D^(1:ℝ) := (Real.rpow_one D).symm
      _≤ D^(1+c) := Real.rpow_le_rpow_of_exponent_le hd (by linarith)
      _≤ H := hDH

theorem small_rows_reference_energy (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a)
    (hs : Function.support W⊆Set.Icc a b) (H0 : ℝ) (hH0 : 1≤ H0) :
    ∃C0:ℝ,0< C0 ∧ ∀(χ:NonzeroElement→Character) (rows:Finset NonzeroElement)
      (s H D c:ℝ),1≤ H → H≤ H0 → 0≤ c → 0< D → D^(1+c)≤ H →
      (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤ H) →
      (∑v∈rows,‖polynomial (χ v) true (childLogTest W s) D 0 0‖^2)≤ C0*H := by
  obtain ⟨K,hK,hbound⟩:=reference_energy_linear W a b ha hs
  refine ⟨K*H0,by positivity,?_⟩
  intro χ rows s H D c hH hHH0 hc hD hDH hrows
  calc
    _≤ K*H*D := hbound χ rows s H D hH hD hrows
    _≤ K*H*H0 := mul_le_mul_of_nonneg_left ((scale_le_rows c H D hc hH hD hDH).trans hHH0)
      (by positivity)
    _=(K*H0)*H := by ring

lemma raw_majorant_ge_linear (C C0 H D κ s : ℝ) (J : ℕ)
    (hC : 0≤ C) (hC0 : 0≤ C0) (hH : 1≤ H) (hκ : 0≤κ) :
    C0*H≤((C+C0)*(1+‖s‖)^(2*J))*H*(H*max 1 D)^κ := by
  have ht : 1≤(1+‖s‖)^(2*J) := one_le_pow₀ (by linarith [norm_nonneg s])
  have hb : 1≤ H*max 1 D := hH.trans
    (le_mul_of_one_le_right (by positivity) (le_max_left _ _))
  have hp : 1≤(H*max 1 D)^κ := Real.one_le_rpow hb hκ
  calc
    C0*H≤(C+C0)*H := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _≤((C+C0)*(1+‖s‖)^(2*J))*H := mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (by positivity) ht) (by positivity)
    _≤ _ := le_mul_of_one_le_right (by positivity) hp

theorem rawMoment_of_large_rows_ge_one (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a)
    (hs : Function.support W⊆Set.Icc a b) (H0 : ℝ) (hH0 : 1≤ H0) :
    ∃C0:ℝ,0< C0 ∧ ∀(data:RowData) (c κ C:ℝ) (J:ℕ),
      0≤ c → 0≤κ → 0≤ C →
      (∀(s H D:ℝ),H0≤ H → 1≤ D → D^(1+c)≤ H →
        ∀rows:Finset NonzeroElement,
          (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤ H) →
          (∑v∈rows,‖polynomial (data.character v) true (childLogTest W s) D 0 0‖^2)≤
            (C*(1+‖s‖)^(2*J))*H*(H*max 1 D)^κ) →
      ∀s:ℝ,RawMoment data (childLogTest W s) c κ ((C+C0)*(1+‖s‖)^(2*J)) := by
  obtain ⟨K,hK,hbound⟩:=reference_energy_linear W a b ha hs
  refine ⟨K*H0,by positivity,?_⟩
  intro data c κ C J hc hκ hC hlarge s H D hH hD hDH rows hrows
  have hsmall (hDH0:D≤ H0) :
      (∑v∈rows,‖polynomial (data.character v) true (childLogTest W s) D 0 0‖^2)≤
        ((C+K*H0)*(1+‖s‖)^(2*J))*H*(H*max 1 D)^κ := by
    calc
      _≤ K*H*D := hbound data.character rows s H D hH hD hrows
      _≤ K*H*H0 := mul_le_mul_of_nonneg_left hDH0 (by positivity)
      _=(K*H0)*H := by ring
      _≤ _ := raw_majorant_ge_linear C (K*H0) H D κ s J hC (by positivity) hH hκ
  by_cases hHH0:H≤ H0
  · exact hsmall ((scale_le_rows c H D hc hH hD hDH).trans hHH0)
  by_cases hD1:D≤1
  · exact hsmall (hD1.trans hH0)
  · apply (hlarge s H D (le_of_not_ge hHH0) (le_of_not_ge hD1) hDH rows hrows).trans
    gcongr
    exact le_add_of_nonneg_right (by positivity)

theorem rawMoment_of_large_rows (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a)
    (hs : Function.support W⊆Set.Icc a b) (H0 : ℝ) (hH0 : 1≤ H0) :
    ∃C0:ℝ,0< C0 ∧ ∀(data:RowData) (c κ C:ℝ) (J:ℕ),
      0≤ c → 0≤κ → 0≤ C →
      (∀(s H D:ℝ),H0≤ H → 0< D → D^(1+c)≤ H →
        ∀rows:Finset NonzeroElement,
          (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤ H) →
          (∑v∈rows,‖polynomial (data.character v) true (childLogTest W s) D 0 0‖^2)≤
            (C*(1+‖s‖)^(2*J))*H*(H*max 1 D)^κ) →
      ∀s:ℝ,RawMoment data (childLogTest W s) c κ ((C+C0)*(1+‖s‖)^(2*J)) := by
  obtain ⟨C0,hC0,hcomplete⟩:=rawMoment_of_large_rows_ge_one W a b ha hs H0 hH0
  refine ⟨C0,hC0,?_⟩
  intro data c κ C J hc hκ hC hlarge
  apply hcomplete data c κ C J hc hκ hC
  intro s H D hH hD hDH rows hrows
  exact hlarge s H D hH (zero_lt_one.trans_le hD) hDH rows hrows

end DetectorDictionaryInverseRawCompact

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators SchwartzMap Topology
open Filter
namespace DetectorDictionaryInverseRawInitialGates
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialRayAttachment InverseInitialExcludedPeriod
open InverseInitialExcludedPool InverseInitialExcludedOverlap InverseInitialExcludedPolynomial
open CanonicalRowCompletion CanonicalCoefficientClass CanonicalQuadraticSieve 
open  UniqueFactorizationMonoid 
open DetectorDictionaryInverseRawGeometry
local notation "O"=> Eisenstein.O

def basePeriod (data:RowData):ℕ:=(baseCharacter data).period

def excluded (data:RowData):Finset (Ideal O):=reflectionExcludedPrimes (basePeriod data)

def deletedBase (data:RowData):Character:=
  (baseCharacter data).excludePrimes (excluded data) (reflectionExcludedPrimes_prime (basePeriod data))

theorem basePeriod_ne_zero (data:RowData):basePeriod data≠0:=Nat.ne_of_gt (Character.period_pos _)

theorem basePeriod_le (data:RowData):Ideal.span {(basePeriod data:O)}≤(baseCharacter data).modulus:=
  Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Character.period_mem _))

theorem raw_base_gates (data:RowData):
    deletedPeriod (basePeriod data)≠0 ∧
    reflectionExcludedPrimes (deletedPeriod (basePeriod data))=excluded data ∧
    (∀x,‖elementCharacter (idealCoeff (deletedBase data)).toMonoidHom x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod (basePeriod data)))
      (elementCharacter (idealCoeff (deletedBase data)).toMonoidHom):=
  deleted_physical_base_gates (baseCharacter data) (basePeriod data)
    (basePeriod_ne_zero data) (basePeriod_le data)

theorem actual_row_fixed_base (data:RowData)(u:NonzeroElement)(I:Ideal O):
    idealCoeff (data.character u) I=idealCoeff (baseCharacter data) I*idealRowHom u.val I:=by
  rw [baseCharacter_coeff]
  exact fixedBase_row data.η (data.character u) data.m data.f u.val (data.character_spec u) I

theorem actual_deleted_row (data:RowData)(u:NonzeroElement)(I:Ideal O):
    idealCoeff ((data.character u).excludePrimes (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data))) I=
      idealCoeff (deletedBase data) I*idealRowHom u.val I:=by
  unfold deletedBase excluded
  rw [idealCoeff_excludePrimes,idealCoeff_excludePrimes,actual_row_fixed_base]
  split_ifs <;> simp

def completeCutoff (H b Btree cap:ℝ):ℕ:=⌈max (Btree*H^(cap+1)) (b*H)⌉₊

theorem completeCutoff_tree (H b Btree cap:ℝ):
    Btree*H^(cap+1)≤(completeCutoff H b Btree cap:ℝ):=
  (le_max_left _ _).trans (Nat.le_ceil _)

theorem completeCutoff_columns (H b Btree cap D n:ℝ)(hb:0≤ b)(hD:0≤ D)
    (hDH:D≤ H)(hn:1≤ n):b*(D/n)≤(completeCutoff H b Btree cap:ℝ):=by
  have hn0:0< n:=zero_lt_one.trans_le hn
  have hdn:D/n≤ D:=(div_le_iff₀ hn0).mpr (le_mul_of_one_le_right hD hn)
  exact (mul_le_mul_of_nonneg_left (hdn.trans hDH) hb).trans
    ((le_max_right _ _).trans (Nat.le_ceil _))

theorem excluded_divisor_norm (data:RowData)(j:Ideal O)
    (hj:j∈idealDivisors (∏P∈excluded data,P)):
    1≤(j.absNorm:ℝ) ∧ (j.absNorm:ℝ)≤((∏P∈excluded data,P).absNorm:ℝ):=by
  have hP:Squarefree (∏P∈excluded data,P):=
    prime_product_squarefree _ (reflectionExcludedPrimes_prime (basePeriod data))
  have hd: j∣∏P∈excluded data,P:=(mem_idealDivisors hP.ne_zero).mp hj
  have hj0:=ne_zero_of_dvd_ne_zero hP.ne_zero hd
  constructor
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hj0)
  · exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero)) (map_dvd Ideal.absNorm hd)

theorem shifted_raw_geometry_eventually (data:RowData)(c eta:ℝ)(hc:0< c)(heta:0< eta):
    ∀ᶠH:ℝ in atTop,1< H ∧ ∀D:ℝ,1≤ D→D^(1+c)≤ H→
      ∀j∈idealDivisors (∏P∈excluded data,P),
      let r:=Real.logb H (D/(j.absNorm:ℝ));
      -eta≤ r ∧ r≤1-capacityGap c ∧ 2*r≤3-capacityGap c ∧
      H^r=D/(j.absNorm:ℝ) ∧ r+7*eta≤1+7*eta ∧ D≤ H:=by
  have ht:∀ᶠH:ℝ in atTop,((∏P∈excluded data,P).absNorm:ℝ)≤ H^eta:=
    (tendsto_rpow_atTop heta).eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (1:ℝ),ht] with H hH ht
  refine ⟨hH,?_⟩
  intro D hD hcap j hj r
  obtain ⟨hn,hnB⟩:=excluded_divisor_norm data j hj
  have hH0:0< H:=zero_lt_one.trans hH
  have hD0:0< D:=zero_lt_one.trans_le hD
  have hn0:0<(j.absNorm:ℝ):=zero_lt_one.trans_le hn
  obtain ⟨hr0,hr1,hr2,hex⟩:=raw_log_capacity H D c hH hD hc hcap
  have hr:r=Real.logb H D-Real.logb H (j.absNorm:ℝ):=
    Real.logb_div hD0.ne' hn0.ne'
  have hnlog:0≤ Real.logb H (j.absNorm:ℝ):=
    div_nonneg (Real.log_nonneg hn) (Real.log_pos hH).le
  have hneta:Real.logb H (j.absNorm:ℝ)≤ eta:=by
    exact (Real.logb_le_iff_le_rpow hH hn0).mpr (hnB.trans ht)
  have hrlo:-eta≤ r:=by rw [hr];linarith
  have hrup:r≤1-capacityGap c:=by rw [hr];linarith
  refine ⟨hrlo,hrup,by rw [hr];linarith,
    Real.rpow_logb hH0 hH.ne' (div_pos hD0 hn0),?_,?_⟩
  · linarith [(capacityGap_pos c hc).le]
  · calc
      D=H^(Real.logb H D):=hex.symm
      _≤ H^1:=Real.rpow_le_rpow_of_exponent_le hH.le (by linarith [(capacityGap_pos c hc).le])
      _=H:=Real.rpow_one _

theorem deleted_row_complete_polynomial (data:RowData)(u:NonzeroElement)
    (W:ℝ→ℂ)(H r sigma freq b:ℝ)(hH:0< H)
    (hW:∀x,W x≠0→x≤ b)(Dpool:ℕ)(hbudget:b*H^r≤(Dpool:ℝ)):
    polynomial ((data.character u).excludePrimes (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data))) true W (H^r) sigma freq=
      InverseInitialConjugateEnergy.originalTotalPolynomial
        (CanonicalRowCompletion.outsideSquarefreeIdeals (excluded data) Dpool) 1
        (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1)
        (twistedProfile W sigma freq) H r 0 u.val:=by
  let χ:=(data.character u).excludePrimes (excluded data)
    (reflectionExcludedPrimes_prime (basePeriod data))
  let F:=CanonicalRowCompletion.outsideSquarefreeIdeals (excluded data) Dpool
  have hs:(∑'I:Ideal O,(moebius I:ℂ)*idealCoeff χ I*
      (W ((I.absNorm:ℝ)/H^r)*(((I.absNorm:ℝ)/H^r:ℝ):ℂ)^(-HeckeDyadic.shift sigma freq)))=
      ∑I∈F,(moebius I:ℂ)*idealCoeff χ I*
        (W ((I.absNorm:ℝ)/H^r)*(((I.absNorm:ℝ)/H^r:ℝ):ℂ)^(-HeckeDyadic.shift sigma freq)):=by
    apply tsum_eq_sum
    intro I hn
    by_cases hsq:Squarefree I
    · by_cases hout:outside (excluded data) I
      · by_cases hw:W ((I.absNorm:ℝ)/H^r)=0
        · simp only [hw,zero_mul,mul_zero]
        · have hN:(I.absNorm:ℝ)≤(Dpool:ℝ):=
            ((div_le_iff₀ (Real.rpow_pos_of_pos hH r)).mp (hW _ hw)).trans hbudget
          have hmem:I∈F:=by
            apply Finset.mem_filter.mpr
            refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,?_,hout⟩,hsq⟩
            · exact Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hsq.ne_zero)
            · exact_mod_cast hN
          exact False.elim (hn hmem)
      · have hz:=deleted_zero_outside (data.character u) (excluded data)
          (reflectionExcludedPrimes_prime (basePeriod data)) I hout
        simp only [χ,hz,mul_zero,zero_mul]
    · simp only [moebius_of_not_squarefree hsq,Int.cast_zero,zero_mul]
  rw [polynomial_all_ideals,hs,normalization_eq H r hH]
  unfold InverseInitialConjugateEnergy.originalTotalPolynomial
  simp only [add_zero,map_one,mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [actual_deleted_row]
  simp only [twistedProfile,InverseInitialPoissonBridge.heckeIdealCharacter_apply]
  change (moebius I:ℂ) * (idealCoeff (deletedBase data) I * idealRowHom u.val I) *
      (W ((I.absNorm:ℝ)/H^r)*(((I.absNorm:ℝ)/H^r:ℝ):ℂ)^(-shift sigma freq)) =
    (moebius I:ℂ) * (idealCoeff (deletedBase data) I * idealRowHom u.val I) *
      (W ((I.absNorm:ℝ)/H^r)*(((I.absNorm:ℝ)/H^r:ℝ):ℂ)^(-shift sigma freq))
  ring

theorem raw_complete_pool (data:RowData)(H D c b Btree cap:ℝ)
    (hH:1< H)(hD:1≤ D)(hc:0< c)(hcap:D^(1+c)≤ H)(hb:0≤ b)
    (W:ℝ→ℂ)(hW:∀x,W x≠0→x≤ b):
    Btree*H^(cap+1)≤(completeCutoff H b Btree cap:ℝ) ∧
    ∀j∈idealDivisors (∏P∈excluded data,P),∀u:NonzeroElement,∀sigma freq:ℝ,
      polynomial ((data.character u).excludePrimes (excluded data)
        (reflectionExcludedPrimes_prime (basePeriod data))) true W
        (D/(j.absNorm:ℝ)) sigma freq=
      InverseInitialConjugateEnergy.originalTotalPolynomial
        (CanonicalRowCompletion.outsideSquarefreeIdeals (excluded data)
          (completeCutoff H b Btree cap)) 1
        (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1)
        (twistedProfile W sigma freq) H (Real.logb H (D/(j.absNorm:ℝ))) 0 u.val:=by
  refine ⟨completeCutoff_tree _ _ _ _,?_⟩
  intro j hj u sigma freq
  have hn:= (excluded_divisor_norm data j hj).1
  have hH0:0< H:=zero_lt_one.trans hH
  have hD0:0< D:=zero_lt_one.trans_le hD
  have hn0:0<(j.absNorm:ℝ):=zero_lt_one.trans_le hn
  have hex:=Real.rpow_logb hH0 hH.ne' (div_pos hD0 hn0)
  obtain ⟨_,hr,_,heD⟩:=raw_log_capacity H D c hH hD hc hcap
  have hDH:D≤ H:=by
    calc
      D=H^(Real.logb H D):=heD.symm
      _≤ H^1:=Real.rpow_le_rpow_of_exponent_le hH.le
        (by linarith [(capacityGap_pos c hc).le])
      _=H:=Real.rpow_one _
  have hbudget:b*H^(Real.logb H (D/(j.absNorm:ℝ)))≤
      (completeCutoff H b Btree cap:ℝ):=by
    rw [hex]
    exact completeCutoff_columns H b Btree cap D _ hb hD0.le hDH hn
  simpa only [hex] using deleted_row_complete_polynomial data u W H
    (Real.logb H (D/(j.absNorm:ℝ))) sigma freq b hH0 hW _ hbudget

end DetectorDictionaryInverseRawInitialGates

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators
namespace DetectorDictionaryInverseRawConjugateGates
open CanonicalRowCompletion
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialConjugateEnergy
open InverseInitialRayAttachment InverseInitialExcludedPeriod CanonicalCoefficientClass
open DetectorDictionaryInverseRawInitialGates InverseInitialExcludedPool
open InverseInitialExcludedOverlap InverseMoment InverseInitialProfile
local notation "O"=> Eisenstein.O

theorem conjugate_element_apply (η:Ideal O→*ℂ)(x:O):
    elementCharacter (conjugateIdealCharacter η) x=star (elementCharacter η x):=rfl

theorem conjugate_element_factors (η:Ideal O→*ℂ)(Q:Ideal O)
    (h:FactorsModulo Q (elementCharacter η)):
    FactorsModulo Q (elementCharacter (conjugateIdealCharacter η)):=by
  intro x y hxy
  exact congrArg star (h x y hxy)

theorem conjugate_element_norm (η:Ideal O→*ℂ)(x:O):
    ‖elementCharacter (conjugateIdealCharacter η) x‖=‖elementCharacter η x‖:=by
  rw [conjugate_element_apply,norm_star]

theorem raw_conjugate_base_gates (data:RowData):
    deletedPeriod (basePeriod data)≠0 ∧
    reflectionExcludedPrimes (deletedPeriod (basePeriod data))=excluded data ∧
    (∀x,‖elementCharacter (conjugateIdealCharacter
      (idealCoeff (deletedBase data)).toMonoidHom) x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod (basePeriod data)))
      (elementCharacter (conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom)):=by
  obtain ⟨hq,he,hn,hp⟩:=raw_base_gates data
  refine ⟨hq,he,?_,conjugate_element_factors _ _ hp⟩
  intro x
  rw [conjugate_element_norm]
  exact hn x

theorem raw_conjugate_zero_outside (data:RowData)(I:Ideal O)
    (hI:¬outside (excluded data) I):
    conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom I=0:=by
  change star (idealCoeff (deletedBase data) I)=0
  rw [show idealCoeff (deletedBase data) I=0 from
    deleted_zero_outside (InverseInitialDetectorSource.baseCharacter data)
      (excluded data) (reflectionExcludedPrimes_prime (basePeriod data)) I hI,star_zero]

theorem childLogTest_conjugate (W:ℝ→ℂ)(θ:ℝ):
    (fun x=> star (childLogTest W θ x))=childLogTest (fun x=> star (W x)) (-θ):=by
  funext x
  simp only [childLogTest,star_mul,JointLogSeparation.kernelLogPhase_conjugate]
  ring

theorem childLogTest_conjugate_norm (W:ℝ→ℂ)(θ x:ℝ):
    ‖childLogTest (fun x=> star (W x)) (-θ) x‖=‖W x‖:=by
  rw [InverseInitialProfileBounds.childLogTest_norm,norm_star]

theorem childLogTest_physical_profiles (W:ℝ→ℂ)(θ:ℝ):
    (fun x=> star (childLogTest W θ x))=clippedSource (fun x=> star (W x)) 1 (-θ) ∧
    childLogTest W θ=clippedSource W 1 θ:=by
  rw [childLogTest_conjugate]
  exact ⟨InverseInitialProfileBounds.childLogTest_eq_clipped _ _,
    InverseInitialProfileBounds.childLogTest_eq_clipped _ _⟩

end DetectorDictionaryInverseRawConjugateGates

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace DetectorDictionaryInverseRawInitialEnergy
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialConjugateEnergy
open InverseInitialRawDictionary InverseInitialExcludedPolynomial InverseInitialExcludedEnergy
open DetectorDictionaryInverseRawInitialGates CanonicalQuadraticSieve 
open Eisenstein  CanonicalRowCompletion CanonicalCoefficientClass
local notation "O"=> Eisenstein.O

private theorem admissible_one : Admissible (1:Ideal O) := by
  refine ⟨one_ne_zero,squarefree_one,?_⟩
  simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero,false_implies,forall_const]

def initialFunction (data:RowData)(W:ℝ→ℂ)(H b Btree cap D sigma freq:ℝ)(j:Ideal O):O→ℂ:=
  originalTotalPolynomial
    (CanonicalRowCompletion.outsideSquarefreeIdeals (excluded data) (completeCutoff H b Btree cap))
    1 (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1)
    (twistedProfile W sigma freq) H (Real.logb H (D/(j.absNorm:ℝ))) 0

theorem deleted_rows_le_initial
    (Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (data:RowData)(W:ℝ→ℂ)(H D c b Btree cap sigma freq:ℝ)
    (hH:1< H)(hD:1≤ D)(hc:0< c)(hcapacity:D^(1+c)≤ H)(hb:0≤ b)
    (hW:∀x,W x≠0→x≤ b)
    (j:Ideal O)(hj:j∈idealDivisors (∏P∈excluded data,P))
    (rows:Finset NonzeroElement)(hrows:∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤ H):
    (∑u∈rows,‖polynomial ((data.character u).excludePrimes (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data))) true W (D/(j.absNorm:ℝ)) sigma freq‖^2)
      ≤ smoothedEnergy Φ H (initialFunction data W H b Btree cap D sigma freq j) := by
  let F:=CanonicalRowCompletion.outsideSquarefreeIdeals (excluded data) (completeCutoff H b Btree cap)
  let f:=initialFunction data W H b Btree cap D sigma freq j
  have hFa:∀I∈F,Admissible I:=fun I hI => (admissible_iff_native I).mpr
    (CanonicalRowCompletion.outsideSquarefree_admissible _ _
      (reflectionExcludedPrimes_bad (basePeriod data)) I hI)
  have hs:Summable (fun u:O=> radialWeight Φ H u*‖f u‖^2):=
    (original_smoothed_overlap_triangle F admissible_one
      (fun I hI _=> admissible_supported (hFa I hI))
      (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1) (twistedProfile W sigma freq)
      (zero_lt_one.trans hH) (Real.logb H (D/(j.absNorm:ℝ))) 0 (fun _=>0)
      Φ (fun x _=> hΦ x) (zero_lt_one.trans hH)).1
  have he (u:NonzeroElement)(hu:u∈rows):
      ‖polynomial ((data.character u).excludePrimes (excluded data)
        (reflectionExcludedPrimes_prime (basePeriod data))) true W (D/(j.absNorm:ℝ)) sigma freq‖^2=
        radialWeight Φ H u.val*‖f u.val‖^2:=by
    have hn:‖ringComplex u.val‖^2/H∈Set.Icc (0:ℝ) 1:=by
      refine ⟨div_nonneg (sq_nonneg _) (zero_lt_one.trans hH).le,?_⟩
      apply (div_le_one (zero_lt_one.trans hH)).mpr
      rw [ringComplex_norm_sq_eq_absNorm_span]
      exact hrows u hu
    rw [(raw_complete_pool data H D c b Btree cap hH hD hc hcapacity hb W hW).2 j hj u sigma freq]
    change ‖f u.val‖^2=(Φ (‖ringComplex u.val‖^2/H)).re*‖f u.val‖^2
    rw [hone _ hn,Complex.one_re,one_mul]
  calc
    _=∑u∈rows,radialWeight Φ H u.val*‖f u.val‖^2:=Finset.sum_congr rfl he
    _=∑u∈rows.image Subtype.val,radialWeight Φ H u*‖f u‖^2:=by
      rw [Finset.sum_image (fun a _ b _ hab=> Subtype.val_injective hab)]
    _≤∑'u:O,radialWeight Φ H u*‖f u‖^2:=hs.sum_le_tsum _
      (fun u _=> mul_nonneg (hΦ _) (sq_nonneg _))
    _=_:=rfl

theorem raw_rows_le_initial
    (Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (data:RowData)(W:ℝ→ℂ)(H D c b Btree cap sigma freq:ℝ)
    (hH:1< H)(hD:1≤ D)(hc:0< c)(hcapacity:D^(1+c)≤ H)(hb:0≤ b)
    (hW:∀x,W x≠0→x≤ b)
    (rows:Finset NonzeroElement)(hrows:∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤ H):
    (∑u∈rows,‖polynomial (data.character u) true W D sigma freq‖^2)≤
      ((idealDivisors (∏P∈excluded data,P)).card:ℝ)*
        ∑j∈idealDivisors (∏P∈excluded data,P),
          smoothedEnergy Φ H (initialFunction data W H b Btree cap D sigma freq j) := by
  have hd:=marked_family rows data.character (excluded data)
    (reflectionExcludedPrimes_prime (basePeriod data)) W D sigma freq b
    (zero_lt_one.trans_le hD) hW (fun _=>1) (fun _=>1) (by intros;norm_num)
  simp only [mul_one,one_mul] at hd
  apply hd.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro j hj
  exact deleted_rows_le_initial Φ hΦ hone data W H D c b Btree cap sigma freq
    hH hD hc hcapacity hb hW j hj rows hrows

end DetectorDictionaryInverseRawInitialEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators
namespace DetectorDictionaryInverseRawInput
open CompletedGauss
open Eisenstein CanonicalRowCompletion CanonicalQuadraticSieve 
open  FirstPassCubeLabels SecondPassArithmetic 
open InverseInitialArithmetic InverseInitialRayAttachment InverseInitialConjugateEnergy
open InverseInitialPoissonBridge InverseInitialExcludedPool
open UniqueFactorizationMonoid
local notation "O"=> Eisenstein.O

private theorem admissible_one : Admissible (1:Ideal O):=by
  refine ⟨one_ne_zero,squarefree_one,?_⟩
  simp only [normalizedFactors_one,Multiset.notMem_zero,false_implies,forall_const]

theorem input_generator_one (F:Finset (Ideal O))(hF:∀I∈F,quadraticIdealAdmissible I)
    (η:O→*ℂ)(H:Finset (primePool F)→ℂ)(u:O):
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=> by rw [poolPrimary_span F hF i];infer_instance;
    inputConjugateRow (poolPrimary F) (fun i => complexSexticChar (Ideal.span {poolPrimary F i}) (poolPrimary_good F hF i)) Finset.univ η
      (primaryIdealGenerator (1:Ideal O)) 1 1 H u=
    inputConjugateRow (poolPrimary F) (fun i => complexSexticChar (Ideal.span {poolPrimary F i}) (poolPrimary_good F hF i)) Finset.univ η 1 1 1 H u := by
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=> by rw [poolPrimary_span F hF i];infer_instance
  simp only [primaryIdealGenerator_one]

theorem complete_pool_selector (E:Finset (Ideal O))(hE:∀P∈E,Prime P)
    (Dpool:ℕ)(hbad:fixedBadPrimes⊆E)(W:ℝ→ℂ)(b Z r:ℝ)
    (hZ:0< Z)(hW:∀x,W x≠0→x≤ b)(hbudget:b*Z^r≤(Dpool:ℝ)):
    let F:=CanonicalRowCompletion.outsideSquarefreeIdeals E Dpool;
    ∀A:Finset (primePool F),
      (if (∏i∈A,i.val)∈F then W (((∏i∈A,i.val).absNorm:ℝ)/Z^r) else 0)=
        W (((∏i∈A,i.val).absNorm:ℝ)/Z^r) := by
  intro F A
  have hF := CanonicalRowCompletion.outsideSquarefree_admissible E Dpool hbad
  simpa only [F,CanonicalRowCompletion.selectedIdealTest,
    CanonicalRowCompletion.poolPrimary_norm _ hF] using
    CanonicalRowCompletion.selectedIdealTest_outside E Dpool hbad hE W b
      (Z^r) (Real.rpow_pos_of_pos hZ r) hW hbudget A

theorem original_complete_star_input
    (E:Finset (Ideal O))(hE:∀P∈E,Prime P)(Dpool:ℕ)(hbad:fixedBadPrimes⊆E)
    (η:Ideal O→*ℂ)(W:ℝ→ℂ)(b Z r:ℝ)(hZ:0< Z)
    (hW:∀x,W x≠0→x≤ b)(hbudget:b*Z^r≤(Dpool:ℝ))(u:O):
    let F:=CanonicalRowCompletion.outsideSquarefreeIdeals E Dpool;
    let hF:=CanonicalRowCompletion.outsideSquarefree_admissible E Dpool hbad;
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=> by rw [poolPrimary_span F hF i];infer_instance;
    star (originalTotalPolynomial F 1 η (fun _=>1) W Z r 0 u)=
      ((Z^(-r/2):ℝ):ℂ)*inputConjugateRow (poolPrimary F) (fun i => complexSexticChar (Ideal.span {poolPrimary F i}) (poolPrimary_good F hF i))
        Finset.univ (elementCharacter (conjugateIdealCharacter η)) 1 1 1
        (initialTest (poolPrimary F) (fun _=>1) (fun x=> star (W x)) Z r) u:=by
  intro F hF
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=> by rw [poolPrimary_span F hF i];infer_instance
  have he:=selected_conjugate_row F (fun I hI => (admissible_iff_native I).mpr (hF I hI)) 1 admissible_one (fun _ _=> isCoprime_one_right)
    (conjugateIdealCharacter η) (fun I=> star (W ((I.absNorm:ℝ)/Z^r))) u
  dsimp only at he
  rw [input_generator_one F hF] at he
  have hselector:(fun A:Finset (primePool F)=>
      if (∏i∈A,i.val)∈F then star (W (((∏i∈A,i.val).absNorm:ℝ)/Z^r)) else 0)=
      initialTest (poolPrimary F) (fun _=>1) (fun x=> star (W x)) Z r:=by
    funext A
    rw [complete_pool_selector E hE Dpool hbad (fun x=> star (W x)) b Z r hZ
      (fun x hx=> hW x (by simpa only [star_ne_zero] using hx)) hbudget]
    simp only [initialTest,one_mul,CanonicalRowCompletion.poolPrimary_norm F hF]
    rfl
  rw [hselector] at he
  rw [←he]
  unfold originalTotalPolynomial
  have hscalar:star ((Z^(-r/2):ℝ):ℂ)=((Z^(-r/2):ℝ):ℂ):=by simp
  simp only [add_zero,map_one,mul_one,star_mul,star_sum,hscalar,
    conjugateIdealCharacter_apply,heckeIdealCharacter_apply]
  rw [mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  simp only [star_intCast]
  ring

theorem original_complete_child_norm
    (E:Finset (Ideal O))(hE:∀P∈E,Prime P)(Dpool:ℕ)(hbad:fixedBadPrimes⊆E)
    (η:Ideal O→*ℂ)(W:ℝ→ℂ)(b Z r t:ℝ)(hZ:0< Z)
    (hW:∀x,W x≠0→x≤ b)(hbudget:b*Z^r≤(Dpool:ℝ))(u:O):
    let F:=CanonicalRowCompletion.outsideSquarefreeIdeals E Dpool;
    let hF:=CanonicalRowCompletion.outsideSquarefree_admissible E Dpool hbad;
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=> by rw [poolPrimary_span F hF i];infer_instance;
    ‖originalTotalPolynomial F 1 η (fun _=>1) (InverseMoment.childLogTest W t) Z r 0 u‖^2=
      ‖((Z^(-r/2):ℝ):ℂ)*inputConjugateRow (poolPrimary F) (fun i => complexSexticChar (Ideal.span {poolPrimary F i}) (poolPrimary_good F hF i))
        Finset.univ (elementCharacter (conjugateIdealCharacter η)) 1 1 1
        (initialTest (poolPrimary F) (fun _=>1)
          (InverseMoment.childLogTest (fun x=> star (W x)) (-t)) Z r) u‖^2:=by
  intro F hF
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=> by rw [poolPrimary_span F hF i];infer_instance
  have hw:∀x,InverseMoment.childLogTest W t x≠0→x≤ b:=by
    intro x hx
    exact hW x ((mul_ne_zero_iff.mp hx).1)
  have he:=original_complete_star_input E hE Dpool hbad η
    (InverseMoment.childLogTest W t) b Z r hZ hw hbudget u
  dsimp only at he
  rw [DetectorDictionaryInverseRawConjugateGates.childLogTest_conjugate] at he
  have hn:=congrArg (fun z:ℂ=>‖z‖^2) he
  simpa only [norm_star] using hn

end DetectorDictionaryInverseRawInput

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators SchwartzMap Topology
open Filter
namespace DetectorDictionaryInverseRawReference
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open Eisenstein  
open CanonicalRowCompletion CanonicalCoefficientClass CanonicalQuadraticSieve
open InverseInitialRawDictionary InverseInitialConjugateEnergy InverseInitialExcludedPeriod
open InverseInitialRayAttachment InverseInitialProfileBounds
open DetectorDictionaryInverseRawInitialGates DetectorDictionaryInverseRawInitialEnergy
open DetectorDictionaryInverseRawInput DetectorDictionaryInverseRawInputBound
open DetectorDictionaryInverseRawConjugateGates DetectorDictionaryInverseRawRealRadial
open DetectorDictionaryInverseRawGeometry 
local notation "O"=> Eisenstein.O

theorem raw_reference_large (W:𝓢(ℝ,ℂ))(a b c κ:ℝ)(ha:0< a)(hb:0< b)
    (hs:Function.support W⊆Set.Icc a b)(hc:0< c)(hκ:0<κ):
    ∃J:ℕ,∀data:RowData,∃C H₀:ℝ,0< C ∧ 1< H₀ ∧
      ∀(t H D:ℝ),H₀≤ H→1≤ D→D^(1+c)≤ H→∀rows:Finset NonzeroElement,
      (∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤ H)→
      (∑u∈rows,‖polynomial (data.character u) true (childLogTest W t) D 0 0‖^2)≤
        (C*(1+‖t‖)^(2*J))*H*(H*max 1 D)^κ := by
  obtain ⟨Φ,hΦcompact,hΦ,hreal,hone⟩:=exists_real_raw_radial_majorant
  obtain ⟨η,τ,π,eps,hη,hτ,hπ,heps,hηone,hηgap,hτgap,hcost⟩:=
    raw_fixed_reserves c (κ/2) hc (by positivity)
  let gap:=capacityGap c/4
  have hgap:0< gap:=by dsimp [gap];exact div_pos (capacityGap_pos c hc) (by norm_num)
  have hηsmall:η≤ gap/50:=by dsimp [gap];nlinarith
  have hτsmall:τ≤ gap/50:=by dsimp [gap];nlinarith
  let Wbar:=SecondPassIntegration.conjugateProfile W
  have hsbar:Function.support Wbar⊆Set.Icc a b:=by
    intro x hx
    exact hs (by simpa only [Wbar,Function.mem_support,SecondPassIntegration.conjugateProfile_apply,star_ne_zero] using hx)
  obtain ⟨J,Btree,hBtree,hinput⟩:=raw_input_bound Wbar a b ha hsbar Φ
    gap eps π η τ (κ/4) hgap heps hπ hη hηone hηsmall hτ hτsmall (by positivity)
  refine ⟨J,?_⟩
  intro data
  obtain ⟨hq,hqset,hn,hperiod⟩:=raw_conjugate_base_gates data
  obtain ⟨C,Hq,hC,hHq,hinput⟩:=hinput (deletedPeriod (basePeriod data)) hq
  obtain ⟨Hg,hg⟩:=eventually_atTop.mp (shifted_raw_geometry_eventually data c η hc hη)
  let T:=idealDivisors (∏P∈excluded data,P)
  let Ctotal:=((T.card:ℝ)+1)^2*C
  refine ⟨Ctotal,max Hq Hg,by dsimp [Ctotal];positivity,lt_max_of_lt_left hHq,?_⟩
  intro t H D hH hD hcapacity rows hrows
  have hHq':Hq≤ H:=(le_max_left _ _).trans hH
  obtain ⟨hHp,hgeom⟩:=hg H ((le_max_right _ _).trans hH)
  have hHpos:0< H:=zero_lt_one.trans hHp
  have hWt:∀x,childLogTest W t x≠0→x≤ b:=by
    intro x hx
    exact (hs ((mul_ne_zero_iff.mp hx).1)).2
  have hraw:=raw_rows_le_initial Φ hΦ hone data (childLogTest W t) H D c b Btree 2 0 0
    hHp hD hc hcapacity hb.le hWt rows hrows
  have hterm (j:Ideal O)(hj:j∈T):
      smoothedEnergy Φ H (initialFunction data (childLogTest W t) H b Btree 2 D 0 0 j)≤
        C*H^(1+15*η+π+eps+κ/4)*(1+‖t‖)^(2*J):=by
    obtain ⟨hrlo,hr₁,hr₂,hex,hrcap,hDH⟩:=hgeom D hD hcapacity j hj
    let r:=Real.logb H (D/(j.absNorm:ℝ))
    let Dpool:=completeCutoff H b Btree 2
    have hpool:Btree*H^3≤(Dpool:ℝ):=by
      convert completeCutoff_tree H b Btree 2 using 1 <;> norm_num
    have hbcover:b*H^r≤(Dpool:ℝ):=by
      rw [hex]
      exact completeCutoff_columns H b Btree 2 D _ hb.le (zero_lt_one.trans_le hD).le hDH
        (excluded_divisor_norm data j hj).1
    have hbound:=hinput H hHq' Dpool hpool
      (elementCharacter (conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom))
      hn hperiod r (-t) (by dsimp [r];linarith)
      (by dsimp [gap] at *;linarith [(capacityGap_pos c hc).le])
      (by dsimp [gap] at *;linarith [(capacityGap_pos c hc).le])
      (by have hh:=capacityGap_lt_one c hc;linarith)
    let F:=CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes (deletedPeriod (basePeriod data))) Dpool
    let hF:=CanonicalRowCompletion.outsideSquarefree_admissible (reflectionExcludedPrimes (deletedPeriod (basePeriod data))) Dpool
      (reflectionExcludedPrimes_bad (deletedPeriod (basePeriod data)))
    let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=> by
      rw [poolPrimary_span F hF i];infer_instance
    have hf:initialFunction data (childLogTest W t) H b Btree 2 D 0 0 j=
        originalTotalPolynomial F 1 (idealCoeff (deletedBase data)).toMonoidHom
          (fun _=>1) (childLogTest W t) H r 0:=by
      unfold initialFunction
      dsimp only [F]
      rw [hqset]
      congr 1
      funext x
      simp [twistedProfile,HeckeDyadic.shift]
    rw [hf,smoothedEnergy_eq_complex_norm Φ hΦ hreal H hHpos]
    have he: (∑'u:O,Φ (‖ringComplex u‖^2/H)*
        (‖originalTotalPolynomial F 1 (idealCoeff (deletedBase data)).toMonoidHom
          (fun _=>1) (childLogTest W t) H r 0 u‖^2:ℝ))=
        (∑'u:O,Φ (‖ringComplex u‖^2/H)*
        (‖((H^(-r/2):ℝ):ℂ)*SecondPassArithmetic.inputConjugateRow
          (poolPrimary F) (fun i => complexSexticChar (Ideal.span {poolPrimary F i})
            (poolPrimary_good F hF i))
          Finset.univ (elementCharacter (conjugateIdealCharacter
            (idealCoeff (deletedBase data)).toMonoidHom)) 1 1 1
          (initialTest (poolPrimary F) (fun _=>1) (childLogTest Wbar (-t)) H r) u‖^2:ℝ)):=by
      apply tsum_congr
      intro u
      congr 2
      exact original_complete_child_norm (reflectionExcludedPrimes (deletedPeriod (basePeriod data)))
        (reflectionExcludedPrimes_prime (deletedPeriod (basePeriod data))) Dpool
        (reflectionExcludedPrimes_bad (deletedPeriod (basePeriod data))) _ W b H r t hHpos
        (fun x hx=>(hs hx).2) hbcover u
    rw [he]
    simpa only [norm_neg] using hbound
  apply hraw.trans
  calc
    _≤(T.card:ℝ)*∑j∈T,C*H^(1+15*η+π+eps+κ/4)*(1+‖t‖)^(2*J):=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (Nat.cast_nonneg _)
    _=(T.card:ℝ)^2*C*H^(1+15*η+π+eps+κ/4)*(1+‖t‖)^(2*J):=by
      simp only [Finset.sum_const,nsmul_eq_mul];ring
    _≤ Ctotal*H^(1+15*η+π+eps+κ/4)*(1+‖t‖)^(2*J):=by
      dsimp [Ctotal]
      gcongr
      nlinarith [Nat.cast_nonneg (α:=ℝ) T.card]
    _≤(Ctotal*(1+‖t‖)^(2*J))*H*(H*max 1 D)^κ:=by
      have he:15*η+π+eps+κ/4≤κ:=by linarith
      have hh:=raw_output_budget H D κ (15*η+π+eps+κ/4) hHp.le hκ.le he
      rw [show (1+15*η+π+eps+κ/4:ℝ)=1+(15*η+π+eps+κ/4) by ring]
      nlinarith [mul_le_mul_of_nonneg_left hh
        (show 0≤ Ctotal*(1+‖t‖)^(2*J) by dsimp [Ctotal];positivity)]

theorem raw_reference_moment (W:𝓢(ℝ,ℂ))(a b c κ:ℝ)(ha:0< a)(hb:0< b)
    (hs:Function.support W⊆Set.Icc a b)(hc:0< c)(hκ:0<κ):
    ∃J:ℕ,∀data:RowData,∃C:ℝ,0< C ∧ ∀t:ℝ,
      RawMoment data (childLogTest W t) c κ (C*(1+‖t‖)^(2*J)) := by
  obtain ⟨J,hlarge⟩:=raw_reference_large W a b c κ ha hb hs hc hκ
  refine ⟨J,?_⟩
  intro data
  obtain ⟨C,H₀,hC,hH₀,hlarge⟩:=hlarge data
  obtain ⟨C₀,hC₀,hcomplete⟩:=DetectorDictionaryInverseRawCompact.rawMoment_of_large_rows_ge_one
    W a b ha hs H₀ hH₀.le
  refine ⟨C+C₀,add_pos hC hC₀,?_⟩
  exact hcomplete data c κ C J hc.le hκ.le hC.le hlarge

end DetectorDictionaryInverseRawReference

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Set

namespace DetectorDictionaryInverseUniform
open HeckeInverseAmplification HeckeDetectorCoefficientTransfer HeckeDetectorDyadicProfiles
open HeckeDetectorRowwisePolynomial CenteredMomentDetectorDictionary

lemma logTest_apply (W : ℝ→ℂ) (n : ℕ) (x : ℝ) :
    logTest W n x=(Real.log x:ℂ)^n*W x := by
  induction n with
  | zero => simp [logTest]
  | succ n ih => simp only [logTest,logProfile,ih,pow_succ];ring

def baseProfile (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (R : ℝ) : ℝ→ℂ :=
  logTest (orientedProfile reverse (ratioProfile V W R)) n

lemma baseProfile_support (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (R : ℝ) :
    Function.support (baseProfile reverse n V W R)⊆Function.support W := by
  apply (logTest_support _ _).trans
  cases reverse
  · exact ratioProfile_support V W R
  · rw [orientedProfile,if_pos rfl,conjugate_profile_support]
    exact ratioProfile_support V W R

lemma baseProfile_smooth (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (R a b : ℝ)
    (ha : 0< a) (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W⊆Icc a b) : ContDiff ℝ ∞ (baseProfile reverse n V W R) := by
  apply logTest_smooth _ n a b ha
  · cases reverse
    · exact (ratioProfile_support V W R).trans hs
    · rw [orientedProfile,if_pos rfl,conjugate_profile_support]
      exact (ratioProfile_support V W R).trans hs
  · have hv : ContDiff ℝ ∞ (ratioProfile V W R) :=
      (hV.comp (by fun_prop)).mul hW
    cases reverse
    · exact hv
    · exact conjugate_profile_smooth _ hv

def inverseLogFamily (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (p : ℝ×ℝ) (x : ℝ) : ℂ :=
  Real.exp (-p.1*x) • ((x:ℂ)^n*
    (orientedProfile reverse V (p.2*Real.exp x)*orientedProfile reverse W (Real.exp x)))

lemma inverseLogFamily_smooth (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (Function.uncurry (inverseLogFamily reverse n V W)) := by
  have hv : ContDiff ℝ ∞ (orientedProfile reverse V) := by
    cases reverse
    · exact hV
    · exact conjugate_profile_smooth _ hV
  have hw : ContDiff ℝ ∞ (orientedProfile reverse W) := by
    cases reverse
    · exact hW
    · exact conjugate_profile_smooth _ hW
  unfold inverseLogFamily Function.uncurry
  exact (by fun_prop : ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ=> Real.exp (-p.1.1*p.2))).smul
    (((Complex.ofRealCLM.contDiff.comp (contDiff_snd : ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ=> p.2))).pow n).mul
      ((hv.comp (by fun_prop)).mul (hw.comp (by fun_prop))))

lemma inverseLogFamily_eq (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (p : ℝ×ℝ) (x : ℝ) :
    inverseLogFamily reverse n V W p x=realInterpolatedLog (baseProfile reverse n V W p.2) p x := by
  unfold inverseLogFamily realInterpolatedLog baseProfile
  rw [logTest_apply,Real.log_exp]
  cases reverse <;> simp [orientedProfile,ratioProfile,map_mul]

lemma inverseLogFamily_support (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (a b : ℝ)
    (ha : 0< a) (hs : Function.support W⊆Icc a b) (p : ℝ×ℝ) :
    Function.support (inverseLogFamily reverse n V W p)⊆Icc (-(|Real.log a|+|Real.log b|)) (|Real.log a|+|Real.log b|) := by
  have he : inverseLogFamily reverse n V W p=realInterpolatedLog (baseProfile reverse n V W p.2) p :=
    funext (inverseLogFamily_eq reverse n V W p)
  rw [he]
  exact realInterpolatedLog_support _ a b ha ((baseProfile_support reverse n V W p.2).trans hs) p

end DetectorDictionaryInverseUniform

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace DetectorDictionaryInverseUniform
open HeckeInverseAmplification HeckeDyadic JointLogSeparation CenteredMomentDetectorDictionary

def inverseLogSchwartz (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (a b : ℝ) (ha : 0< a)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (hs : Function.support W⊆Icc a b)
    (p : ℝ×ℝ) : 𝓢(ℝ,ℂ) :=
  realInterpolatedLogSchwartz (baseProfile reverse n V W p.2) a b ha
    ((baseProfile_support reverse n V W p.2).trans hs)
    (baseProfile_smooth reverse n V W p.2 a b ha hV hW hs) p

lemma inverseLogSchwartz_apply (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (a b : ℝ) (ha : 0< a)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (hs : Function.support W⊆Icc a b)
    (p : ℝ×ℝ) (x : ℝ) :
    inverseLogSchwartz reverse n V W a b ha hV hW hs p x=inverseLogFamily reverse n V W p x := by
  rw [inverseLogSchwartz,realInterpolatedLogSchwartz_apply,inverseLogFamily_eq]

def inverseSchwartz (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (a b : ℝ) (ha : 0< a)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (hs : Function.support W⊆Icc a b)
    (R σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  interpolatedProfile (baseProfile reverse n V W R) a b ha
    ((baseProfile_support reverse n V W R).trans hs)
    (baseProfile_smooth reverse n V W R a b ha hV hW hs) σ t

lemma inverseSchwartz_apply (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (a b : ℝ) (ha : 0< a)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (hs : Function.support W⊆Icc a b)
    (R σ t x : ℝ) :
    inverseSchwartz reverse n V W a b ha hV hW hs R σ t x=
      twistProfile (baseProfile reverse n V W R) σ t x :=
  interpolatedProfile_apply _ _ _ _ _ _ _ _ _

theorem inverseSchwartz_operator_uniform (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ)
    (a b : ℝ) (ha : 0< a) (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W⊆Icc a b) (Rmax : ℝ)
    (op : 𝓢(ℝ,ℂ)→L[ℝ]𝓢(ℝ,ℂ)) (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0< C ∧ ∀R∈Icc (0:ℝ) Rmax,∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (op (inverseSchwartz reverse n V W a b ha hV hW hs R σ t))≤ C*(1+‖t‖)^J := by
  obtain ⟨T,A,hA,hcontrol⟩ := SchwartzPlanePoisson.schwartzCLM_finite_seminorm_control
    (op.comp (CompletedHeight.fixedLogReturnCLM a b ha)) S
  obtain ⟨J,B,hB,hbound⟩ := compact_family_frequencyTwist
    (inverseLogFamily reverse n V W) (inverseLogFamily_smooth reverse n V W hV hW)
    (|Real.log a|+|Real.log b|) (by positivity) (inverseLogFamily_support reverse n V W a b ha hs)
    (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) Rmax) (isCompact_Icc.prod isCompact_Icc)
    (inverseLogSchwartz reverse n V W a b ha hV hW hs)
    (inverseLogSchwartz_apply reverse n V W a b ha hV hW hs) T
  refine ⟨J,A*B,mul_pos hA hB,?_⟩
  intro R hR σ hσ t
  have hp : (σ,R)∈Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) Rmax := ⟨hσ,hR⟩
  have hheight : ‖t/(2*Real.pi)‖≤‖t‖ := by
    rw [norm_div,Real.norm_of_nonneg (by positivity : 0≤2*Real.pi)]
    exact div_le_self (norm_nonneg _) (by linarith [Real.pi_gt_three])
  have hh := hcontrol (frequencyTwist (inverseLogSchwartz reverse n V W a b ha hV hW hs (σ,R)) (t/(2*Real.pi)))
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (op (inverseSchwartz reverse n V W a b ha hV hW hs R σ t))≤ _ at hh
  apply hh.trans
  have hb : T.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (frequencyTwist (inverseLogSchwartz reverse n V W a b ha hV hW hs (σ,R)) (t/(2*Real.pi)))≤ B*(1+‖t‖)^J :=
    (hbound (σ,R) hp (t/(2*Real.pi))).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) J) hB.le)
  exact (mul_le_mul_of_nonneg_left hb hA.le).trans_eq (by ring)

end DetectorDictionaryInverseUniform

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace DetectorDictionaryInverseUniform
open HeckeInverseAmplification HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles

def sourceOperator (scaled : Bool) : 𝓢(ℝ,ℂ)→L[ℝ]𝓢(ℝ,ℂ) :=
  if scaled then scaleCLM else ContinuousLinearMap.id ℝ _

def inverseDetectorSchwartz (reverse : Bool) (n : ℕ) (R σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  inverseSchwartz reverse n cutoff positiveAnnular (1/4) (9/4) (by norm_num)
    (cutoff.smooth ⊤) positiveAnnular_smooth positiveAnnular_support R σ t

lemma inverseDetectorSchwartz_apply (reverse : Bool) (n : ℕ) (R σ t x : ℝ) :
    inverseDetectorSchwartz reverse n R σ t x=
      twistProfile (baseProfile reverse n cutoff positiveAnnular R) σ t x :=
  inverseSchwartz_apply _ _ _ _ _ _ _ _ _ _ _ _ _ _

def inverseDetectorTest (scaled reverse : Bool) (n : ℕ) (R σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  sourceOperator scaled (inverseDetectorSchwartz reverse n R σ t)

lemma inverseDetectorTest_apply (scaled reverse : Bool) (n : ℕ) (R σ t x : ℝ) :
    inverseDetectorTest scaled reverse n R σ t x=
      if scaled then scaleProfile (twistProfile (baseProfile reverse n cutoff positiveAnnular R) σ t) x
      else twistProfile (baseProfile reverse n cutoff positiveAnnular R) σ t x := by
  have he : (inverseDetectorSchwartz reverse n R σ t : ℝ→ℂ)=
      twistProfile (baseProfile reverse n cutoff positiveAnnular R) σ t :=
    funext (inverseDetectorSchwartz_apply reverse n R σ t)
  cases scaled
  · exact inverseDetectorSchwartz_apply _ _ _ _ _ _
  · change scaleCLM (inverseDetectorSchwartz reverse n R σ t) x=_
    rw [scaleCLM_apply,he]
    rfl

theorem inverseDetectorTest_uniform (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0< C ∧ ∀scaled reverse : Bool,∀n : ℕ,n≤2→
      ∀R∈Icc (0:ℝ) 4,∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (inverseDetectorTest scaled reverse n R σ t)≤ C*(1+‖t‖)^J := by
  choose degree C hC hb using fun q : Bool×Bool×Fin 3=> inverseSchwartz_operator_uniform
    q.2.1 q.2.2.val cutoff positiveAnnular (1/4) (9/4) (by norm_num)
    (cutoff.smooth ⊤) positiveAnnular_smooth positiveAnnular_support 4 (sourceOperator q.1) S
  let J := (Finset.univ : Finset (Bool×Bool×Fin 3)).sup degree
  have hsum : 0≤∑q : Bool×Bool×Fin 3,C q := Finset.sum_nonneg (fun q _=>(hC q).le)
  refine ⟨J,1+∑q : Bool×Bool×Fin 3,C q,by linarith,?_⟩
  intro scaled reverse n hn R hR σ hσ t
  let q : Bool×Bool×Fin 3 := (scaled,reverse,⟨n,by omega⟩)
  have hCq : C q≤1+∑q : Bool×Bool×Fin 3,C q := by
    have hh := Finset.single_le_sum (fun q (_ : q∈(Finset.univ : Finset (Bool×Bool×Fin 3)))=>(hC q).le) (Finset.mem_univ q)
    linarith
  have hdegree : degree q≤ J := Finset.le_sup (Finset.mem_univ q)
  have he := hb q R hR σ hσ t
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (inverseDetectorTest scaled reverse n R σ t)≤ _ at he
  exact he.trans (mul_le_mul hCq (pow_le_pow_right₀ (by linarith [norm_nonneg t]) hdegree)
    (by positivity) (by linarith))

end DetectorDictionaryInverseUniform

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace DetectorDictionaryInverseUniform
open HeckeInverseAmplification HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial

lemma positiveAnnular_support_sharp : Function.support positiveAnnular⊆Ioo (1/2) 2 := by
  intro x hx
  have hx0 : 0≤ x := by have := (positiveAnnular_support hx).1; linarith
  have he : DyadicTransfer.annularCutoff cutoff x≠0 := by
    rwa [←positiveAnnular_eq x hx0]
  simpa using HeckeDetectorPartition.annular_support cutoff cutoff_one cutoff_zero x hx0 0 (by simpa using he)

lemma ratioProfile_zero_of_four_le (R : ℝ) (hR : 4≤ R) :
    ratioProfile cutoff positiveAnnular R=0 := by
  funext x
  by_cases hx : positiveAnnular x=0
  · simp [ratioProfile,hx]
  · have hs := positiveAnnular_support_sharp hx
    have hrx : 2≤ R*x := by nlinarith [hs.1]
    simp [ratioProfile,cutoff_zero _ hrx]

lemma inverseDetectorTest_zero_of_four_le (scaled reverse : Bool) (n : ℕ) (R σ t : ℝ)
    (hR : 4≤ R) : inverseDetectorTest scaled reverse n R σ t=0 := by
  have hz : inverseDetectorSchwartz reverse n R σ t=0 := by
    ext x
    rw [inverseDetectorSchwartz_apply]
    simp only [baseProfile,ratioProfile_zero_of_four_le R hR]
    cases reverse <;> simp [orientedProfile,twistProfile,HeckeDyadic.shift,logTest_apply]
  rw [inverseDetectorTest,hz,map_zero]

theorem inverseDetectorTest_uniform_all_ratios (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0< C ∧ ∀scaled reverse : Bool,∀n : ℕ,n≤2→
      ∀R : ℝ,0≤ R→∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (inverseDetectorTest scaled reverse n R σ t)≤ C*(1+‖t‖)^J := by
  obtain ⟨J,C,hC,hb⟩ := inverseDetectorTest_uniform S
  refine ⟨J,C,hC,?_⟩
  intro scaled reverse n hn R hR σ hσ t
  by_cases hh : R≤4
  · exact hb scaled reverse n hn R ⟨hR,hh⟩ σ hσ t
  · rw [inverseDetectorTest_zero_of_four_le _ _ _ _ _ _ (le_of_not_ge hh),map_zero]
    positivity

def inverseSourceSchwartz (scaled reverse : Bool) (n : ℕ) (U tstar r σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  inverseDetectorTest scaled reverse n (U^r/U^tstar) σ t

lemma inverseSourceSchwartz_apply (scaled reverse : Bool) (n : ℕ) (U tstar r σ t x : ℝ) :
    inverseSourceSchwartz scaled reverse n U tstar r σ t x=
      if scaled then scaleProfile (twistProfile
        (logTest (orientedProfile reverse (HeckeDetectorInverseFiberCount.inverseTest U tstar r)) n) σ t) x
      else twistProfile
        (logTest (orientedProfile reverse (HeckeDetectorInverseFiberCount.inverseTest U tstar r)) n) σ t x := by
  simp only [inverseSourceSchwartz,inverseDetectorTest_apply,baseProfile,
    HeckeDetectorInverseFiberCount.inverseTest,inverseProfile_eq_ratio]

theorem inverseSourceSchwartz_uniform (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0< C ∧ ∀scaled reverse : Bool,∀n : ℕ,n≤2→
      ∀U : ℝ,0< U→∀tstar r : ℝ,∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (inverseSourceSchwartz scaled reverse n U tstar r σ t)≤ C*(1+‖t‖)^J := by
  obtain ⟨J,C,hC,hb⟩ := inverseDetectorTest_uniform_all_ratios S
  refine ⟨J,C,hC,?_⟩
  intro scaled reverse n hn U hU tstar r σ hσ t
  exact hb scaled reverse n hn (U^r/U^tstar) (by positivity) σ hσ t

end DetectorDictionaryInverseUniform

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory JointLogSeparation

namespace DetectorDictionaryInverseClippedUniform
open DetectorDictionaryInverseUniform HeckeInverseAmplification
open InverseMoment InverseInitialClippedColumns InverseInitialOverlapFourier
open Eisenstein CompletedGauss
local notation "O" => Eisenstein.O

theorem source_support (scaled reverse : Bool) (n : ℕ) (U tstar r σ t : ℝ) :
    Function.support (inverseSourceSchwartz scaled reverse n U tstar r σ t : ℝ→ℂ) ⊆
      Set.Icc (1/4 : ℝ) (9/4) := by
  let W := inverseDetectorSchwartz reverse n (U^r/U^tstar) σ t
  have hw : Function.support (W : ℝ→ℂ) ⊆ Set.Icc (1/4 : ℝ) (9/4) := by
    have he : (W : ℝ→ℂ) = twistProfile
        (baseProfile reverse n HeckeDetectorProfiles.cutoff
          HeckeDetectorDyadicProfiles.positiveAnnular (U^r/U^tstar)) σ t := by
      funext x
      exact inverseDetectorSchwartz_apply _ _ _ _ _ _
    rw [he]
    exact (twistProfile_support _ _ _).trans
      ((baseProfile_support _ _ _ _ _).trans HeckeDetectorDyadicProfiles.positiveAnnular_support)
  have ht : tsupport (W : ℝ→ℂ) ⊆ Set.Icc (1/4 : ℝ) (9/4) :=
    closure_minimal hw isClosed_Icc
  cases scaled
  · exact hw
  · intro x hx
    by_contra hn
    have hz : W x = 0 := by
      by_contra h
      exact hn (hw h)
    have hd : deriv (W : ℝ→ℂ) x = 0 := by
      by_contra h
      exact hn (ht (support_deriv_subset h))
    apply hx
    change scaleCLM W x = 0
    rw [scaleCLM_apply]
    simp [scaleProfile, hz, hd]

theorem source_zero_of_ratio (scaled reverse : Bool) (n : ℕ) (U tstar r σ t : ℝ)
    (h : 4 ≤ U^r/U^tstar) : inverseSourceSchwartz scaled reverse n U tstar r σ t = 0 :=
  inverseDetectorTest_zero_of_four_le scaled reverse n _ σ t h

theorem exists_reference_window :
    ∃w : 𝓢(ℝ,ℂ), HasCompactSupport (w : ℝ→ℂ) ∧
      tsupport (w : ℝ→ℂ) ⊆ Set.Icc (1/18 : ℝ) (13/4) ∧
      ∀x∈Set.Icc (1/9 : ℝ) (9/4), w x = 1 := by
  obtain ⟨w,hc,hone,hs⟩ := InverseSecondChildWindows.positive_cutoff
    (1/9 : ℝ) (9/4) (by norm_num) (by norm_num)
  refine ⟨w,hc,?_,hone⟩
  convert hs using 1 <;> norm_num

def referenceWindow : 𝓢(ℝ,ℂ) := Classical.choose exists_reference_window

theorem referenceWindow_compact : HasCompactSupport (referenceWindow : ℝ→ℂ) :=
  (Classical.choose_spec exists_reference_window).1

theorem referenceWindow_support : tsupport (referenceWindow : ℝ→ℂ) ⊆
    Set.Icc (1/18 : ℝ) (13/4) :=
  (Classical.choose_spec exists_reference_window).2.1

theorem referenceWindow_one (x : ℝ) (hx : x∈Set.Icc (1/9 : ℝ) (9/4)) :
    referenceWindow x = 1 :=
  (Classical.choose_spec exists_reference_window).2.2 x hx

theorem referenceWindow_agrees (scaled reverse : Bool) (n : ℕ) (U tstar r σ t c y : ℝ)
    (hc : 1≤ c) (hcb : c≤9/4) (hy : 0< y) :
    referenceWindow y * inverseSourceSchwartz scaled reverse n U tstar r σ t (c*y) =
      inverseSourceSchwartz scaled reverse n U tstar r σ t (c*y) := by
  by_cases hz : inverseSourceSchwartz scaled reverse n U tstar r σ t (c*y) = 0
  · simp [hz]
  have hs := source_support scaled reverse n U tstar r σ t hz
  have hh : y∈Set.Icc (1/9 : ℝ) (9/4) := by
    constructor <;> nlinarith [hs.1,hs.2]
  rw [referenceWindow_one y hh,one_mul]

def logSource (scaled reverse : Bool) (n : ℕ) (U tstar r σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  CompletedHeight.logPullbackCLM (1/4) (9/4)
    (inverseSourceSchwartz scaled reverse n U tstar r σ t)

theorem logSource_apply (scaled reverse : Bool) (n : ℕ) (U tstar r σ t x : ℝ) :
    logSource scaled reverse n U tstar r σ t x =
      inverseSourceSchwartz scaled reverse n U tstar r σ t (Real.exp x) :=
  CompletedHeight.logPullbackCLM_eq_actual _ _ (by norm_num) _
    (source_support scaled reverse n U tstar r σ t) x

theorem logSource_eq_kernelLogSource (scaled reverse : Bool) (n : ℕ) (U tstar r σ t : ℝ) :
    logSource scaled reverse n U tstar r σ t =
      kernelLogSource (inverseSourceSchwartz scaled reverse n U tstar r σ t)
        (1/4) (9/4) (by norm_num) (source_support scaled reverse n U tstar r σ t)
        ((inverseSourceSchwartz scaled reverse n U tstar r σ t).smooth ⊤) := by
  ext x
  rw [logSource_apply,kernelLogSource_apply]

def familyDensity (scaled reverse : Bool) (n : ℕ) (U tstar r σ t c v : ℝ) : ℂ :=
  density (logSource scaled reverse n U tstar r σ t) (Real.log c) v

theorem familyDensity_formula (scaled reverse : Bool) (n : ℕ) (U tstar r σ t c v : ℝ) :
    familyDensity scaled reverse n U tstar r σ t c v =
      (𝓕 (logSource scaled reverse n U tstar r σ t)) v * kernelLogPhase v (Real.log c) := rfl

theorem familyDensity_norm (scaled reverse : Bool) (n : ℕ) (U tstar r σ t c v : ℝ) :
    ‖familyDensity scaled reverse n U tstar r σ t c v‖ =
      ‖(𝓕 (logSource scaled reverse n U tstar r σ t)) v‖ := density_norm _ _ _

theorem familyDensity_integrable (J : ℕ) (scaled reverse : Bool) (n : ℕ)
    (U tstar r σ t c : ℝ) :
    Integrable (fun v : ℝ => (1+‖v‖)^J * ‖familyDensity scaled reverse n U tstar r σ t c v‖) := by
  simp only [familyDensity_norm]
  exact JointLogSeparation.schwartz_fourier_one_plus_integrable _ _

theorem familyDensity_moment (J : ℕ) :
    ∃K : ℕ, ∃C : ℝ, 0< C ∧ ∀scaled reverse : Bool, ∀n : ℕ, n≤2 →
      ∀U : ℝ, 0< U → ∀tstar r : ℝ, ∀σ∈Set.Icc (0 : ℝ) 1, ∀t c : ℝ,
      (∫v : ℝ, (1+‖v‖)^J * ‖familyDensity scaled reverse n U tstar r σ t c v‖) ≤
        C*(1+‖t‖)^K := by
  let p := (volume : Measure ℝ).integrablePower
  let S : Finset (ℕ×ℕ) := Finset.Iic (p,J+p)
  obtain ⟨T,A,hA,hop⟩ := SchwartzPlanePoisson.schwartzCLM_finite_seminorm_control
    (CompletedHeight.logPullbackCLM (1/4) (9/4)) S
  obtain ⟨K,B,hB,hsource⟩ := inverseSourceSchwartz_uniform T
  let C := 1+(2 : ℝ)^J*(coefficientMomentBound 0 (2*A*B)+coefficientMomentBound J (2*A*B))
  have hC : 0< C := by
    have h₀ := coefficientMomentBound_nonneg 0 (2*A*B) (by positivity)
    have hJ := coefficientMomentBound_nonneg J (2*A*B) (by positivity)
    dsimp [C]
    positivity
  refine ⟨K,C,hC,?_⟩
  intro scaled reverse n hn U hU tstar r σ hσ t c
  let W := inverseSourceSchwartz scaled reverse n U tstar r σ t
  let g := logSource scaled reverse n U tstar r σ t
  have hb : S.sup (schwartzSeminormFamily ℝ ℝ ℂ) g ≤ A*B*(1+‖t‖)^K := by
    exact (hop W).trans ((mul_le_mul_of_nonneg_left
      (hsource scaled reverse n hn U hU tstar r σ hσ t) hA.le).trans_eq (by ring))
  have hs (i : ℕ) (hi : i≤ J+p) :
      (SchwartzMap.seminorm ℝ 0 i) g + (SchwartzMap.seminorm ℝ p i) g ≤
        2*A*B*(1+‖t‖)^K := by
    have h₀ : schwartzSeminormFamily ℝ ℝ ℂ (0,i) ≤ S.sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
      Finset.le_sup (f:=schwartzSeminormFamily ℝ ℝ ℂ) (by simp [S,hi])
    have hp : schwartzSeminormFamily ℝ ℝ ℂ (p,i) ≤ S.sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
      Finset.le_sup (f:=schwartzSeminormFamily ℝ ℝ ℂ) (by simp [S,hi])
    have h₁ := (Seminorm.le_def.mp h₀ g).trans hb
    have h₂ := (Seminorm.le_def.mp hp g).trans hb
    change (SchwartzMap.seminorm ℝ 0 i) g ≤ _ at h₁
    change (SchwartzMap.seminorm ℝ p i) g ≤ _ at h₂
    linarith
  have hmoment := uniform_fourier_one_plus_moment g J 1
    (2*A*B*(1+‖t‖)^K) (by norm_num) (by positivity)
    (by intro i hi; simpa only [one_mul] using hs i hi)
  simp only [one_mul] at hmoment
  simp only [familyDensity_norm]
  apply hmoment.trans
  have he : (2 : ℝ)^J*(coefficientMomentBound 0 (2*A*B*(1+‖t‖)^K)+
      coefficientMomentBound J (2*A*B*(1+‖t‖)^K)) =
      ((2 : ℝ)^J*(coefficientMomentBound 0 (2*A*B)+coefficientMomentBound J (2*A*B)))*(1+‖t‖)^K := by
    unfold coefficientMomentBound
    ring
  rw [he]
  dsimp [C]
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)


end DetectorDictionaryInverseClippedUniform
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory
namespace DetectorDictionaryInverseRawUniform
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open DetectorDictionaryInverseUniform DetectorDictionaryInverseClippedUniform
open DetectorDictionaryInverseRawFourier

private theorem rawMoment_mono (data : RowData) (W : ℝ→ℂ) (c κ A B : ℝ)
    (hAB : A≤ B) (h : RawMoment data W c κ A) : RawMoment data W c κ B := by
  intro H D hH hD hHD rows hrows
  apply (h H D hH hD hHD rows hrows).trans
  gcongr

theorem raw_family_uniform (J : ℕ) :
    ∃K : ℕ,∃C : ℝ,0< C ∧ ∀(data : RowData)(c κ A : ℝ),0≤ A →
      (∀s,RawMoment data (childLogTest referenceWindow s) c κ (A*(1+‖s‖)^(2*J))) →
      ∀scaled reverse : Bool,∀n : ℕ,n≤2 → ∀U : ℝ,0< U →
      ∀tstar r : ℝ,∀σ∈Set.Icc (0:ℝ) 1,∀t : ℝ,
      RawMoment data (inverseSourceSchwartz scaled reverse n U tstar r σ t)
        c κ (A*C*(1+‖t‖)^K) := by
  obtain ⟨K,B,hB,hmass⟩:=familyDensity_moment J
  refine ⟨2*K,B^2,sq_pos_of_pos hB,?_⟩
  intro data c κ A hA href scaled reverse n hn U hU tstar r σ hσ t
  let W:=inverseSourceSchwartz scaled reverse n U tstar r σ t
  let hs:=source_support scaled reverse n U tstar r σ t
  let g:=kernelLogSource W (1/4) (9/4) (by norm_num) hs (W.smooth ⊤)
  have hw : ∀x,referenceWindow x≠0 → x≤(13/4:ℝ) := by
    intro x hx
    exact (referenceWindow_support (subset_tsupport _ hx)).2
  have hagree : ∀y,0< y → referenceWindow y*W y=W y := by
    intro y hy
    simpa only [one_mul,W] using referenceWindow_agrees scaled reverse n U tstar r σ t 1 y
      (by norm_num) (by norm_num) hy
  have hh:=rawMoment_reference data W (1/4) (9/4) (by norm_num) hs (W.smooth ⊤)
    referenceWindow (13/4) c κ A J hA hw hagree href
  have hm : (∫v:ℝ,(1+‖v‖)^J*‖(𝓕 g) v‖)≤ B*(1+‖t‖)^K := by
    have hb:=hmass scaled reverse n hn U hU tstar r σ hσ t 1
    simpa only [familyDensity_norm,logSource_eq_kernelLogSource,g,W,hs] using hb
  apply rawMoment_mono data W c κ _ _ _ hh
  change A*(∫v:ℝ,(1+‖v‖)^J*‖(𝓕 g) v‖)^2≤ _
  calc
    _≤ A*(B*(1+‖t‖)^K)^2:=mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (integral_nonneg (fun _=> by positivity)) hm 2) hA
    _= _:=by simp only [mul_pow,←pow_mul,Nat.mul_comm];ring

theorem raw_pair_uniform (J : ℕ) :
    ∃K : ℕ,∃C : ℝ,0< C ∧ ∀(data : RowData)(c κ A : ℝ),0≤ A →
      (∀s,RawMoment data (childLogTest referenceWindow s) c κ (A*(1+‖s‖)^(2*J))) →
      ∀reverse : Bool,∀n : ℕ,n≤2 → ∀U : ℝ,0< U →
      ∀tstar r : ℝ,∀σ∈Set.Icc (0:ℝ) 1,∀t : ℝ,
      let W:=twistProfile
        (logTest (HeckeDetectorCoefficientTransfer.orientedProfile reverse
          (HeckeDetectorInverseFiberCount.inverseTest U tstar r)) n) σ t
      RawMoment data W c κ (A*C*(1+‖t‖)^K) ∧
      RawMoment data (scaleProfile W) c κ (A*C*(1+‖t‖)^K) := by
  obtain ⟨K,C,hC,hb⟩:=raw_family_uniform J
  refine ⟨K,C,hC,?_⟩
  intro data c κ A hA href reverse n hn U hU tstar r σ hσ t
  dsimp only
  have hefalse : (inverseSourceSchwartz false reverse n U tstar r σ t:ℝ→ℂ)=
      twistProfile (logTest (HeckeDetectorCoefficientTransfer.orientedProfile reverse
        (HeckeDetectorInverseFiberCount.inverseTest U tstar r)) n) σ t := by
    funext x
    simpa only [Bool.false_eq_true,ite_false] using inverseSourceSchwartz_apply false reverse n U tstar r σ t x
  have hetrue : (inverseSourceSchwartz true reverse n U tstar r σ t:ℝ→ℂ)=
      scaleProfile (twistProfile (logTest (HeckeDetectorCoefficientTransfer.orientedProfile reverse
        (HeckeDetectorInverseFiberCount.inverseTest U tstar r)) n) σ t) := by
    funext x
    simpa only [Bool.true_eq,ite_true] using inverseSourceSchwartz_apply true reverse n U tstar r σ t x
  exact ⟨hefalse ▸ hb data c κ A hA href false reverse n hn U hU tstar r σ hσ t,
    hetrue ▸ hb data c κ A hA href true reverse n hn U hU tstar r σ hσ t⟩

theorem raw_pair_height_uniform (J : ℕ) :
    ∃K : ℕ,∃C : ℝ,0< C ∧ ∀(data : RowData)(c κ A : ℝ),0≤ A →
      (∀s,RawMoment data (childLogTest referenceWindow s) c κ (A*(1+‖s‖)^(2*J))) →
      ∀reverse : Bool,∀n : ℕ,n≤2 → ∀U : ℝ,0< U →
      ∀tstar r : ℝ,∀σ∈Set.Icc (0:ℝ) 1,∀height t : ℝ,0≤ height →
      t∈Set.Icc (-height) height →
      let W:=twistProfile
        (logTest (HeckeDetectorCoefficientTransfer.orientedProfile reverse
          (HeckeDetectorInverseFiberCount.inverseTest U tstar r)) n) σ t
      RawMoment data W c κ (A*C*(1+height)^K) ∧
      RawMoment data (scaleProfile W) c κ (A*C*(1+height)^K) := by
  obtain ⟨K,C,hC,hb⟩:=raw_pair_uniform J
  refine ⟨K,C,hC,?_⟩
  intro data c κ A hA href reverse n hn U hU tstar r σ hσ height t hheight ht
  have hh:=hb data c κ A hA href reverse n hn U hU tstar r σ hσ t
  have hnorm : ‖t‖≤ height := by simpa only [Real.norm_eq_abs,abs_le,Set.mem_Icc] using ht
  have hbound : A*C*(1+‖t‖)^K≤ A*C*(1+height)^K := by gcongr
  exact ⟨rawMoment_mono data _ c κ _ _ hbound hh.1,
    rawMoment_mono data _ c κ _ _ hbound hh.2⟩

end DetectorDictionaryInverseRawUniform

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace DetectorDictionaryInverseRawFiberSource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer InverseInitialPhysicalSlots
open InverseInitialDetectorSource InverseInitialRawDictionary InverseInitialConjugateEnergy
open HeckeDetectorPhysicalSelection
local notation "O"=> Eisenstein.O

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

/-- Expand the physical prime factors into the initial inverse polynomial. -/
theorem fiber_physical_norm_initial
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW : ℝ) (lower : Slot→ℝ)
    (hU : 0< U) (hW : ∀x,W x≠0 → x≤ bW)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)< lower s*U^(F.widths s))
    (u : FreeRow) (hu : u∈F.rows) :
    ‖polynomial (F.family u F.label) true W (U^F.r) σ t*F.physicalProduct selected u‖=
      ‖∑p∈Fintype.piFinset (fun s:selected=>
          livePrimes M H (F.profile s) (F.upper s) (U^(F.widths s))),
        (star (∏s:selected,primeProfile (F.profile s) (U^(F.widths s)) (F.external s) (p s))/
          fixedBase F.rowData.η F.rowData.m F.rowData.f (∏s:selected,p s))*
        originalTotalPolynomial
          ((HeckeInverseAmplification.idealsUpTo ⌈U^F.r*bW⌉₊).filter _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve.Supported)
          (∏s:selected,p s) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
          (twistedProfile (orientedProfile F.reverse W) σ (orientedFrequency F.reverse t))
          U F.r (∑s:selected,F.widths s) u.val‖ := by
  have hn:=norm_of_oriented_coefficients (F.family u F.label)
    (F.rowData.character ⟨u.val,u.property.1⟩) F.reverse (F.row_coeff u hu)
    true W (U^F.r) σ t (Real.rpow_pos_of_pos hU _)
  have hp : F.physicalProduct selected u=
      ∏s:selected,HeckePrimeRow.canonicalPrimeAmplitude M H u.val
        (F.profile s) (F.upper s) (U^(F.widths s)) (F.external s) := by
    simp only [Fiber.physicalProduct,physical]
    exact (Finset.prod_coe_sort selected _).symm
  rw [norm_mul,hn,←norm_mul,hp]
  have hh:=physical_slots_norm_initial M H F.rowData ⟨u.val,u.property.1⟩
    (orientedProfile F.reverse W) (fun s:selected=> F.profile s)
    U F.r σ (orientedFrequency F.reverse t) bW
    (fun s:selected=> lower s) (fun s:selected=> F.upper s) (fun s:selected=> F.widths s)
    (fun s:selected=> F.external s) hU
    (by intro x hx;apply hW x;intro hz;exact hx (by cases F.reverse <;> simp [orientedProfile,hz]))
    (fun s=> hV s s.property) (fun s=> hlarge s s.property)
  convert hh using 1 ; congr 2
  ext p
  simp only [Fintype.mem_piFinset]

theorem fiber_physical_energy_initial
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW : ℝ) (lower : Slot→ℝ)
    (hU : 0< U) (hW : ∀x,W x≠0 → x≤ bW)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)< lower s*U^(F.widths s)) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) true W (U^F.r) σ t*F.physicalProduct selected u‖^2)=
      ∑u∈F.rows,‖∑p∈Fintype.piFinset (fun s:selected=>
          livePrimes M H (F.profile s) (F.upper s) (U^(F.widths s))),
        (star (∏s:selected,primeProfile (F.profile s) (U^(F.widths s)) (F.external s) (p s))/
          fixedBase F.rowData.η F.rowData.m F.rowData.f (∏s:selected,p s))*
        originalTotalPolynomial
          ((HeckeInverseAmplification.idealsUpTo ⌈U^F.r*bW⌉₊).filter _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve.Supported)
          (∏s:selected,p s) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
          (twistedProfile (orientedProfile F.reverse W) σ (orientedFrequency F.reverse t))
          U F.r (∑s:selected,F.widths s) u.val‖^2 := by
  apply Finset.sum_congr rfl
  intro u hu
  rw [fiber_physical_norm_initial F selected W σ t bW lower hU hW hV hlarge u hu]

theorem fiber_inverse_log_upper
    (F : Fiber M H Label Slot U a ε tstar T allowance i) (n : ℕ) :
    ∀x,((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile) x≠0 → x≤9/4 := by
  induction n with
  | zero =>
    intro x hx
    have hv : HeckeDetectorDyadicProfiles.positiveAnnular x≠0 := by
      intro hz
      exact hx (by simp [Fiber.inverseProfile,HeckeDetectorInverseFiberCount.inverseTest,
        HeckeDetectorDyadicBridge.inverseProfile,hz])
    exact (HeckeDetectorDyadicProfiles.positiveAnnular_support hv).2
  | succ n ih =>
    intro x hx
    rw [Function.iterate_succ_apply'] at hx
    exact ih x (HeckeDetectorRowwisePolynomial.logProfile_support _ hx)

theorem fiber_inverse_energy_initial
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (n : ℕ) (σ t : ℝ) (lower : Slot→ℝ)
    (hU : 0< U)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)< lower s*U^(F.widths s)) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) true ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile) (U^F.r) σ t*F.physicalProduct selected u‖^2)=
      ∑u∈F.rows,‖∑p∈Fintype.piFinset (fun s:selected=>
          livePrimes M H (F.profile s) (F.upper s) (U^(F.widths s))),
        (star (∏s:selected,primeProfile (F.profile s) (U^(F.widths s)) (F.external s) (p s))/
          fixedBase F.rowData.η F.rowData.m F.rowData.f (∏s:selected,p s))*
        originalTotalPolynomial
          ((HeckeInverseAmplification.idealsUpTo ⌈U^F.r*(9/4)⌉₊).filter _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve.Supported)
          (∏s:selected,p s) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
          (twistedProfile (orientedProfile F.reverse ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)) σ (orientedFrequency F.reverse t))
          U F.r (∑s:selected,F.widths s) u.val‖^2 := by
  exact fiber_physical_energy_initial F selected
    ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile) σ t (9/4) lower
    hU (fiber_inverse_log_upper F n) hV hlarge

end DetectorDictionaryInverseRawFiberSource

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

/-
The canonical state recursion adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicSieve.CanonicalRankInduction
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.FixedConjugateCuspArrays

/-!
# The canonical state recursion

The canonical state condition `CanonicalStateCondition` and its reopening scale constants.
Retained bins are bounded by the induction hypothesis at smaller rank; four extra powers of
cutoff decay absorb the common-divisor factor; terminal energy.
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

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels CanonicalCoefficientClass RayFourExpansion
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀i,(Ideal.span {p i}).IsMaximal]

omit [DecidableEq ι] in
theorem actualSecondLabel_coprime (bad : Ideal O)
    (hbad : ∀i,IsCoprime (Ideal.span {p i}) bad)
    (B C E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    IsCoprime (actualSecondLabel p B C E V v₁ v₂ ε₁ ε₂) bad := by
  have hprod (S : Finset ι) : IsCoprime (∏i∈S,Ideal.span {p i}) bad :=
    IsCoprime.prod_left (fun i _=>hbad i)
  have hJ : IsCoprime (Ideal.span {jLabel p B (fun i=>v₁ i+v₂ i) ε₁ ε₂}) bad := by
    simp only [jLabel,primeProduct,span_finset_prime_product,←Ideal.span_singleton_pow]
    exact IsCoprime.prod_left (fun i _=>(hbad i).pow_left)
  exact ((hJ.mul_left (hprod C)).mul_left (hprod E)).mul_left (hprod V)

theorem globalNewLabel_coprime (bad : Ideal O)
    (hbad : ∀i,IsCoprime (Ideal.span {p i}) bad) (x : GlobalSecondData ι) :
    IsCoprime (SecondPassFiber.newLabel (globalSecondTuple p x)) bad := by
  unfold globalSecondTuple
  rw [actualSecondTuple_newLabel]
  exact actualSecondLabel_coprime p bad hbad x.cube.support x.common x.source.divisor x.source.overlap
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit

theorem globalCanonicalLabels_coprime (bad : Ideal O)
    (hbad : ∀i,IsCoprime (Ideal.span {p i}) bad)
    (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex) :
    ∀I∈globalCanonicalLabels p source side q j,IsCoprime I bad := by
  intro I hI
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  exact globalNewLabel_coprime p bad hbad x

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels CanonicalCoefficientClass RayFourExpansion
open scoped Classical

structure CanonicalStateCondition (base : O→*ℂ) (bad : Ideal O) (Z η : ℝ)
    (Ψ : O→*ℂ) (m : O) (labels : Finset (Ideal O)) (X F K : ℝ) : Prop where
  coefficient : IsBaseRayTwist base Ψ
  mask_ne_zero : m≠0
  column_pos : 0<X
  label_ge_one : 1≤F
  row_ge_one : 1≤K
  row_le_global : K≤Z^3
  mass_le : X*F≤canonicalRankMass Z (fixedDepthRank Z K)
  invariant : K*‖ringComplex m‖^2≤
    (X*F)*Z^(-canonicalRankMargin ((1:ℝ)/20) η (fixedDepthRank Z K))
  label_bounds : ∀I∈labels,I≠⊥ ∧ Squarefree I ∧ IsCoprime I bad ∧ (Ideal.absNorm I:ℝ)≤F

theorem CanonicalStateCondition.invariant_reserved
    {base : O→*ℂ} {bad : Ideal O} {Z η : ℝ} {Ψ : O→*ℂ} {m : O}
    {labels : Finset (Ideal O)} {X F K : ℝ}
    (h : CanonicalStateCondition base bad Z η Ψ m labels X F K)
    (hZ : 1≤Z) (hη : 0≤η) (hbudget : 3000*η≤(1:ℝ)/40) :
    K*‖ringComplex m‖^2≤(X*F)*Z^(-((1:ℝ)/40)) :=
  canonicalRankMargin_final_bound Z η _ _ _ hZ hη
    (mul_nonneg h.column_pos.le (zero_le_one.trans h.label_ge_one)) hbudget h.invariant

theorem CanonicalStateCondition.small_or_live
    {base : O→*ℂ} {bad : Ideal O} {Z η : ℝ} {Ψ : O→*ℂ} {m : O}
    {labels : Finset (Ideal O)} {X F K : ℝ}
    (h : CanonicalStateCondition base bad Z η Ψ m labels X F K)
    (hZ : Real.exp 9000≤Z) (hZ1 : 1≤Z) (hη : 0≤η)
    (hbudget : 3000*η≤(1:ℝ)/40) :
    K≤F ∨ (1<X ∧ X≤Z^3 ∧ F≤Z^3) := by
  have hi := h.invariant_reserved hZ1 hη hbudget
  have hr : Z^(-((1:ℝ)/40))≤1 := by
    simpa only [Real.rpow_zero] using
      (Real.rpow_le_rpow_of_exponent_le hZ1 (by norm_num : -((1:ℝ)/40)≤0))
  have hi' : K*‖ringComplex m‖^2≤X*F :=
    hi.trans ((mul_le_mul_of_nonneg_left hr
      (mul_nonneg h.column_pos.le (zero_le_one.trans h.label_ge_one))).trans_eq (mul_one _))
  exact canonical_small_or_live Z X F K _ m hZ h.column_pos h.label_ge_one
    (zero_le_one.trans h.row_ge_one) h.mask_ne_zero h.mass_le hi'

variable {ι:Type*} [DecidableEq ι] (p:ι→O) (hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
include hp in
theorem canonicalStateCondition_cutoff_retained
    (base : O→*ℂ) (bad : Ideal O) (Z η : ℝ) (Ψ : O→*ℂ) (m : O)
    (labels : Finset (Ideal O)) (X F Ksrc : ℝ)
    (hstate : CanonicalStateCondition base bad Z η Ψ m labels X F Ksrc)
    (hpbad : ∀i,IsCoprime (Ideal.span {p i}) bad)
    (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O×Ideal O×Ideal O) (j : GlobalLogIndex)
    (hq : q∈globalBinTriples p source side j)
    (χ : RayCharacter) (B : ℝ)
    (hZ : 1<Z) (hZbig : Real.exp 9000≤Z) (hη : 0≤η) (hηsmall : η≤(1:ℝ)/1000)
    (hB : 0<B) (hprogress : Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F)
    (hk : ∀x∈source,x.source.frequency≠0)
    (hb₁ : ∀x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Real.exp 1*B)
    (hb₂ : ∀x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Real.exp 1*B)
    (hretained : globalBinRadial (X/B^3)
      (globalPooledRowScale (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F j) j≤Z^η) :
    let X':=globalPooledColumnScale (X/B^3) j
    let F':=globalPooledLabelScale j
    let K':=globalLogRep j 8*Real.exp 1
    let labels':=globalCanonicalLabels p source side q j
    let m':=fixedTripleMask m q
    fixedDepthRank Z K'+1≤fixedDepthRank Z Ksrc ∧
    CanonicalStateCondition base bad Z η (Ψ*rayMonoid χ) m' labels' X' F' K'  := by
  obtain ⟨hXc,hFc,hKc,hrank,hKglobal,hmass,hinvariant,hm,hlabels⟩ :=
    canonical_retained_scale_closure p hp source side q j hq Z
      (canonicalRankMargin ((1:ℝ)/20) η (fixedDepthRank Z Ksrc)) η X B F Ksrc m
      hZ hZbig hη hηsmall hstate.column_pos hB hstate.label_ge_one hstate.row_ge_one
      hstate.mask_ne_zero hprogress hstate.row_le_global hstate.mass_le hstate.invariant
      hk hb₁ hb₂ hretained
  have hinvariant' : (globalLogRep j 8*Real.exp 1)*‖ringComplex (fixedTripleMask m q)‖^2≤
      (globalPooledColumnScale (X/B^3) j*globalPooledLabelScale j)*
        Z^(-canonicalRankMargin ((1:ℝ)/20) η (fixedDepthRank Z (globalLogRep j 8*Real.exp 1))) := by
    apply hinvariant.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hXc.le (zero_le_one.trans hFc))
    have hmargin := canonicalRankMargin_step ((1:ℝ)/20) η hη _ _
      (fixedDepthRank_initial Z Ksrc hZ (zero_lt_one.trans_le hstate.row_ge_one) hstate.row_le_global) hrank
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hbad := globalCanonicalLabels_coprime p bad hpbad source side q j
  have hbnd : ∀I∈globalCanonicalLabels p source side q j,
      I≠⊥ ∧ Squarefree I ∧ IsCoprime I bad ∧ (Ideal.absNorm I:ℝ)≤globalPooledLabelScale j := by
    intro I hI
    exact ⟨(hlabels I hI).1,(hlabels I hI).2.1,hbad I hI,(hlabels I hI).2.2⟩
  exact ⟨hrank,⟨hstate.coefficient.mul_ray_right χ,
    hm,hXc,hFc,hKc,hKglobal,hmass,hinvariant',hbnd⟩⟩

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory RayFourExpansion CanonicalCoefficientClass
open scoped Classical

/-- Retained bins are bounded by the induction hypothesis at strictly smaller rank. -/
theorem globalFirstQuantitativeBudget_below_rank (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) :
    ∃Clo Chi : ℝ,0<Clo ∧ 0<Chi ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hpr:∀i,lambda^2∣p i-1)
      (base : O→*ℂ) (bad : Ideal O) (Z η : ℝ) (Ψ : O→*ℂ) (m : O)
      (labels : Finset (Ideal O)) (X F Ksrc : ℝ)
      (_hstate : CanonicalStateCondition base bad Z η Ψ m labels X F Ksrc)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) (side : Bool)
      (windows : Fin 7→ℝ→ℂ) (C Cd Ct Γ E oldHeight B M H U A₀ Vmax : ℝ) (N J Ntail : ℕ),
      (∀u,‖base u‖≤1) → (∀i,IsCoprime (Ideal.span {p i}) bad) →
      1<Z → Real.exp 9000≤Z → 0≤η → η≤(1:ℝ)/1000 →
      0≤C → 0≤Γ → 0≤E → 1≤U → 1≤B → 0≤H →
      Ksrc/Z^η≤U → X/B^3≤U → Real.exp 1*B≤U → H≤U → Real.exp M≤U →
      Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F → 0≤A₀ → 0≤Vmax →
      (∀t,‖windows 5 t‖≤Vmax) → (∀t,‖windows 6 t‖≤Vmax) →
      (∀t,windows 5 t≠0→|t|≤A₀) → (∀t,windows 6 t≠0→|t|≤A₀) →
      (∀b∈blocks,‖ringComplex (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤Real.exp 1*B) →
      (∀b∈blocks,‖ringComplex (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤Real.exp 1*B) →
      (∀(Ψ' : O→*ℂ) (m' : O) (labels' : Finset (Ideal O)) (X' F' K' : ℝ),
        CanonicalStateCondition base bad Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z Ksrc → ∀s : ℝ,
        (canonicalLogEnergy p hg (fun _=>1) pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile true (windows 5)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J)) ∧
        (canonicalLogEnergy p hg (fun _=>1) pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile false (windows 6)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J))) →
      globalFirstQuantitativeBudget p hg pool blocks (normHeightTwist Ψ oldHeight) m windows
        C Cd Ct Γ ε (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U (N+1) (2*J) Ntail side≤
        (2*(Fintype.card (QuadraticRayRing×QuadraticRayRing):ℝ))*(∫t:ℝ,firstLogDensity 0 t)*Γ*(((X/B^3)*(Real.exp 1*B)^3)*F)*
          (((Real.exp 1*B)*U)^ε*(Cd+Ct*(U*globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F U H Ntail))+
           C*globalRayTripleConstant*U^(deltaLoss+8*ε)*
             (canonicalDensityConstant E J oldHeight*Clo+globalTerminalConstant A₀ Vmax*(Ksrc/Z^η)*Chi/Z^(η*N))) := by
  obtain ⟨Clo,Chi,hClo,hChi,hbound⟩ := globalFirstQuantitativeBudget_state_bound deltaLoss hδ ε hε
  refine ⟨Clo,Chi,hClo,hChi,?_⟩
  intro ι _ p hp _ hcop hg hc hinj hpr base bad Z η Ψ m labels X F Ksrc hstate pool blocks side
    windows C Cd Ct Γ E oldHeight B M H U A₀ Vmax N J Ntail
    hbase hpbad hZ hZbig hη hηsmall hC hΓ hE hU hB hH hKU hellU hBU hHU heU
    hprogress hA hV hV₁ hV₂ hVs₁ hVs₂ hb₁ hb₂ ih
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hB0 : 0<B := zero_lt_one.trans_le hB
  have hK0 : 0<Ksrc := zero_lt_one.trans_le hstate.row_ge_one
  have hKcut : 0<Ksrc/Z^η := div_pos hK0 (Real.rpow_pos_of_pos hZ0 _)
  have hell : 0<X/B^3 := div_pos hstate.column_pos (pow_pos hB0 _)
  have hBsup : 1≤Real.exp 1*B :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) hB
  apply hbound p hp hg hinj hc hpr pool blocks side Ψ m windows C Cd Ct Γ E oldHeight
    (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U Z η A₀ Vmax N J Ntail
    hC hΓ hE hU hKcut hell hBsup hstate.label_ge_one hH hKU hellU hBU hHU heU hZ0
    hA hV hV₁ hV₂ hVs₁ hVs₂ (fun u=>hstate.coefficient.norm_le hbase u) hb₁ hb₂
  dsimp only
  intro j hj q hq χ s
  let source := globalQuantitativeSource p pool blocks (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U side
  have hk : ∀x∈source,x.source.frequency≠0 :=
    globalQuantitativeSource_frequency_ne_zero p pool blocks (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U side
  have hb₁' : ∀x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Real.exp 1*B :=
    fun x hx=>hb₁ x.first.block (globalQuantitativeSource_block_mem p pool blocks
      (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U side x hx)
  have hb₂' : ∀x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Real.exp 1*B :=
    fun x hx=>hb₂ x.first.block (globalQuantitativeSource_block_mem p pool blocks
      (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U side x hx)
  have hs := canonicalStateCondition_cutoff_retained p hp base bad Z η Ψ m labels X F Ksrc hstate
    hpbad source side q j hq χ B
    hZ hZbig hη hηsmall hB0 hprogress hk hb₁' hb₂' (Finset.mem_filter.mp hj).2.le
  have hr : fixedDepthRank Z (globalLogRep j 8*Real.exp 1)<fixedDepthRank Z Ksrc := by
    have := hs.1
    omega
  exact ih _ _ _ _ _ _ hs.2 hr s


end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory RayFourExpansion CanonicalCoefficientClass
open scoped Classical
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

def canonicalBudgetCoefficient (C Cd Ct Tmax Clo Chi A M : ℝ) : ℝ :=
  (2*(Fintype.card (QuadraticRayRing×QuadraticRayRing):ℝ))*(∫t:ℝ,firstLogDensity 0 t)*
    (Cd+Ct*Tmax+C*globalRayTripleConstant*
      ((Fintype.card Oˣ:ℝ)*(∫t : ℝ,firstLogDensity 0 t)^3*Clo+globalTerminalConstant A M*Chi))

theorem canonicalBudgetCoefficient_nonneg (C Cd Ct Tmax Clo Chi A M : ℝ)
    (hC : 0≤C) (hCd : 0≤Cd) (hCt : 0≤Ct) (hTmax : 0≤Tmax)
    (hClo : 0≤Clo) (hChi : 0≤Chi) :
    0≤canonicalBudgetCoefficient C Cd Ct Tmax Clo Chi A M := by
  have hi : 0≤∫t : ℝ,firstLogDensity 0 t :=
    integral_nonneg (fun t=>firstLogDensity_nonneg 0 t)
  have ht := globalTerminalConstant_nonneg A M
  have hr := globalRayTripleConstant_nonneg
  unfold canonicalBudgetCoefficient
  positivity

theorem canonicalBudgetScalar_bound
    (C Cd Ct Tmax Clo Chi A M Γ P E t B U deltaLoss ε tailFactor terminalFactor : ℝ) (J : ℕ)
    (hC : 0≤C) (hCd : 0≤Cd) (hCt : 0≤Ct) (hTmax : 0≤Tmax)
    (_hClo : 0≤Clo) (hChi : 0≤Chi) (hΓ : 0≤Γ) (hP : 0≤P)
    (hE : 1≤E) (hB : 0≤B) (hBU : B≤U) (hU : 1≤U) (hδ : 0≤deltaLoss) (hε : 0≤ε)
    (htail : tailFactor≤Tmax) (hterminal : terminalFactor≤1) :
    (2*(Fintype.card (QuadraticRayRing×QuadraticRayRing):ℝ))*(∫s:ℝ,firstLogDensity 0 s)*Γ*P*
      ((B*U)^ε*(Cd+Ct*tailFactor)+C*globalRayTripleConstant*U^(deltaLoss+8*ε)*
        (canonicalDensityConstant E J t*Clo+globalTerminalConstant A M*Chi*terminalFactor))≤
    canonicalBudgetCoefficient C Cd Ct Tmax Clo Chi A M*
      Γ*P*U^(deltaLoss+8*ε)*E*(1+‖t‖)^(2*J) := by
  have hi : 0≤∫s : ℝ,firstLogDensity 0 s :=
    integral_nonneg (fun s=>firstLogDensity_nonneg 0 s)
  have ht := globalTerminalConstant_nonneg A M
  have hRT : 0≤globalRayTripleConstant := globalRayTripleConstant_nonneg
  have hU0 : 0<U := zero_lt_one.trans_le hU
  have hpow : (B*U)^ε≤U^(deltaLoss+8*ε) := by
    calc
      _ ≤ (U^2)^ε := Real.rpow_le_rpow (mul_nonneg hB hU0.le) (by nlinarith) hε
      _ = U^(2*ε) := by rw [←Real.rpow_natCast U 2,←Real.rpow_mul hU0.le];norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  have hheight : 1≤(1+‖t‖)^(2*J) := one_le_pow₀ (by linarith [norm_nonneg t])
  have he : 1≤E*(1+‖t‖)^(2*J) := one_le_mul_of_one_le_of_one_le hE hheight
  have hdiag : (B*U)^ε*(Cd+Ct*tailFactor)≤
      U^(deltaLoss+8*ε)*(Cd+Ct*Tmax)*(E*(1+‖t‖)^(2*J)) := by
    calc
      _ ≤ (B*U)^ε*(Cd+Ct*Tmax) := by gcongr
      _ ≤ U^(deltaLoss+8*ε)*(Cd+Ct*Tmax) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) he
  have hchild : canonicalDensityConstant E J t*Clo+globalTerminalConstant A M*Chi*terminalFactor≤
      ((Fintype.card Oˣ:ℝ)*(∫s : ℝ,firstLogDensity 0 s)^3*Clo+globalTerminalConstant A M*Chi)*
        (E*(1+‖t‖)^(2*J)) := by
    have hterm : globalTerminalConstant A M*Chi*terminalFactor≤
        globalTerminalConstant A M*Chi*(E*(1+‖t‖)^(2*J)) :=
      mul_le_mul_of_nonneg_left (hterminal.trans he) (mul_nonneg ht hChi)
    apply (add_le_add le_rfl hterm).trans_eq
    unfold canonicalDensityConstant
    ring
  have hrest := mul_le_mul_of_nonneg_left hchild
    (mul_nonneg (mul_nonneg hC hRT) (Real.rpow_nonneg hU0.le (deltaLoss+8*ε)))
  have hsum := add_le_add hdiag hrest
  have hwhole := mul_le_mul_of_nonneg_left hsum
    (show 0≤(2*(Fintype.card (QuadraticRayRing×QuadraticRayRing):ℝ))*(∫s:ℝ,firstLogDensity 0 s)*Γ*P by positivity)
  exact hwhole.trans_eq (by unfold canonicalBudgetCoefficient;ring)

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory RayFourExpansion CanonicalCoefficientClass
open scoped Classical
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

theorem globalFirstQuantitativeBudget_bounded (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) :
    ∃Clo Chi : ℝ,0<Clo ∧ 0<Chi ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hpr:∀i,lambda^2∣p i-1)
      (base : O→*ℂ) (bad : Ideal O) (Z η : ℝ) (Ψ : O→*ℂ) (m : O)
      (labels : Finset (Ideal O)) (X F Ksrc : ℝ)
      (_hstate : CanonicalStateCondition base bad Z η Ψ m labels X F Ksrc)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) (side : Bool)
      (windows : Fin 7→ℝ→ℂ) (C Cd Ct Tmax Γ E oldHeight B M H U A₀ Vmax : ℝ) (N J Ntail : ℕ),
      (∀u,‖base u‖≤1) → (∀i,IsCoprime (Ideal.span {p i}) bad) →
      1<Z → Real.exp 9000≤Z → 0≤η → η≤(1:ℝ)/1000 →
      0≤C → 0≤Cd → 0≤Ct → 0≤Tmax → 0≤Γ → 1≤E → 1≤U → 1≤B → 0≤H →
      Ksrc/Z^η≤U → X/B^3≤U → Real.exp 1*B≤U → H≤U → Real.exp M≤U →
      Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F → 0≤A₀ → 0≤Vmax →
      (∀t,‖windows 5 t‖≤Vmax) → (∀t,‖windows 6 t‖≤Vmax) →
      (∀t,windows 5 t≠0→|t|≤A₀) → (∀t,windows 6 t≠0→|t|≤A₀) →
      (∀b∈blocks,‖ringComplex (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤Real.exp 1*B) →
      (∀b∈blocks,‖ringComplex (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤Real.exp 1*B) →
      U*globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F U H Ntail≤Tmax →
      (Ksrc/Z^η)/Z^(η*(N:ℝ))≤1 →
      (∀(Ψ' : O→*ℂ) (m' : O) (labels' : Finset (Ideal O)) (X' F' K' : ℝ),
        CanonicalStateCondition base bad Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z Ksrc → ∀s : ℝ,
        (canonicalLogEnergy p hg (fun _=>1) pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile true (windows 5)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J)) ∧
        (canonicalLogEnergy p hg (fun _=>1) pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile false (windows 6)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J))) →
      globalFirstQuantitativeBudget p hg pool blocks (normHeightTwist Ψ oldHeight) m windows
        C Cd Ct Γ ε (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U (N+1) (2*J) Ntail side≤
        canonicalBudgetCoefficient C Cd Ct Tmax Clo Chi A₀ Vmax*
          Γ*(((X/B^3)*(Real.exp 1*B)^3)*F)*U^(deltaLoss+8*ε)*E*(1+‖oldHeight‖)^(2*J) := by
  obtain ⟨Clo,Chi,hClo,hChi,hbound⟩ := globalFirstQuantitativeBudget_below_rank deltaLoss hδ ε hε
  refine ⟨Clo,Chi,hClo,hChi,?_⟩
  intro ι _ p hp _ hcop hg hc hinj hpr base bad Z η Ψ m labels X F Ksrc hstate pool blocks side
    windows C Cd Ct Tmax Γ E oldHeight B M H U A₀ Vmax N J Ntail
    hbase hpbad hZ hZbig hη hηsmall hC hCd hCt hTmax hΓ hE hU hB hH hKU hellU hBU hHU heU
    hprogress hA hV hV₁ hV₂ hVs₁ hVs₂ hb₁ hb₂ htail hterminal ih
  have hb := hbound p hp hcop hg hc hinj hpr base bad Z η Ψ m labels X F Ksrc hstate
    pool blocks side windows C Cd Ct Γ E oldHeight B M H U A₀ Vmax N J Ntail
    hbase hpbad hZ hZbig hη hηsmall hC hΓ (zero_le_one.trans hE) hU hB hH hKU hellU hBU hHU heU
    hprogress hA hV hV₁ hV₂ hVs₁ hVs₂ hb₁ hb₂ ih
  have hX:=hstate.column_pos
  have hF : 0≤F:=zero_le_one.trans hstate.label_ge_one
  have hP : 0≤((X/B^3)*(Real.exp 1*B)^3)*F := by positivity
  have hs := canonicalBudgetScalar_bound C Cd Ct Tmax Clo Chi A₀ Vmax Γ
    (((X/B^3)*(Real.exp 1*B)^3)*F) E oldHeight (Real.exp 1*B) U deltaLoss ε
    (U*globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F U H Ntail)
    ((Ksrc/Z^η)/Z^(η*(N:ℝ))) J hC hCd hCt hTmax hClo.le hChi.le hΓ hP hE
    (by positivity) hBU hU hδ.le hε.le htail hterminal
  have he : globalTerminalConstant A₀ Vmax*(Ksrc/Z^η)*Chi/Z^(η*(N:ℝ)) =
      globalTerminalConstant A₀ Vmax*Chi*((Ksrc/Z^η)/Z^(η*(N:ℝ))) := by ring
  rw [he] at hb
  exact hb.trans hs

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory RayFourExpansion CanonicalCoefficientClass
open scoped Classical
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

def reopeningScaleConstant (A M : ℝ) : ℝ := 1+Real.exp (A+1)+Real.exp M

def reopeningAuxiliaryScale (A M κ Z : ℝ) : ℝ := reopeningScaleConstant A M*Z^(κ+3)

lemma reopeningScaleConstant_one (A M : ℝ) : 1 ≤ reopeningScaleConstant A M := by
  unfold reopeningScaleConstant
  linarith [Real.exp_pos (A+1),Real.exp_pos M]

lemma reopeningScaleConstant_exp (A M : ℝ) : Real.exp A ≤ reopeningScaleConstant A M := by
  have h : Real.exp A ≤ Real.exp (A+1) := Real.exp_le_exp.mpr (by linarith)
  unfold reopeningScaleConstant
  linarith [Real.exp_pos M]

theorem globalFirstRowCap_reopening (Z η X F Ksrc B : ℝ)
    (hZ : 0<Z) (hK : 0<Ksrc) (hB : 0<B) :
    globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F =
      (Real.exp 1)^8*X^2*F^2*Z^η/Ksrc := by
  unfold globalFirstRowCap
  field_simp

theorem globalFirstRowCap_reopening_bound (Z η X F Ksrc B : ℝ)
    (hZ : 1 ≤ Z) (_hη : 0 ≤ η) (hη1 : η ≤ 1) (hX : 1 ≤ X) (hXZ : X ≤ Z^3)
    (hF : 1 ≤ F) (hFZ : F ≤ Z^3) (hK : 1 ≤ Ksrc) (hB : 1 ≤ B) :
    globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F  ≤  (Real.exp 1)^8*Z^13 := by
  rw [globalFirstRowCap_reopening Z η X F Ksrc B (by linarith) (by linarith) (by linarith)]
  have hηZ : Z^η ≤ Z := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ hη1
  calc
    _  ≤  (Real.exp 1)^8*X^2*F^2*Z^η := div_le_self (by positivity) hK
    _  ≤  (Real.exp 1)^8*(Z^3)^2*(Z^3)^2*Z := by gcongr
    _ = _ := by ring

theorem globalFirstRowCap_reopening_small_power (Z η X F Ksrc B deltaLoss : ℝ)
    (hZ : 1 ≤ Z) (hη : 0 ≤ η) (hη1 : η ≤ 1) (hX : 1 ≤ X) (hXZ : X ≤ Z^3)
    (hF : 1 ≤ F) (hFZ : F ≤ Z^3) (hK : 1 ≤ Ksrc) (hB : 1 ≤ B) (hδ : 0 ≤ deltaLoss) :
    (max 1 (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F))^deltaLoss  ≤ 
      ((Real.exp 1)^8)^deltaLoss*Z^(13*deltaLoss) := by
  have he : 1 ≤ Real.exp (1:ℝ) := Real.one_le_exp (by norm_num)
  have hb := globalFirstRowCap_reopening_bound Z η X F Ksrc B hZ hη hη1 hX hXZ hF hFZ hK hB
  have hmax : max 1 (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F) ≤ (Real.exp 1)^8*Z^13 :=
    max_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ he) (one_le_pow₀ hZ)) hb
  apply (Real.rpow_le_rpow (by positivity) hmax hδ).trans_eq
  rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_natCast_mul (by linarith : 0 ≤ Z)]
  norm_num

theorem reopeningAuxiliaryScale_bounds (A M κ Z η X F Ksrc B : ℝ)
    (hκ : 0 ≤ κ) (hZ : 1 ≤ Z) (hη : 0 ≤ η)
    (hX : 1 ≤ X) (hXZ : X ≤ Z^3) (_hF : 1 ≤ F) (hFZ : F ≤ Z^3)
    (hK : 1 ≤ Ksrc) (hKZ : Ksrc ≤ Z^3) (hB : 1 ≤ B) (hactive : B^3 ≤ Real.exp A*X) :
    let U := reopeningAuxiliaryScale A M κ Z
    1 ≤ U ∧ Ksrc/Z^η ≤ U ∧ X/B^3 ≤ U ∧ Real.exp 1*B ≤ U ∧ F ≤ U ∧ Z^κ ≤ U ∧
      Real.exp M ≤ U ∧ (X/B^3)*Real.exp M ≤ U ∧ (X/B^3)⁻¹ ≤ U := by
  let C := reopeningScaleConstant A M
  have hC : 1 ≤ C := reopeningScaleConstant_one A M
  have hCZ : C ≤ C*Z^(κ+3) := le_mul_of_one_le_right (by linarith) (Real.one_le_rpow hZ (by linarith))
  have hZ3 : Z^3 ≤ Z^(κ+3) := by
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by norm_num; linarith)
  have hZκ : Z^κ ≤ Z^(κ+3) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hbase : Z^(κ+3) ≤ C*Z^(κ+3) := le_mul_of_one_le_left (by positivity) hC
  have hKcut : Ksrc/Z^η ≤ Z^3 :=
    (div_le_self (by linarith) (Real.one_le_rpow hZ hη)).trans hKZ
  have hell : X/B^3 ≤ X := div_le_self (by linarith) (one_le_pow₀ hB)
  have hB3 : B ≤ B^3 := by nlinarith [sq_nonneg (B-1)]
  have hBsup : Real.exp 1*B ≤ Real.exp (A+1)*Z^3 := by
    calc
      _  ≤  Real.exp 1*B^3 := mul_le_mul_of_nonneg_left hB3 (Real.exp_pos _).le
      _  ≤  Real.exp 1*(Real.exp A*X) := mul_le_mul_of_nonneg_left hactive (Real.exp_pos _).le
      _  ≤  Real.exp 1*(Real.exp A*Z^3) := by gcongr
      _ = _ := by rw [Real.exp_add]; ring
  have hCA : Real.exp (A+1) ≤ C := by dsimp [C,reopeningScaleConstant]; linarith [Real.exp_pos M]
  have hCM : Real.exp M ≤ C := by dsimp [C,reopeningScaleConstant]; linarith [Real.exp_pos (A+1)]
  have hinv : (X/B^3)⁻¹ ≤ Real.exp A := by
    rw [inv_div]
    exact (div_le_iff₀ (by linarith : 0<X)).mpr hactive
  change 1 ≤ C*Z^(κ+3) ∧ _
  refine ⟨hC.trans hCZ,hKcut.trans (hZ3.trans hbase),
    (hell.trans hXZ).trans (hZ3.trans hbase),?_,hFZ.trans (hZ3.trans hbase),
    hZκ.trans hbase,hCM.trans hCZ,?_,hinv.trans ((reopeningScaleConstant_exp A M).trans hCZ)⟩
  · exact hBsup.trans (mul_le_mul hCA hZ3 (by positivity) (by linarith))
  · calc
      _  ≤  Z^3*Real.exp M := mul_le_mul_of_nonneg_right (hell.trans hXZ) (Real.exp_pos _).le
      _  ≤  Z^(κ+3)*C := mul_le_mul hZ3 hCM (Real.exp_pos _).le (by positivity)
      _ = _ := mul_comm _ _

theorem globalFirstTailFactor_envelope (K ell B F U H : ℝ) (N : ℕ)
    (hK : 0 ≤ K) (hell : 0<ell) (hB : 1 ≤ B) (hF : 1 ≤ F)
    (hU : 1 ≤ U) (hH : 0 ≤ H) (hKU : K ≤ U) (hiell : ell⁻¹ ≤ U) :
    globalFirstTailFactor K ell B F U H N ≤ 4096*U^20/(1+H)^N := by
  have hBi : B⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hB
  have hFi : F⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hF
  have hratio : K*U^2/(ell^2*B^2*F^2) ≤ U^5 := by
    calc
      _ = K*U^2*(ell⁻¹)^2*(B⁻¹)^2*(F⁻¹)^2 := by field_simp
      _  ≤  U*U^2*U^2*1^2*1^2 := by gcongr
      _ = _ := by ring
  have hone : 1+U ≤ 2*U := by linarith
  have hinner : 1+(1+U)^3*(K*U^2/(ell^2*B^2*F^2)) ≤ 16*U^8 := by
    calc
      _  ≤  1+(2*U)^3*U^5 := by gcongr
      _ = 1+8*U^8 := by ring
      _  ≤  _ := by have hh : 1 ≤ U^8 := one_le_pow₀ hU; linarith
  unfold globalFirstTailFactor
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _  ≤  (2*U)^4*(16*U^8)^2 := by gcongr
    _ = _ := by ring

theorem globalFirstTailFactor_reopening_power (A M κ Z η X F Ksrc B : ℝ) (N : ℕ)
    (hκ : 0 ≤ κ) (hZ : 1 ≤ Z) (hη : 0 ≤ η)
    (hX : 1 ≤ X) (hXZ : X ≤ Z^3) (hF : 1 ≤ F) (hFZ : F ≤ Z^3)
    (hK : 1 ≤ Ksrc) (hKZ : Ksrc ≤ Z^3) (hB : 1 ≤ B) (hactive : B^3 ≤ Real.exp A*X) :
    globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F
      (reopeningAuxiliaryScale A M κ Z) (Z^κ) N  ≤ 
      (4096*(reopeningScaleConstant A M)^20)*Z^(20*(κ+3)-κ*N) := by
  have hZ0 : 0<Z := by linarith
  have hB0 : 0<B := by linarith
  have hX0 : 0<X := by linarith
  have hs := reopeningAuxiliaryScale_bounds A M κ Z η X F Ksrc B hκ hZ hη hX hXZ hF hFZ hK hKZ hB hactive
  have hBsup : 1 ≤ Real.exp 1*B := one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) hB
  have hbound := globalFirstTailFactor_envelope (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F
    (reopeningAuxiliaryScale A M κ Z) (Z^κ) N (by positivity) (by positivity) hBsup hF hs.1
    (by positivity) hs.2.1 hs.2.2.2.2.2.2.2.2
  apply hbound.trans
  have hden : (Z^κ)^N ≤ (1+Z^κ)^N := pow_le_pow_left₀ (by positivity) (by linarith [Real.rpow_pos_of_pos hZ0 κ]) N
  calc
    _  ≤  4096*(reopeningAuxiliaryScale A M κ Z)^20/(Z^κ)^N :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by
      unfold reopeningAuxiliaryScale
      rw [mul_pow,←Real.rpow_mul_natCast hZ0.le,←Real.rpow_mul_natCast hZ0.le,
        Real.rpow_sub hZ0]
      ring_nf

theorem globalFirstTailFactor_reopening_arbitrary_decay (A M κ R : ℝ) (hκ : 0<κ) :
    ∃N : ℕ,0<N ∧ ∀Z η X F Ksrc B : ℝ,
      1 ≤ Z → 0 ≤ η → 1 ≤ X → X ≤ Z^3 → 1 ≤ F → F ≤ Z^3 →
      1 ≤ Ksrc → Ksrc ≤ Z^3 → 1 ≤ B → B^3 ≤ Real.exp A*X →
      globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F
        (reopeningAuxiliaryScale A M κ Z) (Z^κ) N  ≤ 
        (4096*(reopeningScaleConstant A M)^20)*Z^(-R) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 0 ((20*(κ+3)+R)/κ))
  have hN0 : 0<N := by exact_mod_cast lt_of_le_of_lt (le_max_left _ _) hN
  have hNR : (20*(κ+3)+R)/κ<(N:ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hexp : 20*(κ+3)-κ*(N:ℝ) ≤ -R := by
    have hm := (div_lt_iff₀ hκ).mp hNR
    nlinarith
  refine ⟨N,hN0,?_⟩
  intro Z η X F Ksrc B hZ hη hX hXZ hF hFZ hK hKZ hB hactive
  exact (globalFirstTailFactor_reopening_power A M κ Z η X F Ksrc B N hκ.le hZ hη
    hX hXZ hF hFZ hK hKZ hB hactive).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hexp) (by positivity))

theorem globalFirstTailFactor_reopening_nat_decay (A M Z η X F Ksrc B : ℝ) (R : ℕ)
    (hZ : 1 ≤ Z) (hη : 0 ≤ η)
    (hX : 1 ≤ X) (hXZ : X ≤ Z^3) (hF : 1 ≤ F) (hFZ : F ≤ Z^3)
    (hK : 1 ≤ Ksrc) (hKZ : Ksrc ≤ Z^3) (hB : 1 ≤ B) (hactive : B^3 ≤ Real.exp A*X) :
    globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F
      (reopeningScaleConstant A M*Z^4) Z (R+80)  ≤ 
      (4096*(reopeningScaleConstant A M)^20)*Z^(-(R:ℝ)) := by
  have h := globalFirstTailFactor_reopening_power A M 1 Z η X F Ksrc B (R+80)
    (by norm_num) hZ hη hX hXZ hF hFZ hK hKZ hB hactive
  have hpow : 20*((1:ℝ)+3)-1*((R+80:ℕ):ℝ)=-(R:ℝ) := by push_cast; ring
  rw [hpow] at h
  norm_num [reopeningAuxiliaryScale,Real.rpow_natCast] at h ⊢
  exact h

lemma reopening_cutoff_ratio (Z η Ksrc : ℝ) (hZ : 0<Z) (hK : 0<Ksrc) :
    Ksrc/(Ksrc/Z^η)=Z^η := by field_simp

lemma globalFirstRowCap_reopening_rpow (Z η X F Ksrc B deltaLoss : ℝ)
    (hZ : 1 ≤ Z) (hη : 0 ≤ η) (hη1 : η ≤ 1) (hX : 1 ≤ X) (hXZ : X ≤ Z^3)
    (hF : 1 ≤ F) (hFZ : F ≤ Z^3) (hK : 1 ≤ Ksrc) (hB : 1 ≤ B) (hδ : 0 ≤ deltaLoss) :
    (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss  ≤ 
      ((Real.exp 1)^8)^deltaLoss*Z^(13*deltaLoss) := by
  have hcap : 0 ≤ globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F := by
    unfold globalFirstRowCap
    positivity
  exact (Real.rpow_le_rpow hcap (le_max_right 1 _) hδ).trans
    (globalFirstRowCap_reopening_small_power Z η X F Ksrc B deltaLoss hZ hη hη1 hX hXZ hF hFZ hK hB hδ)

lemma reopening_cube_bound (A M Z X B : ℝ) (hZ : 1 ≤ Z) (_hX : 1 ≤ X)
    (hXZ : X ≤ Z^3) (hB : 1 ≤ B) (hactive : B^3 ≤ Real.exp A*X) :
    Real.exp 1*B ≤ reopeningScaleConstant A M*Z^3 := by
  have hB3 : B ≤ B^3 := by nlinarith [sq_nonneg (B-1)]
  have hC : Real.exp (A+1) ≤ reopeningScaleConstant A M := by
    unfold reopeningScaleConstant
    linarith [Real.exp_pos M]
  calc
    _  ≤  Real.exp 1*B^3 := mul_le_mul_of_nonneg_left hB3 (Real.exp_pos _).le
    _  ≤  Real.exp 1*(Real.exp A*X) := mul_le_mul_of_nonneg_left hactive (Real.exp_pos _).le
    _  ≤  Real.exp 1*(Real.exp A*Z^3) := by gcongr
    _ = Real.exp (A+1)*Z^3 := by rw [Real.exp_add]; ring
    _  ≤  _ := mul_le_mul_of_nonneg_right hC (by positivity)

theorem reopening_diagonal_monomial (A M Z η X F Ksrc B deltaLoss ε : ℝ)
    (hZ : 1 ≤ Z) (hη : 0 ≤ η) (hη1 : η ≤ 1) (hX : 1 ≤ X) (hXZ : X ≤ Z^3)
    (hF : 1 ≤ F) (hFZ : F ≤ Z^3) (hK : 1 ≤ Ksrc) (hB : 1 ≤ B)
    (hactive : B^3 ≤ Real.exp A*X) (hδ : 0 ≤ deltaLoss) (hε : 0 ≤ ε) :
    (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss *
      ((Real.exp 1*B)*(reopeningScaleConstant A M*Z^4))^ε  ≤ 
      (((Real.exp 1)^8)^deltaLoss*(reopeningScaleConstant A M^2)^ε)*Z^(13*deltaLoss+7*ε) := by
  let C := reopeningScaleConstant A M
  have hC : 1 ≤ C := reopeningScaleConstant_one A M
  have hb := reopening_cube_bound A M Z X B hZ hX hXZ hB hactive
  have hprod : (Real.exp 1*B)*(C*Z^4) ≤ C ^ 2*Z^7 := by
    calc
      _  ≤  (C*Z^3)*(C*Z^4) := mul_le_mul_of_nonneg_right hb (by positivity)
      _ = _ := by ring
  have hpow : ((Real.exp 1*B)*(C*Z^4))^ε ≤ (C ^ 2)^ε*Z^(7*ε) := by
    apply (Real.rpow_le_rpow (by positivity) hprod hε).trans_eq
    rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_natCast_mul (by linarith : 0 ≤ Z)]
    norm_num
  have hcap := globalFirstRowCap_reopening_rpow Z η X F Ksrc B deltaLoss hZ hη hη1 hX hXZ hF hFZ hK hB hδ
  calc
    _  ≤  (((Real.exp 1)^8)^deltaLoss*Z^(13*deltaLoss))*((C ^ 2)^ε*Z^(7*ε)) :=
      mul_le_mul hcap hpow (Real.rpow_nonneg (by positivity) _) (by positivity)
    _ = _ := by rw [Real.rpow_add (by linarith : 0<Z)]; dsimp [C]; ring

theorem reopening_recursive_monomial (A M Z η X F Ksrc B deltaLoss ε : ℝ)
    (hZ : 1 ≤ Z) (hη : 0 ≤ η) (hη1 : η ≤ 1) (hX : 1 ≤ X) (hXZ : X ≤ Z^3)
    (hF : 1 ≤ F) (hFZ : F ≤ Z^3) (hK : 1 ≤ Ksrc) (hB : 1 ≤ B)
    (hδ : 0 ≤ deltaLoss) (_hε : 0 ≤ ε) :
    (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss *
      (reopeningScaleConstant A M*Z^4)^(deltaLoss+8*ε)  ≤ 
      (((Real.exp 1)^8)^deltaLoss*(reopeningScaleConstant A M)^(deltaLoss+8*ε))*Z^(17*deltaLoss+32*ε) := by
  have hC : 0<reopeningScaleConstant A M := lt_of_lt_of_le zero_lt_one (reopeningScaleConstant_one A M)
  have he : (reopeningScaleConstant A M*Z^4)^(deltaLoss+8*ε)=
      reopeningScaleConstant A M^(deltaLoss+8*ε)*Z^(4*deltaLoss+32*ε) := by
    rw [Real.mul_rpow hC.le (by positivity),←Real.rpow_natCast_mul (by linarith : 0 ≤ Z)]
    congr 2
    ring
  rw [he]
  have hcap := globalFirstRowCap_reopening_rpow Z η X F Ksrc B deltaLoss hZ hη hη1 hX hXZ hF hFZ hK hB hδ
  calc
    _  ≤  (((Real.exp 1)^8)^deltaLoss*Z^(13*deltaLoss))*
      (reopeningScaleConstant A M^(deltaLoss+8*ε)*Z^(4*deltaLoss+32*ε)) :=
      mul_le_mul_of_nonneg_right hcap (by positivity)
    _ = _ := by
      have hh : 17*deltaLoss+32*ε=13*deltaLoss+(4*deltaLoss+32*ε) := by ring
      rw [hh]
      simp only [Real.rpow_add (by linarith : 0<Z)]
      ring

theorem reopening_diagonal_with_ratio (A M Z η X F Ksrc B deltaLoss ε : ℝ)
    (hZ : 1 ≤ Z) (hη : 0 ≤ η) (hη1 : η ≤ 1) (hX : 1 ≤ X) (hXZ : X ≤ Z^3)
    (hF : 1 ≤ F) (hFZ : F ≤ Z^3) (hK : 1 ≤ Ksrc) (hB : 1 ≤ B)
    (hactive : B^3 ≤ Real.exp A*X) (hδ : 0 ≤ deltaLoss) (hε : 0 ≤ ε) :
    (Ksrc/(Ksrc/Z^η))*((globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss *
      ((Real.exp 1*B)*(reopeningScaleConstant A M*Z^4))^ε)  ≤ 
      (((Real.exp 1)^8)^deltaLoss*(reopeningScaleConstant A M^2)^ε)*Z^(η+13*deltaLoss+7*ε) := by
  rw [reopening_cutoff_ratio Z η Ksrc (by linarith) (by linarith)]
  apply (mul_le_mul_of_nonneg_left (reopening_diagonal_monomial A M Z η X F Ksrc B deltaLoss ε
    hZ hη hη1 hX hXZ hF hFZ hK hB hactive hδ hε) (by positivity)).trans_eq
  rw [show η+13*deltaLoss+7*ε=η+(13*deltaLoss+7*ε) by ring]
  simp only [Real.rpow_add (by linarith : 0<Z)]
  ring

theorem reopening_recursive_with_ratio (A M Z η X F Ksrc B deltaLoss ε : ℝ)
    (hZ : 1 ≤ Z) (hη : 0 ≤ η) (hη1 : η ≤ 1) (hX : 1 ≤ X) (hXZ : X ≤ Z^3)
    (hF : 1 ≤ F) (hFZ : F ≤ Z^3) (hK : 1 ≤ Ksrc) (hB : 1 ≤ B)
    (hδ : 0 ≤ deltaLoss) (hε : 0 ≤ ε) :
    (Ksrc/(Ksrc/Z^η))*((globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss *
      (reopeningScaleConstant A M*Z^4)^(deltaLoss+8*ε))  ≤ 
      (((Real.exp 1)^8)^deltaLoss*(reopeningScaleConstant A M)^(deltaLoss+8*ε))*Z^(η+17*deltaLoss+32*ε) := by
  rw [reopening_cutoff_ratio Z η Ksrc (by linarith) (by linarith)]
  apply (mul_le_mul_of_nonneg_left (reopening_recursive_monomial A M Z η X F Ksrc B deltaLoss ε
    hZ hη hη1 hX hXZ hF hFZ hK hB hδ hε) (by positivity)).trans_eq
  rw [show η+17*deltaLoss+32*ε=η+(17*deltaLoss+32*ε) by ring]
  simp only [Real.rpow_add (by linarith : 0<Z)]
  ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical

/-- Four extra powers of cutoff decay absorb the common-divisor support factor. -/
theorem globalFirstWeightedTail_reopening_nat_decay (A M Z η X F Ksrc B:ℝ) (R:ℕ)
    (hZ:1≤Z) (hη:0≤η) (hX:1≤X) (hXZ:X≤Z^3) (hF:1≤F) (hFZ:F≤Z^3)
    (hK:1≤Ksrc) (hKZ:Ksrc≤Z^3) (hB:1≤B) (hactive:B^3≤Real.exp A*X):
    (reopeningScaleConstant A M*Z^4)*
      globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F
        (reopeningScaleConstant A M*Z^4) Z (R+84)≤
      (4096*(reopeningScaleConstant A M)^21)*Z^(-(R:ℝ)):=by
  have hC:0≤reopeningScaleConstant A M:=(zero_le_one.trans (reopeningScaleConstant_one A M))
  have hZ0:0<Z:=zero_lt_one.trans_le hZ
  have hb:=globalFirstTailFactor_reopening_nat_decay A M Z η X F Ksrc B (R+4)
    hZ hη hX hXZ hF hFZ hK hKZ hB hactive
  rw [show R+4+80=R+84 by omega] at hb
  have hz:Z^4*Z^(-((R+4:ℕ):ℝ))=Z^(-(R:ℝ)):=by
    rw [←Real.rpow_natCast Z 4,←Real.rpow_add hZ0]
    congr 1
    push_cast
    ring
  apply (mul_le_mul_of_nonneg_left hb (mul_nonneg hC (pow_nonneg hZ0.le 4))).trans_eq
  calc
    _ = (4096*(reopeningScaleConstant A M)^21)*(Z^4*Z^(-((R+4:ℕ):ℝ))):=by ring
    _ = _:=by rw [hz]

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory JointLogSeparation CanonicalCoefficientClass RayFourExpansion
open scoped Classical SchwartzMap ContDiff

theorem exists_polynomial_cutoff_order (p q η R : ℝ) (hη : 0<η) :
    ∃N : ℕ,0<N ∧ ∀C Z : ℝ,0 ≤ C → 1 ≤ Z →
      (C*Z^p)^q/Z^(η*N) ≤ C ^ q*Z^(-R) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 0 ((p*q+R)/η))
  have hN0 : 0<N := by exact_mod_cast lt_of_le_of_lt (le_max_left _ _) hN
  have hNR : (p*q+R)/η<(N:ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hexp : p*q-η*(N:ℝ) ≤ -R := by
    have hm := (div_lt_iff₀ hη).mp hNR
    nlinarith
  refine ⟨N,hN0,?_⟩
  intro C Z hC hZ
  have hZ0 : 0<Z := by linarith
  calc
    _ = C ^ q*Z^(p*q-η*N) := by
      rw [Real.mul_rpow hC (by positivity),←Real.rpow_mul hZ0.le,Real.rpow_sub hZ0]
      ring
    _  ≤  _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hexp) (Real.rpow_nonneg hC _)

theorem reopening_terminal_order (η R : ℝ) (hη : 0<η) :
    ∃N : ℕ,0<N ∧ ∀Z Ksrc : ℝ,1 ≤ Z → 0 ≤ Ksrc → Ksrc ≤ Z^3 →
      (Ksrc/Z^η)/Z^(η*N) ≤ Z^(-R) := by
  obtain ⟨N,hN,horder⟩ := exists_polynomial_cutoff_order 3 1 η R hη
  refine ⟨N,hN,?_⟩
  intro Z Ksrc hZ hK hKZ
  have hb : Ksrc/Z^η ≤ Z^3 := (div_le_self hK (Real.one_le_rpow hZ hη.le)).trans hKZ
  have ho : Z^3/Z^(η*N) ≤ Z^(-R) := by
    have hh := horder 1 Z zero_le_one hZ
    norm_num [Real.rpow_natCast] at hh ⊢
    exact hh
  exact (div_le_div_of_nonneg_right hb (by positivity)).trans ho
theorem lowerCubeBin_mass_product (X F B : ℝ) (hB : B≠0) :
    B*((X/B^3)*(Real.exp 1*B)^2*F)*((X/B^3)*(Real.exp 1*B)^3*F)=
      Real.exp 5*(X*F)^2 := by
  have he : (Real.exp 1)^5=Real.exp 5 := by
    rw [show (5:ℝ)=1+1+1+1+1 by norm_num]
    simp only [Real.exp_add]
    ring
  simp only [mul_pow]
  rw [←he]
  field_simp

theorem canonicalBudget_sqrt_product (b₁ b₂ D₁ D₂ Q : ℝ)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hQ : 0 ≤ Q)
    (h₁ : b₁ ≤ D₁*Q) (h₂ : b₂ ≤ D₂*Q) :
    Real.sqrt b₁*Real.sqrt b₂ ≤ Real.sqrt D₁*Real.sqrt D₂*Q := by
  calc
    _  ≤  Real.sqrt (D₁*Q)*Real.sqrt (D₂*Q) :=
      mul_le_mul (Real.sqrt_le_sqrt h₁) (Real.sqrt_le_sqrt h₂)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul hD₁,Real.sqrt_mul hD₂]
      calc
        _ = Real.sqrt D₁*Real.sqrt D₂*(Real.sqrt Q*Real.sqrt Q) := by ring
        _ = _ := by rw [Real.mul_self_sqrt hQ]

theorem canonicalPairBudget_normalized
    (X F B Ksrc Kcut Cf cap U power E t D₁ D₂ b₁ b₂ : ℝ) (J : ℕ)
    (hX : 0<X) (hF : 0 ≤ F) (hB : 0<B) (hKsrc : 0 ≤ Ksrc) (hKcut : 0<Kcut)
    (hCf : 0 ≤ Cf) (hcap : 0 ≤ cap) (hU : 0 ≤ U) (hE : 0 ≤ E)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (h₁ : b₁ ≤ D₁*((X/B^3)*(Real.exp 1*B)^3*F)*U^power*E*(1+‖t‖)^(2*J))
    (h₂ : b₂ ≤ D₂*((X/B^3)*(Real.exp 1*B)^3*F)*U^power*E*(1+‖t‖)^(2*J)) :
    B*(((X/B^3)*(Real.exp 1*B)^2*F)*(Ksrc/Kcut)*Cf*cap*
      Real.sqrt b₁*Real.sqrt b₂) ≤ 
    (Real.exp 5*Cf*Real.sqrt D₁*Real.sqrt D₂)*(X*F)^2*
      (Ksrc/Kcut)*cap*U^power*E*(1+‖t‖)^(2*J) := by
  let Q:=((X/B^3)*(Real.exp 1*B)^3*F)*U^power*E*(1+‖t‖)^(2*J)
  have hQ : 0 ≤ Q := by dsimp only [Q];positivity
  have hs := canonicalBudget_sqrt_product b₁ b₂ D₁ D₂ Q hD₁ hD₂ hQ
    (by simpa only [Q,mul_assoc] using h₁) (by simpa only [Q,mul_assoc] using h₂)
  have hfac : 0 ≤ B*(((X/B^3)*(Real.exp 1*B)^2*F)*(Ksrc/Kcut)*Cf*cap) := by positivity
  have hh := mul_le_mul_of_nonneg_left hs hfac
  calc
    _ = (B*(((X/B^3)*(Real.exp 1*B)^2*F)*(Ksrc/Kcut)*Cf*cap))*(Real.sqrt b₁*Real.sqrt b₂) := by ring
    _  ≤  _ := hh
    _ = _ := by
      dsimp only [Q]
      calc
        _ = (B*((X/B^3)*(Real.exp 1*B)^2*F)*((X/B^3)*(Real.exp 1*B)^3*F))*
            ((Ksrc/Kcut)*Cf*cap*Real.sqrt D₁*Real.sqrt D₂*U^power*E*(1+‖t‖)^(2*J)) := by ring
        _ = _ := by rw [lowerCubeBin_mass_product X F B hB.ne'];ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory JointLogSeparation CanonicalCoefficientClass RayFourExpansion
open scoped Classical SchwartzMap ContDiff

private theorem two_windows_bound (windows : Fin 7→ℝ→ℂ)
    (hc : ∀i,HasCompactSupport (windows i)) (hs : ∀i,Continuous (windows i)) :
    ∃Vmax : ℝ,0 ≤ Vmax ∧ (∀t,‖windows 5 t‖ ≤ Vmax) ∧ (∀t,‖windows 6 t‖ ≤ Vmax) := by
  have hb (i : Fin 7) : ∃B : ℝ,0 ≤ B ∧ ∀t,‖windows i t‖ ≤ B := by
    obtain ⟨B,hB⟩ := ((hc i).isCompact_range (hs i)).bddAbove_image continuous_norm.continuousOn
    have he (t : ℝ) : ‖windows i t‖ ≤ B := hB ⟨windows i t,⟨t,rfl⟩,rfl⟩
    exact ⟨B,(norm_nonneg _).trans (he 0),he⟩
  obtain ⟨B₅,h₅,hb₅⟩ := hb 5
  obtain ⟨B₆,h₆,hb₆⟩ := hb 6
  exact ⟨B₅+B₆,by linarith,fun t=>(hb₅ t).trans (by linarith),fun t=>(hb₆ t).trans (by linarith)⟩

theorem reopenedCanonicalRow_state_step
    (g V : 𝓢(ℝ,ℂ)) (M Nv : ℝ) (hM : 0 ≤ M) (hNv : 0 ≤ Nv)
    (hgM : ∀t,g t≠0→|t| ≤ M) (hV : ∀t,V t≠0→|t| ≤ Nv)
    (hWin : ∀t,g t≠0→V t=1)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (N J Ntail : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ)
      (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ Clo Chi Vmax₁ Vmax₂ : ℝ),
      0 ≤ Cfirst ∧ 0 ≤ C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0 ≤ C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧ 0<Clo ∧ 0<Chi ∧
      0 ≤ Vmax₁ ∧ 0 ≤ Vmax₂ ∧
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t| ≤ M+7) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t| ≤ M+7) ∧
      ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i=>Ideal.span {p i})) (_hpr : ∀i,lambda^2∣p i-1)
      (base : O→*ℂ) (bad : Ideal O) (Z η : ℝ) (Ψ : O→*ℂ) (m : O)
      (labels : Finset (Ideal O)) (X F Ksrc : ℝ)
      (_hstate : CanonicalStateCondition base bad Z η Ψ m labels X F Ksrc)
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : Ideal O→(ι→₀ℕ)→ℂ)
      (Γ t B H U Tmax E : ℝ),
      (∀u,‖base u‖ ≤ 1) → (∀i,IsCoprime (Ideal.span {p i}) bad) →
      1<Z → Real.exp 9000 ≤ Z → 0 ≤ η → η ≤ (1:ℝ)/1000 →
      0 ≤ Γ → 1 ≤ E → 1 ≤ U → 1 ≤ B → 0 ≤ H → 0 ≤ Tmax →
      Ksrc/Z^η ≤ U → X/B^3 ≤ U → Real.exp 1*B ≤ U → H ≤ U → Real.exp M ≤ U →
      (X/B^3)*Real.exp M ≤ U → Z^((1:ℝ)/1000) ≤ (Real.exp 1*B)*F →
      (∀I∈labels,∀v∈Q,‖β I v‖ ≤ Γ) → (∀v∈Q,v.support⊆pool) →
      (∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2 ≤ Real.exp 1*B) →
      U*globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F U H Ntail ≤ Tmax →
      (Ksrc/Z^η)/Z^(η*(N:ℝ)) ≤ 1 →
      (∀side : Bool, let windows:=if side then windows₁ else windows₂
        ∀(Ψ' : O→*ℂ) (m' : O) (labels' : Finset (Ideal O)) (X' F' K' : ℝ),
        CanonicalStateCondition base bad Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z Ksrc → ∀s : ℝ,
        (canonicalLogEnergy p hg (fun _=>1) pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile true (windows 5)) X' K' ≤ E*(X'*F')^2*(1+‖s‖)^(2*J)) ∧
        (canonicalLogEnergy p hg (fun _=>1) pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile false (windows 6)) X' K' ≤ E*(X'*F')^2*(1+‖s‖)^(2*J))) →
      let D₁:=canonicalBudgetCoefficient C₁ Cd₁ Ct₁ Tmax Clo Chi (M+7) Vmax₁
      let D₂:=canonicalBudgetCoefficient C₂ Cd₂ Ct₂ Tmax Clo Chi (M+7) Vmax₂
      let Ψt:=normHeightTwist Ψ t
      let bs:=reopenedCubeFamily Q
      let a:=reopenedPairCoefficient β
      B*(∑I∈labels,nonzeroRowMajorantSum
         (reopenedCanonicalRow p hg pool Q (β I) Ψ m
           (cubicIdealGenerator I)
           (fun S=>frequencyTwist g t (columnLog p (X/B^3) S))) Ksrc).re ≤ 
      B*(‖canonicalSourceZero p hp hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc (X/B^3)‖+
         ‖canonicalSourceTail p hp hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc (Ksrc/Z^η) (X/B^3)‖)+
      (Real.exp 5*Cfirst*Real.sqrt D₁*Real.sqrt D₂)*Γ^2*(X*F)^2*
        (Ksrc/(Ksrc/Z^η))*(globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss*
        U^(deltaLoss+8*ε)*E*(1+‖t‖)^(2*J) := by
  obtain ⟨w₁,w₂,Cf,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,htransfer⟩ :=
    reopenedCanonicalRow_nonzero_twoPassage g V M Nv hM hNv hgM hV hWin ε deltaLoss hε hδ (N+1) (2*J) Ntail
  obtain ⟨Clo,Chi,hClo,hChi,hbudget⟩ := globalFirstQuantitativeBudget_bounded deltaLoss hδ ε hε
  obtain ⟨Vmax₁,hVmax₁,hw₁₅,hw₁₆⟩ := two_windows_bound w₁ hwc₁ (fun i=>(hws₁ i).continuous)
  obtain ⟨Vmax₂,hVmax₂,hw₂₅,hw₂₆⟩ := two_windows_bound w₂ hwc₂ (fun i=>(hws₂ i).continuous)
  have hwb₁' : ∀i t,w₁ i t≠0→|t| ≤ M+7 := by convert hwb₁ using 1 ; ring_nf
  have hwb₂' : ∀i t,w₂ i t≠0→|t| ≤ M+7 := by convert hwb₂ using 1 ; ring_nf
  refine ⟨w₁,w₂,Cf,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,Clo,Chi,Vmax₁,Vmax₂,
    hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,hClo,hChi,hVmax₁,hVmax₂,
    hwc₁,hws₁,hwb₁',hwc₂,hws₂,hwb₂',?_⟩
  intro ι _ p hp _ hcop hg hc hinj hpr base bad Z η Ψ m labels X F Ksrc hstate pool Q β
    Γ t B H U Tmax E hbase hpbad hZ hZbig hη hηsmall hΓ hE hU hB hH hTmax hKU hellU hBU hHU heU
    hMU hprogress hβ hQ hQB htail hterminal ih
  dsimp only
  have hX:=hstate.column_pos
  have hF0 : 0<F:=zero_lt_one.trans_le hstate.label_ge_one
  have hK0 : 0<Ksrc:=zero_lt_one.trans_le hstate.row_ge_one
  have hB0 : 0<B:=zero_lt_one.trans_le hB
  have hell : 0<X/B^3:=div_pos hX (pow_pos hB0 _)
  have hKcut : 0<Ksrc/Z^η:=div_pos hK0 (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  have hBsup : 1 ≤ Real.exp 1*B:=one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) hB
  have hΨ : ∀u,‖Ψ u‖ ≤ 1:=fun u=>hstate.coefficient.norm_le hbase u
  have he := htransfer p hp hinj hcop hg hc hpr pool Q labels β Ψ m Γ t Ksrc (Ksrc/Z^η)
    (X/B^3) (Real.exp 1*B) F H U hΓ hK0 hKcut hell hBsup hF0 hH hU hMU hΨ hβ hQ hQB
    (fun I hI=>(hstate.label_bounds I hI).2.1) (fun I hI=>(hstate.label_bounds I hI).2.2.2)
  let blocks:=canonicalSourceBlocks pool (reopenedCubeFamily Q)
  have hb₁ : ∀b∈blocks,‖ringComplex (primeProduct p b.cube.support b.cube.leftExponent)‖^2 ≤ Real.exp 1*B:=
    fun b hb=>(canonicalSourceBlocks_cube_norms p pool (reopenedCubeFamily Q) (Real.exp 1*B)
      (fun c hc=>(reopenedCubeFamily_cube_norms p Q _ hQB c hc).1)
      (fun c hc=>(reopenedCubeFamily_cube_norms p Q _ hQB c hc).2) b hb).1
  have hb₂ : ∀b∈blocks,‖ringComplex (primeProduct p b.cube.support b.cube.rightExponent)‖^2 ≤ Real.exp 1*B:=
    fun b hb=>(canonicalSourceBlocks_cube_norms p pool (reopenedCubeFamily Q) (Real.exp 1*B)
      (fun c hc=>(reopenedCubeFamily_cube_norms p Q _ hQB c hc).1)
      (fun c hc=>(reopenedCubeFamily_cube_norms p Q _ hQB c hc).2) b hb).2
  have hbL:=hbudget p hp hcop hg hc hinj hpr base bad Z η Ψ m labels X F Ksrc hstate pool blocks true w₁
    C₁ Cd₁ Ct₁ Tmax (Γ^2) E t B M H U (M+7) Vmax₁ N J Ntail
    hbase hpbad hZ hZbig hη hηsmall hC₁ hCd₁.le hCt₁.le hTmax (sq_nonneg Γ) hE hU hB hH
    hKU hellU hBU hHU heU hprogress (by linarith) hVmax₁ hw₁₅ hw₁₆ (hwb₁' 5) (hwb₁' 6)
    hb₁ hb₂ htail hterminal (ih true)
  have hbR:=hbudget p hp hcop hg hc hinj hpr base bad Z η Ψ m labels X F Ksrc hstate pool blocks false w₂
    C₂ Cd₂ Ct₂ Tmax (Γ^2) E t B M H U (M+7) Vmax₂ N J Ntail
    hbase hpbad hZ hZbig hη hηsmall hC₂ hCd₂.le hCt₂.le hTmax (sq_nonneg Γ) hE hU hB hH
    hKU hellU hBU hHU heU hprogress (by linarith) hVmax₂ hw₂₅ hw₂₆ (hwb₂' 5) (hwb₂' 6)
    hb₁ hb₂ htail hterminal (ih false)
  let D₁:=canonicalBudgetCoefficient C₁ Cd₁ Ct₁ Tmax Clo Chi (M+7) Vmax₁
  let D₂:=canonicalBudgetCoefficient C₂ Cd₂ Ct₂ Tmax Clo Chi (M+7) Vmax₂
  have hD₁ : 0 ≤ D₁:=canonicalBudgetCoefficient_nonneg _ _ _ _ _ _ _ _ hC₁ hCd₁.le hCt₁.le hTmax hClo.le hChi.le
  have hD₂ : 0 ≤ D₂:=canonicalBudgetCoefficient_nonneg _ _ _ _ _ _ _ _ hC₂ hCd₂.le hCt₂.le hTmax hClo.le hChi.le
  have hpairs:=canonicalPairBudget_normalized X F B Ksrc (Ksrc/Z^η) Cf
    ((globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss) U (deltaLoss+8*ε) E t
    (D₁*Γ^2) (D₂*Γ^2) _ _ J hX hF0.le hB0 hK0.le hKcut hCf
    (Real.rpow_nonneg (globalFirstRowCap_pos _ _ _ _ hKcut hell (zero_lt_one.trans_le hBsup) hF0).le _)
    (zero_le_one.trans hU) (zero_le_one.trans hE) (mul_nonneg hD₁ (sq_nonneg Γ)) (mul_nonneg hD₂ (sq_nonneg Γ))
    (by simpa only [mul_assoc] using hbL) (by simpa only [mul_assoc] using hbR)
  have hsqrt : Real.sqrt (D₁*Γ^2)*Real.sqrt (D₂*Γ^2)=Real.sqrt D₁*Real.sqrt D₂*Γ^2 := by
    rw [Real.sqrt_mul hD₁,Real.sqrt_mul hD₂,Real.sqrt_sq_eq_abs]
    calc
      _ = Real.sqrt D₁*Real.sqrt D₂*(|Γ|^2) := by ring
      _ = _ := by rw [sq_abs]
  have hscaled:=mul_le_mul_of_nonneg_left he hB0.le
  calc
    _  ≤  B*(‖canonicalSourceZero p hp hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
        (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m g g rowMajorant Ksrc (X/B^3)‖+
       ‖canonicalSourceTail p hp hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
        (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m g g rowMajorant Ksrc (Ksrc/Z^η) (X/B^3)‖)+
       B*((X/B^3)*(Real.exp 1*B)^2*F*(Ksrc/(Ksrc/Z^η))*Cf*
         (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss*
         Real.sqrt (globalFirstQuantitativeBudget p hg pool blocks (normHeightTwist Ψ t) m w₁
           C₁ Cd₁ Ct₁ (Γ^2) ε (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U (N+1) (2*J) Ntail true)*
         Real.sqrt (globalFirstQuantitativeBudget p hg pool blocks (normHeightTwist Ψ t) m w₂
           C₂ Cd₂ Ct₂ (Γ^2) ε (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U (N+1) (2*J) Ntail false)) :=
      hscaled.trans_eq (by ring)
    _  ≤  _ := by
      apply (add_le_add le_rfl hpairs).trans_eq
      calc
        _ = _ := by rw [show Real.exp 5*Cf*Real.sqrt (D₁*Γ^2)*Real.sqrt (D₂*Γ^2)=
            Real.exp 5*Cf*(Real.sqrt (D₁*Γ^2)*Real.sqrt (D₂*Γ^2)) by ring,hsqrt];ring


end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory JointLogSeparation CanonicalCoefficientClass RayFourExpansion
open scoped Classical SchwartzMap ContDiff

theorem reopenedCanonicalRow_polynomial_step
    (g V : 𝓢(ℝ,ℂ)) (A M Nv : ℝ) (hM : 0 ≤ M) (hNv : 0 ≤ Nv)
    (hgM : ∀t,g t≠0→|t| ≤ M) (hV : ∀t,V t≠0→|t| ≤ Nv)
    (hWin : ∀t,g t≠0→V t=1)
    (ε deltaLoss η : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (hη : 0<η) (hηsmall : η ≤ (1:ℝ)/1000)
    (J : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ) (C : ℝ), 0 ≤ C ∧
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t| ≤ M+7) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t| ≤ M+7) ∧
      ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i=>Ideal.span {p i})) (_hpr : ∀i,lambda^2∣p i-1)
      (base : O→*ℂ) (bad : Ideal O) (Z : ℝ) (Ψ : O→*ℂ) (m : O)
      (labels : Finset (Ideal O)) (X F Ksrc : ℝ)
      (_hstate : CanonicalStateCondition base bad Z η Ψ m labels X F Ksrc)
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : Ideal O→(ι→₀ℕ)→ℂ)
      (Γ t B E : ℝ),
      (∀u,‖base u‖ ≤ 1) → (∀i,IsCoprime (Ideal.span {p i}) bad) →
      1<Z → Real.exp 9000 ≤ Z → 1 ≤ X → X ≤ Z^3 → F ≤ Z^3 →
      0 ≤ Γ → 1 ≤ E → 1 ≤ B → B^3 ≤ Real.exp A*X →
      Z^((1:ℝ)/1000) ≤ (Real.exp 1*B)*F →
      (∀I∈labels,∀v∈Q,‖β I v‖ ≤ Γ) → (∀v∈Q,v.support⊆pool) →
      (∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2 ≤ Real.exp 1*B) →
      (∀side : Bool, let windows:=if side then windows₁ else windows₂
        ∀(Ψ' : O→*ℂ) (m' : O) (labels' : Finset (Ideal O)) (X' F' K' : ℝ),
        CanonicalStateCondition base bad Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z Ksrc → ∀s : ℝ,
        (canonicalLogEnergy p hg (fun _=>1) pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile true (windows 5)) X' K' ≤ E*(X'*F')^2*(1+‖s‖)^(2*J)) ∧
        (canonicalLogEnergy p hg (fun _=>1) pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile false (windows 6)) X' K' ≤ E*(X'*F')^2*(1+‖s‖)^(2*J))) →
      let Ψt:=normHeightTwist Ψ t
      let bs:=reopenedCubeFamily Q
      let a:=reopenedPairCoefficient β
      B*(∑I∈labels,nonzeroRowMajorantSum
         (reopenedCanonicalRow p hg pool Q (β I) Ψ m
           (cubicIdealGenerator I)
           (fun S=>frequencyTwist g t (columnLog p (X/B^3) S))) Ksrc).re ≤ 
      B*(‖canonicalSourceZero p hp hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc (X/B^3)‖+
         ‖canonicalSourceTail p hp hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc (Ksrc/Z^η) (X/B^3)‖)+
      C*Γ^2*(X*F)^2*Z^(η+17*deltaLoss+32*ε)*E*(1+‖t‖)^(2*J) := by
  obtain ⟨N,hN,hterminal⟩ := reopening_terminal_order η 0 hη
  obtain ⟨w₁,w₂,Cf,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,Clo,Chi,Vmax₁,Vmax₂,
    hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,hClo,hChi,hV₁,hV₂,
    hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,hstep⟩ :=
    reopenedCanonicalRow_state_step g V M Nv hM hNv hgM hV hWin ε deltaLoss hε hδ N J 84
  let Cs:=reopeningScaleConstant A M
  let Tmax:=4096*Cs^21
  have hCs : 1 ≤ Cs:=reopeningScaleConstant_one A M
  have hTmax : 0 ≤ Tmax:=by dsimp [Tmax]; positivity
  let D₁:=canonicalBudgetCoefficient C₁ Cd₁ Ct₁ Tmax Clo Chi (M+7) Vmax₁
  let D₂:=canonicalBudgetCoefficient C₂ Cd₂ Ct₂ Tmax Clo Chi (M+7) Vmax₂
  let Cbase:=Real.exp 5*Cf*Real.sqrt D₁*Real.sqrt D₂
  let Cpow:=((Real.exp 1)^8)^deltaLoss*Cs^(deltaLoss+8*ε)
  have hCbase : 0 ≤ Cbase:=by dsimp [Cbase]; positivity
  have hCpow : 0 ≤ Cpow:=by dsimp [Cpow]; positivity
  refine ⟨w₁,w₂,Cbase*Cpow,mul_nonneg hCbase hCpow,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro ι _ p hp _ hcop hg hc hinj hpr base bad Z Ψ m labels X F Ksrc hstate pool Q β
    Γ t B E hbase hpbad hZ hZbig hX hXZ hFZ hΓ hE hB hactive hprogress hβ hQ hQB ih
  have hs:=reopeningAuxiliaryScale_bounds A M 1 Z η X F Ksrc B (by norm_num) hZ.le hη.le
    hX hXZ hstate.label_ge_one hFZ hstate.row_ge_one hstate.row_le_global hB hactive
  norm_num [reopeningAuxiliaryScale,Real.rpow_natCast] at hs
  obtain ⟨hU,hKU,hellU,hBU,hFU,hHU,heU,hMU,hiU⟩:=hs
  have htail : (Cs*Z^4)*globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F
      (Cs*Z^4) Z 84 ≤ Tmax := by
    have hh:=globalFirstWeightedTail_reopening_nat_decay A M Z η X F Ksrc B 0
      hZ.le hη.le hX hXZ hstate.label_ge_one hFZ hstate.row_ge_one hstate.row_le_global hB hactive
    simpa only [Nat.cast_zero,neg_zero,Real.rpow_zero,mul_one,zero_add] using hh
  have ht : (Ksrc/Z^η)/Z^(η*(N:ℝ)) ≤ 1 := by
    simpa only [neg_zero,Real.rpow_zero] using hterminal Z Ksrc hZ.le
      (zero_le_one.trans hstate.row_ge_one) hstate.row_le_global
  have hb:=hstep p hp hcop hg hc hinj hpr base bad Z η Ψ m labels X F Ksrc hstate pool Q β
    Γ t B Z (Cs*Z^(4:ℕ)) Tmax E hbase hpbad hZ hZbig hη.le hηsmall hΓ hE hU hB
    (zero_le_one.trans hZ.le) hTmax hKU hellU hBU hHU heU hMU hprogress hβ hQ hQB htail ht ih
  dsimp only at hb ⊢
  have hm:=reopening_recursive_with_ratio A M Z η X F Ksrc B deltaLoss ε hZ.le hη.le
    (by linarith) hX hXZ hstate.label_ge_one hFZ hstate.row_ge_one hB hδ.le hε.le
  have hx := mul_le_mul_of_nonneg_left hm
    (show 0 ≤ Cbase*Γ^2*(X*F)^2*E*(1+‖t‖)^(2*J) by positivity)
  apply hb.trans
  apply add_le_add le_rfl
  convert hx using 1 <;> dsimp [Cbase,Cpow,D₁,D₂,Cs] <;> ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory JointLogSeparation CanonicalCoefficientClass RayFourExpansion
open scoped Classical SchwartzMap ContDiff

theorem CanonicalStateCondition.row_bound
    {base : O→*ℂ} {bad : Ideal O} {Z η : ℝ} {Ψ : O→*ℂ} {m : O}
    {labels : Finset (Ideal O)} {X F K : ℝ}
    (h : CanonicalStateCondition base bad Z η Ψ m labels X F K)
    (hZ : 1 ≤ Z) (hη : 0 ≤ η) (hbudget : 3000*η ≤ (1:ℝ)/40) :
    K ≤ (X*F)*Z^(-((1:ℝ)/40)) := by
  have hn := element_norm_ge_one m h.mask_ne_zero
  calc
    K = K*1 := (mul_one _).symm
    _  ≤  K*‖ringComplex m‖^2 :=
      mul_le_mul_of_nonneg_left hn (zero_le_one.trans h.row_ge_one)
    _  ≤  _ := h.invariant_reserved hZ hη hbudget

theorem canonicalFirstZero_normalization (C Γ X F K B Z ε : ℝ)
    (hC : 0 ≤ C) (hX : 0<X) (hF : 0 ≤ F) (hK : 0 ≤ K) (hB : 1 ≤ B)
    (hrow : K ≤ (X*F)*Z^(-((1:ℝ)/40))) :
    B*(C*(Real.exp 1*B)^(1+ε)*(X/B^3)*F*Γ^2*K) ≤ 
      (C*(Real.exp 1)^(1+ε))*B^ε*Γ^2*(X*F)^2*Z^(-((1:ℝ)/40)) := by
  have hB0 : 0<B := zero_lt_one.trans_le hB
  have hc : 0 ≤ C*(Real.exp 1)^(1+ε)*B^ε*Γ^2*(X*F) := by
    positivity
  calc
    _ = (C*(Real.exp 1)^(1+ε)*B^ε*Γ^2*(X*F))*K/B := by
      rw [Real.mul_rpow (Real.exp_pos _).le hB0.le,Real.rpow_add hB0,Real.rpow_one]
      field_simp

    _  ≤  (C*(Real.exp 1)^(1+ε)*B^ε*Γ^2*(X*F))*K :=
      div_le_self (mul_nonneg hc hK) hB
    _  ≤  (C*(Real.exp 1)^(1+ε)*B^ε*Γ^2*(X*F))*((X*F)*Z^(-((1:ℝ)/40))) :=
      mul_le_mul_of_nonneg_left hrow hc
    _ = _ := by ring


theorem canonicalFirstTail_numerator (C Γ B₀ B lengthScale F K U ε : ℝ)
    (hC : 0 ≤ C) (_hB₀ : 0 ≤ B₀) (hB : 0 ≤ B) (hL : 0 ≤ lengthScale) (hF : 0 ≤ F)
    (hK : 1 ≤ K) (hU : 1 ≤ U) (hε : 0 ≤ ε)
    (hB₀U : B₀ ≤ U) (hBU : B ≤ U) (hLU : lengthScale ≤ U) (hFU : F ≤ U) (hKU : K ≤ U) :
    B₀*(C*B^(4+ε)*lengthScale^4*F*Γ^2*K*(1+lengthScale^3*B^4/K)^2) ≤ 
      4*C*Γ^2*U^(25+ε) := by
  have hU0 : 0<U := zero_lt_one.trans_le hU
  have hK0 : 0<K := zero_lt_one.trans_le hK
  have hratio : lengthScale^3*B^4/K ≤ U^7 := by
    calc
      _  ≤  lengthScale^3*B^4 := div_le_self (mul_nonneg (pow_nonneg hL _) (pow_nonneg hB _)) hK
      _  ≤  U^3*U^4 := by gcongr
      _ = U^7 := by ring
  have hU7 : 1 ≤ U^7 := one_le_pow₀ hU
  have hs : (1+lengthScale^3*B^4/K)^2 ≤ 4*U^14 := by
    have hnonneg : 0 ≤ lengthScale^3*B^4/K := div_nonneg (by positivity) hK0.le
    have ha : 1+lengthScale^3*B^4/K ≤ 2*U^7 := by linarith
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+lengthScale^3*B^4/K) ha 2
    nlinarith [show (U^7)^2=U^14 by ring]
  calc
    _  ≤  U*(C*U^(4+ε)*U^4*U*Γ^2*U*(4*U^14)) := by
      gcongr
    _ = _ := by
      rw [Real.rpow_add hU0,Real.rpow_add hU0]
      norm_num
      ring

theorem canonicalCutoff_ratio (Ksrc Z η : ℝ) (hK : 0<Ksrc) (hZ : 0<Z) :
    Ksrc/(Ksrc/Z^η)=Z^η := by
  have hz := (Real.rpow_pos_of_pos hZ η).ne'
  field_simp

theorem canonicalFirstTail_polynomial (C Γ B₀ B lengthScale F Ksrc U Z η ε M : ℝ) (A : ℕ)
    (hC : 0 ≤ C) (hB₀ : 0 ≤ B₀) (hB : 0 ≤ B) (hL : 0 ≤ lengthScale) (hF : 0 ≤ F)
    (hK : 1 ≤ Ksrc) (hU : 1 ≤ U) (hε : 0 ≤ ε) (hZ : 0<Z)
    (hB₀U : B₀ ≤ U) (hBU : B ≤ U) (hLU : lengthScale ≤ U) (hFU : F ≤ U) (hKU : Ksrc ≤ U) :
    B₀*(C*B^(4+ε)*lengthScale^4*F*Γ^2*Ksrc*(1+lengthScale^3*B^4/Ksrc)^2/
      (1+(Ksrc/(Ksrc/Z^η))/Real.exp (2*M))^A) ≤ 
      (4*C*Γ^2*(Real.exp (2*M))^A)*U^(25+ε)/Z^(η*(A:ℝ)) := by
  have hK0 : 0<Ksrc := zero_lt_one.trans_le hK
  have hη : 0<Z^η := Real.rpow_pos_of_pos hZ _
  have hden : 0<(Z^η/Real.exp (2*M))^A := pow_pos (div_pos hη (Real.exp_pos _)) _
  rw [canonicalCutoff_ratio Ksrc Z η hK0 hZ]
  calc
    _ = (B₀*(C*B^(4+ε)*lengthScale^4*F*Γ^2*Ksrc*(1+lengthScale^3*B^4/Ksrc)^2))/(1+Z^η/Real.exp (2*M))^A := by ring
    _  ≤  (4*C*Γ^2*U^(25+ε))/(1+Z^η/Real.exp (2*M))^A :=
      div_le_div_of_nonneg_right (canonicalFirstTail_numerator C Γ B₀ B lengthScale F Ksrc U ε
        hC hB₀ hB hL hF hK hU hε hB₀U hBU hLU hFU hKU) (by positivity)
    _  ≤  (4*C*Γ^2*U^(25+ε))/(Z^η/Real.exp (2*M))^A := by
      exact div_le_div_of_nonneg_left (by positivity) hden
        (pow_le_pow_left₀ (div_pos hη (Real.exp_pos _)).le (by linarith) A)
    _ = _ := by
      rw [div_pow,←Real.rpow_natCast (Z^η) A,←Real.rpow_mul hZ.le]
      simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
      ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory JointLogSeparation CanonicalCoefficientClass RayFourExpansion
open scoped Classical SchwartzMap ContDiff

theorem canonicalFirstTail_reopening_order (η ε R : ℝ) (hη : 0<η) (hε : 0 ≤ ε) :
    ∃N : ℕ,0<N ∧ ∀Cscale C Γ B₀ B lengthScale F Ksrc Z M : ℝ,
      1 ≤ Cscale → 0 ≤ C → 0 ≤ B₀ → 0 ≤ B → 0 ≤ lengthScale → 0 ≤ F → 1 ≤ Ksrc → 1 ≤ Z →
      B₀ ≤ Cscale*Z^4 → B ≤ Cscale*Z^4 → lengthScale ≤ Cscale*Z^4 → F ≤ Cscale*Z^4 → Ksrc ≤ Cscale*Z^4 →
      B₀*(C*B^(4+ε)*lengthScale^4*F*Γ^2*Ksrc*(1+lengthScale^3*B^4/Ksrc)^2/
        (1+(Ksrc/(Ksrc/Z^η))/Real.exp (2*M))^N) ≤ 
        (4*C*Γ^2*(Real.exp (2*M))^N*Cscale^(25+ε))*Z^(-R) := by
  obtain ⟨N,hN,horder⟩ := exists_polynomial_cutoff_order 4 (25+ε) η R hη
  refine ⟨N,hN,?_⟩
  intro Cscale C Γ B₀ B lengthScale F Ksrc Z M hCs hC hB₀ hB hL hF hK hZ hB₀U hBU hLU hFU hKU
  have hU : 1 ≤ Cscale*Z^4 := one_le_mul_of_one_le_of_one_le hCs (one_le_pow₀ hZ)
  have hb := canonicalFirstTail_polynomial C Γ B₀ B lengthScale F Ksrc (Cscale*Z^4) Z η ε M N
    hC hB₀ hB hL hF hK hU hε (by linarith) hB₀U hBU hLU hFU hKU
  have ho := horder Cscale Z (by linarith) hZ
  have ho' : (Cscale*Z^4)^(25+ε)/Z^(η*N) ≤ Cscale^(25+ε)*Z^(-R) := by
    norm_num [Real.rpow_natCast] at ho ⊢
    exact ho
  apply hb.trans
  have hm := mul_le_mul_of_nonneg_left ho'
    (show 0 ≤ 4*C*Γ^2*(Real.exp (2*M))^N by positivity)
  convert hm using 1 <;> ring


end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory JointLogSeparation CanonicalCoefficientClass RayFourExpansion
open scoped Classical SchwartzMap ContDiff

theorem reopenedCanonicalFirstErrors_power
    (g : 𝓢(ℝ,ℂ)) (A M : ℝ) (hgM : ∀t,g t≠0→|t| ≤ M)
    (ε η : ℝ) (hε : 0<ε) (hη : 0<η) (hbudget : 3000*η ≤ (1:ℝ)/40) :
    ∃C : ℝ,0 ≤ C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (hpr:∀i,lambda^2∣p i-1)
      (base : O→*ℂ) (bad : Ideal O) (Z : ℝ) (Ψ : O→*ℂ) (m : O)
      (labels : Finset (Ideal O)) (X F Ksrc : ℝ)
      (_hstate : CanonicalStateCondition base bad Z η Ψ m labels X F Ksrc)
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : Ideal O→(ι→₀ℕ)→ℂ)
      (Γ t B : ℝ),
      (∀u,‖base u‖ ≤ 1) → 1 ≤ Z → 1 ≤ X → X ≤ Z^3 → F ≤ Z^3 →
      0 ≤ Γ → 1 ≤ B → B^3 ≤ Real.exp A*X →
      (∀I∈labels,∀v∈Q,‖β I v‖ ≤ Γ) →
      (∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2 ≤ Real.exp 1*B) →
      let Ψt:=normHeightTwist Ψ t
      let bs:=reopenedCubeFamily Q
      let a:=reopenedPairCoefficient β
      B*(‖canonicalSourceZero p hp hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc (X/B^3)‖+
         ‖canonicalSourceTail p hp hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc (Ksrc/Z^η) (X/B^3)‖) ≤ 
      C*Γ^2*(X*F)^2*Z^(3*ε-(1:ℝ)/40) := by
  obtain ⟨N,hN,horder⟩:=canonicalFirstTail_reopening_order η ε ((1:ℝ)/40) hη hε.le
  obtain ⟨Cz,Ct,hCz,hCt,herrors⟩:=reopenedCanonicalFirstErrors g M hgM ε hε N
  let Cs:=reopeningScaleConstant A M
  have hCs : 1 ≤ Cs:=reopeningScaleConstant_one A M
  let Cz':=Cz*(Real.exp 1)^(1+ε)*Cs^ε
  let Ct':=4*Ct*(Real.exp (2*M))^N*Cs^(25+ε)
  have hCz' : 0 ≤ Cz':=by dsimp [Cz']; positivity
  have hCt' : 0 ≤ Ct':=by dsimp [Ct']; positivity
  refine ⟨Cz'+Ct',add_nonneg hCz' hCt',?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr base bad Z Ψ m labels X F Ksrc hstate pool Q β
    Γ t B hbase hZ hX hXZ hFZ hΓ hB hactive hβ hQB
  have hZ0 : 0<Z:=zero_lt_one.trans_le hZ
  have hX0 : 0<X:=zero_lt_one.trans_le hX
  have hB0 : 0<B:=zero_lt_one.trans_le hB
  have hK0 : 0<Ksrc:=zero_lt_one.trans_le hstate.row_ge_one
  have hF0 : 0<F:=zero_lt_one.trans_le hstate.label_ge_one
  have hs:=reopeningAuxiliaryScale_bounds A M 1 Z η X F Ksrc B (by norm_num) hZ hη.le
    hX hXZ hstate.label_ge_one hFZ hstate.row_ge_one hstate.row_le_global hB hactive
  norm_num [reopeningAuxiliaryScale,Real.rpow_natCast] at hs
  obtain ⟨hU,hKU,hellU,hBU,hFU,hHU,heU,hMU,hiU⟩:=hs
  let U:=Cs*Z^(4:ℕ)
  have hBsup : 1 ≤ Real.exp 1*B:=one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) hB
  have hB0U : B ≤ U := (le_mul_of_one_le_left hB0.le (Real.one_le_exp (by norm_num))).trans hBU
  have hKsrcU : Ksrc ≤ U := by
    calc
      _  ≤  Z^3:=hstate.row_le_global
      _  ≤  Z^4:=by nlinarith [sq_nonneg Z,show 0 ≤ Z^2*(Z-1)^2 by positivity]
      _  ≤  U:=le_mul_of_one_le_left (by positivity) hCs
  have herr:=herrors p hp hcop hg hinj hc hpr pool Q labels β Ψ m Γ t Ksrc (Ksrc/Z^η)
    (X/B^3) (Real.exp 1*B) F U hΓ hK0 (by positivity) (by positivity) hBsup
    hstate.label_ge_one hU hMU (fun u=>hstate.coefficient.norm_le hbase u) hβ hQB
    (fun I hI=>(hstate.label_bounds I hI).1) (fun I hI=>(hstate.label_bounds I hI).2.2.2)
  dsimp only at herr ⊢
  have hzero:=canonicalFirstZero_normalization Cz Γ X F Ksrc B Z ε hCz hX0 hF0.le hK0.le hB
    (hstate.row_bound hZ hη.le hbudget)
  have hBpow : B^ε ≤ Cs^ε*Z^(3*ε) := by
    have hh : B ≤ Cs*Z^3 := (le_mul_of_one_le_left hB0.le (Real.one_le_exp (by norm_num))).trans
      (reopening_cube_bound A M Z X B hZ hX hXZ hB hactive)
    apply (Real.rpow_le_rpow hB0.le hh hε.le).trans_eq
    rw [Real.mul_rpow (by linarith) (by positivity),←Real.rpow_natCast_mul hZ0.le]
    norm_num
  have hz : B*‖canonicalSourceZero p hp hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
      (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m g g rowMajorant Ksrc (X/B^3)‖ ≤ 
      Cz'*Γ^2*(X*F)^2*Z^(3*ε-(1:ℝ)/40) := by
    apply ((mul_le_mul_of_nonneg_left herr.1 hB0.le).trans hzero).trans
    calc
      _  ≤  (Cz*(Real.exp 1)^(1+ε))*(Cs^ε*Z^(3*ε))*Γ^2*(X*F)^2*Z^(-((1:ℝ)/40)) := by gcongr
      _ = _ := by rw [show 3*ε-(1:ℝ)/40=3*ε+(-((1:ℝ)/40)) by ring,Real.rpow_add hZ0]; dsimp [Cz']; ring
  have ht0:=horder Cs Ct Γ B (Real.exp 1*B) U F Ksrc Z M hCs hCt hB0.le
    (by positivity) (by positivity) hF0.le hstate.row_ge_one hZ hB0U hBU le_rfl hFU hKsrcU
  have ht : B*‖canonicalSourceTail p hp hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
      (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m g g rowMajorant Ksrc (Ksrc/Z^η) (X/B^3)‖ ≤ 
      Ct'*Γ^2*(X*F)^2*Z^(3*ε-(1:ℝ)/40) := by
    have hpow : Z^(-((1:ℝ)/40)) ≤ Z^(3*ε-(1:ℝ)/40):=
      Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
    have hXF : 1 ≤ (X*F)^2:=one_le_pow₀ (one_le_mul_of_one_le_of_one_le hX hstate.label_ge_one)
    apply ((mul_le_mul_of_nonneg_left herr.2 hB0.le).trans ht0).trans
    calc
      _ = Ct'*Γ^2*Z^(-((1:ℝ)/40)):=by dsimp [Ct']; ring
      _  ≤  Ct'*Γ^2*((X*F)^2*Z^(3*ε-(1:ℝ)/40)):=by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCt' (sq_nonneg Γ))
        exact hpow.trans (le_mul_of_one_le_left (by positivity) hXF)
      _ = _:=by ring
  rw [mul_add]
  exact (add_le_add hz ht).trans_eq (by ring)

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory JointLogSeparation CanonicalCoefficientClass RayFourExpansion
open scoped Classical SchwartzMap ContDiff

theorem reopenedCanonicalRow_closed_step
    (g V : 𝓢(ℝ,ℂ)) (A M Nv : ℝ) (hM : 0 ≤ M) (hNv : 0 ≤ Nv)
    (hgM : ∀t,g t≠0→|t| ≤ M) (hV : ∀t,V t≠0→|t| ≤ Nv)
    (hWin : ∀t,g t≠0→V t=1)
    (ε deltaLoss η : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (hη : 0<η) (hηsmall : η ≤ (1:ℝ)/1000)
    (hbudget : 3000*η ≤ (1:ℝ)/40) (J : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ) (C : ℝ), 0 ≤ C ∧
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t| ≤ M+7) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t| ≤ M+7) ∧
      ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i=>Ideal.span {p i})) (_hpr : ∀i,lambda^2∣p i-1)
      (base : O→*ℂ) (bad : Ideal O) (Z : ℝ) (Ψ : O→*ℂ) (m : O)
      (labels : Finset (Ideal O)) (X F Ksrc : ℝ)
      (_hstate : CanonicalStateCondition base bad Z η Ψ m labels X F Ksrc)
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : Ideal O→(ι→₀ℕ)→ℂ)
      (Γ t B E : ℝ),
      (∀u,‖base u‖ ≤ 1) → (∀i,IsCoprime (Ideal.span {p i}) bad) →
      1<Z → Real.exp 9000 ≤ Z → 1 ≤ X → X ≤ Z^3 → F ≤ Z^3 →
      0 ≤ Γ → 1 ≤ E → 1 ≤ B → B^3 ≤ Real.exp A*X →
      Z^((1:ℝ)/1000) ≤ (Real.exp 1*B)*F →
      (∀I∈labels,∀v∈Q,‖β I v‖ ≤ Γ) → (∀v∈Q,v.support⊆pool) →
      (∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2 ≤ Real.exp 1*B) →
      (∀side : Bool, let windows:=if side then windows₁ else windows₂
        ∀(Ψ' : O→*ℂ) (m' : O) (labels' : Finset (Ideal O)) (X' F' K' : ℝ),
        CanonicalStateCondition base bad Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z Ksrc → ∀s : ℝ,
        (canonicalLogEnergy p hg (fun _=>1) pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile true (windows 5)) X' K' ≤ E*(X'*F')^2*(1+‖s‖)^(2*J)) ∧
        (canonicalLogEnergy p hg (fun _=>1) pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile false (windows 6)) X' K' ≤ E*(X'*F')^2*(1+‖s‖)^(2*J))) →
      B*(∑I∈labels,nonzeroRowMajorantSum
         (reopenedCanonicalRow p hg pool Q (β I) Ψ m
           (cubicIdealGenerator I)
           (fun S=>frequencyTwist g t (columnLog p (X/B^3) S))) Ksrc).re ≤ 
      C*Γ^2*(X*F)^2*Z^(η+17*deltaLoss+32*ε)*E*(1+‖t‖)^(2*J) := by
  obtain ⟨w₁,w₂,Cp,hCp,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,hstep⟩ :=
    reopenedCanonicalRow_polynomial_step g V A M Nv hM hNv hgM hV hWin ε deltaLoss η hε hδ hη hηsmall J
  obtain ⟨Ce,hCe,herrors⟩:=reopenedCanonicalFirstErrors_power g A M hgM ε η hε hη hbudget
  refine ⟨w₁,w₂,Ce+Cp,add_nonneg hCe hCp,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro ι _ p hp _ hcop hg hc hinj hpr base bad Z Ψ m labels X F Ksrc hstate pool Q β
    Γ t B E hbase hpbad hZ hZbig hX hXZ hFZ hΓ hE hB hactive hprogress hβ hQ hQB ih
  have hpstep:=hstep p hp hcop hg hc hinj hpr base bad Z Ψ m labels X F Ksrc hstate pool Q β
    Γ t B E hbase hpbad hZ hZbig hX hXZ hFZ hΓ hE hB hactive hprogress hβ hQ hQB ih
  have herr:=herrors p hp hcop hg hinj hc hpr base bad Z Ψ m labels X F Ksrc hstate pool Q β
    Γ t B hbase hZ.le hX hXZ hFZ hΓ hB hactive hβ hQB
  dsimp only at hpstep herr
  have hpow : Z^(3*ε-(1:ℝ)/40) ≤ Z^(η+17*deltaLoss+32*ε):=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hEH : 1 ≤ E*(1+‖t‖)^(2*J):=
    one_le_mul_of_one_le_of_one_le hE (one_le_pow₀ (by linarith [norm_nonneg t]))
  have he : Ce*Γ^2*(X*F)^2*Z^(3*ε-(1:ℝ)/40) ≤ 
      Ce*Γ^2*(X*F)^2*Z^(η+17*deltaLoss+32*ε)*E*(1+‖t‖)^(2*J) := by
    calc
      _  ≤  Ce*Γ^2*(X*F)^2*Z^(η+17*deltaLoss+32*ε):=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _  ≤  (Ce*Γ^2*(X*F)^2*Z^(η+17*deltaLoss+32*ε))*(E*(1+‖t‖)^(2*J)):=
        le_mul_of_one_le_right (by positivity) hEH
      _ = _:=by ring
  apply hpstep.trans
  exact (add_le_add (herr.trans he) le_rfl).trans_eq (by ring)

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory JointLogSeparation CanonicalCoefficientClass RayFourExpansion
open scoped Classical SchwartzMap ContDiff

variable {ι:Type*} [DecidableEq ι] (p:ι→O) (hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal] (hg:∀i,lambda∉Ideal.span {p i})
include hp in
theorem CanonicalStateCondition.terminal_energy
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr:∀i,lambda^2∣p i-1)
    (pool : Finset ι) (base : O→*ℂ) (bad : Ideal O) (Z η : ℝ) (Ψ : O→*ℂ)
    (m : O) (labels : Finset (Ideal O)) (X F K : ℝ)
    (hstate : CanonicalStateCondition base bad Z η Ψ m labels X F K)
    (hbase : ∀u,‖base u‖ ≤ 1) (hZ : 1<Z) (hη : 0 ≤ η) (hbudget : 3000*η ≤ (1:ℝ)/40)
    (V : ℝ→ℂ) (A M t : ℝ) (hM : 0 ≤ M)
    (hV : ∀s,‖V s‖ ≤ M) (hVs : ∀s,V s≠0→|s| ≤ A)
    (hstop : fixedDepthRank Z K=0 ∨ X ≤ 1) :
    canonicalLogEnergy p hg (fun _=>1) pool (normHeightTwist Ψ t) m labels V X K ≤ 
      canonicalTerminalConstant A M*(X*F)^2 := by
  have hKF : K ≤ F := by
    rcases hstop with hr|hx
    · exact ((fixedDepthRank_zero_iff Z K hZ (zero_lt_one.trans_le hstate.row_ge_one)).mp hr).trans
        hstate.label_ge_one
    · have hi := hstate.invariant_reserved hZ.le hη hbudget
      have hz : Z^(-((1:ℝ)/40)) ≤ 1 := by
        simpa only [Real.rpow_zero] using
          Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num : -((1:ℝ)/40) ≤ 0)
      have hi' : K*‖ringComplex m‖^2 ≤ X*F :=
        hi.trans ((mul_le_mul_of_nonneg_left hz
          (mul_nonneg hstate.column_pos.le (zero_le_one.trans hstate.label_ge_one))).trans_eq (mul_one _))
      exact smallColumn_row_le_label m hstate.mask_ne_zero X F K hx
        (zero_le_one.trans hstate.label_ge_one) (zero_le_one.trans hstate.row_ge_one) hi'
  apply canonicalLogEnergy_terminal p hp hg hinj hpr (fun _=>1) (fun _=>by simp) pool (normHeightTwist Ψ t)
    (fun u=>(normHeightTwist_norm_le Ψ t u).trans (hstate.coefficient.norm_le hbase u)) m labels V X F K A M
    hstate.column_pos hstate.label_ge_one hstate.row_ge_one hKF hM hV hVs
  · exact fun I hI=>(hstate.label_bounds I hI).1
  · exact fun I hI=>(hstate.label_bounds I hI).2.2.2

end SecondPassArithmetic

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

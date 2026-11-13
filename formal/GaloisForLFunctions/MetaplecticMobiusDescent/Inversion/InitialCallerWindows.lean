/-
Initial caller windows adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.FirstLabelCells

/-!
# Initial caller windows

Window sources of the initial energy caller, primary pools and canonical puncture widths;
coprime source masks and retained window quotients; finite physical reassembly.
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
namespace InverseShortCanonicalNormalization
open Eisenstein  CompletedGauss CanonicalRowCompletion
open InverseMoment InverseReflectedPhase InverseTerminalWidths CompletedHeight
local notation "Eis" => Eisenstein.O
universe u v

theorem canonical_short_normalized_generator_energy_uniform_degree
    (lo hi : ℝ) (hlo : 0< lo) (W : ℝ→ℂ)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar eta : ℝ) (hL : 0≤ L) (hcstar : 0< cstar) (heta : 0< eta)
    (heta1 : eta≤1) (hetac : eta≤ cstar/100000) (rmax K : ℕ) :
    ∃ (degree : ℕ), ∀ (q : ℕ) (_hq : q≠0), ∃ (C Z₀ : ℝ),0< C ∧ 1< Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],
    ∀ (m : Eis) (_hm : m≠0) (Z N V M z₀ margin hcut d : ℝ),
      Z₀≤ Z → 0≤ N → 0≤ V → 0≤ M → M≤ L → V≤ L → z₀≤ L → 0≤ hcut → hcut≤ L →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤ Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤ margin →
      V≤ d → hcut≤ d+eta → d≤ cstar/200 →
    ∀ (labels : Finset (Ideal Eis)),
      (∀ f∈labels,Squarefree f ∧ (Ideal.absNorm f:ℝ)≤ Z^V) →
    ∀ (labelGenerator : Ideal Eis→Eis),(∀ f∈labels,Ideal.span {labelGenerator f}=f) →
    ∀ (T : Finset Eis),(∀ k∈T,k≠0 ∧ (Ideal.absNorm (Ideal.span {k}):ℝ)≤ Z^M) →
      Fintype.card σ≤ rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,lambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) → (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,1≤ H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤ H i) → (∏ i,H i)≤ Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ f∈labels,secondLabelWeight K f * ∑ k∈T,
        ‖((Z^(-(N+V)/2):ℝ):ℂ)*((Real.sqrt (Z^N):ℝ):ℂ)*markedShortCompletedSum
          (rowTwist Ψ (ActualFiber.maskElement q m) (labelGenerator f) k)
          (normTwistedSource W θ) (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)≤
        C*(1+‖θ‖)^degree*Z^(N+V-cstar/256) := by
  let : Fintype Eisˣ := @Fintype.ofFinite _ cubic_units_finite
  obtain ⟨degree,hu⟩ := canonical_short_completed_power_energy_uniform_degree lo hi hlo W hWs hW L cstar eta hL hcstar heta heta1 hetac rmax
  refine ⟨degree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,he⟩ := hu q hq
  obtain ⟨D,hD,hlabels⟩ := divisor_weight_sum K L (cstar/256) hL (by positivity)
  refine ⟨D*(6*C),Z₀,by positivity,hZ₀,?_⟩
  intro σ _ _ m hm Z N V M z₀ margin hcut d hZ hN hV hM hMc hVc hzc hcut0 hcutc
    hRn hmargin hreserve hVd hcutd hd labels hlabelsN labelGenerator hlabelGenerator T hT hcard lists H hdis hmax hgood hprime hodd
    hH1 hH hprod Ψ hΨ hperiod θ w hw
  have hz1 : 1≤ Z := (lt_of_lt_of_le hZ₀ hZ).le
  have hz : 0< Z := zero_lt_one.trans_le hz1
  let rows := T.image (fun k => Ideal.span {k})
  have hrows := CompletedUnitRows.image_span_nonzero_norm T (Z^M) hT
  let E := C*(1+‖θ‖)^degree*Z^(N+V-cstar/128)
  have hf (f : Ideal Eis) (hfl : f∈labels) :
      (∑ k∈T,‖markedShortCompletedSum
        (rowTwist Ψ (ActualFiber.maskElement q m) (labelGenerator f) k)
        (normTwistedSource W θ) (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)≤6*E := by
    let uf := CompletedUnitRows.rowUnit (labelGenerator f)
    have hgf : labelGenerator f=uf.val*cubicIdealGenerator f :=
      label_eq_rowUnit_generator f (hlabelsN f hfl).1.ne_zero (labelGenerator f) (hlabelGenerator f hfl)
    apply (CompletedUnitRows.sum_elements_le_units T
      (fun k => ‖markedShortCompletedSum
        (rowTwist Ψ (ActualFiber.maskElement q m) (labelGenerator f) k)
        (normTwistedSource W θ) (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)
      (fun k => sq_nonneg _)).trans
    have hb (u : Eisˣ) :
        (∑ I∈rows,‖markedShortCompletedSum
          (rowTwist Ψ (ActualFiber.maskElement q m) (labelGenerator f)
            (u.val*cubicIdealGenerator I))
          (normTwistedSource W θ) (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)≤ E := by
      have hh := he f (hlabelsN f hfl).1 m hm Z N V M z₀ margin hcut d
        hZ hN hM hMc hVc hzc hcut0 hcutc (hlabelsN f hfl).2 hRn hmargin hreserve hVd hcutd hd
        rows hrows hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod Ψ hΨ hperiod (uf^4*u) θ w hw
      simpa only [hgf,rowTwist_label_transfer,Units.val_mul,Units.val_pow_eq_pow_val,E,mul_assoc] using hh
    calc
      _ ≤ ∑ _u : Eisˣ,E := Finset.sum_le_sum (fun u _ => hb u)
      _ ≤ 6*E := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (by dsimp only [E]; positivity)
        exact_mod_cast EisensteinLatticeCount.card_units_le_six
  have hl : (∑ f∈labels,secondLabelWeight K f)≤ D*Z^(V+cstar/256) :=
    hlabels Z V hz1 hV hVc labels (fun f hfl => ⟨(hlabelsN f hfl).1.ne_zero,(hlabelsN f hfl).2⟩)
  simp_rw [normalization_norm_sq Z N V hz,←Finset.mul_sum]
  calc
    _ ≤ ∑ f∈labels,secondLabelWeight K f*(Z^(-V)*(6*E)) := by
      apply Finset.sum_le_sum
      intro f hfl
      apply mul_le_mul_of_nonneg_left _ (by unfold secondLabelWeight; positivity)
      exact mul_le_mul_of_nonneg_left (hf f hfl) (Real.rpow_nonneg hz.le _)
    _ = (∑ f∈labels,secondLabelWeight K f)*(Z^(-V)*(6*E)) := by rw [Finset.sum_mul]
    _ ≤ (D*Z^(V+cstar/256))*(Z^(-V)*(6*E)) := mul_le_mul_of_nonneg_right hl (by dsimp [E]; positivity)
    _ = (D*(6*C))*(1+‖θ‖)^degree*Z^(N+V-cstar/256) := by
      dsimp only [E]
      have hr : Z^(V+cstar/256)*Z^(-V)*Z^(N+V-cstar/128)=Z^(N+V-cstar/256) := by
        rw [←Real.rpow_add hz,←Real.rpow_add hz]
        congr 1
        ring
      calc
        _ = (D*(6*C))*(1+‖θ‖)^degree*(Z^(V+cstar/256)*Z^(-V)*Z^(N+V-cstar/128)) := by ring
        _ = _ := by rw [hr]

end InverseShortCanonicalNormalization

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open SchwartzPlanePoisson.CanonicalQuadraticSieve
open InverseInitialRayAttachment InverseFirstRayAttachment
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseShortCanonicalNormalization
open Eisenstein  CompletedGauss CanonicalRowCompletion
open InverseMoment InverseReflectedPhase InverseTerminalWidths CompletedHeight
local notation "Eis" => Eisenstein.O
universe u v

theorem canonical_short_normalized_energy_uniform_degree
    (lo hi : ℝ) (hlo : 0< lo) (W : ℝ→ℂ)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar eta : ℝ) (hL : 0≤ L) (hcstar : 0< cstar) (heta : 0< eta)
    (heta1 : eta≤1) (hetac : eta≤ cstar/100000) (rmax K : ℕ) :
    ∃ (degree : ℕ), ∀ (q : ℕ) (_hq : q≠0), ∃ (C Z₀ : ℝ),0< C ∧ 1< Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],
    ∀ (m : Eis) (_hm : m≠0) (Z N V M z₀ margin hcut d : ℝ),
      Z₀≤ Z → 0≤ N → 0≤ V → 0≤ M → M≤ L → V≤ L → z₀≤ L → 0≤ hcut → hcut≤ L →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤ Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤ margin →
      V≤ d → hcut≤ d+eta → d≤ cstar/200 →
    ∀ (labels : Finset (Ideal Eis)),
      (∀ f∈labels,Squarefree f ∧ (Ideal.absNorm f:ℝ)≤ Z^V) →
    ∀ (T : Finset Eis),(∀ k∈T,k≠0 ∧ (Ideal.absNorm (Ideal.span {k}):ℝ)≤ Z^M) →
      Fintype.card σ≤ rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,lambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) → (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,1≤ H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤ H i) → (∏ i,H i)≤ Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ f∈labels,secondLabelWeight K f * ∑ k∈T,
        ‖((Z^(-(N+V)/2):ℝ):ℂ)*((Real.sqrt (Z^N):ℝ):ℂ)*markedShortCompletedSum
          (rowTwist Ψ (ActualFiber.maskElement q m) (cubicIdealGenerator f) k)
          (normTwistedSource W θ) (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)≤
        C*(1+‖θ‖)^degree*Z^(N+V-cstar/256) := by
  obtain ⟨degree,hu⟩ := canonical_short_normalized_generator_energy_uniform_degree lo hi hlo W hWs hW L cstar eta hL hcstar heta heta1 hetac rmax K
  refine ⟨degree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,he⟩ := hu q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ m hm Z N V M z₀ margin hcut d hZ hN hV hM hMc hVc hzc hcut0 hcutc
    hRn hmargin hreserve hVd hcutd hd labels hlabelsN T hT hcard lists H hdis hmax hgood hprime hodd
    hH1 hH hprod Ψ hΨ hperiod θ w hw
  exact he m hm Z N V M z₀ margin hcut d hZ hN hV hM hMc hVc hzc hcut0 hcutc hRn
    hmargin hreserve hVd hcutd hd labels hlabelsN cubicIdealGenerator
    (fun f _ => span_cubicIdealGenerator f) T hT hcard lists H hdis hmax hgood hprime hodd
    hH1 hH hprod Ψ hΨ hperiod θ w hw

end InverseShortCanonicalNormalization

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialRayAttachment
open Eisenstein CanonicalCoefficientClass

theorem poolPrimary_injective (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, quadraticIdealAdmissible I) :
    Function.Injective (fun i : primePool F => Ideal.span {poolPrimary F i}) := by
  intro i k he
  change Ideal.span {poolPrimary F i} = Ideal.span {poolPrimary F k} at he
  rw [poolPrimary_span F hF, poolPrimary_span F hF] at he
  exact Subtype.ext he

theorem poolPrimary_primary (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, quadraticIdealAdmissible I) (i : primePool F) :
    lambda^2 ∣ poolPrimary F i-1 :=
  (primaryIdealPrime_spec i.val (poolPrimary_ne_zero F hF i)).2.2.2

end InverseInitialRayAttachment

namespace InverseInitialEnergyCallerGeometry
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialProfile InverseInitialClippedColumns 
local notation "Eis"=>Eisenstein.O
variable {ι:Type*}[DecidableEq ι]
  (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

include hp hcop in
theorem outerCoefficient_nonzero_coprime
    (Ψ:Eis→*ℂ)(j:Eis)(x:Point ι)(ρ:SecondRayIndex)
    (hn:outerCoefficient p hg Ψ j x ρ≠0) :
    IsCoprime (sourceIdeal p x.overlap) (sourceIdeal p x.common) := by
  apply sourceIdeal_coprime_of_not_mem p
  intro i hi hc
  have hmc : j*(∏k∈x.common,p k)∈Ideal.span {p i} := Ideal.mul_mem_left _ j hc
  have hz : primeCoprimeMask p x.overlap (j*(∏k∈x.common,p k))=0 := by
    unfold primeCoprimeMask
    apply Finset.prod_eq_zero hi
    simp only [if_pos (Ideal.mem_span_singleton.mp hmc), sub_self]
  apply hn
  simp only [outerCoefficient,initialColumn,hz,mul_zero,zero_mul,star_zero]

include hp hcop in
theorem original_nonzero_child_squarefree
    (Ψ:Eis→*ℂ)(j:Eis)(x:Source (ι:=ι) 0)(ρ:SecondRayIndex)
    (hd:x.divisor⊆x.common)
    (hn:outerCoefficient p hg Ψ j (sourcePoint x ∅ ∅) ρ≠0)(u:Eisˣ) :
    Squarefree (initialChild (toTuple p (sectorSource u x))).2.1 := by
  change Squarefree (sourceIdeal p x.divisor*sourceIdeal p x.overlap)
  have hc := outerCoefficient_nonzero_coprime p hp hcop hg Ψ j (sourcePoint x ∅ ∅) ρ hn
  change IsCoprime (sourceIdeal p x.overlap) (sourceIdeal p x.common) at hc
  have hdv := sourceIdeal_dvd p x.divisor x.common hd
  have hcd : IsCoprime (sourceIdeal p x.divisor) (sourceIdeal p x.overlap) :=
    hc.symm.of_isCoprime_of_dvd_left hdv
  exact squarefree_mul_iff.mpr ⟨hcd.isRelPrime,sourceIdeal_squarefree p hcop x.divisor,
    sourceIdeal_squarefree p hcop x.overlap⟩

omit [DecidableEq ι] in
theorem initial_child_label_norm (x:Source (ι:=ι) 0)(u:Eisˣ) :
    ((initialChild (toTuple p (sectorSource u x))).2.1.absNorm:ℝ)=
      (sourceIdeal p x.divisor).absNorm*(sourceIdeal p x.overlap).absNorm := by
  change ((sourceIdeal p x.divisor*sourceIdeal p x.overlap).absNorm:ℝ)=_
  simp only [map_mul,Nat.cast_mul]

include hp in

theorem initial_child_row_norm (hpr:∀i,lambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(u:Eisˣ) :
    ‖ringComplex (initialChild (toTuple p (sectorSource u x))).2.2‖^2=
      ((sourceIdeal p x.divisor).absNorm:ℝ)*‖ringComplex x.frequency‖^2 := by
  change ‖ringComplex (primaryIdealGenerator (sourceIdeal p x.divisor)*((u:Eis)^5*x.frequency))‖^2=_
  have he : primaryIdealGenerator (sourceIdeal p x.divisor)*((u:Eis)^5*x.frequency)=
      ((u^5:Eisˣ):Eis)*(primaryIdealGenerator (sourceIdeal p x.divisor)*x.frequency) := by
    change primaryIdealGenerator (sourceIdeal p x.divisor)*((u:Eis)^5*x.frequency)=
      (u:Eis)^5*(primaryIdealGenerator (sourceIdeal p x.divisor)*x.frequency)
    ring
  rw [he,map_mul,norm_mul,norm_ringComplex_unit,one_mul,map_mul,norm_mul,mul_pow]
  rw [ringComplex_norm_sq_eq_absNorm_span,sourceIdeal_gen p hp hpr]
  rfl

include hp in
theorem initial_child_row_ball (hpr:∀i,lambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(u:Eisˣ)(R:ℝ) :
    (initialChild (toTuple p (sectorSource u x))).2.2∈nonzeroChildFrequencyBall 1 R ↔
    0<((sourceIdeal p x.divisor).absNorm:ℝ)*‖ringComplex x.frequency‖^2 ∧
      ((sourceIdeal p x.divisor).absNorm:ℝ)*‖ringComplex x.frequency‖^2≤R := by
  rw [mem_nonzeroChildFrequencyBall 1 one_ne_zero,one_mul,initial_child_row_norm p hp hpr]

include hp in

theorem initial_child_enclosures
    (hpr:∀i,lambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(u:Eisˣ)(Z θ v H η:ℝ)(hZ:0<Z)
    (hd:((sourceIdeal p x.divisor).absNorm:ℝ)≤Z^(θ+η))
    (hv:((sourceIdeal p x.overlap).absNorm:ℝ)≤Z^(v+η))
    (hh:‖ringComplex x.frequency‖^2≤Z^(H+η)) :
    ((initialChild (toTuple p (sectorSource u x))).2.1.absNorm:ℝ)≤Z^(θ+v+2*η) ∧
      ‖ringComplex (initialChild (toTuple p (sectorSource u x))).2.2‖^2≤Z^(θ+H+2*η) := by
  rw [initial_child_label_norm p,initial_child_row_norm p hp hpr]
  constructor
  · apply (mul_le_mul hd hv (by positivity) (by positivity)).trans_eq
    rw [←Real.rpow_add hZ]
    congr 1
    ring
  · apply (mul_le_mul hd hh (by positivity) (by positivity)).trans_eq
    rw [←Real.rpow_add hZ]
    congr 1
    ring

end InverseInitialEnergyCallerGeometry

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialEnergyCallerSourceMask
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerGeometry InverseInitialProfile 
local notation "Eis"=>Eisenstein.O
variable {ι:Type*}[DecidableEq ι]
  (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

def coprimeSource (S:Finset (Source (ι:=ι) 0)) : Finset (Source (ι:=ι) 0) :=
  S.filter (fun x=>IsCoprime (sourceIdeal p x.overlap) (sourceIdeal p x.common))

include hp hcop in
theorem physicalBlock_coprimeSource
    (hpr:∀i,lambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(H:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ) :
    physicalBlock p hg (pointSource pool S) (w∘erasePoint) Ψ j H W₁ W₂ Φ Z D m =
    physicalBlock p hg (pointSource pool (coprimeSource p S)) (w∘erasePoint)
      Ψ j H W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [pointSource_sum,pointSource_sum,coprimeSource,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hc:IsCoprime (sourceIdeal p x.overlap) (sourceIdeal p x.common)
  · rw [if_pos hc]
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro N hN
    apply Finset.sum_eq_zero
    intro M hM
    apply Finset.sum_eq_zero
    intro ρ hρ
    have hxpoint : sourcePoint x N M∈pointSource pool S := by
      apply Finset.mem_biUnion.mpr
      refine ⟨x,hx,?_⟩
      apply Finset.mem_image.mpr
      exact ⟨(N,M),Finset.mem_product.mpr ⟨hN,hM⟩,rfl⟩
    have hv := pointSource_valid pool S hdiv hf _ hxpoint
    rw [physicalTerm_extracted p hp hcop hg hpr Ψ j H W₁ W₂ Φ Z D m _ hv ρ]
    have hz : outerCoefficient p hg Ψ j (sourcePoint x N M) ρ=0 := by
      by_contra hn
      exact hc (outerCoefficient_nonzero_coprime p hp hcop hg Ψ j (sourcePoint x N M) ρ hn)
    simp only [hz,zero_mul,mul_zero]

include hcop in
theorem retained_child_squarefree
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)
    {x:Source (ι:=ι) 0}(hx:x∈coprimeSource p S)(u:Eisˣ) :
    Squarefree (initialChild (toTuple p (sectorSource u x))).2.1 := by
  obtain ⟨hxs,hcoprime⟩ := Finset.mem_filter.mp hx
  change Squarefree (sourceIdeal p x.divisor*sourceIdeal p x.overlap)
  have hc := hcoprime.symm.of_isCoprime_of_dvd_left (sourceIdeal_dvd p _ _ (hdiv x hxs))
  exact squarefree_mul_iff.mpr ⟨hc.isRelPrime,sourceIdeal_squarefree p hcop _,
    sourceIdeal_squarefree p hcop _⟩

def childLabels (S:Finset (Source (ι:=ι) 0)) : Finset (Ideal Eis) :=
  (coprimeSource p S).image (fun x=>sourceIdeal p x.divisor*sourceIdeal p x.overlap)

include hp in
omit [DecidableEq ι] [∀i,(Ideal.span {p i}).IsMaximal] in
theorem childLabels_ne_zero (S:Finset (Source (ι:=ι) 0)) :
    ∀f∈childLabels p S,f≠0 := by
  intro f hf
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hf
  exact mul_ne_zero (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _)

include hcop in
theorem childLabels_squarefree (S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common) : ∀f∈childLabels p S,Squarefree f := by
  intro f hf
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hf
  exact retained_child_squarefree p hcop S hdiv hx 1

omit [DecidableEq ι] in
theorem child_label_mem (S:Finset (Source (ι:=ι) 0))
    {x:Source (ι:=ι) 0}(hx:x∈coprimeSource p S)(u:Eisˣ) :
    (initialChild (toTuple p (sectorSource u x))).2.1∈childLabels p S :=
  Finset.mem_image.mpr ⟨x,hx,rfl⟩

theorem nonzero_child_ball_neg (R:ℝ)(k:Eis)(hk:k∈nonzeroChildFrequencyBall 1 R) :
    -k∈nonzeroChildFrequencyBall 1 R := by
  rw [mem_nonzeroChildFrequencyBall 1 one_ne_zero,one_mul] at hk ⊢
  simpa only [map_neg,norm_neg] using hk

end InverseInitialEnergyCallerSourceMask

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialEnergyCallerRanges
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerGeometry InverseInitialEnergyCallerSourceMask
open InverseInitialProfile  CanonicalQuadraticSieve
local notation "Eis"=>Eisenstein.O
variable {ι:Type*}[DecidableEq ι]
  (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

include hp hcop hg

omit [DecidableEq ι] in
theorem sourceIdeal_admissible (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (S:Finset ι) : Admissible (sourceIdeal p S) := by
  refine ⟨sourceIdeal_ne_zero p hp S,sourceIdeal_squarefree p hcop S,?_⟩
  intro P hP
  obtain ⟨hprime,hdiv⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff
    (sourceIdeal_ne_zero p hp S)).mp hP
  rw [sourceIdeal,span_finset_prime_product] at hdiv
  obtain ⟨i,hi,hPi⟩ := (hprime.dvd_finsetProd_iff (fun i=>Ideal.span {p i})).mp hdiv
  have he := (prime_dvd_prime_iff_eq hprime (sourcePrime p i).property).mp hPi
  rw [he]
  exact ⟨hg i,hc i⟩

theorem retained_label_admissible (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)
    {x:Source (ι:=ι) 0}(hx:x∈coprimeSource p S)(u:Eisˣ) :
    Admissible (initialChild (toTuple p (sectorSource u x))).2.1 := by
  have hs := (supported_mul_iff (sourceIdeal p x.divisor) (sourceIdeal p x.overlap)).mpr
    ⟨admissible_supported (sourceIdeal_admissible p hp hcop hg hc _),
      admissible_supported (sourceIdeal_admissible p hp hcop hg hc _)⟩
  exact ⟨hs.1,retained_child_squarefree p hcop S hdiv hx u,hs.2⟩

theorem childLabels_subset_range
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (_hpr:∀i,lambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)
    (Z θ v η:ℝ)(hZ:0<Z)
    (hd:∀x∈coprimeSource p S,((sourceIdeal p x.divisor).absNorm:ℝ)≤Z^(θ+η))
    (hv:∀x∈coprimeSource p S,((sourceIdeal p x.overlap).absNorm:ℝ)≤Z^(v+η)) :
    childLabels p S⊆idealRange (Z^(θ+v+2*η)) := by
  intro f hf
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hf
  apply mem_idealRange.mpr
  refine ⟨(admissible_iff_native _).mp (retained_label_admissible p hp hcop hg hc S hdiv hx 1),?_⟩
  change ((sourceIdeal p x.divisor*sourceIdeal p x.overlap).absNorm:ℝ)≤_
  rw [map_mul,Nat.cast_mul]
  apply (mul_le_mul (hd x hx) (hv x hx) (by positivity) (by positivity)).trans_eq
  rw [←Real.rpow_add hZ]
  congr 1
  ring

theorem canonical_child_domains
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hpr:∀i,lambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)
    (hf:∀x∈S,x.frequency≠0)(Z θ v H η:ℝ)(hZ:0<Z)
    (hd:∀x∈coprimeSource p S,((sourceIdeal p x.divisor).absNorm:ℝ)≤Z^(θ+η))
    (hv:∀x∈coprimeSource p S,((sourceIdeal p x.overlap).absNorm:ℝ)≤Z^(v+η))
    (hh:∀x∈coprimeSource p S,‖ringComplex x.frequency‖^2≤Z^(H+η)) :
    ∀x∈coprimeSource p S,∀u:Eisˣ,
      (initialChild (toTuple p (sectorSource u x))).2.1∈idealRange (Z^(θ+v+2*η)) ∧
      (initialChild (toTuple p (sectorSource u x))).2.2∈
        nonzeroChildFrequencyBall 1 (Z^(θ+H+2*η)) := by
  intro x hx u
  refine ⟨childLabels_subset_range p hp hcop hg hc hpr S hdiv Z θ v η hZ hd hv
    (child_label_mem p S hx u),?_⟩
  rw [initial_child_row_ball p hp hpr]
  refine ⟨mul_pos ?_ (sq_pos_of_pos (norm_pos_iff.mpr
    (ringComplex_ne_zero (hf x (Finset.mem_filter.mp hx).1)))),?_⟩
  · exact_mod_cast Nat.pos_of_ne_zero (fun h=>sourceIdeal_ne_zero p hp x.divisor
      (Ideal.absNorm_eq_zero_iff.mp h))
  · have he := (initial_child_enclosures p hp hpr x u Z θ v H η hZ
      (hd x hx) (hv x hx) (hh x hx)).2
    rwa [initial_child_row_norm p hp hpr] at he

end InverseInitialEnergyCallerRanges

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialEnergyCallerWindows
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerGeometry InverseInitialEnergyCallerSourceMask
open InverseInitialProfile InverseInitialClippedColumns InverseInitialKernelBridge
local notation "Eis"=>Eisenstein.O
variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

def sourceRelative (x:Source (ι:=ι) 0)(Z D B v θ H:ℝ) : Fin 6→ℝ :=
  relativeNorm (coordinates p (sourcePoint x ∅ ∅)) Z D B v θ H

def windowSource (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)
    (Z D B v θ H:ℝ) : Finset (Source (ι:=ι) 0) :=
  S.filter (fun x=>outerCutoff ψ (sourceRelative p x Z D B v θ H)≠0)

omit [DecidableEq ι] in
theorem sourceRelative_four (x:Source (ι:=ι) 0)(N M:Finset ι)
    (Z D B v θ H:ℝ)(i:Fin 4) :
    relativeNorm (coordinates p (sourcePoint x N M)) Z D B v θ H (InverseSecondChildWindows.outerIndex i)=
      sourceRelative p x Z D B v θ H (InverseSecondChildWindows.outerIndex i) := by
  fin_cases i <;> simp only [InverseSecondChildWindows.outerIndex,sourceRelative,relativeNorm,
    coordinates,sourcePoint,physicalCoordinates,secondRelativeNorm,Fin.castLE,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
    Matrix.cons_val_zero',Matrix.cons_val_succ']

theorem windowSource_four_nonzero
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(Z D B v θ H:ℝ)
    {x:Point ι}(hx:x∈pointSource pool (windowSource p S ψ Z D B v θ H))(i:Fin 4) :
    ψ i (relativeNorm (coordinates p x) Z D B v θ H (InverseSecondChildWindows.outerIndex i))≠0 := by
  obtain ⟨s,hs,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨⟨N,M⟩,hNM,rfl⟩ := Finset.mem_image.mp hx
  have ho := (Finset.mem_filter.mp hs).2
  change outerCutoff ψ (sourceRelative p s Z D B v θ H)≠0 at ho
  rw [sourceRelative_four]
  have h := mul_ne_zero_iff.mp ho
  have h' := mul_ne_zero_iff.mp h.1
  have h'' := mul_ne_zero_iff.mp h'.1
  fin_cases i
  · exact h''.1
  · exact h''.2
  · exact h'.2
  · exact h.2

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

include hp hcop in
theorem physicalBlock_windowSource
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)
    (Z D B v θ H m:ℝ)(w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ)) :
    physicalBlock p hg (pointSource pool S)
      ((fun x=>w x*outerCutoff ψ (sourceRelative p x Z D B v θ H))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m =
    physicalBlock p hg (pointSource pool (windowSource p S ψ Z D B v θ H))
      ((fun x=>w x*outerCutoff ψ (sourceRelative p x Z D B v θ H))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [pointSource_sum,pointSource_sum,windowSource,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases ho:outerCutoff ψ (sourceRelative p x Z D B v θ H)=0
  · simp only [ho,ne_eq,not_true_eq_false,ite_false,Function.comp_apply,erase_sourcePoint,
      mul_zero,zero_mul,Finset.sum_const_zero]
  · rw [if_pos ho]

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem actual_window_block_support
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (ψ:Fin 4→ℝ→ℂ)(W₁ W₂ ω₁ ω₂:ℝ→ℂ)(V:Fin 6→ℝ→ℂ)
    (a b A₀ B₀ A₂ B₂:ℝ)(hA₀:0<A₀)(hA₂:0<A₂)
    (hψ₀:∀y,ψ 0 y≠0→y∈Set.Icc A₀ B₀)
    (hψ₂:∀y,ψ 2 y≠0→y∈Set.Icc A₂ B₂)
    (hω₁:∀y∈Set.Icc (a/(B₀*B₂)) (b/(A₀*A₂)),ω₁ y=1)
    (hω₂:∀y∈Set.Icc (a/(B₀*B₂)) (b/(A₀*A₂)),ω₂ y=1)
    (hV:∀i y,0<y→ retainedCutoffs ψ ω₁ ω₂ i y≠0→V i (Real.log y)=1)
    (Z D B v θ H c₁ c₂ θ₁ θ₂:ℝ)(hZ:0<Z)
    (hW₁:Function.support (clippedSource W₁ c₁ θ₁)⊆Set.Icc a b)
    (hW₂:Function.support (clippedSource W₂ c₂ θ₂)⊆Set.Icc a b) :
    BlockSupport p (pointSource pool (windowSource p S ψ Z D B v θ H))
      W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂ := by
  have hvalid : ∀x∈pointSource pool (windowSource p S ψ Z D B v θ H),Valid x :=
    pointSource_valid pool _ (fun x hx=>hdiv x (Finset.mem_filter.mp hx).1)
      (fun x hx=>hf x (Finset.mem_filter.mp hx).1)
  have hpos (x:Point ι)(hx:x∈pointSource pool (windowSource p S ψ Z D B v θ H)) :
      ∀i,0<relativeNorm (coordinates p x) Z D B v θ H i :=
    relativeNorm_pos _ (coordinates_pos p hp x (hvalid x hx)) hZ D B v θ H
  refine ⟨?_,?_,?_⟩
  · intro x hx hlive
    have he := fresh_window_eq_one (clippedSource W₁ c₁ θ₁) ω₁ a b A₀ B₀ A₂ B₂
      _ _ _ hW₁ hA₀ hA₂
      (hψ₀ _ (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 0))
      (hψ₂ _ (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 2))
      (hpos x hx 4).le hω₁ hlive
    rw [relative_column_left] at he
    rw [he,star_one]
  · intro x hx hlive
    have he := fresh_window_eq_one (clippedSource W₂ c₂ θ₂) ω₂ a b A₀ B₀ A₂ B₂
      _ _ _ hW₂ hA₀ hA₂
      (hψ₀ _ (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 0))
      (hψ₂ _ (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 2))
      (hpos x hx 5).le hω₂ hlive
    rwa [relative_column_right] at he
  · intro x hx h₁ h₂ i
    apply hV i _ (hpos x hx i)
    apply retainedCutoffs_nonzero ψ ω₁ ω₂ _ ?_ ?_ ?_ i
    · unfold outerCutoff
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero
        (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 0)
        (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 1))
        (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 2))
        (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 3)
    · rw [relative_column_left]
      exact star_ne_zero.mp h₁
    · rwa [relative_column_right]

end InverseInitialEnergyCallerWindows

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialEnergyCallerWindowGeometry
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialEnergyCallerGeometry
open InverseInitialProfile InverseInitialKernelBridge 
local notation "Eis"=>Eisenstein.O
variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

theorem retained_source_windows
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H:ℝ)(hZ:0<Z){x:Source (ι:=ι) 0}
    (hx:x∈windowSource p S ψ Z D B v θ H) :
    ((sourceIdeal p x.common).absNorm:ℝ)≤hi 0*Z^B ∧
    lo 1*Z^θ≤((sourceIdeal p x.divisor).absNorm:ℝ) ∧
    ((sourceIdeal p x.divisor).absNorm:ℝ)≤hi 1*Z^θ ∧
    ((sourceIdeal p x.overlap).absNorm:ℝ)≤hi 2*Z^v ∧
    ‖ringComplex x.frequency‖^2≤hi 3*Z^H := by
  have hm : sourcePoint x ∅ ∅∈pointSource ∅ (windowSource p S ψ Z D B v θ H) := by
    apply Finset.mem_biUnion.mpr
    refine ⟨x,hx,?_⟩
    apply Finset.mem_image.mpr
    exact ⟨(∅,∅),by simp,rfl⟩
  have hh (i:Fin 4) := hψ i (windowSource_four_nonzero p ∅ S ψ Z D B v θ H hm i)
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  have h3 := hh 3
  change ((sourceIdeal p x.common).absNorm:ℝ)/Z^B∈Set.Icc (lo 0) (hi 0) at h0
  change ((sourceIdeal p x.divisor).absNorm:ℝ)/Z^θ∈Set.Icc (lo 1) (hi 1) at h1
  change ((sourceIdeal p x.overlap).absNorm:ℝ)/Z^v∈Set.Icc (lo 2) (hi 2) at h2
  change ‖ringComplex x.frequency‖^2/Z^H∈Set.Icc (lo 3) (hi 3) at h3
  exact ⟨(div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp h0.2,
    (le_div_iff₀ (Real.rpow_pos_of_pos hZ _)).mp h1.1,
    (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp h1.2,
    (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp h2.2,
    (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp h3.2⟩

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
include hp

theorem retained_child_boxes
    (hpr:∀i,lambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))(hhi:∀i,0≤hi i)
    (Z D B v θ H:ℝ)(hZ:0<Z){x:Source (ι:=ι) 0}
    (hx:x∈windowSource p S ψ Z D B v θ H)(u:Eisˣ) :
    ((initialChild (toTuple p (sectorSource u x))).2.1.absNorm:ℝ)≤
      (hi 1*hi 2)*Z^(θ+v) ∧
    ‖ringComplex (initialChild (toTuple p (sectorSource u x))).2.2‖^2≤
      (hi 1*hi 3)*Z^(θ+H) := by
  obtain ⟨h0,h1lo,h1,h2,h3⟩ := retained_source_windows p S ψ lo hi hψ Z D B v θ H hZ hx
  rw [initial_child_label_norm p,initial_child_row_norm p hp hpr]
  constructor
  · apply (mul_le_mul h1 h2 (by positivity) (mul_nonneg (hhi 1) (Real.rpow_nonneg hZ.le _))).trans_eq
    rw [Real.rpow_add hZ]
    ring
  · apply (mul_le_mul h1 h3 (by positivity) (mul_nonneg (hhi 1) (Real.rpow_nonneg hZ.le _))).trans_eq
    rw [Real.rpow_add hZ]
    ring

omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem retained_source_quotients
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)
    (ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))(hlo:0<lo 1)(hhi:0≤hi 0)
    (Z D B v θ H:ℝ)(hZ:0<Z) :
    ∀t∈InverseInitialQuotientGeometry.quotientSet p (windowSource p S ψ Z D B v θ H),
      (t.absNorm:ℝ)≤(hi 0/lo 1)*Z^(B-θ) := by
  intro t ht
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨h0,h1lo,h1,h2,h3⟩ := retained_source_windows p S ψ lo hi hψ Z D B v θ H hZ hx
  rw [InverseInitialQuotientGeometry.quotient_norm_eq p hp x (hdiv x (Finset.mem_filter.mp hx).1)]
  apply (div_le_div₀ (by positivity) h0 (mul_pos hlo (Real.rpow_pos_of_pos hZ _)) h1lo).trans_eq
  rw [Real.rpow_sub hZ]
  ring

end InverseInitialEnergyCallerWindowGeometry

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialEnergyCallerState
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialQuotientGeometry
local notation "Eis"=>Eisenstein.O
variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

omit [DecidableEq ι] in
theorem windowSource_subset_retained
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(Z D B v θ H:ℝ) :
    windowSource p S ψ Z D B v θ H ⊆ retained p S (fun _=>1) (ψ 0) (ψ 1) Z B θ := by
  intro x hx
  refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,?_⟩
  have hn := (Finset.mem_filter.mp hx).2
  have hh := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1
  change ψ 0 (((sourceIdeal p x.common).absNorm:ℝ)/Z^B)*
    ψ 1 (((sourceIdeal p x.divisor).absNorm:ℝ)/Z^θ)≠0 at hh
  simpa only [sourceWeight,one_mul] using hh

theorem window_quotient_subset_retained
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(Z D B v θ H:ℝ) :
    quotientSet p (windowSource p S ψ Z D B v θ H) ⊆
      quotientSet p (retained p S (fun _=>1) (ψ 0) (ψ 1) Z B θ) :=
  Finset.image_subset_image (windowSource_subset_retained p S ψ Z D B v θ H)

theorem initial_F_exact (r z G B θ v:ℝ) :
    max 0 (r+z-2*G-B-v)+(θ+v)=
      initialF r z G (B-θ) (max 0 (r+z-2*G-B-v)-(r+z-2*G-B-v)) := by
  unfold initialF
  ring

variable (hp:∀i,p i≠0)
include hp

theorem actual_window_initial_margins (S : Finset (Source (ι:=ι) 0))
    (ψ : Fin 4 → ℝ → ℂ) (D v H : ℝ)
    (aC bC ad bd Z B θ η : ℝ) (hZ : 1 < Z)
    (hC : Function.support (ψ 0) ⊆ Set.Icc aC bC)
    (hd : Function.support (ψ 1) ⊆ Set.Icc ad bd)
    (hCup : bC ≤ Z^η) (hdlo : Z^(-η) ≤ ad)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common) (hpr : ∀ i, lambda^2 ∣ p i-1)
    {σ : Type*} [DecidableEq σ] (all assigned : Finset σ) (ha : assigned ⊆ all)
    (q : σ → Eis) (z a b : σ → ℝ) (W : σ → ℝ → ℂ)
    (hz : ∀ i ∈ all, 0 ≤ z i) (hq : ∀ i ∈ assigned, q i ≠ 0)
    (hW : ∀ i ∈ assigned, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ assigned, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0)
    (hthreshold : (∏ i ∈ assigned, b i) ≤ Z^η)
    {t : Ideal Eis} (ht : t ∈ quotientSet p (windowSource p S ψ Z D B v θ H))
    (m r δ τ c₁ c₂ : ℝ)
    (h₁ : r+2*assignedCenter all z ≤ m-c₁)
    (h₂ : 2*r+8*assignedCenter all z ≤ 3*m-c₂) :
    c₁+δ-9*η-τ ≤
      initialF r (assignedCenter all z) (assignedCenter assigned z) (B-θ) δ -
      initialM m r (assignedCenter all z) (assignedCenter assigned z) (B-θ) η τ -
      punctureLength Z t (assignedElement assigned q) - assignedCenter (all\assigned) z ∧
    c₂+4*δ-22*η-3*τ ≤
      4*initialF r (assignedCenter all z) (assignedCenter assigned z) (B-θ) δ -
      3*initialM m r (assignedCenter all z) (assignedCenter assigned z) (B-θ) η τ -
      6*assignedCenter (all\assigned) z := by
  exact retained_initial_margins p hp S (fun _=>1) (ψ 0) (ψ 1)
    aC bC ad bd Z B θ η hZ hC hd hCup hdlo hdiv hpr all assigned ha q z a b W
    hz hq hW hret hthreshold (window_quotient_subset_retained p S ψ Z D B v θ H ht)
    m r δ τ c₁ c₂ h₁ h₂

theorem actual_window_canonical_margins (S : Finset (Source (ι:=ι) 0))
    (ψ : Fin 4 → ℝ → ℂ) (D v H : ℝ)
    (aC bC ad bd Z B θ η : ℝ) (hZ : 1 < Z)
    (hC : Function.support (ψ 0) ⊆ Set.Icc aC bC)
    (hd : Function.support (ψ 1) ⊆ Set.Icc ad bd)
    (hCup : bC ≤ Z^η) (hdlo : Z^(-η) ≤ ad)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common) (hpr : ∀ i, lambda^2 ∣ p i-1)
    {σ : Type*} [DecidableEq σ] (all assigned : Finset σ) (ha : assigned ⊆ all)
    (q : σ → Eis) (z a b : σ → ℝ) (W : σ → ℝ → ℂ)
    (hz : ∀ i ∈ all, 0 ≤ z i) (hq : ∀ i ∈ assigned, q i ≠ 0)
    (hW : ∀ i ∈ assigned, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ assigned, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0)
    (hthreshold : (∏ i ∈ assigned, b i) ≤ Z^η)
    {t : Ideal Eis} (ht : t ∈ quotientSet p (windowSource p S ψ Z D B v θ H))
    (m r τ c₁ c₂ : ℝ)
    (h₁ : r+2*assignedCenter all z ≤ m-c₁)
    (h₂ : 2*r+8*assignedCenter all z ≤ 3*m-c₂)
    (hc : 0 ≤ min c₁ c₂) (hη : η ≤ min c₁ c₂ / 100) (hτ : τ ≤ min c₁ c₂ / 100) :
    CanonicalMargins
      (max 0 (r+assignedCenter all z-2*assignedCenter assigned z-B-v)+(θ+v))
      (initialM m r (assignedCenter all z) (assignedCenter assigned z) (B-θ) η τ)
      (punctureLength Z t (assignedElement assigned q))
      (assignedCenter (all\assigned) z) (3*min c₁ c₂/4) := by
  let δ:=max 0 (r+assignedCenter all z-2*assignedCenter assigned z-B-v)-
    (r+assignedCenter all z-2*assignedCenter assigned z-B-v)
  have hδ:0≤δ:=sub_nonneg.mpr (le_max_right _ _)
  obtain ⟨h1,h2⟩ := actual_window_initial_margins p hp S ψ D v H
    aC bC ad bd Z B θ η hZ hC hd hCup hdlo hdiv hpr all assigned ha q z a b W
    hz hq hW hret hthreshold ht m r δ τ c₁ c₂ h₁ h₂
  rw [initial_F_exact]
  change CanonicalMargins (initialF r (assignedCenter all z) (assignedCenter assigned z) (B-θ) δ)
    _ _ _ _
  have hc1:=min_le_left c₁ c₂
  have hc2:=min_le_right c₁ c₂
  constructor <;> linarith

end InverseInitialEnergyCallerState

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialCanonicalState
open Eisenstein CompletedGauss  InverseMoment
open InverseInitialArithmetic InverseInitialQuotientGeometry InverseInitialProfile
open InverseInitialEnergyCallerState InverseInitialEnergyCallerWindows
open InverseInitialEnergyCallerWindowGeometry InverseInitialEnergyCallerGeometry
open InverseInitialEnergyCallerRanges CanonicalQuadraticSieve
local notation "O"=> Eisenstein.O

def fullPunctureWidth (Z:ℝ)(t:Ideal O)(j:O):ℝ :=
  Real.logb Z (Ideal.absNorm (Ideal.span {j*primaryIdealGenerator t}):ℝ)

theorem full_puncture_width_exact (Z:ℝ)(hZ:1< Z)(t:Ideal O)(j:O)
    (hm:j*primaryIdealGenerator t≠0):
    0≤ fullPunctureWidth Z t j ∧
      ‖ringComplex (j*primaryIdealGenerator t)‖^2=Z^(fullPunctureWidth Z t j) := by
  have hn:(1:ℝ)≤ Ideal.absNorm (Ideal.span {j*primaryIdealGenerator t}) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hm))
  constructor
  · unfold fullPunctureWidth Real.logb
    exact div_nonneg (Real.log_nonneg hn) (Real.log_pos hZ).le
  · rw [ringComplex_norm_sq_eq_absNorm_span]
    exact (Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
      (zero_lt_one.trans_le hn)).symm

theorem full_product_width_bound (Z P G η:ℝ)(hZ:1< Z)(t:Ideal O)(j:O)
    (hm:j*primaryIdealGenerator t≠0)
    (hspan:Ideal.span {j*primaryIdealGenerator t}=t*Ideal.span {j})
    (ht:(t.absNorm:ℝ)≤ Z^(P+2*η))
    (hj:(Ideal.absNorm (Ideal.span {j}):ℝ)≤ Z^(G+η)):
    fullPunctureWidth Z t j≤ P+G+3*η := by
  have hz:=zero_lt_one.trans hZ
  have hpos:0<(Ideal.absNorm (Ideal.span {j*primaryIdealGenerator t}):ℝ):=by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hm))
  have hb:(Ideal.absNorm (Ideal.span {j*primaryIdealGenerator t}):ℝ)≤ Z^(P+G+3*η):=by
    rw [hspan,map_mul,Nat.cast_mul]
    apply (mul_le_mul ht hj (by positivity) (Real.rpow_nonneg hz.le _)).trans_eq
    rw [←Real.rpow_add hz]
    congr 1
    ring
  unfold fullPunctureWidth Real.logb
  apply (div_le_iff₀ (Real.log_pos hZ)).mpr
  simpa only [Real.log_rpow hz] using Real.log_le_log hpos hb

theorem physical_row_width_le (m r z G B θ H η τ:ℝ)
    (hcut:radialCenter m H θ (r+z-2*G) B≤4*η+τ):
    θ+H+2*η≤ initialM m r z G (B-θ) η τ := by
  unfold radialCenter at hcut
  unfold initialM
  linarith

theorem enlarged_initial_margins (m r z G B θ v H η τ Q c₁ c₂:ℝ)
    (h₁:r+2*z≤ m-c₁)(h₂:2*r+8*z≤3*m-c₂)
    (hG:0≤ G)(hP:-2*η≤ B-θ)(hQ:Q≤ B-θ+G+3*η)
    (hc:0≤ min c₁ c₂)(hη:0≤η)(hηsmall:η≤ min c₁ c₂/100)
    (hτ:τ≤ min c₁ c₂/100)
    (hcut:radialCenter m H θ (r+z-2*G) B≤4*η+τ):
    CanonicalMargins
      (max 0 (r+z-2*G-B-v)+(θ+v+2*η)) (θ+H+2*η) Q (z-G)
      (3*min c₁ c₂/4) := by
  have hd:0≤ max 0 (r+z-2*G-B-v)-(r+z-2*G-B-v):=
    sub_nonneg.mpr (le_max_right _ _)
  have hh:=initial_margins (delta:=max 0 (r+z-2*G-B-v)-(r+z-2*G-B-v))
    h₁ h₂ hG hP hQ hc hd hηsmall hτ
  have hr:=physical_row_width_le m r z G B θ H η τ hcut
  unfold CanonicalMargins at hh ⊢
  unfold initialF at hh
  constructor <;> linarith [hh.1,hh.2]

theorem enlarged_label_exact (N V η:ℝ)(hV:0≤ V+2*η):
    max 0 (V+2*η)=V+2*η ∧
      N+max 0 (V+2*η)-(N+V)=2*η := by
  rw [max_eq_right hV]
  exact ⟨rfl,by ring⟩

theorem assigned_label_weight_le {σ:Type*}[DecidableEq σ]
    (slots J₁ J₂:Finset σ)(K:ℕ)(hK:slots.card≤ K)
    (h₁:J₁⊆slots)(h₂:J₂⊆slots)(f:Ideal O)(hf:f≠0):
    ((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1)≤ secondLabelWeight K f := by
  have hmem:(1:Ideal O)∈idealDivisors f:=
    (mem_idealDivisors hf).mpr (one_dvd _)
  have hn:(1:ℝ)≤(idealDivisors f).card:=by
    exact_mod_cast Finset.one_le_card.mpr ⟨1,hmem⟩
  have hcard1:=Finset.card_le_card h₁
  have hcard2:=Finset.card_le_card h₂
  exact pow_le_pow_right₀ hn (by omega)

end InverseInitialCanonicalState

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialCanonicalState
open Eisenstein CompletedGauss  InverseMoment
open InverseInitialArithmetic InverseInitialQuotientGeometry InverseInitialProfile
open InverseInitialEnergyCallerState InverseInitialEnergyCallerWindows
open InverseInitialEnergyCallerWindowGeometry InverseInitialEnergyCallerGeometry
open InverseInitialEnergyCallerRanges CanonicalQuadraticSieve
local notation "O"=> Eisenstein.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]

include hp in

theorem live_widths_nonnegative
    (hpr:∀i,lambda^2∣p i-1)(S:Finset (Source (ι:=ι) 0))
    (ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H η:ℝ)(hZ:1< Z)(hhi:∀i,hi i≤ Z^η)
    {x:Source (ι:=ι) 0}(hx:x∈windowSource p S ψ Z D B v θ H)
    (hf:x.frequency≠0):
    0≤θ+v+2*η ∧ 0≤θ+H+2*η := by
  have hz:=zero_lt_one.trans hZ
  obtain ⟨_,_,hd,hv,hh⟩:=retained_source_windows p S ψ lo hi hψ Z D B v θ H hz hx
  have bound (a c:ℝ)(i:Fin 4)(ha:a≤ hi i*Z^c):a≤ Z^(c+η):=by
    apply (ha.trans (mul_le_mul_of_nonneg_right (hhi i) (Real.rpow_nonneg hz.le c))).trans_eq
    rw [←Real.rpow_add hz]
    congr 1
    ring
  obtain ⟨hlabel,hrow⟩:=initial_child_enclosures p hp hpr x 1 Z θ v H η hz
    (bound _ _ 1 hd) (bound _ _ 2 hv) (bound _ _ 3 hh)
  have hI:(1:ℝ)≤ Ideal.absNorm (initialChild (toTuple p (sectorSource 1 x))).2.1:=by
    have hne:(initialChild (toTuple p (sectorSource 1 x))).2.1≠0:=
      mul_ne_zero (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hne)
  have hdiv:(1:ℝ)≤(sourceIdeal p x.divisor).absNorm:=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (sourceIdeal_ne_zero p hp _))
  have hfreq:(1:ℝ)≤‖ringComplex x.frequency‖^2:=by
    rw [ringComplex_norm_sq_eq_absNorm_span]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hf))
  have hr:(1:ℝ)≤‖ringComplex (initialChild (toTuple p (sectorSource 1 x))).2.2‖^2:=by
    rw [initial_child_row_norm p hp hpr]
    exact one_le_mul_of_one_le_of_one_le hdiv hfreq
  constructor
  · exact (Real.rpow_le_rpow_left_iff hZ).mp
      (by simpa only [Real.rpow_zero] using hI.trans hlabel)
  · exact (Real.rpow_le_rpow_left_iff hZ).mp
      (by simpa only [Real.rpow_zero] using hr.trans hrow)

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem retained_full_puncture
    (hpr:∀i,lambda^2∣p i-1)(S:Finset (Source (ι:=ι) 0))
    (ψ:Fin 4→ℝ→ℂ)(D v H aC bC ad bd Z B θ η G:ℝ)(hZ:1< Z)
    (hC:Function.support (ψ 0)⊆Set.Icc aC bC)
    (hd:Function.support (ψ 1)⊆Set.Icc ad bd)
    (hCup:bC≤ Z^η)(hdlo:Z^(-η)≤ ad)
    (hdiv:∀x∈S,x.divisor⊆x.common)
    (j:O)(hj:j≠0)(hnj:(Ideal.absNorm (Ideal.span {j}):ℝ)≤ Z^(G+η))
    {t:Ideal O}(ht:t∈quotientSet p (windowSource p S ψ Z D B v θ H)):
    j*primaryIdealGenerator t≠0 ∧ 0≤ fullPunctureWidth Z t j ∧
    ‖ringComplex (j*primaryIdealGenerator t)‖^2=Z^(fullPunctureWidth Z t j) ∧
    fullPunctureWidth Z t j≤ B-θ+G+3*η := by
  have hspan:=span_source_puncture p hp (windowSource p S ψ Z D B v θ H) hpr j ht
  have ht0:=quotientSet_nonzero p hp (windowSource p S ψ Z D B v θ H) t ht
  have hm:j*primaryIdealGenerator t≠0:=by
    apply Ideal.span_singleton_eq_bot.not.mp
    rw [hspan]
    exact mul_ne_zero ht0 (Ideal.span_singleton_eq_bot.not.mpr hj)
  have hret:=window_quotient_subset_retained p S ψ Z D B v θ H ht
  have hnt:=retained_quotient_bound p hp S (fun _=>1) (ψ 0) (ψ 1)
    aC bC ad bd Z B θ η (zero_lt_one.trans hZ) hC hd hCup hdlo hdiv t hret
  obtain ⟨hn,he⟩:=full_puncture_width_exact Z hZ t j hm
  exact ⟨hm,hn,he,full_product_width_bound Z (B-θ) G η hZ t j hm hspan hnt hnj⟩

end InverseInitialCanonicalState

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialCanonicalState
open Eisenstein CompletedGauss  InverseMoment
open InverseInitialArithmetic InverseInitialQuotientGeometry InverseInitialProfile
open InverseInitialEnergyCallerState InverseInitialEnergyCallerWindows
local notation "O"=> Eisenstein.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]

include hp in

theorem actual_window_state
    (hpr:∀i,lambda^2∣p i-1)(S:Finset (Source (ι:=ι) 0))
    (ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H η:ℝ)(hZ:1< Z)(hη:0≤η)
    (hhi:∀i,hi i≤ Z^η)(hdlo:Z^(-η)≤ lo 1)
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    {σ:Type*}[DecidableEq σ](all assigned:Finset σ)(hassigned:assigned⊆all)
    (q:σ→O)(z a b:σ→ℝ)(W:σ→ℝ→ℂ)
    (hz:∀i∈all,0≤ z i)(hq:∀i∈assigned,q i≠0)
    (hW:∀i∈assigned,Function.support (W i)⊆Set.Icc (a i) (b i))
    (hret:∀i∈assigned,W i ((Ideal.absNorm (Ideal.span {q i}):ℝ)/Z^(z i))≠0)
    (hthreshold:(∏i∈assigned,b i)≤ Z^η)
    {t:Ideal O}(ht:t∈quotientSet p (windowSource p S ψ Z D B v θ H))
    (m r τ c₁ c₂:ℝ)(hD:D=r+assignedCenter all z-2*assignedCenter assigned z)
    (h₁:r+2*assignedCenter all z≤ m-c₁)
    (h₂:2*r+8*assignedCenter all z≤3*m-c₂)
    (hc:0≤ min c₁ c₂)(hηsmall:η≤ min c₁ c₂/100)(hτ:τ≤ min c₁ c₂/100)
    (hcut:radialCenter m H θ D B≤4*η+τ)
    (hclip:max 0 (D-B-v)-(D-B-v)≤3*η):
    let N:=max 0 (D-B-v)
    let V:=θ+v+2*η
    let M:=θ+H+2*η
    let j:=assignedElement assigned q
    j*primaryIdealGenerator t≠0 ∧ 0≤ N ∧ 0≤ V ∧ 0≤ M ∧
    0≤ fullPunctureWidth Z t j ∧
    ‖ringComplex (j*primaryIdealGenerator t)‖^2=Z^(fullPunctureWidth Z t j) ∧
    CanonicalMargins (N+V) M (fullPunctureWidth Z t j)
      (assignedCenter (all\assigned) z+η) (min c₁ c₂/2) ∧
    N+V≤ r+assignedCenter all z+7*η ∧
    M≤ r+assignedCenter all z+7*η ∧
    N+V-(N+(θ+v))=2*η := by
  dsimp only
  have hretained:=window_quotient_subset_retained p S ψ Z D B v θ H ht
  have hP: -2*η≤ B-θ:=by
    have hn:=(nonempty_radius p hp (retained p S (fun _=>1) (ψ 0) (ψ 1) Z B θ)
      Z (B-θ) η hZ ⟨t,hretained⟩
      (retained_quotient_bound p hp S (fun _=>1) (ψ 0) (ψ 1)
        (lo 0) (hi 0) (lo 1) (hi 1) Z B θ η (zero_lt_one.trans hZ)
        (hψ 0) (hψ 1) (hhi 0) hdlo hdiv)).2
    linarith
  have hreg:=assigned_register all assigned hassigned z hz
  have hj:assignedElement assigned q≠0:=Finset.prod_ne_zero_iff.mpr hq
  have hnj:=assigned_norm_power assigned q z a b W Z η (zero_lt_one.trans hZ) hW hret hthreshold
  obtain ⟨hm,hQ0,hnorm,hQ⟩:=retained_full_puncture p hp hpr S ψ D v H
    (lo 0) (hi 0) (lo 1) (hi 1) Z B θ η (assignedCenter assigned z) hZ
    (hψ 0) (hψ 1) (hhi 0) hdlo hdiv (assignedElement assigned q) hj hnj ht
  obtain ⟨x,hx,hxt⟩:=Finset.mem_image.mp ht
  obtain ⟨hV,hM⟩:=live_widths_nonnegative p hp hpr S ψ lo hi hψ Z D B v θ H η hZ hhi
    hx (hf x (Finset.mem_filter.mp hx).1)
  have hmg:=enlarged_initial_margins m r (assignedCenter all z) (assignedCenter assigned z)
    B θ v H η τ (fullPunctureWidth Z t (assignedElement assigned q)) c₁ c₂
    h₁ h₂ hreg.1 hP hQ hc hη hηsmall hτ (by simpa only [hD] using hcut)
  rw [←hD,hreg.2.2] at hmg
  have hactual:CanonicalMargins (max 0 (D-B-v)+(θ+v+2*η)) (θ+H+2*η)
      (fullPunctureWidth Z t (assignedElement assigned q))
      (assignedCenter (all\assigned) z+η) (min c₁ c₂/2):=by
    unfold CanonicalMargins at hmg ⊢
    constructor <;> linarith [hmg.1,hmg.2]
  have hF:max 0 (D-B-v)+(θ+v+2*η)≤ r+assignedCenter all z+7*η:=by
    rw [hD] at hclip ⊢
    linarith [hreg.1]
  have hMF:θ+H+2*η≤ max 0 (D-B-v)+(θ+v+2*η):=by
    have hh:=hactual.1
    linarith [hreg.2.1]
  exact ⟨hm,le_max_left _ _,hV,hM,hQ0,hnorm,hactual,hF,hMF.trans hF,by ring⟩

end InverseInitialCanonicalState

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialCanonicalDomains
open Eisenstein CompletedGauss  InverseMoment
open InverseInitialArithmetic InverseInitialQuotientGeometry InverseInitialProfile
open InverseInitialEnergyCallerWindows InverseInitialEnergyCallerWindowGeometry
open InverseInitialEnergyCallerSourceMask InverseInitialEnergyCallerRanges
open InverseInitialEnergyCallerSource CanonicalQuadraticSieve
local notation "O"=> Eisenstein.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem window_power_bounds
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H η:ℝ)(hZ:0< Z)(hhi:∀i,hi i≤ Z^η)
    {x:Source (ι:=ι) 0}(hx:x∈windowSource p S ψ Z D B v θ H):
    ((sourceIdeal p x.divisor).absNorm:ℝ)≤ Z^(θ+η) ∧
    ((sourceIdeal p x.overlap).absNorm:ℝ)≤ Z^(v+η) ∧
    ‖ringComplex x.frequency‖^2≤ Z^(H+η) := by
  obtain ⟨_,_,hd,hv,hh⟩:=retained_source_windows p S ψ lo hi hψ Z D B v θ H hZ hx
  have hpow (i:Fin 4)(r:ℝ):hi i*Z^r≤ Z^(r+η):=by
    rw [Real.rpow_add hZ]
    exact (mul_le_mul_of_nonneg_right (hhi i) (Real.rpow_nonneg hZ.le _)).trans_eq (mul_comm _ _)
  exact ⟨hd.trans (hpow 1 θ),hv.trans (hpow 2 v),hh.trans (hpow 3 H)⟩

include hp hcop hg in
theorem actual_window_domains
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,lambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H η:ℝ)(hZ:0< Z)(hhi:∀i,hi i≤ Z^η):
    ∀x∈coprimeSource p (windowSource p S ψ Z D B v θ H),∀u:Oˣ,
      (initialChild (toTuple p (sectorSource u x))).2.1∈idealRange (Z^(θ+v+2*η)) ∧
      (initialChild (toTuple p (sectorSource u x))).2.2∈
        nonzeroChildFrequencyBall 1 (Z^(θ+H+2*η)) := by
  apply canonical_child_domains p hp hcop hg hc hpr (windowSource p S ψ Z D B v θ H)
    (fun x hx=> hdiv x (Finset.mem_filter.mp hx).1)
    (fun x hx=> hf x (Finset.mem_filter.mp hx).1) Z θ v H η hZ
  · intro x hx
    exact (window_power_bounds p S ψ lo hi hψ Z D B v θ H η hZ hhi (Finset.mem_filter.mp hx).1).1
  · intro x hx
    exact (window_power_bounds p S ψ lo hi hψ Z D B v θ H η hZ hhi (Finset.mem_filter.mp hx).1).2.1
  · intro x hx
    exact (window_power_bounds p S ψ lo hi hψ Z D B v θ H η hZ hhi (Finset.mem_filter.mp hx).1).2.2

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem retained_quotient_subset
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(Z D B v θ H:ℝ):
    quotientSet p (coprimeSource p (windowSource p S ψ Z D B v θ H))⊆
      quotientSet p (windowSource p S ψ Z D B v θ H) :=
  Finset.image_subset_image (Finset.filter_subset _ _)

end InverseInitialCanonicalDomains

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialEnergyCallerFixedWindows
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open InverseSecondChildWindows InverseSecondProfileUniform
local notation "Eis"=> Eisenstein.O

theorem positiveSource_kernelLogSource (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (θ : ℝ) :
    positiveSource (kernelLogSource W a b ha hs hW) c θ x = clippedSource W c θ x := by
  change kernelLogPhase θ (Real.log x) * W (Real.exp (Real.log x + Real.log c)) = _
  rw [Real.exp_add, Real.exp_log hx, Real.exp_log hc, mul_comm x c]
  rfl

theorem log_source_support (W:ℝ→ℂ)(a b:ℝ)(ha:0< a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W) :
    Function.support (kernelLogSource W a b ha hs hW)⊆
      Set.Icc (-(|Real.log a|+|Real.log b|)) (|Real.log a|+|Real.log b|) := by
  intro x hx
  have hh := hs hx
  change a≤ Real.exp x ∧ Real.exp x≤ b at hh
  have hl := Real.log_le_log ha hh.1
  have hu := Real.log_le_log (Real.exp_pos x) hh.2
  rw [Real.log_exp] at hl hu
  constructor
  · linarith [neg_abs_le (Real.log a),abs_nonneg (Real.log b)]
  · linarith [le_abs_self (Real.log b),abs_nonneg (Real.log a)]

theorem exists_actual_initial_windows
    (W₁ W₂:ℝ→ℂ)(a b bcap:ℝ)(ha:0< a)(hcap:1≤ bcap)
    (hs₁:Function.support W₁⊆Set.Icc a b)(hs₂:Function.support W₂⊆Set.Icc a b)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)
    (lo hi:Fin 4→ℝ)(hlo:∀i,0< lo i)(hhi:∀i,lo i≤ hi i) :
    ∃(wFresh:𝓢(ℝ,ℂ))(V:Fin 6→𝓢(ℝ,ℂ))(M:Fin 6→ℝ)(af bf:ℝ),
      0< af ∧ af≤ bf ∧ HasCompactSupport (wFresh:ℝ→ℂ) ∧
      tsupport (wFresh:ℝ→ℂ)⊆Set.Icc af bf ∧
      (∀i,0≤ M i) ∧ (∀i,HasCompactSupport (V i:ℝ→ℂ)) ∧
      (∀i,Function.support (V i)⊆Set.Icc (-M i) (M i)) ∧
      ∀{ι:Type*}[DecidableEq ι](p:ι→Eis)(_hp:∀i,p i≠0)
      [∀i,(Ideal.span {p i}).IsMaximal]
      (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
      (_hdiv:∀x∈S,x.divisor⊆x.common)(_hf:∀x∈S,x.frequency≠0)
      (ψ:Fin 4→ℝ→ℂ)(_hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
      (Z D B v θ H c₁ c₂ θ₁ θ₂:ℝ),0< Z→1≤ c₁→c₁≤ bcap→1≤ c₂→c₂≤ bcap→
      BlockSupport p (pointSource pool (windowSource p S ψ Z D B v θ H))
        W₁ W₂ wFresh wFresh (fun i=> V i) Z D B v θ H c₁ c₂ θ₁ θ₂ := by
  let m:=|Real.log a|+|Real.log b|
  obtain ⟨wFresh,V,M,af,bf,haf,hab,hwc,hws,hM,hVc,hVs,hw,hcut⟩ :=
    fixed_windows m bcap lo hi (fun _=>0) (by dsimp [m];positivity) hcap hlo hhi (by simp)
  refine ⟨wFresh,V,M,af,bf,haf,hab,hwc,hws,hM,hVc,hVs,?_⟩
  intro ι _ p hp _ pool S hdiv hf ψ hψ Z D B v θ H c₁ c₂ θ₁ θ₂ hZ hc₁ hb₁ hc₂ hb₂
  let g₁ := kernelLogSource W₁ a b ha hs₁ hW₁
  let g₂ := kernelLogSource W₂ a b ha hs₂ hW₂
  have hg₁ : Function.support g₁⊆Set.Icc (-m) m := log_source_support W₁ a b ha hs₁ hW₁
  have hg₂ : Function.support g₂⊆Set.Icc (-m) m := log_source_support W₂ a b ha hs₂ hW₂
  have hvalid : ∀x∈pointSource pool (windowSource p S ψ Z D B v θ H),Valid x :=
    pointSource_valid pool _ (fun x hx=> hdiv x (Finset.mem_filter.mp hx).1)
      (fun x hx=> hf x (Finset.mem_filter.mp hx).1)
  have hpos (x:Point ι)(hx:x∈pointSource pool (windowSource p S ψ Z D B v θ H)) :
      ∀i,0< relativeNorm (coordinates p x) Z D B v θ H i :=
    relativeNorm_pos _ (coordinates_pos p hp x (hvalid x hx)) hZ D B v θ H
  have hblock (x:Point ι)(hx:x∈pointSource pool (windowSource p S ψ Z D B v θ H)) :
      ∀i:Fin 4,relativeNorm (coordinates p x) Z D B v θ H (outerIndex i)∈Set.Icc (lo i) (hi i) :=
    fun i=> hψ i (windowSource_four_nonzero p pool S ψ Z D B v θ H hx i)
  refine ⟨?_,?_,?_⟩
  · intro x hx hn
    have he := hw g₁ hg₁ c₁ θ₁ _ _ _ hc₁ hb₁ (hblock x hx 0) (hblock x hx 2) (hpos x hx 4) ?_
    · rw [relative_column_left] at he
      rw [he,star_one]
    · change positiveSource g₁ c₁ θ₁
        (relativeNorm (coordinates p x) Z D B v θ H 0 *
          relativeNorm (coordinates p x) Z D B v θ H 2 *
          relativeNorm (coordinates p x) Z D B v θ H 4)≠0
      dsimp only [g₁]
      rw [positiveSource_kernelLogSource W₁ a b ha hs₁ hW₁ (zero_lt_one.trans_le hc₁)
        (mul_pos (mul_pos (hpos x hx 0) (hpos x hx 2)) (hpos x hx 4))]
      exact hn
  · intro x hx hn
    have he := hw g₂ hg₂ c₂ θ₂ _ _ _ hc₂ hb₂ (hblock x hx 0) (hblock x hx 2) (hpos x hx 5) ?_
    · rwa [relative_column_right] at he
    · change positiveSource g₂ c₂ θ₂
        (relativeNorm (coordinates p x) Z D B v θ H 0 *
          relativeNorm (coordinates p x) Z D B v θ H 2 *
          relativeNorm (coordinates p x) Z D B v θ H 5)≠0
      dsimp only [g₂]
      rw [positiveSource_kernelLogSource W₂ a b ha hs₂ hW₂ (zero_lt_one.trans_le hc₂)
        (mul_pos (mul_pos (hpos x hx 0) (hpos x hx 2)) (hpos x hx 5))]
      exact hn
  · intro x hx hl hr i
    have hl' : wFresh (relativeNorm (coordinates p x) Z D B v θ H 4)≠0 := by
      rw [relative_column_left]
      exact star_ne_zero.mp hl
    have hr' : wFresh (relativeNorm (coordinates p x) Z D B v θ H 5)≠0 := by
      rwa [relative_column_right]
    have he := hcut (relativeNorm (coordinates p x) Z D B v θ H) (fun _=>0)
      (by simp) (hblock x hx) hl' hr' i
    simpa only [add_zero,relativeLog] using he

end InverseInitialEnergyCallerFixedWindows

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialEnergyCallerEmpty
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialProfile InverseInitialClippedColumns InverseInitialKernelBridge
local notation "Eis"=> Eisenstein.O
variable {ι:Type*}[DecidableEq ι](p:ι→Eis)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

include hp hcop in
theorem physicalBlock_zero_of_fresh_empty
    (hpr:∀i,lambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Point ι→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂ ω₁ ω₂:ℝ→ℂ)(V:Fin 6→ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D B v θ H m c₁ c₂ θ₁ θ₂:ℝ)(hZ:0< Z)
    (hs:BlockSupport p (pointSource pool S) W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂)
    (he:freshColumns p pool ω₁ (Z^(columnCenter D B v))=∅) :
    physicalBlock p hg (pointSource pool S) w Ψ j marks
      (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m=0 := by
  unfold physicalBlock
  apply Finset.sum_eq_zero
  intro x hx
  have hv:=pointSource_valid pool S hdiv hf x hx
  have hleft:x.left⊆pool := by
    obtain ⟨s,hs,hx⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨⟨N,M⟩,hNM,rfl⟩:=Finset.mem_image.mp hx
    exact (Finset.mem_powerset.mp (Finset.mem_product.mp hNM).1).trans Finset.sdiff_subset
  have hω:ω₁ (columnRatio p x.left Z D B v)=0 := by
    by_contra hn
    rw [columnRatio_actual] at hn
    have hm:= (mem_freshColumns p pool ω₁ (Z^(columnCenter D B v)) x.left).mpr ⟨hleft,hn⟩
    rw [he] at hm
    exact Finset.notMem_empty _ hm
  have hW:clippedSource W₁ c₁ θ₁
      (relativeNorm (coordinates p x) Z D B v θ H 0 *
        relativeNorm (coordinates p x) Z D B v θ H 2 *
        relativeNorm (coordinates p x) Z D B v θ H 4)=0 := by
    by_contra hn
    have hh:=hs.1 x hx hn
    simp only [hω,star_zero] at hh
    exact zero_ne_one hh
  apply Finset.sum_eq_zero
  intro ρ hρ
  rw [physicalTerm_extracted p hp hcop hg hpr Ψ j marks _ _ Φ Z D m x hv ρ,
    physicalKernel_nominal _ _ Φ hZ D B v m θ H _ (coordinates_pos p hp x hv)]
  change w x*(_*(_*secondNormProfile _ _ _ _ _
    (relativeNorm (coordinates p x) Z D B v θ H)))=0
  simp only [secondNormProfile,hW,mul_zero,zero_mul,zero_div]

include hp hcop hg in

theorem physical_nonzero_clipping
    (hpr:∀i,lambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Point ι→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂ ω₁ ω₂:ℝ→ℂ)(V:Fin 6→ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D B v θ H m c₁ c₂ θ₁ θ₂ a b η:ℝ)(hZ:1< Z)(hb:1≤ b)
    (hω:Function.support ω₁⊆Set.Icc a b)
    (hs:BlockSupport p (pointSource pool S) W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂)
    (ht:Real.log b≤3*η*Real.log Z)
    (hn:physicalBlock p hg (pointSource pool S) w Ψ j marks
      (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m≠0) :
    0≤ max 0 (columnCenter D B v)-columnCenter D B v ∧
      max 0 (columnCenter D B v)-columnCenter D B v≤3*η := by
  apply freshColumns_initial_clipping_shift p hp pool ω₁ a b Z (columnCenter D B v) η hZ hb hω _ ht
  by_contra he
  have he':freshColumns p pool ω₁ (Z^(columnCenter D B v))=∅:=Finset.not_nonempty_iff_eq_empty.mp he
  exact hn (physicalBlock_zero_of_fresh_empty p hp hcop hg hpr pool S hdiv hf w Ψ j marks
    W₁ W₂ ω₁ ω₂ V Φ Z D B v θ H m c₁ c₂ θ₁ θ₂ (zero_lt_one.trans hZ) hs he')

end InverseInitialEnergyCallerEmpty

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialPhysicalReassembly
open Eisenstein CompletedGauss  FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseInitialRayAttachment InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes
local notation "O"=> Eisenstein.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

include hp hcop in
theorem initialColumn_zero_common (Ψ:O→*ℂ)(j d h:O)(H:Finset ι→ℂ)
    (G U:Finset ι)(hd:¬Disjoint G U):
    initialColumn p hg Ψ j (∏i∈G,p i) d h H U=0:=by
  obtain ⟨i,hiG,hiU⟩:=Finset.not_disjoint_iff.mp hd
  have hm : primeCoprimeMask p U (j*∏k∈G,p k) = 0 := by
    rw [primeCoprimeMask_indicator, if_neg]
    intro h
    exact h i hiU (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem p hiG) j)
  simp only [initialColumn,hm,mul_zero,zero_mul]

include hp hcop in
theorem physicalTerm_zero_left_common (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(G E V N M:Finset ι)(h:O)(ρ:SecondRayIndex)
    (hd:¬Disjoint G (V∪N)):
    physicalTerm p hg Ψ j σ W₁ W₂ Φ Z D m ⟨G,E,V,N,M,h⟩ ρ=0:=by
  simp only [physicalTerm,initialColumn_zero_common p hp hcop hg _ _ _ _ _ _ _ hd,
    star_zero,mul_zero,zero_mul]

include hp hcop in
theorem physicalTerm_zero_right_common (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(G E V N M:Finset ι)(h:O)(ρ:SecondRayIndex)
    (hd:¬Disjoint G (V∪M)):
    physicalTerm p hg Ψ j σ W₁ W₂ Φ Z D m ⟨G,E,V,N,M,h⟩ ρ=0:=by
  simp only [physicalTerm,initialColumn_zero_common p hp hcop hg _ _ _ _ _ _ _ hd,
    mul_zero,zero_mul]

private theorem missing_residual_common (pool G V N:Finset ι)
    (hN:N∈(pool\V).powerset)(hn:N∉((pool\G)\V).powerset):¬Disjoint G (V∪N):=by
  intro hd
  apply hn
  apply Finset.mem_powerset.mpr
  intro i hi
  have hh:=Finset.mem_sdiff.mp (Finset.mem_powerset.mp hN hi)
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hh.1,
    fun hG=> Finset.disjoint_left.mp hd hG (Finset.mem_union_right V hi)⟩,hh.2⟩

include hp hcop in
theorem rectangle_restore_common
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D m:ℝ)(pool G E V:Finset ι)(h:O):
    (∑N∈((pool\G)\V).powerset,∑M∈((pool\G)\V).powerset,∑ρ:SecondRayIndex,
      physicalTerm p hg Ψ j σ W₁ W₂ Φ Z D m ⟨G,E,V,N,M,h⟩ ρ)=
    ∑N∈(pool\V).powerset,∑M∈(pool\V).powerset,∑ρ:SecondRayIndex,
      physicalTerm p hg Ψ j σ W₁ W₂ Φ Z D m ⟨G,E,V,N,M,h⟩ ρ:=by
  have hs:((pool\G)\V).powerset⊆(pool\V).powerset:=
    Finset.powerset_mono.mpr (Finset.sdiff_subset_sdiff Finset.sdiff_subset (Finset.Subset.refl _))
  calc
    _=∑N∈(pool\V).powerset,∑M∈((pool\G)\V).powerset,∑ρ:SecondRayIndex,
        physicalTerm p hg Ψ j σ W₁ W₂ Φ Z D m ⟨G,E,V,N,M,h⟩ ρ:=by
      apply Finset.sum_subset hs
      intro N hN hn
      apply Finset.sum_eq_zero
      intro M hM
      apply Finset.sum_eq_zero
      intro ρ hρ
      exact physicalTerm_zero_left_common p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m G E V N M h ρ
        (missing_residual_common pool G V N hN hn)
    _=_:=by
      apply Finset.sum_congr rfl
      intro N hN
      apply Finset.sum_subset hs
      intro M hM hm
      apply Finset.sum_eq_zero
      intro ρ hρ
      exact physicalTerm_zero_right_common p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m G E V N M h ρ
        (missing_residual_common pool G V M hM hm)

def sourceCodes (pool:Finset ι)(T:Finset O):
    Finset (Σ _G:Finset ι,Σ _E:Finset ι,Finset ι×O):=
  pool.powerset.sigma (fun G=> G.powerset.sigma (fun _E=>(pool\G).powerset×ˢT))

def sourceOfCode (x:Σ _G:Finset ι,Σ _E:Finset ι,Finset ι×O):Source (ι:=ι) 0 where
  common:=x.1
  divisor:=x.2.1
  overlap:=x.2.2.1
  frequency:=x.2.2.2
  assigned:=Fin.elim0

omit [DecidableEq ι] in
theorem sourceOfCode_injective:Function.Injective (sourceOfCode (ι:=ι)):=by
  rintro ⟨G,E,V,h⟩ ⟨G',E',V',h'⟩ he
  have hG:=congrArg Source.common he
  have hE:=congrArg Source.divisor he
  have hV:=congrArg Source.overlap he
  have hh:=congrArg Source.frequency he
  dsimp only [sourceOfCode] at hG hE hV hh
  subst G';subst E';subst V';subst h'
  rfl

def finiteSource (pool:Finset ι)(T:Finset O):Finset (Source (ι:=ι) 0):=
  (sourceCodes pool T).image sourceOfCode

theorem finiteSource_sum {A:Type*}[AddCommMonoid A]
    (pool:Finset ι)(T:Finset O)(f:Source (ι:=ι) 0→A):
    (∑x∈finiteSource pool T,f x)=
      ∑G∈pool.powerset,∑E∈G.powerset,∑V∈(pool\G).powerset,∑h∈T,
        f ⟨G,E,V,h,Fin.elim0⟩:=by
  rw [finiteSource,Finset.sum_image (fun _ _ _ _ he=> sourceOfCode_injective he)]
  simp only [sourceCodes,Finset.sum_sigma,Finset.sum_product,sourceOfCode]

theorem mem_finiteSource (pool:Finset ι)(T:Finset O)(x:Source (ι:=ι) 0):
    x∈finiteSource pool T ↔ x.common⊆pool ∧ x.divisor⊆x.common ∧
      x.overlap⊆pool\x.common ∧ x.frequency∈T:=by
  constructor
  · intro hx
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hx
    simpa only [sourceCodes,Finset.mem_sigma,Finset.mem_product,Finset.mem_powerset,
      sourceOfCode,and_assoc] using ha
  · rintro ⟨hG,hE,hV,hh⟩
    refine Finset.mem_image.mpr ⟨⟨x.common,x.divisor,x.overlap,x.frequency⟩,?_,?_⟩
    · simpa only [sourceCodes,Finset.mem_sigma,Finset.mem_product,Finset.mem_powerset]
        using And.intro hG (And.intro hE (And.intro hV hh))
    · apply Source.ext <;> try rfl
      funext i
      exact Fin.elim0 i

theorem finiteSource_divisor (pool:Finset ι)(T:Finset O):
    ∀x∈finiteSource pool T,x.divisor⊆x.common:=by
  intro x hx
  exact (mem_finiteSource pool T x).mp hx |>.2.1

theorem finiteSource_nonzero (pool:Finset ι)(T:Finset O)(hT:(0:O)∉T):
    ∀x∈finiteSource pool T,x.frequency≠0:=by
  intro x hx he
  exact hT (he ▸ ((mem_finiteSource pool T x).mp hx).2.2.2)

include hp hcop in
theorem finite_physical_reassembly
    (hinj:Function.Injective (fun i=> Ideal.span {p i}))
    (pool:Finset ι)(freqT:Finset O)(Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ):
    (∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
      if Disjoint U T then ∑E∈G.powerset,∑h∈freqT,
        initialPhysicalMode p hg Ψ j σ W Φ Z D m G U T E h else 0)=
    physicalBlock p hg (pointSource pool (finiteSource pool freqT))
      (fun _=>1) Ψ j σ (fun x=> star (W x)) W Φ Z D m:=by
  unfold physicalBlock
  rw [pointSource_sum,finiteSource_sum]
  simp only [one_mul]
  apply Finset.sum_congr rfl
  intro G hG
  have hif (U T:Finset ι):
      (if Disjoint U T then ∑E∈G.powerset,∑h∈freqT,
        initialPhysicalMode p hg Ψ j σ W Φ Z D m G U T E h else 0)=
      ∑E∈G.powerset,∑h∈freqT,if Disjoint U T then
        initialPhysicalMode p hg Ψ j σ W Φ Z D m G U T E h else 0:=by
    split_ifs <;> simp
  simp_rw [hif,Finset.sum_comm (s:=(pool\G).powerset) (t:=G.powerset)]
  apply Finset.sum_congr rfl
  intro E hE
  simp_rw [Finset.sum_comm (s:=(pool\G).powerset) (t:=freqT)]
  apply Finset.sum_congr rfl
  intro h hh
  rw [original_ray_common_insertion p hg hinj]
  apply Finset.sum_congr rfl
  intro V hV
  exact rectangle_restore_common p hp hcop hg Ψ j σ (fun x=> star (W x)) W Φ Z D m pool G E V h

end InverseInitialPhysicalReassembly

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialHighFrequencyTail
theorem norm_tsum_of_finite_bound {α : Type*} (f : α→ℂ) (hf : Summable f) (B : ℝ)
    (hb : ∀F : Finset α,‖∑h∈F,f h‖≤ B) : ‖∑'h,f h‖≤ B := by
  exact le_of_tendsto hf.hasSum.norm (Filter.Eventually.of_forall hb)


end InverseInitialHighFrequencyTail
end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

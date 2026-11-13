/-
Amplification shortening adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.HarmonicMassesAndNonexceptionalPrefactors

/-!
# Amplification shortening

Residual characters and prime roots of the amplification shortening, error energies and the
error polynomial shortening; nonexceptional label weights and reference source blocks;
central-root prime extraction.
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
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentFirstNonexceptionalWeightSum
open Eisenstein  
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCanonicalFirst
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstPhysicalDyadicCount CenteredMomentFirstNonexceptionalPrefactor
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonRadialData
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentActiveSource CenteredMomentSupportedCorrelation CenteredMomentFirstSectors
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentSectorLocalization CenteredMomentRankinRadical
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

abbrev Labels (s:Input ι)(R seed:Ideal O):=
  ActiveLabel (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)

def weight (s:Input ι)(R seed:Ideal O)(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (K r:ℝ)(p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (τ₁ τ₂:Character)
    (n:Blocks (effectiveScale p.val.1 p.val.2 E K) r
      (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm)):ℝ:=
  let h:=commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property
  if block s.η m A t (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) p.val.1 p.val.2 h.1 h.2 E
      (CenteredMomentSecondRetainedRows.retainedRows r 1) W V K
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))=0 then 0
  else ‖scalar p.val.1 p.val.2 h.1 E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*
    volume s.toData/((p.val.1.absNorm:ℝ)*p.val.2.absNorm)*
      Real.sqrt ((τ₁.modulus.absNorm:ℝ)*τ₂.modulus.absNorm)

theorem weight_le (s:Input ι)(R seed:Ideal O)(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (K r a₁ a₂ M F:ℝ)(hK:0< K)(ha₁:0< a₁)(ha₂:0< a₂)(hF:0≤ F)
    (hs₁:∀x,s.W₁ x≠0→a₁≤ x)(hs₂:∀x,s.W₂ x≠0→a₂≤ x)
    (hwin:∀i y,V i y≠0→|y|≤ M)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))(τ₁ τ₂:Character)
    (hc₁:(τ₁.modulus.absNorm:ℝ)≤ F*(s.η.modulus.absNorm:ℝ)*
      ‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=> P.val) E)‖^2*
      ‖ringComplex (activeConductor p.val.1 p.val.2)‖^2)
    (hc₂:(τ₂.modulus.absNorm:ℝ)≤ F*(s.η.modulus.absNorm:ℝ)*
      ‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=> P.val) E)‖^2*
      ‖ringComplex (activeConductor p.val.1 p.val.2)‖^2)
    (n:Blocks (effectiveScale p.val.1 p.val.2 E K) r
      (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm)):
    weight s R seed m A t W V K r p E τ₁ τ₂ n≤
      ((Real.exp M/((∏i,s.lo i)*a₁*a₂))*F*K*(s.η.modulus.absNorm:ℝ))*
        (CenteredMomentFirstInactiveRadicalMass.inactiveWeight p.val.1 p.val.2 E 0/
          (commonRadical p.val.1 p.val.2).absNorm):=by
  have hp:=commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property
  have ha:0<(∏i,s.lo i)*a₁*a₂:=
    mul_pos (mul_pos (Finset.prod_pos (fun i _=> s.lo_pos i)) ha₁) ha₂
  unfold weight
  dsimp only
  split_ifs with hn
  · exact mul_nonneg (by positivity)
      (div_nonneg (CenteredMomentFirstInactiveRadicalMass.inactiveWeight_nonneg _ _ _ _)
        (Nat.cast_nonneg _))
  · have hh:=original_scalar_conductors s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂ m A t _
      p.val.1 p.val.2 hp.1 hp.2 E _ W V K (dyadicScale (n 0)) (dyadicScale (n 1))
      (dyadicScale (n 2)) (dyadicScale (n 3)) M F τ₁ τ₂ hK
      (dyadicScale_pos _) (dyadicScale_pos _) hF hwin hn hc₁ hc₂
    convert hh using 1 ;
      simp only [CenteredMomentFirstInactiveRadicalMass.inactiveWeight,Real.rpow_zero,
        div_one,CenteredMomentFirstPhysicalSource.inactiveWeight] ; ring

def sectorWeight (s:Input ι)(R seed:Ideal O)(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (K r:ℝ)(p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (τ₁ τ₂:Character):ℝ:=
  ∑n:Blocks (effectiveScale p.val.1 p.val.2 E K) r
    (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm),
    weight s R seed m A t W V K r p E τ₁ τ₂ n

def sumWeight (s:Input ι)(R seed:Ideal O)(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (K:ℝ)(radius:(p:Labels s R seed)→Finset (CommonIndex p.val.1 p.val.2)→ℝ)
    (τ₁ τ₂:(p:Labels s R seed)→Finset (CommonIndex p.val.1 p.val.2)→Character):ℝ:=
  ∑p:Labels s R seed,∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
    sectorWeight s R seed m A t W V K (radius p E) p E (τ₁ p E) (τ₂ p E)

theorem original_weight_sum (B L Cr ε:ℝ)(hB:0≤ B)(hL:0≤ L)(hCr:0< Cr)(hε:0<ε):
    ∃C₀:ℝ,0< C₀ ∧ ∀ᶠZ:ℝ in atTop,
    ∀(ι:Type*)[Fintype ι][DecidableEq ι](s:Input ι)(R seed:Ideal O),
      Squarefree seed→seed≠0→s.W₁ 0=0→s.W₂ 0=0→0< sourceRadius s→sourceRadius s≤ Z^B→
    ∀(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K a₁ a₂ M F:ℝ),
      0< K→0< a₁→0< a₂→0≤ F→
      (∀x,s.W₁ x≠0→a₁≤ x)→(∀x,s.W₂ x≠0→a₂≤ x)→
      (∀i y,V i y≠0→|y|≤ M)→
    ∀(radius:(p:Labels s R seed)→Finset (CommonIndex p.val.1 p.val.2)→ℝ)
      (τ₁ τ₂:(p:Labels s R seed)→Finset (CommonIndex p.val.1 p.val.2)→Character),
      (∀p E,radius p E≤ Cr*Z^L)→
      (∀p E,((τ₁ p E).modulus.absNorm:ℝ)≤ F*(s.η.modulus.absNorm:ℝ)*
        ‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=> P.val) E)‖^2*
        ‖ringComplex (activeConductor p.val.1 p.val.2)‖^2)→
      (∀p E,((τ₂ p E).modulus.absNorm:ℝ)≤ F*(s.η.modulus.absNorm:ℝ)*
        ‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=> P.val) E)‖^2*
        ‖ringComplex (activeConductor p.val.1 p.val.2)‖^2)→
      sumWeight s R seed m A t W V K radius τ₁ τ₂≤
        ((Real.exp M/((∏i,s.lo i)*a₁*a₂))*F*K*(s.η.modulus.absNorm:ℝ))*
          (C₀*Z^ε/(seed.absNorm:ℝ)):=by
  obtain ⟨Cd,hCd,hd⟩:=original_blocks_subpower B L Cr (ε/2) hB hL hCr (by linarith)
  obtain ⟨Cm,hCm,hm⟩:=CenteredMomentFirstInactiveRadicalMass.actual_inactive_radical_mass
    B (ε/2) hB (by linarith)
  refine ⟨Cd*Cm,mul_pos hCd hCm,?_⟩
  filter_upwards [hd,eventually_ge_atTop (2:ℝ)] with Z hd hZ
  intro ι _ _ s R seed hs hs0 hz₁ hz₂ hH hHcap m A t W V K a₁ a₂ M F
    hK ha₁ ha₂ hF hs₁ hs₂ hwin radius τ₁ τ₂ hr hc₁ hc₂
  let P:ℝ:=(Real.exp M/((∏i,s.lo i)*a₁*a₂))*F*K*(s.η.modulus.absNorm:ℝ)
  have ha:0<(∏i,s.lo i)*a₁*a₂:=
    mul_pos (mul_pos (Finset.prod_pos (fun i _=> s.lo_pos i)) ha₁) ha₂
  have hP:0≤ P:=by dsimp [P];positivity
  let f:=fun (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))=>
    CenteredMomentFirstInactiveRadicalMass.inactiveWeight p.val.1 p.val.2 E 0/
      (commonRadical p.val.1 p.val.2).absNorm
  have hf:∀p E,0≤ f p E:=by
    intro p E
    exact div_nonneg (CenteredMomentFirstInactiveRadicalMass.inactiveWeight_nonneg _ _ _ _) (Nat.cast_nonneg _)
  have hb (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2)):
      sectorWeight s R seed m A t W V K (radius p E) p E (τ₁ p E) (τ₂ p E)≤
        (Cd*Z^(ε/2)*P)*f p E:=by
    unfold sectorWeight
    have hp:=commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property
    have hcard:=hd p.val.1 p.val.2 hp.1.1 hp.2.1 E K (radius p E) (sourceRadius s)
      hK hH (hr p E) hHcap
    calc
      _≤∑_n:Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
          (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm),P*f p E:=by
        apply Finset.sum_le_sum
        intro n hn
        exact weight_le s R seed m A t W V K (radius p E) a₁ a₂ M F hK ha₁ ha₂ hF
          hs₁ hs₂ hwin p E (τ₁ p E) (τ₂ p E) (hc₁ p E) (hc₂ p E) n
      _≤ _:=by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        convert mul_le_mul_of_nonneg_right hcard (mul_nonneg hP (hf p E)) using 1 <;> first | rfl | ring
  have hmass:=hm Z hZ seed hs hs0
    (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
    (fun I _ hI=> original_column_mask s R seed I hI)
    (fun I _ hI=>(original_column_norm s R seed I hz₁ hz₂ hI).2.trans hHcap) 0 le_rfl
  calc
    _≤∑p:Labels s R seed,∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
        (Cd*Z^(ε/2)*P)*f p E:=by
      unfold sumWeight
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro E hE
      exact hb p E
    _=(Cd*Z^(ε/2)*P)*
        (∑p:Labels s R seed,∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,f p E):=by
      simp only [Finset.mul_sum]
    _≤(Cd*Z^(ε/2)*P)*(Cm*Z^(ε/2)/(seed.absNorm:ℝ)):=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _=P*((Cd*Cm)*Z^ε/(seed.absNorm:ℝ)):=by
      have hz:0< Z:=by linarith
      have he:Z^(ε/2)*Z^(ε/2)=Z^ε:=by rw [←Real.rpow_add hz];congr 1;ring
      calc
        _=P*(Cd*Cm)*(Z^(ε/2)*Z^(ε/2))/(seed.absNorm:ℝ):=by ring
        _=_:=by rw [he];ring

end CenteredMomentFirstNonexceptionalWeightSum

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentFirstNonexceptionalFixedWeightSum
open Eisenstein HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalSource
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentActiveSource CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSupportedCorrelation CenteredMomentSecondRetainedAggregate
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

abbrev Families (s:Input ι)(R seed:Ideal O)(ξ₁ ξ₂:RayCharacter):=
  (p:Labels s R seed)→(E:Finset (CommonIndex p.val.1 p.val.2))→
    FixedPair s.η p.val.1 p.val.2
      (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
        (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property).1 E ξ₁ ξ₂

theorem original_fixed_weight_sum (B L Cr ε:ℝ)(hB:0≤ B)(hL:0≤ L)(hCr:0< Cr)(hε:0<ε):
    ∃C₀:ℝ,0< C₀ ∧ ∀ᶠZ:ℝ in atTop,
    ∀(ι:Type*)[Fintype ι][DecidableEq ι](s:Input ι)(R seed:Ideal O),
      Squarefree seed→seed≠0→s.W₁ 0=0→s.W₂ 0=0→0< sourceRadius s→sourceRadius s≤ Z^B→
    ∀(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K a₁ a₂ M:ℝ),
      0< K→0< a₁→0< a₂→
      (∀x,s.W₁ x≠0→a₁≤ x)→(∀x,s.W₂ x≠0→a₂≤ x)→
      (∀i y,V i y≠0→|y|≤ M)→
    ∀(radius:(p:Labels s R seed)→Finset (CommonIndex p.val.1 p.val.2)→ℝ),
      (∀p E,radius p E≤ Cr*Z^L)→∀ξ₁ ξ₂:RayCharacter,∀F:Families s R seed ξ₁ ξ₂,
      sumWeight s R seed m A t W V K radius (fun p E=>(F p E).left) (fun p E=>(F p E).right)≤
        ((Real.exp M/((∏i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*(s.η.modulus.absNorm:ℝ))*
          (C₀*Z^ε/(seed.absNorm:ℝ)):=by
  obtain ⟨C₀,hC₀,hbound⟩:=original_weight_sum B L Cr ε hB hL hCr hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hbound] with Z hbound
  intro ι _ _ s R seed hs hs0 hz₁ hz₂ hH hHcap m A t W V K a₁ a₂ M
    hK ha₁ ha₂ hs₁ hs₂ hwin radius hr ξ₁ ξ₂ F
  exact hbound ι s R seed hs hs0 hz₁ hz₂ hH hHcap m A t W V K a₁ a₂ M
    fixedPresentationCost hK ha₁ ha₂ fixedPresentationCost_pos.le hs₁ hs₂ hwin radius
    (fun p E=>(F p E).left) (fun p E=>(F p E).right) hr
    (fun p E=>(F p E).conductor_caps.1) (fun p E=>(F p E).conductor_caps.2)

end CenteredMomentFirstNonexceptionalFixedWeightSum

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentFirstNonexceptionalLocalWeightSum
open Eisenstein HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalFixedWeightSum
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicCount
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentActiveSource CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSupportedCorrelation CenteredMomentSecondRetainedAggregate
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentExceptionalAmplitudePair
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def localRadius (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2)):ℝ:=
  frequencyRadius (firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData)) Z ξ

theorem original_local_fixed_weight_sum (hi:ι→ℝ)(b₁ b₂ B ξ ε:ℝ)
    (hB:0≤ B)(hξ:0≤ξ)(hε:0<ε):
    ∃C₀:ℝ,0< C₀ ∧ ∀ᶠZ:ℝ in atTop,
    ∀(s:Input ι)(R seed:Ideal O),Squarefree seed→seed≠0→s.W₁ 0=0→s.W₂ 0=0→
      (∀i,|s.hi i|≤ hi i)→|s.b₁|≤ b₁→|s.b₂|≤ b₂→0< sourceRadius s→
    ∀(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K a₁ a₂ M:ℝ),
      0< K→0< a₁→0< a₂→volume s.toData≤ Z^B→K⁻¹≤ Z^B→
      (∀x,s.W₁ x≠0→a₁≤ x)→(∀x,s.W₂ x≠0→a₂≤ x)→
      (∀i y,V i y≠0→|y|≤ M)→
    ∀ξ₁ ξ₂:RayCharacter,∀F:Families s R seed ξ₁ ξ₂,
      sumWeight s R seed m A t W V K (localRadius s R seed K Z ξ)
        (fun p E=>(F p E).left) (fun p E=>(F p E).right)≤
      ((Real.exp M/((∏i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*(s.η.modulus.absNorm:ℝ))*
        (C₀*Z^ε/(seed.absNorm:ℝ)):=by
  obtain ⟨C₀,hC₀,hbound⟩:=original_fixed_weight_sum (B+1) (3*B+ξ/2) 1 ε
    (by positivity) (by positivity) (by norm_num) hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ),
    eventually_ge_atTop ((∏i,hi i)*b₁*b₂)] with Z hbound hZ hfixed
  intro s R seed hs hs0 hz₁ hz₂ hhi hb₁ hb₂ hH m A t W V K a₁ a₂ M
    hK ha₁ ha₂ hV hKi hs₁ hs₂ hwin ξ₁ ξ₂ F
  apply hbound ι s R seed hs hs0 hz₁ hz₂ hH
    (input_radius_cap hi b₁ b₂ B Z s hhi hb₁ hb₂ hZ hfixed hV)
    m A t W V K a₁ a₂ M hK ha₁ ha₂ hs₁ hs₂ hwin
    (localRadius s R seed K Z ξ) _ ξ₁ ξ₂ F
  intro p E
  simpa only [localRadius,one_mul] using
    local_frequency_radius_cap p.val.1 p.val.2 E K (volume s.toData) Z B ξ
      hK (volume_pos s.toData).le hZ hV hKi

end CenteredMomentFirstNonexceptionalLocalWeightSum

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstPhysicalActiveDictionary
open Eisenstein  
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentRowNorm CenteredMomentHeckeExpansion
open CenteredMomentFirstSectors CenteredMomentFirstSectorEnergy CenteredMomentFirstSectorTransform
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCompleteCommon
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentActive
open CenteredMomentFirstReduced CenteredMomentFirstFrequency CenteredMomentFirstWholeKernel
open CenteredMomentFirstColumns CenteredMomentFirstAssembly CenteredMomentGaussEnergy
open CenteredMomentSmooth CenteredMomentScale CenteredMomentPrimitive 
open CenteredMomentFirstPhysicalSource CenteredMomentActiveSource
local notation "O" => Eisenstein.O

theorem columns_active (C D : Ideal O) (hD : D≠0) (S : Finset (Ideal O))
    (β : Ideal O→ℂ) :
    columns C D hD (activeSource S β)=
      (columns C D hD S).filter (fun I=>β (D*I)≠0) := by
  ext I
  simp only [columns,Finset.mem_filter,mem_residualPool,supportedColumns_active]
  tauto

theorem element_value (C D : Ideal O) (hD : D≠0) (S : Finset (Ideal O))
    (I : columns C D hD S) :
    element C D hD S I=primaryIdealGenerator (I:Ideal O) := rfl

theorem column_sum_active (C D : Ideal O) (hD : D≠0) (S : Finset (Ideal O))
    (β f : Ideal O→ℂ) (hf : ∀I,β (D*I)=0→f I=0) :
    (∑I∈columns C D hD (activeSource S β),f I)=∑I∈columns C D hD S,f I := by
  rw [columns_active,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hi : β (D*I)=0
  · simp only [hi,ne_eq,not_true_eq_false,ite_false,hf I hi]
  · simp only [hi,ne_eq,not_false_eq_true,ite_true]

theorem column_pair_sum_active (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (f : Ideal O→Ideal O→ℂ)
    (hl : ∀I J,β (C*I)=0→f I J=0) (hr : ∀I J,β (D*J)=0→f I J=0) :
    (∑I∈columns C C hC (activeSource S β),∑J∈columns C D hD (activeSource S β),f I J)=
      ∑I∈columns C C hC S,∑J∈columns C D hD S,f I J := by
  simp_rw [column_sum_active C D hD S β _ (fun J h=> hr _ J h)]
  apply column_sum_active C C hC S β
  intro I hi
  exact Finset.sum_eq_zero (fun J hJ=> hl I J hi)

lemma primary_supported (I : Ideal O) (hI : Supported I) :
    Supported (Ideal.span {primaryIdealGenerator I}) := by
  rw [primary_span_supported I hI]
  exact hI

def physicalTerm (η : Character) (m A : O) (t : ℝ) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ)
    (h : O) (I J : Ideal O) : ℂ :=
  if hI : Supported I then if hJ : Supported J then
    let na:=primaryIdealGenerator I
    let nb:=primaryIdealGenerator J
    let e:=TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E
    let k:=K/‖ringComplex e‖^2
    let r:=activeConductor C D
    if IsCoprime I J then
      (tripleRow na nb r (supportedModulusCharacter na (primary_supported I hI))
        (supportedModulusCharacter nb (primary_supported J hJ))⁻¹ (activeFunction C D hC) e *
      ((k/‖ringComplex (na*(nb*r))‖^2:ℝ):ℂ)*
      tripleFourier na nb r
        (supported_element_ne_zero _ (primary_supported I hI))
        (supported_element_ne_zero _ (primary_supported J hJ))
        (finitePrimeModulus_ne_zero _) (supportedModulusCharacter na (primary_supported I hI))
        (supportedModulusCharacter nb (primary_supported J hJ))⁻¹ (activeFunction C D hC) h)*
      (coefficient η m A t β C I*star (coefficient η m A t β D J))*
      windows V (k/‖ringComplex r‖^2) (‖ringComplex h‖^2)
        (‖ringComplex na‖^2) (‖ringComplex nb‖^2) K₀ H₀ A₀ B₀*
      SchwartzPlanePoisson.paperRadialFourier W
        (k*‖ringComplex h‖^2/‖ringComplex (na*(nb*r))‖^2)
    else 0
  else 0 else 0

theorem physicalTerm_zero_left (η : Character) (m A : O) (t : ℝ) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ)
    (h : O) (I J : Ideal O) (hi : β (C*I)=0) :
    physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J=0 := by
  simp only [physicalTerm,coefficient,hi,zero_mul,mul_zero]
  split_ifs <;> rfl

theorem physicalTerm_zero_right (η : Character) (m A : O) (t : ℝ) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ)
    (h : O) (I J : Ideal O) (hj : β (D*J)=0) :
    physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J=0 := by
  simp only [physicalTerm,coefficient,hj,zero_mul,star_zero,mul_zero]
  split_ifs <;> rfl

theorem block_eq_ideal_sums (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ) :
    block η m A t S β C D hC hD E rows W V K K₀ H₀ A₀ B₀=
      inactiveWeight C D E * ∑h∈rows,
        ∑I∈columns C C hC.1 S,∑J∈columns C D hD.1 S,
          physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J := by
  unfold block
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  calc
    _=∑I:columns C C hC.1 S,∑J:columns C D hD.1 S,
        physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J := by
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro J hJ
      simp only [physicalTerm,dif_pos (column_supported C C hC.1 S I),
        dif_pos (column_supported C D hD.1 S J),element]
      rfl
    _=_ := by
      simp_rw [Finset.sum_coe_sort]
      exact Finset.sum_coe_sort (columns C C hC.1 S)
        (fun I=>∑J∈columns C D hD.1 S,
          physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J)

theorem block_active (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ) :
    block η m A t (activeSource S β) β C D hC hD E rows W V K K₀ H₀ A₀ B₀=
      block η m A t S β C D hC hD E rows W V K K₀ H₀ A₀ B₀ := by
  rw [block_eq_ideal_sums,block_eq_ideal_sums]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  exact column_pair_sum_active C D hC.1 hD.1 S β
    (physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h)
    (fun I J hi=> physicalTerm_zero_left η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J hi)
    (fun I J hj=> physicalTerm_zero_right η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J hj)

theorem block_active_ne_zero_iff (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ) :
    block η m A t (activeSource S β) β C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0 ↔
      block η m A t S β C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0 := by
  rw [block_active]

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _
open CenteredMomentCommonRadialData CenteredMomentFirstRetainedNorm
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstScale
open CenteredMomentSectorLocalization CenteredMomentLogDyadic

theorem original_dyadic_block_active (s : Input ι) (R seed : Ideal O)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ) :
    let β:=CenteredMomentOriginalCommonHarmonic.coefficient s R seed
    block s.η m A t (activeSource S β) β C D hC hD E rows W
      (fun _=> logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3))=
    block s.η m A t S β C D hC hD E rows W
      (fun _=> logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  apply block_active

theorem original_sector_active (s : Input ι) (R seed : Ideal O)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    sector s R seed m A t
        (activeSource S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed))
        C D hC hD W K X Z ξ=
      sector s R seed m A t S C D hC hD W K X Z ξ := by
  unfold sector
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only
  apply Finset.sum_congr rfl
  intro n hn
  apply block_active

theorem original_sectorMass_active (s : Input ι) (R seed : Ideal O)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    sectorMass s R seed m A t
        (activeSource S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed))
        C D hC hD W K X Z ξ=
      sectorMass s R seed m A t S C D hC hD W K X Z ξ := by
  unfold sectorMass
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only
  apply Finset.sum_congr rfl
  intro n hn
  rw [block_active]

theorem original_retained_full_sectorMass [DecidableEq ι] (s : Input ι) (R seed : Ideal O)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) (hK : 0< K) :
    let β:=CenteredMomentOriginalCommonHarmonic.coefficient s R seed
    let T:=activeSource S β
    ‖CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A t S β W K X Z ξ‖≤
      ∑p:commonLabels (supportedColumns T) (supportedColumns T),
        sectorMass s R seed m A t S p.val.1 p.val.2
          (commonLabels_supported T p).1 (commonLabels_supported T p).2 W K X Z ξ := by
  dsimp only
  apply (original_retained_norm s R seed hz₁ hz₂ m A t S W K X Z ξ hK).trans_eq
  apply Finset.sum_congr rfl
  intro p hp
  exact original_sectorMass_active s R seed m A t S _ _ _ _ W K X Z ξ

theorem active_sectorMass_sum (s : Input ι) (R seed : Ideal O)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (Φ : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    let T:=activeSource S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
    (∑p:commonLabels (supportedColumns T) (supportedColumns T),
      sectorMass s R seed m A t T p.val.1 p.val.2
        (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K X Z ξ)=
    ∑p:commonLabels (supportedColumns T) (supportedColumns T),
      sectorMass s R seed m A t S p.val.1 p.val.2
        (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K X Z ξ := by
  dsimp only
  apply Finset.sum_congr rfl
  intro p hp
  exact original_sectorMass_active s R seed m A t S _ _ _ _ Φ K X Z ξ

theorem physicalMass_full_source [DecidableEq ι] (s : Input ι) (R seed : Ideal O)
    (m A : O) (Φ : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    CenteredMomentFirstSourceReduction.physicalMass s R seed m A Φ K Z ξ=
      let S:=CenteredMomentSourceMass.finiteColumns (Fintype.piFinset s.pools)
      let β:=CenteredMomentOriginalCommonHarmonic.coefficient s R seed
      let T:=activeSource S β
      ∑p:commonLabels (supportedColumns T) (supportedColumns T),
        sectorMass s R seed m A s.t S p.val.1 p.val.2
          (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K
          (CenteredMomentExceptionalAmplitudePair.volume s.toData) Z ξ := by
  exact active_sectorMass_sum s R seed m A s.t
    (CenteredMomentSourceMass.finiteColumns (Fintype.piFinset s.pools)) Φ K
    (CenteredMomentExceptionalAmplitudePair.volume s.toData) Z ξ

theorem normalized_physicalMass_full_source [DecidableEq ι] (s : Input ι)
    (R seed : Ideal O) (m A : O) (Φ : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    CenteredMomentFirstSourceReduction.physicalMass s R seed m A Φ K Z ξ /
        CenteredMomentExceptionalAmplitudePair.volume s.toData=
      let S:=CenteredMomentSourceMass.finiteColumns (Fintype.piFinset s.pools)
      let β:=CenteredMomentOriginalCommonHarmonic.coefficient s R seed
      let T:=activeSource S β
      (∑p:commonLabels (supportedColumns T) (supportedColumns T),
        sectorMass s R seed m A s.t S p.val.1 p.val.2
          (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K
          (CenteredMomentExceptionalAmplitudePair.volume s.toData) Z ξ) /
        CenteredMomentExceptionalAmplitudePair.volume s.toData := by
  exact congrArg (fun x:ℝ=> x/CenteredMomentExceptionalAmplitudePair.volume s.toData)
    (physicalMass_full_source s R seed m A Φ K Z ξ)

end CenteredMomentFirstPhysicalActiveDictionary

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentFirstReferenceSource
open Eisenstein HeckeFamily CanonicalQuadraticSieve 
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstPhysicalDyadicCount CenteredMomentFirstRetainedNorm
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalLocalWeightSum
open CenteredMomentFirstPhysicalActiveDictionary CenteredMomentFirstSourceReduction
open CenteredMomentFirstInactiveRadicalMass CenteredMomentFirstDiscardedEnergy
open CenteredMomentSecondRetainedAggregate CenteredMomentActiveSource CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentCanonicalFirst CenteredMomentFirstSectors
open CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentExceptionalAmplitudePair CenteredMomentRankinRadical
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

abbrev SourceBlocks (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)(p:Labels s R seed)
    (E:Finset (CommonIndex p.val.1 p.val.2)):=
  Blocks (effectiveScale p.val.1 p.val.2 E K) (localRadius s R seed K Z ξ p E)
    (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm)

def originalBlock (s:Input ι)(R seed:Ideal O)(W:𝓢(ℝ,ℂ))(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (n:SourceBlocks s R seed K Z ξ p E):ℂ:=
  block s.η (CenteredMomentSecondHeightFamily.fixedBadMask*cubicIdealGenerator R) 1 s.t
    (finiteColumns (Fintype.piFinset s.pools)) (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
    p.val.1 p.val.2
    (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property).1
    (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property).2 E
    (retainedRows (localRadius s R seed K Z ξ p E) 1) W (fun _=> logAnnulus)
    K (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))

def radicalWeight (s:Input ι)(R seed:Ideal O)(p:Labels s R seed)
    (E:Finset (CommonIndex p.val.1 p.val.2)):ℝ:=
  CenteredMomentFirstInactiveRadicalMass.inactiveWeight p.val.1 p.val.2 E 0/
    ((commonRadical p.val.1 p.val.2).absNorm:ℝ)

omit [DecidableEq ι] in
lemma radicalWeight_nonneg (s:Input ι)(R seed:Ideal O)(p:Labels s R seed)
    (E:Finset (CommonIndex p.val.1 p.val.2)):0≤ radicalWeight s R seed p E:=
  div_nonneg (inactiveWeight_nonneg _ _ _ _) (Nat.cast_nonneg _)

lemma physicalMass_eq_sum (s:Input ι)(R seed:Ideal O)(W:𝓢(ℝ,ℂ))(K Z ξ:ℝ):
    physicalMass s R seed (CenteredMomentSecondHeightFamily.fixedBadMask*cubicIdealGenerator R) 1 W K Z ξ=
      ∑p:Labels s R seed,∑E∈inactiveSubsets p.val.1 p.val.2,
        ∑n:SourceBlocks s R seed K Z ξ p E,‖originalBlock s R seed W K Z ξ p E n‖:=by
  rw [physicalMass_full_source]
  rfl

theorem original_block_sum (hi:ι→ℝ)(b₁ b₂ B ξ ε:ℝ)
    (hB:0≤ B)(hξ:0≤ξ)(hε:0<ε):
    ∃C₀:ℝ,0< C₀ ∧ ∀ᶠZ:ℝ in atTop,∀s:Input ι,∀R seed:Ideal O,
      Squarefree seed→seed≠0→s.W₁ 0=0→s.W₂ 0=0→
      (∀i,|s.hi i|≤ hi i)→|s.b₁|≤ b₁→|s.b₂|≤ b₂→0< sourceRadius s→
    ∀W:𝓢(ℝ,ℂ),∀K A:ℝ,0< K→0≤ A→volume s.toData≤ Z^B→K⁻¹≤ Z^B→
    (∀p:Labels s R seed,∀E∈inactiveSubsets p.val.1 p.val.2,
      ∀n:SourceBlocks s R seed K Z ξ p E,
      ‖originalBlock s R seed W K Z ξ p E n‖/volume s.toData≤ A*radicalWeight s R seed p E)→
    physicalMass s R seed (CenteredMomentSecondHeightFamily.fixedBadMask*cubicIdealGenerator R) 1 W K Z ξ/
      volume s.toData≤ A*(C₀*Z^ε/(seed.absNorm:ℝ)) := by
  obtain ⟨Cd,hCd,hd⟩:=original_input_local_blocks_subpower hi b₁ b₂ B ξ (ε/2) hB hξ (by linarith)
  obtain ⟨Cm,hCm,hm⟩:=actual_inactive_radical_mass (B+1) (ε/2) (by linarith) (by linarith)
  refine ⟨Cd*Cm,mul_pos hCd hCm,?_⟩
  filter_upwards [hd,eventually_ge_atTop (2:ℝ),eventually_ge_atTop ((∏i,hi i)*b₁*b₂)] with Z hd hZ hfixed
  intro s R seed hs hs0 hz₁ hz₂ hhi hb₁ hb₂ hH W K A hK hA hV hKi hblock
  have hZ1:1≤ Z:=by linarith
  have hcap:=input_radius_cap hi b₁ b₂ B Z s hhi hb₁ hb₂ hZ1 hfixed hV
  have hmass:=hm Z hZ seed hs hs0
    (finiteColumns (Fintype.piFinset s.pools)) (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
    (fun I _ hI=> original_column_mask s R seed I hI)
    (fun I _ hI=>(original_column_norm s R seed I hz₁ hz₂ hI).2.trans hcap) 0 (le_refl _)
  have hf:∀p E,0≤ radicalWeight s R seed p E:=radicalWeight_nonneg s R seed
  have hsector (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
      (hE:E∈inactiveSubsets p.val.1 p.val.2):
      (∑n:SourceBlocks s R seed K Z ξ p E,‖originalBlock s R seed W K Z ξ p E n‖/volume s.toData)≤
        (Cd*Z^(ε/2)*A)*radicalWeight s R seed p E := by
    have hp:=commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property
    have hcard:=hd s hhi hb₁ hb₂ hH p.val.1 p.val.2 hp.1.1 hp.2.1 E K hK hV hKi
    change (Fintype.card (SourceBlocks s R seed K Z ξ p E):ℝ)≤ Cd*Z^(ε/2) at hcard
    calc
      _≤∑_n:SourceBlocks s R seed K Z ξ p E,A*radicalWeight s R seed p E:=
        Finset.sum_le_sum (fun n _=> hblock p E hE n)
      _ = (Fintype.card (SourceBlocks s R seed K Z ξ p E):ℝ)*(A*radicalWeight s R seed p E) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _ ≤ (Cd*Z^(ε/2))*(A*radicalWeight s R seed p E) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg hA (hf p E))
      _ = _ := (mul_assoc _ _ _).symm
  rw [physicalMass_eq_sum]
  simp only [Finset.sum_div]
  calc
    _≤∑p:Labels s R seed,∑E∈inactiveSubsets p.val.1 p.val.2,
        (Cd*Z^(ε/2)*A)*radicalWeight s R seed p E:=by
      apply Finset.sum_le_sum;intro p _
      exact Finset.sum_le_sum (fun E hE=> hsector p E hE)
    _=(Cd*Z^(ε/2)*A)*(∑p:Labels s R seed,∑E∈inactiveSubsets p.val.1 p.val.2,
        radicalWeight s R seed p E):=by simp_rw [←Finset.mul_sum]
    _≤(Cd*Z^(ε/2)*A)*(Cm*Z^(ε/2)/(seed.absNorm:ℝ)):=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _=_ := by
      rw [show Z^ε=Z^(ε/2)*Z^(ε/2) by rw [←Real.rpow_add (by linarith : 0< Z)];congr 1;ring]
      ring

end CenteredMomentFirstReferenceSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentAmplificationEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationCount
local notation "O" => Eisenstein.O

def eligiblePairs (rows P : Finset O) (allow : O → O → Prop) : Finset (O × O) :=
  (rows.product P).filter (fun x => allow x.1 x.2)

def outputRow (x : O × O) : O := x.2^6*x.1

theorem outputRow_norm (x : O × O) (Z M L : ℝ) (hZ : 0 < Z)
    (hh : (Ideal.absNorm (Ideal.span {x.1}) : ℝ) ≤ Z^M)
    (hp : (Ideal.absNorm (Ideal.span {x.2}) : ℝ) ≤ Z^L) :
    (Ideal.absNorm (Ideal.span {outputRow x}) : ℝ) ≤ Z^(M+6*L) := by
  calc
    _ = (Ideal.absNorm (Ideal.span {x.2}) : ℝ)^6 *
        (Ideal.absNorm (Ideal.span {x.1}) : ℝ) := by
      simp only [outputRow,← Ideal.span_singleton_mul_span_singleton,
        ← Ideal.span_singleton_pow,map_mul,map_pow,Nat.cast_mul,Nat.cast_pow]
    _ ≤ (Z^L)^6 * Z^M := mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hp 6) hh
      (Nat.cast_nonneg _) (by positivity)
    _ = Z^(M+6*L) := by
      rw [← Real.rpow_mul_natCast hZ.le,← Real.rpow_add hZ]
      congr 1
      ring

theorem amplified_energy_pushforward (rows P : Finset O) (allow : O → O → Prop)
    (hrows : ∀ h ∈ rows, h ≠ 0) (hp : ∀ p ∈ P, Prime p)
    (hprimary : ∀ p ∈ P, lambda^2 ∣ p-1)
    (Z ell M L : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hpl : ∀ p ∈ P, Z^ell ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ))
    (hpu : ∀ p ∈ P, (Ideal.absNorm (Ideal.span {p}) : ℝ) ≤ Z^L)
    (hhu : ∀ h ∈ rows, (Ideal.absNorm (Ideal.span {h}) : ℝ) ≤ Z^M)
    (H : O → ℂ) :
    (∑ x ∈ eligiblePairs rows P allow, ‖H (outputRow x)‖^2) ≤
      ((M+6*L)/ell)*∑ y ∈ (eligiblePairs rows P allow).image outputRow, ‖H y‖^2 := by
  apply positive_pushforward_bound _ outputRow (fun y => ‖H y‖^2) _ (fun _ _ => sq_nonneg _)
  intro y hy
  obtain ⟨x,hx,hxy⟩ := Finset.mem_image.mp hy
  have hxm := Finset.mem_product.mp (Finset.mem_filter.mp hx).1
  have hy0 : y ≠ 0 := by
    rw [← hxy]
    exact mul_ne_zero (pow_ne_zero _ (hp x.2 hxm.2).ne_zero) (hrows x.1 hxm.1)
  apply amplified_row_fiber_count _ y hy0
  · intro z hz
    exact hp z.2 (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).2
  · intro z hz
    exact hprimary z.2 (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).2
  · intro z hz
    exact (Finset.mem_filter.mp hz).2
  · exact hZ
  · exact hell
  · intro z hz
    exact hpl z.2 (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).2
  · rw [← hxy]
    exact outputRow_norm x Z M L (zero_lt_one.trans hZ) (hhu x.1 hxm.1) (hpu x.2 hxm.2)

theorem sum_eligiblePairs (rows P : Finset O) (allow : O → O → Prop) (f : O → O → ℝ) :
    (∑ h ∈ rows, ∑ p ∈ P.filter (allow h), f h p) =
      ∑ x ∈ eligiblePairs rows P allow, f x.1 x.2 := by
  simp only [eligiblePairs,Finset.sum_filter]
  exact (Finset.sum_product rows P (fun x : O × O => if allow x.1 x.2 then f x.1 x.2 else 0)).symm

def errorEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) (h p : O) : ℝ :=
  ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 1 h‖^2 +
  ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 6 h‖^2 +
  ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 7 h‖^2

theorem gauss_energy_amplification {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (rows P : Finset O) (allow : O → O → Prop)
    (hrows : ∀ h ∈ rows, h ≠ 0) (hp : ∀ p ∈ P, Prime p)
    (hs : ∀ p ∈ P, Supported (Ideal.span {p}))
    (hg : ∀ p ∈ P, lambda ∉ Ideal.span {p})
    (hc : ∀ p ∈ P, ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hprimary : ∀ p ∈ P, lambda^2 ∣ p-1)
    (hallow : ∀ h ∈ rows, ∀ p ∈ P, allow h p → ¬p ∣ h)
    (κ : ℝ) (hκ : 0 < κ) (hsize : ∀ h ∈ rows, κ ≤ (P.filter (allow h)).card)
    (Z ell M L : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hpl : ∀ p ∈ P, Z^ell ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ))
    (hpu : ∀ p ∈ P, (Ideal.absNorm (Ideal.span {p}) : ℝ) ≤ Z^L)
    (hhu : ∀ h ∈ rows, (Ideal.absNorm (Ideal.span {h}) : ℝ) ≤ Z^M) :
    (∑ h ∈ rows, ‖gaussPolynomial S a ha c h‖^2) ≤ (4/κ)*
      (((M+6*L)/ell)*(∑ y ∈ (eligiblePairs rows P allow).image outputRow,
        ‖gaussPolynomial S a ha c y‖^2) +
        ∑ x ∈ eligiblePairs rows P allow, errorEnergy S a ha c x.1 x.2) := by
  have hj : (∑ h ∈ rows, ‖gaussPolynomial S a ha c h‖^2) ≤
      (4/κ)*∑ x ∈ eligiblePairs rows P allow,
        (‖gaussPolynomial S a ha c (outputRow x)‖^2 + errorEnergy S a ha c x.1 x.2) := by
    change _ ≤ (4/κ)*∑ x ∈ eligiblePairs rows P allow,
      (‖gaussPolynomial S a ha c (x.2^6*x.1)‖^2 + errorEnergy S a ha c x.1 x.2)
    rw [← sum_eligiblePairs rows P allow (fun h p =>
      ‖gaussPolynomial S a ha c (p^6*h)‖^2 + errorEnergy S a ha c h p),Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h hh
    have hn : (P.filter (allow h)).Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp (hκ.trans_le (hsize h hh)))
    have hb := polynomial_pool_bound S a ha c (P.filter (allow h)) hn
      (fun p hpP => hp p (Finset.mem_filter.mp hpP).1)
      (fun p hpP => hs p (Finset.mem_filter.mp hpP).1)
      (fun p hpP => hg p (Finset.mem_filter.mp hpP).1)
      (fun p hpP => hc p (Finset.mem_filter.mp hpP).1) h
      (fun p hpP => hallow h hh p (Finset.mem_filter.mp hpP).1 (Finset.mem_filter.mp hpP).2)
    calc
      _ ≤ (4 / ((P.filter (allow h)).card : ℝ)) *
          ∑ p ∈ P.filter (allow h), (‖gaussPolynomial S a ha c (p^6*h)‖^2 + errorEnergy S a ha c h p) := by
        simpa only [errorEnergy,add_assoc] using hb
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by norm_num) hκ (hsize h hh))
        (Finset.sum_nonneg (fun p _ => add_nonneg (sq_nonneg _) (by unfold errorEnergy; positivity)))
  have hf := amplified_energy_pushforward rows P allow hrows hp hprimary Z ell M L hZ hell
    hpl hpu hhu (gaussPolynomial S a ha c)
  apply hj.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.sum_add_distrib]
  exact add_le_add hf le_rfl

end CenteredMomentAmplificationEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped BigOperators Classical
namespace CenteredMomentAmplificationEligibility
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationEnergy
open CanonicalQuadraticSieve
local notation "O" => Eisenstein.O

def exclusionIdeal (R s : Ideal O) (h : O) : Ideal O := R*s*Ideal.span {h}

def eligible (R s : Ideal O) (h p : O) : Prop := ¬Ideal.span {p}∣exclusionIdeal R s h

theorem exclusionIdeal_ne_zero (R s : Ideal O) (h : O)
    (hR : R ≠ 0) (hs : s ≠ 0) (hh : h ≠ 0) : exclusionIdeal R s h ≠ 0 :=
  mul_ne_zero (mul_ne_zero hR hs) (Ideal.span_singleton_eq_bot.not.mpr hh)

theorem exclusionIdeal_norm (R s : Ideal O) (h : O) (Z B b M : ℝ) (hZ : 0 < Z)
    (hR : (Ideal.absNorm R:ℝ) ≤ Z^B) (hs : (Ideal.absNorm s:ℝ) ≤ Z^b)
    (hh : (Ideal.absNorm (Ideal.span {h}):ℝ) ≤ Z^M) :
    (Ideal.absNorm (exclusionIdeal R s h):ℝ) ≤ Z^(B+b+M) := by
  simp only [exclusionIdeal,map_mul,Nat.cast_mul]
  calc
    _ ≤ (Z^B*Z^b)*Z^M := mul_le_mul
      (mul_le_mul hR hs (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)) hh
      (Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [← Real.rpow_add hZ,← Real.rpow_add hZ]

theorem eligible_not_dvd_row (R s : Ideal O) (h p : O) (he : eligible R s h p) : ¬p∣h := by
  intro hd
  apply he
  exact (Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_span_singleton.mpr hd)).trans
    (dvd_mul_left (Ideal.span {h}) (R*s))

theorem eligible_coprime_divisor (R s : Ideal O) (h p : O)
    (hp : Prime (Ideal.span {p})) (he : eligible R s h p) : IsCoprime s (Ideal.span {p}) := by
  have hmax := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  apply IsCoprime.symm
  apply Ideal.isCoprime_iff_codisjoint.mpr
  apply (Ideal.isMaximal_def.mp hmax).not_le_iff_codisjoint.mp
  intro hle
  have hd : Ideal.span {p} ∣ s := Ideal.dvd_iff_le.mpr hle
  exact he (hd.trans ((dvd_mul_left s R).mul_right (Ideal.span {h})))

theorem uniform_eligible_pool (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P,Q ∉ fixedBadPrimes)
    (R s : Ideal O) (hR0 : R ≠ 0) (hs0 : s ≠ 0)
    (Z ell B b M : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hlower : ∀ Q ∈ P,Z^ell ≤ (Ideal.absNorm Q:ℝ))
    (hR : (Ideal.absNorm R:ℝ) ≤ Z^B) (hs : (Ideal.absNorm s:ℝ) ≤ Z^b)
    (hsize : 2*((B+b+M)/ell) ≤ P.card)
    (h : O) (hh0 : h ≠ 0) (hh : (Ideal.absNorm (Ideal.span {h}):ℝ) ≤ Z^M) :
    (P.card:ℝ)/2 ≤ ((elementPool P).filter (eligible R s h)).card := by
  unfold eligible
  convert eligible_element_card_half P hp hbad (exclusionIdeal R s h)
    (exclusionIdeal_ne_zero R s h hR0 hs0 hh0) Z ell (B+b+M) hZ hell hlower
    (exclusionIdeal_norm R s h Z B b M (zero_lt_one.trans hZ) hR hs hh) hsize

theorem actual_eligible_amplification {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (rows : Finset O) (hrows : ∀ h ∈ rows,h ≠ 0)
    (P : Finset (Ideal O)) (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P,Q ∉ fixedBadPrimes)
    (hP : P.Nonempty) (R s : Ideal O) (hR0 : R ≠ 0) (hs0 : s ≠ 0)
    (Z ell B b M L : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hlower : ∀ Q ∈ P,Z^ell ≤ (Ideal.absNorm Q:ℝ))
    (hupper : ∀ Q ∈ P,(Ideal.absNorm Q:ℝ) ≤ Z^L)
    (hR : (Ideal.absNorm R:ℝ) ≤ Z^B) (hs : (Ideal.absNorm s:ℝ) ≤ Z^b)
    (hsize : 2*((B+b+M)/ell) ≤ P.card)
    (hrowNorm : ∀ h ∈ rows,(Ideal.absNorm (Ideal.span {h}):ℝ) ≤ Z^M) :
    (∑ h ∈ rows, ‖CenteredMomentGaussEnergy.gaussPolynomial S a ha c h‖^2) ≤
      (8/(P.card:ℝ))*
        (((M+6*L)/ell)*(∑ y ∈ (eligiblePairs rows (elementPool P) (eligible R s)).image outputRow,
          ‖CenteredMomentGaussEnergy.gaussPolynomial S a ha c y‖^2)+
          ∑ x ∈ eligiblePairs rows (elementPool P) (eligible R s),errorEnergy S a ha c x.1 x.2) := by
  have hpos : (0:ℝ)< P.card := by exact_mod_cast Finset.card_pos.mpr hP
  have hb := gauss_energy_amplification S a ha c rows (elementPool P) (eligible R s) hrows
    (fun p hpP => (elementPool_data P hp hbad p hpP).1)
    (fun p hpP => (elementPool_data P hp hbad p hpP).2.2.2.1)
    (fun p hpP => (elementPool_data P hp hbad p hpP).2.2.2.2.1)
    (fun p hpP => (elementPool_data P hp hbad p hpP).2.2.2.2.2)
    (fun p hpP => (elementPool_data P hp hbad p hpP).2.2.1)
    (fun h hh p hpP he => eligible_not_dvd_row R s h p he)
    ((P.card:ℝ)/2) (by positivity)
    (fun h hh => uniform_eligible_pool P hp hbad R s hR0 hs0 Z ell B b M hZ hell hlower hR hs hsize h (hrows h hh) (hrowNorm h hh))
    Z ell M L hZ hell
    (fun p hpP => hlower (Ideal.span {p}) (elementPool_data P hp hbad p hpP).2.1)
    (fun p hpP => hupper (Ideal.span {p}) (elementPool_data P hp hbad p hpP).2.1)
    hrowNorm
  convert hb using 1 <;> first | rfl | ring

end CenteredMomentAmplificationEligibility

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
open Filter
namespace CenteredMomentAmplificationSlotGap
local notation "O" => Eisenstein.O

theorem eventually_scale_gap (b η ell : ℝ) (hgap : η < ell) :
    ∀ᶠ Z : ℝ in atTop, 1 ≤ Z ∧ b*Z^η < Z^ell := by
  have hg := (tendsto_rpow_atTop (sub_pos.mpr hgap)).eventually (eventually_gt_atTop b)
  filter_upwards [hg,eventually_ge_atTop (1:ℝ)] with Z hz hZ
  refine ⟨hZ,?_⟩
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hh := mul_lt_mul_of_pos_right hz (Real.rpow_pos_of_pos hZ0 η)
  rwa [← Real.rpow_add hZ0,sub_add_cancel] at hh

theorem amplifier_not_dvd_slot (P Q : Ideal O) (hP : Prime P) (hQ : Prime Q)
    (Z ell η b : ℝ) (hgap : b*Z^η < Z^ell)
    (hPN : Z^ell ≤ (Ideal.absNorm P:ℝ)) (hQN : (Ideal.absNorm Q:ℝ) ≤ b*Z^η) :
    ¬P∣Q := by
  intro hd
  have he := (prime_dvd_prime_iff_eq hP hQ).mp hd
  subst Q
  linarith

theorem amplifier_not_dvd_slot_product {ι : Type*} (S : Finset ι) (v : ι → Ideal O)
    (P : Ideal O) (hP : Prime P) (hv : ∀ i ∈ S,Prime (v i))
    (Z ell η b : ℝ) (hgap : b*Z^η < Z^ell) (hPN : Z^ell ≤ (Ideal.absNorm P:ℝ))
    (hN : ∀ i ∈ S,(Ideal.absNorm (v i):ℝ) ≤ b*Z^η) :
    ¬P∣∏ i ∈ S,v i := by
  apply hP.not_dvd_finsetProd
  intro i hi
  exact amplifier_not_dvd_slot P (v i) hP (hv i hi) Z ell η b hgap hPN (hN i hi)

theorem live_profile_norm_bound (W : ℝ → ℂ) (b Z z η : ℝ) (I : Ideal O)
    (hb : 0 ≤ b) (hZ : 1 ≤ Z) (hz : z ≤ η)
    (hs : Function.support W ⊆ Set.Iic b)
    (hW : W ((Ideal.absNorm I:ℝ)/Z^z) ≠ 0) :
    (Ideal.absNorm I:ℝ) ≤ b*Z^η := by
  have hpow : 0 < Z^z := Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _
  have h := (div_le_iff₀ hpow).mp (hs hW)
  exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hz) hb)

theorem eventually_live_slot_exclusion (b η ell : ℝ) (hb : 0 ≤ b) (hgap : η < ell) :
    ∀ᶠ Z : ℝ in atTop,
      ∀ {ι : Type*} (S : Finset ι) (v : ι → Ideal O) (W : ι → ℝ → ℂ) (z : ι → ℝ),
      (∀ i ∈ S,Prime (v i)) → (∀ i ∈ S,z i ≤ η) →
      (∀ i ∈ S,Function.support (W i) ⊆ Set.Iic b) →
      (∀ i ∈ S,W i ((Ideal.absNorm (v i):ℝ)/Z^(z i)) ≠ 0) →
      ∀ P : Ideal O,Prime P → Z^ell ≤ (Ideal.absNorm P:ℝ) → ¬P∣∏ i ∈ S,v i := by
  filter_upwards [eventually_scale_gap b η ell hgap] with Z hZ
  intro ι S v W z hv hz hs hW P hP hPN
  exact amplifier_not_dvd_slot_product S v P hP hv Z ell η b hZ.2 hPN
    (fun i hi => live_profile_norm_bound (W i) b Z (z i) η (v i) hb hZ.1 (hz i hi) (hs i hi) (hW i hi))

end CenteredMomentAmplificationSlotGap

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentAmplificationShortening
open CanonicalQuadraticSieve CanonicalRowCompletion 
open CenteredMomentGaussEnergy CenteredMomentSupportedCorrelation CenteredMomentUnequal
open CenteredMomentAmplification CenteredMomentAmplificationLocal CenteredMomentAmplificationGlobal
open ProbePhysical
local notation "O" => Eisenstein.O

def residualCharacter (p : O) (k : ℕ) (u : O) : ℂ :=
  sexticReciprocityPhase p u ^ k * idealRowHom u (Ideal.span {p}) ^ (2*k)

theorem crossFactor_primary (p u : O) (k : ℕ)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hpp : lambda^2 ∣ p-1) (hup : lambda^2 ∣ u-1) :
    idealRowHom u (Ideal.span {p^k}) * idealRowHom (p^k) (Ideal.span {u}) =
      residualCharacter p k u := by
  rw [← Ideal.span_singleton_pow,map_pow,idealRowHom_argument_pow p k _ ((supported_iff_native _).mp hu).1,
    idealRowHom_primary_reciprocity u p hup hpp ((supported_iff_native _).mp hu) ((supported_iff_native _).mp hp),
    sexticReciprocityPhase_symm u p,mul_pow]
  unfold residualCharacter
  rw [show 2*k=k+k by omega,pow_add]
  ring

theorem gauss_primary_power_product (p u : O) (k : ℕ)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hpp : lambda^2 ∣ p-1) (hup : lambda^2 ∣ u-1)
    (hcop : IsCoprime p u) (h : O) :
    sexticGauss (p^k*u) (mul_ne_zero (pow_ne_zero _ (CenteredMomentSupportedCorrelation.supported_element_ne_zero p hp))
      (CenteredMomentSupportedCorrelation.supported_element_ne_zero u hu)) h =
      residualCharacter p k u * sexticGauss (p^k) (pow_ne_zero _ (CenteredMomentSupportedCorrelation.supported_element_ne_zero p hp)) h *
        sexticGauss u (CenteredMomentSupportedCorrelation.supported_element_ne_zero u hu) h := by
  rw [sexticGauss_coprime_product (p^k) u (supported_power p hp k) hu hcop.pow_left,
    crossFactor_primary p u k hp hu hpp hup]

theorem residualCharacter_six (p u : O) (hp : Supported (Ideal.span {p})) :
    residualCharacter p 6 u = sexticReciprocityPhase p u ^ 6 *
      coprimalityMask u p := by
  unfold residualCharacter
  norm_num only
  rw [twelfth_power_mask p hp u]

def primeRoot (p : O) (k : ℕ) : ℂ :=
  (Real.sqrt ((Ideal.absNorm (Ideal.span {p}) : ℝ)^k) : ℂ)

theorem primeRoot_sq (p : O) (k : ℕ) :
    primeRoot p k * primeRoot p k = (Ideal.absNorm (Ideal.span {p}) : ℂ)^k := by
  rw [primeRoot,← Complex.ofReal_mul,Real.mul_self_sqrt (by positivity),Complex.ofReal_pow,
    Complex.ofReal_natCast]

theorem modulusRoot_product (p u : O) (k : ℕ) :
    (Real.sqrt (Ideal.absNorm (Ideal.span {p^k*u}) : ℝ) : ℂ) =
      primeRoot p k * (Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ) : ℂ) := by
  simp only [← Ideal.span_singleton_mul_span_singleton,← Ideal.span_singleton_pow,
    map_mul,map_pow,Nat.cast_mul,Nat.cast_pow,Real.sqrt_mul (by positivity :
      0 ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ)^k),Complex.ofReal_mul,primeRoot]

theorem gaussRow_shortening (p u : O) (k : ℕ)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hpp : lambda^2 ∣ p-1) (hup : lambda^2 ∣ u-1)
    (hcop : IsCoprime p u) (h : O) :
    gaussRow (p^k*u) (supported_mul_elements _ _ (supported_power p hp k) hu) h =
      residualCharacter p k u *
        (sexticGauss (p^k) (pow_ne_zero _ (CenteredMomentSupportedCorrelation.supported_element_ne_zero p hp)) h / primeRoot p k) *
          gaussRow u hu h := by
  unfold gaussRow
  rw [gauss_primary_power_product p u k hp hu hpp hup hcop h,modulusRoot_product]
  ring

theorem central_error_shortening (p u : O) (n : ℕ)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hpp : lambda^2 ∣ p-1) (hup : lambda^2 ∣ u-1)
    (hcop : IsCoprime p u) (h : O) :
    (gaussRow (p^(n+1)*u) (supported_mul_elements _ _ (supported_power p hp (n+1)) hu) h -
      gaussRow (p^(n+1)*u) (supported_mul_elements _ _ (supported_power p hp (n+1)) hu) (p^6*h)) /
        primeRoot p (n+1) =
      (centralLocal p (CenteredMomentSupportedCorrelation.supported_element_ne_zero p hp) n h -
        centralLocal p (CenteredMomentSupportedCorrelation.supported_element_ne_zero p hp) n (p^6*h)) *
          (residualCharacter p (n+1) u * gaussRow u hu h) := by
  rw [gaussRow_shortening p u (n+1) hp hu hpp hup hcop,
    gaussRow_shortening p u (n+1) hp hu hpp hup hcop]
  have hinv : gaussRow u hu (p^6*h) = gaussRow u hu h := by
    unfold gaussRow
    rw [gauss_sixth_frequency u hu p h hcop]
  rw [hinv]
  unfold centralLocal
  rw [← primeRoot_sq p (n+1)]
  ring

theorem supported_phase_sq (p u : O) (hp : Supported (Ideal.span {p}))
    (hu : Supported (Ideal.span {u})) : sexticReciprocityPhase p u ^ 2 = 1 := by
  have hp2 : ¬ (2 : O) ∣ p :=
    ((CanonicalRowCompletion.supported_span_iff p).mp ((supported_iff_native _).mp hp)).2
  have hu2 : ¬ (2 : O) ∣ u :=
    ((CanonicalRowCompletion.supported_span_iff u).mp ((supported_iff_native _).mp hu)).2
  rw [sexticReciprocityPhase_good p u hp2 hu2]
  exact FixedRayArithmetic.quadraticPhase_sq
    (fun h => hp2 (Ideal.mem_span_singleton.mp h))
    (fun h => hu2 (Ideal.mem_span_singleton.mp h))

theorem residualCharacter_moving (p u : O) (k : ℕ)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hpp : lambda^2 ∣ p-1) (hup : lambda^2 ∣ u-1) :
    residualCharacter p k u = sexticReciprocityPhase p u ^ k *
      idealRowHom (p^(2*k)) (Ideal.span {u}) := by
  rw [residualCharacter,idealRowHom_argument_pow p (2*k) _ ((supported_iff_native _).mp hu).1,
    idealRowHom_primary_reciprocity p u hpp hup ((supported_iff_native _).mp hp) ((supported_iff_native _).mp hu),mul_pow,
    pow_mul,supported_phase_sq p u hp hu,one_pow,one_mul]

def errorScalar (p : O) (hp : p ≠ 0) (n : ℕ) (h : O) : ℂ :=
  centralLocal p hp n h - centralLocal p hp n (p^6*h)

theorem centralLocal_unit_zero (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (n : ℕ) (hn : n ≠ 0)
    (h : O) (hph : ¬p ∣ h) : centralLocal p hp.ne_zero n h = 0 := by
  unfold centralLocal
  rw [← mul_one h,sexticGauss_unit_scale _ (supported_power p hs (n+1)) h 1
    ((hp.irreducible.coprime_iff_not_dvd.mpr hph).symm.pow_right),
    gauss_prime_power_one p hp hg hc]
  simp only [hn,ite_false,mul_zero,zero_div]

theorem centralLocal_six_zero (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (n : ℕ) (hn5 : n ≠ 5) (hn6 : n ≠ 6)
    (h : O) (hph : ¬p ∣ h) : centralLocal p hp.ne_zero n (p^6*h) = 0 := by
  unfold centralLocal
  rw [mul_comm (p^6) h,sexticGauss_unit_scale _ (supported_power p hs (n+1)) h (p^6)
    ((hp.irreducible.coprime_iff_not_dvd.mpr hph).symm.pow_right),
    gauss_prime_power_six p hp hg hc]
  simp only [hn5,hn6,ite_false,mul_zero,zero_div]

theorem errorScalar_norms (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (h : O) (hph : ¬p ∣ h) :
    ‖errorScalar p hp.ne_zero 0 h‖^2 = (Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹ ∧
    ‖errorScalar p hp.ne_zero 5 h‖^2 = (1-(Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹)^2 ∧
    ‖errorScalar p hp.ne_zero 6 h‖^2 = (Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹ := by
  unfold errorScalar
  rw [centralLocal_six_zero p hp hs hg hc 0 (by decide) (by decide) h hph,
    centralLocal_unit_zero p hp hs hg hc 5 (by decide) h hph,
    centralLocal_unit_zero p hp hs hg hc 6 (by decide) h hph,
    sub_zero,zero_sub,zero_sub,norm_neg,norm_neg,mul_comm (p^6) h]
  exact ⟨centralLocal_one_norm_sq p hp hs hg hc h hph,
    centralLocal_six_norm_sq p hp hs hg hc h hph,
    centralLocal_seven_norm_sq p hp hs hg hc h hph⟩

theorem error_polynomial_shortening {α : Type*} (S : Finset α)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : lambda^2 ∣ p-1) (n : ℕ) (u : α → O)
    (hu : ∀ i, Supported (Ideal.span {u i})) (hup : ∀ i, lambda^2 ∣ u i-1)
    (hcop : ∀ i, IsCoprime p (u i)) (c : α → ℂ) (h : O) :
    amplificationError S (fun i => p^(n+1)*u i)
      (fun i => supported_mul_elements _ _ (supported_power p hs (n+1)) (hu i))
      (fun i => c i / primeRoot p (n+1)) (fun i => multiplicity p (p^(n+1)*u i)) p (n+1) h =
      errorScalar p hp.ne_zero n h *
        gaussPolynomial S u hu (fun i => c i * residualCharacter p (n+1) (u i)) h := by
  unfold amplificationError gaussPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hv : multiplicity p (p^(n+1)*u i) = n+1 := by
    rw [multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp
      (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (CenteredMomentSupportedCorrelation.supported_element_ne_zero _ (hu i)))),
      multiplicity_pow_self_of_prime hp,
      multiplicity_eq_zero.mpr (hp.irreducible.coprime_iff_not_dvd.mp (hcop i)),add_zero]
  dsimp only
  simp only [if_pos hv]
  have he := central_error_shortening p (u i) n hs (hu i) hpp (hup i) (hcop i) h
  change _ = errorScalar p hp.ne_zero n h *
    (c i * residualCharacter p (n+1) (u i) * gaussRow (u i) (hu i) h)
  calc
    _ = c i * ((gaussRow (p^(n+1)*u i)
        (supported_mul_elements _ _ (supported_power p hs (n+1)) (hu i)) h -
      gaussRow (p^(n+1)*u i)
        (supported_mul_elements _ _ (supported_power p hs (n+1)) (hu i)) (p^6*h)) /
        primeRoot p (n+1)) := by ring
    _ = _ := by rw [he]; unfold errorScalar; ring

end CenteredMomentAmplificationShortening

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentAmplificationRectangle
open CenteredMomentRectangle CenteredMomentExtraction CenteredMomentAmplificationShortening
local notation "O" => Eisenstein.O

theorem centralRoot_extract (p : O) (hp : p ≠ 0) (k : ℕ) (T : ℝ) (hT : 0 < T) :
    (Real.sqrt T : ℂ)⁻¹ = (primeRoot p k)⁻¹ *
      (Real.sqrt (T / (Ideal.absNorm (Ideal.span {p}) : ℝ)^k) : ℂ)⁻¹ := by
  have hN : 0 < (Ideal.absNorm (Ideal.span {p}) : ℝ) := Nat.cast_pos.mpr
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp)))
  have hroot : Real.sqrt T = Real.sqrt ((Ideal.absNorm (Ideal.span {p}) : ℝ)^k) *
      Real.sqrt (T / (Ideal.absNorm (Ideal.span {p}) : ℝ)^k) := by
    rw [← Real.sqrt_mul (pow_nonneg hN.le k)]
    congr 1
    field_simp
  rw [hroot,Complex.ofReal_mul,mul_inv,primeRoot]

theorem centered_coefficient_prime_extract (p : O) (hp : p ≠ 0)
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ T : ℝ) (hT : 0 < T)
    (Q I J : Ideal O) (k j : ℕ) (hj : j ≤ k) :
    (Real.sqrt T : ℂ)⁻¹ *
      (idealWeight c χ R t (Q * ((Ideal.span {p})^j*I) * ((Ideal.span {p})^(k-j)*J)) *
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂
          ((Ideal.span {p})^j*I) ((Ideal.span {p})^(k-j)*J)) =
      (idealWeight c χ R t ((Ideal.span {p})^k) / primeRoot p k) *
        ((Real.sqrt (T/(Ideal.absNorm (Ideal.span {p}) : ℝ)^k) : ℂ)⁻¹ *
          (idealWeight c χ R t (Q*I*J) *
            idealRectangle W₁ W₂
              (X₁/(Ideal.absNorm (Ideal.span {p}) : ℝ)^j)
              (X₂/(Ideal.absNorm (Ideal.span {p}) : ℝ)^(k-j))
              (Y₁/(Ideal.absNorm (Ideal.span {p}) : ℝ)^j)
              (Y₂/(Ideal.absNorm (Ideal.span {p}) : ℝ)^(k-j)) I J)) := by
  rw [extracted_rectangle_coefficient,centralRoot_extract p hp k T hT]
  have hprod : Q*(Ideal.span {p})^j*(Ideal.span {p})^(k-j) = Q*(Ideal.span {p})^k := by
    rw [mul_assoc,← pow_add,Nat.add_sub_of_le hj]
  rw [hprod]
  simp only [idealWeight_mul,map_pow,Nat.cast_pow]
  ring

theorem centered_product_prime_extract (p : O) (k j : ℕ) (hj : j ≤ k)
    (X₁ X₂ Y₁ Y₂ T : ℝ) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) :
    (X₁/(Ideal.absNorm (Ideal.span {p}) : ℝ)^j) *
      (X₂/(Ideal.absNorm (Ideal.span {p}) : ℝ)^(k-j)) =
        T/(Ideal.absNorm (Ideal.span {p}) : ℝ)^k ∧
    (Y₁/(Ideal.absNorm (Ideal.span {p}) : ℝ)^j) *
      (Y₂/(Ideal.absNorm (Ideal.span {p}) : ℝ)^(k-j)) =
        T/(Ideal.absNorm (Ideal.span {p}) : ℝ)^k := by
  simp only [div_mul_div_comm,← pow_add,Nat.add_sub_of_le hj,hX,hY,and_self]

end CenteredMomentAmplificationRectangle

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

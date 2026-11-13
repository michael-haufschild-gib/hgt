/-
First annular inputs adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.AmplifiedRetainedRadii

/-!
# First annular inputs

Active and error inputs of the first annular stage and the readiness gates; residual columns
of the amplification domain and paid source reserves; existence of amplification families.
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
open scoped Classical BigOperators

namespace CenteredMomentFirstAmplifiedCapacityRadius
open HeckeFamily CanonicalQuadraticSieve CompletedGauss Eisenstein
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstPhysicalSource
open CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstNonexceptionalPrefactor
open CenteredMomentFirstCanonicalFamily CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentFirstScale 
open CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstAmplificationChoice
open CenteredMomentCommonRadiusSaving
local notation "O"=> Eisenstein.O

lemma enlarged_gain_extraction (c d w wo sigma branch delta reserve:ℝ)
    (_hw:0≤ w)(hwo:wo≤2*w):
    -d+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve≤
      -min c d+branch*sigma+delta+reserve := by
  have h:max (d-c-2*w+wo) 0≤ d-min c d:=by
    apply max_le <;> linarith [min_le_left c d,min_le_right c d]
  linarith

theorem actual_reference_shift (η τ:Character)(C D:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(K V Z red w wo cost gain:ℝ)
    (hK:0< K)(hV:0< V)(hZ:1< Z)(hred:0< red)(hcost:0< cost)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D}):
    let c:=Real.logb Z (C.absNorm:ℝ);
    let d:=Real.logb Z (D.absNorm:ℝ);
    let K0:=Real.logb Z (firstNominalScale C D
      (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V);
    Real.logb Z (Z^(K0+gain))-
      Real.logb Z (cost*(τ.modulus.absNorm:ℝ)*Z^wo)-Real.logb Z (V/(red*Z^w))=
      Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        Real.logb Z red-c-d+gain+w-wo-
        Real.logb Z fixedPresentationCost-Real.logb Z cost := by
  have hc:=norm_pos C hC.1
  have hd:=norm_pos D hD.1
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hE:=norm_pos _ (subsetGenerator_supported C D hC E).1
  have hR:=active_norm_pos C D
  have hz:0< Z:=zero_lt_one.trans hZ
  have hh:=actual_reference_width η τ C D hC E K Z hK hZ hmod
  dsimp only
  rw [nominal_equal_support C D _ hC.1 hD.1 hCD K V]
  simp (disch := positivity) only [Real.logb_mul,Real.logb_div,Real.logb_pow,
    Real.logb_rpow hz hZ.ne'] at hh ⊢
  norm_num at hh ⊢
  linarith

theorem actual_main_reference_shift (η τ:Character)(C D:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(K V Z red sigma delta reserve:ℝ)
    (hK:0< K)(hV:0< V)(hZ:1< Z)(hred:0< red)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D}):
    let c:=Real.logb Z (C.absNorm:ℝ);
    let d:=Real.logb Z (D.absNorm:ℝ);
    let K0:=Real.logb Z (firstNominalScale C D
      (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V);
    Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-
      Real.logb Z (τ.modulus.absNorm:ℝ)-Real.logb Z (V/red)≤
      Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        (Real.logb Z red-c)-min c d+2*sigma+delta+reserve-
        Real.logb Z fixedPresentationCost := by
  have hh:=actual_reference_shift η τ C D hC hD hCD E K V Z red 0 0 1
    (max (Real.logb Z (D.absNorm:ℝ)-Real.logb Z (C.absNorm:ℝ)) 0+2*sigma+delta+reserve)
    hK hV hZ hred (by norm_num) hmod
  have hg:=enlarged_gain_extraction (Real.logb Z (C.absNorm:ℝ))
    (Real.logb Z (D.absNorm:ℝ)) 0 0 sigma 2 delta reserve (by norm_num) (by norm_num)
  dsimp only at hh ⊢
  simp only [Real.rpow_zero,mul_one,one_mul,Real.logb_one,add_zero,sub_zero] at hh hg
  change _≤ _
  rw [mainCommonRadius]
  simp only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh ⊢
  norm_num at hg
  linarith

theorem actual_error_reference_shift (η τ:Character)(C D:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(K V Z red sigma delta reserve cost:ℝ)
    (hK:0< K)(hV:0< V)(hZ:1< Z)(hred:0< red)(hcost:0< cost)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D})
    (p:O)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7)(hs:0≤ sigma)
    (hl:sigma/6≤ Real.logb Z (normValue p)):
    let c:=Real.logb Z (C.absNorm:ℝ);
    let d:=Real.logb Z (D.absNorm:ℝ);
    let K0:=Real.logb Z (firstNominalScale C D
      (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V);
    Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p k)-
      Real.logb Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k))-
      Real.logb Z (V/(red*Z^(errorRemoval p Z k)))≤
      Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        (Real.logb Z red-c)-min c d+6*errorRemoval p Z k+delta+reserve-
        Real.logb Z fixedPresentationCost-Real.logb Z cost := by
  have hp:0≤ Real.logb Z (normValue p):=by linarith
  have hw:0≤ errorRemoval p Z k:=by unfold errorRemoval;positivity
  have hwo:errorMoving p Z k≤2*errorRemoval p Z k:=by
    rcases hk with rfl|rfl|rfl <;> simp only [errorMoving,errorRemoval] <;> norm_num <;> linarith
  have he:sigma+errorRemoval p Z k-errorMoving p Z k≤6*errorRemoval p Z k:=by
    rcases hk with rfl|rfl|rfl <;> simp only [errorMoving,errorRemoval] <;> norm_num <;> linarith
  have hh:=actual_reference_shift η τ C D hC hD hCD E K V Z red
    (errorRemoval p Z k) (errorMoving p Z k) cost
    (max (Real.logb Z (D.absNorm:ℝ)-Real.logb Z (C.absNorm:ℝ)-
      2*errorRemoval p Z k+errorMoving p Z k) 0+sigma+delta+reserve)
    hK hV hZ hred hcost hmod
  have hg:=enlarged_gain_extraction (Real.logb Z (C.absNorm:ℝ))
    (Real.logb Z (D.absNorm:ℝ)) (errorRemoval p Z k) (errorMoving p Z k)
    sigma 1 delta reserve hw hwo
  dsimp only at hh ⊢
  simp only [one_mul] at hg
  rw [errorCommonRadius]
  simp only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh ⊢
  linarith

end CenteredMomentFirstAmplifiedCapacityRadius

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstAmplifiedCapacitySource
open HeckeFamily CanonicalQuadraticSieve CompletedGauss  Eisenstein
open CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplifiedCapacityRadius CenteredMomentSecondCapacitySourceShift
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentAmplifiedRetainedRadius
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

theorem frozen_reduction_log (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C)
    (Z:ℝ)(hZ:1< Z)(hne:frozenCoefficient B.val C R s.ν s.W s.P≠0):
    Real.logb Z (rawReduction B.val s.P)-Real.logb Z (C.absNorm:ℝ)≤
      -(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower) := by
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have ha:0< min 1 s.lower:=lt_min zero_lt_one s.lower_pos
  have hh:=(actual_reduction_norm B.val (alloc_ne s C B) C R (allocation_product s C B)
    s.ν s.W s.P s.P_pos s.lower s.upper s.lower_pos s.slot_support hne).1
  have hl:=Real.logb_le_logb_of_le hZ (mul_pos (pow_pos ha _) hr) hh
  rw [Real.logb_mul (pow_pos ha _).ne' hr.ne',Real.logb_pow] at hl
  nlinarith

theorem inherited_affine_parent (s:Input ι)(C _R:Ideal O)(B:actualAllocations s.pools C)
    (Z κ M:ℝ)(hZ:1< Z)(hκ:1/6≤κ)(hP:∀i,1≤ s.P i)
    (hcap:CenteredMomentEnergyBands.length Z s.X₁+
      CenteredMomentEnergyBands.length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤ M):
    Real.logb Z (volume s)+(6*κ-1)*
      (∑i:CenteredMomentCommonProfile.liveIndices B.val,Real.logb Z (s.P i))≤ M := by
  have hp:=CenteredMomentEnergyInputParentCapacity.input_affine_capacity s Z κ M hZ hcap
  have hs:=CenteredMomentAllocatedChildCapacity.common_slot_logs_le s C B Z hZ hP
  have hh:=mul_le_mul_of_nonneg_left hs (by linarith:0≤6*κ-1)
  linarith

theorem actual_main_source_shift (s:Input ι)(τ υ:Character)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(t:ℝ)
    (hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (K Z sigma delta reserve cost a:ℝ)(hK:0< K)(hZ:1< Z)(hcost:0< cost)(ha:0< a)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D})
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)
    (hC₂:Supported C₂)(hD₂:Supported D₂)(hCD₂:primeSupport C₂=primeSupport D₂)
    (U:Finset (CommonIndex C₂ D₂))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hlower:∀I:Ideal O,β I≠0→a*volume (child s C R0 B τ t)≤(I.absNorm:ℝ))
    (hne:physicalBlock υ t S β C₂ D₂ hC₂ hD₂ U R rows W
      (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) n≠0):
    Real.logb Z (volume (child s C R0 B τ t)/(C₂.absNorm:ℝ))-
      Real.logb Z (adjustedEnvelopeRef (cost*(τ.modulus.absNorm:ℝ)) C₂ D₂ U n)≤
      Real.logb Z (volume s)-(Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))+
        2*sigma+delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
        min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
        Real.logb Z fixedPresentationCost-Real.logb Z cost+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2)) := by
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hrad:0< mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume s)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve:=by
    unfold mainCommonRadius;positivity
  have hg:=actual_capacity_shift_reference υ t S β C₂ D₂ hC₂ hD₂ hCD₂ U R rows W _
    (volume (child s C R0 B τ t)) a Z (cost*(τ.modulus.absNorm:ℝ)) n
    (mul_pos hcost hq) hrad (volume_pos _) ha hZ hlower hne
  have hr:=actual_main_reference_shift s.η τ C D hC hD hCD E K (volume s) Z
    (rawReduction B.val s.P) sigma delta reserve hK (volume_pos s) hZ
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) hmod
  have he:=frozen_reduction_log s C R0 B Z hZ hB
  rw [common_volume] at hg
  rw [Real.logb_mul hcost.ne' hq.ne'] at hg
  dsimp only at hr
  rw [common_volume]
  linarith

theorem actual_error_source_shift (s:Input ι)(τ υ:Character)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(t:ℝ)
    (hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (K Z sigma delta reserve cost a:ℝ)(hK:0< K)(hZ:1< Z)(hcost:0< cost)(ha:0< a)
    (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7)(hs:0≤ sigma)
    (hl:sigma/6≤ Real.logb Z (normValue p))
    (hslot:∀i,∀I∈(child s C R0 B τ t).slots i,IsCoprime (Ideal.span {p}) I)
    (Bp:actualAllocations (child s C R0 B τ t).pools ((Ideal.span {p})^k))(v:ℝ)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D})
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)
    (hC₂:Supported C₂)(hD₂:Supported D₂)(hCD₂:primeSupport C₂=primeSupport D₂)
    (U:Finset (CommonIndex C₂ D₂))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hlower:∀I:Ideal O,β I≠0→a*volume (twiceChild s C R0 B τ t (Ideal.span {p}) k Bp υ v)≤(I.absNorm:ℝ))
    (hne:physicalBlock υ v S β C₂ D₂ hC₂ hD₂ U R rows W
      (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k) n≠0):
    Real.logb Z (volume (twiceChild s C R0 B τ t (Ideal.span {p}) k Bp υ v)/(C₂.absNorm:ℝ))-
      Real.logb Z (adjustedEnvelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) C₂ D₂ U n)≤
      Real.logb Z (volume s)-(Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))+
        6*errorRemoval p Z k+delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
        min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
        Real.logb Z fixedPresentationCost-Real.logb Z cost+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2)) := by
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hrad:0< errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume s)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k:=by
    unfold errorCommonRadius;positivity
  have hg:=actual_capacity_shift_reference υ v S β C₂ D₂ hC₂ hD₂ hCD₂ U R rows W _
    (volume (twiceChild s C R0 B τ t (Ideal.span {p}) k Bp υ v)) a Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) n
    (by positivity) hrad (volume_pos _) ha hZ hlower hne
  have hr:=actual_error_reference_shift s.η τ C D hC hD hCD E K (volume s) Z
    (rawReduction B.val s.P) sigma delta reserve cost hK (volume_pos s) hZ
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) hcost hmod p k hk hs hl
  have he:=frozen_reduction_log s C R0 B Z hZ hB
  have hQ:(Ideal.span {p})≠(0:Ideal O):=Ideal.span_singleton_eq_bot.not.mpr hp
  have hv:=twice_volume s C R0 B τ t (Ideal.span {p}) hQ k hslot Bp υ v
  have hn:(Ideal.absNorm (Ideal.span {p}):ℝ)=normValue p:=by
    simp only [normValue]
  rw [hn] at hv
  rw [hv] at hg ⊢
  dsimp only at hr
  rw [errorRemoval_power p hp Z hZ k] at hr
  linarith

end CenteredMomentFirstAmplifiedCapacitySource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace CenteredMomentFirstAnnularInput
open HeckeFamily CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalChildEnergy CenteredMomentSecondHeightFamily
open CenteredMomentHeckeColumnWindow CenteredMomentGaussNormalization
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentCommonAllocationSum

variable {ι:Type*}[Fintype ι]

theorem normalized_input_coefficient (s:Input ι)(R seed:Ideal Eisenstein.O)
    (W:𝓢(ℝ,ℂ))(H:ℝ):
    (gaussEnergy Finset.univ (sourceGenerator (original s R seed).columns)
      (sourceGenerator_supported (original s R seed).columns)
      ((original s R seed).coefficient s.η fixedBadMask s.t (volume s)) W H).re=
      normalizedGaussSource s R seed W H:=by
  unfold OriginalData.coefficient normalizedGaussSource sourceGaussEnergy
  rw [show (fun I:supportedColumns (original s R seed).columns=>
      (Real.sqrt (volume s):ℂ)⁻¹*((original s R seed).beta I*
        CenteredMomentHeckeExpansion.rowWeight s.η fixedBadMask 1 1 s.t I))=
      (fun I:supportedColumns (original s R seed).columns=>(Real.sqrt (volume s):ℂ)⁻¹*
        ((original s R seed).beta I*heightCoeff s.η s.t I)) by
    funext I
    rw [←heightCoeff_eq_fixed_rowWeight s.η s.t I (Finset.mem_filter.mp I.property).2]]
  exact gaussEnergy_central _ _ _ _ (volume s) (volume_pos s) W H

theorem normalized_child_coefficient (s:Input ι)(C R seed:Ideal Eisenstein.O)
    (B:actualAllocations s.pools C)(τ:Character)(t:ℝ)(W:𝓢(ℝ,ℂ))(H:ℝ):
    (gaussEnergy Finset.univ (sourceGenerator (original (child s C R B τ t) (R*C) seed).columns)
      (sourceGenerator_supported (original (child s C R B τ t) (R*C) seed).columns)
      ((original (child s C R B τ t) (R*C) seed).coefficient τ fixedBadMask t
        (volume (child s C R B τ t))) W H).re=
      childNormalizedGaussSource s C R seed B τ t W H:=
  normalized_input_coefficient (child s C R B τ t) (R*C) seed W H

end CenteredMomentFirstAnnularInput

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace CenteredMomentFirstAnnularInput
open HeckeFamily CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentCommonRadialData CenteredMomentSecondHeightFamily

variable {ι:Type*}[Fintype ι]

def activeInput (s:Input ι):Input ι:={s with
  slots:=fun i=>(s.slots i).filter (fun I=> s.W i ((I.absNorm:ℝ)/s.P i)≠0)
  prime:=fun i I hI=> s.prime i I (Finset.mem_filter.mp hI).1
  coefficient_bound:=fun i I hI=> s.coefficient_bound i I (Finset.mem_filter.mp hI).1}

lemma original_active (s:Input ι)(R seed:Ideal Eisenstein.O):
    original (activeInput s) R seed=(original s R seed).active:=by
  unfold original OriginalData.active
  congr 1
  funext j
  cases j <;> rfl

lemma active_volume (s:Input ι):volume (activeInput s)=volume s:=rfl

lemma active_normalized (s:Input ι)(R seed:Ideal Eisenstein.O)(W:𝓢(ℝ,ℂ))(H:ℝ):
    normalizedGaussSource (activeInput s) R seed W H=normalizedGaussSource s R seed W H:=by
  rw [←normalized_input_coefficient,←normalized_input_coefficient,original_active]
  exact congrArg Complex.re ((original s R seed).active_gaussEnergy s.η fixedBadMask s.t (volume s) W H)

end CenteredMomentFirstAnnularInput

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstChildLower
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonExceptionalGates CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

theorem child_lower (s:Input ι)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t Z r:ℝ)(hZ:1< Z)
    (hX₁:Z^r≤ s.X₁)(hX₂:Z^r≤ s.X₂)(hY₁:Z^r≤ s.Y₁)(hY₂:Z^r≤ s.Y₂):
    let d:=child s C R B τ t
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤ d.X₁ ∧
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤ d.X₂ ∧
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤ d.Y₁ ∧
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤ d.Y₂:=by
  exact ⟨extracted_lower s C hC B (Sum.inr 0) Z r s.X₁ hZ hX₁,
    extracted_lower s C hC B (Sum.inr 1) Z r s.X₂ hZ hX₂,
    extracted_lower s C hC B (Sum.inr 0) Z r s.Y₁ hZ hY₁,
    extracted_lower s C hC B (Sum.inr 1) Z r s.Y₂ hZ hY₂⟩

theorem twice_lower (s:Input ι)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t:ℝ)
    (Q:Ideal O)(hQ:Q≠0)(k:ℕ)
    (Bp:actualAllocations (child s C R B τ t).pools (Q^k))
    (υ:Character)(v Z r:ℝ)(hZ:1< Z)
    (hX₁:Z^r≤ s.X₁)(hX₂:Z^r≤ s.X₂)(hY₁:Z^r≤ s.Y₁)(hY₂:Z^r≤ s.Y₂):
    let d:=twiceChild s C R B τ t Q k Bp υ v
    let r':=r-Real.logb Z (C.absNorm:ℝ)-(k:ℝ)*Real.logb Z (Q.absNorm:ℝ)
    Z^r'≤ d.X₁ ∧ Z^r'≤ d.X₂ ∧ Z^r'≤ d.Y₁ ∧ Z^r'≤ d.Y₂:=by
  have hc:=child_lower s C R hC B τ t Z r hZ hX₁ hX₂ hY₁ hY₂
  have hp:=child_lower (child s C R B τ t) (Q^k) (R*C) (pow_ne_zero k hQ)
    Bp υ v Z (r-Real.logb Z (C.absNorm:ℝ)) hZ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  have hnorm:(Q.absNorm:ℝ)>0:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hQ)
  have he:Real.logb Z ((Q^k).absNorm:ℝ)=(k:ℝ)*Real.logb Z (Q.absNorm:ℝ):=by
    rw [map_pow,Nat.cast_pow,Real.logb_pow]
  simpa only [he,twiceChild] using hp

theorem removed_width_cap (L c w:ℝ):
    (2/3:ℝ)*(c+w)+(2/3:ℝ)*max (L-c-w) 0≥(2/3:ℝ)*L:=by
  have h:=le_max_left (L-c-w) 0
  linarith

theorem paired_removed_width_cap (L c₁ w₁ c₂ w₂:ℝ):
    ((c₁+w₁)+(c₂+w₂))/3+
      (max (L-c₁-w₁) 0+max (L-c₂-w₂) 0)/3≥(2/3:ℝ)*L:=by
  have h₁:=le_max_left (L-c₁-w₁) 0
  have h₂:=le_max_left (L-c₂-w₂) 0
  linarith

end CenteredMomentFirstChildLower

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentFirstSecondInputGates
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonAllocationSum CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy
open CenteredMomentSectorLocalization
local notation "O"=> Eisenstein.O
local instance {α:Type*}:DecidableEq α:=Classical.decEq _

structure Ready {ι:Type*}[Fintype ι](s:Input ι)(R:Ideal O)(K Z ξ B:ℝ):Prop where
  puncture_ne : R≠0
  scale_pos : 0< K
  volume_cap : volume s≤ Z^B
  source_nonneg : 0≤ sourceRadius s
  source_cap : sourceRadius s≤ Z^B
  conductor_cap : (s.η.modulus.absNorm:ℝ)≤ Z^B
  puncture_cap : (R.absNorm:ℝ)≤ Z^B
  nominal_pos : 0< nominal s K
  nominal_cap : nominal s K≤ Z^B
  frequency_pos : 0< frequencyRadius (nominal s K) Z ξ
  frequency_cap : frequencyRadius (nominal s K) Z ξ≤ Z^B

theorem normalized_zero {ι:Type*}[Fintype ι](s:Input ι)(R seed:Ideal O)
    (hz:∀I:Ideal O,(original s R seed).beta I=0)(W:𝓢(ℝ,ℂ))(K:ℝ):
    normalizedGaussSource s R seed W K=0:=by
  simp [normalizedGaussSource,sourceGaussEnergy,gaussEnergy,gaussPolynomial,hz]

theorem eventually_twice_ready (N:ℕ)(b b₁ b₂ ε:ℝ)
    (hb:1≤ b)(hb₁:1≤ b₁)(hb₂:1≤ b₂)(hε:0<ε):
    ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤ N → Endpoints b b₁ b₂ s →
    ∀(C R seed:Ideal O)(B:actualAllocations s.pools C)(τ:Character)(t:ℝ),
    R≠0 → frozenCoefficient B.val C R s.ν s.W s.P≠0 →
    ∀(Q:Ideal O),Q≠0 → ∀k:ℕ,
    (∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I)→
    ∀(Bp:actualAllocations (child s C R B τ t).pools (Q^k))(υ:Character)(v K A D P q ξ:ℝ),
    0< K → 0≤ξ → s.W₁ 0=0 → s.W₂ 0=0 →
    volume s≤ Z^A → K⁻¹≤ Z^D → (R.absNorm:ℝ)≤ Z^P → (υ.modulus.absNorm:ℝ)≤ Z^q →
    (∃I:Ideal O,(original (twiceChild s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed).beta I≠0)→
    Ready (twiceChild s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) K Z ξ (exponent A D P q ε ξ):=by
  filter_upwards [eventual_twice_caps N b b₁ b₂ ε hb hb₁ hb₂ hε,
    eventual_live_puncture N b b₁ b₂ ε hb hb₁ hb₂ hε] with Z hc hp
  refine ⟨hc.1,?_⟩
  intro ι _ s hs he C R seed B τ t hR hB Q hQ k hslot Bp υ v K A D P q ξ
    hK hξ hz₁ hz₂ hV hKi hRN hυ hlive
  have hh:=hc.2 s hs he C R B τ t hB Q hQ k hslot Bp υ v K A D ξ hK hV hKi
  have hr:=hp.2 s hs he C R seed B τ t hB Q hQ k hslot Bp υ v A P hz₁ hz₂ hV hRN hlive
  have h₁:A+ε≤ exponent A D P q ε ξ:=le_max_left _ _
  have h₂:2*A+D+ε+ξ/2≤ exponent A D P q ε ξ:=
    (le_max_left _ _).trans (le_max_right _ _)
  have h₃:A+P+ε≤ exponent A D P q ε ξ:=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h₄:q≤ exponent A D P q ε ξ:=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hpow {x y:ℝ}(h:x≤ y):Z^x≤ Z^y:=Real.rpow_le_rpow_of_exponent_le hc.1.le h
  refine ⟨mul_ne_zero (mul_ne_zero hR (allocation_ne s C B)) (pow_ne_zero k hQ),hK,
    hh.1.trans (hpow h₁),hh.2.1,hh.2.2.1.trans (hpow h₁),
    hυ.trans (hpow h₄),hr.trans (hpow h₃),hh.2.2.2.1,
    hh.2.2.2.2.1.trans (hpow ((by linarith : 2*A+D+ε≤2*A+D+ε+ξ/2).trans h₂)),
    hh.2.2.2.2.2.1,hh.2.2.2.2.2.2.trans (hpow h₂)⟩

end CenteredMomentFirstSecondInputGates

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentFirstSecondActiveErrorGates
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentFirstSecondInputGates CenteredMomentFirstAnnularInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentSectorLocalization
local notation "O" => Eisenstein.O
local instance {α : Type*} : DecidableEq α := Classical.decEq _
variable {ι : Type*} [Fintype ι]

def errorInput (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) : Input (liveIndices Bp.val) :=
  child (activeInput (child s C R B τ t)) (Q^k) (R*C) Bp υ v

lemma active_endpoints (s : Input ι) (b b₁ b₂ : ℝ) (he : Endpoints b b₁ b₂ s) :
    Endpoints b b₁ b₂ (activeInput s) := he

theorem error_caps (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤ b) (h₁ : 1≤ b₁) (h₂ : 1≤ b₂)
    (s : Input ι) (hc : Fintype.card ι≤ N) (he : Endpoints b b₁ b₂ s)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    let d := errorInput s C R B τ t Q k Bp υ v;
    let H := volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k);
    0< H ∧ 0≤ sourceRadius d ∧ volume d≤ geometry N b b₁ b₂*H ∧
      sourceRadius d≤ geometry N b b₁ b₂*H := by
  dsimp only
  have hC := norm_ge_one C (allocation_ne s C B)
  have hNp : 0<(Q.absNorm:ℝ)^k := pow_pos (zero_lt_one.trans_le (norm_ge_one Q hQ)) k
  have hH : 0< volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k) :=
    div_pos (volume_pos s) (mul_pos (zero_lt_one.trans_le hC) hNp)
  have hv : volume (errorInput s C R B τ t Q k Bp υ v)≤
      b^N*(volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)) := by
    rw [errorInput,child_volume _ Q hQ k hslot,active_volume]
    exact (div_le_div_of_nonneg_right (common_volume_le N b hb s hc he.1 C R B τ t hne)
      hNp.le).trans_eq (by ring)
  have hc1 := (live_card_le B.val).trans hc
  have hc2 := (live_card_le Bp.val).trans hc1
  have hep := endpoints_child b b₁ b₂ _
    (active_endpoints _ b b₁ b₂ (endpoints_child b b₁ b₂ s he C R B τ t))
    (Q^k) (R*C) Bp υ v
  have hr := radius_bound N b b₁ b₂ hb h₁ h₂ _ hc2 hep
  have hpow : b^N≤ geometry N b b₁ b₂ := by
    have hp : 1≤ b^N := one_le_pow₀ hb
    unfold geometry
    rw [show 2*N=N+N by omega,pow_add]
    have hh : 1≤ b₁*b₂ := by nlinarith
    nlinarith
  refine ⟨hH,hr.1,hv.trans (mul_le_mul_of_nonneg_right hpow hH.le),?_⟩
  exact hr.2.trans ((mul_le_mul_of_nonneg_left hv (show 0≤ b^N*b₁*b₂ by positivity)).trans_eq (by
    unfold geometry;rw [show 2*N=N+N by omega,pow_add];ring))

theorem eventually_active_error_ready (N : ℕ) (b b₁ b₂ ε : ℝ)
    (hb : 1≤ b) (h₁ : 1≤ b₁) (h₂ : 1≤ b₂) (hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀{ι : Type*}[Fintype ι],∀s : Input ι,
    Fintype.card ι≤ N → Endpoints b b₁ b₂ s →
    ∀(C R seed : Ideal O)(B : actualAllocations s.pools C)(τ : Character)(t : ℝ),
    R≠0 → frozenCoefficient B.val C R s.ν s.W s.P≠0 →
    ∀(Q : Ideal O),Q≠0 → ∀k : ℕ,
    (∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I) →
    ∀(Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
      (υ : Character)(v K A D P q ξ : ℝ),
    0< K → 0≤ξ → s.W₁ 0=0 → s.W₂ 0=0 →
    volume s≤ Z^A → K⁻¹≤ Z^D → (R.absNorm:ℝ)≤ Z^P → (υ.modulus.absNorm:ℝ)≤ Z^q →
    (∃I : Ideal O,(original (errorInput s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed).beta I≠0) →
    Ready (errorInput s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) K Z ξ
      (exponent A D P q ε ξ) := by
  filter_upwards [eventual_geometry (geometry N b b₁ b₂) ε
    (geometry_ge_one N b b₁ b₂ hb h₁ h₂) hε] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ s hc he C R seed B τ t hR hB Q hQ k hslot Bp υ v K A D P q ξ
    hK hξ hz₁ hz₂ hVp hKi hRN hυ hlive
  let d := errorInput s C R B τ t Q k Bp υ v
  let G := geometry N b b₁ b₂
  have hg : 1≤ G := geometry_ge_one N b b₁ b₂ hb h₁ h₂
  have hcap := error_caps N b b₁ b₂ hb h₁ h₂ s hc he C R B τ t hB Q hQ k hslot Bp υ v
  have hd : 0<(C.absNorm:ℝ)*(Q.absNorm:ℝ)^k := mul_pos
    (zero_lt_one.trans_le (norm_ge_one C (allocation_ne s C B)))
    (pow_pos (zero_lt_one.trans_le (norm_ge_one Q hQ)) k)
  have hd1 : 1≤(C.absNorm:ℝ)*(Q.absNorm:ℝ)^k := by
    have hc := norm_ge_one C (allocation_ne s C B)
    have hq : 1 ≤ (Q.absNorm : ℝ)^k := one_le_pow₀ (norm_ge_one Q hQ)
    nlinarith
  have hHV : volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)≤ volume s :=
    div_le_self (volume_pos s).le hd1
  have hm := mul_le_mul_of_nonneg_left hHV (zero_le_one.trans hg)
  have hpoly := polynomial_caps G (volume s) (volume d) (sourceRadius d) K Z A D ε ξ
    hg hZ.1 hZ.2.2 (volume_pos s) (volume_pos d) hcap.2.1 hK
    (hcap.2.2.1.trans hm) (hcap.2.2.2.trans hm) hVp hKi
  obtain ⟨I,hI⟩ := hlive
  have hi := child_column_norm (activeInput (child s C R B τ t)) (Q^k) (R*C) seed Bp υ v hz₁ hz₂ I hI
  have hone : 1≤ G*(volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)) :=
    (norm_ge_one I hi.1).trans (hi.2.2.trans hcap.2.2.2)
  rw [←mul_div_assoc] at hone
  have hprod : (C.absNorm:ℝ)*(Q.absNorm:ℝ)^k≤ G*volume s := by
    simpa only [one_mul] using (le_div_iff₀ hd).mp hone
  have hpunct : (((R*C)*(Q^k)).absNorm:ℝ)≤ Z^(A+P+ε) := by
    rw [puncture_norm]
    calc
      _≤(R.absNorm:ℝ)*(G*volume s) := by nlinarith [mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg R.absNorm)]
      _≤ Z^P*(Z^ε*Z^A) := mul_le_mul hRN
        (mul_le_mul hZ.2.1 hVp (volume_pos s).le (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _))
        (mul_nonneg (zero_le_one.trans hg) (volume_pos s).le)
        (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
      _=Z^(A+P+ε) := by rw [←Real.rpow_add (zero_lt_one.trans hZ.1),←Real.rpow_add (zero_lt_one.trans hZ.1)];congr 1;ring
  have h₁ : A+ε≤ exponent A D P q ε ξ := le_max_left _ _
  have h₂ : 2*A+D+ε+ξ/2≤ exponent A D P q ε ξ :=
    (le_max_left _ _).trans (le_max_right _ _)
  have h₃ : A+P+ε≤ exponent A D P q ε ξ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h₄ : q≤ exponent A D P q ε ξ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hpow {x y : ℝ} (h : x≤ y) : Z^x≤ Z^y := Real.rpow_le_rpow_of_exponent_le hZ.1.le h
  exact ⟨mul_ne_zero (mul_ne_zero hR (allocation_ne s C B)) (pow_ne_zero k hQ),hK,
    hpoly.1.trans (hpow h₁),hcap.2.1,hpoly.2.1.trans (hpow h₁),
    hυ.trans (hpow h₄),hpunct.trans (hpow h₃),nominal_pos d K hK,
    hpoly.2.2.1.trans (hpow ((by linarith : 2*A+D+ε≤2*A+D+ε+ξ/2).trans h₂)),
    hpoly.2.2.2.1,hpoly.2.2.2.2.trans (hpow h₂)⟩

end CenteredMomentFirstSecondActiveErrorGates

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstAmplifiedActiveCapacitySource
open HeckeFamily CanonicalQuadraticSieve CompletedGauss  Eisenstein
open CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplifiedCapacityRadius CenteredMomentSecondCapacitySourceShift
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentAmplifiedRetainedRadius
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

open CenteredMomentFirstAmplifiedCapacitySource CenteredMomentFirstSecondActiveErrorGates
open CenteredMomentFirstAnnularInput

theorem active_error_volume (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    volume (errorInput s C R B τ t Q k Bp υ v)=
      volume s/(rawReduction B.val s.P*(Q.absNorm:ℝ)^k) := by
  rw [errorInput,child_volume _ Q hQ k hslot,active_volume,common_volume]
  ring

theorem actual_active_error_source_shift (s:Input ι)(τ υ:Character)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(t:ℝ)
    (hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (K Z sigma delta reserve cost a:ℝ)(hK:0< K)(hZ:1< Z)(hcost:0< cost)(ha:0< a)
    (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7)(hs:0≤ sigma)
    (hl:sigma/6≤ Real.logb Z (normValue p))
    (hslot:∀i,∀I∈(activeInput (child s C R0 B τ t)).slots i,IsCoprime (Ideal.span {p}) I)
    (Bp:actualAllocations (activeInput (child s C R0 B τ t)).pools ((Ideal.span {p})^k))(v:ℝ)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D})
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)
    (hC₂:Supported C₂)(hD₂:Supported D₂)(hCD₂:primeSupport C₂=primeSupport D₂)
    (U:Finset (CommonIndex C₂ D₂))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hlower:∀I:Ideal O,β I≠0→a*volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v)≤(I.absNorm:ℝ))
    (hne:physicalBlock υ v S β C₂ D₂ hC₂ hD₂ U R rows W
      (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k) n≠0):
    Real.logb Z (volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v)/(C₂.absNorm:ℝ))-
      Real.logb Z (adjustedEnvelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) C₂ D₂ U n)≤
      Real.logb Z (volume s)-(Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))+
        6*errorRemoval p Z k+delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
        min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
        Real.logb Z fixedPresentationCost-Real.logb Z cost+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2)) := by
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hrad:0< errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume s)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k:=by
    unfold errorCommonRadius;positivity
  have hg:=actual_capacity_shift_reference υ v S β C₂ D₂ hC₂ hD₂ hCD₂ U R rows W _
    (volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v)) a Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) n
    (by positivity) hrad (volume_pos _) ha hZ hlower hne
  have hr:=actual_error_reference_shift s.η τ C D hC hD hCD E K (volume s) Z
    (rawReduction B.val s.P) sigma delta reserve cost hK (volume_pos s) hZ
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) hcost hmod p k hk hs hl
  have he:=frozen_reduction_log s C R0 B Z hZ hB
  have hQ:(Ideal.span {p})≠(0:Ideal O):=Ideal.span_singleton_eq_bot.not.mpr hp
  have hv:=active_error_volume s C R0 B τ t (Ideal.span {p}) hQ k hslot Bp υ v
  have hn:(Ideal.absNorm (Ideal.span {p}):ℝ)=normValue p:=by
    simp only [normValue]
  rw [hn] at hv
  rw [hv] at hg ⊢
  dsimp only at hr
  rw [errorRemoval_power p hp Z hZ k] at hr
  linarith

theorem actual_active_error_source_shift_right (s:Input ι)(τ υ:Character)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(t:ℝ)
    (hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (K Z sigma delta reserve cost a:ℝ)(hK:0< K)(hZ:1< Z)(hcost:0< cost)(ha:0< a)
    (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7)(hs:0≤ sigma)
    (hl:sigma/6≤ Real.logb Z (normValue p))
    (hslot:∀i,∀I∈(activeInput (child s C R0 B τ t)).slots i,IsCoprime (Ideal.span {p}) I)
    (Bp:actualAllocations (activeInput (child s C R0 B τ t)).pools ((Ideal.span {p})^k))(v:ℝ)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D})
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)
    (hC₂:Supported C₂)(hD₂:Supported D₂)(hCD₂:primeSupport C₂=primeSupport D₂)
    (U:Finset (CommonIndex C₂ D₂))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hlower:∀I:Ideal O,β I≠0→a*volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v)≤(I.absNorm:ℝ))
    (hne:physicalBlock υ v S β C₂ D₂ hC₂ hD₂ U R rows W
      (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k) n≠0):
    Real.logb Z (volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v)/(D₂.absNorm:ℝ))-
      Real.logb Z (adjustedEnvelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) C₂ D₂ U n)≤
      Real.logb Z (volume s)-(Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))+
        6*errorRemoval p Z k+delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
        min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
        Real.logb Z fixedPresentationCost-Real.logb Z cost+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2)) := by
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hrad:0< errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume s)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k:=by
    unfold errorCommonRadius;positivity
  have hg:=actual_capacity_shift_reference_right υ v S β C₂ D₂ hC₂ hD₂ hCD₂ U R rows W _
    (volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v)) a Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) n
    (by positivity) hrad (volume_pos _) ha hZ hlower hne
  have hr:=actual_error_reference_shift s.η τ C D hC hD hCD E K (volume s) Z
    (rawReduction B.val s.P) sigma delta reserve cost hK (volume_pos s) hZ
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) hcost hmod p k hk hs hl
  have he:=frozen_reduction_log s C R0 B Z hZ hB
  have hQ:(Ideal.span {p})≠(0:Ideal O):=Ideal.span_singleton_eq_bot.not.mpr hp
  have hv:=active_error_volume s C R0 B τ t (Ideal.span {p}) hQ k hslot Bp υ v
  have hn:(Ideal.absNorm (Ideal.span {p}):ℝ)=normValue p:=by
    simp only [normValue]
  rw [hn] at hv
  rw [hv] at hg ⊢
  dsimp only at hr
  rw [errorRemoval_power p hp Z hZ k] at hr
  linarith

end CenteredMomentFirstAmplifiedActiveCapacitySource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstAmplifiedActiveAffine
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentFirstAnnularInput CenteredMomentFirstSecondActiveErrorGates
open CenteredMomentFirstAmplifiedActiveCapacitySource CenteredMomentAllocatedChildCapacity
open CenteredMomentEnergyInputParentCapacity CenteredMomentEnergyBands
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

theorem active_error_slot_logs_le (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v Z : ℝ) (hZ : 1< Z) (hP : ∀i,1≤ s.P i) :
    (∑i,Real.logb Z ((errorInput s C R B τ t Q k Bp υ v).P i))≤
      ∑i,Real.logb Z (s.P i) := by
  have hp : ∀i,1≤(activeInput (child s C R B τ t)).P i := fun i=> hP i.val
  have hs := common_slot_logs_le (activeInput (child s C R B τ t)) (Q^k) Bp Z hZ hp
  exact hs.trans (common_slot_logs_le s C B Z hZ hP)

theorem active_error_parent_affine (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v Z κ M : ℝ) (hZ : 1< Z) (hκ : 1/6≤κ) (hP : ∀i,1≤ s.P i)
    (hcap : length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤ M) :
    Real.logb Z (volume s)+(6*κ-1)*
      (∑i,Real.logb Z ((errorInput s C R B τ t Q k Bp υ v).P i))≤ M := by
  have hh := input_affine_capacity s Z κ M hZ hcap
  have hs := active_error_slot_logs_le s C R B τ t Q k Bp υ v Z hZ hP
  have hm := mul_le_mul_of_nonneg_left hs (by linarith : 0≤6*κ-1)
  linarith

theorem active_error_raw_affine (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v Z κ M : ℝ) (hZ : 1< Z) (hκ : 1/6≤κ) (hP : ∀i,1≤ s.P i)
    (hcap : length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤ M) :
    Real.logb Z (volume (errorInput s C R B τ t Q k Bp υ v))+(6*κ-1)*
      (∑i,Real.logb Z ((errorInput s C R B τ t Q k Bp υ v).P i))≤
      M-Real.logb Z (rawReduction B.val s.P)-(k:ℝ)*Real.logb Z (Q.absNorm:ℝ) := by
  have hh := active_error_parent_affine s C R B τ t Q k Bp υ v Z κ M hZ hκ hP hcap
  have hr := rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have hq : 0<(Q.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hQ)
  rw [active_error_volume s C R B τ t Q hQ k hslot Bp υ v,
    Real.logb_div (volume_pos s).ne' (mul_pos hr (pow_pos hq k)).ne',
    Real.logb_mul hr.ne' (pow_pos hq k).ne',Real.logb_pow]
  linarith

end CenteredMomentFirstAmplifiedActiveAffine

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstAmplifiedPaidAdmission
open HeckeFamily CanonicalQuadraticSieve CompletedGauss  Eisenstein
open CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplifiedCapacityRadius CenteredMomentSecondCapacitySourceShift
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentAmplifiedRetainedRadius
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

open CenteredMomentFirstAmplifiedCapacityCommon CenteredMomentFirstAmplifiedCapacitySource
open CenteredMomentFirstAmplifiedActiveAffine CenteredMomentFirstAmplifiedActiveCapacitySource
open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedChildCapacity

def sourceReserve {α:Type*}[Fintype α] (s:Input ι)(childInput:Input α)
    (C D:Ideal O)(Z delta reserve cost a:ℝ):ℝ :=
  max (delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
    min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
    Real.logb Z fixedPresentationCost-Real.logb Z cost+
    Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
    (Fintype.card α:ℝ)*Real.logb Z (max 1 childInput.upper)) 0

lemma sourceReserve_nonneg {α:Type*}[Fintype α] (s:Input ι)(childInput:Input α)
    (C D:Ideal O)(Z delta reserve cost a:ℝ):0≤ sourceReserve s childInput C D Z delta reserve cost a :=
  le_max_right _ _

lemma common_affine (s:Input ι)(C:Ideal O)(B:actualAllocations s.pools C)
    (Z κ A M:ℝ)(hZ:1< Z)(hκ:1/6≤κ)(hP:∀i,1≤ s.P i)
    (hp:A+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤ M):
    A+(6*κ-1)*(∑i:liveIndices B.val,Real.logb Z (s.P i.val))≤ M := by
  have hs:=common_slot_logs_le s C B Z hZ hP
  have hm:=mul_le_mul_of_nonneg_left hs (by linarith:0≤6*κ-1)
  linarith

theorem actual_main_admission (s:Input ι)(τ υ:Character)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(t:ℝ)
    (hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (K Z sigma delta reserve cost a:ℝ)(hK:0< K)(hZ:1< Z)(hcost:0< cost)(ha:0< a)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D})
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)
    (hC₂:Supported C₂)(hD₂:Supported D₂)(hCD₂:primeSupport C₂=primeSupport D₂)
    (U:Finset (CommonIndex C₂ D₂))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hlower:∀I:Ideal O,β I≠0→a*volume (child s C R0 B τ t)≤(I.absNorm:ℝ))
    (hne:physicalBlock υ t S β C₂ D₂ hC₂ hD₂ U R rows W
      (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) n≠0)
    (Cpick Rpick:Ideal O)(hside:Cpick=C₂ ∨ Cpick=D₂)
    (B₂:actualAllocations (child s C R0 B τ t).pools Cpick)
    (hB₂:frozenCoefficient B₂.val Cpick Rpick (child s C R0 B τ t).ν (child s C R0 B τ t).W (child s C R0 B τ t).P≠0)
    (κ Mdecl:ℝ)(hκ:1/6≤κ)(hP:∀i,1≤ s.P i)
    (hcap:CenteredMomentEnergyBands.length Z s.X₁+
      CenteredMomentEnergyBands.length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤ Mdecl)
    (hM:Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ)≤ Mdecl):
    let input:=child s C R0 B τ t;
    let delta1:=Mdecl-(Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))+
      sourceReserve s input C D Z delta reserve cost a;
    0≤ delta1 ∧
    Real.logb Z (volume s)+(6*κ-1)*(∑i:liveIndices B₂.val,Real.logb Z (input.P i.val))≤ Mdecl ∧
    Real.logb Z (preVolume (commonData (withHeight input υ t) Cpick Rpick B₂))-
      Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)) C₂ D₂ U n)≤
      Real.logb Z (volume s)-Mdecl+6*(sigma/3)+delta1+Real.logb Z (ratioPenalty n) := by
  dsimp only
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hqref:0< cost*(τ.modulus.absNorm:ℝ):=mul_pos hcost hq
  have hf:=inherited_affine_parent s C R0 B Z κ Mdecl hZ hκ hP hcap
  have hPchild:∀i,1≤(child s C R0 B τ t).P i:=fun i=> hP i.val
  have hparent:=common_affine (child s C R0 B τ t) Cpick B₂ Z κ (Real.logb Z (volume s)) Mdecl hZ hκ hPchild hf
  have hr:=actual_main_reference_shift s.η τ C D hC hD hCD E K (volume s) Z
    (rawReduction B.val s.P) sigma delta reserve hK (volume_pos s) hZ
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) hmod
  have he:=frozen_reduction_log s C R0 B Z hZ hB
  have hrad:0< mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume s)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve:=by
    unfold mainCommonRadius;positivity
  have hg:
    Real.logb Z (preVolume (commonData (withHeight (child s C R0 B τ t) υ t) Cpick Rpick B₂))-
      Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)) C₂ D₂ U n)≤
      Real.logb Z (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)-Real.logb Z (cost*(τ.modulus.absNorm:ℝ))-
      Real.logb Z (volume (child s C R0 B τ t))+Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
      (Fintype.card (liveIndices B.val):ℝ)*Real.logb Z (max 1 (child s C R0 B τ t).upper)+
      Real.logb Z (ratioPenalty n) := by
    rcases hside with hside|hside
    · subst Cpick
      exact common_raw_reference_shift (child s C R0 B τ t) υ t S β C₂ D₂ Rpick hC₂ hD₂ hCD₂
        B₂ hB₂ U R rows W _ a Z (cost*(τ.modulus.absNorm:ℝ)) n hqref hrad ha hZ hlower hne
    · subst Cpick
      exact common_raw_reference_shift_right (child s C R0 B τ t) υ t S β C₂ D₂ Rpick hC₂ hD₂ hCD₂
        B₂ hB₂ U R rows W _ a Z (cost*(τ.modulus.absNorm:ℝ)) n hqref hrad ha hZ hlower hne
  rw [common_volume,Real.logb_mul hcost.ne' hq.ne'] at hg
  dsimp only at hr
  have hres:=le_max_left
    (delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
      min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
      Real.logb Z fixedPresentationCost-Real.logb Z cost+
      Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
      (Fintype.card (liveIndices B.val):ℝ)*Real.logb Z (max 1 (child s C R0 B τ t).upper)) 0
  refine ⟨add_nonneg (sub_nonneg.mpr hM) (sourceReserve_nonneg _ _ _ _ _ _ _ _ _),hparent,?_⟩
  unfold sourceReserve
  linarith

theorem actual_active_error_admission (s:Input ι)(τ υ:Character)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(t:ℝ)
    (hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (K Z sigma delta reserve cost a:ℝ)(hK:0< K)(hZ:1< Z)(hcost:0< cost)(ha:0< a)
    (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7)(hs:0≤ sigma)
    (hl:sigma/6≤ Real.logb Z (normValue p))
    (hslot:∀i,∀I∈(activeInput (child s C R0 B τ t)).slots i,IsCoprime (Ideal.span {p}) I)
    (Bp:actualAllocations (activeInput (child s C R0 B τ t)).pools ((Ideal.span {p})^k))(v:ℝ)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D})
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)
    (hC₂:Supported C₂)(hD₂:Supported D₂)(hCD₂:primeSupport C₂=primeSupport D₂)
    (U:Finset (CommonIndex C₂ D₂))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hlower:∀I:Ideal O,β I≠0→a*volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v)≤(I.absNorm:ℝ))
    (hne:physicalBlock υ v S β C₂ D₂ hC₂ hD₂ U R rows W
      (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k) n≠0)
    (Cpick Rpick:Ideal O)(hside:Cpick=C₂ ∨ Cpick=D₂)
    (B₂:actualAllocations (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).pools Cpick)
    (hB₂:frozenCoefficient B₂.val Cpick Rpick (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).ν (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).W (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).P≠0)
    (κ Mdecl:ℝ)(hκ:1/6≤κ)(hP:∀i,1≤ s.P i)
    (hcap:CenteredMomentEnergyBands.length Z s.X₁+
      CenteredMomentEnergyBands.length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤ Mdecl)
    (hM:Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ)≤ Mdecl):
    let input:=errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v;
    let delta1:=Mdecl-(Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))+
      sourceReserve s input C D Z delta reserve cost a;
    0≤ delta1 ∧
    Real.logb Z (volume s)+(6*κ-1)*(∑i:liveIndices B₂.val,Real.logb Z (input.P i.val))≤ Mdecl ∧
    Real.logb Z (preVolume (commonData (withHeight input υ v) Cpick Rpick B₂))-
      Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) C₂ D₂ U n)≤
      Real.logb Z (volume s)-Mdecl+6*errorRemoval p Z k+delta1+Real.logb Z (ratioPenalty n) := by
  dsimp only
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hqref:0< cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k):=by positivity
  have hf:=active_error_parent_affine s C R0 B τ t (Ideal.span {p}) k Bp υ v Z κ Mdecl hZ hκ hP hcap
  have hPchild:∀i,1≤(errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).P i:=fun i=> hP i.val.val
  have hparent:=common_affine (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v) Cpick B₂ Z κ (Real.logb Z (volume s)) Mdecl hZ hκ hPchild hf
  have hr:=actual_error_reference_shift s.η τ C D hC hD hCD E K (volume s) Z
    (rawReduction B.val s.P) sigma delta reserve cost hK (volume_pos s) hZ
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) hcost hmod p k hk hs hl
  have he:=frozen_reduction_log s C R0 B Z hZ hB
  have hrad:0< errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume s)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k:=by
    unfold errorCommonRadius;positivity
  have hg:
    Real.logb Z (preVolume (commonData (withHeight (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v) υ v) Cpick Rpick B₂))-
      Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) C₂ D₂ U n)≤
      Real.logb Z (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k)-Real.logb Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k))-
      Real.logb Z (volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v))+Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
      (Fintype.card (liveIndices Bp.val):ℝ)*Real.logb Z (max 1 (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).upper)+
      Real.logb Z (ratioPenalty n) := by
    rcases hside with hside|hside
    · subst Cpick
      exact common_raw_reference_shift (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v) υ v S β C₂ D₂ Rpick hC₂ hD₂ hCD₂
        B₂ hB₂ U R rows W _ a Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) n hqref hrad ha hZ hlower hne
    · subst Cpick
      exact common_raw_reference_shift_right (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v) υ v S β C₂ D₂ Rpick hC₂ hD₂ hCD₂
        B₂ hB₂ U R rows W _ a Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) n hqref hrad ha hZ hlower hne
  have hQ:(Ideal.span {p})≠(0:Ideal O):=Ideal.span_singleton_eq_bot.not.mpr hp
  have hv:=active_error_volume s C R0 B τ t (Ideal.span {p}) hQ k hslot Bp υ v
  have hn:(Ideal.absNorm (Ideal.span {p}):ℝ)=normValue p:=by simp only [normValue]
  rw [hn] at hv
  rw [hv] at hg
  dsimp only at hr
  rw [errorRemoval_power p hp Z hZ k] at hr
  have hres:=le_max_left
    (delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
      min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
      Real.logb Z fixedPresentationCost-Real.logb Z cost+
      Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
      (Fintype.card (liveIndices Bp.val):ℝ)*Real.logb Z (max 1 (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).upper)) 0
  refine ⟨add_nonneg (sub_nonneg.mpr hM) (sourceReserve_nonneg _ _ _ _ _ _ _ _ _),hparent,?_⟩
  unfold sourceReserve
  linarith

theorem actual_width_admission {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayFourExpansion.RayCharacter→Character}
    (hf:CenteredMomentSecondExceptionalFamily.Family η C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
    (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0< K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)
    (qref Z:ℝ)(hq:(η.modulus.absNorm:ℝ)≤ qref)(hZ:1< Z)(χ:RayFourExpansion.RayCharacter):
    Real.logb Z (dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)-
      Real.logb Z (envelopeRef qref C D U n)≤0 := by
  have hh:=actual_width_le_reference hf t S β R rows W K hK n hne qref Z hq hZ χ
  linarith

lemma common_preVolume_height (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C)
    (τ υ:Character)(v t:ℝ):
    preVolume (commonData (withHeight s τ v) C R B)=
      preVolume (commonData (withHeight s υ t) C R B) := rfl

end CenteredMomentFirstAmplifiedPaidAdmission

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstAmplifiedPaidReserve
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacitySource
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstPhysicalSource CenteredMomentSecondCanonicalScalar CenteredMomentFirstScale
open CenteredMomentSecondRadicalBudget
open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
local notation "O"=> Eisenstein.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _

def fixedNumerator (N:ℕ)(lower upper cost0 a0:ℝ):ℝ :=
  (N:ℝ)*|Real.log (min 1 lower)|+(N:ℝ)*|Real.log (max 1 upper)|+
    |Real.log fixedPresentationCost|+|Real.log cost0|+
    |Real.log (4/((fixedFactor:ℝ)*a0^2))|

lemma fixedNumerator_nonneg (N:ℕ)(lower upper cost0 a0:ℝ):
    0≤ fixedNumerator N lower upper cost0 a0 := by unfold fixedNumerator;positivity

theorem source_reserve_bound (N:ℕ)(lower upper cost0 a0:ℝ)
    (hlower:0< lower)(hcost0:0< cost0)(ha0:0< a0)
    {ι α:Type*}[Fintype ι][Fintype α](s:Input ι)(input:Input α)
    (hn:Fintype.card ι≤ N)(hnc:Fintype.card α≤ N)
    (hl:lower≤ s.lower)(hu:input.upper≤ upper)
    (C D:Ideal O)(hC:C≠0)(hD:D≠0)(Z delta reserve cost a:ℝ)
    (hZ:1< Z)(hd:0≤ delta)(hr:0≤ reserve)(hc:cost0≤ cost)(ha:a0≤ a):
    sourceReserve s input C D Z delta reserve cost a≤
      delta+reserve+fixedNumerator N lower upper cost0 a0/Real.log Z := by
  have hz:=Real.log_pos hZ
  have hN:(0:ℝ)≤ N:=Nat.cast_nonneg _
  have hnc:(Fintype.card α:ℝ)≤ N:=by exact_mod_cast hnc
  have hno:(Fintype.card ι:ℝ)≤ N:=by exact_mod_cast hn
  have hmin:=Real.logb_le_logb_of_le hZ (lt_min zero_lt_one hlower) (min_le_min_left 1 hl)
  have hmin0:0≤-Real.logb Z (min 1 lower):=by
    have hh:=Real.logb_le_logb_of_le hZ (lt_min zero_lt_one hlower) (min_le_left 1 lower)
    rw [Real.logb_one] at hh
    linarith
  have hlow: -(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)≤(N:ℝ)*(-Real.logb Z (min 1 lower)):=by
    have hh:=mul_le_mul_of_nonneg_left hmin (Nat.cast_nonneg (Fintype.card ι): (0:ℝ)≤ _)
    have hh':=mul_le_mul_of_nonneg_right hno hmin0
    nlinarith
  have hmax:=Real.logb_le_logb_of_le hZ (lt_of_lt_of_le zero_lt_one (le_max_left 1 input.upper))
    (max_le_max_left 1 hu)
  have hmax0:0≤ Real.logb Z (max 1 upper):=Real.logb_nonneg hZ (le_max_left _ _)
  have hupp:(Fintype.card α:ℝ)*Real.logb Z (max 1 input.upper)≤(N:ℝ)*Real.logb Z (max 1 upper):=
    (mul_le_mul_of_nonneg_left hmax (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hnc hmax0)
  have hcost:=Real.logb_le_logb_of_le hZ hcost0 hc
  have hf:0<(fixedFactor:ℝ):=by exact_mod_cast fixedFactor_pos
  have ha':0< a:=ha0.trans_le ha
  have hfrac:4/((fixedFactor:ℝ)*a^2)≤4/((fixedFactor:ℝ)*a0^2):=by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul_of_nonneg_left (sq_le_sq₀ ha0.le ha'.le |>.mpr ha) hf.le
  have harg:=Real.logb_le_logb_of_le hZ (by positivity:0<4/((fixedFactor:ℝ)*a^2)) hfrac
  have hCN:(1:ℝ)≤ C.absNorm:=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hDN:(1:ℝ)≤ D.absNorm:=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hcommon:0≤ min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ)):=
    le_min (Real.logb_nonneg hZ hCN) (Real.logb_nonneg hZ hDN)
  have habs:
      (N:ℝ)*(-Real.logb Z (min 1 lower))+(N:ℝ)*Real.logb Z (max 1 upper)-
        Real.logb Z fixedPresentationCost-Real.logb Z cost0+
        Real.logb Z (4/((fixedFactor:ℝ)*a0^2))≤ fixedNumerator N lower upper cost0 a0/Real.log Z:=by
    simp only [Real.logb]
    rw [show (N:ℝ)*(-(Real.log (min 1 lower)/Real.log Z))+
      (N:ℝ)*(Real.log (max 1 upper)/Real.log Z)-Real.log fixedPresentationCost/Real.log Z-
      Real.log cost0/Real.log Z+Real.log (4/((fixedFactor:ℝ)*a0^2))/Real.log Z=
      ((N:ℝ)*(-Real.log (min 1 lower))+(N:ℝ)*Real.log (max 1 upper)-
        Real.log fixedPresentationCost-Real.log cost0+Real.log (4/((fixedFactor:ℝ)*a0^2)))/Real.log Z by ring]
    apply (div_le_div_iff_of_pos_right hz).mpr
    have h1:=mul_le_mul_of_nonneg_left (neg_le_abs (Real.log (min 1 lower))) hN
    have h2:=mul_le_mul_of_nonneg_left (le_abs_self (Real.log (max 1 upper))) hN
    unfold fixedNumerator
    linarith [neg_le_abs (Real.log fixedPresentationCost),neg_le_abs (Real.log cost0),
      le_abs_self (Real.log (4/((fixedFactor:ℝ)*a0^2)))]
  unfold sourceReserve
  apply max_le
  · linarith
  · exact add_nonneg (add_nonneg hd hr) (div_nonneg (fixedNumerator_nonneg _ _ _ _ _) hz.le)

theorem eventually_source_reserve (N:ℕ)(lower upper cost0 a0 theta:ℝ)
    (hlower:0< lower)(hcost0:0< cost0)(ha0:0< a0)(htheta:0< theta):
    ∃Z0:ℝ,1< Z0 ∧ ∀Z:ℝ,Z0≤ Z→
      ∀{ι α:Type*}[Fintype ι][Fintype α],∀(s:Input ι)(input:Input α),
      Fintype.card ι≤ N→Fintype.card α≤ N→lower≤ s.lower→input.upper≤ upper→
      ∀(C D:Ideal O),C≠0→D≠0→∀delta reserve cost a:ℝ,
      0≤ delta→0≤ reserve→cost0≤ cost→a0≤ a→
      sourceReserve s input C D Z delta reserve cost a≤ delta+reserve+theta := by
  let L:=fixedNumerator N lower upper cost0 a0
  have hL:0≤ L:=fixedNumerator_nonneg _ _ _ _ _
  let Z0:=Real.exp (1+L/theta)
  have hZ0:1< Z0:=Real.one_lt_exp_iff.mpr (by positivity)
  refine ⟨Z0,hZ0,?_⟩
  intro Z hZZ ι α _ _ s input hn hnc hl hu C D hC hD delta reserve cost a hd hr hc ha
  have hZ:1< Z:=hZ0.trans_le hZZ
  have hlog:=Real.log_le_log (Real.exp_pos _) hZZ
  rw [Real.log_exp] at hlog
  have hsmall:L/Real.log Z≤ theta:=by
    apply (div_le_iff₀ (Real.log_pos hZ)).mpr
    have hh:(L/theta)*theta≤(Real.log Z)*theta:=
      mul_le_mul_of_nonneg_right (by linarith) htheta.le
    rw [div_mul_cancel₀ _ htheta.ne'] at hh
    linarith
  have hb:=source_reserve_bound N lower upper cost0 a0 hlower hcost0 ha0 s input
    hn hnc hl hu C D hC hD Z delta reserve cost a hZ hd hr hc ha
  exact hb.trans (by change delta+reserve+L/Real.log Z≤ _;linarith)

theorem eventually_actual_amplified_reserves (N:ℕ)(lower upper cost0 a0 theta:ℝ)
    (hlower:0< lower)(hcost0:0< cost0)(ha0:0< a0)(htheta:0< theta):
    ∃Z0:ℝ,1< Z0 ∧ ∀Z:ℝ,Z0≤ Z→
      ∀{ι:Type*}[Fintype ι],∀s:Input ι,
      Fintype.card ι≤ N→lower≤ s.lower→s.upper≤ upper→
      ∀(C D R:Ideal O),C≠0→D≠0→∀B:actualAllocations s.pools C,
      ∀(τ:Character)(t delta reserve cost a:ℝ),
      0≤ delta→0≤ reserve→cost0≤ cost→a0≤ a→
      sourceReserve s (child s C R B τ t) C D Z delta reserve cost a≤ delta+reserve+theta ∧
      ∀(Q:Ideal O)(k:ℕ)
        (Bp:actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
        (υ:Character)(v:ℝ),
        sourceReserve s (errorInput s C R B τ t Q k Bp υ v) C D Z delta reserve cost a≤
          delta+reserve+theta := by
  obtain ⟨Z0,hZ0,hbound⟩:=eventually_source_reserve N lower upper cost0 a0 theta
    hlower hcost0 ha0 htheta
  refine ⟨Z0,hZ0,?_⟩
  intro Z hZZ ι _ s hn hl hu C D R hC hD B τ t delta reserve cost a hd hr hc ha
  have hchild:Fintype.card (liveIndices B.val)≤ N:=(live_card_le B.val).trans hn
  refine ⟨hbound Z hZZ s (child s C R B τ t) hn hchild hl hu C D hC hD
    delta reserve cost a hd hr hc ha,?_⟩
  intro Q k Bp υ v
  have herr:Fintype.card (liveIndices Bp.val)≤ N:=(live_card_le Bp.val).trans hchild
  exact hbound Z hZZ s (errorInput s C R B τ t Q k Bp υ v) hn herr hl hu C D hC hD
    delta reserve cost a hd hr hc ha

end CenteredMomentFirstAmplifiedPaidReserve

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentAmplificationMask
open CenteredMomentRectangle CenteredMomentAmplificationRectangle CenteredMomentAmplificationShortening
local notation "O" => Eisenstein.O

theorem whole_product_divisibility (p : O) (s Q I J : Ideal O)
    (hcop : IsCoprime s (Ideal.span {p})) (k j : ℕ) (hj : j ≤ k) :
    s∣Q*((Ideal.span {p})^j*I)*((Ideal.span {p})^(k-j)*J) ↔ s∣Q*I*J := by
  have he : Q*((Ideal.span {p})^j*I)*((Ideal.span {p})^(k-j)*J) =
      (Ideal.span {p})^k*(Q*I*J) := by
    calc
      _ = ((Ideal.span {p})^j*(Ideal.span {p})^(k-j))*(Q*I*J) := by ring
      _ = _ := by rw [← pow_add,Nat.add_sub_of_le hj]
  rw [he]
  exact ⟨(hcop.pow_right (n := k)).dvd_of_dvd_mul_left,
    fun h => dvd_mul_of_dvd_right h _⟩

theorem masked_centered_coefficient_prime_extract (p : O) (hp : p ≠ 0)
    (s : Ideal O) (hcop : IsCoprime s (Ideal.span {p}))
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ T : ℝ) (hT : 0 < T)
    (Q I J : Ideal O) (k j : ℕ) (hj : j ≤ k) :
    (Real.sqrt T:ℂ)⁻¹ *
      (idealWeight c χ R t (Q*((Ideal.span {p})^j*I)*((Ideal.span {p})^(k-j)*J))*
        CenteredMomentRectangle.idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂
          ((Ideal.span {p})^j*I) ((Ideal.span {p})^(k-j)*J)) *
      (if s∣Q*((Ideal.span {p})^j*I)*((Ideal.span {p})^(k-j)*J) then (1:ℂ) else 0) =
      (idealWeight c χ R t ((Ideal.span {p})^k)/primeRoot p k)*
        ((Real.sqrt (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^k):ℂ)⁻¹ *
          (idealWeight c χ R t (Q*I*J)*
            CenteredMomentRectangle.idealRectangle W₁ W₂
              (X₁/(Ideal.absNorm (Ideal.span {p}):ℝ)^j)
              (X₂/(Ideal.absNorm (Ideal.span {p}):ℝ)^(k-j))
              (Y₁/(Ideal.absNorm (Ideal.span {p}):ℝ)^j)
              (Y₂/(Ideal.absNorm (Ideal.span {p}):ℝ)^(k-j)) I J)*
          (if s∣Q*I*J then (1:ℂ) else 0)) := by
  simp only [whole_product_divisibility p s Q I J hcop k j hj]
  rw [centered_coefficient_prime_extract p hp c χ R t W₁ W₂ X₁ X₂ Y₁ Y₂ T hT Q I J k j hj]
  ring

end CenteredMomentAmplificationMask

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentAmplificationAllocation
open CanonicalQuadraticSieve CanonicalRowCompletion  CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentSupportedCorrelation
local notation "O" => Eisenstein.O

theorem primeRemainder_primary (p : O) (hp : Prime p) (hpp : lambda^2 ∣ p-1)
    (a : O) (ha : Supported (Ideal.span {a})) (hpa : lambda^2 ∣ a-1) :
    lambda^2 ∣ primeRemainder p hp a (supported_element_ne_zero a ha)-1 := by
  let r := primeRemainder p hp a (supported_element_ne_zero a ha)
  have hr := primeRemainder_supported p hp a ha
  have hgen := supported_primaryIdealGenerator_ne_zero (Ideal.span {r}) hr
  have he : a = p^(multiplicity p a)*primaryIdealGenerator (Ideal.span {r}) := by
    calc
      a = primaryIdealGenerator (Ideal.span {a}) := (primaryIdealGenerator_span a
        (supported_element_ne_zero a ha) hpa).symm
      _ = _ := by
        conv_lhs => rw [(primeRemainder_spec p hp a (supported_element_ne_zero a ha)).1]
        rw [← Ideal.span_singleton_mul_span_singleton,primaryIdealGenerator_mul,
          ← Ideal.span_singleton_pow,primaryIdealGenerator_pow,primaryIdealGenerator_span p hp.ne_zero hpp]
  have hre : r = primaryIdealGenerator (Ideal.span {r}) := by
    apply mul_left_cancel₀ (pow_ne_zero (multiplicity p a) hp.ne_zero)
    exact (primeRemainder_spec p hp a (supported_element_ne_zero a ha)).1.symm.trans he
  change lambda^2 ∣ r-1
  rw [hre]
  exact (primaryIdealGenerator_spec _ hgen).2

theorem plain_product_valuation (p : O) (hp : Prime p) (q a b : O)
    (hq : q ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hpq : ¬p ∣ q) :
    multiplicity p (q*a*b) = multiplicity p a + multiplicity p b := by
  rw [multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp (mul_ne_zero (mul_ne_zero hq ha) hb)),
    multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp (mul_ne_zero hq ha)),
    multiplicity_eq_zero.mpr hpq,zero_add]

theorem plain_product_remainder (p : O) (hp : Prime p) (q a b : O)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    q*a*b = p^(multiplicity p a + multiplicity p b) *
      (q*primeRemainder p hp a ha*primeRemainder p hp b hb) := by
  conv_lhs => rw [(primeRemainder_spec p hp a ha).1,(primeRemainder_spec p hp b hb).1]
  rw [pow_add]
  ring

theorem split_plain_valuation {α β : Type*} (S : Finset α) (T : Finset β)
    (v : α → ℕ) (w : β → ℕ) (k : ℕ) (c : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, if v i + w j = k then c i j else 0) =
      ∑ r ∈ Finset.range (k+1), ∑ i ∈ S, ∑ j ∈ T,
        if v i = r ∧ w j = k-r then c i j else 0 := by
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hk : v i + w j = k
  · rw [if_pos hk,Finset.sum_eq_single (v i)]
    · simp only [true_and]
      rw [if_pos (by omega)]
    · intro r hr hne
      rw [if_neg (fun h => hne h.1.symm)]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  · rw [if_neg hk]
    symm
    apply Finset.sum_eq_zero
    intro r hr
    rw [if_neg]
    intro h
    exact hk (by have hh := Finset.mem_range.mp hr; omega)

theorem split_actual_plain_product {α β : Type*} (S : Finset α) (T : Finset β)
    (p : O) (hp : Prime p) (q : O) (hq : q ≠ 0) (hpq : ¬p ∣ q)
    (a : α → O) (ha : ∀ i, a i ≠ 0) (b : β → O) (hb : ∀ j, b j ≠ 0)
    (k : ℕ) (c : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, if multiplicity p (q*a i*b j) = k then c i j else 0) =
      ∑ r ∈ Finset.range (k+1), ∑ i ∈ S, ∑ j ∈ T,
        if multiplicity p (a i) = r ∧ multiplicity p (b j) = k-r then c i j else 0 := by
  simp_rw [plain_product_valuation p hp q _ _ hq (ha _) (hb _) hpq]
  exact split_plain_valuation S T _ _ k c

theorem error_allocation_count (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    (Finset.range (k+1)).card ≤ 8 := by
  rw [Finset.card_range]
  rcases hk with rfl | rfl | rfl <;> omega

end CenteredMomentAmplificationAllocation

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentAmplificationSource
open CanonicalQuadraticSieve CanonicalRowCompletion  CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationAllocation CenteredMomentGaussEnergy
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow CenteredMomentLiveDomain
local notation "O" => Eisenstein.O

 theorem primeRoot_ne_zero (p : O) (hp : p ≠ 0) (k : ℕ) : primeRoot p k ≠ 0 := by
  unfold primeRoot
  apply Complex.ofReal_ne_zero.mpr
  apply Real.sqrt_ne_zero'.mpr
  apply pow_pos
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hp))

theorem original_error_shortening {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hap : ∀ i, lambda^2 ∣ a i-1) (c : α → ℂ)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : lambda^2 ∣ p-1) (n : ℕ) (h : O) :
    amplificationError S a ha c (fun i => multiplicity p (a i)) p (n+1) h =
      (primeRoot p (n+1)*errorScalar p hp.ne_zero n h)*
        gaussPolynomial S
          (fun i => primeRemainder p hp (a i) (supported_element_ne_zero _ (ha i)))
          (fun i => primeRemainder_supported p hp (a i) (ha i))
          (fun i => if multiplicity p (a i)=n+1 then
            c i*residualCharacter p (n+1)
              (primeRemainder p hp (a i) (supported_element_ne_zero _ (ha i))) else 0) h := by
  unfold amplificationError gaussPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  by_cases hv : multiplicity p (a i)=n+1
  · simp only [if_pos hv]
    let r := primeRemainder p hp (a i) (supported_element_ne_zero _ (ha i))
    have hr := primeRemainder_supported p hp (a i) (ha i)
    have hcop : IsCoprime p r := hp.irreducible.coprime_iff_not_dvd.mpr
      (primeRemainder_spec p hp (a i) (supported_element_ne_zero _ (ha i))).2
    have hf : a i=p^(n+1)*r := by
      simpa only [hv] using (primeRemainder_spec p hp (a i) (supported_element_ne_zero _ (ha i))).1
    have he := central_error_shortening p r n hs hr hpp
      (primeRemainder_primary p hp hpp (a i) (ha i) (hap i)) hcop h
    have he' : gaussRow (a i) (ha i) h-gaussRow (a i) (ha i) (p^6*h) =
        primeRoot p (n+1)*(errorScalar p hp.ne_zero n h *
          (residualCharacter p (n+1) r*gaussRow r hr h)) := by
      have hh := (div_eq_iff (primeRoot_ne_zero p hp.ne_zero (n+1))).mp he
      simp only [hf,errorScalar]
      exact hh.trans (by ring)
    rw [he']
    ring
  · simp only [if_neg hv,zero_mul,mul_zero]

theorem source_error_shortening (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : lambda^2 ∣ p-1) (n : ℕ) (h : O) :
    amplificationError Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => c I)
      (fun I => multiplicity p (sourceGenerator S I)) p (n+1) h =
      (primeRoot p (n+1)*errorScalar p hp.ne_zero n h)*
        gaussPolynomial Finset.univ
          (fun I : supportedColumns S => primeRemainder p hp (sourceGenerator S I)
            (supported_element_ne_zero _ (sourceGenerator_supported S I)))
          (fun I => primeRemainder_supported p hp (sourceGenerator S I) (sourceGenerator_supported S I))
          (fun I => if multiplicity p (sourceGenerator S I)=n+1 then
            c I*residualCharacter p (n+1)
              (primeRemainder p hp (sourceGenerator S I)
                (supported_element_ne_zero _ (sourceGenerator_supported S I))) else 0) h := by
  apply original_error_shortening _ _ _ _ _ p hp hs hpp n h
  intro I
  exact (primaryIdealGenerator_spec I (supported_primaryIdealGenerator_ne_zero I
    (Finset.mem_filter.mp I.property).2)).2

end CenteredMomentAmplificationSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentAmplificationSourceDomain
open CanonicalQuadraticSieve CanonicalRowCompletion  CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationAllocation CenteredMomentGaussEnergy
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow CenteredMomentLiveDomain
local notation "O" => Eisenstein.O

def residualIdeal (p : O) (hp : Prime p) (I : Ideal O) : Ideal O :=
  if hI : Supported I then Ideal.span {primeRemainder p hp (primaryIdealGenerator I)
    (supported_primaryIdealGenerator_ne_zero I hI)} else 0

theorem residualIdeal_supported (p : O) (hp : Prime p) (I : Ideal O) (hI : Supported I) :
    Supported (residualIdeal p hp I) := by
  rw [residualIdeal,dif_pos hI]
  exact primeRemainder_supported p hp (primaryIdealGenerator I)
    (by rw [primary_span_supported I hI];exact hI)

theorem residualIdeal_generator (p : O) (hp : Prime p) (hpp : lambda^2 ∣ p-1)
    (I : Ideal O) (hI : Supported I) :
    primaryIdealGenerator (residualIdeal p hp I) =
      primeRemainder p hp (primaryIdealGenerator I) (supported_primaryIdealGenerator_ne_zero I hI) := by
  rw [residualIdeal,dif_pos hI]
  apply primaryIdealGenerator_span
  · apply supported_element_ne_zero
    simpa only [residualIdeal,dif_pos hI] using residualIdeal_supported p hp I hI
  · exact primeRemainder_primary p hp hpp (primaryIdealGenerator I)
      (by rw [primary_span_supported I hI];exact hI)
      (primaryIdealGenerator_spec I (supported_primaryIdealGenerator_ne_zero I hI)).2

theorem residualIdeal_reconstruct (p : O) (hp : Prime p) (I : Ideal O) (hI : Supported I) :
    (Ideal.span {p})^(multiplicity p (primaryIdealGenerator I))*residualIdeal p hp I=I := by
  rw [residualIdeal,dif_pos hI,Ideal.span_singleton_pow,
    Ideal.span_singleton_mul_span_singleton,
    ← (primeRemainder_spec p hp (primaryIdealGenerator I) (supported_primaryIdealGenerator_ne_zero I hI)).1]
  exact primary_span_supported I hI

def valuationColumns (S : Finset (Ideal O)) (p : O) (k : ℕ) : Finset (Ideal O) :=
  (supportedColumns S).filter (fun I => multiplicity p (primaryIdealGenerator I)=k)

def residualColumns (S : Finset (Ideal O)) (p : O) (hp : Prime p) (k : ℕ) : Finset (Ideal O) :=
  (valuationColumns S p k).image (residualIdeal p hp)

theorem valuationColumns_supported (S : Finset (Ideal O)) (p : O) (k : ℕ)
    (I : Ideal O) (hI : I∈valuationColumns S p k) : Supported I :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2

theorem residualIdeal_injOn (S : Finset (Ideal O)) (p : O) (hp : Prime p) (k : ℕ) :
    Set.InjOn (residualIdeal p hp) (valuationColumns S p k) := by
  intro I hI J hJ he
  have hi := residualIdeal_reconstruct p hp I (valuationColumns_supported S p k I hI)
  have hj := residualIdeal_reconstruct p hp J (valuationColumns_supported S p k J hJ)
  rw [(Finset.mem_filter.mp hI).2] at hi
  rw [(Finset.mem_filter.mp hJ).2] at hj
  exact hi.symm.trans ((congrArg (fun x => (Ideal.span {p})^k*x) he).trans hj)

theorem residualColumns_supported (S : Finset (Ideal O)) (p : O) (hp : Prime p) (k : ℕ)
    (I : Ideal O) (hI : I∈residualColumns S p hp k) : Supported I := by
  obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
  exact residualIdeal_supported p hp J (valuationColumns_supported S p k J hJ)

theorem residual_column_sum (S : Finset (Ideal O)) (p : O) (hp : Prime p) (k : ℕ)
    (c f : Ideal O → ℂ) :
    (∑ I∈valuationColumns S p k,c I*f (residualIdeal p hp I))=
      ∑ I∈residualColumns S p hp k,c ((Ideal.span {p})^k*I)*f I := by
  rw [residualColumns,Finset.sum_image (residualIdeal_injOn S p hp k)]
  apply Finset.sum_congr rfl
  intro I hI
  have hi := residualIdeal_reconstruct p hp I (valuationColumns_supported S p k I hI)
  rw [(Finset.mem_filter.mp hI).2] at hi
  rw [hi]

end CenteredMomentAmplificationSourceDomain

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentAmplificationSourcePolynomial
open CanonicalQuadraticSieve CanonicalRowCompletion  CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationSource CenteredMomentAmplificationSourceDomain
open CenteredMomentGaussEnergy CenteredMomentSupportedCorrelation
open CenteredMomentSourceRow CenteredMomentLiveDomain
local notation "O" => Eisenstein.O

 theorem residual_primaryGaussRow (p : O) (hp : Prime p)
    (hpp : lambda^2 ∣ p-1) (I : Ideal O) (hI : Supported I) (h : O) :
    primaryGaussRow (residualIdeal p hp I) h=
      gaussRow (primeRemainder p hp (primaryIdealGenerator I)
        (supported_primaryIdealGenerator_ne_zero I hI))
        (primeRemainder_supported p hp (primaryIdealGenerator I)
          (by rw [primary_span_supported I hI];exact hI)) h := by
  simp only [primaryGaussRow,dif_pos (residualIdeal_supported p hp I hI),
    residualIdeal_generator p hp hpp I hI]

 theorem supported_residualColumns (S : Finset (Ideal O)) (p : O) (hp : Prime p) (k : ℕ) :
    supportedColumns (residualColumns S p hp k)=residualColumns S p hp k := by
  apply Finset.filter_eq_self.mpr
  exact residualColumns_supported S p hp k

theorem remainder_polynomial (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (p : O) (hp : Prime p) (hpp : lambda^2 ∣ p-1) (k : ℕ) (h : O) :
    gaussPolynomial Finset.univ
      (fun I : supportedColumns S => primeRemainder p hp (sourceGenerator S I)
        (supported_element_ne_zero _ (sourceGenerator_supported S I)))
      (fun I => primeRemainder_supported p hp (sourceGenerator S I) (sourceGenerator_supported S I))
      (fun I => if multiplicity p (sourceGenerator S I)=k then
        c I*residualCharacter p k
          (primeRemainder p hp (sourceGenerator S I)
            (supported_element_ne_zero _ (sourceGenerator_supported S I))) else 0) h =
      gaussPolynomial Finset.univ (sourceGenerator (residualColumns S p hp k))
        (sourceGenerator_supported (residualColumns S p hp k))
        (fun I : supportedColumns (residualColumns S p hp k) =>
          c ((Ideal.span {p})^k*I)*residualCharacter p k (primaryIdealGenerator I)) h := by
  let f : Ideal O → ℂ := fun I => residualCharacter p k (primaryIdealGenerator I)*primaryGaussRow I h
  have he := residual_column_sum S p hp k c f
  have hl : (∑ I∈valuationColumns S p k,c I*f (residualIdeal p hp I))=
      gaussPolynomial Finset.univ
        (fun I : supportedColumns S => primeRemainder p hp (sourceGenerator S I)
          (supported_element_ne_zero _ (sourceGenerator_supported S I)))
        (fun I => primeRemainder_supported p hp (sourceGenerator S I) (sourceGenerator_supported S I))
        (fun I => if multiplicity p (sourceGenerator S I)=k then
          c I*residualCharacter p k
            (primeRemainder p hp (sourceGenerator S I)
              (supported_element_ne_zero _ (sourceGenerator_supported S I))) else 0) h := by
    rw [valuationColumns,Finset.sum_filter]
    unfold gaussPolynomial
    rw [← Finset.sum_coe_sort (supportedColumns S)]
    apply Finset.sum_congr rfl
    intro I hI
    have hIs : Supported (I : Ideal O) := (Finset.mem_filter.mp I.property).2
    dsimp only [sourceGenerator]
    rw [show f (residualIdeal p hp I)=
      residualCharacter p k (primeRemainder p hp (primaryIdealGenerator I)
        (supported_primaryIdealGenerator_ne_zero I hIs))*
      gaussRow (primeRemainder p hp (primaryIdealGenerator I)
        (supported_primaryIdealGenerator_ne_zero I hIs))
        (primeRemainder_supported p hp (primaryIdealGenerator I)
          (by rw [primary_span_supported I hIs]
              exact hIs)) h by
      dsimp only [f]
      rw [residualIdeal_generator p hp hpp I hIs,
        residual_primaryGaussRow p hp hpp I hIs h]]
    split_ifs <;> ring
  refine hl.symm.trans (he.trans ?_)
  have hh := source_gaussPolynomial (residualColumns S p hp k)
    (fun I => c ((Ideal.span {p})^k*I)*residualCharacter p k (primaryIdealGenerator I)) h
  refine Eq.trans ?_ hh.symm
  rw [supported_residualColumns]
  apply Finset.sum_congr rfl
  intro I hI
  dsimp only [f]
  ring

end CenteredMomentAmplificationSourcePolynomial

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentAmplificationSourcePool
open CanonicalQuadraticSieve CanonicalRowCompletion  CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationAllocation CenteredMomentAmplificationSourceDomain
open CenteredMomentSourceRow CenteredMomentLiveDomain CenteredMomentFirstSectors
open CenteredMomentSupportedCorrelation CenteredMomentUnequal
local notation "O" => Eisenstein.O

theorem residualIdeal_coprime (p : O) (hp : Prime p) (I : Ideal O) (hI : Supported I) :
    IsCoprime (Ideal.span {p}) (residualIdeal p hp I) := by
  rw [residualIdeal,dif_pos hI,Ideal.isCoprime_span_singleton_iff]
  exact hp.irreducible.coprime_iff_not_dvd.mpr
    (primeRemainder_spec p hp (primaryIdealGenerator I) (supported_primaryIdealGenerator_ne_zero I hI)).2

theorem residualColumns_eq (S : Finset (Ideal O)) (p : O) (hp : Prime p)
    (hs : Supported (Ideal.span {p})) (hpp : lambda^2 ∣ p-1) (k : ℕ) :
    residualColumns S p hp k=
      (supportedColumns (residualPool ((Ideal.span {p})^k) (pow_ne_zero k hs.1) S)).filter
        (fun I => IsCoprime (Ideal.span {p}) I) := by
  ext I
  constructor
  · intro hI
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
    have hsJ := valuationColumns_supported S p k J hJ
    have hh := residualIdeal_reconstruct p hp J hsJ
    rw [(Finset.mem_filter.mp hJ).2] at hh
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_,residualIdeal_supported p hp J hsJ⟩,
      residualIdeal_coprime p hp J hsJ⟩
    apply (mem_residualPool _ _ S _).mpr
    rw [hh]
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hJ).1).1
  · intro hI
    obtain ⟨hI,hcop⟩ := Finset.mem_filter.mp hI
    obtain ⟨hpool,hsI⟩ := Finset.mem_filter.mp hI
    have hIS := (mem_residualPool _ _ S I).mp hpool
    let J := (Ideal.span {p})^k*I
    have hsJ : Supported J := by
      rw [supported_mul_iff]
      constructor
      · simpa only [← Ideal.span_singleton_pow] using supported_power p hs k
      · exact hsI
    have hgen : primaryIdealGenerator J=p^k*primaryIdealGenerator I := by
      rw [show J=(Ideal.span {p})^k*I from rfl,primaryIdealGenerator_mul,primaryIdealGenerator_pow,
        primaryIdealGenerator_span p hp.ne_zero hpp]
    have hcop' : IsCoprime p (primaryIdealGenerator I) := by
      apply (Ideal.isCoprime_span_singleton_iff _ _).mp
      rw [primary_span_supported I hsI]
      exact hcop
    have hv : multiplicity p (primaryIdealGenerator J)=k := by
      rw [hgen,multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp
        (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (supported_primaryIdealGenerator_ne_zero I hsI))),
        multiplicity_pow_self_of_prime hp,
        multiplicity_eq_zero.mpr (hp.irreducible.coprime_iff_not_dvd.mp hcop'),add_zero]
    have hj : J∈valuationColumns S p k :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hIS,hsJ⟩,hv⟩
    refine Finset.mem_image.mpr ⟨J,hj,?_⟩
    apply mul_left_cancel₀ (pow_ne_zero k hs.1)
    have hh := residualIdeal_reconstruct p hp J hsJ
    simpa only [hv] using hh

end CenteredMomentAmplificationSourcePool

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentAmplificationSourceError
open CanonicalQuadraticSieve CanonicalRowCompletion  CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationSource CenteredMomentAmplificationSourceDomain
open CenteredMomentAmplificationSourcePolynomial CenteredMomentAmplificationSourcePool
open CenteredMomentAmplificationRectangle CenteredMomentGaussNormalization
open CenteredMomentGaussEnergy CenteredMomentSupportedCorrelation CenteredMomentSourceRow
local notation "O" => Eisenstein.O

 theorem source_error_residual (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : lambda^2 ∣ p-1) (n : ℕ) (h : O) :
    amplificationError Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => c I)
      (fun I => multiplicity p (sourceGenerator S I)) p (n+1) h =
      (primeRoot p (n+1)*errorScalar p hp.ne_zero n h)*
        gaussPolynomial Finset.univ (sourceGenerator (residualColumns S p hp (n+1)))
          (sourceGenerator_supported (residualColumns S p hp (n+1)))
          (fun I : supportedColumns (residualColumns S p hp (n+1)) =>
            c ((Ideal.span {p})^(n+1)*I)*residualCharacter p (n+1) (primaryIdealGenerator I)) h := by
  rw [source_error_shortening S c p hp hs hpp n h,
    remainder_polynomial S c p hp hpp (n+1) h]

theorem normalized_source_error (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : lambda^2 ∣ p-1) (n : ℕ) (h : O) (T : ℝ) (hT : 0< T) :
    amplificationError Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => (Real.sqrt T:ℂ)⁻¹*c I)
      (fun I => multiplicity p (sourceGenerator S I)) p (n+1) h =
      errorScalar p hp.ne_zero n h *
        gaussPolynomial Finset.univ (sourceGenerator (residualColumns S p hp (n+1)))
          (sourceGenerator_supported (residualColumns S p hp (n+1)))
          (fun I : supportedColumns (residualColumns S p hp (n+1)) =>
            (Real.sqrt (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)):ℂ)⁻¹*
            (c ((Ideal.span {p})^(n+1)*I)*residualCharacter p (n+1) (primaryIdealGenerator I))) h := by
  rw [source_error_residual S (fun I => (Real.sqrt T:ℂ)⁻¹*c I) p hp hs hpp n h]
  simp only [mul_assoc,gaussPolynomial_const_mul]
  rw [centralRoot_extract p hp.ne_zero (n+1) T hT]
  have hr := primeRoot_ne_zero p hp.ne_zero (n+1)
  field_simp

theorem normalized_source_error_sq (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : lambda^2 ∣ p-1) (n : ℕ) (h : O) (T : ℝ) (hT : 0< T) :
    ‖amplificationError Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => (Real.sqrt T:ℂ)⁻¹*c I)
      (fun I => multiplicity p (sourceGenerator S I)) p (n+1) h‖^2 =
      ‖errorScalar p hp.ne_zero n h‖^2 *
        ‖gaussPolynomial Finset.univ (sourceGenerator (residualColumns S p hp (n+1)))
          (sourceGenerator_supported (residualColumns S p hp (n+1)))
          (fun I : supportedColumns (residualColumns S p hp (n+1)) =>
            (Real.sqrt (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)):ℂ)⁻¹*
            (c ((Ideal.span {p})^(n+1)*I)*residualCharacter p (n+1) (primaryIdealGenerator I))) h‖^2 := by
  rw [normalized_source_error S c p hp hs hpp n h T hT,norm_mul,mul_pow]

end CenteredMomentAmplificationSourceError

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentAmplificationErrorPool
open CanonicalQuadraticSieve 
open CenteredMomentAmplificationSourceDomain CenteredMomentAmplificationSourcePolynomial
open CenteredMomentAmplificationSourcePool CenteredMomentSourceRow CenteredMomentLiveDomain
open CenteredMomentGaussEnergy CenteredMomentFirstSectors CenteredMomentOriginalChildEnergy
local notation "O" => Eisenstein.O

 theorem residual_polynomial_eq_punctured (S : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : lambda^2 ∣ p-1) (k : ℕ) (hk : 0< k) (h : O) :
    gaussPolynomial Finset.univ (sourceGenerator (residualColumns S p hp k))
      (sourceGenerator_supported (residualColumns S p hp k))
      (fun I : supportedColumns (residualColumns S p hp k) => c ((Ideal.span {p})^k*I)*f I) h=
    gaussPolynomial Finset.univ
      (sourceGenerator (residualPool ((Ideal.span {p})^k) (pow_ne_zero k hs.1) S))
      (sourceGenerator_supported (residualPool ((Ideal.span {p})^k) (pow_ne_zero k hs.1) S))
      (fun I : supportedColumns (residualPool ((Ideal.span {p})^k) (pow_ne_zero k hs.1) S) =>
        (if IsCoprime ((Ideal.span {p})^k) (I:Ideal O) then c ((Ideal.span {p})^k*I) else 0)*f I) h := by
  let C := (Ideal.span {p})^k
  let Q := residualPool C (pow_ne_zero k hs.1) S
  refine (source_gaussPolynomial _ (fun I => c (C*I)*f I) h).trans ?_
  refine Eq.trans ?_ (source_gaussPolynomial Q
    (fun I => (if IsCoprime C I then c (C*I) else 0)*f I) h).symm
  rw [supported_residualColumns,residualColumns_eq S p hp hs hpp k,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  dsimp only [C]
  rw [IsCoprime.pow_left_iff hk]
  split_ifs <;> simp only [zero_mul]

 theorem residual_energy_eq_punctured (S : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : lambda^2 ∣ p-1) (k : ℕ) (hk : 0< k) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy (residualColumns S p hp k) (fun I => c ((Ideal.span {p})^k*I)) f W K=
      sourceGaussEnergy (residualPool ((Ideal.span {p})^k) (pow_ne_zero k hs.1) S)
        (fun I => if IsCoprime ((Ideal.span {p})^k) I then c ((Ideal.span {p})^k*I) else 0) f W K := by
  unfold sourceGaussEnergy gaussEnergy
  apply tsum_congr
  intro h
  rw [residual_polynomial_eq_punctured S c f p hp hs hpp k hk h]

end CenteredMomentAmplificationErrorPool

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentAmplificationErrorEnergy
open CanonicalQuadraticSieve CanonicalRowCompletion  CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationSourceError CenteredMomentAmplificationSourceDomain
open CenteredMomentGaussEnergy CenteredMomentGaussNormalization
open CenteredMomentSourceRow CenteredMomentOriginalChildEnergy
local notation "O" => Eisenstein.O

theorem localErrorCost_exact (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6)
    (h : O) (hh : ¬p∣h) : ‖errorScalar p hp.ne_zero n h‖^2=localErrorCost p n := by
  have he := errorScalar_norms p hp hs hg hc h hh
  rcases hn with rfl|rfl|rfl
  · simpa only [localErrorCost,show ¬(0:ℕ)=5 by decide,ite_false] using he.1
  · simpa only [localErrorCost,ite_true] using he.2.1
  · simpa only [localErrorCost,show ¬(6:ℕ)=5 by decide,ite_false] using he.2.2

theorem finite_original_error_energy (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hpp : lambda^2 ∣ p-1)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) (T : ℝ) (hT : 0< T)
    (rows : Finset O) (hrows : ∀ h∈rows,¬p∣h)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K)
    (hW : ∀ z : O,0≤(W (‖ringComplex z‖^2/K)).re)
    (hmajor : ∀ z∈rows,1≤(W (‖ringComplex z‖^2/K)).re) :
    (∑ h∈rows,‖amplificationError Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => (Real.sqrt T:ℂ)⁻¹*c I)
      (fun I => multiplicity p (sourceGenerator S I)) p (n+1) h‖^2)≤
      localErrorCost p n *
        ((sourceGaussEnergy (residualColumns S p hp (n+1))
          (fun I => c ((Ideal.span {p})^(n+1)*I))
          (fun I => residualCharacter p (n+1) (primaryIdealGenerator I)) W K).re /
          (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1))) := by
  let Q := residualColumns S p hp (n+1)
  let T' := T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)
  let d : supportedColumns Q → ℂ := fun I =>
    c ((Ideal.span {p})^(n+1)*I)*residualCharacter p (n+1) (primaryIdealGenerator I)
  have ht : 0< T' := by
    apply div_pos hT
    apply pow_pos
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs.1)
  have he : (∑ h∈rows,‖amplificationError Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => (Real.sqrt T:ℂ)⁻¹*c I)
      (fun I => multiplicity p (sourceGenerator S I)) p (n+1) h‖^2)=
      localErrorCost p n *∑ h∈rows,
        ‖gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
          (fun I => (Real.sqrt T':ℂ)⁻¹*d I) h‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    rw [normalized_source_error_sq S c p hp hs hpp n h T hT,
      localErrorCost_exact p hp hs hg hc n hn h (hrows h hh)]
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (localErrorCost_nonneg p n)
  have hh := finite_energy_le_gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I => (Real.sqrt T':ℂ)⁻¹*d I) W K hK rows hW hmajor
  rw [gaussEnergy_central _ _ _ d T' ht] at hh
  exact hh

end CenteredMomentAmplificationErrorEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentAmplificationFamily
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion
open  CompletedGauss RayFourExpansion
open CenteredMomentAmplificationShortening CenteredMomentFixedRay
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow
open CenteredMomentSecondChildProfile CenteredMomentSourceRow CenteredMomentChildRows
local notation "O" => Eisenstein.O

def amplificationPhase (p : O) (k : ℕ) (r : RayRing) : ℂ :=
  quotientPhase (Ideal.Quotient.mk _ p) r ^ k

theorem amplificationPhase_mk (p u : O) (k : ℕ) :
    amplificationPhase p k (Ideal.Quotient.mk _ u)=sexticReciprocityPhase p u^k := by
  rw [amplificationPhase,quotientPhase_mk]

theorem amplificationPhase_norm (p : O) (k : ℕ) (r : RayRing) :
    ‖amplificationPhase p k r‖≤1 := by
  rw [amplificationPhase,norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (sexticReciprocityPhase_norm _ _)

theorem amplificationPhase_mass (p : O) (k : ℕ) :
    (∑ χ : RayCharacter,‖phaseCoeff (amplificationPhase p k) χ‖)≤16 := by
  have h := phaseCoeff_sum_norm_le (amplificationPhase p k) 1
    (fun u => amplificationPhase_norm p k u)
  rw [mul_one] at h
  exact h.trans (by exact_mod_cast rayUnit_card_le)

theorem amplificationPhase_expansion (p u : O) (k : ℕ)
    (hu : Supported (Ideal.span {u})) :
    sexticReciprocityPhase p u^k=
      ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*rayMonoid χ u := by
  have he := phase_expansion (amplificationPhase p k) u
  change ProbeCompleted.rayMask u * amplificationPhase p k (Ideal.Quotient.mk _ u) = _ at he
  simpa only [supported_rayMask u hu,one_mul,amplificationPhase_mk] using he

theorem exists_amplification_family (η : Character) (m p : O)
    (hm : m≠0) (hp : p≠0) (hs : Supported (Ideal.span {p}))
    (hpp : lambda^2 ∣ p-1) (hmLam : lambda∣m) (hm2 : (2:O)∣m) (k : ℕ) :
    ∃ τ : RayCharacter → Character,
      (∀ χ, (τ χ).modulus.absNorm≤ rowConductorBound (childCharacter η χ) m 1 (p^(2*k))) ∧
      ∀ I : Ideal O,Supported I → ∀ t : ℝ,
        rowWeight η m 1 1 t I*residualCharacter p k (primaryIdealGenerator I)=
          ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I := by
  choose τ hN hτ using fun χ : RayCharacter =>
    exists_second_height_character η χ m (p^(2*k)) hm (pow_ne_zero _ hp) hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro I hI t
  have hn := supported_primaryIdealGenerator_ne_zero I hI
  have hgen : Supported (Ideal.span {primaryIdealGenerator I}) := by
    rw [primary_span_supported I hI];exact hI
  rw [residualCharacter_moving p _ k hs hgen hpp (primaryIdealGenerator_spec I hn).2,
    primary_span_supported I hI,amplificationPhase_expansion p _ k hgen]
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [hτ χ I hI t]
  ring

theorem original_column_family (η : Character) (m p : O) (k : ℕ)
    (τ : RayCharacter → Character)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      rowWeight η m 1 1 t I*residualCharacter p k (primaryIdealGenerator I)=
        ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I)
    (C I : Ideal O) (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) :
    (β (C*I)*rowWeight η m 1 1 t (C*I))*residualCharacter p k (primaryIdealGenerator I)=
      rowWeight η m 1 1 t C *
        ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*(β (C*I)*heightCoeff (τ χ) t I) := by
  rw [map_mul]
  calc
    _ = rowWeight η m 1 1 t C *
      (β (C*I)*(rowWeight η m 1 1 t I*residualCharacter p k (primaryIdealGenerator I))) := by ring
    _ = _ := by rw [hτ I hI t,Finset.mul_sum];congr 1;apply Finset.sum_congr rfl;intro χ hχ;ring

end CenteredMomentAmplificationFamily

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

/-
First annular majorants adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.HarmonicMassesAndNonexceptionalPrefactors

/-!
# First annular majorants

Annular majorant profiles and weights, mixed allowances and extracted allowances; common
energies and allocated data of the first physical source; fixed reference pairs of the mixed
root.
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

namespace CenteredMomentFirstPhysicalSource
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentAmplificationLiveMask CenteredMomentLiveDomain CenteredMomentRemainingBox
open CenteredMomentGaussEnergy CenteredMomentSourceAllocationEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentSecondHeightFamily CenteredMomentCommonPuncture CenteredMomentOriginalChildEnergy
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def allocatedData (D:OriginalData ι)(C L:Ideal O)(B:actualAllocations D.S C):
    OriginalData (liveIndices B.val) where
  S:=remainingSets B.val (fun i=> residualPool (B.val i)
    ((allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1 i) (D.S i))
  R:=D.R*C
  s:=L
  nu:=fun i=> D.nu i.val
  slot:=fun i=> D.slot i.val
  lengths:=fun i=> D.lengths i.val
  W₁:=D.W₁
  W₂:=D.W₂
  X₁:=D.X₁
  X₂:=D.X₂
  Y₁:=D.Y₁
  Y₂:=D.Y₂
  B₁:=D.B₁*B.val (Sum.inr 0)
  B₂:=D.B₂*B.val (Sum.inr 1)

lemma allocated_pools (D:OriginalData ι)(C L:Ideal O)(B:actualAllocations D.S C):
    Fintype.piFinset (allocatedData D C L B).S=
      liveBox D.S B.val (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1:=rfl

lemma allocated_profile (D:OriginalData ι)(C L:Ideal O)(B:actualAllocations D.S C):
    (allocatedData D C L B).profile=maskedLiveProfile B.val C D.R L D.nu D.slot D.lengths
      D.W₁ D.W₂ D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂:=rfl

def commonGauss (D:OriginalData ι)(C:Ideal O)(hC:Supported C)(τ:Character)(t:ℝ)(L:Ideal O)(z:O):ℂ:=
  let Q:=residualPool C hC.1 D.columns
  gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I:supportedColumns Q=>(if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O)
      then D.beta (C*I) else 0)*heightCoeff τ t I) z

theorem common_gauss_allocation (D:OriginalData ι)
    (hS:∀i,∀I∈D.S i,I≠0)(hp:∀i,∀I∈D.S (Sum.inl i),Prime I)
    (C:Ideal O)(hC:Supported C)(hseed:D.s∣C)(τ:Character)(t:ℝ)(L:Ideal O)(z:O):
    commonGauss D C hC τ t L z=
      ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
        gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported (allocatedData D C L B).columns)
          (fun I=>((allocatedData D C L B).beta I)*heightCoeff τ t I) z:=by
  let Q:=residualPool C hC.1 D.columns
  let b:=fun B:actualAllocations D.S C=> frozenCoefficient B.val C D.R D.nu D.slot D.lengths
  let d:=fun (B:actualAllocations D.S C)(I:supportedColumns Q)=>
    finiteColumnCoefficient (liveBox D.S B.val (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1)
      (liveProfile B.val C D.R D.nu D.slot D.lengths D.W₁ D.W₂ D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂) I*
        ((if L∣(I:Ideal O) then 1 else 0)*heightCoeff τ t I)
  have he (I:supportedColumns Q):
      (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I=
        ∑B,b B*d B I:=by
    have hc:=original_source_punctured_column D.S hS hp C D.R D.s I hC.1
      (Finset.mem_filter.mp I.property).2.1 hseed D.nu D.slot D.lengths D.W₁ D.W₂
      D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂
    change (if IsCoprime C (I:Ideal O) then D.beta (C*I) else 0)=_ at hc
    by_cases hl:L∣(I:Ideal O)
    · simp only [hl,and_true]
      change (if IsCoprime C (I:Ideal O) then _ else 0)*heightCoeff τ t I=_
      rw [hc,Finset.sum_mul]
      simp only [b,d,hl,ite_true,one_mul,mul_assoc]
    · simp only [hl,and_false,ite_false,zero_mul,b,d,mul_zero,Finset.sum_const_zero]
  unfold commonGauss
  change gaussPolynomial Finset.univ (sourceGenerator Q) _ _ z=_
  rw [funext he,gaussPolynomial_allocation]
  apply Finset.sum_congr rfl
  intro B hB
  apply congrArg (fun w:ℂ=> b B*w)
  have hh:=live_gaussPolynomial D.S hS hp B.val
    (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1 C D.R hC
    (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
    D.nu D.slot D.lengths D.W₁ D.W₂ D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂
    (fun I=>(if L∣I then 1 else 0)*heightCoeff τ t I) z
  change gaussPolynomial Finset.univ (sourceGenerator Q) _ (d B) z=_ at hh
  rw [hh]
  congr 1
  funext I
  change _=finiteColumnCoefficient _ (allocatedData D C L B).profile I*heightCoeff τ t I
  rw [allocated_profile,maskedLiveProfile,column_mask]
  dsimp only [liveProfile]
  rw [allocated_pools]
  ring

theorem normalized_common_gauss_allocation (D:OriginalData ι)
    (hS:∀i,∀I∈D.S i,I≠0)(hp:∀i,∀I∈D.S (Sum.inl i),Prime I)
    (C:Ideal O)(hC:Supported C)(hseed:D.s∣C)(τ:Character)(t T:ℝ)(L:Ideal O)(z:O):
    (Real.sqrt T:ℂ)⁻¹*commonGauss D C hC τ t L z=
      ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
        gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported (allocatedData D C L B).columns)
          ((allocatedData D C L B).coefficient τ fixedBadMask t T) z:=by
  rw [common_gauss_allocation D hS hp C hC hseed τ t L z,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  simp only [OriginalData.coefficient,gaussPolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [heightCoeff_eq_fixed_rowWeight τ t I (Finset.mem_filter.mp I.property).2]
  ring

end CenteredMomentFirstPhysicalSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstPhysicalSource
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentSecondSectorColumns CenteredMomentFirstSectorTransform 
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors CenteredMomentLiveDomain
open CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentChildAssembly
local notation "O"=> Eisenstein.O

theorem columns_gauss_polynomial (C:Ideal O)(hC:Supported C)(S:Finset (Ideal O))
    (f:Ideal O→ℂ)(z:O):
    gaussPolynomial Finset.univ (element C C hC.1 S) (element_supported C C hC.1 S)
      (fun a=> f a) z=
    gaussPolynomial Finset.univ (sourceGenerator (residualPool C hC.1 S))
      (sourceGenerator_supported _) (fun I=> if IsCoprime C (I:Ideal O) then f I else 0) z:=by
  rw [source_gaussPolynomial (residualPool C hC.1 S)
    (fun I=> if IsCoprime C I then f I else 0) z,supported_residualPool C hC S]
  have he (a:columns C C hC.1 S):
      gaussRow (element C C hC.1 S a) (element_supported C C hC.1 S a) z=
        primaryGaussRow a z:=by
    rw [primaryGaussRow,dif_pos (column_supported C C hC.1 S a)]
    rfl
  simp only [gaussPolynomial,he]
  rw [Finset.sum_coe_sort (columns C C hC.1 S) (fun I=> f I*primaryGaussRow I z)]
  unfold columns
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs <;> simp

theorem columns_gauss_polynomial_filter (Q C:Ideal O)(hC:Supported C)(S:Finset (Ideal O))
    (f:Ideal O→ℂ)(z:O):
    gaussPolynomial Finset.univ (element Q C hC.1 S) (element_supported Q C hC.1 S)
      (fun a=> f a) z=
    gaussPolynomial Finset.univ (sourceGenerator (residualPool C hC.1 S))
      (sourceGenerator_supported _) (fun I=> if IsCoprime Q (I:Ideal O) then f I else 0) z:=by
  rw [source_gaussPolynomial (residualPool C hC.1 S)
    (fun I=> if IsCoprime Q I then f I else 0) z,supported_residualPool C hC S]
  have he (a:columns Q C hC.1 S):
      gaussRow (element Q C hC.1 S a) (element_supported Q C hC.1 S a) z=
        primaryGaussRow a z:=by
    rw [primaryGaussRow,dif_pos (column_supported Q C hC.1 S a)]
    rfl
  simp only [gaussPolynomial,he]
  rw [Finset.sum_coe_sort (columns Q C hC.1 S) (fun I=> f I*primaryGaussRow I z)]
  unfold columns
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs <;> simp

variable {ι:Type*}[Fintype ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem first_column_original_data (D:OriginalData ι)
    (hS:∀i,∀I∈D.S i,I≠0)(hp:∀i,∀I∈D.S (Sum.inl i),Prime I)
    (C:Ideal O)(hC:Supported C)(hseed:D.s∣C)(τ:Character)(t T:ℝ)(L:Ideal O)
    (a:columns C C hC.1 D.columns→ℂ)
    (ha:∀I:columns C C hC.1 D.columns,
      a I=(if L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I)(z:O):
    (Real.sqrt T:ℂ)⁻¹*gaussPolynomial Finset.univ (element C C hC.1 D.columns)
      (element_supported C C hC.1 D.columns) a z=
      ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
        gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported (allocatedData D C L B).columns)
          ((allocatedData D C L B).coefficient τ fixedBadMask t T) z:=by
  rw [funext ha,columns_gauss_polynomial C hC D.columns
    (fun I=>(if L∣I then D.beta (C*I) else 0)*heightCoeff τ t I) z]
  have he:(fun I:supportedColumns (residualPool C hC.1 D.columns)=>
      if IsCoprime C (I:Ideal O) then
        (if L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I else 0)=
      (fun I:supportedColumns (residualPool C hC.1 D.columns)=>
        (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I):=by
    funext I
    by_cases hc:IsCoprime C (I:Ideal O) <;> by_cases hl:L∣(I:Ideal O) <;> simp [hc,hl]
  rw [he]
  exact normalized_common_gauss_allocation D hS hp C hC hseed τ t T L z

theorem first_column_original_data_filter (D:OriginalData ι)
    (hS:∀i,∀I∈D.S i,I≠0)(hp:∀i,∀I∈D.S (Sum.inl i),Prime I)
    (Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)(hQC:primeSupport Q=primeSupport C)
    (hseed:D.s∣C)(τ:Character)(t T:ℝ)(L:Ideal O)
    (a:columns Q C hC.1 D.columns→ℂ)
    (ha:∀I:columns Q C hC.1 D.columns,
      a I=(if L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I)(z:O):
    (Real.sqrt T:ℂ)⁻¹*gaussPolynomial Finset.univ (element Q C hC.1 D.columns)
      (element_supported Q C hC.1 D.columns) a z=
      ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
        gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported (allocatedData D C L B).columns)
          ((allocatedData D C L B).coefficient τ fixedBadMask t T) z:=by
  rw [funext ha,columns_gauss_polynomial_filter Q C hC D.columns
    (fun I=>(if L∣I then D.beta (C*I) else 0)*heightCoeff τ t I) z]
  have he:(fun I:supportedColumns (residualPool C hC.1 D.columns)=>
      if IsCoprime Q (I:Ideal O) then
        (if L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I else 0)=
      (fun I:supportedColumns (residualPool C hC.1 D.columns)=>
        (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I):=by
    funext I
    rw [coprime_of_same_support Q C I hQ hC.1 (Finset.mem_filter.mp I.property).2.1 hQC]
    by_cases hc:IsCoprime C (I:Ideal O) <;> by_cases hl:L∣(I:Ideal O) <;> simp [hc,hl]
  rw [he]
  exact normalized_common_gauss_allocation D hS hp C hC hseed τ t T L z

end CenteredMomentFirstPhysicalSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstPhysicalSource
open HeckeFamily CanonicalQuadraticSieve 
open CenteredMomentFirstAmplificationChoice CenteredMomentSourceRow
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCommonSupport
open CenteredMomentGaussEnergy CenteredMomentFirstColumns CenteredMomentChildAssembly
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentSecondHeightFamily
open RayFourExpansion  Eisenstein CenteredMomentHeckeExpansion
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι]
local instance firstCanonicalDataDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def allocatedPolynomial (s:OriginalData ι)(C L:Ideal O)(τ:Character)(t T:ℝ)(z:O):ℂ:=
  ∑B:actualAllocations s.S C,frozenCoefficient B.val C s.R s.nu s.slot s.lengths*
    gaussPolynomial Finset.univ (sourceGenerator (allocatedData s C L B).columns)
      (sourceGenerator_supported (allocatedData s C L B).columns)
      ((allocatedData s C L B).coefficient τ fixedBadMask t T) z

def leftChild (s:OriginalData ι)(η:Character)(m:O)(t:ℝ)
    (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))
    (χ:RayCharacter)(L:Ideal O)(z:O):ℂ:=
  let e:=TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E
  let r:=activeConductor C D
  let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
  gaussPolynomial Finset.univ (element C C hC.1 s.columns) (element_supported C C hC.1 s.columns)
    (divisorCoefficient L (element C C hC.1 s.columns)
      (fun a=> coefficient η m 1 t s.beta C a*leftCoefficient e r ρ (element C C hC.1 s.columns a)) χ) z

def rightChild (s:OriginalData ι)(η:Character)(m:O)(t:ℝ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (χ:RayCharacter)(L:Ideal O)(z:O):ℂ:=
  let e:=TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E
  let r:=activeConductor C D
  let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
  gaussPolynomial Finset.univ (element C D hD.1 s.columns) (element_supported C D hD.1 s.columns)
    (divisorCoefficient L (element C D hD.1 s.columns)
      (fun a=> coefficient η m 1 t s.beta D a*rightCoefficient e r ρ (element C D hD.1 s.columns a)) χ) z

theorem actual_canonical_original_data (η:Character)(m:O)(hm:m≠0)
    (hmLam:lambda∣m)(hm2:(2:O)∣m)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayCharacter):
    let e:=TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E;
    let M:=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*activeConductor C D};
    ∃τ₁ τ₂:Character,τ₁.modulus=M ∧ τ₂.modulus=M ∧
      ∀s:OriginalData ι,(∀i,∀I∈s.S i,I≠0)→(∀i,∀I∈s.S (Sum.inl i),Prime I)→
      s.s∣C→s.s∣D→∀t T:ℝ,∀L:Ideal O,∀z:O,
        (Real.sqrt T:ℂ)⁻¹*leftChild s η m t C D hC E ξ₁ L z=
          allocatedPolynomial s C L τ₁ t T z ∧
        (Real.sqrt T:ℂ)⁻¹*rightChild s η m t C D hC hD E ξ₂ L (-z)=
          allocatedPolynomial s D L τ₂ t T (-z):=by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩:=actual_child_family η m hm hmLam hm2 C D hC hD E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,?_⟩
  intro s hS hp hsC hsD t T L z
  constructor
  · exact first_column_original_data s hS hp C hC hsC τ₁ t T L _
      (h₁ s.columns s.beta t L) z
  · exact first_column_original_data_filter s hS hp C D hC.1 hD hCD hsD τ₂ t T L _
      (h₂ s.columns s.beta t L) (-z)

end CenteredMomentFirstPhysicalSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory

namespace CenteredMomentFirstPhysicalSource
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentSmooth
open JointLogSeparation
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι]
local instance firstWindowDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma generator_span (S:Finset (Ideal O))(I:supportedColumns S):
    Ideal.span {sourceGenerator S I}=(I:Ideal O):=
  primary_span_supported I (Finset.mem_filter.mp I.property).2

def commonWindow (D:OriginalData ι)(C:Ideal O)(hC:Supported C)(τ:Character)
    (t θ X:ℝ)(V:ℝ→ℂ)(L:Ideal O)(z:O):ℂ:=
  let Q:=residualPool C hC.1 D.columns
  gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I:supportedColumns Q=>(if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O)
      then D.beta (C*I) else 0)*heightCoeff τ t I*
      columnPhase V (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ) z

theorem common_window_original_integral (D:OriginalData ι)
    (hS:∀i,∀I∈D.S i,I≠0)(hp:∀i,∀I∈D.S (Sum.inl i),Prime I)
    (C:Ideal O)(hC:Supported C)(hseed:D.s∣C)(τ:Character)(t T θ X:ℝ)(hX:0< X)
    (V:ℝ→ℂ)(hVc:HasCompactSupport V)(hVs:ContDiff ℝ ∞ V)(L:Ideal O)(z:O):
    (Real.sqrt T:ℂ)⁻¹*commonWindow D C hC τ t θ X V L z=
      ∫w:ℝ,columnDensity V hVc hVs w*kernelLogPhase (θ-w) (Real.log X)*
        ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
          gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
            (sourceGenerator_supported (allocatedData D C L B).columns)
            ((allocatedData D C L B).coefficient τ fixedBadMask
              (t+2*Real.pi*(w-θ)) T) z:=by
  let Q:=residualPool C hC.1 D.columns
  let β:=fun I:supportedColumns Q=> if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O)
    then D.beta (C*I) else 0
  have hh:=gauss_column_integral Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    β τ t θ X hX V hVc hVs z
  simp only [generator_span] at hh
  change commonWindow D C hC τ t θ X V L z=
    ∫w:ℝ,columnDensity V hVc hVs w*kernelLogPhase (θ-w) (Real.log X)*
      commonGauss D C hC τ (t+2*Real.pi*(w-θ)) L z at hh
  rw [hh,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with w
  have he:=normalized_common_gauss_allocation D hS hp C hC hseed τ
    (t+2*Real.pi*(w-θ)) T L z
  rw [←he]
  ring

theorem common_window_original_integrable (D:OriginalData ι)
    (hS:∀i,∀I∈D.S i,I≠0)(hp:∀i,∀I∈D.S (Sum.inl i),Prime I)
    (C:Ideal O)(hC:Supported C)(hseed:D.s∣C)(τ:Character)(t T θ X:ℝ)(hX:0< X)
    (V:ℝ→ℂ)(hVc:HasCompactSupport V)(hVs:ContDiff ℝ ∞ V)(L:Ideal O)(z:O):
    Integrable (fun w:ℝ=> columnDensity V hVc hVs w*kernelLogPhase (θ-w) (Real.log X)*
      ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
        gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported (allocatedData D C L B).columns)
          ((allocatedData D C L B).coefficient τ fixedBadMask (t+2*Real.pi*(w-θ)) T) z):=by
  let Q:=residualPool C hC.1 D.columns
  let β:=fun I:supportedColumns Q=> if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O)
    then D.beta (C*I) else 0
  have hh:=(CenteredMomentHeckeWindowEnergy.gauss_column_integrable Finset.univ
    (sourceGenerator Q) (sourceGenerator_supported Q) β τ t θ X hX V hVc hVs z).const_mul
      ((Real.sqrt T:ℂ)⁻¹)
  simp only [generator_span] at hh
  convert hh using 1
  funext w
  rw [←normalized_common_gauss_allocation D hS hp C hC hseed τ (t+2*Real.pi*(w-θ)) T L z]
  change _=(Real.sqrt T:ℂ)⁻¹*(columnDensity V hVc hVs w*kernelLogPhase (θ-w) (Real.log X)*
    commonGauss D C hC τ (t+2*Real.pi*(w-θ)) L z)
  ring

end CenteredMomentFirstPhysicalSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory

namespace CenteredMomentFirstPhysicalSource
open Eisenstein   HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentGaussEnergy CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentSecondSectorColumns CenteredMomentConjugateWindow
open CenteredMomentSecondHeightFamily CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentFirstColumns CenteredMomentChildAssembly CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentCommonSupport RayFourExpansion 
open JointLogSeparation
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι]
local instance firstWindowColumnsDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma element_norm (Q C:Ideal O)(hC:C≠0)(S:Finset (Ideal O))(I:columns Q C hC S):
    ‖ringComplex (element Q C hC S I)‖^2=(Ideal.absNorm (I:Ideal O):ℝ):=by
  rw [ringComplex_norm_sq_eq_absNorm_span,element_span]

theorem column_window_common (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t θ X:ℝ)(V:ℝ→ℂ)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)(z:O):
    gaussPolynomial Finset.univ (element Q C hC.1 s.columns)
      (element_supported Q C hC.1 s.columns)
      (fun I=> a I*columnPhase V
        (Real.log (‖ringComplex (element Q C hC.1 s.columns I)‖^2/X)) θ) z=
        commonWindow s C hC τ t θ X V L z:=by
  simp only [ha,element_norm]
  rw [columns_gauss_polynomial_filter Q C hC s.columns
    (fun I=>(if L∣I then s.beta (C*I) else 0)*heightCoeff τ t I*
      columnPhase V (Real.log ((Ideal.absNorm I:ℝ)/X)) θ) z]
  unfold commonWindow
  congr 1
  funext I
  rw [coprime_of_same_support Q C I hQ hC.1 (Finset.mem_filter.mp I.property).2.1 hQC]
  by_cases hc:IsCoprime C (I:Ideal O) <;> by_cases hl:L∣(I:Ideal O) <;> simp [hc,hl]

theorem column_window_original_integral (s:OriginalData ι)
    (hS:∀i,∀I∈s.S i,I≠0)(hp:∀i,∀I∈s.S (Sum.inl i),Prime I)
    (Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)(hQC:primeSupport Q=primeSupport C)
    (hseed:s.s∣C)(τ:Character)(t T θ X:ℝ)(hX:0< X)
    (V:ℝ→ℂ)(hVc:HasCompactSupport V)(hVs:ContDiff ℝ ∞ V)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)(z:O):
    (Real.sqrt T:ℂ)⁻¹*gaussPolynomial Finset.univ (element Q C hC.1 s.columns)
      (element_supported Q C hC.1 s.columns)
      (fun I=> a I*columnPhase V
        (Real.log (‖ringComplex (element Q C hC.1 s.columns I)‖^2/X)) θ) z=
      ∫w:ℝ,columnDensity V hVc hVs w*kernelLogPhase (θ-w) (Real.log X)*
        allocatedPolynomial s C L τ (t+2*Real.pi*(w-θ)) T z:=by
  rw [column_window_common s Q C hQ hC hQC τ t θ X V L a ha z]
  exact common_window_original_integral s hS hp C hC hseed τ t T θ X hX V hVc hVs L z

theorem column_star_window_original_integral (s:OriginalData ι)
    (hS:∀i,∀I∈s.S i,I≠0)(hp:∀i,∀I∈s.S (Sum.inl i),Prime I)
    (Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)(hQC:primeSupport Q=primeSupport C)
    (hseed:s.s∣C)(τ:Character)(t T θ X:ℝ)(hX:0< X)
    (V:ℝ→ℂ)(hVc:HasCompactSupport V)(hVs:ContDiff ℝ ∞ V)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)(z:O):
    (Real.sqrt T:ℂ)⁻¹*gaussPolynomial Finset.univ (element Q C hC.1 s.columns)
      (element_supported Q C hC.1 s.columns)
      (fun I=> a I*star (columnPhase V
        (Real.log (‖ringComplex (element Q C hC.1 s.columns I)‖^2/X)) θ)) (-z)=
      ∫w:ℝ,columnDensity (fun x=> star (V x)) (conjugate_compact V hVc)
        (conjugate_smooth V hVs) w*kernelLogPhase (-θ-w) (Real.log X)*
        allocatedPolynomial s C L τ (t+2*Real.pi*(w-(-θ))) T (-z):=by
  simp only [star_columnPhase]
  exact column_window_original_integral s hS hp Q C hQ hC hQC hseed τ t T (-θ) X hX
    (fun x=> star (V x)) (conjugate_compact V hVc) (conjugate_smooth V hVs) L a ha (-z)

end CenteredMomentFirstPhysicalSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory

namespace CenteredMomentFirstPhysicalSource
open Eisenstein   HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentGaussEnergy CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentSecondSectorColumns CenteredMomentConjugateWindow
open CenteredMomentSecondHeightFamily CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentFirstColumns CenteredMomentChildAssembly CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentCommonSupport RayFourExpansion 
open JointLogSeparation
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι]
local instance firstWindowCanonicalDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def leftWindowChild (s:OriginalData ι)(η:Character)(m:O)(t:ℝ)
    (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))
    (χ:RayCharacter)(L:Ideal O)(θ X:ℝ)(V:ℝ→ℂ)(z:O):ℂ:=
  let e:=TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E
  let r:=activeConductor C D
  let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
  gaussPolynomial Finset.univ (element C C hC.1 s.columns) (element_supported C C hC.1 s.columns)
    (fun I=> divisorCoefficient L (element C C hC.1 s.columns)
      (fun a=> coefficient η m 1 t s.beta C a*leftCoefficient e r ρ (element C C hC.1 s.columns a)) χ I*
      columnPhase V (Real.log (‖ringComplex (element C C hC.1 s.columns I)‖^2/X)) θ) z

def rightWindowChild (s:OriginalData ι)(η:Character)(m:O)(t:ℝ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (χ:RayCharacter)(L:Ideal O)(θ X:ℝ)(V:ℝ→ℂ)(z:O):ℂ:=
  let e:=TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E
  let r:=activeConductor C D
  let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
  gaussPolynomial Finset.univ (element C D hD.1 s.columns) (element_supported C D hD.1 s.columns)
    (fun I=> divisorCoefficient L (element C D hD.1 s.columns)
      (fun a=> coefficient η m 1 t s.beta D a*rightCoefficient e r ρ (element C D hD.1 s.columns a)) χ I*
      star (columnPhase V (Real.log (‖ringComplex (element C D hD.1 s.columns I)‖^2/X)) θ)) z

theorem actual_canonical_window_integrals (η:Character)(m:O)(hm:m≠0)
    (hmLam:lambda∣m)(hm2:(2:O)∣m)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayCharacter):
    let e:=TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E;
    let M:=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*activeConductor C D};
    ∃τ₁ τ₂:Character,τ₁.modulus=M ∧ τ₂.modulus=M ∧
      ∀s:OriginalData ι,(∀i,∀I∈s.S i,I≠0)→(∀i,∀I∈s.S (Sum.inl i),Prime I)→
      s.s∣C→s.s∣D→∀t T θ X Y:ℝ,0< X→0< Y→
      ∀V₁:ℝ→ℂ,∀hV₁c:HasCompactSupport V₁,∀hV₁s:ContDiff ℝ ∞ V₁,
      ∀V₂:ℝ→ℂ,∀hV₂c:HasCompactSupport V₂,∀hV₂s:ContDiff ℝ ∞ V₂,
      ∀L:Ideal O,∀z:O,
        (Real.sqrt T:ℂ)⁻¹*leftWindowChild s η m t C D hC E ξ₁ L θ X V₁ z=
          (∫w:ℝ,columnDensity V₁ hV₁c hV₁s w*kernelLogPhase (θ-w) (Real.log X)*
            allocatedPolynomial s C L τ₁ (t+2*Real.pi*(w-θ)) T z) ∧
        (Real.sqrt T:ℂ)⁻¹*rightWindowChild s η m t C D hC hD E ξ₂ L θ Y V₂ (-z)=
          (∫w:ℝ,columnDensity (fun x=> star (V₂ x)) (conjugate_compact V₂ hV₂c)
            (conjugate_smooth V₂ hV₂s) w*kernelLogPhase (-θ-w) (Real.log Y)*
            allocatedPolynomial s D L τ₂ (t+2*Real.pi*(w-(-θ))) T (-z)):=by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩:=actual_child_family η m hm hmLam hm2 C D hC hD E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,?_⟩
  intro s hS hp hsC hsD t T θ X Y hX hY V₁ hV₁c hV₁s V₂ hV₂c hV₂s L z
  constructor
  · exact column_window_original_integral s hS hp C C hC.1 hC rfl hsC τ₁ t T θ X hX
      V₁ hV₁c hV₁s L _ (h₁ s.columns s.beta t L) z
  · exact column_star_window_original_integral s hS hp C D hC.1 hD hCD hsD τ₂ t T θ Y hY
      V₂ hV₂c hV₂s L _ (h₂ s.columns s.beta t L) z

end CenteredMomentFirstPhysicalSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace CenteredMomentFirstPhysicalSource
open Eisenstein  HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentGaussEnergy CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeWindowEnergy CenteredMomentSmoothedWindowEnergy
open CenteredMomentSecondSectorColumns CenteredMomentConjugateWindow 
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι]
local instance firstWindowEnergyDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def commonEnergy (s:OriginalData ι)(C:Ideal O)(hC:Supported C)(τ:Character)
    (t:ℝ)(L:Ideal O)(U:𝓢(ℝ,ℂ))(K:ℝ):ℂ:=
  let Q:=residualPool C hC.1 s.columns
  gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I:supportedColumns Q=>(if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O)
      then s.beta (C*I) else 0)*heightCoeff τ t I) U K

lemma column_unwindowed_common (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t:ℝ)(L:Ideal O)(z:O):
    gaussPolynomial Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=>(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I) z=
      commonGauss s C hC τ t L z:=by
  rw [columns_gauss_polynomial_filter Q C hC s.columns
    (fun I=>(if L∣I then s.beta (C*I) else 0)*heightCoeff τ t I) z]
  unfold commonGauss
  congr 1
  funext I
  rw [coprime_of_same_support Q C I hQ hC.1 (Finset.mem_filter.mp I.property).2.1 hQC]
  by_cases hc:IsCoprime C (I:Ideal O) <;> by_cases hl:L∣(I:Ideal O) <;> simp [hc,hl]

theorem column_unwindowed_energy (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t:ℝ)(L:Ideal O)(U:𝓢(ℝ,ℂ))(K:ℝ):
    gaussEnergy Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=>(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I) U K=
      commonEnergy s C hC τ t L U K:=by
  unfold gaussEnergy commonEnergy
  apply tsum_congr
  intro z
  rw [column_unwindowed_common s Q C hQ hC hQC τ t L z]
  rfl

theorem column_window_energy (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t θ X:ℝ)(hX:0< X)
    (V:ℝ→ℂ)(hVc:HasCompactSupport V)(hVs:ContDiff ℝ ∞ V)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)
    (U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0< K)(hU:∀z:O,0≤(U (‖ringComplex z‖^2/K)).re)
    (J:ℕ)(E:ℝ)(hE:0≤ E)
    (henergy:∀v:ℝ,(commonEnergy s C hC τ v L U K).re≤ E*(1+‖v‖)^(2*J)):
    (gaussEnergy Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=> a I*columnPhase V
        (Real.log (‖ringComplex (element Q C hC.1 s.columns I)‖^2/X)) θ) U K).re≤
      (E*heightCost t θ^(2*J))*(∫w:ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2:=by
  have hh:=smoothed_window_energy_from_height V hVc hVs J Finset.univ
    (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
    (fun I:columns Q C hC.1 s.columns=> if L∣(I:Ideal O) then s.beta (C*I) else 0)
    τ t θ X hX U K hK hU E hE (fun v=> by
      simp only [element_span]
      rw [column_unwindowed_energy s Q C hQ hC hQC]
      exact henergy v)
  simpa only [ha,element_span,element_norm] using hh

theorem column_star_window_energy (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t θ X:ℝ)(hX:0< X)
    (V:ℝ→ℂ)(hVc:HasCompactSupport V)(hVs:ContDiff ℝ ∞ V)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)
    (U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0< K)(hU:∀z:O,0≤(U (‖ringComplex z‖^2/K)).re)
    (J:ℕ)(E:ℝ)(hE:0≤ E)
    (henergy:∀v:ℝ,(commonEnergy s C hC τ v L U K).re≤ E*(1+‖v‖)^(2*J)):
    (gaussEnergy Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=> a I*star (columnPhase V
        (Real.log (‖ringComplex (element Q C hC.1 s.columns I)‖^2/X)) θ)) U K).re≤
      (E*heightCost t (-θ)^(2*J))*(∫w:ℝ,(1+‖w‖)^J*
        ‖columnDensity (fun x=> star (V x)) (conjugate_compact V hVc) (conjugate_smooth V hVs) w‖)^2:=by
  simp only [star_columnPhase]
  exact column_window_energy s Q C hQ hC hQC τ t (-θ) X hX
    (fun x=> star (V x)) (conjugate_compact V hVc) (conjugate_smooth V hVs)
    L a ha U K hK hU J E hE henergy

end CenteredMomentFirstPhysicalSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace CenteredMomentFirstPhysicalSource
open Eisenstein  HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice
open CenteredMomentGaussEnergy CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentLogDyadic CenteredMomentSecondWindowSource CenteredMomentSecondWindowBudget
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι]

theorem column_dyadic_window_energy (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t θ X:ℝ)(hX:0< X)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)
    (U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0< K)(hU:∀z:O,0≤(U (‖ringComplex z‖^2/K)).re)
    (J:ℕ)(E:ℝ)(hE:0≤ E)
    (henergy:∀v:ℝ,(commonEnergy s C hC τ v L U K).re≤ E*(1+‖v‖)^(2*J)):
    (gaussEnergy Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=> a I*columnPhase logAnnulus
        (Real.log (‖ringComplex (element Q C hC.1 s.columns I)‖^2/X)) θ) U K).re≤
      (windowBudget J t E*(1+‖θ‖)^J)^2:=by
  exact (column_window_energy s Q C hQ hC hQC τ t θ X hX
    logAnnulus logAnnulus_compact logAnnulus_smooth L a ha U K hK hU J E hE henergy).trans
      (shifted_window_budget J t θ E hE)

theorem column_star_dyadic_window_energy (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t θ X:ℝ)(hX:0< X)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)
    (U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0< K)(hU:∀z:O,0≤(U (‖ringComplex z‖^2/K)).re)
    (J:ℕ)(E:ℝ)(hE:0≤ E)
    (henergy:∀v:ℝ,(commonEnergy s C hC τ v L U K).re≤ E*(1+‖v‖)^(2*J)):
    (gaussEnergy Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=> a I*star (columnPhase logAnnulus
        (Real.log (‖ringComplex (element Q C hC.1 s.columns I)‖^2/X)) θ)) U K).re≤
      (windowBudget J t E*(1+‖θ‖)^J)^2:=by
  simpa only [star_logAnnulus_column,norm_neg] using
    column_dyadic_window_energy s Q C hQ hC hQC τ t (-θ) X hX L a ha U K hK hU J E hE henergy

end CenteredMomentFirstPhysicalSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace CenteredMomentFirstPhysicalSource
open Eisenstein   HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSecondHeightFamily CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstColumns CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredMomentFirstMaskedFamily CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstNonexceptionalPrefactor CenteredMomentCommonSupport CenteredMomentConjugateWindow
open CenteredMomentChildAssembly RayFourExpansion CompletedGauss CenteredMomentGaussEnergy JointLogSeparation
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι]
local instance firstFixedSourceDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _

variable {η:Character}{C D:Ideal O}{hC:Supported C}
  {E:Finset (CommonIndex C D)}{ξ₁ ξ₂:RayCharacter}

theorem FixedPair.left_column (F:FixedPair η C D hC E ξ₁ ξ₂)(s:OriginalData ι)(t:ℝ)(L:Ideal O)
    (I:columns C C hC.1 s.columns):
    divisorCoefficient L (element C C hC.1 s.columns)
      (fun a=> coefficient η (fixedBadMask*cubicIdealGenerator s.R) 1 t s.beta C a*
        leftCoefficient (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)
          (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
            (activeExponent C D)) (element C C hC.1 s.columns a)) ξ₁ I=
      (if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff F.left t I:=
  fixed_divisor_column s η F.left C _ ξ₁ F.left_height L I
    (column_supported C C hC.1 s.columns I) t

theorem FixedPair.right_column (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (s:OriginalData ι)(t:ℝ)(L:Ideal O)(I:columns C D hD.1 s.columns):
    divisorCoefficient L (element C D hD.1 s.columns)
      (fun a=> coefficient η (fixedBadMask*cubicIdealGenerator s.R) 1 t s.beta D a*
        rightCoefficient (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)
          (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
            (activeExponent C D)) (element C D hD.1 s.columns a)) ξ₂ I=
      (if L∣(I:Ideal O) then s.beta (D*I) else 0)*heightCoeff F.right t I:=
  fixed_divisor_column s η F.right D _ ξ₂ F.right_height L I
    (column_supported C D hD.1 s.columns I) t

theorem FixedPair.original_data (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(s:OriginalData ι)
    (hS:∀i,∀I∈s.S i,I≠0)(hp:∀i,∀I∈s.S (Sum.inl i),Prime I)(hsC:s.s∣C)(hsD:s.s∣D)
    (t T:ℝ)(L:Ideal O)(z:O):
    (Real.sqrt T:ℂ)⁻¹*leftChild s η (fixedBadMask*cubicIdealGenerator s.R) t C D hC E ξ₁ L z=
      allocatedPolynomial s C L F.left t T z ∧
    (Real.sqrt T:ℂ)⁻¹*rightChild s η (fixedBadMask*cubicIdealGenerator s.R) t C D hC hD E ξ₂ L (-z)=
      allocatedPolynomial s D L F.right t T (-z):=by
  constructor
  · exact first_column_original_data s hS hp C hC hsC F.left t T L _ (F.left_column s t L) z
  · exact first_column_original_data_filter s hS hp C D hC.1 hD hCD hsD F.right t T L _
      (F.right_column hD s t L) (-z)

theorem FixedPair.window_integrals (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(s:OriginalData ι)
    (hS:∀i,∀I∈s.S i,I≠0)(hp:∀i,∀I∈s.S (Sum.inl i),Prime I)(hsC:s.s∣C)(hsD:s.s∣D)
    (t T θ X Y:ℝ)(hX:0< X)(hY:0< Y)
    (V₁:ℝ→ℂ)(hV₁c:HasCompactSupport V₁)(hV₁s:ContDiff ℝ ∞ V₁)
    (V₂:ℝ→ℂ)(hV₂c:HasCompactSupport V₂)(hV₂s:ContDiff ℝ ∞ V₂)(L:Ideal O)(z:O):
    (Real.sqrt T:ℂ)⁻¹*leftWindowChild s η (fixedBadMask*cubicIdealGenerator s.R) t C D hC E ξ₁ L θ X V₁ z=
      (∫w:ℝ,columnDensity V₁ hV₁c hV₁s w*kernelLogPhase (θ-w) (Real.log X)*
        allocatedPolynomial s C L F.left (t+2*Real.pi*(w-θ)) T z) ∧
    (Real.sqrt T:ℂ)⁻¹*rightWindowChild s η (fixedBadMask*cubicIdealGenerator s.R) t C D hC hD E ξ₂ L θ Y V₂ (-z)=
      (∫w:ℝ,columnDensity (fun x=> star (V₂ x)) (conjugate_compact V₂ hV₂c)
        (conjugate_smooth V₂ hV₂s) w*kernelLogPhase (-θ-w) (Real.log Y)*
        allocatedPolynomial s D L F.right (t+2*Real.pi*(w-(-θ))) T (-z)):=by
  constructor
  · exact column_window_original_integral s hS hp C C hC.1 hC rfl hsC F.left t T θ X hX
      V₁ hV₁c hV₁s L _ (F.left_column s t L) z
  · exact column_star_window_original_integral s hS hp C D hC.1 hD hCD hsD F.right t T θ Y hY
      V₂ hV₂c hV₂s L _ (F.right_column hD s t L) z

theorem FixedPair.scalar_conductors (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (K A₀ B₀ a T M:ℝ)(hK:0< K)(hA:0< A₀)(hB:0< B₀)(ha:0< a)(hT:0< T)
    (hl:a*T≤(C.absNorm:ℝ)*Real.exp M*A₀)(hr:a*T≤(D.absNorm:ℝ)*Real.exp M*B₀):
    ‖scalar C D hC E K A₀ B₀‖*T/((C.absNorm:ℝ)*D.absNorm)*
      Real.sqrt ((F.left.modulus.absNorm:ℝ)*F.right.modulus.absNorm)≤
      ‖inactiveWeight C D E‖*(Real.exp M/a)*fixedPresentationCost*K*(η.modulus.absNorm:ℝ)/
        (CenteredMomentRankinRadical.commonRadical C D).absNorm:=by
  exact actual_scalar_conductors C D hC hD E η F.left F.right K A₀ B₀ a T M fixedPresentationCost
    hK hA hB ha hT fixedPresentationCost_pos.le hl hr F.conductor_caps.1 F.conductor_caps.2

end CenteredMomentFirstPhysicalSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstPhysicalSource
open Eisenstein   HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport CenteredMomentGaussEnergy
open CenteredMomentLogDyadic CenteredMomentSecondWindowBudget RayFourExpansion CompletedGauss
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι]
variable {η:Character}{C D:Ideal O}{hC:Supported C}
  {E:Finset (CommonIndex C D)}{ξ₁ ξ₂:RayCharacter}

theorem FixedPair.left_common_energy (F:FixedPair η C D hC E ξ₁ ξ₂)(s:OriginalData ι)
    (t:ℝ)(L:Ideal O)(U:𝓢(ℝ,ℂ))(K:ℝ):
    (∑'z:O,((‖leftChild s η (fixedBadMask*cubicIdealGenerator s.R) t C D hC E ξ₁ L z‖^2:ℝ):ℂ)*
      U (‖ringComplex z‖^2/K))=commonEnergy s C hC F.left t L U K:=by
  change gaussEnergy Finset.univ (element C C hC.1 s.columns)
    (element_supported C C hC.1 s.columns) _ U K=_
  rw [funext (F.left_column s t L)]
  exact column_unwindowed_energy s C C hC.1 hC rfl F.left t L U K

theorem FixedPair.right_common_energy (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(s:OriginalData ι)(t:ℝ)(L:Ideal O)(U:𝓢(ℝ,ℂ))(K:ℝ):
    (∑'z:O,((‖rightChild s η (fixedBadMask*cubicIdealGenerator s.R) t C D hC hD E ξ₂ L z‖^2:ℝ):ℂ)*
      U (‖ringComplex z‖^2/K))=commonEnergy s D hD F.right t L U K:=by
  change gaussEnergy Finset.univ (element C D hD.1 s.columns)
    (element_supported C D hD.1 s.columns) _ U K=_
  rw [funext (F.right_column hD s t L)]
  exact column_unwindowed_energy s C D hC.1 hD hCD F.right t L U K

theorem FixedPair.right_reflected_common_energy (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(s:OriginalData ι)(t:ℝ)(L:Ideal O)(U:𝓢(ℝ,ℂ))(K:ℝ):
    (∑'z:O,((‖rightChild s η (fixedBadMask*cubicIdealGenerator s.R) t C D hC hD E ξ₂ L (-z)‖^2:ℝ):ℂ)*
      U (‖ringComplex z‖^2/K))=commonEnergy s D hD F.right t L U K:=by
  rw [←F.right_common_energy hD hCD s t L U K]
  simpa only [Equiv.neg_apply,map_neg,norm_neg] using (Equiv.neg O).tsum_eq
    (fun z:O=>((‖rightChild s η (fixedBadMask*cubicIdealGenerator s.R) t C D hC hD E ξ₂ L z‖^2:ℝ):ℂ)*
      U (‖ringComplex z‖^2/K))

theorem FixedPair.left_window_energy (F:FixedPair η C D hC E ξ₁ ξ₂)(s:OriginalData ι)
    (t θ X:ℝ)(hX:0< X)(L:Ideal O)(U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0< K)
    (hU:∀z:O,0≤(U (‖ringComplex z‖^2/K)).re)(J:ℕ)(B:ℝ)(hB:0≤ B)
    (hsource:∀v:ℝ,(commonEnergy s C hC F.left v L U K).re≤ B*(1+‖v‖)^(2*J)):
    (∑'z:O,((‖leftWindowChild s η (fixedBadMask*cubicIdealGenerator s.R) t C D hC E ξ₁ L θ X logAnnulus z‖^2:ℝ):ℂ)*
      U (‖ringComplex z‖^2/K)).re≤(windowBudget J t B*(1+‖θ‖)^J)^2:=by
  exact column_dyadic_window_energy s C C hC.1 hC rfl F.left t θ X hX L _
    (F.left_column s t L) U K hK hU J B hB hsource

theorem FixedPair.right_window_energy (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(s:OriginalData ι)(t θ X:ℝ)(hX:0< X)(L:Ideal O)
    (U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0< K)(hU:∀z:O,0≤(U (‖ringComplex z‖^2/K)).re)
    (J:ℕ)(B:ℝ)(hB:0≤ B)
    (hsource:∀v:ℝ,(commonEnergy s D hD F.right v L U K).re≤ B*(1+‖v‖)^(2*J)):
    (∑'z:O,((‖rightWindowChild s η (fixedBadMask*cubicIdealGenerator s.R) t C D hC hD E ξ₂ L θ X logAnnulus z‖^2:ℝ):ℂ)*
      U (‖ringComplex z‖^2/K)).re≤(windowBudget J t B*(1+‖θ‖)^J)^2:=by
  exact column_star_dyadic_window_energy s C D hC.1 hD hCD F.right t θ X hX L _
    (F.right_column hD s t L) U K hK hU J B hB hsource

end CenteredMomentFirstPhysicalSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstPhysicalSource
open Eisenstein   HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport CenteredMomentGaussEnergy
open CenteredMomentLogDyadic CenteredMomentSecondWindowBudget RayFourExpansion CompletedGauss
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentSecondIdealBlockBound
local notation "O"=> Eisenstein.O
universe u

theorem fixed_log_block_from_common_energy (W:𝓢(ℝ,ℂ))(decay J₁ J₂:ℕ):
    ∃Cbound:ℝ,0≤ Cbound ∧ ∀{ι:Type u}[Fintype ι],∀η:Character,∀s:OriginalData ι,
    ∀t:ℝ,∀(C D:Ideal O)(hC:Supported C)(hD:Supported D),primeSupport C=primeSupport D→
    ∀(E:Finset (CommonIndex C D))(rows:Finset O),(∀h∈rows,h≠0)→
    ∀K K₀ H₀ A₀ B₀:ℝ,0< K→0< K₀→0< H₀→0< A₀→0< B₀→
    ∀(U:𝓢(ℝ,ℂ))(H:ℝ),0< H→
    (∀h:O,0≤(U (‖ringComplex h‖^2/H)).re)→
    (∀h∈rows,1≤(U (‖ringComplex h‖^2/H)).re)→
    ∀E₁ E₂:Ideal O→ℝ,
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 s.columns))
      (fun b=> Ideal.span {element C D hD.1 s.columns b}),0≤ E₁ L)→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 s.columns))
      (fun b=> Ideal.span {element C D hD.1 s.columns b}),0≤ E₂ L)→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 s.columns))
      (fun b=> Ideal.span {element C D hD.1 s.columns b}),∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy s C hC (fixedPair η C D hC E χ χ).left v L U H).re≤ E₁ L*(1+‖v‖)^(2*J₁))→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 s.columns))
      (fun b=> Ideal.span {element C D hD.1 s.columns b}),∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy s D hD (fixedPair η C D hC E χ χ).right v L U H).re≤ E₂ L*(1+‖v‖)^(2*J₂))→
    (1+K₀*H₀/(A₀*B₀))^decay*
      ‖block η (fixedBadMask*cubicIdealGenerator s.R) 1 t s.columns s.beta C D hC hD E rows W
        (fun _=> logAnnulus) K K₀ H₀ A₀ B₀‖≤
      ‖scalar C D hC E K A₀ B₀‖*Cbound*
        ∑L∈divisorPool (Finset.univ:Finset (columns C D hD.1 s.columns))
          (fun b=> Ideal.span {element C D hD.1 s.columns b}),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
            (windowBudget J₁ t (E₁ L)*windowBudget J₂ t (E₂ L)):=by
  obtain ⟨Cb,hCb,hbound⟩:=physical_block_child_bound W (fun _=> logAnnulus) (fun _=> Real.log 4)
    (fun _=> Real.log_nonneg (by norm_num)) (fun _ _ hn=> logAnnulus_enclosure _ hn) decay J₁ J₂
  refine ⟨Cb,hCb,?_⟩
  intro ι inst η s t C D hC hD hCD E rows hrows K K₀ H₀ A₀ B₀ hK hK₀ hH₀ hA₀ hB₀
    U H hH hU hmajor E₁ E₂ hE₁ hE₂ hleft hright
  apply hbound η (fixedBadMask*cubicIdealGenerator s.R) t s.columns s.beta C D hC hD hCD E rows hrows
    K K₀ H₀ A₀ B₀ hK hK₀ hH₀ hA₀ hB₀
    (fun _ _=> logAnnulus_norm _) (fun _ _=> logAnnulus_norm _) U H hH hU hmajor
    (fun L=> windowBudget J₁ t (E₁ L)) (fun L=> windowBudget J₂ t (E₂ L))
    (fun L _=> windowBudget_nonneg _ _ _) (fun L _=> windowBudget_nonneg _ _ _)
  · intro L hL χ θ
    exact (fixedPair η C D hC E χ χ).left_window_energy s t θ A₀ hA₀ L U H hH hU J₁ (E₁ L)
      (hE₁ L hL) (hleft L hL χ)
  · intro L hL χ θ
    exact (fixedPair η C D hC E χ χ).right_window_energy hD hCD s t θ B₀ hB₀ L U H hH hU J₂ (E₂ L)
      (hE₂ L hL) (hright L hL χ)

end CenteredMomentFirstPhysicalSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstPhysicalDyadicRows
open Eisenstein  
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst
open CenteredMomentFirstWholeKernel CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentRowNorm
local notation "O" => Eisenstein.O

def activeRows (rows : Finset O) (n : Fin 4→ℤ) : Finset O :=
  rows.filter (fun h => dyadicWeight (n 1) (normValue h) ≠ 0)

lemma mem_activeRows (rows : Finset O) (n : Fin 4→ℤ) (h : O) :
    h∈activeRows rows n ↔ h∈rows ∧ dyadicWeight (n 1) (normValue h)≠0 := by
  simp only [activeRows,Finset.mem_filter]

lemma activeRows_subset (rows : Finset O) (n : Fin 4→ℤ) : activeRows rows n⊆rows :=
  Finset.filter_subset _ _

lemma activeRows_nonzero (rows : Finset O) (n : Fin 4→ℤ) (h : O)
    (hh : h∈activeRows rows n) : h≠0 := by
  intro hz
  subst h
  apply ((mem_activeRows rows n 0).mp hh).2
  rw [show normValue (0:O)=0 by simp [normValue_eq_embedding],
    dyadicWeight_zero_nonpos (n 1) 0 le_rfl]

lemma activeRows_norm (rows : Finset O) (n : Fin 4→ℤ) (h : O)
    (hh : h∈activeRows rows n) :
    1≤ normValue h ∧ dyadicScale (n 1)/4< normValue h ∧ normValue h< dyadicScale (n 1) :=
  ⟨normValue_ge_one h (activeRows_nonzero rows n h hh),
    dyadicWeight_support (n 1) ((mem_activeRows rows n h).mp hh).2⟩

lemma activeRows_scale_gt_one (rows : Finset O) (n : Fin 4→ℤ)
    (hne : (activeRows rows n).Nonempty) : 1< dyadicScale (n 1) := by
  obtain ⟨h,hh⟩:=hne
  exact (activeRows_norm rows n h hh).1.trans_lt (activeRows_norm rows n h hh).2.2

lemma activeRows_ball_majorant (rows : Finset O) (n : Fin 4→ℤ) (h : O)
    (hh : h∈activeRows rows n) :
    1≤(ballProfile (‖ringComplex h‖^2/dyadicScale (n 1))).re :=
  ballProfile_majorizes _ (dyadicScale_pos (n 1)) h (activeRows_norm rows n h hh).2.2.le

lemma row_log_window (n : ℤ) (h : O) :
    logAnnulus (Real.log (‖ringComplex h‖^2/dyadicScale n)) =
      (dyadicWeight n (normValue h):ℂ) := by
  by_cases hh : h=0
  · subst h
    simp only [map_zero,norm_zero,zero_pow (by decide : 2≠0),zero_div,Real.log_zero,
      logAnnulus,Real.exp_zero]
    rw [annulus_zero_high 1 le_rfl]
    rw [show normValue (0:O)=0 by simp [normValue_eq_embedding],
      dyadicWeight_zero_nonpos n 0 le_rfl,Complex.ofReal_zero]
  · rw [←normValue_eq_embedding]
    exact (actual_dyadic_log_window n (normValue h)
      (zero_lt_one.trans_le (normValue_ge_one h hh))).symm

theorem block_activeRows (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O→ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ) :
    block η m A t S c C D hC hD E rows W (fun _=> logAnnulus) K
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) =
    block η m A t S c C D hC hD E (activeRows rows n) W (fun _=> logAnnulus) K
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  unfold block
  dsimp only
  congr 1
  symm
  apply Finset.sum_subset (activeRows_subset rows n)
  intro h hrows hinactive
  have hw : dyadicWeight (n 1) (normValue h)=0 := by
    by_contra hweight
    exact hinactive ((mem_activeRows rows n h).mpr ⟨hrows,hweight⟩)
  simp only [windows,row_log_window,hw,Complex.ofReal_zero,
    mul_zero,zero_mul,ite_self,Finset.sum_const_zero]

end CenteredMomentFirstPhysicalDyadicRows

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace CenteredMomentFirstAnnularMajorant
open CenteredMomentSectorLocalization CenteredMomentDyadicCount

def weight (x:ℝ):ℝ:=cutoff (x/2)*(1-cutoff (4*x))

lemma weight_bounds (x:ℝ):0≤ weight x ∧ weight x≤1:=by
  have h₁:=cutoff_bounds (x/2)
  have h₂:=cutoff_bounds (4*x)
  unfold weight
  constructor
  · exact mul_nonneg h₁.1 (sub_nonneg.mpr h₂.2)
  · exact (mul_le_mul_of_nonneg_left (sub_le_self _ h₂.1) h₁.1).trans
      (by simpa only [mul_one] using h₁.2)

lemma weight_zero_low (x:ℝ)(hx:x≤1/8):weight x=0:=by
  rw [weight,cutoff_one (4*x) (by linarith),sub_self,mul_zero]

lemma weight_zero_high (x:ℝ)(hx:2≤ x):weight x=0:=by
  rw [weight,cutoff_zero (x/2) (by linarith),zero_mul]

lemma weight_one (x:ℝ)(hx:1/4≤ x)(hx':x≤1):weight x=1:=by
  rw [weight,cutoff_one (x/2) (by linarith),cutoff_zero (4*x) (by linarith)]
  norm_num

lemma weight_support:Function.support weight⊆Set.Icc (1/8:ℝ) 2:=by
  intro x hx
  exact ⟨(lt_of_not_ge (fun h=> hx (weight_zero_low x h))).le,
    (lt_of_not_ge (fun h=> hx (weight_zero_high x h))).le⟩

lemma weight_smooth:ContDiff ℝ ∞ weight:=by
  have hc:ContDiff ℝ ∞ cutoff:=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))
  exact (hc.comp (contDiff_id.div_const 2)).mul
    (contDiff_const.sub (hc.comp (contDiff_const.mul contDiff_id)))

def profile:𝓢(ℝ,ℂ):=
  (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (show Function.support (fun x:ℝ=>(weight x:ℂ))⊆Set.Icc (1/8:ℝ) 2 from by
      intro x hx
      apply weight_support
      intro hz
      apply hx
      change (weight x:ℂ)=0
      rw [hz]
      rfl)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp weight_smooth)

lemma profile_apply (x:ℝ):profile x=(weight x:ℂ):=rfl
lemma profile_nonneg (x:ℝ):0≤(profile x).re:=(weight_bounds x).1
lemma profile_le_one (x:ℝ):(profile x).re≤1:=(weight_bounds x).2
lemma profile_zero:profile 0=0:=by rw [profile_apply,weight_zero_low 0 (by norm_num)];rfl
lemma profile_one (x:ℝ)(hx:1/4≤ x)(hx':x≤1):profile x=1:=by
  rw [profile_apply,weight_one x hx hx'];rfl

lemma scaled_majorant (H q:ℝ)(hH:0< H)(hlo:H/4≤ q)(hhi:q≤ H):
    (profile (q/H)).re=1:=by
  rw [profile_one (q/H) ((le_div_iff₀ hH).mpr (by linarith))
    ((div_le_one hH).mpr hhi)]
  rfl

def bands (H:ℝ):Finset ℤ:=indices (H/8) (2*H)

lemma bands_scale (H:ℝ)(hH:0< H)(j:ℤ)(hj:j∈bands H):
    H/8≤ dyadicScale j ∧ dyadicScale j≤8*H:=by
  have h:=(mem_indices_iff_scale (H/8) (2*H) (by positivity) (by positivity) j).mp hj
  constructor
  · exact h.1
  · linarith [h.2]

lemma bands_card (H:ℝ)(hH:0< H):((bands H).card:ℝ)≤7:=by
  have h:=indices_card_bound (H/8) (2*H) (by positivity) (by linarith)
  have he:(2*H)/(H/8)=16:=by field_simp;ring
  rw [he,show (16:ℝ)=(2:ℝ)^4 by norm_num,Real.logb_pow] at h
  norm_num [Real.logb_self_eq_one] at h
  change ((indices (H/8) (2*H)).card:ℝ)≤7
  exact_mod_cast h

lemma weighted_partition (H q:ℝ)(hH:0< H):
    (profile (q/H)).re=(∑j∈bands H,dyadicWeight j q)*(profile (q/H)).re:=by
  by_cases h:weight (q/H)=0
  · simp only [profile_apply,Complex.ofReal_re,h,mul_zero]
  · have hx:=weight_support h
    have hq:q∈Set.Icc (H/8) (2*H):=⟨by linarith [(le_div_iff₀ hH).mp hx.1],
      (div_le_iff₀ hH).mp hx.2⟩
    rw [bands,dyadic_partition_on_interval (H/8) (2*H) q (by positivity) hq]
    exact (one_mul _).symm

end CenteredMomentFirstAnnularMajorant

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstPhysicalAnnularCommonBound
open Eisenstein   HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport CenteredMomentGaussEnergy
open CenteredMomentLogDyadic CenteredMomentSecondWindowBudget RayFourExpansion CompletedGauss
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentSectorLocalization
local notation "O" => Eisenstein.O
universe u

theorem actual_annular_block_from_common_energy (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) :
    ∃ Cbound : ℝ, 0≤ Cbound ∧ ∀ {ι : Type u} [Fintype ι],
    ∀ (η : Character) (s : OriginalData ι) (t : ℝ)
      (C D : Ideal O) (hC : Supported C) (hD : Supported D),
    primeSupport C=primeSupport D → ∀ (E : Finset (CommonIndex C D))
      (rows : Finset O) (K : ℝ), 0< K → ∀ n : Fin 4→ℤ,
    ∀ E₁ E₂ : Ideal O→ℝ,
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=> Ideal.span {element C D hD.1 s.columns b}), 0≤ E₁ L) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=> Ideal.span {element C D hD.1 s.columns b}), 0≤ E₂ L) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=> Ideal.span {element C D hD.1 s.columns b}), ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s C hC (fixedPair η C D hC E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ E₁ L*(1+‖v‖)^(2*J₁)) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=> Ideal.span {element C D hD.1 s.columns b}), ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s D hD (fixedPair η C D hC E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ E₂ L*(1+‖v‖)^(2*J₂)) →
    (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay *
      ‖block η (fixedBadMask*cubicIdealGenerator s.R) 1 t s.columns s.beta C D hC hD E rows W
        (fun _=> logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
          (dyadicScale (n 2)) (dyadicScale (n 3))‖ ≤
      ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cbound*
        ∑ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
          (fun b=> Ideal.span {element C D hD.1 s.columns b}),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
            (windowBudget J₁ t (E₁ L)*windowBudget J₂ t (E₂ L)) := by
  obtain ⟨Cb,hCb,hbound⟩:=fixed_log_block_from_common_energy W decay J₁ J₂
  refine ⟨Cb,hCb,?_⟩
  intro ι inst η s t C D hC hD hCD E rows K hK n E₁ E₂ hE₁ hE₂ hleft hright
  rw [block_activeRows η (fixedBadMask*cubicIdealGenerator s.R) 1 t s.columns s.beta
    C D hC hD E rows W K n]
  exact hbound η s t C D hC hD hCD E (activeRows rows n)
    (activeRows_nonzero rows n) K (dyadicScale (n 0)) (dyadicScale (n 1))
    (dyadicScale (n 2)) (dyadicScale (n 3)) hK
    (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _)
    CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1)) (dyadicScale_pos _) (fun _=> CenteredMomentFirstAnnularMajorant.profile_nonneg _)
    (fun h hh=> by
      have hn:=activeRows_norm rows n h hh
      have hm:=CenteredMomentFirstAnnularMajorant.scaled_majorant
        (dyadicScale (n 1)) (normValue h) (dyadicScale_pos _) hn.2.1.le hn.2.2.le
      simpa only [normValue_eq_embedding] using hm.ge)
    E₁ E₂ hE₁ hE₂ hleft hright

end CenteredMomentFirstPhysicalAnnularCommonBound

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentFirstDivisorSupport
open HeckeFamily CanonicalQuadraticSieve 
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentGaussEnergy
open CenteredMomentSecondDivisorSupport CenteredMomentChildAssembly
open CenteredMomentHeckeColumnWindow
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport RayFourExpansion
local notation "O"=> Eisenstein.O
variable {ι : Type*} [Fintype ι]

lemma common_coefficient_zero (s : OriginalData ι) (D : Ideal O) (hD : Supported D)
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤ H)
    (L : Ideal O) (hL : H/(D.absNorm:ℝ)< L.absNorm)
    (τ : Character) (t : ℝ) (I : supportedColumns (residualPool D hD.1 s.columns)) :
    (if IsCoprime D (I:Ideal O) ∧ L∣(I:Ideal O) then s.beta (D*I) else 0)*heightCoeff τ t I=0 := by
  split_ifs with hi
  · have hz : s.beta (D*I)=0 := by
      by_contra hn
      exact (not_le_of_gt hL) (live_right_divisor_norm D I L hD.1
        (Finset.mem_filter.mp I.property).2.1 s.beta H hβ hn hi.2)
    rw [hz,zero_mul]
  · rw [zero_mul]

theorem commonEnergy_zero (s : OriginalData ι) (D : Ideal O) (hD : Supported D)
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤ H)
    (L : Ideal O) (hL : H/(D.absNorm:ℝ)< L.absNorm)
    (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    commonEnergy s D hD τ t L W K=0 := by
  unfold commonEnergy gaussEnergy gaussPolynomial
  simp only [common_coefficient_zero s D hD H hβ L hL τ t,zero_mul,
    Finset.sum_const_zero,norm_zero,zero_pow (by decide : 2≠0),Complex.ofReal_zero,tsum_zero]

lemma right_coefficient_zero (s : OriginalData ι) (C D : Ideal O) (hD : Supported D)
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤ H)
    (L : Ideal O) (hL : H/(D.absNorm:ℝ)< L.absNorm)
    (η : Character) (m : O) (t : ℝ) (χ : RayCharacter)
    (a : columns C D hD.1 s.columns→ℂ) (I : columns C D hD.1 s.columns) :
    divisorCoefficient L (element C D hD.1 s.columns)
      (fun I=> coefficient η m 1 t s.beta D I*a I) χ I=0 := by
  unfold divisorCoefficient
  rw [element_span]
  split_ifs with hd
  · have hz : s.beta (D*I)=0 := by
      by_contra hn
      exact (not_le_of_gt hL) (live_right_divisor_norm D I L hD.1
        (column_supported C D hD.1 s.columns I).1 s.beta H hβ hn hd)
    simp only [coefficient,hz,zero_mul]
  · rfl

theorem rightWindowChild_zero (s : OriginalData ι) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤ H)
    (L : Ideal O) (hL : H/(D.absNorm:ℝ)< L.absNorm)
    (η : Character) (m : O) (t : ℝ) (χ : RayCharacter)
    (θ X : ℝ) (V : ℝ→ℂ) (z : O) :
    rightWindowChild s η m t C D hC hD E χ L θ X V z=0 := by
  unfold rightWindowChild gaussPolynomial
  dsimp only
  simp only [right_coefficient_zero s C D hD H hβ L hL η m t χ,
    zero_mul,Finset.sum_const_zero]

theorem signed_right_window_filter (s : OriginalData ι) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤ H)
    (η : Character) (m : O) (t : ℝ) (χ : RayCharacter)
    (θ X : ℝ) (V : ℝ→ℂ) (Ds : Finset (Ideal O)) (rows : Finset O)
    (F : Ideal O→O→ℂ) :
    (∑L∈Ds,∑z∈rows,F L z*star (rightWindowChild s η m t C D hC hD E χ L θ X V (-z)))=
      ∑L∈Ds.filter (fun L=>(L.absNorm:ℝ)≤ H/(D.absNorm:ℝ)),
        ∑z∈rows,F L z*star (rightWindowChild s η m t C D hC hD E χ L θ X V (-z)) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro L hLD
  by_cases hl : (L.absNorm:ℝ)≤ H/(D.absNorm:ℝ)
  · rw [if_pos hl]
  · rw [if_neg hl]
    simp only [rightWindowChild_zero s C D hC hD E H hβ L (lt_of_not_ge hl),star_zero,
      mul_zero,Finset.sum_const_zero]

theorem supported_harmonic_mass (B δ : ℝ) (hB : 0≤ B) (hδ : 0<δ) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
      ∀(Ds : Finset (Ideal O))(D : Ideal O)(H : ℝ),H/(D.absNorm:ℝ)≤ Z^B →
      (∑L∈Ds.filter (fun L=>(L.absNorm:ℝ)≤ H/(D.absNorm:ℝ)),
        ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖/(L.absNorm:ℝ))≤ C*Z^δ := by
  obtain ⟨C,hC,hbound⟩:=CenteredMomentMobiusHarmonicMass.full_mass_subpower B δ hB hδ
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro Ds D H hcap
  exact hz.2 _ (fun L hL _=>(Finset.mem_filter.mp hL).2.trans hcap)

open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput

theorem input_commonEnergy_zero (s : Input ι) (R seed D : Ideal O) (hD : Supported D)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (L : Ideal O)
    (hL : CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)< L.absNorm)
    (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    commonEnergy (original s R seed) D hD τ t L W K=0 :=
  commonEnergy_zero (original s R seed) D hD _
    (fun I hi=>(CenteredMomentOriginalCommonHarmonic.original_column_norm s R seed I hz₁ hz₂ hi).2)
    L hL τ t W K

theorem input_rightWindowChild_zero (s : Input ι) (R seed C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (L : Ideal O)
    (hL : CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)< L.absNorm)
    (η : Character) (m : O) (t : ℝ) (χ : RayCharacter)
    (θ X : ℝ) (V : ℝ→ℂ) (z : O) :
    rightWindowChild (original s R seed) η m t C D hC hD E χ L θ X V z=0 :=
  rightWindowChild_zero (original s R seed) C D hC hD E _
    (fun I hi=>(CenteredMomentOriginalCommonHarmonic.original_column_norm s R seed I hz₁ hz₂ hi).2)
    L hL η m t χ θ X V z

end CenteredMomentFirstDivisorSupport

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentFirstDivisorCommonBound
open HeckeFamily CanonicalQuadraticSieve  CompletedGauss 
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentGaussEnergy
open CenteredMomentFirstDivisorSupport CenteredMomentChildAssembly
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport RayFourExpansion
open CenteredMomentHeckeColumnWindow CenteredMomentSecondWindowBudget
open CenteredMomentSectorLocalization CenteredMomentLogDyadic CenteredMomentMobiusRegroup
open CenteredMomentSecondHeightFamily CenteredMomentFirstPhysicalAnnularCommonBound
local notation "O"=> Eisenstein.O

def pairMajorant {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (b : α→ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑i∈S,∑j∈S,b i*b j*‖∑'z:O,(gaussRow (a i) (ha i) z*star (gaussRow (a j) (ha j) z))*
    W (‖ringComplex z‖^2/K)‖

lemma pairMajorant_nonneg {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (b : α→ℝ) (hb : ∀i∈S,0≤ b i)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : 0≤ pairMajorant S a ha b W K :=
  Finset.sum_nonneg (fun i hi=> Finset.sum_nonneg (fun j hj=>
    mul_nonneg (mul_nonneg (hb i hi) (hb j hj)) (norm_nonneg _)))

lemma gaussEnergy_pair_bound {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ) (b : α→ℝ)
    (hc : ∀i∈S,‖c i‖≤ b i) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) :
    (gaussEnergy S a ha c W K).re≤ pairMajorant S a ha b W K := by
  apply (Complex.re_le_norm _).trans
  rw [gaussEnergy_expand S a ha c W K hK]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  simp only [norm_mul,norm_star]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (hc i hi) (hc j hj) (norm_nonneg _) ((norm_nonneg _).trans (hc i hi)))
    (norm_nonneg _)

variable {ι : Type*} [Fintype ι]

def coarse (s : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  pairMajorant Finset.univ (sourceGenerator (residualPool C hC.1 s.columns))
    (sourceGenerator_supported _) (fun I:supportedColumns (residualPool C hC.1 s.columns)=>
      ‖if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then s.beta (C*I) else 0‖) W K

lemma coarse_nonneg (s : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : 0≤ coarse s C hC L W K :=
  pairMajorant_nonneg _ _ _ _ (fun _ _=> norm_nonneg _) _ _

lemma commonEnergy_coarse (s : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) (τ : Character) (v : ℝ) :
    (commonEnergy s C hC τ v L W K).re≤ coarse s C hC L W K := by
  apply gaussEnergy_pair_bound _ _ _ _ _ _ W K hK
  intro I hI
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (CenteredMomentSourceSecondZeroEnergy.heightCoeff_norm_le_one τ v I
      (Finset.mem_filter.mp I.property).2.1)

universe u

theorem actual_supported_annular_block (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) :
    ∃ Cbound : ℝ, 0≤ Cbound ∧ ∀ {ι : Type u} [Fintype ι],
    ∀ (η : Character) (s : OriginalData ι) (t : ℝ)
      (C D : Ideal O) (hC : Supported C) (hD : Supported D),
    primeSupport C=primeSupport D → ∀ (E : Finset (CommonIndex C D))
      (rows : Finset O) (K : ℝ), 0< K → ∀ n : Fin 4→ℤ,
    ∀ Hsource : ℝ,(∀I,s.beta I≠0→(I.absNorm:ℝ)≤ Hsource) →
    ∀ E₁ E₂ : ℝ,0≤ E₁ → 0≤ E₂ →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=> Ideal.span {element C D hD.1 s.columns b}), (L.absNorm:ℝ)≤ Hsource/(D.absNorm:ℝ) → Squarefree L → ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s C hC (fixedPair η C D hC E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (E₁/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₁)) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=> Ideal.span {element C D hD.1 s.columns b}), (L.absNorm:ℝ)≤ Hsource/(D.absNorm:ℝ) → Squarefree L → ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s D hD (fixedPair η C D hC E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (E₂/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₂)) →
    (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay *
      ‖block η (fixedBadMask*cubicIdealGenerator s.R) 1 t s.columns s.beta C D hC hD E rows W
        (fun _=> logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
          (dyadicScale (n 2)) (dyadicScale (n 3))‖ ≤
      ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cbound*
        (∑ L∈(divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
          (fun b=> Ideal.span {element C D hD.1 s.columns b})).filter
            (fun L=>(L.absNorm:ℝ)≤ Hsource/(D.absNorm:ℝ)),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖/(L.absNorm:ℝ))*
            (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
  obtain ⟨Cb,hCb,hbound⟩:=actual_annular_block_from_common_energy W decay J₁ J₂
  refine ⟨Cb,hCb,?_⟩
  intro ι inst η s t C D hC hD hCD E rows K hK n Hsource hβ E₁ E₂ hE₁ hE₂ hleft hright
  let live (L : Ideal O) : Prop := (L.absNorm:ℝ)≤ Hsource/(D.absNorm:ℝ)
  let U := CenteredMomentFirstAnnularMajorant.profile
  let H := dyadicScale (n 1)
  let active (L : Ideal O) : Prop := live L ∧ (UniqueFactorizationMonoid.moebius L:ℂ)≠0
  let F₁ (L : Ideal O) := if active L then E₁/(L.absNorm:ℝ) else coarse s C hC L U H
  let F₂ (L : Ideal O) := if active L then E₂/(L.absNorm:ℝ) else if live L then coarse s D hD L U H else 0
  have hF₁ (L : Ideal O) : 0≤ F₁ L := by
    dsimp only [F₁]; split_ifs
    · exact div_nonneg hE₁ (Nat.cast_nonneg _)
    · exact coarse_nonneg _ _ _ _ _ _
  have hF₂ (L : Ideal O) : 0≤ F₂ L := by
    dsimp only [F₂]; split_ifs
    · exact div_nonneg hE₂ (Nat.cast_nonneg _)
    · exact coarse_nonneg _ _ _ _ _ _
    · exact le_rfl
  have hh:=hbound η s t C D hC hD hCD E rows K hK n F₁ F₂
    (fun L _=> hF₁ L) (fun L _=> hF₂ L)
    (by
      intro L hL χ v
      by_cases hl:active L
      · simpa only [F₁,if_pos hl] using hleft L hL hl.1 (CenteredMomentWholeDivisorShell.squarefree_of_moebius_ne_zero L hl.2) χ v
      · apply (commonEnergy_coarse s C hC L U H (dyadicScale_pos _) _ v).trans
        rw [show F₁ L=coarse s C hC L U H from if_neg hl]
        exact le_mul_of_one_le_right (coarse_nonneg _ _ _ _ _ _)
          (one_le_pow₀ (by linarith [norm_nonneg v])))
    (by
      intro L hL χ v
      by_cases hl:active L
      · simpa only [F₂,if_pos hl] using hright L hL hl.1 (CenteredMomentWholeDivisorShell.squarefree_of_moebius_ne_zero L hl.2) χ v
      · by_cases hc:live L
        · apply (commonEnergy_coarse s D hD L U H (dyadicScale_pos _) _ v).trans
          simp only [F₂,if_neg hl,if_pos hc]
          exact le_mul_of_one_le_right (coarse_nonneg _ _ _ _ _ _) (one_le_pow₀ (by linarith [norm_nonneg v]))
        · rw [commonEnergy_zero s D hD Hsource hβ L (lt_of_not_ge hc)]
          simp only [F₂,if_neg hl,if_neg hc,Complex.zero_re,zero_mul,le_refl])
  let Ds:=divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
    (fun b=> Ideal.span {element C D hD.1 s.columns b})
  have he : (∑L∈Ds,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
      (windowBudget J₁ t (F₁ L)*windowBudget J₂ t (F₂ L))) =
      (∑L∈Ds.filter live,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖/(L.absNorm:ℝ))*
        (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
    rw [Finset.sum_mul,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro L hL
    by_cases hμ:(UniqueFactorizationMonoid.moebius L:ℂ)=0
    · simp only [hμ,norm_zero,zero_mul,zero_div,ite_self]
    · by_cases hl:live L
      · have ha:active L:=⟨hl,hμ⟩
        simp only [F₁,F₂,if_pos ha,live,if_pos hl]
        rw [CenteredMomentSecondHarmonicBudget.paired_divisor J₁ J₂ t E₁ E₂ _ (Nat.cast_nonneg _)]
        ring
      · have ha:¬active L:=fun hh=> hl hh.1
        simp only [F₂,if_neg ha,live,if_neg hl,windowBudget,Real.sqrt_zero,zero_mul,mul_zero]
  exact hh.trans_eq (by rw [he]; ring)

theorem actual_supported_annular_harmonic (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ)
    (B δ : ℝ) (hB : 0≤ B) (hδ : 0<δ) :
    ∃ Cbound : ℝ, 0< Cbound ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀ {ι : Type u} [Fintype ι],
    ∀ (η : Character) (s : OriginalData ι) (t : ℝ)
      (C D : Ideal O) (hC : Supported C) (hD : Supported D),
    primeSupport C=primeSupport D → ∀ (E : Finset (CommonIndex C D))
      (rows : Finset O) (K : ℝ), 0< K → ∀ n : Fin 4→ℤ,
    ∀ Hsource : ℝ,(∀I,s.beta I≠0→(I.absNorm:ℝ)≤ Hsource) →
    Hsource/(D.absNorm:ℝ)≤ Z^B → ∀ E₁ E₂ : ℝ,0≤ E₁ → 0≤ E₂ →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=> Ideal.span {element C D hD.1 s.columns b}), (L.absNorm:ℝ)≤ Hsource/(D.absNorm:ℝ) → Squarefree L → ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s C hC (fixedPair η C D hC E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (E₁/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₁)) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=> Ideal.span {element C D hD.1 s.columns b}), (L.absNorm:ℝ)≤ Hsource/(D.absNorm:ℝ) → Squarefree L → ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s D hD (fixedPair η C D hC E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (E₂/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₂)) →
    (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay *
      ‖block η (fixedBadMask*cubicIdealGenerator s.R) 1 t s.columns s.beta C D hC hD E rows W
        (fun _=> logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
          (dyadicScale (n 2)) (dyadicScale (n 3))‖ ≤
      ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cbound*Z^δ*
        (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
  obtain ⟨Cb,hCb,hbound⟩:=actual_supported_annular_block W decay J₁ J₂
  obtain ⟨Cm,hCm,hmass⟩:=supported_harmonic_mass B δ hB hδ
  refine ⟨(Cb+1)*Cm,mul_pos (by linarith) hCm,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι inst η s t C D hC hD hCD E rows K hK n Hsource hβ hcap E₁ E₂ hE₁ hE₂ hleft hright
  have hh:=hbound η s t C D hC hD hCD E rows K hK n Hsource hβ E₁ E₂ hE₁ hE₂ hleft hright
  have hm:=hZ.2 (divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
    (fun b=> Ideal.span {element C D hD.1 s.columns b})) D Hsource hcap
  have hW : 0≤ windowBudget J₁ t E₁*windowBudget J₂ t E₂ :=
    mul_nonneg (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _)
  have hz : 0≤ Z^δ := Real.rpow_nonneg ((zero_lt_one.trans hZ.1).le) _
  calc
    _ ≤ _ := hh
    _ ≤ ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cb*(Cm*Z^δ)*
        (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
      gcongr
    _ ≤ _ := by
      have hc : Cb≤ Cb+1 := by linarith
      calc
        _ = ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cb*Cm*Z^δ*
          (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by ring
        _ ≤ ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*(Cb+1)*Cm*Z^δ*
          (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by gcongr
        _ = _ := by ring

end CenteredMomentFirstDivisorCommonBound

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstWindowBudgets
open CenteredMomentSecondWindowBudget

lemma sqrt_sum_le {α:Type*}(s:Finset α)(E:α→ℝ)(hE:∀i∈s,0≤ E i):
    Real.sqrt (∑i∈s,E i)≤∑i∈s,Real.sqrt (E i):=by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    have he:0≤ E a:=hE a (Finset.mem_insert_self _ _)
    have hs:0≤∑i∈s,E i:=Finset.sum_nonneg (fun i hi=> hE i (Finset.mem_insert_of_mem hi))
    have hadd:Real.sqrt (E a+∑i∈s,E i)≤ Real.sqrt (E a)+Real.sqrt (∑i∈s,E i):=by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith [Real.sq_sqrt he,Real.sq_sqrt hs,
          mul_nonneg (Real.sqrt_nonneg (E a)) (Real.sqrt_nonneg (∑i∈s,E i))]
    exact hadd.trans (add_le_add le_rfl (ih (fun i hi=> hE i (Finset.mem_insert_of_mem hi))))

lemma windowBudget_sum {α:Type*}(s:Finset α)(E:α→ℝ)(hE:∀i∈s,0≤ E i)
    (J:ℕ)(t:ℝ):
    windowBudget J t (∑i∈s,E i)≤∑i∈s,windowBudget J t (E i):=by
  unfold windowBudget
  rw [←Finset.sum_mul,←Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (sqrt_sum_le s E hE) (pow_nonneg (heightEnvelope_pos t).le _))
    (profileMoment_nonneg J)

theorem windowBudget_pair_sum {α β:Type*}(s:Finset α)(u:Finset β)
    (E:α→ℝ)(F:β→ℝ)(hE:∀i∈s,0≤ E i)(hF:∀j∈u,0≤ F j)
    (J₁ J₂:ℕ)(t:ℝ):
    windowBudget J₁ t (∑i∈s,E i)*windowBudget J₂ t (∑j∈u,F j)≤
      ∑i∈s,∑j∈u,windowBudget J₁ t (E i)*windowBudget J₂ t (F j):=by
  have hh:=mul_le_mul (windowBudget_sum s E hE J₁ t) (windowBudget_sum u F hF J₂ t)
    (windowBudget_nonneg J₂ t _) (Finset.sum_nonneg (fun i _=> windowBudget_nonneg J₁ t (E i)))
  apply hh.trans_eq
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]

open Eisenstein   HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport CenteredMomentGaussEnergy
open CenteredMomentLogDyadic CenteredMomentSecondWindowBudget RayFourExpansion CompletedGauss
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentSectorLocalization
local notation "O" => Eisenstein.O
universe u

theorem actual_annular_block_from_four_budgets (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) :
    ∃ Cbound : ℝ, 0≤ Cbound ∧ ∀ {ι : Type u} [Fintype ι],
    ∀ (η : Character) (s : OriginalData ι) (t : ℝ)
      (C D : Ideal O) (hC : Supported C) (hD : Supported D),
    primeSupport C=primeSupport D → ∀ (E : Finset (CommonIndex C D))
      (rows : Finset O) (K : ℝ), 0< K → ∀ n : Fin 4→ℤ,
    ∀ E₁ E₂ : Ideal O→Fin 4→ℝ,
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=> Ideal.span {element C D hD.1 s.columns b}), ∀ i,0≤ E₁ L i) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=> Ideal.span {element C D hD.1 s.columns b}), ∀ i,0≤ E₂ L i) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=> Ideal.span {element C D hD.1 s.columns b}), ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s C hC (fixedPair η C D hC E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (∑i,E₁ L i)*(1+‖v‖)^(2*J₁)) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=> Ideal.span {element C D hD.1 s.columns b}), ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s D hD (fixedPair η C D hC E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (∑i,E₂ L i)*(1+‖v‖)^(2*J₂)) →
    (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay *
      ‖block η (fixedBadMask*cubicIdealGenerator s.R) 1 t s.columns s.beta C D hC hD E rows W
        (fun _=> logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
          (dyadicScale (n 2)) (dyadicScale (n 3))‖ ≤
      ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cbound*
        ∑ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
          (fun b=> Ideal.span {element C D hD.1 s.columns b}),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
            (∑i:Fin 4,∑j:Fin 4,windowBudget J₁ t (E₁ L i)*windowBudget J₂ t (E₂ L j)) := by
  obtain ⟨Cb,hCb,hbound⟩:=CenteredMomentFirstPhysicalAnnularCommonBound.actual_annular_block_from_common_energy W decay J₁ J₂
  refine ⟨Cb,hCb,?_⟩
  intro ι inst η s t C D hC hD hCD E rows K hK n E₁ E₂ hE₁ hE₂ hleft hright
  have hh:=hbound η s t C D hC hD hCD E rows K hK n
    (fun L=>∑i,E₁ L i) (fun L=>∑i,E₂ L i)
    (fun L hL=> Finset.sum_nonneg (fun i _=> hE₁ L hL i))
    (fun L hL=> Finset.sum_nonneg (fun i _=> hE₂ L hL i)) hleft hright
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) hCb)
  apply Finset.sum_le_sum
  intro L hL
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact windowBudget_pair_sum Finset.univ Finset.univ (E₁ L) (E₂ L)
    (fun i _=> hE₁ L hL i) (fun i _=> hE₂ L hL i) J₁ J₂ t

end CenteredMomentFirstWindowBudgets

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstMixedAllowance
open CanonicalQuadraticSieve CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentRankinRadical CenteredMomentFirstCanonicalAllowance
open CenteredMomentFirstScale
local notation "O"=> Eisenstein.O

def allowance (C D:Ideal O)(Z:ℝ):ℝ:=
  max (3*Real.logb Z (C.absNorm:ℝ)-5*Real.logb Z (D.absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)) 0/6

def extractedAllowance (I J:Ideal O)(Z:ℝ):ℝ:=
  max (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) 0/6

lemma allowance_nonneg (C D:Ideal O)(Z:ℝ):0≤ allowance C D Z:=by
  unfold allowance;positivity

lemma actual_allowance_sum (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CubicEisenstein.primeSupport C=CubicEisenstein.primeSupport D)(Z:ℝ)(hZ:1< Z):
    allowance C D Z+
      max (3*Real.logb Z (D.absNorm:ℝ)-5*Real.logb Z (C.absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)) 0/6≤
      Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ)-
        2*Real.logb Z ((commonRadical C D).absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ):=
  actual_canonical_common_support_allowance C D hC hD hCD Z hZ


end CenteredMomentFirstMixedAllowance

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstMixedRoot
open CanonicalQuadraticSieve CenteredMomentFirstMixedAllowance
open CenteredMomentFirstCanonicalAllowance CenteredMomentFirstNonexceptionalPrefactor
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical CenteredMomentCompleteCommon
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open Eisenstein   HeckeFamily
open CenteredMomentFirstScale CenteredMomentSupportedCorrelation
local notation "O"=> Eisenstein.O

lemma active_span_swap (C D:Ideal O):
    Ideal.span {activeConductor D C}=Ideal.span {activeConductor C D}:=by
  rw [activeConductor_span_filter,activeConductor_span_filter,
    CenteredMomentCompleteCommon.commonSupport_comm D C]
  congr 1
  apply Finset.filter_congr
  intro P hP
  simp only [CenteredMomentActive.netExponent]
  omega

lemma allowance_pair (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CubicEisenstein.primeSupport C=CubicEisenstein.primeSupport D)(Z:ℝ)(hZ:1< Z):
    allowance C D Z+allowance D C Z≤
      Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ)-
        2*Real.logb Z ((commonRadical C D).absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ):=by
  have hh:=actual_allowance_sum C D hC hD hCD Z hZ
  simpa only [allowance,active_span_swap C D] using hh

lemma allowance_root (Z C D P R b:ℝ)(hZ:1< Z)(hC:0< C)(hD:0< D)(hP:0< P)(hR:0< R)
    (hb:b≤ Real.logb Z C+Real.logb Z D-2*Real.logb Z P-Real.logb Z R):
    Real.sqrt R/Real.sqrt (C*D)*Z^(b/2)≤1/P:=by
  have hz:0< Z:=zero_lt_one.trans hZ
  have hlz:0< Real.log Z:=Real.log_pos hZ
  have hb':b≤(Real.log C+Real.log D-2*Real.log P-Real.log R)/Real.log Z:=by
    convert hb using 1 ; simp only [Real.logb] ; ring
  have hh: b*Real.log Z≤ Real.log C+Real.log D-2*Real.log P-Real.log R:=
    (le_div_iff₀ hlz).mp hb'
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  simp (disch := positivity) only [Real.log_mul,Real.log_div,Real.log_sqrt,
    Real.log_rpow,Real.log_one]
  nlinarith

lemma paired_reference_root (qL qR V C D Z bL bR EL ER:ℝ)
    (hqL:0< qL)(hqR:0< qR)(hV:0< V)(hC:0< C)(hD:0< D)(hZ:0< Z)
    (_hEL:0≤ EL)(_hER:0≤ ER):
    Real.sqrt ((qL*(V/C)^2*Z^bL*EL)*(qR*(V/D)^2*Z^bR*ER))=
      V^2/(C*D)*Real.sqrt (qL*qR)*Z^((bL+bR)/2)*Real.sqrt (EL*ER):=by
  have hbase:Real.sqrt ((qL*(V/C)^2*Z^bL)*(qR*(V/D)^2*Z^bR))=
      V^2/(C*D)*Real.sqrt (qL*qR)*Z^((bL+bR)/2):=by
    apply Real.log_injOn_pos
    · simp only [Set.mem_Ioi];positivity
    · simp only [Set.mem_Ioi];positivity
    · simp (disch := positivity) only [Real.log_sqrt,Real.log_mul,Real.log_div,
        Real.log_pow,Real.log_rpow]
      ring
  rw [show (qL*(V/C)^2*Z^bL*EL)*(qR*(V/D)^2*Z^bR*ER)=
    ((qL*(V/C)^2*Z^bL)*(qR*(V/D)^2*Z^bR))*(EL*ER) by ring,
    Real.sqrt_mul (by positivity),hbase]

theorem actual_fixed_reference_pair (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CubicEisenstein.primeSupport C=CubicEisenstein.primeSupport D)
    (E:Finset (CommonIndex C D))(η:Character)(ξ₁ ξ₂:RayFourExpansion.RayCharacter)
    (F:FixedPair η C D hC E ξ₁ ξ₂)
    (K A₀ B₀ a T M Z EL ER:ℝ)(hK:0< K)(hA:0< A₀)(hB:0< B₀)
    (ha:0< a)(hT:0< T)(hZ:1< Z)(hEL:0≤ EL)(hER:0≤ ER)
    (hl:a*T≤(C.absNorm:ℝ)*Real.exp M*A₀)
    (hr:a*T≤(D.absNorm:ℝ)*Real.exp M*B₀):
    ‖scalar C D hC E K A₀ B₀‖/T*
      Real.sqrt (((F.left.modulus.absNorm:ℝ)*(T/(C.absNorm:ℝ))^2*Z^(allowance C D Z)*EL)*
        ((F.right.modulus.absNorm:ℝ)*(T/(D.absNorm:ℝ))^2*Z^(allowance D C Z)*ER))≤
      ‖inactiveWeight C D E‖*(Real.exp M/a)*fixedPresentationCost*K*(η.modulus.absNorm:ℝ)/
        (commonRadical C D).absNorm*Real.sqrt (EL*ER):=by
  have hF:0< fixedPresentationCost:=fixedPresentationCost_pos
  have hNC:0<(C.absNorm:ℝ):=norm_pos C hC.1
  have hND:0<(D.absNorm:ℝ):=norm_pos D hD.1
  have hNR:0<((Ideal.span {activeConductor C D}).absNorm:ℝ):=active_norm_pos C D
  have hP:0<((commonRadical C D).absNorm:ℝ):=norm_pos _ (commonRadical_ne_zero C D)
  have hqL:0<(F.left.modulus.absNorm:ℝ):=norm_pos _ F.left.modulus_ne_bot
  have hqR:0<(F.right.modulus.absNorm:ℝ):=norm_pos _ F.right.modulus_ne_bot
  have he:0<‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)‖:=
    norm_pos_iff.mpr (ringComplex_ne_zero (supported_element_ne_zero _ (subsetGenerator_supported C D hC E)))
  have hrpos:0<‖ringComplex (activeConductor C D)‖:=
    norm_pos_iff.mpr (ringComplex_ne_zero (supported_element_ne_zero _ (activeConductor_supported C D hC)))
  have hs:=scalar_conductor_algebra _ _ K T _ _ _ (Real.exp M/a) fixedPresentationCost
    (η.modulus.absNorm:ℝ) (F.left.modulus.absNorm:ℝ) (F.right.modulus.absNorm:ℝ)
    (norm_nonneg _) (norm_nonneg _) hK.le hT (mul_pos hNC hND)
    (sq_pos_of_pos he) hrpos (by positivity) fixedPresentationCost_pos.le (Nat.cast_nonneg _)
    hqL.le hqR.le (weighted_scalar_volume C D hC E K A₀ B₀ a T M hK hA hB ha hT hl hr)
    F.conductor_caps.1 F.conductor_caps.2
  have haR:=allowance_root Z (C.absNorm:ℝ) (D.absNorm:ℝ)
    ((commonRadical C D).absNorm:ℝ) ((Ideal.span {activeConductor C D}).absNorm:ℝ)
    (allowance C D Z+allowance D C Z) hZ hNC hND hP hNR
    (allowance_pair C D hC hD hCD Z hZ)
  rw [←ringComplex_norm_sq_eq_absNorm_span,Real.sqrt_sq (norm_nonneg _)] at haR
  rw [paired_reference_root _ _ T _ _ Z _ _ EL ER hqL hqR hT hNC hND
    (zero_lt_one.trans hZ) hEL hER]
  calc
    _=(‖scalar C D hC E K A₀ B₀‖*T/((C.absNorm:ℝ)*D.absNorm)*
        Real.sqrt ((F.left.modulus.absNorm:ℝ)*F.right.modulus.absNorm))*
        (Z^((allowance C D Z+allowance D C Z)/2)*Real.sqrt (EL*ER)):=by
      field_simp
    _≤(‖inactiveWeight C D E‖*(Real.exp M/a)*fixedPresentationCost*K*(η.modulus.absNorm:ℝ)*
        (‖ringComplex (activeConductor C D)‖/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)))*
        (Z^((allowance C D Z+allowance D C Z)/2)*Real.sqrt (EL*ER)):=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _=(‖inactiveWeight C D E‖*(Real.exp M/a)*fixedPresentationCost*K*(η.modulus.absNorm:ℝ))*
        ((‖ringComplex (activeConductor C D)‖/Real.sqrt ((C.absNorm:ℝ)*D.absNorm))*
          Z^((allowance C D Z+allowance D C Z)/2))*Real.sqrt (EL*ER):=by ring
    _≤(‖inactiveWeight C D E‖*(Real.exp M/a)*fixedPresentationCost*K*(η.modulus.absNorm:ℝ))*
        (1/(commonRadical C D).absNorm)*Real.sqrt (EL*ER):=by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left haR (by positivity))
        (Real.sqrt_nonneg _)
    _=_:=by ring

open CenteredMomentFirstPhysicalSourceSupport CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open HeckeFamily CenteredMomentSupportedCorrelation

theorem original_fixed_reference_pair {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed:Ideal O)(a₁ a₂:ℝ)(ha₁:0< a₁)(ha₂:0< a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤ x)(hs₂:∀x,s.W₂ x≠0→a₂≤ x)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CubicEisenstein.primeSupport C=CubicEisenstein.primeSupport D)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayFourExpansion.RayCharacter)
    (F:FixedPair s.η C D hC E ξ₁ ξ₂)
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(U:Fin 4→ℝ→ℂ)
    (K K₀ H₀ A₀ B₀ M Z EL ER:ℝ)(hK:0< K)(hA:0< A₀)(hB:0< B₀)(hZ:1< Z)
    (hEL:0≤ EL)(hER:0≤ ER)(hwin:∀i y,U i y≠0→|y|≤ M)
    (hn:block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W U K K₀ H₀ A₀ B₀≠0):
    let V:=volume s.toData;
    ‖scalar C D hC E K A₀ B₀‖/V*
      Real.sqrt (((F.left.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z)*EL)*
        ((F.right.modulus.absNorm:ℝ)*(V/(D.absNorm:ℝ))^2*Z^(allowance D C Z)*ER))≤
      ‖inactiveWeight C D E‖*(Real.exp M/((∏i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*
        (s.η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm*Real.sqrt (EL*ER):=by
  have ha:0<(∏i,s.lo i)*a₁*a₂:=
    mul_pos (mul_pos (Finset.prod_pos (fun i _=> s.lo_pos i)) ha₁) ha₂
  obtain ⟨hl,hr⟩:=block_reference_lower s.η m A t S
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) C D hC hD E rows W U
    K K₀ H₀ A₀ B₀ ((∏i,s.lo i)*a₁*a₂) (volume s.toData) M hA hB
    (fun I hi=> original_column_lower s R seed I a₁ a₂ ha₁.le ha₂.le hs₁ hs₂ hi) hwin hn
  exact actual_fixed_reference_pair C D hC hD hCD E s.η ξ₁ ξ₂ F
    K A₀ B₀ _ _ M Z EL ER hK hA hB ha (volume_pos s.toData) hZ hEL hER hl hr

end CenteredMomentFirstMixedRoot

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstMixedWindow
open CenteredMomentFirstMixedRoot CenteredMomentFirstMixedAllowance CenteredMomentSecondWindowBudget
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSourceSupport CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical CenteredMomentCompleteCommon
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentFirstScale CenteredMomentFirstNonexceptionalPrefactor
local notation "O"=> Eisenstein.O

theorem original_four_budget_reference {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed:Ideal O)(a₁ a₂:ℝ)(ha₁:0< a₁)(ha₂:0< a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤ x)(hs₂:∀x,s.W₂ x≠0→a₂≤ x)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CubicEisenstein.primeSupport C=CubicEisenstein.primeSupport D)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayFourExpansion.RayCharacter)
    (F:FixedPair s.η C D hC E ξ₁ ξ₂)
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(U:Fin 4→ℝ→ℂ)
    (K K₀ H₀ A₀ B₀ M Z:ℝ)(EL ER:Fin 4→ℝ)(JL JR:ℕ)(height:ℝ)(hK:0< K)(hA:0< A₀)(hB:0< B₀)(hZ:1< Z)
    (hEL:∀i,0≤ EL i)(hER:∀i,0≤ ER i)(hwin:∀i y,U i y≠0→|y|≤ M)
    (hn:block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W U K K₀ H₀ A₀ B₀≠0):
    let V:=volume s.toData;
    ‖scalar C D hC E K A₀ B₀‖/V*
      (∑i:Fin 4,∑j:Fin 4,
        windowBudget JL height ((F.left.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z)*EL i)*
        windowBudget JR height ((F.right.modulus.absNorm:ℝ)*(V/(D.absNorm:ℝ))^2*Z^(allowance D C Z)*ER j))≤
      (‖inactiveWeight C D E‖*(Real.exp M/((∏i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*
        (s.η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm)*
        (∑i:Fin 4,∑j:Fin 4,windowBudget JL height (EL i)*windowBudget JR height (ER j)) :=by
  dsimp only
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hh:=original_fixed_reference_pair s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂
    m A t S C D hC hD hCD E ξ₁ ξ₂ F rows W U K K₀ H₀ A₀ B₀ M Z
    (EL i) (ER j) hK hA hB hZ (hEL i) (hER j) hwin hn
  have hqL:0<(F.left.modulus.absNorm:ℝ):=norm_pos _ F.left.modulus_ne_bot
  have hqR:0<(F.right.modulus.absNorm:ℝ):=norm_pos _ F.right.modulus_ne_bot
  have hCpos:=norm_pos C hC.1
  have hDpos:=norm_pos D hD.1
  have hV:=volume_pos s.toData
  have hz:0< Z:=zero_lt_one.trans hZ
  have hei:=hEL i
  have herj:=hER j
  have hh':=mul_le_mul_of_nonneg_right hh
    (mul_nonneg (mul_nonneg (pow_nonneg (heightEnvelope_pos height).le JL)
      (profileMoment_nonneg JL)) (mul_nonneg (pow_nonneg (heightEnvelope_pos height).le JR)
      (profileMoment_nonneg JR)))
  simp only [Real.sqrt_mul (by positivity : 0≤
    (F.left.modulus.absNorm:ℝ)*(volume s.toData/(C.absNorm:ℝ))^2*Z^(allowance C D Z)*EL i),
    Real.sqrt_mul (hEL i)] at hh'
  unfold windowBudget
  nlinarith only [hh']

end CenteredMomentFirstMixedWindow

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

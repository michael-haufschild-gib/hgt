/-
First-stage admissions adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Energy.CanonicalErrorBounds

/-!
# First-stage admissions

Amplifier caps and source admission of the first annular stage, live and raw-scale admissions
and amplifier family admission; uniform and homogeneous four-power bounds.
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
open scoped Classical BigOperators SchwartzMap ContDiff

namespace CenteredMomentEnergyCanonicalAmplifiedUniform
open HeckeFamily 
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=> Eisenstein.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary InversePrincipalEnergy

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion  Eisenstein
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentFirstAmplifiedFourCoefficients

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

lemma front_mono {a b:ℝ}(p:Profiles a b)(U V:Finset (ℕ×ℕ))(hUV:U⊆V)
    (J K:ℕ)(hJK:J≤ K)(c d C₀ C₁ t height:ℝ)
    (hc:0≤ c)(hcd:c≤ d)(hC₀:0≤ C₀)(hC₁:0≤ C₁)(hh:0≤ height):
    c*(C₀+C₁+1)*(p.control U)^2*(1+|t|+height)^J≤
      d*(C₀+C₁+1)*(p.control V)^2*(1+|t|+height)^K:=by
  have hp:p.control U≤ p.control V:=by
    unfold Profiles.control
    exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hUV) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono hUV) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hp0:=p.control_nonneg U
  have hp1:=p.control_nonneg V
  have ht:(1+|t|+height)^J≤(1+|t|+height)^K:=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hJK
  have hd:0≤ d:=hc.trans hcd
  gcongr

theorem actual_original_subsets_amplified_power
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤ Mslot)(hεmask:0<εmask)(haPlain:0< a)(hbPlain:0≤ b)
    (L:ℝ)(hL:0≤ L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0< aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤ Mcap)(hLs:0≤ Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0< lower)(hupper:1≤ upper)
    (ha0:0< a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤ highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤ Bcap)(hξ:0<ξ)
    (sigma cost:ℝ)(hsigma:0< sigma)(hξsmall:ξ≤ sigma/4)(hcost:1≤ cost):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0< Cbound ∧ ∃Z₀:ℝ,1< Z₀ ∧
    (∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤ Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤ C₀ → 0≤ C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) →
    (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤ bslot) → (∀i,src.M i≤ Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤ N → lower≤ src.lower → src.upper≤ upper →
    0≤ src.b₁ → 0≤ src.b₂ → src.b₁≤ max 1 b → src.b₂≤ max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D} →
    ∀K delta reserve asource:ℝ,0< K → 0< asource →
    0≤ delta → 0≤ reserve → a0≤ asource →
    let input:=child src C R0 B τ t
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
    Ready input (R0*C) Kmain Z ξ Bcap →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤ Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤ Z^L → src.X₂≤ Z^L → src.Y₁≤ Z^L → src.Y₂≤ Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mwidth →
    Mwidth-sigma/2≤ Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤ CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    normalizedGaussSource input (R0*C) seed CenteredMomentFirstAmplificationChoice.ballProfile Kmain≤
      (∑j,(Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|t|+height)^Jheight*
        Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ))*
        mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2) ∧
    (∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤ Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤ C₀ → 0≤ C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) →
    (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤ bslot) → (∀i,src.M i≤ Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤ N → lower≤ src.lower → src.upper≤ upper →
    0≤ src.b₁ → 0≤ src.b₂ → src.b₁≤ max 1 b → src.b₂≤ max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D} →
    ∀K delta reserve asource:ℝ,0< K → 0< asource →
    0≤ delta → 0≤ reserve → a0≤ asource →
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=0 ∨ k=5 ∨ k=6) →
    sigma/6≤ Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^(k+1)),
    ∀(υ:Character)(χerr:RayCharacter),
    υ.modulus.absNorm≤ CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter τ χerr) fixedBadMask prime
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent k) →
    (υ.modulus.absNorm:ℝ)≤ cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (k+1)) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) (k+1) Bp υ t →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (k+1)
    Ready input ((R0*C)*(Ideal.span {prime})^(k+1)) Kerror Z ξ Bcap →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤ Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤ Z^L → src.X₂≤ Z^L → src.Y₁≤ Z^L → src.Y₂≤ Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mwidth →
    Mwidth-sigma/2≤ Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤ CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    normalizedGaussSource input ((R0*C)*(Ideal.span {prime})^(k+1)) seed
      CenteredMomentFirstAmplificationChoice.ballProfile Kerror≤
      (∑j,(Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|t|+height)^Jheight*
        Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ))*
        CenteredMomentFirstAmplifiedFourCoefficients.errorPowers prime (k+1)
        (τ.modulus.absNorm:ℝ) Z Kerror
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2) :=by
  obtain ⟨Um,Jm,hm⟩:=
    CenteredMomentEnergyCanonicalMainSubsets.actual_original_subsets_main_power (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma cost hsigma hξsmall hcost
  obtain ⟨Ue,Je,he⟩:=
    CenteredMomentEnergyCanonicalErrorSubsets.actual_original_subsets_error_power (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma cost hsigma hξsmall hcost
  refine ⟨Um∪Ue,max Jm Je,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cm,hCm,Zm,hZm,hmain⟩:=hm η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Ce,hCe,Ze,hZe,herror⟩:=he η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cm+Ce,add_pos hCm hCe,max Zm Ze,lt_of_lt_of_le hZm (le_max_left _ _),?_,?_⟩
  ·
    intro Aorig θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
      hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
      hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
      K delta reserve asource hK hasource hdelta hreserve haSource
    dsimp only
    intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
      hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
    have hg:=hmain Aorig θ Z ((le_max_left _ _).trans hZ) εchild C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
      hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
      K delta reserve asource hK hasource hdelta hreserve haSource
      hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
      hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
    have hfront:=front_mono p Um (Um∪Ue) Finset.subset_union_left Jm (max Jm Je) (le_max_left _ _)
      Cm (Cm+Ce) C₀ C₁ t height hCm.le (le_add_of_nonneg_right hCe.le) hC₀ hC₁ hheight
    dsimp only at hg ⊢
    have hz:0< Z:=zero_lt_one.trans ((lt_of_lt_of_le hZm (le_max_left Zm Ze)).trans_le hZ)
    apply hg.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (volume_pos _).le _)
    apply mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hfront (Real.rpow_nonneg hz.le _)) (Nat.cast_nonneg _))
    fin_cases j <;> simp only [mainPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
      try unfold mainCommonRadius
    all_goals positivity
  ·
    intro Aorig θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
      hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
      hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
      K delta reserve asource hK hasource hdelta hreserve haSource
      prime hprime k hk hprimeScale hslot Bp υ χerr hN hυ input hinput
    dsimp only
    intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
      hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
    have hg:=herror Aorig θ Z ((le_max_right _ _).trans hZ) εchild C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
      hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
      K delta reserve asource hK hasource hdelta hreserve haSource
      prime hprime k hk hprimeScale hslot Bp υ χerr t hN hυ input hinput
      hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
      hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
    have hfront:=front_mono p Ue (Um∪Ue) Finset.subset_union_right Je (max Jm Je) (le_max_right _ _)
      Ce (Cm+Ce) C₀ C₁ t height hCe.le (le_add_of_nonneg_left hCm.le) hC₀ hC₁ hheight
    dsimp only at hg ⊢
    have hz:0< Z:=zero_lt_one.trans ((lt_of_lt_of_le hZm (le_max_left Zm Ze)).trans_le hZ)
    apply hg.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (volume_pos _).le _)
    apply mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hfront (Real.rpow_nonneg hz.le _)) (Nat.cast_nonneg _))
    fin_cases j <;> simp only [CenteredMomentFirstAmplifiedFourCoefficients.errorPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
      try unfold errorCommonRadius
    all_goals positivity

end CenteredMomentEnergyCanonicalAmplifiedUniform

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

universe u
namespace CenteredMomentEnergyFirstAnnularAdmission
open HeckeFamily Eisenstein 
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstReferenceSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalLocalWeightSum
open CenteredMomentFirstPhysicalDyadicCount CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentSectorLocalization CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstPhysicalLedger CenteredMomentFirstExtractedLedger
local notation "O" => Eisenstein.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

omit [DecidableEq ι] in
lemma source_dyad_retained (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (n:SourceBlocks s R seed K Z ξ p E):
    Retained (localRadius s R seed K Z ξ p E) (n 1):=by
  have hn: (n 1:ℤ)∈retainedIndices (localRadius s R seed K Z ξ p E):=(n 1).property
  exact ((mem_retainedIndices _ _).mp hn).1

omit [DecidableEq ι] in
lemma source_dyad_gt_one (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (n:SourceBlocks s R seed K Z ξ p E):1< dyadicScale (n 1):=by
  have hn: (n 1:ℤ)∈retainedIndices (localRadius s R seed K Z ξ p E):=(n 1).property
  obtain ⟨q,hq,hweight⟩:=((mem_retainedIndices _ _).mp hn).2
  exact hq.trans_lt ((dyadicWeight_support (n 1)) hweight).2

omit [DecidableEq ι] in
lemma source_nominal_positive (s:Input ι)(R seed:Ideal O)(K:ℝ)(hK:0< K)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2)):
    0< firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData):=by
  have he:=Ideal.span_singleton_eq_bot.not.mpr
    (TruncatedPrincipalPoisson.primeSubsetGenerator_ne_zero (fun P:CommonIndex p.val.1 p.val.2=> P.val) E)
  have hE:(∏P∈E,P.val)≠(0:Ideal O):=by
    simpa only [TruncatedPrincipalPoisson.primeSubsetGenerator_span,Ideal.zero_eq_bot] using he
  exact firstNominalScale_pos _ _ _ hE K _ hK (volume_pos s.toData)

omit [DecidableEq ι] in
lemma source_nominal_span (s:Input ι)(R seed:Ideal O)(K:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2)):
    firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData)=
      firstNominalScale p.val.1 p.val.2
        (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=> P.val) E})
        K (volume s.toData):=by rw [TruncatedPrincipalPoisson.primeSubsetGenerator_span]

def amplifierCap (A D ξcap:ℝ):ℝ:=3*max A D+ξcap/2+1

omit [DecidableEq ι] in
theorem source_amplifier_packet (A D ξcap Z:ℝ)(hZ:32≤ Z)
    (s:Input ι)(R seed:Ideal O)(K ξ:ℝ)(hK:0< K)(hξ:ξ≤ξcap)
    (hV:volume s.toData≤ Z^A)(hKi:K⁻¹≤ Z^D)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (n:SourceBlocks s R seed K Z ξ p E):
    let Tsec:=firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData);
    0< Tsec ∧ 0< dyadicScale (n 1) ∧
      dyadicScale (n 1)≤4*frequencyRadius Tsec Z ξ ∧
      8*dyadicScale (n 1)≤ Z^(amplifierCap A D ξcap) ∧
      Tsec≤1*firstNominalScale p.val.1 p.val.2
        (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=> P.val) E})
        K (volume s.toData):=by
  have hz:1≤ Z:=by linarith
  have hzpos:0< Z:=by linarith
  have hfreq:=retained_scale_le _ (n 1) (source_dyad_retained s R seed K Z ξ p E n)
  have hV':volume s.toData≤ Z^(max A D):=hV.trans
    (Real.rpow_le_rpow_of_exponent_le hz (le_max_left _ _))
  have hKi':K⁻¹≤ Z^(max A D):=hKi.trans
    (Real.rpow_le_rpow_of_exponent_le hz (le_max_right _ _))
  have hrad:=local_frequency_radius_cap p.val.1 p.val.2 E K (volume s.toData) Z
    (max A D) ξ hK (volume_pos s.toData).le hz hV' hKi'
  have hrad':localRadius s R seed K Z ξ p E≤ Z^(3*max A D+ξcap/2):=by
    apply hrad.trans
    exact Real.rpow_le_rpow_of_exponent_le hz (by linarith)
  refine ⟨source_nominal_positive s R seed K hK p E,dyadicScale_pos _,hfreq,?_,?_⟩
  · calc
      _≤32*Z^(3*max A D+ξcap/2):=by linarith
      _≤ Z*Z^(3*max A D+ξcap/2):=
        mul_le_mul_of_nonneg_right hZ (Real.rpow_nonneg hzpos.le _)
      _=Z^(amplifierCap A D ξcap):=by
        unfold amplifierCap
        rw [Real.rpow_add_one hzpos.ne']
        ring
  · rw [one_mul]
    exact (source_nominal_span s R seed K p E).le

omit [DecidableEq ι] in
lemma source_frequency_ledger (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)(hK:0< K)(hZ:1< Z)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (n:SourceBlocks s R seed K Z ξ p E):
    Real.logb Z (dyadicScale (n 1))≤
      Real.logb Z (firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData))+
        frequencyLoss Z 1 ξ:=by
  apply retained_first_dyad_enclosure _ Z 1 _ ξ hZ (by norm_num) _ (n 1)
    (source_dyad_retained s R seed K Z ξ p E n)
  rw [one_mul,Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne'
    (source_nominal_positive s R seed K hK p E)]

theorem fixed_endpoint_radius (N:ℕ)(upper b₁ b₂ A Z:ℝ)
    (hu:1≤ upper)(hb₁:0≤ b₁)(hb₂:0≤ b₂)(hZ:32≤ Z)
    (hfixed:upper^N*b₁*b₂≤ Z)
    (s:Input ι)(hN:Fintype.card ι≤ N)
    (hhi:∀i,|s.hi i|≤ upper)(hs₁:|s.b₁|≤ b₁)(hs₂:|s.b₂|≤ b₂)
    (hV:volume s.toData≤ Z^A):sourceRadius s≤ Z^(A+1):=by
  apply input_radius_cap (fun _:ι=> upper) b₁ b₂ A Z s hhi hs₁ hs₂ (by linarith) _ hV
  have hpow:upper^(Fintype.card ι)≤ upper^N:=pow_le_pow_right₀ hu hN
  simpa only [Finset.prod_const,Finset.card_univ] using
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hb₁) hb₂).trans hfixed

theorem eventually_source_admission (N:ℕ)(upper b₁ b₂ A D ξcap:ℝ)
    (hu:1≤ upper)(hb₁:0≤ b₁)(hb₂:0≤ b₂):
    ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀(α:Type u)[Fintype α][DecidableEq α],∀s:Input α,Fintype.card α≤ N →
      (∀i,|s.hi i|≤ upper) → |s.b₁|≤ b₁ → |s.b₂|≤ b₂ →
      ∀(R seed:Ideal O)(K ξ:ℝ),0< K → ξ≤ξcap →
      volume s.toData≤ Z^A → K⁻¹≤ Z^D →
      sourceRadius s≤ Z^(A+1) ∧
      ∀(p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
        (n:SourceBlocks s R seed K Z ξ p E),
      let Tsec:=firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData);
      0< Tsec ∧ 1< dyadicScale (n 1) ∧
        dyadicScale (n 1)≤4*frequencyRadius Tsec Z ξ ∧
        8*dyadicScale (n 1)≤ Z^(amplifierCap A D ξcap) ∧
        Tsec≤1*firstNominalScale p.val.1 p.val.2
          (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=> P.val) E})
          K (volume s.toData):=by
  filter_upwards [eventually_ge_atTop (32:ℝ),eventually_ge_atTop (upper^N*b₁*b₂)] with Z hZ hf
  refine ⟨by linarith,?_⟩
  intro α _ _ s hN hhi hs₁ hs₂ R seed K ξ hK hξ hV hKi
  refine ⟨fixed_endpoint_radius N upper b₁ b₂ A Z hu hb₁ hb₂ hZ hf s hN hhi hs₁ hs₂ hV,?_⟩
  intro p E n
  have hh:=source_amplifier_packet A D ξcap Z hZ s R seed K ξ hK hξ hV hKi p E n
  exact ⟨hh.1,source_dyad_gt_one s R seed K Z ξ p E n,hh.2.2⟩

end CenteredMomentEnergyFirstAnnularAdmission

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentEnergyFirstRawScaleAdmission
open HeckeFamily  CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentEnergyAmplifiedRayDictionary CenteredMomentFirstAnnularInput
open CenteredMomentFirstChildLower CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization
local notation "O"=> Eisenstein.O
variable {α:Type*}[Fintype α]
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _

def parentLower (s:Input α)(Z:ℝ):ℝ:=
  min (min (Real.logb Z s.X₁) (Real.logb Z s.X₂))
    (min (Real.logb Z s.Y₁) (Real.logb Z s.Y₂))

theorem parent_lower_scales (s:Input α)(Z:ℝ)(hZ:1< Z):
    Z^(parentLower s Z)≤ s.X₁ ∧ Z^(parentLower s Z)≤ s.X₂ ∧
    Z^(parentLower s Z)≤ s.Y₁ ∧ Z^(parentLower s Z)≤ s.Y₂:=by
  have h (X:ℝ)(hX:0< X)(hx:parentLower s Z≤ Real.logb Z X):Z^(parentLower s Z)≤ X:=by
    calc
      _≤ Z^(Real.logb Z X):=Real.rpow_le_rpow_of_exponent_le hZ.le hx
      _=X:=Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hX
  exact ⟨h _ s.X₁_pos ((min_le_left _ _).trans (min_le_left _ _)),
    h _ s.X₂_pos ((min_le_left _ _).trans (min_le_right _ _)),
    h _ s.Y₁_pos ((min_le_right _ _).trans (min_le_left _ _)),
    h _ s.Y₂_pos ((min_le_right _ _).trans (min_le_right _ _))⟩

theorem main_minimum_lower (s:Input α)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t Z:ℝ)(hZ:1< Z):
    let d:=child s C R B τ t
    let r:=parentLower s Z-Real.logb Z (C.absNorm:ℝ)
    Z^r≤ d.X₁ ∧ Z^r≤ d.X₂ ∧ Z^r≤ d.Y₁ ∧ Z^r≤ d.Y₂:=by
  have h:=parent_lower_scales s Z hZ
  exact child_lower s C R hC B τ t Z (parentLower s Z) hZ h.1 h.2.1 h.2.2.1 h.2.2.2

theorem active_error_lower (s:Input α)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t:ℝ)(p:O)(hp:p≠0)(k:ℕ)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools ((Ideal.span {p})^k))
    (υ:Character)(v Z r:ℝ)(hZ:1< Z)
    (hX₁:Z^r≤ s.X₁)(hX₂:Z^r≤ s.X₂)(hY₁:Z^r≤ s.Y₁)(hY₂:Z^r≤ s.Y₂):
    let d:=child (activeInput (child s C R B τ t)) ((Ideal.span {p})^k) (R*C) Bp υ v
    let r':=r-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k
    Z^r'≤ d.X₁ ∧ Z^r'≤ d.X₂ ∧ Z^r'≤ d.Y₁ ∧ Z^r'≤ d.Y₂:=by
  have hc:=child_lower s C R hC B τ t Z r hZ hX₁ hX₂ hY₁ hY₂
  have hpn:(Ideal.span {p}:Ideal O)≠0:=Ideal.span_singleton_eq_bot.not.mpr hp
  have hh:=child_lower (activeInput (child s C R B τ t)) ((Ideal.span {p})^k) (R*C)
    (pow_ne_zero k hpn) Bp υ v Z (r-Real.logb Z (C.absNorm:ℝ)) hZ
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  have he:Real.logb Z (((Ideal.span {p}:Ideal O)^k).absNorm:ℝ)=errorRemoval p Z k:=by
    rw [map_pow,Nat.cast_pow,Real.logb_pow]
    rfl
  simpa only [he] using hh

theorem restored_error_lower (s:Input α)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t:ℝ)(p:O)(hp:p≠0)(k:ℕ)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools ((Ideal.span {p})^k))
    (υ:Character)(v Z r:ℝ)(hZ:1< Z)
    (hX₁:Z^r≤ s.X₁)(hX₂:Z^r≤ s.X₂)(hY₁:Z^r≤ s.Y₁)(hY₂:Z^r≤ s.Y₂):
    let d:=restoredError s C R B τ t (Ideal.span {p}) k Bp υ v
    let r':=r-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k
    Z^r'≤ d.X₁ ∧ Z^r'≤ d.X₂ ∧ Z^r'≤ d.Y₁ ∧ Z^r'≤ d.Y₂:=by
  exact active_error_lower s C R hC B τ t p hp k Bp υ v Z r hZ hX₁ hX₂ hY₁ hY₂

theorem error_minimum_lower (s:Input α)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t:ℝ)(p:O)(hp:p≠0)(k:ℕ)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools ((Ideal.span {p})^k))
    (υ:Character)(v Z:ℝ)(hZ:1< Z):
    let d:=child (activeInput (child s C R B τ t)) ((Ideal.span {p})^k) (R*C) Bp υ v
    let r':=parentLower s Z-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k
    Z^r'≤ d.X₁ ∧ Z^r'≤ d.X₂ ∧ Z^r'≤ d.Y₁ ∧ Z^r'≤ d.Y₂:=by
  have h:=parent_lower_scales s Z hZ
  exact active_error_lower s C R hC B τ t p hp k Bp υ v Z (parentLower s Z) hZ
    h.1 h.2.1 h.2.2.1 h.2.2.2

end CenteredMomentEnergyFirstRawScaleAdmission

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentEnergyFirstLiveAdmission
open HeckeFamily CanonicalQuadraticSieve  
open Eisenstein CenteredMomentCanonicalFirst CenteredMomentSourceMass
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentAmplificationChildSourceCaps CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstSecondInputGates CenteredMomentFirstSecondActiveErrorGates
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentFirstAmplifiedRadiusLower CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstAnnularInput CenteredMomentSectorLocalization
open CenteredMomentSecondInputCapacitySource CenteredMomentFirstSourceConductorCaps
open CenteredMomentEnergyInputParentCapacity CenteredMomentEnergyBands
open CenteredMomentEnergyAmplifiedChildWidth CenteredMomentSecondHeightFamily
open CenteredMomentSourceLiveColumn CenteredMomentActiveSource
open CenteredMomentPrimePool CenteredMomentPrimeElements
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentChildRows CompletedGauss RayFourExpansion
open CenteredMomentLogDyadic CenteredMomentRowNorm
local notation "O" => Eisenstein.O
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem first_block_active_rows_nonempty
    (η : Character) (m A : O) (t : ℝ) (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (E : Finset (CommonIndex C D)) (rows : Finset O) (W : 𝓢(ℝ,ℂ))
    (K : ℝ) (n : Fin 4 → ℤ)
    (hne : block η m A t S c C D hC hD E rows W (fun _ => logAnnulus) K
      (dyadicScale (n 0)) (dyadicScale (n 1))
      (dyadicScale (n 2)) (dyadicScale (n 3)) ≠ 0) :
    (activeRows rows n).Nonempty := by
  by_contra h
  have he : activeRows rows n = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  apply hne
  rw [block_activeRows, he]
  simp only [block, Finset.sum_empty, mul_zero]

theorem original_both_columns {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (R seed C D : Ideal O) (hseed : Squarefree seed)
    (hz₁ : s.W₁ 0 = 0) (hz₂ : s.W₂ 0 = 0)
    (hC : Supported C) (hD : Supported D)
    (hlabel : (C,D) ∈ CenteredMomentFirstSectors.commonLabels
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)))
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed))))
    (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayCharacter)
    (F : FixedPair s.η C D hC E ξ₁ ξ₂) (t T : ℝ) (L : Ideal O) (z : O) :
    (Real.sqrt T : ℂ)⁻¹ * leftChild (original s R seed) s.η
      (fixedBadMask*cubicIdealGenerator R) t C D hC E ξ₁ L z =
      allocatedPolynomial (original s R seed) C L F.left t T z ∧
    (Real.sqrt T : ℂ)⁻¹ * rightChild (original s R seed) s.η
      (fixedBadMask*cubicIdealGenerator R) t C D hC hD E ξ₂ L (-z) =
      allocatedPolynomial (original s R seed) D L F.right t T (-z) := by
  have hg := actual_common_gates s R seed hseed hz₁ hz₂ C D hlabel
  exact F.original_data hD hg.2.2.1 (original s R seed) s.pools_ne
    (fun i I hI => s.prime i I hI) hg.2.2.2.1 hg.2.2.2.2.1 t T L z

def columnIdeal (C D : Ideal O) (right : Bool) : Ideal O := if right then D else C

def oppositeIdeal (C D : Ideal O) (right : Bool) : Ideal O := if right then C else D

def columnMainRadius (C D : Ideal O) (E : Finset (CommonIndex C D))
    (K V Z σ δ reserve : ℝ) (right : Bool) : ℝ :=
  mainCommonRadius Z (Real.logb Z ((oppositeIdeal C D right).absNorm : ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E}) K V))
    (Real.logb Z ((columnIdeal C D right).absNorm : ℝ)) σ δ reserve

def columnErrorRadius (C D : Ideal O) (E : Finset (CommonIndex C D))
    (K V Z σ δ reserve : ℝ) (right : Bool) (p : O) (k : ℕ) : ℝ :=
  errorCommonRadius Z (Real.logb Z ((oppositeIdeal C D right).absNorm : ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E}) K V))
    (Real.logb Z ((columnIdeal C D right).absNorm : ℝ)) σ δ reserve p k

lemma columnMainRadius_left (C D : Ideal O) (E : Finset (CommonIndex C D))
    (K V Z σ δ reserve : ℝ) :
    columnMainRadius C D E K V Z σ δ reserve false = mainRadius C D E K V Z σ δ reserve := rfl

lemma columnErrorRadius_left (C D : Ideal O) (E : Finset (CommonIndex C D))
    (K V Z σ δ reserve : ℝ) (p : O) (k : ℕ) :
    columnErrorRadius C D E K V Z σ δ reserve false p k =
      errorRadius C D E K V Z σ δ reserve p k := rfl

lemma common_exponent_le (A P ξ : ℝ) (hA : 0 ≤ A) (hP : 0 ≤ P) (hξ : ξ ≤ 1) :
    commonExponent A 0 P (A+1) (3*A+3) 1 ξ ≤ readyBudget A P := by
  unfold commonExponent readyBudget
  exact max_le (by linarith) (max_le (by linarith) (max_le (by linarith) (by linarith)))

lemma error_exponent_le (A P σ ξ : ℝ) (hA : 0 ≤ A) (hP : 0 ≤ P)
    (hσ : σ ≤ 1) (hξ : ξ ≤ 1) :
    exponent A 0 P (3*A+3+σ/3) 1 ξ ≤ readyBudget A P := by
  unfold exponent readyBudget
  exact max_le (by linarith) (max_le (by linarith) (max_le (by linarith) (by linarith)))

lemma ready_mono {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Input ι) (R : Ideal O)
    (K Z ξ B B' : ℝ) (hZ : 1 ≤ Z) (hB : B ≤ B')
    (h : Ready s R K Z ξ B) : Ready s R K Z ξ B' := by
  have hp := Real.rpow_le_rpow_of_exponent_le hZ hB
  exact ⟨h.puncture_ne,h.scale_pos,h.volume_cap.trans hp,h.source_nonneg,
    h.source_cap.trans hp,h.conductor_cap.trans hp,h.puncture_cap.trans hp,
    h.nominal_pos,h.nominal_cap.trans hp,h.frequency_pos,h.frequency_cap.trans hp⟩

lemma lower_profile_zero (W : ℝ → ℂ) (a : ℝ) (ha : 0 < a)
    (h : ∀ x, W x ≠ 0 → a ≤ x) : W 0 = 0 := by
  by_contra hn
  exact (not_le_of_gt ha) (h 0 hn)

theorem main_lower_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (l a : ℝ) (hl : 0 < l) (ha : 0 < a)
    (s : Input ι) (hc : Fintype.card ι ≤ N) (hs : l ≤ s.lower)
    (hW₁ : ∀ x, s.W₁ x ≠ 0 → a ≤ x) (hW₂ : ∀ x, s.W₂ x ≠ 0 → a ≤ x)
    (C R seed : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    ∀ I : Ideal O, coefficient (child s C R B τ t) (R*C) seed I ≠ 0 →
      lowerFactor N l a * volume (child s C R B τ t) ≤ (I.absNorm : ℝ) := by
  intro I hI
  exact actual_lower_support N l a hl ha (child s C R B τ t)
    ((live_card_le B.val).trans hc) hs hW₁ hW₂ (R*C) seed I hI

theorem error_lower_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (l a : ℝ) (hl : 0 < l) (ha : 0 < a)
    (s : Input ι) (hc : Fintype.card ι ≤ N) (hs : l ≤ s.lower)
    (hW₁ : ∀ x, s.W₁ x ≠ 0 → a ≤ x) (hW₂ : ∀ x, s.W₂ x ≠ 0 → a ≤ x)
    (C R seed : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    ∀ I : Ideal O, coefficient (errorInput s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed I ≠ 0 →
      lowerFactor N l a * volume (errorInput s C R B τ t Q k Bp υ v) ≤ (I.absNorm : ℝ) := by
  intro I hI
  exact actual_lower_support N l a hl ha (errorInput s C R B τ t Q k Bp υ v)
    ((live_card_le Bp.val).trans ((live_card_le B.val).trans hc))
    hs hW₁ hW₂ ((R*C)*(Q^k)) seed I hI

theorem eventual_parent_radius (N : ℕ) (b b₁ b₂ : ℝ)
    (hb : 1 ≤ b) (hb₁ : 1 ≤ b₁) (hb₂ : 1 ≤ b₂) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
      ∀ s : Input ι, Fintype.card ι ≤ N → Endpoints b b₁ b₂ s →
      ∀ A : ℝ, volume s ≤ Z^A → sourceRadius s ≤ Z^(A+1) := by
  let G := b^N*b₁*b₂
  have hG : 1 ≤ G := by
    have hp : 1 ≤ b^N := one_le_pow₀ hb
    dsimp [G]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hp hb₁) hb₂
  filter_upwards [eventual_geometry G 1 hG (by norm_num)] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro ι _ _ s hc he A hV
  have hr := (radius_bound N b b₁ b₂ hb hb₁ hb₂ s hc he).2
  have hg : G ≤ Z := by simpa only [Real.rpow_one] using hZ.2.1
  apply hr.trans
  calc
    G * volume s ≤ Z * Z^A := mul_le_mul hg hV (volume_pos s).le (zero_lt_one.trans hZ.1).le
    _ = Z^(A+1) := by rw [Real.rpow_add_one (zero_lt_one.trans hZ.1).ne']; ring

theorem eventually_main_packet (N : ℕ) (b b₁ b₂ l a A P : ℝ)
    (hb : 1 ≤ b) (hb₁ : 1 ≤ b₁) (hb₂ : 1 ≤ b₂)
    (hl : 0 < l) (ha : 0 < a) (hA : 0 ≤ A) (hP : 0 ≤ P) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
      ∀ s : Input ι, Fintype.card ι ≤ N → Endpoints b b₁ b₂ s → l ≤ s.lower →
      (∀ x, s.W₁ x ≠ 0 → a ≤ x) → (∀ x, s.W₂ x ≠ 0 → a ≤ x) →
      ∀ κ : ℝ, 1/6 ≤ κ → (∀ i, 1 ≤ s.P i) →
      length Z s.X₁ + length Z s.X₂ + 6*κ*(∑ i, Real.logb Z (s.P i)) ≤ A →
      (s.η.modulus.absNorm : ℝ) ≤ Z^A →
      ∀ R seed : Ideal O, R ≠ 0 → (R.absNorm : ℝ) ≤ Z^P → Squarefree seed →
      ∀ C D : Ideal O, ∀ hC : Supported C, ∀ hD : Supported D,
      (C,D) ∈ CenteredMomentFirstSectors.commonLabels
        (CenteredMomentSourceRow.supportedColumns (activeSource
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)))
        (CenteredMomentSourceRow.supportedColumns (activeSource
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed))) →
      ∀ E : Finset (CommonIndex C D), ∀ ξ₁ ξ₂ : RayCharacter,
      ∀ F : FixedPair s.η C D hC E ξ₁ ξ₂, ∀ τ : Character, τ = F.left ∨ τ = F.right →
      ∀ K Csec Tsec σ ξ reserve : ℝ, 0 < K → 0 < Csec → 0 ≤ σ → 0 ≤ ξ → ξ ≤ 1 →
      0 ≤ reserve →
      Tsec ≤ Csec * firstNominalScale C D
        (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E}) K (volume s) →
      ∀ rows : Finset O, ∀ W : 𝓢(ℝ,ℂ), ∀ n : Fin 4 → ℤ,
      Retained (frequencyRadius Tsec Z ξ) (n 1) →
      block s.η (fixedBadMask*cubicIdealGenerator R) 1 s.t
        (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)
        C D hC hD E rows W (fun _ => logAnnulus) K
        (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3)) ≠ 0 →
      ∀ side : Bool, ∀ B : actualAllocations s.pools (columnIdeal C D side), ∀ t : ℝ,
      frozenCoefficient B.val (columnIdeal C D side) R s.ν s.W s.P ≠ 0 →
      let Km := columnMainRadius C D E K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve side
      Ready (child s (columnIdeal C D side) R B τ t) (R*columnIdeal C D side) Km Z ξ (readyBudget A P) ∧
      (∀ I : Ideal O, coefficient (child s (columnIdeal C D side) R B τ t) (R*columnIdeal C D side) seed I ≠ 0 →
        lowerFactor N l a * volume (child s (columnIdeal C D side) R B τ t) ≤ (I.absNorm : ℝ)) := by
  filter_upwards [eventually_common_ready N b b₁ b₂ 1 hb hb₁ hb₂ (by norm_num),
    eventual_parent_radius N b b₁ b₂ hb hb₁ hb₂,
    eventually_caps 1 (by norm_num)] with Z hready hradius hchars
  refine ⟨hready.1, ?_⟩
  intro ι _ _ s hc he hs hW₁ hW₂ κ hκ hPs hcapacity hη R seed hR hRN hseed
    C D hC hD hlabel E ξ₁ ξ₂ F τ hτ K Csec Tsec σ ξ reserve hK hCsec hσ hξ hξ1
    hreserve hsec rows W n hn hblock side B t hB
  dsimp only
  have hz := hready.1
  have hV := original_volume_cap s Z κ A hz hκ hPs hcapacity
  have hH := hradius.2 s hc he A hV
  have hz₁ := lower_profile_zero s.W₁ a ha hW₁
  have hz₂ := lower_profile_zero s.W₂ a ha hW₂
  have hcdata := actual_common_gates s R seed hseed hz₁ hz₂ C D hlabel
  have hCN := hcdata.2.2.2.2.2.1.trans hH
  have hJN : ((columnIdeal C D side).absNorm : ℝ) ≤ Z^(A+1) := by
    cases side
    · exact hCN
    · exact hcdata.2.2.2.2.2.2.trans hH
  have ht := hchars.2 s.η C D hC E ξ₁ ξ₂ F A (A+1) hη hCN
  have htau : (τ.modulus.absNorm : ℝ) ≤ Z^(3*A+3) := by
    have hx : (τ.modulus.absNorm : ℝ) ≤ Z^(A+2*(A+1)+1) := by
      rcases hτ with rfl | rfl
      · exact ht.1
      · exact ht.2.1
    simpa only [show A+2*(A+1)+1 = 3*A+3 by ring] using hx
  have hE : Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E} ≠ 0 := by
    exact Ideal.span_singleton_eq_bot.not.mpr (TruncatedPrincipalPoisson.primeSubsetGenerator_ne_zero _ _)
  have hne := first_block_active_rows_nonempty s.η (fixedBadMask*cubicIdealGenerator R) 1 s.t
    _ _ C D hC hD E rows W K n hblock
  have hrec := (active_row_reciprocals C D _ hE K (volume s) Z Csec Tsec ξ
    (Real.logb Z ((oppositeIdeal C D side).absNorm : ℝ))
    (Real.logb Z ((columnIdeal C D side).absNorm : ℝ)) σ reserve
    hK (volume_pos s) hz hCsec hσ hreserve hsec rows n hn hne 1 1).1
  have hKm : 0 < columnMainRadius C D E K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve side := by
    unfold columnMainRadius mainCommonRadius
    positivity
  have hKmInv : (columnMainRadius C D E K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve side)⁻¹ ≤ Z^(0 : ℝ) := by
    simpa only [columnMainRadius,nominalLog,Real.rpow_zero] using hrec
  have hr := hready.2 s hc he (columnIdeal C D side) R B τ t hR hB _ A 0 P (A+1) (3*A+3) ξ
    hKm hξ hV hKmInv hRN hJN htau
  exact ⟨ready_mono _ _ _ Z ξ _ _ hz.le (common_exponent_le A P ξ hA hP hξ1) hr,
    main_lower_support N l a hl ha s hc hs hW₁ hW₂ (columnIdeal C D side) R seed B τ t⟩

theorem eventually_error_packet (N : ℕ) (b b₁ b₂ l a A P : ℝ)
    (hb : 1 ≤ b) (hb₁ : 1 ≤ b₁) (hb₂ : 1 ≤ b₂)
    (hl : 0 < l) (ha : 0 < a) (hA : 0 ≤ A) (hP : 0 ≤ P) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
      ∀ s : Input ι, Fintype.card ι ≤ N → Endpoints b b₁ b₂ s → l ≤ s.lower →
      (∀ x, s.W₁ x ≠ 0 → a ≤ x) → (∀ x, s.W₂ x ≠ 0 → a ≤ x) →
      ∀ κ : ℝ, 1/6 ≤ κ → (∀ i, 1 ≤ s.P i) →
      length Z s.X₁ + length Z s.X₂ + 6*κ*(∑ i, Real.logb Z (s.P i)) ≤ A →
      (s.η.modulus.absNorm : ℝ) ≤ Z^A →
      ∀ R seed : Ideal O, R ≠ 0 → (R.absNorm : ℝ) ≤ Z^P → Squarefree seed →
      ∀ C D : Ideal O, ∀ hC : Supported C, ∀ hD : Supported D,
      (C,D) ∈ CenteredMomentFirstSectors.commonLabels
        (CenteredMomentSourceRow.supportedColumns (activeSource
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)))
        (CenteredMomentSourceRow.supportedColumns (activeSource
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed))) →
      ∀ E : Finset (CommonIndex C D), ∀ ξ₁ ξ₂ : RayCharacter,
      ∀ F : FixedPair s.η C D hC E ξ₁ ξ₂, ∀ τ : Character, τ = F.left ∨ τ = F.right →
      ∀ K Csec Tsec σ ξ reserve : ℝ, 0 < K → 0 < Csec → 0 ≤ σ → σ ≤ 1 →
      0 ≤ ξ → ξ ≤ 1 → 0 ≤ reserve →
      Tsec ≤ Csec * firstNominalScale C D
        (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E}) K (volume s) →
      ∀ rows : Finset O, ∀ W : 𝓢(ℝ,ℂ), ∀ n : Fin 4 → ℤ,
      Retained (frequencyRadius Tsec Z ξ) (n 1) →
      block s.η (fixedBadMask*cubicIdealGenerator R) 1 s.t
        (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)
        C D hC hD E rows W (fun _ => logAnnulus) K
        (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3)) ≠ 0 →
      ∀ side : Bool, ∀ B : actualAllocations s.pools (columnIdeal C D side), ∀ t : ℝ,
      frozenCoefficient B.val (columnIdeal C D side) R s.ν s.W s.P ≠ 0 →
      ∀ (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (Sbad : Finset (Ideal O)),
      fixedBadPrimes ⊆ Sbad →
      ∀ p ∈ elementPool (primePool M H Sbad (1/2) 1 (Z^(σ/3))),
      ∀ k : ℕ, k = 1 ∨ k = 6 ∨ k = 7 →
      (∀ i, ∀ I ∈ (activeInput (child s (columnIdeal C D side) R B τ t)).slots i, IsCoprime (Ideal.span {p}) I) →
      ∀ Bp : actualAllocations (activeInput (child s (columnIdeal C D side) R B τ t)).pools ((Ideal.span {p})^k),
      ∀ (χ : RayCharacter) (υ : Character) (v : ℝ),
      υ.modulus.absNorm ≤ radicalBound (childCharacter τ χ) fixedBadMask p (errorMovingExponent (k-1)) →
      let d := errorInput s (columnIdeal C D side) R B τ t (Ideal.span {p}) k Bp υ v
      let Re := (R*columnIdeal C D side)*(Ideal.span {p})^k
      let Ke := columnErrorRadius C D E K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve side p k
      ((∀ I : Ideal O, coefficient d Re seed I = 0) ∧ normalizedGaussSource d Re seed ballProfile Ke = 0) ∨
      (Ready d Re Ke Z ξ (readyBudget A P) ∧
        (∀ I : Ideal O, coefficient d Re seed I ≠ 0 →
          lowerFactor N l a * volume d ≤ (I.absNorm : ℝ))) := by
  filter_upwards [eventually_active_error_ready N b b₁ b₂ 1 hb hb₁ hb₂ (by norm_num),
    eventual_parent_radius N b b₁ b₂ hb hb₁ hb₂,
    eventually_caps 1 (by norm_num)] with Z hready hradius hchars
  refine ⟨hready.1, ?_⟩
  intro ι _ _ s hc he hs hW₁ hW₂ κ hκ hPs hcapacity hη R seed hR hRN hseed
    C D hC hD hlabel E ξ₁ ξ₂ F τ hτ K Csec Tsec σ ξ reserve hK hCsec hσ hσ1
    hξ hξ1 hreserve hsec rows W n hn hblock side B t hB M _ H Sbad hbad p hp k _hk
    hslot Bp χ υ v hυ
  dsimp only
  let d := errorInput s (columnIdeal C D side) R B τ t (Ideal.span {p}) k Bp υ v
  let Re := (R*columnIdeal C D side)*(Ideal.span {p})^k
  let Ke := columnErrorRadius C D E K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve side p k
  by_cases hdead : ∀ I : Ideal O, coefficient d Re seed I = 0
  · exact Or.inl ⟨hdead, normalized_zero d Re seed hdead ballProfile Ke⟩
  right
  have hlive : ∃ I : Ideal O, (original d Re seed).beta I ≠ 0 := by
    simpa only [original_beta,not_forall] using hdead
  have hz := hready.1
  have hV := original_volume_cap s Z κ A hz hκ hPs hcapacity
  have hH := hradius.2 s hc he A hV
  have hz₁ := lower_profile_zero s.W₁ a ha hW₁
  have hz₂ := lower_profile_zero s.W₂ a ha hW₂
  have hcdata := actual_common_gates s R seed hseed hz₁ hz₂ C D hlabel
  have hCN := hcdata.2.2.2.2.2.1.trans hH
  have hJN : ((columnIdeal C D side).absNorm : ℝ) ≤ Z^(A+1) := by
    cases side
    · exact hCN
    · exact hcdata.2.2.2.2.2.2.trans hH
  have hd := elementPool_data _
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(σ/3)) Q hQ).1)
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(σ/3)) Q hQ).2) p hp
  have hp0 : p ≠ 0 := hd.1.ne_zero
  have hQ : Ideal.span {p} ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hp0
  have hpupper := (pool_prime_log_range M H Sbad hbad Z σ hz p hp).2
  have hPN : ((Ideal.span {p}).absNorm : ℝ) ≤ Z^(σ/3) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hz.le hpupper
    rwa [Real.rpow_logb (zero_lt_one.trans hz) (ne_of_gt hz) (normValue_pos p hp0)] at hh
  have ht := hchars.2 s.η C D hC E ξ₁ ξ₂ F A (A+1) hη hCN
  have hv : (υ.modulus.absNorm : ℝ) ≤ Z^(3*A+3+σ/3) := by
    have hh := ht.2.2 τ υ hτ χ p hp0 (errorMovingExponent (k-1)) (σ/3) hυ hPN
    simpa only [show A+2*(A+1)+σ/3+1 = 3*A+3+σ/3 by ring] using hh
  have hE : Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E} ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (TruncatedPrincipalPoisson.primeSubsetGenerator_ne_zero _ _)
  have hne := first_block_active_rows_nonempty s.η (fixedBadMask*cubicIdealGenerator R) 1 s.t
    _ _ C D hC hD E rows W K n hblock
  have hrec := (active_row_reciprocals C D _ hE K (volume s) Z Csec Tsec ξ
    (Real.logb Z ((oppositeIdeal C D side).absNorm : ℝ))
    (Real.logb Z ((columnIdeal C D side).absNorm : ℝ)) σ reserve
    hK (volume_pos s) hz hCsec hσ hreserve hsec rows n hn hne p k).2
  have hKe : 0 < Ke := by
    dsimp [Ke,columnErrorRadius,errorCommonRadius]
    positivity
  have hKeInv : Ke⁻¹ ≤ Z^(0 : ℝ) := by
    simpa only [Ke,columnErrorRadius,nominalLog,Real.rpow_zero] using hrec
  have hr := hready.2 s hc he (columnIdeal C D side) R seed B τ t hR hB _ hQ k hslot Bp υ v Ke
    A 0 P (3*A+3+σ/3) ξ hKe hξ hz₁ hz₂ hV hKeInv hRN hv hlive
  exact ⟨ready_mono _ _ Ke Z ξ _ _ hz.le (error_exponent_le A P σ ξ hA hP hσ1 hξ1) hr,
    error_lower_support N l a hl ha s hc hs hW₁ hW₂ (columnIdeal C D side) R seed B τ t _ k Bp υ v⟩

end CenteredMomentEnergyFirstLiveAdmission

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentEnergyAmplifierFamilyAdmission
open HeckeFamily CanonicalQuadraticSieve  Eisenstein
open CenteredMomentFirstSourceConductorCaps CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplificationActiveFactor CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily CenteredMomentChildRows
open CenteredMomentSectorLocalization CenteredMomentFirstAmplifiedFourCoefficients
local notation "O"=> Eisenstein.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

def referenceCost : ℝ := max 1 rayCost

lemma referenceCost_ge_one : 1≤ referenceCost := le_max_left _ _

theorem actual_error_reference_cap (ρ υ:Character)(χ:RayFourExpansion.RayCharacter)
    (p:O)(hp:p≠0)(n:ℕ)(hn:n=0 ∨ n=5 ∨ n=6)(Z:ℝ)(hZ:1< Z)
    (hυ:υ.modulus.absNorm≤ radicalBound (childCharacter ρ χ) fixedBadMask p
      (errorMovingExponent n)):
    (υ.modulus.absNorm:ℝ)≤ referenceCost*(ρ.modulus.absNorm:ℝ)*
      Z^(errorMoving p Z (n+1)):=by
  have hray:=CenteredMomentSecondRadicalBudget.child_modulus_bound ρ χ
  have hN:(υ.modulus.absNorm:ℝ)≤
      ((childCharacter ρ χ).modulus.absNorm:ℝ)*(Ideal.span {fixedBadMask}).absNorm*
        (Ideal.span {(72:O)}).absNorm*Z^(errorMoving p Z (n+1)):=by
    rw [←radicalBound_error_power (childCharacter ρ χ) fixedBadMask p hp Z hZ n hn]
    exact_mod_cast hυ
  have hr:((childCharacter ρ χ).modulus.absNorm:ℝ)≤
      (ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm:=by exact_mod_cast hray
  calc
    _≤((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*
        (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
        Z^(errorMoving p Z (n+1)):=by apply hN.trans;gcongr
    _=rayCost*(ρ.modulus.absNorm:ℝ)*Z^(errorMoving p Z (n+1)):=by
      unfold rayCost fixedPresentationCost;ring
    _≤ _:=by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
      exact mul_le_mul_of_nonneg_right (le_max_right 1 rayCost) (Nat.cast_nonneg _)

end CenteredMomentEnergyAmplifierFamilyAdmission

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentEnergyFirstHighExceptionalPowers
open HeckeFamily CanonicalQuadraticSieve CompletedGauss Eisenstein 
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstMixedAllowance CenteredMomentFirstMixedChild
open CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstPhysicalSource CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
open CenteredMomentCommonRadiusSaving CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentRankinRadical
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationErrorEnergy
local notation "O"=> Eisenstein.O
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

open CenteredMomentFirstMixedExceptionalCap CenteredMomentFirstMixedCommonRadius

theorem actual_main_exceptional_uniform_cap (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex I J=> P.val) A})
    (K X Z j sigma delta reserve Mdecl : ℝ) (hZ : 1< Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (hK:0< K)(hX:0< X)
    (hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤ Mdecl) :
    ((X/(I.absNorm:ℝ))*(X/(I.absNorm:ℝ))^((1:ℝ)/3)*(mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)^((5:ℝ)/6)*Z^(-sigma/3)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max (Mdecl/4-Real.logb Z (I.absNorm:ℝ)) 0/3)≤
      Z^(Real.logb Z X-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+4*sigma/3+5*(delta+reserve)/6):=by
  have hz:0< Z:=zero_lt_one.trans hZ
  have hf:=fixed_presentation_log_nonneg Z hZ
  have hr : 0 ≤ max (Mdecl/4-Real.logb Z (I.absNorm:ℝ)) 0 := le_max_right _ _
  have hrLower:=le_max_left (Mdecl/4-Real.logb Z (I.absNorm:ℝ)) (0:ℝ)
  have hi : 0 ≤ Real.logb Z (I.absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  have hc:=commonPart_of_equal_support I J hI.1 hIJ
  have hd:=commonPart_of_equal_support J I hJ.1 hIJ.symm
  have hs:=actual_main_column_saving η τ fixedBadMask I J E hI hJ A
    K X Z j sigma delta reserve hZ hmod
  dsimp only at hs
  simp only [hc,hd,extracted_allowance_eq I J hI.1 hJ.1 hIJ Z] at hs
  have he:=(actual_exceptional_reference η τ I J hI hJ hIJ A K X Z j
    (Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)-j) 0 0 (sigma/3) hK hX hZ hmod).le
  rw [←hE] at he
  have hrad:0< mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve:=by unfold mainCommonRadius;positivity
  rw [show j+(Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)-j)=Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve) by ring,
    Real.rpow_logb hz hZ.ne' hrad] at he
  simp only [neg_zero,Real.rpow_zero,mul_one,div_one] at he
  have hexp:-sigma/3=-(sigma/3):=by ring
  rw [hexp]
  have hmul:=mul_le_mul_of_nonneg_right he
    (Real.rpow_nonneg hz.le (-2*max (Mdecl/4-Real.logb Z (I.absNorm:ℝ)) 0/3))
  apply hmul.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  simp only [nominalLog] at hs ⊢
  linarith

theorem actual_error_exceptional_uniform_cap (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex I J=> P.val) A})
    (K X Z j sigma delta reserve Mdecl : ℝ) (hZ : 1< Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hK:0< K)(hX:0< X)
    (hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤ Mdecl) :
    ((X/(I.absNorm:ℝ))*localErrorCost p0 (k-1)*(X/(I.absNorm:ℝ)/(normValue p0)^k)^((1:ℝ)/3)*(errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)^((5:ℝ)/6)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max (Mdecl/4-Real.logb Z (I.absNorm:ℝ)-errorRemoval p0 Z k) 0/3)≤
      Z^(Real.logb Z X-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+3*sigma/2+5*(delta+reserve)/6):=by
  have hz:0< Z:=zero_lt_one.trans hZ
  have hf:=fixed_presentation_log_nonneg Z hZ
  have hr : 0 ≤ max (Mdecl/4-Real.logb Z (I.absNorm:ℝ)-errorRemoval p0 Z k) 0 := le_max_right _ _
  have hrLower:=le_max_left (Mdecl/4-Real.logb Z (I.absNorm:ℝ)-errorRemoval p0 Z k) (0:ℝ)
  have hi : 0 ≤ Real.logb Z (I.absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  have hc:=commonPart_of_equal_support I J hI.1 hIJ
  have hd:=commonPart_of_equal_support J I hJ.1 hIJ.symm
  have hs:=actual_error_column_saving η τ fixedBadMask I J E hI hJ A
    K X Z j sigma delta reserve hZ hmod M H Sbad hbad p0 hp0 k hk
  dsimp only at hs
  simp only [hc,hd,extracted_allowance_eq I J hI.1 hJ.1 hIJ Z] at hs
  have hp:=elementPool_data _
    (fun Q hQ=>(primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).1)
    (fun Q hQ=>(primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).2) p0 hp0
  have hl : 0 ≤ Real.logb Z (normValue p0) :=
    Real.logb_nonneg hZ (normValue_ge_one p0 hp.1.ne_zero)
  have hw : 0 ≤ errorRemoval p0 Z k := by unfold errorRemoval; positivity
  have he:=actual_error_reference_le η τ I J hI hJ hIJ A K X Z j
    (Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)-j) hK hX hZ hmod p0 hp.1.ne_zero k hk
  rw [←hE] at he
  have hrad:0< errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k:=by unfold errorCommonRadius;positivity
  rw [show j+(Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)-j)=Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k) by ring,
    Real.rpow_logb hz hZ.ne' hrad] at he
  have hmul:=mul_le_mul_of_nonneg_right he
    (Real.rpow_nonneg hz.le (-2*max (Mdecl/4-Real.logb Z (I.absNorm:ℝ)-errorRemoval p0 Z k) 0/3))
  apply hmul.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  simp only [nominalLog] at hs ⊢
  linarith

end CenteredMomentEnergyFirstHighExceptionalPowers

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentEnergyFirstHighFourCoefficients
open HeckeFamily CanonicalQuadraticSieve CompletedGauss Eisenstein 
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstMixedAllowance
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual
open CenteredMomentFirstMixedExceptionalLow CenteredMomentFirstMixedDiagonal
open CenteredMomentSuccessorPaidParameters
local notation "O"=> Eisenstein.O
local notation "Ray"=> RayFourExpansion.RayCharacter

open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentEnergyFirstHighExceptionalPowers

theorem actual_main_high_cores (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mwidth Mcap:ℝ)
    (hK:0< K)(hV:0< V)(hZ:1< Z)(hs:0≤ sigma)(heps:0≤ eps)(_hM:0≤ Mdecl)
    (hcap:Mdecl≤ Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤ Mwidth)(hwidth:Mwidth≤ Mdecl)
    (hlow:Real.logb Z V≤ Mdecl)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D}):
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    ∀j:Fin 4,Z^(-sigma/3)*mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
      (allowance C D Z) Kmain (sigma/3) (Mdecl-M0) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)) j≤
      Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j) := by
  dsimp only
  have hz:0< Z:=zero_lt_one.trans hZ
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hc:=norm_pos C hC.1
  have hr:0< mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve:=by unfold mainCommonRadius;positivity
  have havg:Z^(-sigma/3)≤1:=Real.rpow_le_one_of_one_le_of_nonpos hZ.le (by linarith)
  have hA:Real.logb Z V≤ Mdecl:=by linarith
  have hAcap:Real.logb Z V≤ Mcap:=hA.trans hcap
  intro j
  fin_cases j
  · have hh:=main_paid_core (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
      (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)
      (sigma/3) (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ))
      hq hV hc hZ (allowance_nonneg _ _ _) (by linarith)
    simpa [lossVector,neg_div] using hh
  · have hh:=actual_main_exceptional_uniform_cap η τ C D
      (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) hC hD hCD E rfl
      K V Z 0 sigma delta reserve Mwidth hZ hmod hK hV hactual
    have ht:Z^(-sigma/3)*mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)) 1≤
        Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
          4*sigma/3+5*(delta+reserve)/6):=by
      convert hh using 1 <;> first | rfl | (dsimp [mainCores,reference]; ring)
    apply ht.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    linarith
  · have hh:=actual_main_diagonal η τ C D hC hD hCD E K V Z sigma delta reserve eps hK hV hZ heps hmod
    have hc0:0≤ mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)) 2:=by
      dsimp [mainCores,reference];positivity
    apply (mul_le_mul_of_nonneg_right havg hc0).trans
    rw [one_mul]
    apply hh.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    have he:=mul_le_mul_of_nonneg_left hAcap heps
    linarith
  · have hh:=actual_main_diagonal η τ C D hC hD hCD E K V Z sigma delta reserve 0 hK hV hZ (by norm_num) hmod
    simp only [Real.rpow_zero,mul_one,zero_mul,add_zero] at hh
    have ht:=mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hz.le (-saving))
    have hcore:mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)) 3≤
        Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
          2*sigma+delta+reserve)*Z^(-saving):=by
      convert ht using 1 <;> first | rfl | (dsimp [mainCores,reference]; ring)
    have ht':=mul_le_mul_of_nonneg_left hcore (Real.rpow_nonneg hz.le (-sigma/3))
    apply ht'.trans
    calc
      _≤1*(Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
          2*sigma+delta+reserve)*Z^(-saving)):=mul_le_mul_of_nonneg_right havg (by positivity)
      _≤ _:=by
        rw [one_mul,←Real.rpow_add hz]
        apply Real.rpow_le_rpow_of_exponent_le hZ.le
        dsimp [lossVector]
        linarith

theorem actual_error_high_cores (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mwidth Mcap:ℝ)
    (hK:0< K)(hV:0< V)(hZ:1< Z)(hs:0≤ sigma)(heps:0≤ eps)(_hM:0≤ Mdecl)
    (hcap:Mdecl≤ Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤ Mwidth)(hwidth:Mwidth≤ Mdecl)
    (hlow:Real.logb Z V≤ Mdecl)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D})
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))(hbad:fixedBadPrimes⊆Sbad)
    (p:O)(hp:p∈elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7):
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k;
    ∀j:Fin 4,errorCores p k (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
      (allowance C D Z) Kerror (Mdecl-M0) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k) j≤
      Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j) := by
  dsimp only
  have hz:0< Z:=zero_lt_one.trans hZ
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hc:=norm_pos C hC.1
  have hpdata:=elementPool_data _ (fun Q hQ=>(primePool_data M H Sbad hbad _ _ _ Q hQ).1)
    (fun Q hQ=>(primePool_data M H Sbad hbad _ _ _ Q hQ).2) p hp
  have hp0:p≠0:=hpdata.1.ne_zero
  have hr:0< errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k:=by unfold errorCommonRadius;positivity
  have hA:Real.logb Z V≤ Mdecl:=by linarith
  have hAcap:Real.logb Z V≤ Mcap:=hA.trans hcap
  intro j
  fin_cases j
  · have hh:=error_paid_core p hp0 k hk (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
      (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k)
      (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k)
      hq hV hc hZ (allowance_nonneg _ _ _) (by linarith)
    simpa [lossVector] using hh
  · have hh:=actual_error_exceptional_uniform_cap η τ C D
      (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) hC hD hCD E rfl
      K V Z 0 sigma delta reserve Mwidth hZ hmod M H Sbad hbad p hp k hk hK hV hactual
    have ht:errorCores p k (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k) 1≤
        Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
          3*sigma/2+5*(delta+reserve)/6):=by
      convert hh using 1 <;> first | rfl | (dsimp [errorCores,reference]; ring)
    apply ht.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    linarith
  · have hh:=actual_error_diagonal η τ C D hC hD hCD E K V Z sigma delta reserve eps hK hV hZ heps hmod p hp0 k hk
    apply hh.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    have he:=mul_le_mul_of_nonneg_left hAcap heps
    linarith
  · have hh:=actual_error_diagonal η τ C D hC hD hCD E K V Z sigma delta reserve 0 hK hV hZ (by norm_num) hmod p hp0 k hk
    simp only [Real.rpow_zero,mul_one,zero_mul,add_zero] at hh
    have ht:=mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hz.le (-saving))
    have hcore:errorCores p k (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k) 3≤
        Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
          sigma+delta+reserve)*Z^(-saving):=by
      convert ht using 1 <;> first | rfl | (dsimp [errorCores,reference]; ring)
    apply hcore.trans
    rw [←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    linarith

theorem actual_high_four_coefficients
    (M:Ideal O)[NeZero M](Hray:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))
    (hbad:fixedBadPrimes⊆Sbad)
    (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mwidth Mcap Mamp primeLoss:ℝ)
    (hK:0< K)(hV:0< V)(hZ:1< Z)(hs:0< sigma)(heps:0≤ eps)(hM:0≤ Mdecl)
    (hcap:Mdecl≤ Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤ Mwidth)(hwidth:Mwidth≤ Mdecl)
    (hlow:Real.logb Z V≤ Mdecl)(hloss:0≤ primeLoss)(hMamp:0≤ Mamp)
    (hcard:Z^(sigma/3-primeLoss)≤(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).card)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D})
    (H:Fin 4→ℝ)(hH:∀j,0≤ H j):
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z;
    let main:=mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
      (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0 (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)
      (sigma/3) (Mdecl-M0) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ));
    let error:=fun (p:elementPool P) (i:Fin 3) (_χ:Ray)=>
      errorCores p (errorIndex i+1) (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
        (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0 (Real.logb Z (C.absNorm:ℝ))
          sigma delta reserve p (errorIndex i+1)) (Mdecl-M0) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z (errorIndex i+1));
    ∀j,averagedCoefficients P ((Mamp+2*sigma)/(sigma/6)) H main error j≤
      56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ))*H j*
        Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j+primeLoss) := by
  dsimp only
  have hz:0< Z:=zero_lt_one.trans hZ
  have hne:(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).Nonempty:=by
    apply Finset.card_pos.mp
    exact_mod_cast (Real.rpow_pos_of_pos hz (sigma/3-primeLoss)).trans_le hcard
  have hmain:=actual_main_high_cores η τ C D hC hD hCD E K V Z sigma delta reserve paid eps saving
    Mdecl Mwidth Mcap hK hV hZ hs.le heps hM hcap hactual hwidth hlow hmod
  have herror:=fun (p:elementPool (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))))
      (i:Fin 3) (χ:Ray)=>
    actual_error_high_cores η τ C D hC hD hCD E K V Z sigma delta reserve paid eps saving
      Mdecl Mwidth Mcap hK hV hZ hs.le heps hM hcap hactual hwidth hlow hmod
      M Hray Sbad hbad p p.property (errorIndex i+1)
      (by fin_cases i <;> norm_num [errorIndex])
  exact averaged_coefficients_bound _ hne
    (fun Q hQ=>(primePool_data M Hray Sbad hbad _ _ _ Q hQ).1)
    (fun Q hQ=>(primePool_data M Hray Sbad hbad _ _ _ Q hQ).2)
    Z (sigma/3) primeLoss ((Mamp+2*sigma)/(sigma/6)) hZ hloss
    (div_nonneg (by linarith) (by positivity)) hcard H _ _ _ hH
    (by simpa only [neg_div] using hmain) herror

end CenteredMomentEnergyFirstHighFourCoefficients

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentEnergyFirstHighNormalizedGaussianPowers
open HeckeFamily CanonicalQuadraticSieve CompletedGauss Eisenstein 
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily CenteredMomentCompleteCommon
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstMixedAllowance
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentFirstCommonReferencePower
local notation "O"=> Eisenstein.O
local notation "Ray"=> RayFourExpansion.RayCharacter

open CenteredMomentEnergyFirstHighFourCoefficients

theorem actual_high_normalized_four_powers
    (M:Ideal O)[NeZero M](Hray:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))
    (hbad:fixedBadPrimes⊆Sbad)
    (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mwidth Mcap Mamp primeLoss:ℝ)
    (hK:0< K)(hV:0< V)(hZ:1< Z)(hs:0< sigma)(heps:0≤ eps)(hM:0≤ Mdecl)
    (hcap:Mdecl≤ Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤ Mwidth)(hwidth:Mwidth≤ Mdecl)
    (hlow:Real.logb Z V≤ Mdecl)(hloss:0≤ primeLoss)(hMamp:0≤ Mamp)
    (hcard:Z^(sigma/3-primeLoss)≤(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).card)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D})
    (upper:ℝ)(N:ℕ)(hupper:0≤ upper)
    (H:Fin 4→ℝ)(hH:∀j,0≤ H j):
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z;
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    let Kerror:=fun (p:elementPool P)(i:Fin 3)(_:Ray)=>
      errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p (errorIndex i+1);
    let alpha:=CenteredMomentSecondChildPowerBudget.powers eps;
    let amain:=fun j=> H j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
      (Mdecl-M0) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)) j;
    let aerror:=fun (p:elementPool P)(i:Fin 3)(χ:Ray)(j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z (Kerror p i χ)
        (Mdecl-M0) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z (errorIndex i+1)) j;
    (∑j:Fin 4,normalizedPower upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z
      (allowance C D Z) eps
      (sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror alpha j) N (alpha j))≤
      (C.absNorm:ℝ)^eps*∑j:Fin 4,(upper^N)^(alpha j)*
        (56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ))*H j*
          Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j+primeLoss)) := by
  dsimp only
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hc:=norm_pos C hC.1
  have hz:=zero_lt_one.trans hZ
  have hn:=actual_power_reference_identity
    (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))) ((Mamp+2*sigma)/(sigma/6))
    upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z (allowance C D Z) eps N H
    (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)
    (sigma/3) (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ))
    (fun p i χ=> errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p (errorIndex i+1))
    (fun p i χ=> Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z (errorIndex i+1)) hV hc hq hz
  have hav:=actual_high_four_coefficients M Hray Sbad hbad η τ C D hC hD hCD E
    K V Z sigma delta reserve paid eps saving Mdecl Mwidth Mcap Mamp primeLoss
    hK hV hZ hs heps hM hcap hactual hwidth hlow hloss hMamp hcard hmod H hH
  dsimp only at hn hav
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [hn j]
  have hpos:0≤(C.absNorm:ℝ)^eps*(upper^N)^(CenteredMomentSecondChildPowerBudget.powers eps j):=by positivity
  exact (mul_le_mul_of_nonneg_left (hav j) hpos).trans_eq (by ring)

end CenteredMomentEnergyFirstHighNormalizedGaussianPowers

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentEnergyFirstHighGaussianUniformPowers
open HeckeFamily CanonicalQuadraticSieve CompletedGauss Eisenstein 
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily CenteredMomentCompleteCommon
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstMixedAllowance
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentFirstCommonReferencePower
open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentSecondChildPowerBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFiniteProfileExceptional
open InversePrincipalEnergy
local notation "O"=> Eisenstein.O
local notation "Ray"=> RayFourExpansion.RayCharacter

lemma finite_power_budget (upper nc Z eps Bcommon deficit primeLoss G F seed:ℝ)
    (N:ℕ)(hupper:1≤ upper)(hnc:0≤ nc)(hZ:1< Z)(heps:0≤ eps)(heps1:eps≤1)
    (hncap:nc≤ Z^Bcommon)(hG:0≤ G)(_hF:0≤ F)(_hseed:0< seed)
    (H srcLoss actualLoss:Fin 4→ℝ)(hH:∀j,0≤ H j)
    (hbound:∀j,H j≤ F*Z^(srcLoss j)/seed):
    nc^eps*(∑j:Fin 4,(upper^N)^(powers eps j)*
      (G*H j*Z^(deficit+actualLoss j+primeLoss)))≤
      (upper^N*G*F/seed)*Z^(deficit+eps*Bcommon+primeLoss)*
        ∑j:Fin 4,Z^(srcLoss j+actualLoss j):=by
  have hz:0< Z:=zero_lt_one.trans hZ
  have hncPow:nc^eps≤ Z^(eps*Bcommon):=by
    have hh:=Real.rpow_le_rpow hnc hncap heps
    simpa only [←Real.rpow_mul hz.le,mul_comm Bcommon eps] using hh
  have hu:1≤ upper^N:=one_le_pow₀ hupper
  have hup (j:Fin 4):(upper^N)^(powers eps j)≤ upper^N:=by
    have hp:powers eps j≤1:=by fin_cases j <;> simp [powers] <;> linarith
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hu hp
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hj0:=hH j
  have hu0:0≤ upper:=zero_le_one.trans hupper
  calc
    _≤ Z^(eps*Bcommon)*(upper^N*(G*(F*Z^(srcLoss j)/seed)*Z^(deficit+actualLoss j+primeLoss))):=by
      apply mul_le_mul hncPow _ (by positivity) (by positivity)
      apply mul_le_mul (hup j) _ (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      exact mul_le_mul_of_nonneg_left (hbound j) hG
    _=(upper^N*G*F/seed)*Z^(deficit+eps*Bcommon+primeLoss)*Z^(srcLoss j+actualLoss j):=by
      calc
        _=(upper^N*G*F/seed)*(Z^(eps*Bcommon)*Z^(srcLoss j)*Z^(deficit+actualLoss j+primeLoss)):=by ring
        _=_:=by
          rw [←Real.rpow_add hz, ←Real.rpow_add hz]
          rw [show eps*Bcommon + srcLoss j + (deficit+actualLoss j+primeLoss) =
            (deficit+eps*Bcommon+primeLoss)+(srcLoss j+actualLoss j) by ring,
            Real.rpow_add hz]
          ring

theorem actual_high_uniform_four_powers {a b:ℝ}
    (N:ℕ)(upper b1 b2 Amax loFloor:ℝ)
    (Cm Ce Cd Ct Cc cost epsilon deltaSource thetaSource Bcap:ℝ)
    (Jprofile Jchild degree:ℕ)(Sp Tchild Sf:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (hu:1≤ upper)(hb1:0≤ b1)(hb2:0≤ b2)(hAmax:0≤ Amax)(hlo:0< loFloor)
    (hCm:0≤ Cm)(hCe:0≤ Ce)(hCd:0≤ Cd)(hCt:0≤ Ct)(hCc:0≤ Cc)(hcost:0≤ cost)
    (sigma delta reserve paid saving Mcap Mamp primeLoss Bcommon:ℝ)
    (hs:0< sigma)(heps:0≤ epsilon)(heps1:epsilon≤1)(hloss:0≤ primeLoss)(hMamp:0≤ Mamp):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,∀Q:Ideal O,∀Kfix:ℝ,0≤ Kfix→∃Cbound:ℝ,0< Cbound ∧
    ∀p:Profiles a b,∀Z t height A seed C0 C1:ℝ,
      1< Z→0≤ height→0≤ A→A≤ Amax→1≤ seed→0≤ C0→0≤ C1→
    ∀(M:Ideal O)[NeZero M](Hray:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O)),
    fixedBadPrimes⊆Sbad→
    ∀(η τ:Character)(C D:Ideal O)(_hC:Supported C)(_hD:Supported D),
    primeSupport C=primeSupport D→∀E:Finset (CommonIndex C D),
    ∀K V Mdecl Mwidth:ℝ,0< K→0< V→0≤ Mdecl→Mdecl≤ Mcap→
    Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤ Mwidth→Mwidth≤ Mdecl→
    Real.logb Z V≤ Mdecl→
    Z^(sigma/3-primeLoss)≤(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).card→
    τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D}→
    (C.absNorm:ℝ)≤ Z^Bcommon→
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z;
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    let Kerror:=fun (q:elementPool P)(i:Fin 3)(_:Ray)=>
      errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve q (errorIndex i+1);
    let alpha:=powers epsilon;
    let Ebase:=Cc*(C0+C1)*diagonalControl W*(p.control Tchild)^2*(1+height)^degree;
    let H:=CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed
      (fixedFactors Cm Ce Cd Ct Z epsilon deltaSource thetaSource Bcap cost Ebase t loFloor seed Jchild Sf W);
    let amain:=fun j=> H j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
      (Mdecl-M0) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)) j;
    let aerror:=fun (q:elementPool P)(i:Fin 3)(χ:Ray)(j:Fin 4)=>
      H j*errorPowers q (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z (Kerror q i χ)
        (Mdecl-M0) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval q Z (errorIndex i+1)) j;
    (∑j:Fin 4,normalizedPower upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z
      (allowance C D Z) epsilon
      (sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror alpha j) N (alpha j))≤
      (Cbound*(C0+C1+1)*(p.control U)^2*(1+|t|+height)^J/seed)*
        Z^(Mdecl-M0+epsilon*Bcommon+primeLoss)*
        ∑j:Fin 4,Z^(losses epsilon deltaSource thetaSource Bcap j+
          lossVector sigma delta reserve paid epsilon Mcap saving j):=by
  obtain ⟨U,J,hweights⟩:=actual_weights N upper b1 b2 Amax loFloor
    Cm Ce Cd Ct Cc cost epsilon deltaSource thetaSource Bcap Jprofile Jchild degree Sp Tchild Sf W
    (zero_le_one.trans hu) hb1 hb2 hAmax hlo hCm hCe hCd hCt hCc hcost
  refine ⟨U,J,?_⟩
  intro Q Kfix hKfix
  obtain ⟨Cweights,hCweights,hw⟩:=hweights Q Kfix hKfix
  let G:=56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ))
  have hG:0< G:=by dsimp [G];positivity
  refine ⟨upper^N*G*Cweights,by positivity,?_⟩
  intro p Z t height A seed C0 C1 hZ hheight hA hAA hseed hC0 hC1
    M _ Hray Sbad hbad η τ C D hC hD hCD E K V Mdecl Mwidth hK hV hM hcap hactual hwidth hlow hcard hmod hncap
  dsimp only
  let Ebase:=Cc*(C0+C1)*diagonalControl W*(p.control Tchild)^2*(1+height)^degree
  let H:=CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed
    (fixedFactors Cm Ce Cd Ct Z epsilon deltaSource thetaSource Bcap cost Ebase t loFloor seed Jchild Sf W)
  have hEbase:0≤ Ebase:=by
    have hd:=diagonalControl_nonneg W
    dsimp [Ebase]
    positivity
  have hH:∀j,0≤ H j:=coefficients_nonneg N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed _
    (zero_le_one.trans hu) hb1 hb2 hKfix (zero_le_one.trans hseed)
    (fixedFactors_nonneg Cm Ce Cd Ct Z epsilon deltaSource thetaSource Bcap cost Ebase t loFloor seed Jchild Sf W
      hCm hCe hCd hCt (zero_le_one.trans hZ.le) hcost hEbase hlo.le (zero_le_one.trans hseed))
  have ha:=CenteredMomentEnergyFirstHighNormalizedGaussianPowers.actual_high_normalized_four_powers
    M Hray Sbad hbad η τ C D hC hD hCD E
    K V Z sigma delta reserve paid epsilon saving Mdecl Mwidth Mcap Mamp primeLoss
    hK hV hZ hs heps hM hcap hactual hwidth hlow hloss hMamp hcard hmod upper N (zero_le_one.trans hu)
    H hH
  dsimp only at ha
  apply ha.trans
  have hb:=finite_power_budget upper (C.absNorm:ℝ) Z epsilon Bcommon
    (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) primeLoss G
    (Cweights*(C0+C1+1)*(p.control U)^2*(1+|t|+height)^J) seed N hu (Nat.cast_nonneg _)
    hZ heps heps1 hncap hG.le (by positivity) (zero_lt_one.trans_le hseed) H
    (losses epsilon deltaSource thetaSource Bcap)
    (lossVector sigma delta reserve paid epsilon Mcap saving) hH
    (hw p Z t height A seed C0 C1 (zero_lt_one.trans hZ) hheight hA hAA hseed hC0 hC1)
  convert hb using 1 <;> first | rfl | (dsimp only [G]; ring)

theorem actual_high_homogeneous_four_powers
    (M:Ideal O)[NeZero M](Hray:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))
    (hbad:fixedBadPrimes⊆Sbad)
    (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mwidth Mcap Mamp primeLoss:ℝ)
    (hK:0< K)(hV:0< V)(hZ:1< Z)(hs:0< sigma)(heps:0≤ eps)(hM:0≤ Mdecl)
    (hcap:Mdecl≤ Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤ Mwidth)(hwidth:Mwidth≤ Mdecl)
    (hlow:Real.logb Z V≤ Mdecl)(hloss:0≤ primeLoss)(hMamp:0≤ Mamp)
    (hcard:Z^(sigma/3-primeLoss)≤(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).card)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D})
    (upper:ℝ)(N:ℕ)(hupper:1≤ upper)
    (H:Fin 4→ℝ)(hH:∀j,0≤ H j)
    (F seed Bcommon:ℝ)(srcLoss:Fin 4→ℝ)(hF:0≤ F)(hseed:0< seed)(heps1:eps≤1)
    (hncap:(C.absNorm:ℝ)≤ Z^Bcommon)
    (hbound:∀j,H j≤ F*Z^(srcLoss j)/seed):
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z;
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    let Kerror:=fun (p:elementPool P)(i:Fin 3)(_:Ray)=>
      errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p (errorIndex i+1);
    let alpha:=CenteredMomentSecondChildPowerBudget.powers eps;
    let amain:=fun j=> H j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
      (Mdecl-M0) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)) j;
    let aerror:=fun (p:elementPool P)(i:Fin 3)(χ:Ray)(j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z (Kerror p i χ)
        (Mdecl-M0) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z (errorIndex i+1)) j;
    (∑j:Fin 4,normalizedPower upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z
      (allowance C D Z) eps
      (sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror alpha j) N (alpha j))≤
      (upper^N*(56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ)))*F/seed)*
        Z^(Mdecl-M0+eps*Bcommon+primeLoss)*
        ∑j:Fin 4,Z^(srcLoss j+lossVector sigma delta reserve paid eps Mcap saving j) := by
  have ha:=CenteredMomentEnergyFirstHighNormalizedGaussianPowers.actual_high_normalized_four_powers
    M Hray Sbad hbad η τ C D hC hD hCD E
    K V Z sigma delta reserve paid eps saving Mdecl Mwidth Mcap Mamp primeLoss
    hK hV hZ hs heps hM hcap hactual hwidth hlow hloss hMamp hcard hmod
    upper N (zero_le_one.trans hupper) H hH
  dsimp only at ha ⊢
  apply ha.trans
  exact finite_power_budget upper (C.absNorm:ℝ) Z eps Bcommon
    (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) primeLoss
    (56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ))) F seed N
    hupper (Nat.cast_nonneg _) hZ heps heps1 hncap (by positivity) hF hseed H
    srcLoss (lossVector sigma delta reserve paid eps Mcap saving) hH hbound

end CenteredMomentEnergyFirstHighGaussianUniformPowers

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentEnergyFirstNormalizedGaussianPowers
open HeckeFamily CanonicalQuadraticSieve CompletedGauss Eisenstein 
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily CenteredMomentCompleteCommon
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstMixedAllowance
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentFirstCommonReferencePower
local notation "O"=> Eisenstein.O
local notation "Ray"=> RayFourExpansion.RayCharacter

theorem actual_normalized_four_powers
    (M:Ideal O)[NeZero M](Hray:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))
    (hbad:fixedBadPrimes⊆Sbad)
    (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mcap Mamp primeLoss:ℝ)
    (hK:0< K)(hV:0< V)(hZ:1< Z)(hs:0< sigma)(heps:0≤ eps)(hM:0≤ Mdecl)
    (hcap:Mdecl≤ Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤ Mdecl)
    (hlow:Real.logb Z V≤5*Mdecl/6)(hloss:0≤ primeLoss)(hMamp:0≤ Mamp)
    (hcard:Z^(sigma/3-primeLoss)≤(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).card)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D})
    (upper:ℝ)(N:ℕ)(hupper:0≤ upper)
    (H:Fin 4→ℝ)(hH:∀j,0≤ H j)(rmain:ℝ)
    (rerror:elementPool (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3)))→Fin 3→Ray→ℝ):
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z;
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    let Kerror:=fun (p:elementPool P)(i:Fin 3)(_:Ray)=>
      errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p (errorIndex i+1);
    let alpha:=CenteredMomentSecondChildPowerBudget.powers eps;
    let amain:=fun j=> H j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
      (Mdecl-M0) paid saving rmain j;
    let aerror:=fun (p:elementPool P)(i:Fin 3)(χ:Ray)(j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z (Kerror p i χ)
        (Mdecl-M0) paid saving (rerror p i χ) j;
    (∑j:Fin 4,normalizedPower upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z
      (allowance C D Z) eps
      (sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror alpha j) N (alpha j))≤
      (C.absNorm:ℝ)^eps*∑j:Fin 4,(upper^N)^(alpha j)*
        (56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ))*H j*
          Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j+primeLoss)) := by
  dsimp only
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hc:=norm_pos C hC.1
  have hz:=zero_lt_one.trans hZ
  have hn:=actual_power_reference_identity
    (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))) ((Mamp+2*sigma)/(sigma/6))
    upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z (allowance C D Z) eps N H
    (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)
    (sigma/3) (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid saving rmain
    (fun p i χ=> errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p (errorIndex i+1))
    rerror hV hc hq hz
  have hav:=actual_low_four_coefficients M Hray Sbad hbad η τ C D hC hD hCD E
    K V Z sigma delta reserve paid eps saving Mdecl Mcap Mamp primeLoss
    hK hV hZ hs heps hM hcap hactual hlow hloss hMamp hcard hmod H hH rmain rerror
  dsimp only at hn hav
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [hn j]
  have hpos:0≤(C.absNorm:ℝ)^eps*(upper^N)^(CenteredMomentSecondChildPowerBudget.powers eps j):=by positivity
  exact (mul_le_mul_of_nonneg_left (hav j) hpos).trans_eq (by ring)

end CenteredMomentEnergyFirstNormalizedGaussianPowers

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentEnergyFirstLowHomogeneousPowers
open HeckeFamily CanonicalQuadraticSieve CompletedGauss Eisenstein 
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily CenteredMomentCompleteCommon
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstMixedAllowance
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentFirstCommonReferencePower
open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentSecondChildPowerBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFiniteProfileExceptional
open InversePrincipalEnergy
local notation "O"=> Eisenstein.O
local notation "Ray"=> RayFourExpansion.RayCharacter

open CenteredMomentEnergyFirstHighGaussianUniformPowers

theorem actual_low_homogeneous_four_powers
    (M:Ideal O)[NeZero M](Hray:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))
    (hbad:fixedBadPrimes⊆Sbad)
    (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mcap Mamp primeLoss:ℝ)
    (hK:0< K)(hV:0< V)(hZ:1< Z)(hs:0< sigma)(heps:0≤ eps)(hM:0≤ Mdecl)
    (hcap:Mdecl≤ Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤ Mdecl)
    (hlow:Real.logb Z V≤5*Mdecl/6)(hloss:0≤ primeLoss)(hMamp:0≤ Mamp)
    (hcard:Z^(sigma/3-primeLoss)≤(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).card)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D})
    (upper:ℝ)(N:ℕ)(hupper:1≤ upper)
    (H:Fin 4→ℝ)(hH:∀j,0≤ H j)
    (F seed Bcommon:ℝ)(srcLoss:Fin 4→ℝ)(hF:0≤ F)(hseed:0< seed)(heps1:eps≤1)
    (hncap:(C.absNorm:ℝ)≤ Z^Bcommon)
    (hbound:∀j,H j≤ F*Z^(srcLoss j)/seed)
    (rmain:ℝ)
    (rerror:elementPool (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3)))→Fin 3→Ray→ℝ):
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z;
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    let Kerror:=fun (p:elementPool P)(i:Fin 3)(_:Ray)=>
      errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p (errorIndex i+1);
    let alpha:=CenteredMomentSecondChildPowerBudget.powers eps;
    let amain:=fun j=> H j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
      (Mdecl-M0) paid saving rmain j;
    let aerror:=fun (p:elementPool P)(i:Fin 3)(χ:Ray)(j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z (Kerror p i χ)
        (Mdecl-M0) paid saving (rerror p i χ) j;
    (∑j:Fin 4,normalizedPower upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z
      (allowance C D Z) eps
      (sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror alpha j) N (alpha j))≤
      (upper^N*(56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ)))*F/seed)*
        Z^(Mdecl-M0+eps*Bcommon+primeLoss)*
        ∑j:Fin 4,Z^(srcLoss j+lossVector sigma delta reserve paid eps Mcap saving j) := by
  have ha:=CenteredMomentEnergyFirstNormalizedGaussianPowers.actual_normalized_four_powers
    M Hray Sbad hbad η τ C D hC hD hCD E
    K V Z sigma delta reserve paid eps saving Mdecl Mcap Mamp primeLoss
    hK hV hZ hs heps hM hcap hactual hlow hloss hMamp hcard hmod
    upper N (zero_le_one.trans hupper) H hH rmain rerror
  dsimp only at ha ⊢
  apply ha.trans
  exact finite_power_budget upper (C.absNorm:ℝ) Z eps Bcommon
    (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) primeLoss
    (56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ))) F seed N
    hupper (Nat.cast_nonneg _) hZ heps heps1 hncap (by positivity) hF hseed H
    srcLoss (lossVector sigma delta reserve paid eps Mcap saving) hH hbound

end CenteredMomentEnergyFirstLowHomogeneousPowers

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

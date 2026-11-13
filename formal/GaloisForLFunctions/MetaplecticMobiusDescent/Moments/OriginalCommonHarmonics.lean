/-
Original common harmonics adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.SecondBlockAggregates

/-!
# Original common harmonics

Coefficients and source radii of the original common harmonic; child input volumes; internal
conductors, relative characters and natural characters of fixed-ray sources; allocated ray
dictionary matches.
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
open scoped BigOperators Classical SchwartzMap ContDiff

namespace CenteredMomentSecondOriginalChildren
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss 
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSecondIdealBlockBound
local notation "O" => Eisenstein.O

open Filter
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def core (s:Input ι) (C:Ideal O) (C0 Z δ E:ℝ) : ℝ :=
  C0*Z^δ*(profileCost s*E)*(s.X₁*s.X₂*∏i,s.P i)/(Ideal.absNorm C:ℝ)

omit [DecidableEq ι] in
lemma envelope_eq_core (s:Input ι) (C L:Ideal O) (C0 Z δ E:ℝ) :
    envelope s C L C0 Z δ E=core s C C0 Z δ E/(Ideal.absNorm L:ℝ):=by
  unfold envelope core;ring

def sourceRadial (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (H:ℝ) (hH:0< H)
    (hΦ:∀z:O,0≤(Φ (normValue z/H)).re) : Radial :=
  ⟨keep,Φ,H,hH,fun z=> by simpa only [normValue_eq_embedding] using hΦ z⟩

theorem actual_block_from_original_children (lo hi:ι→ℝ) (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤ B) (hδ:0<δ) :
    ∃C0 Ce:ℝ,0< C0 ∧ 0< Ce ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀r:ℝ,0< r →
      ∀(η:Character) (τ:RayCharacter→Character) (t:ℝ) (s:Input ι),
      (∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) → ∀R0 seed:Ideal O,
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀(C D:Ideal O) (hC:Supported C) (hD:Supported D),
      seed∣C → seed∣D → (Ideal.absNorm C:ℝ)≤ Z^B → (Ideal.absNorm D:ℝ)≤ Z^B →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff η v I*idealRowHom A I*rayMonoid χ (primaryIdealGenerator I)) →
      (∀J:sectorPool D hD.1 S,(Ideal.absNorm (J:Ideal O):ℝ)≤ Z^B) →
      ∀(R:ℝ) (rows:Finset O) (ρ x:O→ℝ) (X Y:ℝ),0< X → 0< Y →
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤ Ideal.span {(72:O)} →
      lambda∣m → (2:O)∣m →
      (∀z∈rows,nonexceptional η χ₀ Q m A z) →
      ∀(Φ:𝓢(ℝ,ℂ)) (H:ℝ),∀hH:0< H,
      ∀hΦ:(∀z:O,0≤(Φ (normValue z/H)).re), (∀z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀E₁ E₂:ℝ,
      0≤ E₁ → 0≤ E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
        ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) C R0 b)
            (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) L a≤ E₁*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
        ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) D R0 b)
            (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) L a≤ E₂*(1+‖v‖)^(2*J₂)) →
      (1+r)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
              wholeKernel W (fun _=> logAnnulus) r (ρ z) (x z)
                (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
                (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y))‖≤
        C0*Z^δ*(windowBudget J₁ t (core s C Ce Z δ E₁)*windowBudget J₂ t (core s D Ce Z δ E₂)) := by
  obtain ⟨Ce,hCe,hsource⟩:=actual_height_envelope lo hi B δ hB hδ
  obtain ⟨C0,hC0,hkernel⟩:=CenteredMomentSecondSummedBlock.actual_block_from_divisor_envelopes W decay J₁ J₂ B δ hB hδ
  refine ⟨C0,Ce,hC0,hCe,?_⟩
  filter_upwards [hkernel] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro r hr η τ t s hlo hhi R0 seed S β C D hC hD hsC hsD hnC hnD hCD U A hτ hn
    R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2 hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  have hcore (G:Ideal O) (E:ℝ) (hE:0≤ E):0≤ core s G Ce Z δ E:=by
    unfold core
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCe.le (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _))
      (mul_nonneg (profileCost_nonneg s) hE))
      (mul_nonneg (mul_nonneg s.X₁_pos.le s.X₂_pos.le) (Finset.prod_nonneg (fun i _=>(s.P_pos i).le)))) (Nat.cast_nonneg _)
  apply hZ.2 r hr η τ t S β C D hC hD hCD U hτ hn R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor (core s C Ce Z δ E₁) (core s D Ce Z δ E₂)
    (hcore C E₁ hE₁) (hcore D E₂ hE₂)
  · intro L hL hsf χ v
    have hNL: (Ideal.absNorm L:ℝ)≤ Z^B:=
      (CenteredMomentWholeDivisorShell.divisorPool_nonzero_norm Finset.univ
        (fun J:sectorPool D hD.1 S=>(J:Ideal O))
        (fun J _=>(sectorPool_supported D hD.1 S J).1) (Z^B) (fun J _=> hn J) L hL).2
    have hh:=hsource s hlo hhi (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) C hC R0 seed L hsC hsf
      E₁ Z hE₁ hZ.1 hnC hNL J₁ (τ χ) v (hleft L hL hsf χ v)
    simpa only [envelope_eq_core,sourceRadial,S,β,A] using hh
  · intro L hL hsf χ v
    have hNL: (Ideal.absNorm L:ℝ)≤ Z^B:=
      (CenteredMomentWholeDivisorShell.divisorPool_nonzero_norm Finset.univ
        (fun J:sectorPool D hD.1 S=>(J:Ideal O))
        (fun J _=>(sectorPool_supported D hD.1 S J).1) (Z^B) (fun J _=> hn J) L hL).2
    have hh:=hsource s hlo hhi (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) D hD R0 seed L hsD hsf
      E₂ Z hE₂ hZ.1 hnD hNL J₂ (τ χ) v (hright L hL hsf χ v)
    simpa only [envelope_eq_core,sourceRadial,S,β,A] using hh

end CenteredMomentSecondOriginalChildren

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace CenteredMomentAllocatedNaturalRadial
open HeckeFamily HeckeDyadic  MeasureTheory
open CenteredMomentAllocatedNaturalSource CenteredMomentCommonMaskRadialEnergy
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentRetainedProfile CenteredMomentLattice
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentOriginalRadialComparison CenteredMomentRadialPolynomialEnergy
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope CenteredMomentEligibleEnergy
open CenteredMomentCommonAllocationSum CenteredMomentRadialEligibleEnergy
local notation "O" => Eisenstein.O

lemma profile_support (V : Plain) (U : ℝ) (hU : 0< U) (t : ℝ) :
    Function.support (V.profile U hU t : ℝ→ℂ)⊆Set.Icc (V.a/max 1 V.b) (max 1 V.b) := by
  by_cases h : 1≤ U*V.b
  · rw [V.profile_retained U hU t h]
    exact (retainedProfile_support V.W V.a V.b V.a_pos V.support V.smooth U hU h t).trans
      (fun _ hx=>⟨hx.1,hx.2.trans (le_max_right _ _)⟩)
  · rw [V.profile_zero U hU t (lt_of_not_ge h)]
    simp

def naturalCharacter (η : Character) (z : O) : Character :=
  if h : z≠0 then (naturalRow η z h).character else η

lemma naturalCharacter_eq (η : Character) (z : O) (hz : z≠0) :
    naturalCharacter η z=(naturalRow η z hz).character := by simp [naturalCharacter,hz]

variable {α : Type*} [Fintype α] [DecidableEq α]

def Shared (F : Finset α) (b M : α→ℝ) (C ε : ℝ) : Prop :=
  ∀(R : Finset (Ideal O))(hR : ∀I∈R,Prime I)
      (χ : O→Character)(W₁ W₂ : 𝓢(ℝ,ℂ))(X₁ X₂ a₁ b₁ a₂ b₂ : ℝ)
      (pool : α→Finset (Ideal O))(β : α→Ideal O→ℂ)(P : α→ℝ)
      (keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(K E : ℝ),
      0< X₁ → 0< X₂ → 0≤ b₁ → 0≤ b₂ →
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₁ b₁ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₂ b₂ →
      (∀j∈F,∀I∈pool j,Prime I) → (∀j∈F,0< P j) →
      (∀j∈F,∀I∈pool j,‖β j I‖≤ M j) →
      (∀j∈F,∀I∈pool j,β j I≠0 → (I.absNorm:ℝ)≤ b j*P j) →
      0< K → (∀z,0≤(Φ (‖ringComplex z‖^2/K)).re) → 0≤ E →
      (∀D₁∈R.powerset,∀D₂∈R.powerset,∀J∈F.powerset,
        radialEnergy (fun z=> polynomial (χ z) false W₁
          (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
          polynomial (χ z) false W₂ (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
          ∏j∈F\J,naturalSlot (χ z) (pool j) (β j) (P j)) keep Φ K≤ E) →
      radialEnergy (fun z=> polynomial ((χ z).excludePrimes R hR) false W₁ X₁ 0 0 *
        polynomial ((χ z).excludePrimes R hR) false W₂ X₂ 0 0 *
        ∏j∈F,naturalSlot ((χ z).excludePrimes R hR) (pool j) (β j) (P j)) keep Φ K≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε*E

theorem uniform_shared (b M : α→ℝ) (hM : ∀i,0≤ M i) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀T : Finset α,∀F : Finset T,
      Shared F (fun i=> b i) (fun i=> M i) C ε := by
  have he (T : Finset α) (F : Finset T) : ∃C : ℝ,0< C ∧ Shared F (fun i=> b i) (fun i=> M i) C ε :=
    actual_radial_shared_energy F (fun i=> b i) (fun i=> M i) (fun i _=> hM i) ε hε
  choose C hC hb using he
  let B : ℝ:=1+∑T : Finset α,∑F : Finset T,C T F
  have hp (T : Finset α) : 0≤∑F : Finset T,C T F:=Finset.sum_nonneg (fun F _=>(hC T F).le)
  refine ⟨B,by have hh : 0≤∑T : Finset α,∑F : Finset T,C T F:=Finset.sum_nonneg (fun T _=> hp T);dsimp [B];linarith,?_⟩
  intro T F R hR χ W₁ W₂ X₁ X₂ a₁ b₁ a₂ b₂ pool β P keep Φ K E
    hX₁ hX₂ hb₁ hb₂ hs₁ hs₂ hprime hP hβ hs hK hΦ hE hchild
  have hCB : C T F≤ B := by
    have h₁:=Finset.single_le_sum (fun G _=>(hC T G).le) (Finset.mem_univ F)
    have h₂:=Finset.single_le_sum (fun T _=> hp T) (Finset.mem_univ T)
    dsimp [B];linarith
  exact (hb T F R hR χ W₁ W₂ X₁ X₂ a₁ b₁ a₂ b₂ pool β P keep Φ K E
    hX₁ hX₂ hb₁ hb₂ hs₁ hs₂ hprime hP hβ hs hK hΦ hE hchild).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCB
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hE)

def commonChild (s : Input α) (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (V₁ V₂ : Plain) (left : Bool) (z : O) (D₁ D₂ : Finset (Ideal O))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) : ℂ :=
  let d:=commonData (withHeight s τ v) C R B
  if left then child (naturalCharacter τ z) L a V₁ V₂ d.slots d.coefficient d.P v
    d.X₁ d.X₂ d.X₁_pos d.X₂_pos D₁ D₂ J
  else child (naturalCharacter τ z) L a V₁ V₂ d.slots d.coefficient d.P v
    d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos D₁ D₂ J

lemma common_rawScale (s : Input α) (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))) :
    rawScale L a (commonData (withHeight s τ v) C R B).X₁ 0=
      s.X₁/(Ideal.absNorm (B.val (Sum.inr 0)*CenteredMomentDivisorRectangle.selectedPlain L a 0):ℝ) := by
  simp only [rawScale,commonData,withHeight,map_mul,Nat.cast_mul,div_div]

theorem common_allocated_normalized (s : Input α) (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (hRC : R*C≠0) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (V₁ V₂ : Plain) (hV₁ : V₁.W=s.W₁) (hV₂ : V₂.W=s.W₂) (z : O) (hz : z≠0) :
    let d:=commonData (withHeight s τ v) C R B
    allocatedPositiveRow d.η d.m d.A z d.t d.slots d.coefficient d.P L a d.W₁ d.W₂ d.X₁ d.X₂=
      (((clippedScale (rawScale L a d.X₁ 0)):ℂ)^(Complex.I*v)*
       ((clippedScale (rawScale L a d.X₂ 1)):ℂ)^(Complex.I*v))*
       (polynomial (excluded (naturalCharacter τ z) (R*C)) false
          (V₁.profile _ (rawScale_pos L a d.X₁ d.X₁_pos 0) v) (clippedScale (rawScale L a d.X₁ 0)) 0 0*
        polynomial (excluded (naturalCharacter τ z) (R*C)) false
          (V₂.profile _ (rawScale_pos L a d.X₂ d.X₂_pos 1) v) (clippedScale (rawScale L a d.X₂ 1)) 0 0*
        ∏i∈liveIndices L a,naturalSlot (excluded (naturalCharacter τ z) (R*C))
          (d.slots i) (heightCoefficient (d.coefficient i) v) (d.P i)) := by
  dsimp only
  rw [naturalCharacter_eq τ z hz]
  have hh:=allocated_normalized τ z hz (R*C) hRC L a V₁ V₂
    (commonData (withHeight s τ v) C R B).slots
    (commonData (withHeight s τ v) C R B).coefficient
    (commonData (withHeight s τ v) C R B).P
    (commonData (withHeight s τ v) C R B).P_pos v
    (commonData (withHeight s τ v) C R B).X₁ (commonData (withHeight s τ v) C R B).X₂
    (commonData (withHeight s τ v) C R B).X₁_pos (commonData (withHeight s τ v) C R B).X₂_pos
  simpa only [hV₁,hV₂,commonData,withHeight] using hh

theorem allocated_radial_bound (b M : α→ℝ) (C₀ ε : ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (hb : Shared (liveIndices D a) b M C₀ ε)
    (η : Character) (R : Ideal O) (hR : R≠0) (V₁ V₂ : Plain)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (hprime : ∀i,∀I∈pool i,Prime I) (hP : ∀i,0< P i)
    (hβ : ∀i,∀I∈pool i,‖β i I‖≤ M i)
    (hs : ∀i,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤ b i*P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0< X₁) (hX₂ : 0< X₂)
    (r : Radial) (hkeep : ∀z,r.keep z → z≠0) (E : ℝ) (hE : 0≤ E)
    (hchild : ∀D₁∈(primeSupport R).powerset,
      ∀D₂∈(primeSupport R).powerset,∀J∈(liveIndices D a).powerset,
      radialEnergy (fun z=> child (naturalCharacter η z) D a V₁ V₂ pool β P t X₁ X₂
        hX₁ hX₂ D₁ D₂ J) r.keep r.profile r.scale≤ E) :
    radialEnergy (fun z=> allocatedPositiveRow η
      (CenteredMomentSecondHeightFamily.fixedBadMask*cubicIdealGenerator R)
      1 z t pool β P D a V₁.W V₂.W X₁ X₂) r.keep r.profile r.scale≤
        C₀*(Ideal.absNorm R.radical:ℝ)^ε*E := by
  have hh:=hb (primeSupport R) (CenteredMomentNaturalRowSource.support_prime R) (naturalCharacter η)
    (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t)
    (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t)
    (clippedScale (rawScale D a X₁ 0)) (clippedScale (rawScale D a X₂ 1))
    (V₁.a/max 1 V₁.b) (max 1 V₁.b) (V₂.a/max 1 V₂.b) (max 1 V₂.b)
    pool (fun i=> heightCoefficient (β i) t) P r.keep r.profile r.scale E
    (by unfold clippedScale;positivity) (by unfold clippedScale;positivity)
    (by positivity) (by positivity) (profile_support V₁ _ _ t) (profile_support V₂ _ _ t)
    (fun i _=> hprime i) (fun i _=> hP i)
    (fun i _ I hi=> by rw [heightCoefficient_norm _ _ _ (hprime i I hi).ne_zero];exact hβ i I hi)
    (fun i _ I hi hn=> hs i I hi (left_ne_zero_of_mul hn)) r.scale_pos r.nonneg hE hchild
  rw [←primeSupport_product_radical R hR]
  convert hh using 1
  all_goals try rfl
  unfold radialEnergy
  apply tsum_congr
  intro z
  split_ifs with hz
  · dsimp only
    rw [allocated_normalized η z (hkeep z hz) R hR D a V₁ V₂ pool β P hP t X₁ X₂ hX₁ hX₂,
      naturalCharacter_eq η z (hkeep z hz)]
    have hphase (U : ℝ) : ‖((clippedScale U):ℂ)^(Complex.I*t)‖=1 :=
      positive_height_phase_norm _ _ (by unfold clippedScale;positivity)
    simp only [excluded,norm_mul,hphase,one_mul]
  · rfl

theorem natural_child_summable (η : Character) (R : Ideal O)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0< X₁) (hX₂ : 0< X₂)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : D₁⊆primeSupport R)
    (hD₂ : D₂⊆primeSupport R) (J : Finset α) (r : Radial) :
    Summable (fun z=> if r.keep z then
      ‖child (naturalCharacter η z) D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ D₁ D₂ J‖^2*
        (r.profile (‖ringComplex z‖^2/r.scale)).re else 0) := by
  have hn (S : Finset (Ideal O)) (hS : S⊆primeSupport R) :
      (0:ℝ)< Ideal.absNorm (∏I∈S,I) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr (fun I hI=>(CenteredMomentNaturalRowSource.support_prime R I (hS hI)).ne_zero)))
  obtain ⟨PB,hPB,hbound⟩:=slots_bounded (liveIndices D a\J) pool (fun i=> heightCoefficient (β i) t) P
  exact pair_radial_summable (naturalCharacter η)
    (fun z=>∏i∈liveIndices D a\J,naturalSlot (naturalCharacter η z) (pool i) (heightCoefficient (β i) t) (P i))
    (fun _=>0) (fun _=>0)
    (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t) (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t)
    (V₁.a/max 1 V₁.b) (max 1 V₁.b) (V₂.a/max 1 V₂.b) (max 1 V₂.b)
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ))
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ)) PB
    (by positivity) (by positivity) (div_pos (by unfold clippedScale;positivity) (hn D₁ hD₁))
    (div_pos (by unfold clippedScale;positivity) (hn D₂ hD₂))
    (profile_support V₁ _ _ t) (profile_support V₂ _ _ t) (fun z=> hbound (naturalCharacter η z))
    r.keep r.profile r.scale r.scale_pos

omit [DecidableEq α] in
lemma common_nonzero (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C) : C≠0 := by
  rw [←(Finset.mem_filter.mp B.property).2]
  exact Finset.prod_ne_zero_iff.mpr (fun i _=> alloc_ne s C B i)

lemma child_energy_eq_radial (s : Data α) (r : Radial) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (α⊕Fin 2))) :
    childEnergy s r D a=
      radialEnergy (fun z=> allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P
        D a s.W₁ s.W₂ s.X₁ s.X₂) r.keep r.profile r.scale+
      radialEnergy (fun z=> allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P
        D a s.W₁ s.W₂ s.Y₁ s.Y₂) r.keep r.profile r.scale := by
  have hx:=CenteredMomentPositiveSummability.allocated_positive_summable s.η s.m s.A s.t
    s.W₁ s.W₂ s.b₁ s.b₂ s.X₁ s.X₂ s.support₁ s.support₂ s.X₁_pos s.X₂_pos
    s.slots s.coefficient s.P D a r.keep r.profile r.scale r.scale_pos
  have hy:=CenteredMomentPositiveSummability.allocated_positive_summable s.η s.m s.A s.t
    s.W₁ s.W₂ s.b₁ s.b₂ s.Y₁ s.Y₂ s.support₁ s.support₂ s.Y₁_pos s.Y₂_pos
    s.slots s.coefficient s.P D a r.keep r.profile r.scale r.scale_pos
  unfold childEnergy radialEnergy
  rw [←hx.tsum_add hy]
  apply tsum_congr
  intro z
  unfold Radial.weight
  split_ifs <;> ring

def CommonBound (b M : α→ℝ) (C₀ ε : ℝ) : Prop :=
  ∀s : Input α,(∀i,s.hi i≤ b i) → (∀i,s.M i≤ M i) →
    ∀(τ : Character) (v : ℝ) (C R : Ideal O),R≠0 → ∀B : actualAllocations s.pools C,
    ∀(L : Ideal O) (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),
    ∀V₁ V₂ : Plain,V₁.W=s.W₁ → V₂.W=s.W₂ → ∀r : Radial,(∀z,r.keep z → z≠0) →
    ∀E₁ E₂ : ℝ,0≤ E₁ → 0≤ E₂ →
    (∀D₁∈(primeSupport (R*C)).powerset,
     ∀D₂∈(primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      radialEnergy (fun z=> commonChild s τ v C R B L a V₁ V₂ true z D₁ D₂ J) r.keep r.profile r.scale≤ E₁) →
    (∀D₁∈(primeSupport (R*C)).powerset,
     ∀D₂∈(primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      radialEnergy (fun z=> commonChild s τ v C R B L a V₁ V₂ false z D₁ D₂ J) r.keep r.profile r.scale≤ E₂) →
    childEnergy (commonData (withHeight s τ v) C R B) r L a≤
      C₀*(Ideal.absNorm (R*C).radical:ℝ)^ε*(E₁+E₂)

theorem actual_common_radial_energy (b M : α→ℝ) (hM : ∀i,0≤ M i) (ε : ℝ) (hε : 0<ε) :
    ∃C₀ : ℝ,0< C₀ ∧ CommonBound b M C₀ ε := by
  obtain ⟨C₀,hC₀,hbound⟩:=uniform_shared b M hM ε hε
  refine ⟨C₀,hC₀,?_⟩
  intro s hhi hMs τ v C R hR B L a V₁ V₂ hV₁ hV₂ r hkeep E₁ E₂ hE₁ hE₂ hleft hright
  let d:=commonData (withHeight s τ v) C R B
  have hRC : R*C≠0:=mul_ne_zero hR (common_nonzero s C B)
  have hb:=hbound (CenteredMomentCommonProfile.liveIndices B.val) (liveIndices L a)
  have hc:= (commonSlots s C B).controls
  have hβ : ∀i,∀I∈d.slots i,‖d.coefficient i I‖≤ M i := by
    intro i I _
    exact (hc.1 i I).trans (hMs i)
  have hs : ∀i,∀I∈d.slots i,d.coefficient i I≠0 → (I.absNorm:ℝ)≤ b i*d.P i := by
    intro i I _ hn
    exact (hc.2 i I hn).trans (mul_le_mul_of_nonneg_right (hhi i) (s.P_pos i).le)
  have hl:=allocated_radial_bound (fun i : CenteredMomentCommonProfile.liveIndices B.val=> b i)
    (fun i=> M i) C₀ ε L a hb τ (R*C) hRC V₁ V₂ d.slots d.coefficient d.P
    d.prime d.P_pos hβ hs v d.X₁ d.X₂ d.X₁_pos d.X₂_pos r hkeep E₁ hE₁ hleft
  have hr:=allocated_radial_bound (fun i : CenteredMomentCommonProfile.liveIndices B.val=> b i)
    (fun i=> M i) C₀ ε L a hb τ (R*C) hRC V₁ V₂ d.slots d.coefficient d.P
    d.prime d.P_pos hβ hs v d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos r hkeep E₂ hE₂ hright
  rw [child_energy_eq_radial]
  have hh:=add_le_add hl hr
  rw [←mul_add] at hh
  simpa only [d,commonData,withHeight,hV₁,hV₂] using hh

lemma nonexceptional_nonzero (η : Character) (χ : RayFourExpansion.RayCharacter)
    (Q : Ideal O) (m A z : O)
    (hz : CenteredMomentRestrictedEnergy.nonexceptional η χ Q m A z) : z≠0 := hz.1

theorem uniform_initial_common_radial_energy (b M : α→ℝ) (hM : ∀i,0≤ M i) (ε : ℝ) (hε : 0<ε) :
    ∃C₀ : ℝ,0< C₀ ∧ ∀T : Finset α,CommonBound (fun i : T=> b i) (fun i : T=> M i) C₀ ε := by
  have he (T : Finset α) : ∃C₀ : ℝ,0< C₀ ∧ CommonBound (fun i : T=> b i) (fun i : T=> M i) C₀ ε :=
    actual_common_radial_energy (fun i : T=> b i) (fun i : T=> M i) (fun i=> hM i) ε hε
  choose C hC hb using he
  let C₀ : ℝ:=1+∑T : Finset α,C T
  have hsum : 0≤∑T : Finset α,C T:=Finset.sum_nonneg (fun T _=>(hC T).le)
  refine ⟨C₀,by dsimp [C₀];linarith,?_⟩
  intro T s hhi hMs τ v I R hR B L a V₁ V₂ hV₁ hV₂ r hkeep E₁ E₂ hE₁ hE₂ hleft hright
  have hCB : C T≤ C₀ := by
    have hh:=Finset.single_le_sum (fun T _=>(hC T).le) (Finset.mem_univ T)
    dsimp [C₀];linarith
  exact (hb T s hhi hMs τ v I R hR B L a V₁ V₂ hV₁ hV₂ r hkeep E₁ E₂ hE₁ hE₂ hleft hright).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCB
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (add_nonneg hE₁ hE₂))

lemma common_raw_same_product (s : Input α) (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))) :
    let d:=commonData (withHeight s τ v) C R B
    rawScale L a d.X₁ 0*rawScale L a d.X₂ 1=rawScale L a d.Y₁ 0*rawScale L a d.Y₂ 1 :=
  raw_same_product L a _ _ _ _ (commonData (withHeight s τ v) C R B).same_product.symm

theorem original_nonexceptional_common_radial_energy (b M : α→ℝ) (hM : ∀i,0≤ M i)
    (ε : ℝ) (hε : 0<ε) :
    ∃C₀ : ℝ,0< C₀ ∧ ∀s : Input α,(∀i,s.hi i≤ b i) → (∀i,s.M i≤ M i) →
    ∀(τ : Character) (v : ℝ) (C R : Ideal O),R≠0 → ∀B : actualAllocations s.pools C,
    ∀(L : Ideal O) (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),
    ∀V₁ V₂ : Plain,V₁.W=s.W₁ → V₂.W=s.W₂ → ∀(η : Character) (χ : RayFourExpansion.RayCharacter) (Q : Ideal O) (m A : O)
      (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0< H)
      (hΦ : ∀z : O,0≤(Φ (CenteredMomentSectorLocalization.normValue z/H)).re),
    let r:=CenteredMomentSecondOriginalChildren.sourceRadial
      (CenteredMomentRestrictedEnergy.nonexceptional η χ Q m A) Φ H hH hΦ

    ∀E₁ E₂ : ℝ,0≤ E₁ → 0≤ E₂ →
    (∀D₁∈(primeSupport (R*C)).powerset,
     ∀D₂∈(primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      radialEnergy (fun z=> commonChild s τ v C R B L a V₁ V₂ true z D₁ D₂ J) r.keep r.profile r.scale≤ E₁) →
    (∀D₁∈(primeSupport (R*C)).powerset,
     ∀D₂∈(primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      radialEnergy (fun z=> commonChild s τ v C R B L a V₁ V₂ false z D₁ D₂ J) r.keep r.profile r.scale≤ E₂) →
    childEnergy (commonData (withHeight s τ v) C R B) r L a≤
      C₀*(Ideal.absNorm (R*C).radical:ℝ)^ε*(E₁+E₂) := by
  obtain ⟨C₀,hC₀,hb⟩:=actual_common_radial_energy b M hM ε hε
  refine ⟨C₀,hC₀,?_⟩
  intro s hhi hMs τ v C R hR B L a V₁ V₂ hV₁ hV₂ η χ Q m A Φ H hH hΦ r
    E₁ E₂ hE₁ hE₂ hleft hright
  exact hb s hhi hMs τ v C R hR B L a V₁ V₂ hV₁ hV₂ r
    (fun _ hz=> hz.1) E₁ E₂ hE₁ hE₂ hleft hright

end CenteredMomentAllocatedNaturalRadial

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace CenteredMomentDetectorDictionary
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
local notation "O" => Eisenstein.O

lemma normalizedSlot_character (η ν : Character) (m A z : O)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (t D : ℝ) :
    normalizedSlot η m A z S (fun P=> idealCoeff ν P*β P) t D=
      normalizedSlot (η.product ν) m A z S β t D := by
  unfold normalizedSlot rowSlot
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  rw [idealCoeff_product]
  ring

lemma product_row_presentation (η χ ν : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n) :
    ∀n,elementCoeff (χ.product ν) n=rowTwist (elementHom (η.product ν)) m 1 (A*z) n := by
  intro n
  rw [elementCoeff_product,hrow]
  change (elementCoeff η n*((idealRowHom (m^6*1^4*(A*z))).toMonoidHom.comp principalIdealHom.toMonoidHom) n)*elementCoeff ν n=
    elementCoeff (η.product ν) n*((idealRowHom (m^6*1^4*(A*z))).toMonoidHom.comp principalIdealHom.toMonoidHom) n
  rw [elementCoeff_product]
  ring

theorem relative_normalizedSlot_eq_ray (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η χ ν : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (W : ℝ→ℂ) (b D σ t v : ℝ) (hD : 0< D) :
    normalizedSlot η m A z (primePool M H b D)
      (fun P=> idealCoeff ν P*HeckePrimeAnnular.annularWeight W D σ v P) t D=
      (D:ℂ)^(Complex.I*t)*HeckePrimeRay.rayPrimePolynomial M H (χ.product ν) W b D σ (t+v) := by
  rw [normalizedSlot_character]
  exact CenteredMomentPrimeSlotShift.normalizedSlot_eq_ray M H (η.product ν) (χ.product ν)
    m A z (product_row_presentation η χ ν m A z hrow) W b D σ t v hD

theorem physicalSlot_eq_relativeRay (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η χ : Character) (m A u : O)
    (hrow : ∀n,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*u) n)
    (W : ℝ→ℂ) (b D t : ℝ) (z : ℂ) (hD : 0< D) :
    normalizedSlot η m A u (primePool M H b D) (physicalSlotCoefficient η W D z) t D=
      (D:ℂ)^(Complex.I*t)*HeckePrimeRay.rayPrimePolynomial M H (χ.product η.inverse)
        (fun y=> conj (W y)) b D (1-z.re) (t-z.im) := by
  have he : normalizedSlot η m A u (primePool M H b D) (physicalSlotCoefficient η W D z) t D=
      normalizedSlot η m A u (primePool M H b D)
        (fun P=> idealCoeff η.inverse P*HeckePrimeAnnular.annularWeight (fun y=> conj (W y)) D (1-z.re) (-z.im) P) t D := by
    unfold normalizedSlot rowSlot
    congr 1
    apply Finset.sum_congr rfl
    intro P hP
    rw [physicalSlotCoefficient_annular η W D z P (Finset.mem_filter.mp hP).2.1.ne_zero hD]
  rw [he]
  exact relative_normalizedSlot_eq_ray M H η χ η.inverse m A u hrow
    (fun y=> conj (W y)) b D (1-z.re) t (-z.im) hD

end CenteredMomentDetectorDictionary

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFixedRayInducingTransport
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile
open CanonicalRowCompletion 
open CenteredMomentExceptionalPair CenteredMomentFixedRowMask
local notation "O" => Eisenstein.O

theorem modulus_generator_ne_zero (ν : Character) :
    cubicIdealGenerator ν.modulus ≠ 0 :=
  cubicIdealGenerator_ne_zero ν.modulus ν.modulus_ne_bot

theorem modulus_unit_iff (ν : Character) (n : O) :
    IsUnit (Ideal.Quotient.mk ν.modulus n) ↔
      IsCoprime n (cubicIdealGenerator ν.modulus) := by
  rw [IdealCharacter.isUnit_mk_iff_isCoprime]
  conv_lhs => rw [←span_cubicIdealGenerator ν.modulus]
  rw [Ideal.isCoprime_span_singleton_iff]

theorem elementCoeff_product_inverse_mask (η ν : Character) (n : O) :
    elementCoeff ((η.product ν).product ν.inverse) n =
      if IsCoprime n (cubicIdealGenerator ν.modulus) then elementCoeff η n else 0 := by
  rw [elementCoeff_product,elementCoeff_product,elementCoeff_inverse]
  by_cases hn : IsCoprime n (cubicIdealGenerator ν.modulus)
  · have hv : elementCoeff ν n ≠ 0 :=
      MulChar.apply_ne_zero_iff.mpr ((modulus_unit_iff ν n).mpr hn)
    simp only [hn,ite_true,mul_assoc,mul_inv_cancel₀ hv,mul_one]
  · have hv : elementCoeff ν n = 0 :=
      MulChar.map_nonunit ν.residue (fun hu=> hn ((modulus_unit_iff ν n).mp hu))
    simp only [hn,ite_false,hv,mul_zero,zero_mul]

theorem rowTwist_product (η ν : Character) (m f z n : O) :
    rowTwist (elementHom (η.product ν)) m f z n =
      rowTwist (elementHom η) m f z n * elementCoeff ν n := by
  change elementCoeff (η.product ν) n * idealRowHom (m^6*f^4*z) (Ideal.span {n}) =
    (elementCoeff η n * idealRowHom (m^6*f^4*z) (Ideal.span {n})) * elementCoeff ν n
  rw [elementCoeff_product]
  ring

theorem rowTwist_product_inverse_mask (η ν : Character) (m A z n : O)
    (hmLam : lambda ∣ m) (hm2 : (2:O) ∣ m) :
    rowTwist (elementHom ((η.product ν).product ν.inverse)) m 1 (A*z) n =
      rowTwist (elementHom η) (m*cubicIdealGenerator ν.modulus) 1 (A*z) n := by
  rw [row_mask_mul η m (cubicIdealGenerator ν.modulus) A z n hmLam hm2]
  change elementCoeff ((η.product ν).product ν.inverse) n *
    idealRowHom (m^6*1^4*(A*z)) (Ideal.span {n}) = _
  rw [elementCoeff_product_inverse_mask]
  split_ifs
  · rfl
  · exact zero_mul _

theorem fixedInducingRow_product_of (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (h : FixedInducingRow η Q m A z) :
    FixedInducingRow (η.product ν) Q m A z :=
  fixedInducingRow_of_product η (η.product ν) ν Q m A z z hν
    (fun n=> rowTwist_product η ν m 1 (A*z) n) h

theorem fixedInducingRow_product_iff (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (hm : m≠0) (hA : A≠0) (hz : z≠0)
    (hmLam : lambda ∣ m) (hm2 : (2:O) ∣ m) :
    FixedInducingRow (η.product ν) Q m A z ↔ FixedInducingRow η Q m A z := by
  constructor
  · intro h
    have hi := fixedInducingRow_product_of (η.product ν) ν.inverse Q m A z hν h
    obtain ⟨χ,ψ,hprim,hind,hQ,hrow⟩ := hi
    apply (fixedInducingRow_mul_mask_iff η Q m (cubicIdealGenerator ν.modulus) A z
      hm (modulus_generator_ne_zero ν) hA hz hmLam hm2).mp
    exact ⟨χ,ψ,hprim,hind,hQ,fun n=>(hrow n).trans
      (rowTwist_product_inverse_mask η ν m A z n hmLam hm2)⟩
  · exact fixedInducingRow_product_of η ν Q m A z hν

theorem not_fixedInducingRow_product_iff (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (hm : m≠0) (hA : A≠0) (hz : z≠0)
    (hmLam : lambda ∣ m) (hm2 : (2:O) ∣ m) :
    (¬FixedInducingRow (η.product ν) Q m A z) ↔ ¬FixedInducingRow η Q m A z :=
  not_congr (fixedInducingRow_product_iff η ν Q m A z hν hm hA hz hmLam hm2)

theorem fixedInducingRow_product_inverse_iff (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (hm : m≠0) (hA : A≠0) (hz : z≠0)
    (hmLam : lambda ∣ m) (hm2 : (2:O) ∣ m) :
    FixedInducingRow (η.product ν.inverse) Q m A z ↔ FixedInducingRow η Q m A z :=
  fixedInducingRow_product_iff η ν.inverse Q m A z hν hm hA hz hmLam hm2

theorem not_fixedInducingRow_product_inverse_iff (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (hm : m≠0) (hA : A≠0) (hz : z≠0)
    (hmLam : lambda ∣ m) (hm2 : (2:O) ∣ m) :
    (¬FixedInducingRow (η.product ν.inverse) Q m A z) ↔ ¬FixedInducingRow η Q m A z :=
  not_congr (fixedInducingRow_product_inverse_iff η ν Q m A z hν hm hA hz hmLam hm2)

end CenteredMomentFixedRayInducingTransport

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeRowClosure  CanonicalRowCompletion
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentFixedRayInducingTransport CenteredMomentFixedRowMask CenteredExceptionalProfile
local notation "O" => Eisenstein.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

def relativeCharacter (η₀ : Character) (θ : RayQuotient.Characters M H) : Character :=
  (HeckeRayQuotient.character M H hH θ).product η₀.inverse

lemma relativeCharacter_ideal (η₀ : Character) (θ : RayQuotient.Characters M H) (I : Ideal O) :
    idealCoeff (relativeCharacter M H hH η₀ θ) I=
      idealCoeff (HeckeRayQuotient.character M H hH θ) I*idealCoeff η₀.inverse I :=
  idealCoeff_product _ _ _

lemma relativeCharacter_norm (η₀ : Character) (θ : RayQuotient.Characters M H) (I : Ideal O) :
    ‖idealCoeff (relativeCharacter M H hH η₀ θ) I‖≤1 := idealCoeff_norm_le_one _ _

lemma relativeCharacter_modulus (η₀ : Character) (θ : RayQuotient.Characters M H) :
    (relativeCharacter M H hH η₀ θ).modulus.absNorm≤ M.absNorm*η₀.modulus.absNorm :=
  HeckePrimeScale.product_modulus_bound _ _

lemma relativeCharacter_fixedQ (η₀ : Character) (θ : RayQuotient.Characters M H)
    (Q : Ideal O) (hQM : Q≤ M) (hQη : Q≤η₀.modulus) :
    Q≤(relativeCharacter M H hH η₀ θ).modulus := le_inf hQM hQη

lemma excluded_product_ideal (χ ν : Character) (R : Ideal O) (hR : R≠0) (I : Ideal O) :
    idealCoeff (excluded χ R) I*idealCoeff ν I=idealCoeff (excluded (χ.product ν) R) I := by
  rw [excluded_ideal χ R hR,excluded_ideal (χ.product ν) R hR,idealCoeff_product]
  split_ifs <;> simp

lemma sector_element {η : Character} {z : O} (F : NaturalRow η z)
    (η₀ : Character) (θ : RayQuotient.Characters M H) (n : O) :
    elementCoeff (F.character.product (relativeCharacter M H hH η₀ θ)) n=
      rowTwist (elementHom (η.product (relativeCharacter M H hH η₀ θ))) fixedBadMask 1 z n := by
  simpa only [one_mul] using CenteredMomentDetectorDictionary.product_row_presentation η F.character
    (relativeCharacter M H hH η₀ θ) fixedBadMask 1 z
    (by simpa only [one_mul] using F.element) n

theorem sector_fixedQ_iff (η η₀ : Character) (θ : RayQuotient.Characters M H)
    (Q R : Ideal O) (z : O) (hQM : Q≤ M) (hQη : Q≤η₀.modulus)
    (hR : R≠0) (hz : z≠0) :
    FixedInducingRow (η.product (relativeCharacter M H hH η₀ θ)) Q
      (fixedBadMask*cubicIdealGenerator R) 1 z ↔
    FixedInducingRow η Q (fixedBadMask*cubicIdealGenerator R) 1 z :=
  fixedInducingRow_product_iff η (relativeCharacter M H hH η₀ θ) Q
    (fixedBadMask*cubicIdealGenerator R) 1 z
    (relativeCharacter_fixedQ M H hH η₀ θ Q hQM hQη)
    (mul_ne_zero fixedBadMask_ne_zero (cubicIdealGenerator_ne_zero R hR)) one_ne_zero hz
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _))

theorem sector_nonprincipal {η : Character} {z : O} (F : NaturalRow η z)
    (η₀ : Character) (θ : RayQuotient.Characters M H) (Q R : Ideal O)
    (hQM : Q≤ M) (hQη : Q≤η₀.modulus) (hR : R≠0) (hz : z≠0)
    (hex : ¬FixedInducingRow η Q (fixedBadMask*cubicIdealGenerator R) 1 z) :
    (F.character.product (relativeCharacter M H hH η₀ θ)).residue≠1 := by
  have hbase : ¬FixedInducingRow η Q fixedBadMask 1 z := by
    intro h
    exact hex ((fixedInducingRow_mul_mask_iff η Q fixedBadMask (cubicIdealGenerator R) 1 z
      fixedBadMask_ne_zero (cubicIdealGenerator_ne_zero R hR) one_ne_zero hz
      (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr h)
  exact CenteredMomentRayNonprincipal.actual_row_twist_nonprincipal η F.character
    (relativeCharacter M H hH η₀ θ) Q fixedBadMask 1 z
    (by simpa only [one_mul] using F.element)
    (relativeCharacter_fixedQ M H hH η₀ θ Q hQM hQη) hbase

end CenteredMomentNaturalFixedRaySource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentNaturalFixedRaySource
open HeckeFamily CenteredExceptionalProfile CenteredExceptionalCount
open HeckeRowClosure CanonicalRowCompletion 
open CenteredMomentNaturalRowSource UniqueFactorizationMonoid
local notation "O" => Eisenstein.O

def internalQ (Q : Ideal O) (η₀ : Character) : Ideal O := Q⊓η₀.modulus

lemma internalQ_ne_zero (Q : Ideal O) (hQ : Q≠0) (η₀ : Character) : internalQ Q η₀≠0 :=
  Ideal.inf_ne_bot_of_ne_bot hQ η₀.modulus_ne_bot

lemma internalQ_ne_top (Q : Ideal O) (hQ : Q≠⊤) (η₀ : Character) : internalQ Q η₀≠⊤ := by
  intro h
  exact hQ (top_le_iff.mp (h ▸ (inf_le_left : internalQ Q η₀≤ Q)))

lemma internalQ_coprime (Q P : Ideal O) (η₀ : Character)
    (hQP : IsCoprime Q P) (hηP : IsCoprime η₀.modulus P) : IsCoprime (internalQ Q η₀) P :=
  (hQP.mul_left hηP).of_isCoprime_of_dvd_left (Ideal.dvd_iff_le.mpr Ideal.mul_le_inf)

lemma natural_nonzero_base {η : Character} {z : O} (F : NaturalRow η z) (I : Ideal O)
    (h : idealCoeff F.character I≠0) : idealCoeff η I≠0 := by
  rw [F.ideal] at h
  exact left_ne_zero_of_mul h

lemma coefficient_forcing_coprime (η₀ : Character) (e : O) (he : elementCoeff η₀ e≠0)
    (Q P : Ideal O) (hQP : IsCoprime Q P) (hPe : P∣Ideal.span {e}) :
    IsCoprime (internalQ Q η₀) P :=
  internalQ_coprime Q P η₀ hQP (CenteredMomentChildRows.old_coefficient_prime_coprime η₀ e he P hPe)

theorem energy_split (η η₀ : Character) (Q : Ideal O) (m A : O)
    (rows : Finset O) (f : O→ℂ) :
    (∑z∈rows,‖f z‖^2)=
      (∑z∈rows.filter (fun z=>¬FixedInducingRow η (internalQ Q η₀) m A z),‖f z‖^2)+
      ∑z∈rows.filter (fun z=> FixedInducingRow η (internalQ Q η₀) m A z),‖f z‖^2 := by
  simpa only [not_not] using
    (Finset.sum_filter_add_sum_filter_not rows (fun z=>¬FixedInducingRow η (internalQ Q η₀) m A z)
      (fun z=>‖f z‖^2)).symm

theorem internal_exceptional_count (η η₀ : Character) (Q : Ideal O)
    (hQ0 : Q≠0) (hQ : Q≠⊤) (hQ72 : Q≤ Ideal.span {(72:O)})
    (m A : O) (hm : m≠0) (hA : A≠0) (hmLam : lambda∣m) (hm2 : (2:O)∣m)
    (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀P∈normalizedFactors D,lambda∉P ∧ (2:O)∉P ∧
      IsCoprime Q P ∧ IsCoprime η₀.modulus P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P%6=2)
    (Z C M F : ℝ) (hZ : 0< Z) (hC : 0≤ C)
    (hDnorm : Z^(F/2)≤(D.absNorm:ℝ))
    (hN : ∀z∈rows,((Ideal.span {z}).absNorm:ℝ)≤ C*Z^M) :
    ((rows.filter (fun z=> FixedInducingRow η (internalQ Q η₀) m A z)).card:ℝ)≤
      768*(6:ℝ)^(normalizedFactors (internalQ Q η₀)).toFinset.card*C ^ (1/6:ℝ)*Z^((M-2*F)/6) := by
  apply fixed_support_exceptional_count η (internalQ Q η₀) (internalQ_ne_zero Q hQ0 η₀)
    (internalQ_ne_top Q hQ η₀) (inf_le_left.trans hQ72) m A hm hA hmLam hm2
    (rows.filter (fun z=> FixedInducingRow η (internalQ Q η₀) m A z))
    (fun z hz=> hrows z (Finset.mem_filter.mp hz).1)
    (fun z hz=>(Finset.mem_filter.mp hz).2) D hD ?_ Z C M F hZ hC hDnorm
    (fun z hz=> hN z (Finset.mem_filter.mp hz).1)
  intro P hP
  obtain ⟨hLam,h2,hQP,hη₀,hη,hv⟩:=hgood P hP
  exact ⟨hLam,h2,internalQ_coprime Q P η₀ hQP hη₀,hη,hv⟩

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem internal_sector_nonprincipal {η : Character} {z : O} (F : NaturalRow η z)
    (η₀ : Character) (θ : RayQuotient.Characters M H) (Q R : Ideal O)
    (hQM : Q≤ M) (hR : R≠0) (hz : z≠0)
    (hex : ¬FixedInducingRow η (internalQ Q η₀) (CenteredMomentSecondHeightFamily.fixedBadMask*cubicIdealGenerator R) 1 z) :
    (F.character.product (relativeCharacter M H hH η₀ θ)).residue≠1 :=
  sector_nonprincipal M H hH F η₀ θ (internalQ Q η₀) R
    (inf_le_left.trans hQM) inf_le_right hR hz hex

end CenteredMomentNaturalFixedRaySource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ContDiff
namespace CenteredMomentRayMaskedFloor
open HeckeFamily HeckeDyadic HeckePrimeAnnular CenteredMomentCommonMaskEnergy
local notation "O" => Eisenstein.O

 theorem slot_coefficient_bounds (W : ℝ→ℂ) (a b lo hi : ℝ) (ha : 0< a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : Continuous W) :
    ∃B : ℝ,0< B ∧ ∀(ν : Character)(P σ v t : ℝ),0< P → lo≤σ → σ≤ hi →
    ∀I : Ideal O,I≠0 →
      ‖heightCoefficient (fun I=> idealCoeff ν I*annularWeight W P σ v I) t I‖≤ B ∧
      (heightCoefficient (fun I=> idealCoeff ν I*annularWeight W P σ v I) t I≠0 →
        (I.absNorm:ℝ)≤ b*P) := by
  obtain ⟨B,hB,hprofile⟩ := fixed_profile_norm_bound W hW a b lo hi ha
  refine ⟨B,hB,?_⟩
  intro ν P σ v t hP hσlo hσhi I hI
  rw [heightCoefficient_norm _ _ _ hI]
  constructor
  · apply (show ‖idealCoeff ν I*annularWeight W P σ v I‖≤‖annularWeight W P σ v I‖ by
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one ν I)).trans
    by_cases hz : W ((I.absNorm:ℝ)/P)=0
    · simp [annularWeight,hz,hB.le]
    · have hs := hWs hz
      rw [annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le hs.1)]
      simpa only [Complex.neg_re,shift_re] using hprofile σ ⟨hσlo,hσhi⟩ _ hs
  · intro hn
    have hw : W ((I.absNorm:ℝ)/P)≠0 := by
      intro hh
      exact hn (by simp [heightCoefficient,annularWeight,hh])
    exact (div_le_iff₀ hP).mp (hWs hw).2

end CenteredMomentRayMaskedFloor

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
namespace CenteredMomentAmplificationChildInput
open CenteredMomentCommonRadialData
variable {ι : Type*} [Fintype ι]
def volume (s : Input ι) : ℝ := s.X₁*s.X₂*∏i,s.P i

theorem volume_pos (s : Input ι) : 0< volume s :=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=> s.P_pos i))


end CenteredMomentAmplificationChildInput

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentOriginalCommonHarmonic
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentSupportedZeroEnergy CenteredMomentSourceZeroEnergy CenteredMomentAddedZeroUniform
open CenteredMomentActiveSource
local notation "O" => Eisenstein.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def coefficient (s:Input ι) (R seed:Ideal O) : Ideal O→ℂ:=
  finiteColumnCoefficient (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)

def sourceRadius (s:Input ι):ℝ:=(∏i,s.hi i)*s.b₁*s.b₂*(s.X₁*s.X₂)*(∏i,s.P i)

omit [DecidableEq ι] in
 theorem original_column_mask (s:Input ι) (R seed I:Ideal O) (h:coefficient s R seed I≠0):
    seed∣I:=by
  obtain ⟨v,hv,hv0,he⟩:=finiteColumnCoefficient_witness (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) I h
  rw [←he]
  by_contra hn
  apply hv0
  simp only [profileCoefficient,hn,ite_false,mul_zero]

omit [DecidableEq ι] in
 theorem original_column_norm (s:Input ι) (R seed I:Ideal O)
    (hz₁:s.W₁ 0=0) (hz₂:s.W₂ 0=0) (h:coefficient s R seed I≠0):
    I≠0 ∧ (Ideal.absNorm I:ℝ)≤ sourceRadius s:=by
  obtain ⟨v,hv,hv0,he⟩:=finiteColumnCoefficient_witness (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) I h
  have hz (i:ι):s.W i 0=0:=by
    by_contra hn
    have hh:=(s.support i hn).1
    linarith [s.lo_pos i]
  have hh:=profileCoefficient_product_bound R s.ν s.W s.P s.hi s.W₁ s.W₂ s.b₁ s.b₂
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos
    one_ne_zero one_ne_zero rfl s.same_product hz hz₁ hz₂
    (fun i x hx=>(s.support i hx).2) (fun x hx=> s.support₁ hx) (fun x hx=> s.support₂ hx) v hv0
  rw [he] at hh
  simpa only [sourceRadius,map_one,Nat.cast_one,mul_one,div_one] using hh


end CenteredMomentOriginalCommonHarmonic

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace CenteredMomentAllocatedRayDictionary
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation
open CenteredMomentCommonMaskEnergy CenteredMomentInductionEnergy
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentHeckeTwist CenteredMomentHeckeCancellation
local notation "O" => Eisenstein.O

variable {α : Type*} [Fintype α] [DecidableEq α]

section RayData
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

structure Matches (s : Input α) (η₀ : Character)
    (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ)
    (W : ℝ → ℂ) (bslot Z : ℝ) : Prop where
  character : ∀ i I, s.ν i I = idealCoeff (relativeCharacter M H hH η₀ (θ i)) I
  profile : ∀ i y, s.W i y = W y * (y : ℂ)^(-HeckeDyadic.shift (σ i) (freq i))
  pool : ∀ i, s.slots i = primePool M H bslot (Z^(w i))
  scale : ∀ i, s.P i = Z^(w i)


end RayData
end CenteredMomentAllocatedRayDictionary

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

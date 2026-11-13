/-
Allocated clipped profiles adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.FirstAnnularInputs

/-!
# Allocated clipped profiles

Clipped scales, annulus templates, seeds and derivative choices of energy profiles; band
subtype transport; matches of the amplified ray dictionary and restored errors.
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

namespace CenteredMomentEnergyAllocatedPaid
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyPaidRemoval CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation
open CenteredMomentAllocatedRayDictionary InversePrincipalEnergy
local notation "O" => Eisenstein.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem actual_allocated_paid_bands (W:ℝ→ℂ)(aslot bslot Mcap bΦ Lslot εremove lo hi κ:ℝ)
    (ha:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤ Mcap)(hbΦ:0≤ bΦ)(hLs:0≤ Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃dc:ℕ,∃Cc:ℝ,0< Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1< Z₀ ∧ ∀Z:ℝ,Z₀≤ Z →
    ∀(a b Bmask L εchild:ℝ)(Q:Ideal O),Q≤ M →
    ∀(degree:ℕ)(S:Finset (ℕ×ℕ))(C₀ C₁:ℝ),0≤ C₀ → 0≤ C₁ →
    ZeroAt (internalQ Q η₀) a b bΦ Bmask L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) → (∀i,w i≤ Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀st:NaturalState Z Bmask bΦ,st.puncture=1 → st.fixedModulus=internalQ Q η₀ → st.width≤ Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,0< X₁ → 0< X₂ → X₁≤ Z^L → X₂≤ Z^L →
    let d:=commonData (withHeight src st.character v) C R B
    energy st.character st.mask 1 0 (p.profile 0) (p.profile 1)
      (fun i:remaining src C B D alloc J=> d.slots i.val)
      (fun i:remaining src C B D alloc J=> CenteredMomentCommonMaskEnergy.heightCoefficient (d.coefficient i.val) v)
      (fun i:remaining src C B D alloc J=> d.P i.val)
      X₁ X₂ st.radial.keep st.radial.profile st.radial.scale ≤
      Cc*(C₀+C₁)*diagonalControl st.radial.profile*(p.control S)^2*
        (1+(|v|+height))^(dc+degree)*
        Z^(st.width+εchild+εremove+
          CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
            (length Z X₁) (length Z X₂) st.width κ/6+κ*mesh) := by
  obtain ⟨dc,Cc,hCc,hbound⟩:=actual_paid_bands (α:=α) M H hH W aslot bslot Mcap bΦ Lslot
    εremove lo hi κ ha hWs hW hMcap hbΦ hLs hε hbeta hκ
  refine ⟨dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ a b Bmask L εchild Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J st hunit hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  dsimp only
  rw [common_energy hmatch st.character v C R B D alloc J st.mask 1
    (p.profile 0) (p.profile 1) X₁ X₂ st.radial.keep st.radial.profile st.radial.scale]
  have he:=hbound Z hZ a b Bmask L εchild Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    (originalImage src C B D alloc J) w σ (fun i=> v+freq i) 0 (|v|+height) mesh
    hmesh hw hwm hwL hσlo hσhi (add_nonneg (abs_nonneg _) hheight)
    (fun i=>(abs_add_le _ _).trans (add_le_add le_rfl (hfreq i)))
    st hunit hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  simpa only [abs_zero,add_zero] using he

end CenteredMomentEnergyAllocatedPaid

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace CenteredMomentEnergyAllocatedClipped
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary InversePrincipalEnergy
local notation "O"=> Eisenstein.O
variable {α:Type*}[Fintype α][DecidableEq α]

def pair (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    {a b:ℝ}(ha:0< a)(p:Profiles a b)(v X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂):
    Profiles (a/max 1 b) b :=
  retainedPair a b ha p ![rawScale D alloc X₁ 0,rawScale D alloc X₂ 1]
    (by intro i;fin_cases i;exact rawScale_pos D alloc X₁ hX₁ 0;exact rawScale_pos D alloc X₂ hX₂ 1) v

def scale (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (X:ℝ)(j:Fin 2)(F:Finset (Ideal O)):ℝ:=
  clippedScale (rawScale D alloc X j)/((∏I∈F,I).absNorm:ℝ)

lemma scale_pos (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (X:ℝ)(j:Fin 2)(F:Finset (Ideal O))(hF:∀I∈F,I≠0):0< scale D alloc X j F:=by
  have hn:0<((∏I∈F,I).absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.prod_ne_zero_iff.mpr hF))
  exact div_pos (by unfold clippedScale;positivity) hn

lemma scale_cap (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (Z L X:ℝ)(hZ:1≤ Z)(hL:0≤ L)(hX:0< X)(hc:X≤ Z^L)
    (j:Fin 2)(F:Finset (Ideal O))(hF:∀I∈F,I≠0):scale D alloc X j F≤ Z^L:=
  (allocatedScale_le D alloc X hX j F hF).trans (max_le (Real.one_le_rpow hZ hL) hc)

lemma allocated_pair {Z Bmask bΦ a b:ℝ}(st:NaturalState Z Bmask bΦ)(hunit:st.puncture=1)
    (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (ha:0< a)(p:Profiles a b)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (v X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)(F₁ F₂:Finset (Ideal O))(J:Finset α):
    allocatedEnergy st.character st.radial D alloc
      (sourcePlain a b ha (p.profile 0) (p.support 0))
      (sourcePlain a b ha (p.profile 1) (p.support 1)) pool β P v X₁ X₂ hX₁ hX₂ F₁ F₂ J =
    energy st.character st.mask 1 0
      ((pair D alloc ha p v X₁ X₂ hX₁ hX₂).profile 0)
      ((pair D alloc ha p v X₁ X₂ hX₁ hX₂).profile 1)
      (fun i:↥(liveIndices D alloc\J)=> pool i)
      (fun i:↥(liveIndices D alloc\J)=> CenteredMomentCommonMaskEnergy.heightCoefficient (β i) v)
      (fun i:↥(liveIndices D alloc\J)=> P i)
      (scale D alloc X₁ 0 F₁) (scale D alloc X₂ 1 F₂)
      st.radial.keep st.radial.profile st.radial.scale:=by
  simp only [allocatedEnergy,pair,retainedPair,scale,NaturalState.mask,hunit,
    Matrix.cons_val_zero,Matrix.cons_val_one]

variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem actual_clipped_paid_bands (W:ℝ→ℂ)(aslot bslot Mcap bΦ Lslot εremove lo hi κ:ℝ)
    (ha:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤ Mcap)(hbΦ:0≤ bΦ)(hLs:0≤ Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃dc:ℕ,∃Cc:ℝ,0< Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1< Z₀ ∧ ∀Z:ℝ,Z₀≤ Z →
    ∀(a b Bmask L εchild:ℝ)(ha:0< a),0≤ L → ∀Q:Ideal O,Q≤ M →
    ∀(degree:ℕ)(S:Finset (ℕ×ℕ))(C₀ C₁:ℝ),0≤ C₀ → 0≤ C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b bΦ Bmask L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b bΦ Bmask L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) → (∀i,w i≤ Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀st:NaturalState Z Bmask bΦ,st.puncture=1 → st.fixedModulus=internalQ Q η₀ → st.width≤ Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0< X₁,∀hX₂:0< X₂,X₁≤ Z^L → X₂≤ Z^L →
    ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
    let d:=commonData (withHeight src st.character v) C R B
    allocatedEnergy st.character st.radial D alloc
      (sourcePlain a b ha (p.profile 0) (p.support 0))
      (sourcePlain a b ha (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J ≤
      Cc*(C₀+C₁)*diagonalControl st.radial.profile*
        ((pair D alloc ha p v X₁ X₂ hX₁ hX₂).control S)^2*
        (1+(|v|+height))^(dc+degree)*
        Z^(st.width+εchild+εremove+
          CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
            (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) st.width κ/6+κ*mesh) := by
  obtain ⟨dc,Cc,hCc,hbound⟩:=actual_allocated_paid_bands (α:=α) M H hH W aslot bslot Mcap bΦ Lslot
    εremove lo hi κ ha hWs hW hMcap hbΦ hLs hε hbeta hκ
  refine ⟨dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ a b Bmask L εchild ha hL Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J st hunit hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  dsimp only
  rw [allocated_pair st hunit]
  exact hbound Z hZ (a/max 1 b) b Bmask L εchild Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J st hunit hQ hs (pair D alloc ha p v X₁ X₂ hX₁ hX₂)
    (scale D alloc X₁ 0 F₁) (scale D alloc X₂ 1 F₂)
    (scale_pos D alloc X₁ 0 F₁ hF₁) (scale_pos D alloc X₂ 1 F₂ hF₂)
    (scale_cap D alloc Z L X₁ st.base_ge_one hL hX₁ hc₁ 0 F₁ hF₁)
    (scale_cap D alloc Z L X₂ st.base_ge_one hL hX₂ hc₂ 1 F₂ hF₂)

end CenteredMomentEnergyAllocatedClipped

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyAllocatedClipped
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary InversePrincipalEnergy
local notation "O"=> Eisenstein.O
variable {α:Type*}[Fintype α][DecidableEq α]

variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem actual_clipped_homogeneous_bands (W:ℝ→ℂ)(aslot bslot Mcap bΦ Lslot εremove lo hi κ:ℝ)
    (a b:ℝ)(haPlain:0< a)(L:ℝ)(hL:0≤ L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤ Mcap)(hbΦ:0≤ bΦ)(hLs:0≤ Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0< Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1< Z₀ ∧ ∀Z:ℝ,Z₀≤ Z →
    ∀(Bmask εchild:ℝ)(Q:Ideal O),Q≤ M →
    ∀C₀ C₁:ℝ,0≤ C₀ → 0≤ C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b bΦ Bmask L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b bΦ Bmask L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) → (∀i,w i≤ Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀st:NaturalState Z Bmask bΦ,st.puncture=1 → st.fixedModulus=internalQ Q η₀ → st.width≤ Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0< X₁,∀hX₂:0< X₂,X₁≤ Z^L → X₂≤ Z^L →
    ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
    let d:=commonData (withHeight src st.character v) C R B
    allocatedEnergy st.character st.radial D alloc
      (sourcePlain a b haPlain (p.profile 0) (p.support 0))
      (sourcePlain a b haPlain (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J ≤
      Cc*(C₀+C₁)*diagonalControl st.radial.profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        Z^(st.width+εchild+εremove+
          CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
            (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) st.width κ/6+κ*mesh) := by
  obtain ⟨dc,Cc,hCc,hbound⟩:=actual_clipped_paid_bands (α:=α) M H hH W aslot bslot Mcap bΦ Lslot
    εremove lo hi κ ha hWs hW hMcap hbΦ hLs hε hbeta hκ
  obtain ⟨n,T,Cp,hCp,hprofile⟩:=retained_pair_control a b haPlain S
  refine ⟨n,T,dc,Cc*Cp^2,mul_pos hCc (sq_pos_of_pos hCp),?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ Bmask εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J st hunit hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  have he:=hbound Z hZ a b Bmask L εchild haPlain hL Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J st hunit hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  dsimp only at he ⊢
  let U:Fin 2→ℝ:=![rawScale D alloc X₁ 0,rawScale D alloc X₂ 1]
  have hU:∀i,0< U i:=by
    intro i;fin_cases i
    · exact rawScale_pos D alloc X₁ hX₁ 0
    · exact rawScale_pos D alloc X₂ hX₂ 1
  have hp:(pair D alloc haPlain p v X₁ X₂ hX₁ hX₂).control S≤
      Cp*p.control T*(1+|v|+height)^(2*n):=by
    have h:=hprofile p U hU v
    have hpw:(1+‖v‖)^(2*n)≤(1+|v|+height)^(2*n):=
      pow_le_pow_left₀ (by positivity) (by simp only [Real.norm_eq_abs];linarith) _
    exact h.trans (mul_le_mul_of_nonneg_left hpw (mul_nonneg hCp.le (p.control_nonneg T)))
  apply he.trans
  calc
    _≤ Cc*(C₀+C₁)*diagonalControl st.radial.profile*
        (Cp*p.control T*(1+|v|+height)^(2*n))^2*
        (1+(|v|+height))^(dc+degree)*
        Z^(st.width+εchild+εremove+
          CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
            (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) st.width κ/6+κ*mesh):=by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans st.base_ge_one) _)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Profiles.control_nonneg _ _) hp 2)
        (mul_nonneg (mul_nonneg hCc.le (add_nonneg hC₀ hC₁)) (diagonalControl_nonneg _))
    _=_:=by
      have hpow:(1+|v|+height)^(4*n)=((1+|v|+height)^(2*n))^2:=by
        rw [←pow_mul]
        congr 1
        omega
      simp only [←add_assoc,mul_pow,pow_add,hpow]
      ring

end CenteredMomentEnergyAllocatedHomogeneous

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace CenteredMomentEnergyCanonicalChildBound
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
local notation "O"=> Eisenstein.O
variable {α:Type*}[Fintype α][DecidableEq α]

variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem actual_canonical_child_bands (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b:ℝ)(haPlain:0< a)(L:ℝ)(hL:0≤ L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤ Mcap)(hLs:0≤ Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0< Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1< Z₀ ∧ ∀Z:ℝ,Z₀≤ Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤ M →
    ∀C₀ C₁:ℝ,0≤ C₀ → 0≤ C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) → (∀i,w i≤ Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤ CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤ Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0< X₁,∀hX₂:0< X₂,X₁≤ Z^L → X₂≤ Z^L →
    ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
    let d:=commonData (withHeight src τ v) C R B
    allocatedEnergy τ (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad) D alloc
      (sourcePlain a b haPlain (p.profile 0) (p.support 0))
      (sourcePlain a b haPlain (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J ≤
      Cc*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        ((τ.modulus.absNorm:ℝ)*CenteredMomentSectorLocalization.dyadicScale (dyad 1))*
        Z^(εchild+εremove+
          CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
            (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) (Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)) κ/6+κ*mesh) := by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=actual_clipped_homogeneous_bands (α:=α) M H hH W aslot bslot
    Mcap 2 Lslot εremove lo hi κ a b haPlain L hL degree S ha hWs hW hMcap (by norm_num)
    hLs hε hbeta hκ
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  have hZ1:1< Z:=hZ₀.trans_le hZ
  let st:=canonicalState Z 0 hZ1 τ (internalQ Q η₀) 1 one_ne_zero (by simp) dyad hn
  have he:=hbound Z hZ 0 εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J st rfl rfl hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  have hpow:=canonicalState_power Z 0 hZ1 τ (internalQ Q η₀) 1 one_ne_zero (by simp) dyad hn
  change Z^st.width=(τ.modulus.absNorm:ℝ)*CenteredMomentSectorLocalization.dyadicScale (dyad 1) at hpow
  dsimp only at he ⊢
  have heq:st.width+εchild+εremove+
      CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
        (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) st.width κ/6+κ*mesh =
    st.width+(εchild+εremove+CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
      (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) st.width κ/6+κ*mesh):=by ring
  rw [heq,Real.rpow_add (zero_lt_one.trans hZ1),hpow] at he
  convert he using 1 <;> simp only [st,canonicalState,NaturalState.width] ; ring

end CenteredMomentEnergyCanonicalChildBound

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace CenteredMomentEnergyCanonicalLiveBound
open HeckeFamily 
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=> Eisenstein.O
variable {α:Type*}[Fintype α][DecidableEq α]

def LiveChild (η:Character)(r:Radial)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))(V₁ V₂:Plain)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)(F₁ F₂:Finset (Ideal O))(J:Finset α):Prop:=
  ∃z:O,r.keep z ∧ (r.profile (‖ringComplex z‖^2/r.scale)).re≠0 ∧
    child (naturalCharacter η z) D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ F₁ F₂ J≠0

theorem energy_zero_of_not_live (η:Character)(r:Radial)(hz:∀z,r.keep z→z≠0)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))(V₁ V₂:Plain)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)(hP:∀i,0< P i)
    (t X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)(F₁ F₂:Finset (Ideal O))(J:Finset α)
    (hF₁:∀I∈F₁,I≠0)(hF₂:∀I∈F₂,I≠0)
    (hn:¬LiveChild η r D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ F₁ F₂ J):
    allocatedEnergy η r D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ F₁ F₂ J=0:=by
  rw [←child_radial_eq_energy η r hz D a V₁ V₂ pool β P hP t X₁ X₂ hX₁ hX₂ F₁ F₂ J hF₁ hF₂]
  unfold radialEnergy
  apply (tsum_congr (g:=fun _ : O=>(0:ℝ)) ?_).trans (tsum_zero)
  intro z
  by_cases hk:r.keep z
  · rw [if_pos hk]
    by_cases hφ:(r.profile (‖ringComplex z‖^2/r.scale)).re=0
    · rw [hφ,mul_zero]
    · have hc:child (naturalCharacter η z) D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ F₁ F₂ J=0:=by
        by_contra hh
        exact hn ⟨z,hk,hφ,hh⟩
      simp only [hc,norm_zero,zero_pow (by decide:2≠0),zero_mul]
  · rw [if_neg hk]

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

theorem actual_live_canonical_child_bands (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b:ℝ)(haPlain:0< a)(L:ℝ)(hL:0≤ L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤ Mcap)(hLs:0≤ Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0< Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1< Z₀ ∧ ∀Z:ℝ,Z₀≤ Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤ M →
    ∀C₀ C₁:ℝ,0≤ C₀ → 0≤ C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) → (∀i,w i≤ Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤ CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤ Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0< X₁,∀hX₂:0< X₂,X₁≤ Z^L → X₂≤ Z^L →
    ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
    let d:=commonData (withHeight src τ v) C R B
    ∀Mnom cost:ℝ,
    (LiveChild τ (canonicalRadial τ (internalQ Q η₀) dyad) D alloc
      (sourcePlain a b haPlain (p.profile 0) (p.support 0))
      (sourcePlain a b haPlain (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J →
      Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)-Mnom+
        CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
          (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂))
          (Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)) κ/6≤ cost) →
    allocatedEnergy τ (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad) D alloc
      (sourcePlain a b haPlain (p.profile 0) (p.support 0))
      (sourcePlain a b haPlain (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J ≤
      Cc*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        Z^(Mnom+εchild+εremove+cost+κ*mesh) := by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=actual_canonical_child_bands (α:=α) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b haPlain L hL degree S ha hWs hW hMcap hLs hε hbeta hκ
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  dsimp only
  intro Mnom cost hcost
  have hz:1< Z:=hZ₀.trans_le hZ
  have hz0:0< Z:=zero_lt_one.trans hz
  let d:=commonData (withHeight src τ v) C R B
  let rad:=canonicalRadial τ (internalQ Q η₀) dyad
  let V₁:=sourcePlain a b haPlain (p.profile 0) (p.support 0)
  let V₂:=sourcePlain a b haPlain (p.profile 1) (p.support 1)
  by_cases hne:LiveChild τ rad D alloc V₁ V₂ d.slots d.coefficient d.P
      v X₁ X₂ hX₁ hX₂ F₁ F₂ J
  · have he:=hbound Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
      src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
    dsimp only at he
    have hnorm:0<(τ.modulus.absNorm:ℝ):=by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot)
    have hpower:Z^(Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ))=
        (τ.modulus.absNorm:ℝ)*dyadicScale (dyad 1):=by
      rw [Real.rpow_add hz0,Real.rpow_logb hz0 hz.ne' (dyadicScale_pos _),
        Real.rpow_logb hz0 hz.ne' hnorm,mul_comm]
    apply he.trans
    rw [←hpower,mul_assoc,←Real.rpow_add hz0]
    apply mul_le_mul_of_nonneg_left _ (by
      have hd:0≤ diagonalControl rad.profile:=by unfold diagonalControl;positivity
      have hp:=p.control_nonneg T
      positivity)
    apply Real.rpow_le_rpow_of_exponent_le hz.le
    have hh:=hcost hne
    linarith
  · have he:=energy_zero_of_not_live τ rad (fun z hz=> hz.1) D alloc V₁ V₂
      d.slots d.coefficient d.P d.P_pos v X₁ X₂ hX₁ hX₂ F₁ F₂ J hF₁ hF₂ hne
    change allocatedEnergy τ rad D alloc V₁ V₂ d.slots d.coefficient d.P
      v X₁ X₂ hX₁ hX₂ F₁ F₂ J≤ _
    rw [he]
    have hd:0≤ diagonalControl rad.profile:=by unfold diagonalControl;positivity
    have hp:=p.control_nonneg T
    positivity

end CenteredMomentEnergyCanonicalLiveBound

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentEnergyCanonicalLiveCapacity
open HeckeFamily  CenteredMomentEnergyCanonicalLiveBound
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial CenteredMomentRetainedProfile
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyBands
open CenteredMomentEnergyDeletedChildCapacity CenteredMomentRadialEligibleEnergy
local notation "O"=> Eisenstein.O
variable {α:Type*}[Fintype α][DecidableEq α]

lemma original_deleted_excess (src:Input α)(C R:Ideal O)(B:actualAllocations src.pools C)
    (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset
      (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (J:Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (τ:Character)(v Z X₁ X₂ κ Mactual:ℝ)(w:α→ℝ)
    (hZ:1< Z)(hscale:∀i,src.P i=Z^(w i))(F₁ F₂:Finset (Ideal O)):
    deletedExcess D alloc Z X₁ X₂ κ Mactual
      (commonData (withHeight src τ v) C R B).P F₁ F₂ J =
    CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
      (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) Mactual κ:=by
  unfold deletedExcess CenteredMomentLiveCapacity.excess originalImage
  simp only [Finset.sum_map,originalEmbedding,Function.Embedding.coeFn_mk]
  congr 3
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  change Real.logb Z (src.P i.val)=w i.val
  rw [hscale,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']

theorem live_source_paid_cost (src:Input α)(C R:Ideal O)(B:actualAllocations src.pools C)
    (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset
      (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (J:Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (τ:Character)(rad:Radial)(V₁ V₂:Plain)(v Z X₁ X₂ κ A M Mnom Mactual u ell δ₁ δ₂ θ:ℝ)
    (w:α→ℝ)(h₁:0< X₁)(h₂:0< X₂)(F₁ F₂:Finset (Ideal O))
    (hZ:1< Z)(hκ:0≤κ)(hw:∀i,0≤ w i)(hscale:∀i,src.P i=Z^(w i))
    (hF₁:∀I∈F₁,I≠0)(hF₂:∀I∈F₂,I≠0)
    (hparent:A+(6*κ-1)*(∑i:CenteredMomentCommonProfile.liveIndices B.val,w i.val)≤ M)
    (hshift:Real.logb Z (X₁*X₂*∏i:CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-Mnom≤
      A-M+6*(u+ell)+δ₁)
    (hwidth:Mactual-Mnom≤δ₂)(hu:0≤ u)(hell:0≤ ell)(hδ₁:0≤δ₁)(hδ₂:0≤δ₂)(hθ:0≤θ)
    (hclip:Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ)
    (hlive:LiveChild τ rad D alloc V₁ V₂
      (commonData (withHeight src τ v) C R B).slots
      (commonData (withHeight src τ v) C R B).coefficient
      (commonData (withHeight src τ v) C R B).P v X₁ X₂ h₁ h₂ F₁ F₂ J):
    Mactual-Mnom+CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
      (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) Mactual κ/6≤
      δ₂+u+ell+δ₁/6+θ/3:=by
  obtain ⟨z,hz,hφ,hchild⟩:=hlive
  let d:=commonData (withHeight src τ v) C R B
  have hP:∀i,1≤ d.P i:=by
    intro i
    change 1≤ src.P i.val
    rw [hscale]
    exact Real.one_le_rpow hZ.le (hw i.val)
  have hp:A+(6*κ-1)*(∑i,Real.logb Z (d.P i))≤ M:=by
    simpa only [d,commonData,withHeight,hscale,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hparent
  have hb:=child_paid_width (naturalCharacter τ z) D alloc V₁ V₂ d.slots d.coefficient d.P
    v Z X₁ X₂ κ A M Mnom Mactual u ell δ₁ δ₂ θ h₁ h₂ F₁ F₂ J
    hZ hκ hP hF₁ hF₂ hchild hp hshift hwidth hu hell hδ₁ hδ₂ hθ hclip
  rw [original_deleted_excess src C R B D alloc J τ v Z X₁ X₂ κ Mactual w hZ hscale F₁ F₂] at hb
  linarith

end CenteredMomentEnergyCanonicalLiveCapacity

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace CenteredMomentEnergyCanonicalPaidSource
open HeckeFamily 
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=> Eisenstein.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
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

theorem actual_canonical_paid_source (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b:ℝ)(haPlain:0< a)(L:ℝ)(hL:0≤ L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤ Mcap)(hLs:0≤ Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0< Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1< Z₀ ∧ ∀Z:ℝ,Z₀≤ Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤ M →
    ∀C₀ C₁:ℝ,0≤ C₀ → 0≤ C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) → (∀i,w i≤ Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤ CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤ Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0< X₁,∀hX₂:0< X₂,X₁≤ Z^L → X₂≤ Z^L →
    ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
    let d:=commonData (withHeight src τ v) C R B
    ∀A Mparent Mnom u ell δ₁ δ₂ θclip:ℝ,
    0≤ u → 0≤ ell → 0≤δ₁ → 0≤δ₂ → 0≤θclip →
    A+(6*κ-1)*(∑i:CenteredMomentCommonProfile.liveIndices B.val,w i.val)≤ Mparent →
    Real.logb Z (X₁*X₂*∏i:CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-Mnom≤
      A-Mparent+6*(u+ell)+δ₁ →
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)-Mnom≤δ₂ →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    allocatedEnergy τ (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad) D alloc
      (sourcePlain a b haPlain (p.profile 0) (p.support 0))
      (sourcePlain a b haPlain (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J ≤
      Cc*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        Z^(Mnom+εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) := by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=actual_live_canonical_child_bands (α:=α) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b haPlain L hL degree S ha hWs hW hMcap hLs hε hbeta hκ
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  dsimp only
  intro A Mparent Mnom u ell δ₁ δ₂ θclip hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  apply hbound Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
    Mnom (δ₂+u+ell+δ₁/6+θclip/3)
  intro hlive
  exact live_source_paid_cost src C R B D alloc J τ (canonicalRadial τ (internalQ Q η₀) dyad)
    (sourcePlain a b haPlain (p.profile 0) (p.support 0))
    (sourcePlain a b haPlain (p.profile 1) (p.support 1))
    v Z X₁ X₂ κ A Mparent Mnom
    (Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ))
    u ell δ₁ δ₂ θclip w hX₁ hX₂ F₁ F₂ (hZ₀.trans_le hZ)
    (by linarith) hw hmatch.scale hF₁ hF₂ hparent hshift hdefect hu hell hδ₁ hδ₂ hθclip hclip hlive

end CenteredMomentEnergyCanonicalPaidSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace CenteredMomentEnergyCanonicalCommonPaid
open HeckeFamily 
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=> Eisenstein.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource
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

theorem actual_common_paid_source (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤ Mslot)(hεmask:0<εmask)(haPlain:0< a)(L:ℝ)(hL:0≤ L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤ Mcap)(hLs:0≤ Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0< Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1< Z₀ ∧ ∀Z:ℝ,Z₀≤ Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤ M →
    ∀C₀ C₁:ℝ,0≤ C₀ → 0≤ C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) → (∀i,w i≤ Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤ bslot) → (∀i,src.M i≤ Mslot) →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),R≠0 →
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤ CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤ Mcap →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    let d:=commonData (withHeight src τ v) C R B
    d.X₁≤ Z^L → d.X₂≤ Z^L → d.Y₁≤ Z^L → d.Y₂≤ Z^L →
    ∀A Mparent Mnom u ell δ₁ δ₂ θclip:ℝ,
    0≤ u → 0≤ ell → 0≤δ₁ → 0≤δ₂ → 0≤θclip →
    A+(6*κ-1)*(∑i:CenteredMomentCommonProfile.liveIndices B.val,w i.val)≤ Mparent →
    Real.logb Z (d.X₁*d.X₂*∏i:CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-Mnom≤
      A-Mparent+6*(u+ell)+δ₁ →
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)-Mnom≤δ₂ →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    childEnergy d (canonicalRadial τ (internalQ Q η₀) dyad) D alloc ≤
      Cc*(Ideal.absNorm (R*C).radical:ℝ)^εmask*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        Z^(Mnom+εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) := by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=actual_canonical_paid_source (α:=α) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b haPlain L hL degree S ha hWs hW hMcap hLs hε hbeta hκ
  obtain ⟨Cm,hCm,hcommon⟩:=actual_common_from_energy (α:=α) (fun _=> bslot) (fun _=> Mslot)
    (fun _=> hMslot) εmask hεmask
  refine ⟨n,T,dc,2*Cm*Cc,by positivity,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
  dsimp only
  intro hX₁ hX₂ hY₁ hY₂ A Mparent Mnom u ell δ₁ δ₂ θclip
    hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  let d:=commonData (withHeight src τ v) C R B
  let rad:=canonicalRadial τ (internalQ Q η₀) dyad
  let V₁:=sourcePlain a b haPlain (p.profile 0) (p.support 0)
  let V₂:=sourcePlain a b haPlain (p.profile 1) (p.support 1)
  let E:=Cc*(C₀+C₁)*diagonalControl rad.profile*(p.control T)^2*
    (1+(|v|+height))^(dc+degree+4*n)*
    Z^(Mnom+εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh)
  have hz:1< Z:=hZ₀.trans_le hZ
  have he:0≤ E:=by
    have hd:0≤ diagonalControl rad.profile:=by unfold diagonalControl;positivity
    have hz0:0< Z:=zero_lt_one.trans hz
    dsimp [E]
    positivity
  have hleft:∀X₁ X₂:ℝ,∀h₁:0< X₁,∀h₂:0< X₂,X₁≤ Z^L → X₂≤ Z^L →
      X₁*X₂=d.X₁*d.X₂ → ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
      ∀J,allocatedEnergy τ rad D alloc V₁ V₂ d.slots d.coefficient d.P
        v X₁ X₂ h₁ h₂ F₁ F₂ J≤ E:=by
    intro X₁ X₂ h₁ h₂ hc₁ hc₂ hprod F₁ F₂ hF₁ hF₂ J
    apply hbound Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
      src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ h₁ h₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
      A Mparent Mnom u ell δ₁ δ₂ θclip hu hell hδ₁ hδ₂ hθclip hparent _ hdefect hclip
    simpa only [hprod] using hshift
  have hh:=hcommon src hhi hMs τ v C R hR B D alloc V₁ V₂ hp₁ hp₂ rad
    (fun z hz=> hz.1) E E he he (by
      intro left F₁ hF₁ F₂ hF₂ J hJ
      have hf₁:∀I∈F₁,I≠0:=fun I hi=>(CenteredMomentNaturalRowSource.support_prime (R*C) I
        ((Finset.mem_powerset.mp hF₁) hi)).ne_zero
      have hf₂:∀I∈F₂,I≠0:=fun I hi=>(CenteredMomentNaturalRowSource.support_prime (R*C) I
        ((Finset.mem_powerset.mp hF₂) hi)).ne_zero
      cases left
      · exact hleft d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos hY₁ hY₂ d.same_product F₁ F₂ hf₁ hf₂ J
      · exact hleft d.X₁ d.X₂ d.X₁_pos d.X₂_pos hX₁ hX₂ rfl F₁ F₂ hf₁ hf₂ J)
  apply hh.trans_eq
  dsimp [E]
  ring

end CenteredMomentEnergyCanonicalCommonPaid

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace CenteredMomentEnergyCanonicalReferencePaid
open HeckeFamily 
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=> Eisenstein.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
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

theorem actual_reference_paid_source (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤ Mslot)(hεmask:0<εmask)(haPlain:0< a)(L:ℝ)(hL:0≤ L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤ Mcap)(hLs:0≤ Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0< Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1< Z₀ ∧ ∀Z:ℝ,Z₀≤ Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤ M →
    ∀C₀ C₁:ℝ,0≤ C₀ → 0≤ C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) → (∀i,w i≤ Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤ bslot) → (∀i,src.M i≤ Mslot) →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),R≠0 →
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤ CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤ Mcap →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    let d:=commonData (withHeight src τ v) C R B
    d.X₁≤ Z^L → d.X₂≤ Z^L → d.Y₁≤ Z^L → d.Y₂≤ Z^L →
    ∀A Mparent reference u ell δ₁ δ₂ θclip:ℝ,0< reference →
    0≤ u → 0≤ ell → 0≤δ₁ → 0≤δ₂ → 0≤θclip →
    A+(6*κ-1)*(∑i:CenteredMomentCommonProfile.liveIndices B.val,w i.val)≤ Mparent →
    Real.logb Z (d.X₁*d.X₂*∏i:CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-Real.logb Z reference≤
      A-Mparent+6*(u+ell)+δ₁+Real.logb Z (ratioPenalty dyad) →
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)-Real.logb Z reference≤δ₂ →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    childEnergy d (canonicalRadial τ (internalQ Q η₀) dyad) D alloc ≤
      Cc*(Ideal.absNorm (R*C).radical:ℝ)^εmask*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        reference*(ratioPenalty dyad)^((1:ℝ)/6)*
        Z^(εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) := by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=actual_common_paid_source (α:=α) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL degree S
    ha hWs hW hMcap hLs hε hbeta hκ
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
  dsimp only
  intro hX₁ hX₂ hY₁ hY₂ A Mparent reference u ell δ₁ δ₂ θclip href
    hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  have hz:1< Z:=hZ₀.trans_le hZ
  have hz0:0< Z:=zero_lt_one.trans hz
  have hr:1≤ ratioPenalty dyad:=le_max_left _ _
  have hr0:0< ratioPenalty dyad:=zero_lt_one.trans_le hr
  have hlog:0≤ Real.logb Z (ratioPenalty dyad):=Real.logb_nonneg hz hr
  have hh:=hbound Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ A Mparent (Real.logb Z reference) u ell
    (δ₁+Real.logb Z (ratioPenalty dyad)) δ₂ θclip hu hell (by linarith) hδ₂ hθclip
    hparent (by linarith) hdefect hclip
  have hpow:Z^(Real.logb Z reference+εchild+εremove+
      (δ₂+u+ell+(δ₁+Real.logb Z (ratioPenalty dyad))/6+θclip/3)+κ*mesh)=
      reference*(ratioPenalty dyad)^((1:ℝ)/6)*
        Z^(εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh):=by
    rw [show Real.logb Z reference+εchild+εremove+
      (δ₂+u+ell+(δ₁+Real.logb Z (ratioPenalty dyad))/6+θclip/3)+κ*mesh=
      Real.logb Z reference+Real.logb Z (ratioPenalty dyad)*((1:ℝ)/6)+
        (εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) by ring]
    rw [Real.rpow_add hz0,Real.rpow_add hz0,Real.rpow_logb hz0 hz.ne' href,
      Real.rpow_mul hz0.le,Real.rpow_logb hz0 hz.ne' hr0]
  rw [hpow] at hh
  convert hh using 1 ; ring

end CenteredMomentEnergyCanonicalReferencePaid

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentEnergyBandSubtypeTransport
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyState
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentEnergyReindex
local notation "O" => Eisenstein.O
variable {α β : Type*} [Fintype α] [Fintype β]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

omit [Fintype α] [Fintype β] in
theorem positiveAt_embedding (e : β↪α)
    (W : ℝ→ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ)
    (h : PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C) :
    PositiveAt (α:=β) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C := by
  intro T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂
    hX₁ hX₂ hcap₁ hcap₂ hcapacity
  let E : T≃T.map e := subsetMapEquiv e T
  let θ' : T.map e→RayQuotient.Characters M H := θ∘E.symm
  let w' : T.map e→ℝ := w∘E.symm
  let σ' : T.map e→ℝ := σ∘E.symm
  let v' : T.map e→ℝ := v∘E.symm
  have hsum : (∑i:T.map e,w' i)=∑i:T,w i := E.symm.sum_comp w
  have hh := h (T.map e) θ' w' σ' v' t height
    (fun i=> hw (E.symm i)) (fun i=> hwL (E.symm i))
    (fun i=> hσlo (E.symm i)) (fun i=> hσhi (E.symm i))
    hheight (fun i=> hv (E.symm i)) s hQ hs p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂
    (by rw [hsum];exact hcapacity)
  have he := energy_reindex E s.character s.mask 1 (p.profile 0) (p.profile 1)
    (fun i:T.map e=> primePool M H bslot (Z^(w' i)))
    (fun (i:T.map e) I=> idealCoeff (relativeCharacter M H hH η₀ (θ' i)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w' i)) (σ' i) (v' i) I)
    (fun i:T.map e=> Z^(w' i)) t X₁ X₂ s.radial.keep s.radial.profile s.radial.scale
  have he' : energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:T=> primePool M H bslot (Z^(w i)))
      (fun (i:T) I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i:T=> Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale =
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:T.map e=> primePool M H bslot (Z^(w' i)))
      (fun (i:T.map e) I=> idealCoeff (relativeCharacter M H hH η₀ (θ' i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w' i)) (σ' i) (v' i) I)
      (fun i:T.map e=> Z^(w' i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale := by
    simpa only [Function.comp_def,θ',w',σ',v',Equiv.symm_apply_apply] using he
  exact he'.le.trans hh

omit [Fintype α] in
theorem positiveAt_subtype (T : Finset α)
    (W : ℝ→ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ)
    (h : PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C) :
    PositiveAt (α:=T) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C :=
  positiveAt_embedding M H hH ⟨Subtype.val,Subtype.val_injective⟩ W bslot a b bΦ Bmask L
    Lslot lo hi Mcap ε κ Z η₀ Q degree S C h

end CenteredMomentEnergyBandSubtypeTransport

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace CenteredMomentEnergyCanonicalUniformReference
open HeckeFamily 
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=> Eisenstein.O
variable {α:Type*}[Fintype α][DecidableEq α]

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

theorem original_subsets_reference_paid (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤ Mslot)(hεmask:0<εmask)(haPlain:0< a)(L:ℝ)(hL:0≤ L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤ Mcap)(hLs:0≤ Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0< Cc ∧ ∀η₀:Character,∃Z₀:ℝ,1< Z₀ ∧
    ∀Jorig:Finset α,∀θ:Jorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤ Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤ M →
    ∀C₀ C₁:ℝ,0≤ C₀ → 0≤ C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Jorig→ℝ)(v height mesh:ℝ),
    0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) → (∀i,w i≤ Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input Jorig,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤ bslot) → (∀i,src.M i≤ Mslot) →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),R≠0 →
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤ CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤ Mcap →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    let d:=commonData (withHeight src τ v) C R B
    d.X₁≤ Z^L → d.X₂≤ Z^L → d.Y₁≤ Z^L → d.Y₂≤ Z^L →
    ∀A Mparent reference u ell δ₁ δ₂ θclip:ℝ,0< reference →
    0≤ u → 0≤ ell → 0≤δ₁ → 0≤δ₂ → 0≤θclip →
    A+(6*κ-1)*(∑i:CenteredMomentCommonProfile.liveIndices B.val,w i.val)≤ Mparent →
    Real.logb Z (d.X₁*d.X₂*∏i:CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-Real.logb Z reference≤
      A-Mparent+6*(u+ell)+δ₁+Real.logb Z (ratioPenalty dyad) →
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)-Real.logb Z reference≤δ₂ →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    childEnergy d (canonicalRadial τ (internalQ Q η₀) dyad) D alloc ≤
      Cc*(Ideal.absNorm (R*C).radical:ℝ)^εmask*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        reference*(ratioPenalty dyad)^((1:ℝ)/6)*
        Z^(εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) := by
  have hex (J:Finset α):=actual_reference_paid_source (α:=J) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL degree S
    ha hWs hW hMcap hLs hε hbeta hκ
  choose n T dc Cc hCc hbound using hex
  let n₀:=∑J:Finset α,n J
  let dc₀:=∑J:Finset α,dc J
  let T₀:Finset (ℕ×ℕ):=Finset.univ.biUnion T
  let Ctot:ℝ:=1+∑J:Finset α,Cc J
  have hCt:0< Ctot:=by
    have hh:=Finset.sum_nonneg (fun J (_:J∈(Finset.univ:Finset (Finset α)))=>(hCc J).le)
    dsimp [Ctot];linarith
  refine ⟨n₀,T₀,dc₀,Ctot,hCt,?_⟩
  intro η₀
  let Choices:=ΣJ:Finset α,J→RayQuotient.Characters M H
  let:Fintype (RayQuotient.Characters M H):=Fintype.ofFinite _
  let:Fintype Choices:=inferInstance
  have hchoices (c:Choices):∃Z₀:ℝ,1< Z₀ ∧ _:=hbound c.1 η₀ c.2
  choose Zchoice hZchoice hb using hchoices
  let Z₀:ℝ:=1+∑c:Choices,Zchoice c
  have hZ₀:1< Z₀:=by
    have hn:Nonempty Choices:=⟨⟨∅,fun i=> False.elim (Finset.notMem_empty _ i.property)⟩⟩
    let:Nonempty Choices:=hn
    have hh:=Finset.sum_pos (s:=Finset.univ) (fun c _=>(zero_lt_one.trans (hZchoice c)))
      Finset.univ_nonempty
    dsimp [Z₀];linarith
  refine ⟨Z₀,hZ₀,?_⟩
  intro Jorig θ Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
  dsimp only
  intro hX₁ hX₂ hY₁ hY₂ A Mparent reference u ell δ₁ δ₂ θclip href
    hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  have hZi:Zchoice ⟨Jorig,θ⟩≤ Z:=by
    have hh:=Finset.single_le_sum (s:=Finset.univ)
      (fun c _=>(zero_lt_one.trans (hZchoice c)).le) (Finset.mem_univ (⟨Jorig,θ⟩:Choices))
    dsimp [Z₀] at hZ
    linarith
  have hp:=positiveAt_subtype M H hH Jorig W bslot (a/max 1 b) b 2 0 L Lslot lo hi
    Mcap εchild κ Z η₀ Q degree S C₁ hpos
  have hh:=hb ⟨Jorig,θ⟩ Z hZi εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hp
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ A Mparent reference u ell δ₁ δ₂ θclip href
    hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  have hc:Cc Jorig≤ Ctot:=by
    have hh:=Finset.single_le_sum (s:=Finset.univ) (fun J _=>(hCc J).le) (Finset.mem_univ Jorig)
    dsimp [Ctot];linarith
  have ht:T Jorig⊆T₀:=by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨Jorig,Finset.mem_univ _,hx⟩
  have hctrl:p.control (T Jorig)≤ p.control T₀:=by
    unfold Profiles.control
    exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono ht) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono ht) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hn₀:n Jorig≤ n₀:=Finset.single_le_sum (fun _ _=> Nat.zero_le _) (Finset.mem_univ Jorig)
  have hdc₀:dc Jorig≤ dc₀:=Finset.single_le_sum (fun _ _=> Nat.zero_le _) (Finset.mem_univ Jorig)
  have hdeg:dc Jorig+degree+4*n Jorig≤ dc₀+degree+4*n₀:=by omega
  have hpow:(1+(|v|+height))^(dc Jorig+degree+4*n Jorig)≤
      (1+(|v|+height))^(dc₀+degree+4*n₀):=
    pow_le_pow_right₀ (by linarith [abs_nonneg v]) hdeg
  have hcontrol:=p.control_nonneg (T Jorig)
  have hd:0≤ diagonalControl (canonicalRadial τ (internalQ Q η₀) dyad).profile:=by
    unfold diagonalControl;positivity
  have hz0:0< Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have hr:0< ratioPenalty dyad:=zero_lt_one.trans_le (le_max_left _ _)
  apply hh.trans
  gcongr

end CenteredMomentEnergyCanonicalUniformReference

end

end

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace CenteredMomentEnergyProfiles
/-- A Schwartz profile supported in a fixed interval. -/
structure Test (a b:ℝ) where
  profile : 𝓢(ℝ,ℂ)
  support : Function.support (profile:ℝ→ℂ)⊆Set.Icc a b

open CenteredMomentSectorLocalization in
lemma annulus_support : Function.support (fun x:ℝ=>(annulus x:ℂ))⊆Set.Icc (1/4:ℝ) 1:=by
  intro x hx
  have hn:annulus x≠0:=by simpa using hx
  exact ⟨(lt_of_not_ge (fun h=>hn (annulus_zero_low x h))).le,
    (lt_of_not_ge (fun h=>hn (annulus_zero_high x h))).le⟩

/-- The smooth dyadic annulus as a compactly supported Schwartz profile. -/
def annulusTemplate:Test (1/4) 1 where
  profile:=(HasCompactSupport.of_support_subset_isCompact isCompact_Icc annulus_support).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp CenteredMomentSectorLocalization.annulus_smooth)
  support:=annulus_support

lemma annulusTemplate_apply (x:ℝ):annulusTemplate.profile x=(CenteredMomentSectorLocalization.annulus x:ℂ):=rfl

def annulusSeed (a b:ℝ)(ha:a≤1/4)(hb:1≤b):Test a b where
  profile:=annulusTemplate.profile
  support:=fun _x hx=>⟨ha.trans (annulusTemplate.support hx).1,
    (annulusTemplate.support hx).2.trans hb⟩


end CenteredMomentEnergyProfiles
end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace CenteredMomentEnergyProfiles
open CenteredMomentFiniteProfileExceptional CenteredMomentAllocatedNaturalSource
open CenteredMomentScaleSupremum

def derivativeChoice (W:𝓢(ℝ,ℂ))(j:Fin 2):𝓢(ℝ,ℂ):=
  if j=0 then W else DetectorDictionaryInverseUniform.scaleCLM W

lemma derivativeChoice_apply (W:𝓢(ℝ,ℂ))(j:Fin 2):
    (derivativeChoice W j:ℝ→ℂ)=scaleTest W j:=by
  unfold derivativeChoice scaleTest
  split_ifs
  · rfl
  · exact funext (DetectorDictionaryInverseUniform.scaleCLM_apply W)

lemma derivativeChoice_support (a b:ℝ)(W:𝓢(ℝ,ℂ))
    (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)(j:Fin 2):
    Function.support (derivativeChoice W j:ℝ→ℂ)⊆Set.Icc a b:=by
  rw [derivativeChoice_apply]
  exact scaleTest_support W a b hs j

def step (a b:ℝ)(ha:0< a)(W:Test a b)(U:ℝ)(hU:0< U)(t:ℝ)(j:Fin 2):
    Test (a/max 1 b) b where
  profile:=derivativeChoice ((sourcePlain a b ha W.profile W.support).profile U hU t) j
  support:=derivativeChoice_support _ _ _ (sourcePlain_support a b ha W.profile W.support U hU t) j

theorem step_control (a b:ℝ)(ha:0< a)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀W:Test a b,∀U:ℝ,∀hU:0< U,∀t:ℝ,∀j:Fin 2,
      sourceControl S (step a b ha W U hU t j).profile≤
        C*sourceControl T W.profile*(1+‖t‖)^n:=by
  obtain ⟨n₀,T₀,C₀,hC₀,h₀⟩:=plain_profile_source_control a b ha S
  obtain ⟨n₁,T₁,C₁,hC₁,h₁⟩:=scaled_plain_profile_source_control a b ha S
  refine ⟨n₀+n₁,T₀∪T₁,C₀+C₁,add_pos hC₀ hC₁,?_⟩
  intro W U hU t j
  have hT₀:sourceControl T₀ W.profile≤ sourceControl (T₀∪T₁) W.profile:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left : T₀⊆T₀∪T₁)) W.profile
  have hT₁:sourceControl T₁ W.profile≤ sourceControl (T₀∪T₁) W.profile:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_right : T₁⊆T₀∪T₁)) W.profile
  have hH:1≤1+‖t‖:=by linarith [norm_nonneg t]
  have hR:=sourceControl_nonneg (T₀∪T₁) W.profile
  by_cases hj:j=0
  · have hh:=h₀ W.profile W.support U hU t
    change sourceControl S (if j=0 then _ else _)≤ _
    rw [if_pos hj]
    apply hh.trans
    exact mul_le_mul
      (mul_le_mul (le_add_of_nonneg_right hC₁.le) hT₀ (sourceControl_nonneg _ _)
        (add_pos hC₀ hC₁).le)
      (pow_le_pow_right₀ hH (Nat.le_add_right _ _)) (by positivity) (by positivity)
  · have hh:=h₁ W.profile W.support U hU t
    change sourceControl S (if j=0 then _ else _)≤ _
    rw [if_neg hj]
    apply hh.trans
    exact mul_le_mul
      (mul_le_mul (le_add_of_nonneg_left hC₀.le) hT₁ (sourceControl_nonneg _ _)
        (add_pos hC₀ hC₁).le)
      (pow_le_pow_right₀ hH (Nat.le_add_left _ _)) (by positivity) (by positivity)

/-- Repeated radial-profile transformations with bounded height parameters. -/
inductive Path (a b:ℝ)(ha:0< a)(T:ℝ)(W:Test a b):
    (n:ℕ)→Test (lower a b n) b→Prop
  | base : Path a b ha T W 0 W
  | next {n:ℕ}{V:Test (lower a b n) b}
      (path:Path a b ha T W n V)(U:ℝ)(hU:0< U)(t:ℝ)(j:Fin 2)(ht:‖t‖≤ T):
      Path a b ha T W (n+1) (step _ b (lower_pos a b ha n) V U hU t j)

theorem path_control (a b:ℝ)(ha:0< a)(d:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃R:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀W:Test a b,∀T:ℝ,0≤ T→∀V:Test (lower a b d) b,Path a b ha T W d V→
      sourceControl S V.profile≤ C*sourceControl R W.profile*(1+T)^n:=by
  induction d generalizing S with
  | zero=>
    refine ⟨0,S,1,zero_lt_one,?_⟩
    intro W T hT V hpath
    cases hpath
    simp
  | succ d ih=>
    obtain ⟨ns,Rs,Cs,hCs,hs⟩:=step_control (lower a b d) b (lower_pos a b ha d) S
    obtain ⟨np,R,Cp,hCp,hp⟩:=ih Rs
    refine ⟨np+ns,R,Cs*Cp,mul_pos hCs hCp,?_⟩
    intro W T hT V hpath
    cases hpath with
    | next old U hU t j ht=>
      rename_i V
      have h1:=hs V U hU t j
      have h2:=hp W T hT V old
      have hR:=sourceControl_nonneg R W.profile
      have h3:(1+‖t‖)^ns≤(1+T)^ns:=pow_le_pow_left₀ (by positivity) (by linarith) ns
      apply h1.trans
      apply (mul_le_mul (mul_le_mul_of_nonneg_left h2 hCs.le) h3 (by positivity) (by positivity)).trans_eq
      rw [pow_add]
      ring

lemma support_at_depth (a b:ℝ)(ha:0< a)(d n:ℕ)(hn:n≤ d)
    (V:Test (lower a b n) b):
    Function.support (V.profile:ℝ→ℂ)⊆Set.Icc (lower a b d) b:=by
  intro x hx
  exact ⟨(lower_antitone a b ha hn).trans (V.support hx).1,(V.support hx).2⟩

theorem paths_upto_control (a b:ℝ)(ha:0< a)(d:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃R:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀W:Test a b,∀T:ℝ,0≤ T→∀k:ℕ,k≤ d→∀V:Test (lower a b k) b,
      Path a b ha T W k V→
      sourceControl S V.profile≤ C*sourceControl R W.profile*(1+T)^n:=by
  choose J R C hC hbound using fun k:Fin (d+1)=> path_control a b ha k.val S
  let Rs:Finset (ℕ×ℕ):=Finset.univ.biUnion R
  let Cs:ℝ:=1+∑k,C k
  have hCs:0< Cs:=by
    have hh:=Finset.sum_nonneg (fun k (_:k∈(Finset.univ:Finset (Fin (d+1))))=>(hC k).le)
    dsimp [Cs];linarith
  refine ⟨∑k,J k,Rs,Cs,hCs,?_⟩
  intro W T hT k hk V hpath
  let l:Fin (d+1):=⟨k,by omega⟩
  have he:=hbound l W T hT V hpath
  have hR:R l⊆Rs:=by
    intro i hi
    exact Finset.mem_biUnion.mpr ⟨l,Finset.mem_univ _,hi⟩
  have hcontrol:sourceControl (R l) W.profile≤ sourceControl Rs W.profile:=
    Seminorm.le_def.mp (Finset.sup_mono hR) W.profile
  have hconst:C l≤ Cs:=by
    have hh:=Finset.single_le_sum (fun j (_:j∈(Finset.univ:Finset (Fin (d+1))))=>(hC j).le)
      (Finset.mem_univ l)
    dsimp [Cs];linarith
  have hdegree:J l≤∑j,J j:=Finset.single_le_sum (fun j (_:j∈(Finset.univ:Finset (Fin (d+1))))=> Nat.zero_le _) (Finset.mem_univ l)
  have hRpos:=sourceControl_nonneg Rs W.profile
  apply he.trans
  exact mul_le_mul (mul_le_mul hconst hcontrol (sourceControl_nonneg _ _) hCs.le)
    (pow_le_pow_right₀ (by linarith) hdegree) (by positivity) (by positivity)

end CenteredMomentEnergyProfiles

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentEnergyAmplifiedRayDictionary
open HeckeFamily CenteredMomentSecondHeightFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentAmplificationChildSourceCaps CenteredMomentAllocatedRayDictionary
open CenteredMomentFirstAnnularInput CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open CenteredMomentInductionEnergy CenteredMomentCommonMaskEnergy
open CenteredMomentEligibleEnergy CenteredMomentCommonHeightEnvelope
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O" => Eisenstein.O
variable {α : Type*} [Fintype α]
local instance {β : Type*} : DecidableEq β := Classical.decEq _

lemma active_pools_subset (s : Input α) (j : α⊕Fin 2) :
    (activeInput s).pools j⊆s.pools j := by
  cases j with
  | inl i => exact Finset.filter_subset _ _
  | inr j => exact Finset.Subset.refl _

lemma actualAllocations_mono {β : Type*} [Fintype β]
    (S T : β→Finset (Ideal O)) (h : ∀i,S i⊆T i) (C : Ideal O) :
    actualAllocations S C⊆actualAllocations T C := by
  intro B hB
  obtain ⟨hlabel,hprod⟩ := Finset.mem_filter.mp hB
  obtain ⟨v,hv,hvB⟩ := Finset.mem_image.mp hlabel
  refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨v,?_,hvB⟩,hprod⟩
  exact Fintype.mem_piFinset.mpr (fun i=> h i (Fintype.mem_piFinset.mp hv i))

abbrev restoreAllocation (s : Input α) (C : Ideal O)
    (B : actualAllocations (activeInput s).pools C) : actualAllocations s.pools C :=
  ⟨B.val,actualAllocations_mono _ _ (active_pools_subset s) C B.property⟩

@[simp] lemma restoreAllocation_val (s : Input α) (C : Ideal O)
    (B : actualAllocations (activeInput s).pools C) : (restoreAllocation s C B).val=B.val := rfl

lemma restoreAllocation_injective (s : Input α) (C : Ideal O) :
    Function.Injective (restoreAllocation s C) := by
  intro B D h
  exact Subtype.ext (congrArg (fun x : actualAllocations s.pools C=> x.val) h)

lemma child_active (s : Input α) (C R : Ideal O)
    (B : actualAllocations (activeInput s).pools C) (τ : Character) (t : ℝ) :
    child (activeInput s) C R B τ t=
      activeInput (child s C R (restoreAllocation s C B) τ t) := rfl

lemma active_coefficient (s : Input α) (i : α) :
    (activeInput s).toData.coefficient i=s.toData.coefficient i := rfl

lemma rowSlot_active (s : Input α) (i : α) (η : Character) (m A z : O) (t v : ℝ) :
    rowSlot η m A z ((activeInput s).slots i)
      (heightCoefficient ((activeInput s).toData.coefficient i) v) t=
    rowSlot η m A z (s.slots i) (heightCoefficient (s.toData.coefficient i) v) t := by
  unfold rowSlot
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro I hI hn
  have hz : s.W i ((I.absNorm:ℝ)/s.P i)=0 := by
    by_contra hh
    exact hn (Finset.mem_filter.mpr ⟨hI,hh⟩)
  simp only [heightCoefficient,Data.coefficient,activeInput,hz,mul_zero,zero_mul]

lemma positive_active (s : Input α) (η : Character) (m A z : O)
    (W₁ W₂ : ℝ→ℂ) (t v X₁ X₂ : ℝ) :
    positiveSlotRow η m A z W₁ W₂ (activeInput s).slots
      (fun i=> heightCoefficient ((activeInput s).toData.coefficient i) v)
      (activeInput s).P t X₁ X₂=
    positiveSlotRow η m A z W₁ W₂ s.slots
      (fun i=> heightCoefficient (s.toData.coefficient i) v) s.P t X₁ X₂ := by
  unfold positiveSlotRow
  congr 2
  exact Finset.prod_congr rfl (fun i _=> rowSlot_active s i η m A z t v)

theorem energy_active (s : Input α) (η : Character) (m A : O)
    (W₁ W₂ : ℝ→ℂ) (t v X₁ X₂ : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy η m A t W₁ W₂ (activeInput s).slots
      (fun i=> heightCoefficient ((activeInput s).toData.coefficient i) v)
      (activeInput s).P X₁ X₂ keep Φ K=
    energy η m A t W₁ W₂ s.slots
      (fun i=> heightCoefficient (s.toData.coefficient i) v) s.P X₁ X₂ keep Φ K := by
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_active]

theorem positive_active_restrict {κ : Type*} [Fintype κ] (s : Input α) (f : κ→α)
    (η : Character) (m A z : O) (W₁ W₂ : ℝ→ℂ) (t v X₁ X₂ : ℝ) :
    positiveSlotRow η m A z W₁ W₂ (fun i=>(activeInput s).slots (f i))
      (fun i=> heightCoefficient ((activeInput s).toData.coefficient (f i)) v)
      (fun i=>(activeInput s).P (f i)) t X₁ X₂=
    positiveSlotRow η m A z W₁ W₂ (fun i=> s.slots (f i))
      (fun i=> heightCoefficient (s.toData.coefficient (f i)) v)
      (fun i=> s.P (f i)) t X₁ X₂ := by
  unfold positiveSlotRow
  congr 2
  exact Finset.prod_congr rfl (fun i _=> rowSlot_active s (f i) η m A z t v)

theorem energy_active_restrict {κ : Type*} [Fintype κ] (s : Input α) (f : κ→α)
    (η : Character) (m A : O) (W₁ W₂ : ℝ→ℂ) (t v X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy η m A t W₁ W₂ (fun i=>(activeInput s).slots (f i))
      (fun i=> heightCoefficient ((activeInput s).toData.coefficient (f i)) v)
      (fun i=>(activeInput s).P (f i)) X₁ X₂ keep Φ K=
    energy η m A t W₁ W₂ (fun i=> s.slots (f i))
      (fun i=> heightCoefficient (s.toData.coefficient (f i)) v)
      (fun i=> s.P (f i)) X₁ X₂ keep Φ K := by
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_active_restrict]

theorem common_energy_active (s : Input α) (C R : Ideal O)
    (B : actualAllocations (activeInput s).pools C) (τ : Character) (v : ℝ)
    (L : Ideal O)
    (a : CenteredMomentDivisorAllocation.Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2)))
    (J : Finset (liveIndices B.val)) (m A : O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let d : CenteredMomentEligibleEnergy.Data (liveIndices B.val) :=
      commonData (withHeight (activeInput s) τ v) C R
        ⟨B.val, by simpa only [withHeight, Input.pools] using B.property⟩
    let e : CenteredMomentEligibleEnergy.Data (liveIndices B.val) :=
      commonData (withHeight s τ v) C R
        ⟨B.val, by simpa only [withHeight, Input.pools, restoreAllocation_val]
          using (restoreAllocation s C B).property⟩
    energy τ m A 0 W₁ W₂
      (fun i:remaining (activeInput s) C B L a J=> d.slots i.val)
      (fun i:remaining (activeInput s) C B L a J=> heightCoefficient (d.coefficient i.val) v)
      (fun i:remaining (activeInput s) C B L a J=> d.P i.val) X₁ X₂ keep Φ K=
    energy τ m A 0 W₁ W₂
      (fun i:remaining s C (restoreAllocation s C B) L a J=> e.slots i.val)
      (fun i:remaining s C (restoreAllocation s C B) L a J=> heightCoefficient (e.coefficient i.val) v)
      (fun i:remaining s C (restoreAllocation s C B) L a J=> e.P i.val) X₁ X₂ keep Φ K := by
  exact energy_active_restrict s
    (fun i:remaining (activeInput s) C B L a J=> i.val.val) τ m A W₁ W₂ 0 v X₁ X₂ keep Φ K

def restoredError (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) : Input (liveIndices Bp.val) :=
  twiceChild s C R B τ t Q k (restoreAllocation (child s C R B τ t) (Q^k) Bp) υ v

lemma error_source_active (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    child (activeInput (child s C R B τ t)) (Q^k) (R*C) Bp υ v=
      activeInput (restoredError s C R B τ t Q k Bp υ v) := rfl

theorem restoredError_data (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    let d:=restoredError s C R B τ t Q k Bp υ v
    d.η=υ ∧ d.t=v ∧ d.m=fixedBadMask*cubicIdealGenerator ((R*C)*(Q^k)) ∧
    d.X₁=s.X₁/(B.val (Sum.inr 0)).absNorm/(Bp.val (Sum.inr 0)).absNorm ∧
    d.X₂=s.X₂/(B.val (Sum.inr 1)).absNorm/(Bp.val (Sum.inr 1)).absNorm ∧
    d.Y₁=s.Y₁/(B.val (Sum.inr 0)).absNorm/(Bp.val (Sum.inr 0)).absNorm ∧
    d.Y₂=s.Y₂/(B.val (Sum.inr 1)).absNorm/(Bp.val (Sum.inr 1)).absNorm :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem error_live_slots (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k)) :
    liveIndices Bp.val=Finset.univ :=
  prime_slots_live (activeInput (child s C R B τ t)) Q hQ k hslot Bp

theorem restoredError_volume (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    volume (restoredError s C R B τ t Q k Bp υ v)=
      volume s/(CenteredMomentCommonRawScale.rawReduction B.val s.P*(Q.absNorm:ℝ)^k) := by
  have hh:=child_volume (activeInput (child s C R B τ t)) Q hQ k hslot (R*C) Bp υ v
  rw [error_source_active,active_volume,active_volume,common_volume,div_div] at hh
  exact hh

theorem error_normalized_source (s : Input α) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    childNormalizedGaussSource (activeInput (child s C R B τ t)) (Q^k) (R*C) seed Bp υ v Φ K=
      normalizedGaussSource (restoredError s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed Φ K := by
  unfold childNormalizedGaussSource
  rw [error_source_active,active_normalized]

theorem error_normalized_sum (s : Input α) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (υ : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k)→Character)
    (v : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k)→ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑Bp:actualAllocations (activeInput (child s C R B τ t)).pools (Q^k),
      childNormalizedGaussSource (activeInput (child s C R B τ t)) (Q^k) (R*C) seed Bp (υ Bp) (v Bp) Φ K)=
    ∑Bp:actualAllocations (activeInput (child s C R B τ t)).pools (Q^k),
      normalizedGaussSource (restoredError s C R B τ t Q k Bp (υ Bp) (v Bp)) ((R*C)*(Q^k)) seed Φ K :=
  Finset.sum_congr rfl (fun Bp _=> error_normalized_source s C R seed B τ t Q k Bp (υ Bp) (v Bp) Φ K)

theorem error_energy (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let e:=child (activeInput (child s C R B τ t)) (Q^k) (R*C) Bp υ v
    let d:=restoredError s C R B τ t Q k Bp υ v
    energy e.η e.m 1 0 W₁ W₂ e.slots
      (fun i=> heightCoefficient (e.toData.coefficient i) e.t) e.P X₁ X₂ keep Φ K=
    energy d.η d.m 1 0 W₁ W₂ d.slots
      (fun i=> heightCoefficient (d.toData.coefficient i) d.t) d.P X₁ X₂ keep Φ K := by
  dsimp only
  rw [error_source_active]
  exact energy_active (restoredError s C R B τ t Q k Bp υ v) υ
    (fixedBadMask*cubicIdealGenerator ((R*C)*(Q^k))) 1 W₁ W₂ 0 v X₁ X₂ keep Φ K

section Ray
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
variable {s : Input α} {η₀ : Character} {θ : α→RayQuotient.Characters M H}
  {w σ freq : α→ℝ} {W : ℝ→ℂ} {bslot Z : ℝ}

theorem matches_child (h : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    Matches M H hH (child s C R B τ t) η₀
      (fun i=>θ i.val) (fun i=> w i.val) (fun i=>σ i.val)
      (fun i=> freq i.val) W bslot Z := by
  constructor
  · intro i I;exact h.character i.val I
  · intro i y;exact h.profile i.val y
  · intro i;exact h.pool i.val
  · intro i;exact h.scale i.val

theorem matches_twiceChild (h : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :
    Matches M H hH (twiceChild s C R B τ t Q k Bp υ v) η₀
      (fun i=>θ i.val.val) (fun i=> w i.val.val) (fun i=>σ i.val.val)
      (fun i=> freq i.val.val) W bslot Z :=
  matches_child M H hH (matches_child M H hH h C R B τ t) (Q^k) (R*C) Bp υ v

theorem active_common_ray_energy (h : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations (activeInput s).pools C) (L : Ideal O)
    (a : CenteredMomentDivisorAllocation.Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2)))
    (J : Finset (liveIndices B.val)) (m A : O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let d : CenteredMomentEligibleEnergy.Data (liveIndices B.val) :=
      commonData (withHeight (activeInput s) τ v) C R
        ⟨B.val, by simpa only [withHeight, Input.pools] using B.property⟩
    energy τ m A 0 W₁ W₂
      (fun i:remaining (activeInput s) C B L a J=> d.slots i.val)
      (fun i:remaining (activeInput s) C B L a J=> heightCoefficient (d.coefficient i.val) v)
      (fun i:remaining (activeInput s) C B L a J=> d.P i.val) X₁ X₂ keep Φ K=
    energy τ m A 0 W₁ W₂
      (fun i:originalImage s C (restoreAllocation s C B) L a J=> primePool M H bslot (Z^(w i)))
      (fun i:originalImage s C (restoreAllocation s C B) L a J=> fun I=>
        idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v+freq i) I)
      (fun i:originalImage s C (restoreAllocation s C B) L a J=> Z^(w i)) X₁ X₂ keep Φ K :=
  (common_energy_active s C R B τ v L a J m A W₁ W₂ X₁ X₂ keep Φ K).trans
    (common_energy h τ v C R (restoreAllocation s C B) L a J m A W₁ W₂ X₁ X₂ keep Φ K)

theorem restoredError_matches (h : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    Matches M H hH (restoredError s C R B τ t Q k Bp υ v) η₀
      (fun i=>θ i.val.val) (fun i=> w i.val.val) (fun i=>σ i.val.val)
      (fun i=> freq i.val.val) W bslot Z :=
  matches_twiceChild M H hH h C R B τ t Q k (restoreAllocation (child s C R B τ t) (Q^k) Bp) υ v

end Ray
end CenteredMomentEnergyAmplifiedRayDictionary

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

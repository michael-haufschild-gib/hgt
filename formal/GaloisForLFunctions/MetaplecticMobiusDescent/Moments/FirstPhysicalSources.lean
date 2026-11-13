/-
First physical sources adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.FirstSectorTails
import GaloisForLFunctions.MetaplecticMobiusDescent.Energy.NaturalStates

/-!
# First physical sources

Coefficients, columns, blocks, elements and inactive weights of the first physical source;
sector masses and retained norms of the first active sectors.
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
open Filter
namespace CenteredMomentRayMaskedFloor
open HeckeFamily HeckeZeroSupremum InversePrincipalEnergy
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentPrimeSlot CenteredMomentInductionEnergy
local notation "O" => Eisenstein.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem exists_positive_floor {α : Type*} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (a₀ b₀ bΦ Bmask ε Lslot lo hi κ : ℝ)
    (ha₀ : 0< a₀) (hb₀ : 0≤ b₀) (hbΦ : 0< bΦ) (hmask : 0≤ Bmask)
    (hε : 0<ε) (hLs : 0≤ Lslot) (hbeta : (51/100:ℝ)≤ beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ T → (∀i,|v i|≤ T) →
    ∀(Q : Ideal O),Q≤ M → ∀s : NaturalState Z Bmask bΦ,
      s.fixedModulus=internalQ Q η₀ → s.width≤ε/16 → 6*κ*(∑i,w i)≤ s.width →
    ∀p : Profiles a₀ b₀,∀X₁ X₂ : ℝ,0< X₁ → 0< X₂ →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=> primePool M H b (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i=> Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      C*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+T)^degree*Z^(s.width+ε) := by
  let e : ℝ := ε/(4*(Bmask+1))
  have he : 0< e := div_pos hε (by positivity)
  have hcost : Bmask*e≤ε/4 := by
    have hh := mul_le_mul_of_nonneg_left (show Bmask≤ Bmask+1 by linarith) he.le
    have hid : e*(Bmask+1)=ε/4 := by dsimp [e]; field_simp
    rw [hid] at hh
    linarith
  obtain ⟨J,S,C,hC,hfloor⟩ := natural_masked_positive_floor (α:=α) M H hH W a b ha hWs hW
    a₀ b₀ e ha₀ hb₀ he (ε/16) Lslot (ε/4) lo hi κ bΦ (by positivity) hbΦ.le hLs
    (by positivity) hbeta hκ
  refine ⟨J,S,C*bΦ^4,mul_pos hC (pow_pos hbΦ _),?_⟩
  intro η₀
  filter_upwards [hfloor η₀] with Z hZ
  intro θ w σ v t T hw hwL hσlo hσhi hT hv Q hQM s hQ hs hslots p X₁ X₂ hX₁ hX₂
  have hZ1 := s.base_ge_one
  have hZ0 : 0< Z := zero_lt_one.trans_le hZ1
  have hrad : (s.puncture.radical.absNorm:ℝ)^e≤ Z^(Bmask*e) := by
    rw [Real.rpow_mul hZ0.le]
    exact Real.rpow_le_rpow (by positivity) s.radical_bound he.le
  have hex (z : O) (hz : s.radial.keep z) :
      ¬CenteredExceptionalProfile.FixedInducingRow s.character (internalQ Q η₀)
        (fixedBadMask*cubicIdealGenerator s.puncture) 1 z := by
    rw [←hQ]
    exact s.nonexceptional z hz
  have hh := hZ θ w σ v t T hw hwL hσlo hσhi hT hv s.character Q s.radial s.puncture
    s.puncture_ne_zero hQM s.row_ne_zero hex s.radial_support s.rowWidth s.characterWidth
    (ε/16) s.row_nonneg s.character_nonneg hs le_rfl s.scale_eq s.modulus_bound
    (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) X₁ X₂ hX₁ hX₂
  have hwidth : s.rowWidth≤ s.width := by dsimp [NaturalState.width]; linarith [s.character_nonneg]
  have hbudget : Bmask*e+(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i))≤ s.width+ε := by
    linarith
  have hpow : Z^(Bmask*e)*Z^(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i))≤ Z^(s.width+ε) := by
    rw [←Real.rpow_add hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ1 hbudget
  have hd := diagonalControl_nonneg s.radial.profile
  have hc := p.control_nonneg S
  apply hh.trans
  change C*(s.puncture.radical.absNorm:ℝ)^e*diagonalControl s.radial.profile*bΦ^4*
    (p.control S)^2*(1+|t|+T)^J*Z^(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i))≤ _
  calc
    _ ≤ C*Z^(Bmask*e)*diagonalControl s.radial.profile*bΦ^4*
      (p.control S)^2*(1+|t|+T)^J*Z^(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i)) := by gcongr
    _ = (C*bΦ^4*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+T)^J)*
      (Z^(Bmask*e)*Z^(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

end CenteredMomentRayMaskedFloor

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace CenteredMomentSourceInputFirstSectorTail
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceZeroEnergy CenteredMomentSourceLiveColumn CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceProfileMassUniform CenteredMomentSourceProfileMass
open CenteredMomentSupportedTailAggregate CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair CenteredMomentNaturalRadialCutoff
open CenteredMomentSourceInputTailUniform CenteredMomentFirstTailAggregate
open CenteredMomentSourceInputFirstTailUniform
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

omit [DecidableEq ι] in
theorem local_input_tail_arbitrary_saving (hi:ι→ℝ)(wlo whi B ξ saving:ℝ)
    (hhi:∀i,0≤ hi i)(hwlo:0< wlo)(hwhi:0≤ whi)(hB:0≤ B)(hξ:0<ξ):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤ hi i)→∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K Tsec:ℝ),
      0< K→volume s.toData≤ Z^B→Tsec≤ Z^B→(volume s.toData)^2/K≤ Tsec→
      ‖CenteredMomentFirstSectorLocalization.discardedEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K (volume s.toData) Z ξ‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving):=by
  obtain ⟨Adec,hdecay⟩:=choose_first_tail_order B ξ saving hB hξ
  obtain ⟨SΦ,Ctail,hCtail,htail⟩:=local_discarded_energy_bound Adec 1 zero_lt_one
  let Cmass:=1+2*128^(Fintype.card ι+2)*(∏i,hi i)*whi^2
  have hprodhi:0≤∏i,hi i:=Finset.prod_nonneg (fun i _=> hhi i)
  have hCmass:0< Cmass:=by dsimp [Cmass];positivity
  let HN:=Real.log (max 1 ((∏i,hi i)*whi^2))
  have hexp:(∏i,hi i)*whi^2≤ Real.exp HN:=by
    dsimp [HN]
    rw [Real.exp_log (zero_lt_one.trans_le (le_max_left _ _))]
    exact le_max_right _ _
  let C:=Cmass^2*Ctail*(Real.exp HN)*(1+Real.exp (2*HN))^2
  refine ⟨SΦ,C,by dsimp [C];positivity,?_⟩
  filter_upwards [eventually_tail_threshold HN ξ hξ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K Tsec hK hVcap hTcap hnom
  let V:=volume s.toData
  have hV:0< V:=volume_pos s
  have hT:0< Tsec:=(div_pos (sq_pos_of_pos hV) hK).trans_le hnom
  have hmass:=input_mass hi whi hhi hwhi s W₁ W₂ wlo hwlo he₁ he₂ hs₁ hs₂ hshi R seed
  have hcontrol:=plainControl_nonneg s W₁ W₂
  have hm:(∑I∈finiteColumns (Fintype.piFinset s.pools),‖coefficient s R seed I‖)≤
      Cmass*plainControl s W₁ W₂*V:=by
    apply hmass.trans
    apply mul_le_mul_of_nonneg_right _ hV.le
    apply mul_le_mul_of_nonneg_right _ hcontrol
    dsimp [Cmass]
    linarith
  have hn (I:Ideal O)(_hI:I∈finiteColumns (Fintype.piFinset s.pools))
      (hI:coefficient s R seed I≠0):(Ideal.absNorm I:ℝ)≤ Real.exp HN*V:=
    (input_column_bound hi whi s W₁ W₂ wlo hwlo he₁ he₂ hs₁ hs₂ hshi R seed I hI).trans
      (mul_le_mul_of_nonneg_right hexp hV.le)
  have ht:=htail s.η m A s.t (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)
    Φ K V HN Tsec Z 1 ξ hK hV hZ.1 le_rfl hn
    hnom (by simpa using hZ.2)
  simp only [Real.rpow_one] at ht
  have hsquare:=pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=> norm_nonneg _)) hm 2
  have hp:0< min 1 (kernelReference Tsec HN):=lt_min zero_lt_one (kernelReference_pos _ _ hT)
  have hzpos:0< Z:=zero_lt_one.trans hZ.1
  have hzpower:0< Z^(ξ/4):=Real.rpow_pos_of_pos hzpos _
  have hden:0<(min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec:=by positivity
  have hb:=hdecay HN Z V Tsec hZ.1.le hV hVcap hT hTcap
  calc
    _≤((Cmass*plainControl s W₁ W₂*V)^2*K*(Real.exp HN*V)*
        (Ctail*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec))/V:=by
      apply div_le_div_of_nonneg_right _ hV.le
      apply ht.trans
      apply div_le_div_of_nonneg_right _ hden.le
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsquare (mul_nonneg (Real.exp_pos HN).le hV.le)) hK.le).trans_eq
        (by ring)
    _=(Cmass^2*Ctail*(Real.exp HN)*(plainControl s W₁ W₂)^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        (V^2*((min 1 (kernelReference Tsec HN))^2)⁻¹*((1+Z^(ξ/4))^Adec)⁻¹):=by
      field_simp [ne_of_gt hV,ne_of_gt hp]
    _≤(Cmass^2*Ctail*(Real.exp HN)*(plainControl s W₁ W₂)^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        ((1+Real.exp (2*HN))^2*Z^(-saving)):=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _=_:=by dsimp [C];ring

end CenteredMomentSourceInputFirstSectorTail

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace CenteredMomentSourceInputFirstSectorTail
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceZeroEnergy CenteredMomentSourceLiveColumn CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceProfileMassUniform CenteredMomentSourceProfileMass
open CenteredMomentSupportedTailAggregate CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair CenteredMomentNaturalRadialCutoff
open CenteredMomentSourceInputTailUniform CenteredMomentFirstTailAggregate
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

omit [DecidableEq ι] in
theorem local_input_tail (hi:ι→ℝ)(wlo whi B ξ saving:ℝ)
    (hhi:∀i,0≤ hi i)(hwlo:0< wlo)(hwhi:0≤ whi)(hB:0≤ B)(hξ:0<ξ):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤ hi i)→∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),
      0< K→volume s.toData≤ Z^B→K⁻¹≤ Z^B→
      ‖CenteredMomentFirstSectorLocalization.discardedEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K (volume s.toData) Z ξ‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving) := by
  obtain ⟨S,C,hC,htail⟩ := local_input_tail_arbitrary_saving hi wlo whi (3*B) ξ saving
    hhi hwlo hwhi (by positivity) hξ
  refine ⟨S,C,hC,?_⟩
  filter_upwards [htail] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK hV hKi
  have hz : 0< Z := zero_lt_one.trans hZ.1
  have hV0 : 0< volume s.toData := volume_pos s
  have hVcap : volume s.toData≤ Z^(3*B) := hV.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith))
  have hTcap : (volume s.toData)^2/K≤ Z^(3*B) := by
    rw [div_eq_mul_inv]
    apply (mul_le_mul (pow_le_pow_left₀ hV0.le hV 2) hKi (inv_nonneg.mpr hK.le) (by positivity)).trans_eq
    rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz]
    congr 1
    norm_num
    ring
  exact hZ.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K _ hK hVcap hTcap le_rfl

end CenteredMomentSourceInputFirstSectorTail

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace CenteredMomentSourceInputFirstRemainder
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentExceptionalAmplitudePair CenteredMomentSourceInputTailUniform
open CenteredMomentSourceInputZeroUniform CenteredMomentSourceInputFirstSectorTail
open CenteredMomentFirstEnergy SchwartzPlanePoisson
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

omit [DecidableEq ι] in
theorem original_first_remainder (hi:ι→ℝ)(wlo whi B ε ξ saving:ℝ)
    (hhi:∀i,0≤ hi i)(hwlo:0< wlo)(hwhi:0≤ whi)(hB:0≤ B)(hε:0<ε)(hξ:0<ξ):
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0< Cdiag ∧ 0< Ctail ∧
      ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),
      s.W₁=W₁→s.W₂=W₂→Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→(∀i,s.hi i≤ hi i)→
      ∀(m A:O),lambda∣m→(2:O)∣m→
      ∀(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0< K→
      volume s.toData≤ Z^B→K⁻¹≤ Z^B→
      ‖finiteHeckeEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
          (coefficient s R seed) Φ K-
        CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A s.t
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed) Φ K
          (volume s.toData) Z ξ‖/volume s.toData≤
      Cdiag*(plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^ε+
      Ctail*(plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving):=by
  obtain ⟨Sdiag,Cdiag,hCdiag,hdiag⟩:=first_input_zero_capped hi wlo whi B ε hhi hwlo hwhi hB hε
  obtain ⟨Stail,Ctail,hCtail,htail⟩:=local_input_tail hi wlo whi B ξ saving hhi hwlo hwhi hB hξ
  refine ⟨Sdiag,Stail,Cdiag,Ctail,hCdiag,hCtail,?_⟩
  filter_upwards [htail] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A hml hm2 R seed Φ K hK hVcap hKi
  have hd:=hdiag Z hZ.1.le s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi hVcap m A R seed Φ K hK.le
  have ht:=hZ.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK hVcap hKi
  rw [CenteredMomentFirstSectorLocalization.finiteHeckeEnergy_sector_localized
    s.η m A s.t hml hm2 (finiteColumns (Fintype.piFinset s.pools))
    (coefficient s R seed) Φ K (volume s.toData) Z ξ hK]
  rw [show ∀a b c:ℂ,a+b+c-b=a+c by intros;ring]
  exact ((div_le_div_of_nonneg_right (norm_add_le _ _) (volume_pos s).le).trans_eq
    (add_div _ _ _)).trans (add_le_add hd ht)

end CenteredMomentSourceInputFirstRemainder

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentFirstAssembly
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentFirstColumns CenteredMomentMobiusRegroup CenteredMomentChildAssembly
open CenteredMomentGaussEnergy RayFourExpansion
local notation "O" => Eisenstein.O

def originalPhase (e r : O) (ρ : O → ℂ) (a b : O) : ℂ :=
  (idealRowHom e (Ideal.span {a})*star (idealRowHom e (Ideal.span {b}))*ρ e)*
    (idealRowHom (b*r) (Ideal.span {a})*star (idealRowHom (a*r) (Ideal.span {b}))*ρ (a*b))

theorem originalPhase_eq (e r a b : O) (ρ : O → ℂ)
    (hρ : ∀ x y,ρ (x*y)=ρ x*ρ y)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpa : lambda^2∣a-1)
    (hpb : lambda^2∣b-1) (hab : IsCoprime a b) :
    originalPhase e r ρ a b=firstExtension e r ρ a b :=
  first_phase_columns e r a b ρ hρ ha hb hpa hpb hab

theorem first_divisor_pair {α β : Type*} (L : Ideal O)
    (a : α → O) (b : β → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (hb : ∀ j,Supported (Ideal.span {b j}))
    (c : α → ℂ) (d : β → ℂ) (e r : O) (ρ : O → ℂ) (h : O)
    (i : α) (j : β) (K : ℂ) :
    (if L∣Ideal.span {a i} ∧ L∣Ideal.span {b j} then
      firstExtension e r ρ (a i) (b j)*(c i*star (d j))*
        (gaussRow (a i) (ha i) h*star (gaussRow (b j) (hb j) (-h)))*K else 0) =
    ρ e*∑ χ : RayCharacter,∑ ξ : RayCharacter,
      pairCoeff firstPhaseTable χ ξ*
        ((divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ i*gaussRow (a i) (ha i) h)*
          star (divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) (ξ⁻¹) j*
            gaussRow (b j) (hb j) (-h)))*K := by
  by_cases hi : L∣Ideal.span {a i}
  · by_cases hj : L∣Ideal.span {b j}
    · simp only [hi,hj,and_self,ite_true,divisorCoefficient,star_mul,rayCharacter_inverse_star]
      rw [firstExtension_separated e r (a i) (b j) ρ (ha i) (hb j)]
      simp only [Finset.mul_sum,Finset.sum_mul,star_mul,rayCharacter_inverse_star]
      apply Finset.sum_congr rfl
      intro χ hχ
      apply Finset.sum_congr rfl
      intro ξ hξ
      ring
    · simp only [hi,hj,and_false,ite_false,divisorCoefficient,ite_true,zero_mul,star_zero,
        mul_zero,Finset.sum_const_zero]
  · simp only [hi,false_and,ite_false,divisorCoefficient,zero_mul,mul_zero,Finset.sum_const_zero]

theorem finite_first_children {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → O) (b : β → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (hb : ∀ j,Supported (Ideal.span {b j}))
    (hpa : ∀ i,lambda^2∣a i-1)
    (hpb : ∀ j,lambda^2∣b j-1)
    (c : α → ℂ) (d : β → ℂ) (e r : O) (ρ : O → ℂ)
    (hρ : ∀ x y,ρ (x*y)=ρ x*ρ y) (h : O) (K : α → β → ℂ) :
    (∑ i∈S,∑ j∈T,(if IsCoprime (a i) (b j) then originalPhase e r ρ (a i) (b j) else 0)*
      (c i*star (d j))*(gaussRow (a i) (ha i) h*star (gaussRow (b j) (hb j) (-h)))*K i j) =
    ∑ L∈divisorPool T (fun j => Ideal.span {b j}),
      (UniqueFactorizationMonoid.moebius L:ℂ)*ρ e*
        ∑ χ : RayCharacter,∑ ξ : RayCharacter,
          pairCoeff firstPhaseTable χ ξ*∑ i∈S,∑ j∈T,
            ((divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ i*gaussRow (a i) (ha i) h)*
              star (divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) (ξ⁻¹) j*
                gaussRow (b j) (hb j) (-h)))*K i j := by
  have ht (i : α) (j : β) :
      (if IsCoprime (a i) (b j) then originalPhase e r ρ (a i) (b j) else 0)*
        (c i*star (d j))*(gaussRow (a i) (ha i) h*star (gaussRow (b j) (hb j) (-h)))*K i j =
      if IsCoprime (Ideal.span {a i}) (Ideal.span {b j}) then
        firstExtension e r ρ (a i) (b j)*(c i*star (d j))*
          (gaussRow (a i) (ha i) h*star (gaussRow (b j) (hb j) (-h)))*K i j else 0 := by
    rw [Ideal.isCoprime_span_singleton_iff]
    by_cases hc : IsCoprime (a i) (b j)
    · simp only [hc,ite_true,originalPhase_eq e r (a i) (b j) ρ hρ (ha i) (hb j) (hpa i) (hpb j) hc]
    · simp only [hc,ite_false,zero_mul]
  simp_rw [ht]
  rw [finite_pair_mobius S T (fun i => Ideal.span {a i}) (fun j => Ideal.span {b j})
    (fun j _ => (hb j).1)]
  apply Finset.sum_congr rfl
  intro L hL
  simp_rw [first_divisor_pair L a b ha hb c d e r ρ h]
  simp_rw [← Finset.mul_sum (s:=T),← Finset.mul_sum (s:=S)]
  rw [pair_ray_fubini]
  ring

theorem separated_first_gaussPolynomials {α β : Type*} (S : Finset α) (T : Finset β)
    (L : Ideal O) (a : α → O) (b : β → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (hb : ∀ j,Supported (Ideal.span {b j}))
    (c : α → ℂ) (d : β → ℂ) (e r : O) (ρ : O → ℂ) (χ ξ : RayCharacter)
    (f : α → ℂ) (g : β → ℂ) (h : O) :
    (∑ i∈S,∑ j∈T,
      ((divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ i*gaussRow (a i) (ha i) h)*
        star (divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) (ξ⁻¹) j*
          gaussRow (b j) (hb j) (-h)))*(f i*star (g j))) =
      gaussPolynomial S a ha (fun i => divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ i*f i) h*
        star (gaussPolynomial T b hb
          (fun j => divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) (ξ⁻¹) j*g j) (-h)) := by
  simp only [gaussPolynomial,star_sum,star_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end CenteredMomentFirstAssembly

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentFirstFrequency
open Eisenstein  CubicEisenstein CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentFirstNormalization CenteredMomentFirstReduced CenteredMomentFirstAssembly
open CenteredMomentFirstColumns CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
open CenteredMomentPrimitive CenteredMomentGaussEnergy CenteredMomentChildAssembly CenteredMomentMobiusRegroup
open RayFourExpansion
local notation "O" => Eisenstein.O

theorem normalized_dilated_frequency {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,lambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (e a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (har : IsCoprime a (b*finitePrimeModulus P)) (hbr : IsCoprime b (finitePrimeModulus P))
    (k : ℝ) (h : O) :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    let ρ := finiteSexticRow P hg j
    tripleRow a b r (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ G e*
      ((k/‖ringComplex (a*(b*r))‖^2:ℝ):ℂ)*
      tripleFourier a b r (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
        (finitePrimeModulus_ne_zero P) (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ G h =
      ((k:ℂ)*canonicalNormalizedGauss P hcop hg j/(‖ringComplex r‖:ℂ))*star (ρ h)*
        originalPhase e r ρ a b*
        ((gaussRow a ha h/(‖ringComplex a‖:ℂ))*star (gaussRow b hb (-h)/(‖ringComplex b‖:ℂ))) := by
  dsimp only
  let := finiteEisensteinQuotientOfNonzero (supported_element_ne_zero b hb)
  have he := normalized_active_coefficient P hcop hg hchar j hj0 hj6 a b ha hb har hbr h
  dsimp only at he
  rw [Complex.ofReal_div]
  calc
    _ = (k:ℂ)*tripleRow a b (finitePrimeModulus P) (supportedModulusCharacter a ha)
        (supportedModulusCharacter b hb)⁻¹
        (principalSexticRow P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P)) e*
        (tripleFourier a b (finitePrimeModulus P) (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
          (finitePrimeModulus_ne_zero P) (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹
          (principalSexticRow P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P)) h /
          (‖ringComplex (a*(b*finitePrimeModulus P))‖^2:ℝ)) := by ring
    _ = _ := by
      rw [he,tripleRow,← MulChar.star_apply',supportedModulusCharacter_mk,
        supportedModulusCharacter_mk,
        principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P) e]
      simp only [originalPhase,Complex.star_def,map_div₀,Complex.conj_ofReal]
      ring

def dilatedFrequency {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,lambda ∉ P i) (j : ι → ℕ)
    (e a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (k : ℝ) (h : O) : ℂ :=
  let r := finitePrimeModulus P
  let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
  tripleRow a b r (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ G e*
    ((k/‖ringComplex (a*(b*r))‖^2:ℝ):ℂ)*
    tripleFourier a b r (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
      (finitePrimeModulus_ne_zero P) (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ G h

theorem finite_dilated_children {ι α β : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,lambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (S : Finset α) (T : Finset β) (a : α → O) (b : β → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (hb : ∀ l,Supported (Ideal.span {b l}))
    (hpa : ∀ i,lambda^2∣a i-1)
    (hpb : ∀ l,lambda^2∣b l-1)
    (har : ∀ i,IsCoprime (a i) (finitePrimeModulus P))
    (hbr : ∀ l,IsCoprime (b l) (finitePrimeModulus P))
    (c : α → ℂ) (d : β → ℂ) (e : O) (k : ℝ) (h : O) (K : α → β → ℂ) :
    let r := finitePrimeModulus P
    let ρ := finiteSexticRow P hg j
    (∑ i∈S,∑ l∈T,
      (if IsCoprime (a i) (b l) then dilatedFrequency P hcop hg j e (a i) (b l) (ha i) (hb l) k h else 0)*
        (c i*star (d l))*K i l) =
      ((k:ℂ)*canonicalNormalizedGauss P hcop hg j/(‖ringComplex r‖:ℂ))*star (ρ h)*
        ∑ L∈divisorPool T (fun l => Ideal.span {b l}),
          (UniqueFactorizationMonoid.moebius L:ℂ)*ρ e*
            ∑ χ : RayCharacter,∑ ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*
              ∑ i∈S,∑ l∈T,
                ((divisorCoefficient L a (fun i => (c i/(‖ringComplex (a i)‖:ℂ))*leftCoefficient e r ρ (a i)) χ i*
                    gaussRow (a i) (ha i) h)*
                  star (divisorCoefficient L b (fun l => (d l/(‖ringComplex (b l)‖:ℂ))*rightCoefficient e r ρ (b l)) (ξ⁻¹) l*
                    gaussRow (b l) (hb l) (-h)))*K i l := by
  dsimp only
  let r := finitePrimeModulus P
  let ρ := finiteSexticRow P hg j
  let F := ((k:ℂ)*canonicalNormalizedGauss P hcop hg j/(‖ringComplex r‖:ℂ))*star (ρ h)
  have ht (i : α) (l : β) :
      (if IsCoprime (a i) (b l) then dilatedFrequency P hcop hg j e (a i) (b l) (ha i) (hb l) k h else 0)*
          (c i*star (d l))*K i l =
        F*((if IsCoprime (a i) (b l) then originalPhase e r ρ (a i) (b l) else 0)*
          ((c i/(‖ringComplex (a i)‖:ℂ))*star (d l/(‖ringComplex (b l)‖:ℂ)))*
          (gaussRow (a i) (ha i) h*star (gaussRow (b l) (hb l) (-h)))*K i l) := by
    by_cases hab : IsCoprime (a i) (b l)
    · simp only [hab,ite_true]
      rw [show dilatedFrequency P hcop hg j e (a i) (b l) (ha i) (hb l) k h=_ from
        normalized_dilated_frequency P hcop hg hchar j hj0 hj6 e (a i) (b l) (ha i) (hb l)
          (hab.mul_right (har i)) (hbr l) k h]
      dsimp only [F,r,ρ]
      simp only [Complex.star_def,map_div₀,Complex.conj_ofReal]
      ring
    · simp [hab]
  simp_rw [ht,← Finset.mul_sum]
  rw [finite_first_children S T a b ha hb hpa hpb
    (fun i => c i/(‖ringComplex (a i)‖:ℂ)) (fun l => d l/(‖ringComplex (b l)‖:ℂ)) e r ρ
    (finiteSexticRow_mul P hg j) h K]

end CenteredMomentFirstFrequency

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstCommonTransport
open Eisenstein  CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentActive
open CenteredMomentFirstSectorEnergy CompletedGauss
local notation "O"=> Eisenstein.O

theorem extracted_support (I J:Ideal O):
    commonSupport (commonPart I J) (commonPart J I)=commonSupport I J:=by
  rw [commonSupport,commonPart_support,commonPart_support,commonSupport_comm J I,Finset.inter_self]

def commonEquiv (I J:Ideal O):CommonIndex I J ≃ CommonIndex (commonPart I J) (commonPart J I) where
  toFun P:=⟨P.val,by rw [extracted_support];exact P.property⟩
  invFun P:=⟨P.val,by rw [←extracted_support I J];exact P.property⟩
  left_inv _:=rfl
  right_inv _:=rfl

@[simp] theorem commonEquiv_val (I J:Ideal O)(P:CommonIndex I J):
    (commonEquiv I J P).val=P.val:=rfl

@[simp] theorem extracted_left (I J:Ideal O)(P:CommonIndex I J):
    leftExponent (commonPart I J) (commonPart J I) (commonEquiv I J P)=leftExponent I J P:=by
  simp only [leftExponent,commonEquiv_val,commonPart_valuation,if_pos P.property]

@[simp] theorem extracted_right (I J:Ideal O)(P:CommonIndex I J):
    rightExponent (commonPart I J) (commonPart J I) (commonEquiv I J P)=rightExponent I J P:=by
  have hp:P.val∈commonSupport J I:=by rw [commonSupport_comm];exact P.property
  simp only [rightExponent,commonEquiv_val,commonPart_valuation,if_pos hp]

def activeEquiv (I J:Ideal O):ActiveIndex I J ≃ ActiveIndex (commonPart I J) (commonPart J I) where
  toFun P:=⟨commonEquiv I J P.val,by
    simpa only [ActiveIndex,CenteredMomentActive.activeSupport,Finset.mem_filter,Finset.mem_univ,true_and,extracted_left,extracted_right]
      using P.property⟩
  invFun P:=⟨(commonEquiv I J).symm P.val,by
    have hp:=P.property
    have he:(commonEquiv I J) ((commonEquiv I J).symm P.val)=P.val:=(commonEquiv I J).apply_symm_apply _
    rw [←he] at hp
    simpa only [ActiveIndex,CenteredMomentActive.activeSupport,Finset.mem_filter,Finset.mem_univ,true_and,extracted_left,extracted_right]
      using hp⟩
  left_inv P:=by apply Subtype.ext;exact (commonEquiv I J).symm_apply_apply _
  right_inv P:=by apply Subtype.ext;exact (commonEquiv I J).apply_symm_apply _

@[simp] theorem activeEquiv_prime (I J:Ideal O)(P:ActiveIndex I J):
    activePrime (commonPart I J) (commonPart J I) (activeEquiv I J P)=activePrime I J P:=rfl

@[simp] theorem activeEquiv_exponent (I J:Ideal O)(P:ActiveIndex I J):
    activeExponent (commonPart I J) (commonPart J I) (activeEquiv I J P)=activeExponent I J P:=by
  change netExponent (leftExponent _ _ (commonEquiv I J P.val))
    (rightExponent _ _ (commonEquiv I J P.val))=_
  rw [extracted_left,extracted_right]
  rfl

theorem activeConductor_extracted (I J:Ideal O):
    activeConductor (commonPart I J) (commonPart J I)=activeConductor I J:=by
  unfold activeConductor finitePrimeModulus
  congr 1
  exact (Fintype.prod_equiv (activeEquiv I J) _ _ (fun P=> by rw [activeEquiv_prime])).symm

theorem activeRow_extracted (I J:Ideal O)(hI:Supported I)(z:O):
    finiteSexticRow (activePrime (commonPart I J) (commonPart J I))
      (activeGood _ _ (commonPart_supported I J hI))
      (activeExponent (commonPart I J) (commonPart J I)) z=
    finiteSexticRow (activePrime I J) (activeGood I J hI) (activeExponent I J) z:=by
  unfold finiteSexticRow
  apply (Fintype.prod_equiv (activeEquiv I J) _ _ ?_).symm
  intro P
  rw [activeEquiv_exponent]
  rfl

theorem activeFunction_mk_extracted (I J:Ideal O)(hI:Supported I)(z:O):
    activeFunction (commonPart I J) (commonPart J I) (commonPart_supported I J hI)
      (Ideal.Quotient.mk _ z)=activeFunction I J hI (Ideal.Quotient.mk _ z):=by
  simp only [activeFunction]
  exact activeRow_extracted I J hI z

def mappedSubset (I J:Ideal O)(E:Finset (CommonIndex I J)):
    Finset (CommonIndex (commonPart I J) (commonPart J I)):=E.map (commonEquiv I J).toEmbedding

theorem mappedSubset_product (I J:Ideal O)(E:Finset (CommonIndex I J)):
    (∏P∈mappedSubset I J E,P.val)=∏P∈E,P.val:=by
  simp only [mappedSubset,Finset.prod_map,Equiv.toEmbedding_apply,commonEquiv_val]

theorem mappedSubset_generator (I J:Ideal O)(E:Finset (CommonIndex I J)):
    TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex (commonPart I J) (commonPart J I)=> P.val)
      (mappedSubset I J E)=TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex I J=> P.val) E:=by
  unfold TruncatedPrincipalPoisson.primeSubsetGenerator
  simp only [mappedSubset,Finset.prod_map,Equiv.toEmbedding_apply,commonEquiv_val]

theorem mappedSubset_inactive (I J:Ideal O)(E:Finset (CommonIndex I J)):
    mappedSubset I J E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets (commonPart I J) (commonPart J I) ↔
      E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets I J:=by
  simp only [CenteredMomentFirstDiscardedEnergy.inactiveSubsets,Finset.mem_powerset]
  constructor
  · intro h P hP
    have hp:=h (Finset.mem_map.mpr ⟨P,hP,rfl⟩)
    simpa only [Equiv.toEmbedding_apply,principalSupport,Finset.mem_filter,Finset.mem_univ,true_and,extracted_left,extracted_right]
      using hp
  · intro h P hP
    obtain ⟨R,hR,rfl⟩:=Finset.mem_map.mp hP
    have hr:=h hR
    simpa only [Equiv.toEmbedding_apply,principalSupport,Finset.mem_filter,Finset.mem_univ,true_and,extracted_left,extracted_right]
      using hr

theorem nominal_extracted (I J:Ideal O)(E:Finset (CommonIndex I J))(K X:ℝ):
    CenteredMomentFirstScale.firstNominalScale (commonPart I J) (commonPart J I)
      (∏P∈mappedSubset I J E,P.val) K X=
    CenteredMomentFirstScale.firstNominalScale I J (∏P∈E,P.val) K X:=by
  obtain ⟨hc,hd⟩:=fixed_common_parts (commonPart I J) (commonPart J I)
    (commonPart_ne_zero I J) (commonPart_ne_zero J I) (commonParts_equal_support I J)
  unfold CenteredMomentFirstScale.firstNominalScale
  rw [mappedSubset_product,activeConductor_extracted,hc,hd]

end CenteredMomentFirstCommonTransport

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstCommonFourierTransport
open Eisenstein   CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstReduced
open CenteredMomentSupportedCorrelation
open CenteredMomentCommonSupport CenteredMomentFirstLocalization CenteredMomentFirstScale
open CenteredMomentSectorLocalization CenteredMomentFirstCommonTransport
local notation "O"=> Eisenstein.O

theorem quotient_function_heq (r r':O)(hr:r'=r)
    (G:Residue r→ℂ)(G':Residue r'→ℂ)
    (hG:∀z:O,G' (Ideal.Quotient.mk _ z)=G (Ideal.Quotient.mk _ z)):
    HEq G' G:=by
  subst r'
  apply heq_of_eq
  funext x
  obtain ⟨z,rfl⟩:=Ideal.Quotient.mk_surjective x
  exact hG z

def retainedFourierTerm (a b r:O)(ha:a≠0)(hb:b≠0)(hr:r≠0)
    (χa:MulChar (Residue a) ℂ)(χb:MulChar (Residue b) ℂ)(G:Residue r→ℂ)
    (e:O)(E:Ideal O)(W:𝓢(ℝ,ℂ))(K R:ℝ):ℂ:=
  let k:=K/normValue e
  (UniqueFactorizationMonoid.moebius E:ℂ)*tripleRow a b r χa χb G e*
    (((k/normValue (a*(b*r)):ℝ):ℂ)*∑'h:O,
      (retainedWeight R (normValue h):ℂ)*tripleFourier a b r ha hb hr χa χb G h*
        SchwartzPlanePoisson.paperRadialFourier W ((k/normValue (a*(b*r)))*normValue h))

theorem retainedFourierTerm_transport (a b r r':O)(ha:a≠0)(hb:b≠0)(hr:r≠0)(hr':r'≠0)
    (χa:MulChar (Residue a) ℂ)(χb:MulChar (Residue b) ℂ)(G:Residue r→ℂ)(G':Residue r'→ℂ)
    (he:r'=r)(hG:∀z:O,G' (Ideal.Quotient.mk _ z)=G (Ideal.Quotient.mk _ z))
    (e:O)(E:Ideal O)(W:𝓢(ℝ,ℂ))(K R:ℝ):
    retainedFourierTerm a b r' ha hb hr' χa χb G' e E W K R=
      retainedFourierTerm a b r ha hb hr χa χb G e E W K R:=by
  subst r'
  have hg:G'=G:=eq_of_heq (quotient_function_heq r r rfl G G' hG)
  subst G'
  rfl

def fixedRetainedTerm (C D:Ideal O)(hC:Supported C)(a b:O)
    (ha:Supported (Ideal.span {a}))(hb:Supported (Ideal.span {b}))
    (E:Finset (CommonIndex C D))(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  retainedFourierTerm a b (activeConductor C D)
    (supported_element_ne_zero _ ha) (supported_element_ne_zero _ hb) (finitePrimeModulus_ne_zero _)
    (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ (activeFunction C D hC)
    (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E) (∏P∈E,P.val) W K
    (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ)

theorem canonicalRetainedTerm_fixed (I J:Ideal O)(hI:Supported I)(hJ:Supported J)
    (E:Finset (CommonIndex I J))(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    canonicalRetainedTerm I J hI hJ E W K
      (firstNominalScale I J (∏P∈E,P.val) K X) Z ξ=
    fixedRetainedTerm (commonPart I J) (commonPart J I) (commonPart_supported I J hI)
      (residualGenerator I J) (residualGenerator J I)
      (residualGenerator_supported I J hI) (residualGenerator_supported J I hJ)
      (mappedSubset I J E) W K X Z ξ:=by
  unfold fixedRetainedTerm
  rw [nominal_extracted,mappedSubset_generator,mappedSubset_product]
  have hh:=retainedFourierTerm_transport (residualGenerator I J) (residualGenerator J I)
    (activeConductor I J) (activeConductor (commonPart I J) (commonPart J I))
    (supported_element_ne_zero _ (residualGenerator_supported I J hI))
    (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
    (finitePrimeModulus_ne_zero _) (finitePrimeModulus_ne_zero _)
    (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹
    (activeFunction I J hI) (activeFunction (commonPart I J) (commonPart J I) (commonPart_supported I J hI))
    (activeConductor_extracted I J) (activeFunction_mk_extracted I J hI)
    (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex I J=> P.val) E) (∏P∈E,P.val) W K
    (frequencyRadius (firstNominalScale I J (∏P∈E,P.val) K X) Z ξ)
  exact hh.symm

def inactiveEquiv (I J:Ideal O):
    CenteredMomentFirstDiscardedEnergy.inactiveSubsets I J ≃
      CenteredMomentFirstDiscardedEnergy.inactiveSubsets (commonPart I J) (commonPart J I):=
  (Equiv.finsetCongr (commonEquiv I J)).subtypeEquiv (fun E=>(mappedSubset_inactive I J E).symm)

@[simp] theorem inactiveEquiv_val (I J:Ideal O)
    (E:CenteredMomentFirstDiscardedEnergy.inactiveSubsets I J):
    (inactiveEquiv I J E).val=mappedSubset I J E.val:=rfl

theorem canonicalRetainedPair_fixed (I J:Ideal O)(hI:Supported I)(hJ:Supported J)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    CenteredMomentFirstSectorLocalization.retainedPair I J hI hJ W K X Z ξ=
    ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets (commonPart I J) (commonPart J I),
      fixedRetainedTerm (commonPart I J) (commonPart J I) (commonPart_supported I J hI)
        (residualGenerator I J) (residualGenerator J I)
        (residualGenerator_supported I J hI) (residualGenerator_supported J I hJ) E W K X Z ξ:=by
  unfold CenteredMomentFirstSectorLocalization.retainedPair
  apply Finset.sum_bij (fun E _=> mappedSubset I J E)
  · intro E hE
    exact (mappedSubset_inactive I J E).mpr hE
  · intro E hE F hF he
    exact (Equiv.finsetCongr (commonEquiv I J)).injective he
  · intro F hF
    obtain ⟨E,he⟩:=(Equiv.finsetCongr (commonEquiv I J)).surjective F
    change mappedSubset I J E=F at he
    exact ⟨E,(mappedSubset_inactive I J E).mp (he.symm ▸ hF),he⟩
  · intro E hE
    exact canonicalRetainedTerm_fixed I J hI hJ E W K X Z ξ

end CenteredMomentFirstCommonFourierTransport

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentFirstRetainedSector
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSourceRow CenteredMomentFirstSectorLocalization CenteredMomentFirstCommonFourierTransport
open CenteredMomentHeckeExpansion CenteredMomentCommonSectors
open CenteredMomentFirstSectors CenteredMomentCompleteCommon CenteredMomentSecondSectorColumns
open CenteredMomentHeckeColumnWindow
open CenteredMomentSupport CenteredMomentSectorLocalization
local notation "O" => Eisenstein.O

def retainedKernel (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  if hI : Supported I then if hJ : Supported J then CenteredMomentFirstSectorLocalization.retainedPair I J hI hJ W K X Z ξ else 0 else 0

theorem retainedKernel_eq (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    retainedKernel I J W K X Z ξ=CenteredMomentFirstSectorLocalization.retainedPair I J hI hJ W K X Z ξ := by
  simp only [retainedKernel,dif_pos hI,dif_pos hJ]

theorem retainedEnergy_common_sectors (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    CenteredMomentFirstSectorLocalization.retainedEnergy η m A t S β W K X Z ξ=
      ∑ p∈commonLabels (supportedColumns S) (supportedColumns S),
        ∑ q∈pairSector p.1 p.2 (supportedColumns S) (supportedColumns S),
          ((β q.1*rowWeight η m A 1 t q.1)*star (β q.2*rowWeight η m A 1 t q.2))*
            retainedKernel q.1 q.2 W K X Z ξ := by
  let F := fun I J : Ideal O=>((β I*rowWeight η m A 1 t I)*star (β J*rowWeight η m A 1 t J))*
    retainedKernel I J W K X Z ξ
  have he : CenteredMomentFirstSectorLocalization.retainedEnergy η m A t S β W K X Z ξ=
      ∑ I : supportedColumns S,∑ J : supportedColumns S,F I J := by
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro J hJ
    dsimp only [F]
    rw [retainedKernel_eq I J (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2]
  rw [he]
  have hj (I : Ideal O) : (∑ J : supportedColumns S,F I J)=∑ J∈supportedColumns S,F I J :=
    Finset.sum_coe_sort _ _
  simp_rw [hj]
  rw [Finset.sum_coe_sort (supportedColumns S) (fun I=>∑ J∈supportedColumns S,F I J)]
  exact sum_common_sectors _ _ F

theorem retained_sector_independent (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : CubicEisenstein.primeSupport C=CubicEisenstein.primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((β q.1*rowWeight η m A 1 t q.1)*star (β q.2*rowWeight η m A 1 t q.2))*
        retainedKernel q.1 q.2 W K X Z ξ)=
      rowWeight η m A 1 t C*star (rowWeight η m A 1 t D)*
        ∑ I : sectorPool C hC S,∑ J : sectorPool D hD S,
          if IsCoprime (I:Ideal O) (J:Ideal O) then
            ((β (C*I)*rowWeight η m A 1 t I)*star (β (D*J)*rowWeight η m A 1 t J))*
              retainedKernel (C*I) (D*J) W K X Z ξ else 0 := by
  rw [←independent_sector_pools C D hC hD hCD S
    (fun I J=>((β (C*I)*rowWeight η m A 1 t I)*star (β (D*J)*rowWeight η m A 1 t J))*
      retainedKernel (C*I) (D*J) W K X Z ξ)]
  rw [pairSector_double_sum C D hC hD hCD _ _
    (fun I hI=>(Finset.mem_filter.mp hI).2.1) (fun I hI=>(Finset.mem_filter.mp hI).2.1)
    (fun I J=>((β I*rowWeight η m A 1 t I)*star (β J*rowWeight η m A 1 t J))*
      retainedKernel I J W K X Z ξ)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  split_ifs <;> simp only [map_mul,star_mul,mul_zero]
  ring

theorem reconstructed_residualParts (C D I J:Ideal O)(hC:C≠0)(hD:D≠0)(hI:I≠0)(hJ:J≠0)
    (hCD:CubicEisenstein.primeSupport C=CubicEisenstein.primeSupport D)
    (hCI:IsCoprime C I)(hCJ:IsCoprime C J)(hIJ:IsCoprime I J):
    residualPart (C*I) (D*J)=I ∧ residualPart (D*J) (C*I)=J:=by
  obtain ⟨hc,hd⟩:=reconstructed_commonParts C D I J hC hD hI hJ hCD hCI hCJ hIJ
  constructor
  · have hh:=reconstruct (C*I) (D*J) (mul_ne_zero hC hI)
    rw [hc] at hh
    exact (mul_left_cancel₀ hC hh).symm
  · have hh:=reconstruct (D*J) (C*I) (mul_ne_zero hD hJ)
    rw [hd] at hh
    exact (mul_left_cancel₀ hD hh).symm

theorem canonicalRetainedPair_of_common (I J C D:Ideal O)(hI:Supported I)(hJ:Supported J)
    (hC:Supported C)(hc:commonPart I J=C)(hd:commonPart J I=D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    CenteredMomentFirstSectorLocalization.retainedPair I J hI hJ W K X Z ξ=
      ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
        fixedRetainedTerm C D hC (CenteredMomentCanonicalFirst.residualGenerator I J)
          (CenteredMomentCanonicalFirst.residualGenerator J I)
          (CenteredMomentCanonicalFirst.residualGenerator_supported I J hI)
          (CenteredMomentCanonicalFirst.residualGenerator_supported J I hJ) E W K X Z ξ:=by
  subst C
  subst D
  exact canonicalRetainedPair_fixed I J hI hJ W K X Z ξ

theorem retainedKernel_fixed (C D I J:Ideal O)(hC:Supported C)(hD:Supported D)
    (hI:Supported I)(hJ:Supported J)
    (hCD:CubicEisenstein.primeSupport C=CubicEisenstein.primeSupport D)
    (hCI:IsCoprime C I)(hCJ:IsCoprime C J)(hIJ:IsCoprime I J)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    retainedKernel (C*I) (D*J) W K X Z ξ=
      ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
        fixedRetainedTerm C D hC (primaryIdealGenerator I) (primaryIdealGenerator J)
          (by rw [primary_span_supported I hI];exact hI)
          (by rw [primary_span_supported J hJ];exact hJ) E W K X Z ξ:=by
  have hCI':Supported (C*I):=(supported_mul_iff C I).mpr ⟨hC,hI⟩
  have hDJ':Supported (D*J):=(supported_mul_iff D J).mpr ⟨hD,hJ⟩
  rw [retainedKernel_eq _ _ hCI' hDJ']
  obtain ⟨hc,hd⟩:=reconstructed_commonParts C D I J hC.1 hD.1 hI.1 hJ.1 hCD hCI hCJ hIJ
  obtain ⟨hi,hj⟩:=reconstructed_residualParts C D I J hC.1 hD.1 hI.1 hJ.1 hCD hCI hCJ hIJ
  have hh:=canonicalRetainedPair_of_common (C*I) (D*J) C D hCI' hDJ' hC hc hd W K X Z ξ
  simpa only [CenteredMomentCanonicalFirst.residualGenerator,hi,hj] using hh

end CenteredMomentFirstRetainedSector

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstPhysicalSource
open Eisenstein  
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentSourceRow CenteredMomentRowNorm
open CenteredMomentFirstSectors CenteredMomentFirstSectorEnergy CenteredMomentFirstSectorTransform
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCompleteCommon
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentActive
open CenteredMomentFirstReduced CenteredMomentFirstFrequency CenteredMomentFirstWholeKernel
open CenteredMomentFirstColumns CenteredMomentFirstAssembly CenteredMomentGaussEnergy
open CenteredMomentSmooth CenteredMomentScale CenteredMomentPrimitive 
local notation "O"=> Eisenstein.O

def columns (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O)):Finset (Ideal O):=
  (residualPool D hD (supportedColumns S)).filter (fun I=> IsCoprime C I)

lemma column_supported (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))
    (a:columns C D hD S):Supported (a:Ideal O):=
  residualPool_supported D hD S ⟨a.val,(Finset.mem_filter.mp a.property).1⟩

def element (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):O:=
  primaryIdealGenerator a

lemma element_span (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):
    Ideal.span {element C D hD S a}=a:=primary_span_supported a (column_supported C D hD S a)

lemma element_supported (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):
    Supported (Ideal.span {element C D hD S a}):=by
  rw [element_span];exact column_supported C D hD S a

lemma element_primary (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):
    lambda^2∣element C D hD S a-1:=
  (primaryIdealGenerator_spec a (supported_primaryIdealGenerator_ne_zero a
    (column_supported C D hD S a))).2

lemma active_span_dvd (C D:Ideal O)(hC:C≠0)(hD:D≠0)
    (hCD:primeSupport C=primeSupport D):Ideal.span {activeConductor C D}∣C:=by
  have hh:=activeConductor_span_dvd C D
  rw [(fixed_common_parts C D hC hD hCD).1] at hh
  exact hh

lemma element_coprime_active (C D B:Ideal O)(hC:C≠0)(hD:D≠0)(hB:B≠0)
    (hCD:primeSupport C=primeSupport D)(S:Finset (Ideal O))(a:columns C B hB S):
    IsCoprime (element C B hB S a) (activeConductor C D):=by
  rw [←Ideal.isCoprime_span_singleton_iff,element_span]
  exact (Finset.mem_filter.mp a.property).2.symm.of_isCoprime_of_dvd_right (active_span_dvd C D hC hD hCD)

def coefficient (η:Character)(m A:O)(t:ℝ)(c:Ideal O→ℂ)(D:Ideal O)
    (I:Ideal O):ℂ:=c (D*I)*CenteredMomentHeckeExpansion.rowWeight η m A 1 t I

def inactiveWeight (C D:Ideal O)(E:Finset (CommonIndex C D)):ℂ:=
  (UniqueFactorizationMonoid.moebius (∏P∈E,P.val):ℂ)

def block (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K K₀ H₀ A₀ B₀:ℝ):ℂ:=
  let e:=TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E
  let k:=K/‖ringComplex e‖^2
  let r:=activeConductor C D
  inactiveWeight C D E * ∑h∈rows,
    ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      let na:=element C C hC.1 S a
      let nb:=element C D hD.1 S b
      if IsCoprime (a:Ideal O) (b:Ideal O) then
        (tripleRow na nb r (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) e *
        ((k/‖ringComplex (na*(nb*r))‖^2:ℝ):ℂ)*
        tripleFourier na nb r
          (supported_element_ne_zero _ (element_supported C C hC.1 S a))
          (supported_element_ne_zero _ (element_supported C D hD.1 S b))
          (finitePrimeModulus_ne_zero _) (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) h)*
        (coefficient η m A t c C a*star (coefficient η m A t c D b))*
        windows V (k/‖ringComplex r‖^2) (‖ringComplex h‖^2)
          (‖ringComplex na‖^2) (‖ringComplex nb‖^2) K₀ H₀ A₀ B₀*
        SchwartzPlanePoisson.paperRadialFourier W (k*‖ringComplex h‖^2/‖ringComplex (na*(nb*r))‖^2)
      else 0


end CenteredMomentFirstPhysicalSource
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstPhysicalSource
open Eisenstein  HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentFirstSectorEnergy
open CenteredMomentFirstSectorTransform
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCommonSupport
open CenteredMomentFirstColumns CenteredMomentChildAssembly CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeExpansion RayFourExpansion
local notation "O"=> Eisenstein.O

theorem original_pool_restriction (C D:Ideal O)(hC:C≠0)(hD:D≠0)
    (S:Finset (Ideal O))(f:Ideal O→Ideal O→ℂ):
    (∑a∈residualPool C hC (supportedColumns S),∑b∈residualPool D hD (supportedColumns S),
      if IsCoprime C a ∧ IsCoprime C b ∧ IsCoprime a b then f a b else 0)=
    ∑a:columns C C hC S,∑b:columns C D hD S,
      if IsCoprime (a:Ideal O) (b:Ideal O) then f a b else 0:=by
  rw [Finset.sum_coe_sort (columns C C hC S)
    (fun a:Ideal O=>∑b:columns C D hD S,if IsCoprime a (b:Ideal O) then f a b else 0)]
  unfold columns
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hca:IsCoprime C a
  · simp only [hca,true_and,ite_true]
    rw [Finset.sum_coe_sort _ (fun b:Ideal O=> if IsCoprime a b then f a b else 0),Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hcb:IsCoprime C b <;> simp [hcb]
  · simp [hca]


end CenteredMomentFirstPhysicalSource
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentFirstWholeKernel
open Eisenstein  CanonicalQuadraticSieve SchwartzPlanePoisson
open CenteredMomentFirstFrequency CenteredMomentFirstColumns CenteredMomentGaussEnergy CenteredMomentFirstAssembly
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentPrimitive CenteredMomentScale CenteredMomentSmooth CenteredMomentFirstReduced
local notation "O" => Eisenstein.O

theorem dilated_frequency_whole_kernel {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,lambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (e a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (har : IsCoprime a (b*finitePrimeModulus P)) (hbr : IsCoprime b (finitePrimeModulus P))
    (k : ℝ) (hk : 0< k) (h : O) (hh : h≠0)
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) (K₀ H₀ A₀ B₀ : ℝ)
    (hK₀ : 0< K₀) (hH₀ : 0< H₀) (hA₀ : 0< A₀) (hB₀ : 0< B₀) :
    let r := finitePrimeModulus P
    let ρ := finiteSexticRow P hg j
    let kr := k/‖ringComplex r‖^2
    dilatedFrequency P hcop hg j e a b ha hb k h *
      windows V kr (‖ringComplex h‖^2) (‖ringComplex a‖^2) (‖ringComplex b‖^2) K₀ H₀ A₀ B₀ *
      paperRadialFourier W (k*‖ringComplex h‖^2/‖ringComplex (a*(b*r))‖^2)=
      ((k:ℂ)*canonicalNormalizedGauss P hcop hg j/
        ((‖ringComplex r‖:ℂ)*(Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ)))*
        star (ρ h)*originalPhase e r ρ a b *
        (gaussRow a ha h*star (gaussRow b hb (-h)))*
        wholeKernel W V (K₀*H₀/(A₀*B₀))
          (Real.log (kr/K₀)) (Real.log (‖ringComplex h‖^2/H₀))
          (Real.log (‖ringComplex a‖^2/A₀)) (Real.log (‖ringComplex b‖^2/B₀)) := by
  dsimp only
  have haN : 0<‖ringComplex a‖ := norm_pos_iff.mpr (ringComplex_ne_zero (supported_element_ne_zero a ha))
  have hbN : 0<‖ringComplex b‖ := norm_pos_iff.mpr (ringComplex_ne_zero (supported_element_ne_zero b hb))
  have hrN : 0<‖ringComplex (finitePrimeModulus P)‖ :=
    norm_pos_iff.mpr (ringComplex_ne_zero (finitePrimeModulus_ne_zero P))
  have hhN : 0<‖ringComplex h‖ := norm_pos_iff.mpr (ringComplex_ne_zero hh)
  have hk' : 0< k/‖ringComplex (finitePrimeModulus P)‖^2 := div_pos hk (sq_pos_of_pos hrN)
  rw [show dilatedFrequency P hcop hg j e a b ha hb k h=_ from
    normalized_dilated_frequency P hcop hg hchar j hj0 hj6 e a b ha hb har hbr k h]
  rw [wholeKernel_actual W V _ _ _ _ K₀ H₀ A₀ B₀ hk' (sq_pos_of_pos hhN)
    (sq_pos_of_pos haN) (sq_pos_of_pos hbN) hK₀ hH₀ hA₀ hB₀]
  have harg : k*‖ringComplex h‖^2/‖ringComplex (a*(b*finitePrimeModulus P))‖^2=
      (k/‖ringComplex (finitePrimeModulus P)‖^2)*‖ringComplex h‖^2/
        (‖ringComplex a‖^2*‖ringComplex b‖^2) := by
    simp only [map_mul,norm_mul]
    ring
  rw [harg]
  simp only [windows,Real.sqrt_sq haN.le,Real.sqrt_sq hbN.le,
    Complex.star_def,map_div₀,Complex.conj_ofReal]
  have hA : (Real.sqrt A₀:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hA₀).ne'
  have hB : (Real.sqrt B₀:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hB₀).ne'
  have hr : (‖ringComplex (finitePrimeModulus P)‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hrN.ne'
  have ha' : (‖ringComplex a‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr haN.ne'
  have hb' : (‖ringComplex b‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hbN.ne'
  have alg (c r a b A B x y u v : ℂ) (hr : r≠0) (ha : a≠0) (hb : b≠0)
      (hA : A≠0) (hB : B≠0) :
      (c/r*x*(u/a*(v/b)))*y=c/(r*A*B)*x*(u*v)*((A*B/(a*b))*y) := by
    field_simp
  convert alg ((k:ℂ)*canonicalNormalizedGauss P hcop hg j)
    (‖ringComplex (finitePrimeModulus P)‖:ℂ) (‖ringComplex a‖:ℂ) (‖ringComplex b‖:ℂ)
    (Real.sqrt A₀:ℂ) (Real.sqrt B₀:ℂ)
    (star (finiteSexticRow P hg j h)*originalPhase e (finitePrimeModulus P) (finiteSexticRow P hg j) a b)
    (windows V (k/‖ringComplex (finitePrimeModulus P)‖^2) (‖ringComplex h‖^2)
      (‖ringComplex a‖^2) (‖ringComplex b‖^2) K₀ H₀ A₀ B₀*
      paperRadialFourier W ((k/‖ringComplex (finitePrimeModulus P)‖^2)*‖ringComplex h‖^2/
        (‖ringComplex a‖^2*‖ringComplex b‖^2)))
    (gaussRow a ha h) (star (gaussRow b hb (-h))) hr ha' hb' hA hB using 1 <;>
    simp only [windows,Complex.star_def] <;> ring

end CenteredMomentFirstWholeKernel

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstPhysicalSource
open Eisenstein  
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentSourceRow CenteredMomentRowNorm
open CenteredMomentFirstSectors CenteredMomentFirstSectorEnergy CenteredMomentFirstSectorTransform
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCompleteCommon
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentActive
open CenteredMomentFirstReduced CenteredMomentFirstFrequency CenteredMomentFirstWholeKernel
open CenteredMomentFirstColumns CenteredMomentFirstAssembly CenteredMomentGaussEnergy
open CenteredMomentSmooth CenteredMomentScale CenteredMomentPrimitive 
local notation "O"=> Eisenstein.O

def scalar (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))(K A₀ B₀:ℝ):ℂ:=
  let e:=TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E
  let k:=K/‖ringComplex e‖^2
  inactiveWeight C D E * ((k:ℂ)*canonicalNormalizedGauss (activePrime C D)
    (activeCoprime C D) (activeGood C D hC) (activeExponent C D)/
      ((‖ringComplex (activeConductor C D)‖:ℂ)*(Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ)))

theorem block_eq_whole (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(rows:Finset O)(hrows:∀h∈rows,h≠0)
    (W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K K₀ H₀ A₀ B₀:ℝ)
    (hK:0< K)(hK₀:0< K₀)(hH₀:0< H₀)(hA₀:0< A₀)(hB₀:0< B₀):
    let e:=TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E
    let k:=K/‖ringComplex e‖^2
    let r:=activeConductor C D
    let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
    block η m A t S c C D hC hD E rows W V K K₀ H₀ A₀ B₀=
      scalar C D hC E K A₀ B₀ * ∑h∈rows,star (ρ h)*
        ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
          ((if IsCoprime (element C C hC.1 S a) (element C D hD.1 S b) then
            originalPhase e r ρ (element C C hC.1 S a) (element C D hD.1 S b) else 0)*
            (coefficient η m A t c C a*star (coefficient η m A t c D b)))*
          (gaussRow _ (element_supported C C hC.1 S a) h*
            star (gaussRow _ (element_supported C D hD.1 S b) (-h)))*
          wholeKernel W V (K₀*H₀/(A₀*B₀))
            (Real.log ((k/‖ringComplex r‖^2)/K₀)) (Real.log (‖ringComplex h‖^2/H₀))
            (Real.log (‖ringComplex (element C C hC.1 S a)‖^2/A₀))
            (Real.log (‖ringComplex (element C D hD.1 S b)‖^2/B₀)):=by
  dsimp only
  have he:TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E≠0:=
    supported_element_ne_zero _ (subsetGenerator_supported C D hC E)
  have hk:0< K/‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)‖^2:=
    div_pos hK (sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero he)))
  unfold block scalar
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hcop:IsCoprime (element C C hC.1 S a) (element C D hD.1 S b)↔
      IsCoprime (a:Ideal O) (b:Ideal O):=by
    rw [←Ideal.isCoprime_span_singleton_iff,element_span,element_span]
  by_cases hab:IsCoprime (a:Ideal O) (b:Ideal O)
  · simp only [hab,ite_true,hcop]
    have hh:=dilated_frequency_whole_kernel (activePrime C D) (activeCoprime C D)
      (activeGood C D hC) (fun P=> common_odd C D hC P.val) (activeExponent C D)
      (netExponent_ne_zero _ _ _) (fun P=> netExponent_lt_six _ _)
      (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)
      (element C C hC.1 S a) (element C D hD.1 S b)
      (element_supported C C hC.1 S a) (element_supported C D hD.1 S b)
      ((hcop.mpr hab).mul_right (element_coprime_active C D C hC.1 hD.1 hC.1 hCD S a))
      (element_coprime_active C D D hC.1 hD.1 hD.1 hCD S b)
      _ hk h (hrows h hh) W V K₀ H₀ A₀ B₀ hK₀ hH₀ hA₀ hB₀
    dsimp only at hh
    change inactiveWeight C D E * (_*_*_*_)=_
    calc
      _=inactiveWeight C D E*(coefficient η m A t c C a*star (coefficient η m A t c D b))*
        (dilatedFrequency (activePrime C D) (activeCoprime C D) (activeGood C D hC)
          (activeExponent C D) (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)
          (element C C hC.1 S a) (element C D hD.1 S b)
          (element_supported C C hC.1 S a) (element_supported C D hD.1 S b)
          (K/‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)‖^2) h *
        windows V _ _ _ _ K₀ H₀ A₀ B₀ * SchwartzPlanePoisson.paperRadialFourier W _):=by
          dsimp [dilatedFrequency,activeFunction,activeConductor];ring
      _=_:=by rw [hh];dsimp only [activeConductor];ring
  · simp [hab,hcop]

end CenteredMomentFirstPhysicalSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstPhysicalSource
open Eisenstein  HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentFirstSectorEnergy
open CenteredMomentFirstSectorTransform CenteredMomentFirstChildProfile
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCommonSupport
open CenteredMomentFirstColumns CenteredMomentChildAssembly CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeExpansion RayFourExpansion
local notation "O"=> Eisenstein.O

theorem actual_child_family (η:Character)(m:O)(hm:m≠0)
    (hmLam:lambda∣m)(hm2:(2:O)∣m)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (ξ₁ ξ₂:RayCharacter):
    let e:=TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E;
    let r:=activeConductor C D;
    let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D);
    let M:=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*r};
    ∃τ₁ τ₂:Character,τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀S:Finset (Ideal O),∀c:Ideal O→ℂ,∀t:ℝ,∀L:Ideal O,∀a:columns C C hC.1 S,
        divisorCoefficient L (element C C hC.1 S)
          (fun a=> coefficient η m 1 t c C a*leftCoefficient e r ρ (element C C hC.1 S a)) ξ₁ a=
          (if L∣(a:Ideal O) then c (C*a) else 0)*heightCoeff τ₁ t a) ∧
      (∀S:Finset (Ideal O),∀c:Ideal O→ℂ,∀t:ℝ,∀L:Ideal O,∀b:columns C D hD.1 S,
        divisorCoefficient L (element C D hD.1 S)
          (fun b=> coefficient η m 1 t c D b*rightCoefficient e r ρ (element C D hD.1 S b)) ξ₂ b=
          (if L∣(b:Ideal O) then c (D*b) else 0)*heightCoeff τ₂ t b):=by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩:=exists_first_divisor_pair η m hm hmLam hm2 C D hC E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,?_,?_⟩
  · intro S c t L a
    exact h₁ L a (column_supported C C hC.1 S a) (fun I=> c (C*I)) t
  · intro S c t L b
    exact h₂ L b (column_supported C D hD.1 S b) (fun I=> c (D*I)) t

end CenteredMomentFirstPhysicalSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstPhysicalDyadicAssembly
open Eisenstein  
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst
open CenteredMomentFirstReduced CenteredMomentFirstColumns CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentRowNorm
open CenteredMomentFirstWholeKernel CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentDyadicCount CenteredMomentPrimitive
local notation "O"=> Eisenstein.O

def retainedBlock (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(K R:ℝ):ℂ:=
  let e:=TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E
  let k:=K/‖ringComplex e‖^2
  let r:=activeConductor C D
  inactiveWeight C D E * ∑h∈rows,
    ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      let na:=element C C hC.1 S a
      let nb:=element C D hD.1 S b
      if IsCoprime (a:Ideal O) (b:Ideal O) then
        (tripleRow na nb r (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) e *
        ((k/‖ringComplex (na*(nb*r))‖^2:ℝ):ℂ)*
        tripleFourier na nb r
          (supported_element_ne_zero _ (element_supported C C hC.1 S a))
          (supported_element_ne_zero _ (element_supported C D hD.1 S b))
          (finitePrimeModulus_ne_zero _) (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) h)*
        (coefficient η m A t c C a*star (coefficient η m A t c D b))*
        (retainedWeight R (‖ringComplex h‖^2):ℂ)*
        SchwartzPlanePoisson.paperRadialFourier W (k*‖ringComplex h‖^2/‖ringComplex (na*(nb*r))‖^2)
      else 0

def retainedIndices (R:ℝ):Finset ℤ := (finite_retained_integral_dyads R).toFinset

lemma mem_retainedIndices (R:ℝ)(n:ℤ):
    n∈retainedIndices R↔Retained R n ∧ ∃q:ℝ,1≤ q ∧ dyadicWeight n q≠0 :=
  (finite_retained_integral_dyads R).mem_toFinset

lemma retained_partition (R q:ℝ)(hq:1≤ q):
    (∑n∈retainedIndices R,dyadicWeight n q)=retainedWeight R q :=by
  unfold retainedWeight
  rw [tsum_eq_sum (s:=retainedIndices R) (fun n hn=> by
    split_ifs with hr
    · by_contra hh
      exact hn ((mem_retainedIndices R n).mpr ⟨hr,q,hq,hh⟩)
    · rfl)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [if_pos ((mem_retainedIndices R n).mp hn).1]

def bands (K R A B:ℝ):Fin 4→Finset ℤ :=
  ![indices K K,retainedIndices R,indices 1 A,indices 1 B]

abbrev Blocks (K R A B:ℝ):=∀i:Fin 4,↥(bands K R A B i)

lemma product_partition (K R A B h a b:ℝ)(hK:0< K)(hh:1≤ h)
    (ha:a∈Set.Icc (1:ℝ) A)(hb:b∈Set.Icc (1:ℝ) B):
    (∑n:Blocks K R A B,∏i:Fin 4,dyadicWeight (n i) (![K,h,a,b] i))=
      retainedWeight R h :=by
  have he (i:Fin 4):
      (∑n:bands K R A B i,dyadicWeight n (![K,h,a,b] i))=
        (if i=1 then retainedWeight R h else 1):=by
    fin_cases i
    · change (∑n:indices K K,dyadicWeight n K)=1
      rw [Finset.sum_coe_sort (indices K K) (fun n:ℤ=> dyadicWeight n K)]
      exact dyadic_partition_on_interval K K K hK ⟨le_rfl,le_rfl⟩
    · change (∑n:retainedIndices R,dyadicWeight n h)=retainedWeight R h
      rw [Finset.sum_coe_sort (retainedIndices R) (fun n:ℤ=> dyadicWeight n h)]
      exact retained_partition R h hh
    · change (∑n:indices 1 A,dyadicWeight n a)=1
      rw [Finset.sum_coe_sort (indices 1 A) (fun n:ℤ=> dyadicWeight n a)]
      exact dyadic_partition_on_interval 1 A a (by norm_num) ha
    · change (∑n:indices 1 B,dyadicWeight n b)=1
      rw [Finset.sum_coe_sort (indices 1 B) (fun n:ℤ=> dyadicWeight n b)]
      exact dyadic_partition_on_interval 1 B b (by norm_num) hb
  rw [←Fintype.prod_sum (fun (i:Fin 4)(n:bands K R A B i)=>
    dyadicWeight n (![K,h,a,b] i))]
  simp_rw [he]
  norm_num [Fin.prod_univ_four]

lemma windows_partition (K R A B h a b:ℝ)(hK:0< K)(hh:1≤ h)
    (ha:a∈Set.Icc (1:ℝ) A)(hb:b∈Set.Icc (1:ℝ) B):
    (∑n:Blocks K R A B, windows (fun _=> logAnnulus) K h a b
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)))=
      (retainedWeight R h:ℂ):=by
  calc
    _ = ∑n:Blocks K R A B,((∏i:Fin 4,dyadicWeight (n i) (![K,h,a,b] i):ℝ):ℂ):=by
      apply Finset.sum_congr rfl
      intro n hn
      simpa [Fin.prod_univ_four] using
        (actual_product_windows K h a b hK (zero_lt_one.trans_le hh)
          (zero_lt_one.trans_le ha.1) (zero_lt_one.trans_le hb.1) (fun i=> n i)).symm
    _ = _ :=by
      rw [←Complex.ofReal_sum,product_partition K R A B h a b hK hh ha hb]

def effectiveScale (C D:Ideal O)(E:Finset (CommonIndex C D))(K:ℝ):ℝ:=
  (K/‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)‖^2)/
    ‖ringComplex (activeConductor C D)‖^2

lemma effectiveScale_pos (C D:Ideal O)(E:Finset (CommonIndex C D))(K:ℝ)(hK:0< K):
    0< effectiveScale C D E K:=by
  unfold effectiveScale
  apply div_pos (div_pos hK ?_) ?_
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero (TruncatedPrincipalPoisson.primeSubsetGenerator_ne_zero _ _)))
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero (finitePrimeModulus_ne_zero _)))

lemma element_norm (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):
    ‖ringComplex (element C D hD S a)‖^2=((a:Ideal O).absNorm:ℝ):=by
  rw [ringComplex_norm_sq_eq_absNorm_span,element_span]

lemma element_norm_ge_one (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):
    1≤‖ringComplex (element C D hD S a)‖^2:=by
  rw [element_norm]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (column_supported C D hD S a).1)

lemma element_norm_le (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S)
    (c:Ideal O→ℂ)(H:ℝ)(hcap:∀I,c I≠0→(I.absNorm:ℝ)≤ H)(ha:c (D*a)≠0):
    ‖ringComplex (element C D hD S a)‖^2≤ H/(D.absNorm:ℝ):=by
  have hDpos:(0:ℝ)< D.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  rw [element_norm]
  apply (le_div_iff₀ hDpos).mpr
  simpa only [map_mul,Nat.cast_mul,mul_comm] using hcap (D*a) ha

theorem retainedBlock_eq_blocks
    (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(hrows:∀h∈rows,h≠0)(W:𝓢(ℝ,ℂ))(K R H:ℝ)(hK:0< K)
    (hcap:∀I,c I≠0→(I.absNorm:ℝ)≤ H):
    retainedBlock η m A t S c C D hC hD E rows W K R=
      ∑n:Blocks (effectiveScale C D E K) R (H/(C.absNorm:ℝ)) (H/(D.absNorm:ℝ)),
        block η m A t S c C D hC hD E rows W (fun _=> logAnnulus) K
          (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)):=by
  unfold retainedBlock block
  dsimp only
  rw [←Finset.mul_sum]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab:IsCoprime (a:Ideal O) (b:Ideal O)
  · simp only [hab,ite_true]
    by_cases hca:c (C*(a:Ideal O))=0
    · simp [coefficient,hca]
    by_cases hcb:c (D*(b:Ideal O))=0
    · simp [coefficient,hcb]
    have hnorm:1≤‖ringComplex h‖^2:=by
      rw [ringComplex_norm_sq_eq_absNorm_span]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr (hrows h hh)))
    have hpart:=windows_partition (effectiveScale C D E K) R
      (H/(C.absNorm:ℝ)) (H/(D.absNorm:ℝ)) (‖ringComplex h‖^2)
      (‖ringComplex (element C C hC.1 S a)‖^2) (‖ringComplex (element C D hD.1 S b)‖^2)
      (effectiveScale_pos C D E K hK) hnorm
      ⟨element_norm_ge_one C C hC.1 S a,element_norm_le C C hC.1 S a c H hcap hca⟩
      ⟨element_norm_ge_one C D hD.1 S b,element_norm_le C D hD.1 S b c H hcap hcb⟩
    rw [←Finset.sum_mul,←Finset.mul_sum]
    congr 1
    congr 1
    exact hpart.symm
  · simp [hab]

lemma block_retained (K R A B:ℝ)(n:Blocks K R A B):Retained R (n 1):=
  ((mem_retainedIndices R (n 1)).mp (n 1).property).1

def retainedInfiniteBlock (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (W:𝓢(ℝ,ℂ))(K R:ℝ):ℂ:=
  let e:=TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E
  let k:=K/‖ringComplex e‖^2
  let r:=activeConductor C D
  inactiveWeight C D E * ∑'h:O,
    ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      let na:=element C C hC.1 S a
      let nb:=element C D hD.1 S b
      if IsCoprime (a:Ideal O) (b:Ideal O) then
        (tripleRow na nb r (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) e *
        ((k/‖ringComplex (na*(nb*r))‖^2:ℝ):ℂ)*
        tripleFourier na nb r
          (supported_element_ne_zero _ (element_supported C C hC.1 S a))
          (supported_element_ne_zero _ (element_supported C D hD.1 S b))
          (finitePrimeModulus_ne_zero _) (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) h)*
        (coefficient η m A t c C a*star (coefficient η m A t c D b))*
        (retainedWeight R (‖ringComplex h‖^2):ℂ)*
        SchwartzPlanePoisson.paperRadialFourier W (k*‖ringComplex h‖^2/‖ringComplex (na*(nb*r))‖^2)
      else 0

lemma retained_rows_nonzero (R:ℝ):
    ∀h∈CenteredMomentSecondRetainedRows.retainedRows R 1,h≠0:=by
  intro h hh hz
  have hn:=((TruncatedPrincipalPoisson.mem_rowNormDisk _ _).mp hh).1
  subst h
  simp at hn

theorem retainedInfiniteBlock_eq_finite
    (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (W:𝓢(ℝ,ℂ))(K R:ℝ):
    retainedInfiniteBlock η m A t S c C D hC hD E W K R=
      retainedBlock η m A t S c C D hC hD E
        (CenteredMomentSecondRetainedRows.retainedRows R 1) W K R:=by
  unfold retainedInfiniteBlock retainedBlock
  dsimp only
  congr 1
  apply tsum_eq_sum
  intro h hh
  have hz:retainedWeight R (‖ringComplex h‖^2)=0:=by
    by_contra hn
    apply hh
    apply CenteredMomentSecondRetainedRows.retained_mem_rows R 1 h one_ne_zero
    simpa only [one_mul,normValue_eq_embedding] using hn
  simp only [hz,Complex.ofReal_zero,mul_zero,zero_mul,ite_self,Finset.sum_const_zero]

theorem original_retained_dyadic
    {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (W:𝓢(ℝ,ℂ))(K R:ℝ)(hK:0< K):
    retainedInfiniteBlock s.η m A t S
      (CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed) C D hC hD E W K R=
      ∑n:Blocks (effectiveScale C D E K) R
          (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(C.absNorm:ℝ))
          (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)),
        block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed)
          C D hC hD E (CenteredMomentSecondRetainedRows.retainedRows R 1) W
          (fun _=> logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
            (dyadicScale (n 2)) (dyadicScale (n 3)):=by
  rw [retainedInfiniteBlock_eq_finite]
  exact retainedBlock_eq_blocks s.η m A t S _ C D hC hD E _
    (retained_rows_nonzero R) W K R _ hK
    (fun I hI=>(CenteredMomentOriginalCommonHarmonic.original_column_norm s Rbad seed I hz₁ hz₂ hI).2)

end CenteredMomentFirstPhysicalDyadicAssembly

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstRetainedPhysical
open Eisenstein  HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentFirstSectors CenteredMomentFirstSectorTransform CenteredMomentSourceRow
open CenteredMomentFirstRetainedSector CenteredMomentFirstCommonFourierTransport
open CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSupportedCorrelation CenteredMomentHeckeExpansion CenteredMomentCompleteCommon
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentFirstReduced
local notation "O"=> Eisenstein.O

 theorem original_sector_columns (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:C≠0)(hD:D≠0)(hCD:primeSupport C=primeSupport D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    (∑q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((c q.1*rowWeight η m A 1 t q.1)*star (c q.2*rowWeight η m A 1 t q.2))*
        retainedKernel q.1 q.2 W K X Z ξ)=
    rowWeight η m A 1 t C*star (rowWeight η m A 1 t D)*
      ∑a:columns C C hC S,∑b:columns C D hD S,
        if IsCoprime (a:Ideal O) (b:Ideal O) then
          (coefficient η m A t c C a*star (coefficient η m A t c D b))*
            retainedKernel (C*a) (D*b) W K X Z ξ else 0:=by
  rw [←original_pool_restriction C D hC hD S
    (fun a b=>(coefficient η m A t c C a*star (coefficient η m A t c D b))*
      retainedKernel (C*a) (D*b) W K X Z ξ)]
  rw [pairSector_double_sum C D hC hD hCD _ _
    (fun I hI=>(Finset.mem_filter.mp hI).2.1) (fun I hI=>(Finset.mem_filter.mp hI).2.1)
    (fun I J=>((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      retainedKernel I J W K X Z ξ)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp only [coefficient,map_mul,star_mul,mul_zero]
  ring

def fixedRetainedSector (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      if IsCoprime (a:Ideal O) (b:Ideal O) then
        (coefficient η m A t c C a*star (coefficient η m A t c D b))*
          fixedRetainedTerm C D hC (element C C hC.1 S a) (element C D hD.1 S b)
            (element_supported C C hC.1 S a) (element_supported C D hD.1 S b) E W K X Z ξ
      else 0

theorem original_sector_fixed (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    (∑q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((c q.1*rowWeight η m A 1 t q.1)*star (c q.2*rowWeight η m A 1 t q.2))*
        retainedKernel q.1 q.2 W K X Z ξ)=
    rowWeight η m A 1 t C*star (rowWeight η m A 1 t D)*
      fixedRetainedSector η m A t S c C D hC hD W K X Z ξ:=by
  rw [original_sector_columns η m A t S c C D hC.1 hD.1 hCD W K X Z ξ]
  congr 1
  let F:=fun (a:columns C C hC.1 S) (b:columns C D hD.1 S) (E:Finset (CommonIndex C D))=>
    if IsCoprime (a:Ideal O) (b:Ideal O) then
      (coefficient η m A t c C a*star (coefficient η m A t c D b))*
        fixedRetainedTerm C D hC (element C C hC.1 S a) (element C D hD.1 S b)
          (element_supported C C hC.1 S a) (element_supported C D hD.1 S b) E W K X Z ξ
    else 0
  calc
    _=∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,F a b E:=by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hab:IsCoprime (a:Ideal O) (b:Ideal O)
      · simp only [F,hab,ite_true]
        rw [retainedKernel_fixed C D a b hC hD (column_supported C C hC.1 S a)
          (column_supported C D hD.1 S b) hCD (Finset.mem_filter.mp a.property).2
          (Finset.mem_filter.mp b.property).2 hab W K X Z ξ,Finset.mul_sum]
        rfl
      · simp only [F,hab,ite_false,Finset.sum_const_zero]
    _=∑a:columns C C hC.1 S,∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
      ∑b:columns C D hD.1 S,F a b E:=by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _=fixedRetainedSector η m A t S c C D hC hD W K X Z ξ:=Finset.sum_comm

end CenteredMomentFirstRetainedPhysical

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstRetainedBlock
open Eisenstein   HeckeFamily CompletedGauss CanonicalQuadraticSieve
open CenteredMomentFirstRetainedPhysical CenteredMomentFirstCommonFourierTransport
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentRowNorm
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation CenteredMomentSectorLocalization CenteredMomentFirstScale
local notation "O"=> Eisenstein.O

lemma retained_tsum (R:ℝ)(f:O→ℂ):
    (∑'h:O,(retainedWeight R (normValue h):ℂ)*f h)=
      ∑h∈CenteredMomentSecondRetainedRows.retainedRows R 1,
        (retainedWeight R (normValue h):ℂ)*f h:=by
  apply tsum_eq_sum
  intro h hh
  have hz:retainedWeight R (normValue h)=0:=by
    by_contra hn
    apply hh
    apply CenteredMomentSecondRetainedRows.retained_mem_rows R 1 h one_ne_zero
    simpa only [one_mul] using hn
  simp only [hz,Complex.ofReal_zero,zero_mul]

lemma retainedFourierTerm_finite (a b r:O)(ha:a≠0)(hb:b≠0)(hr:r≠0)
    (χa:MulChar (Residue a) ℂ)(χb:MulChar (Residue b) ℂ)(G:Residue r→ℂ)
    (e:O)(E:Ideal O)(W:𝓢(ℝ,ℂ))(K R:ℝ):
    retainedFourierTerm a b r ha hb hr χa χb G e E W K R=
      (UniqueFactorizationMonoid.moebius E:ℂ)*
      ∑h∈CenteredMomentSecondRetainedRows.retainedRows R 1,
        (tripleRow a b r χa χb G e *
          (((K/normValue e)/normValue (a*(b*r)):ℝ):ℂ)*
          tripleFourier a b r ha hb hr χa χb G h)*
        (retainedWeight R (normValue h):ℂ)*
        SchwartzPlanePoisson.paperRadialFourier W
          ((K/normValue e)*normValue h/normValue (a*(b*r))):=by
  unfold retainedFourierTerm
  dsimp only
  simp_rw [mul_assoc (retainedWeight R (normValue _):ℂ)]
  rw [retained_tsum]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [show (K/normValue e)/normValue (a*(b*r))*normValue h=
    (K/normValue e)*normValue h/normValue (a*(b*r)) by ring]
  ring

lemma finite_pair_row_sum {α β:Type*}[Fintype α][Fintype β]
    (rows:Finset O)(p:α→β→Prop)[DecidableRel p]
    (c:α→β→ℂ)(μ:ℂ)(f:α→β→O→ℂ):
    (∑a:α,∑b:β,if p a b then c a b*(μ*∑h∈rows,f a b h) else 0)=
      μ*∑h∈rows,∑a:α,∑b:β,if p a b then c a b*f a b h else 0:=by
  have hp (a:α)(b:β):
      (if p a b then c a b*(μ*∑h∈rows,f a b h) else 0)=
        ∑h∈rows,μ*(if p a b then c a b*f a b h else 0):=by
    by_cases hab:p a b
    · simp only [hab,ite_true,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      ring
    · simp [hab]
  simp_rw [hp,Finset.mul_sum]
  calc
    _=∑a:α,∑h∈rows,∑b:β,μ*(if p a b then c a b*f a b h else 0):=by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _=_:=Finset.sum_comm

theorem fixed_sector_term_block
    (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    (∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      if IsCoprime (a:Ideal O) (b:Ideal O) then
        (coefficient η m A t c C a*star (coefficient η m A t c D b))*
          fixedRetainedTerm C D hC (element C C hC.1 S a) (element C D hD.1 S b)
            (element_supported C C hC.1 S a) (element_supported C D hD.1 S b) E W K X Z ξ
      else 0)=
    retainedInfiniteBlock η m A t S c C D hC hD E W K
      (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ):=by
  unfold fixedRetainedTerm
  generalize_proofs
  simp_rw [retainedFourierTerm_finite]
  rw [finite_pair_row_sum]
  rw [retainedInfiniteBlock_eq_finite]
  unfold retainedBlock inactiveWeight
  dsimp only
  simp only [normValue_eq_embedding]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> ring

theorem fixed_sector_blocks
    (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    fixedRetainedSector η m A t S c C D hC hD W K X Z ξ=
      ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
        retainedInfiniteBlock η m A t S c C D hC hD E W K
          (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ):=by
  unfold fixedRetainedSector
  apply Finset.sum_congr rfl
  intro E hE
  exact fixed_sector_term_block η m A t S c C D hC hD E W K X Z ξ

end CenteredMomentFirstRetainedBlock

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstRetainedAssembly
open Eisenstein  HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstRetainedPhysical CenteredMomentFirstRetainedSector
open CenteredMomentFirstRetainedBlock CenteredMomentFirstSectorTransform CenteredMomentFirstSectors
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSourceRow CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentRowNorm
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation CenteredMomentHeckeExpansion
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentLogDyadic
local notation "O"=> Eisenstein.O

def infiniteSector (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    retainedInfiniteBlock η m A t S c C D hC hD E W K
      (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ)

theorem retained_energy_blocks (η:Character)(m A:O)(t:ℝ)
    (S:Finset (Ideal O))(c:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    CenteredMomentFirstSectorLocalization.retainedEnergy η m A t S c W K X Z ξ=
      ∑p:commonLabels (supportedColumns S) (supportedColumns S),
        rowWeight η m A 1 t p.val.1*star (rowWeight η m A 1 t p.val.2)*
          infiniteSector η m A t S c p.val.1 p.val.2
            (commonLabels_supported S p).1 (commonLabels_supported S p).2 W K X Z ξ:=by
  rw [retainedEnergy_common_sectors]
  rw [←Finset.sum_coe_sort _ (fun p:Ideal O×Ideal O=>
    ∑q∈pairSector p.1 p.2 (supportedColumns S) (supportedColumns S),
      ((c q.1*rowWeight η m A 1 t q.1)*star (c q.2*rowWeight η m A 1 t q.2))*
        retainedKernel q.1 q.2 W K X Z ξ)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [original_sector_fixed η m A t S c p.val.1 p.val.2
    (commonLabels_supported S p).1 (commonLabels_supported S p).2
    (commonLabels_data _ _ p.val.1 p.val.2 p.property).2.2 W K X Z ξ]
  exact congrArg (fun z=> rowWeight η m A 1 t p.val.1*star (rowWeight η m A 1 t p.val.2)*z)
    (fixed_sector_blocks η m A t S c p.val.1 p.val.2
      (commonLabels_supported S p).1 (commonLabels_supported S p).2 W K X Z ξ)

def physicalSector {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    let R:=frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ
    ∑n:Blocks (effectiveScale C D E K) R
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(C.absNorm:ℝ))
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)),
      block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed)
        C D hC hD E (CenteredMomentSecondRetainedRows.retainedRows R 1) W
        (fun _=> logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3))

theorem original_retained_physical
    {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ)(hK:0< K):
    CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A t S
      (CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed) W K X Z ξ=
      ∑p:commonLabels (supportedColumns S) (supportedColumns S),
        rowWeight s.η m A 1 t p.val.1*star (rowWeight s.η m A 1 t p.val.2)*
          physicalSector s Rbad seed m A t S p.val.1 p.val.2
            (commonLabels_supported S p).1 (commonLabels_supported S p).2 W K X Z ξ:=by
  rw [retained_energy_blocks]
  apply Finset.sum_congr rfl
  intro p hp
  apply congrArg
  unfold infiniteSector physicalSector
  apply Finset.sum_congr rfl
  intro E hE
  exact original_retained_dyadic s Rbad seed hz₁ hz₂ m A t S p.val.1 p.val.2
    (commonLabels_supported S p).1 (commonLabels_supported S p).2 E W K _ hK

end CenteredMomentFirstRetainedAssembly

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstRetainedActive
open Eisenstein HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstRetainedSector CenteredMomentSourceRow CenteredMomentHeckeExpansion
open CenteredMomentFirstSectors CenteredMomentSupportedCorrelation
open CenteredMomentActiveSource (activeSource supportedColumns_active)
local notation "O"=> Eisenstein.O

 theorem retained_energy_sum (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))
    (β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    CenteredMomentFirstSectorLocalization.retainedEnergy η m A t S β W K X Z ξ=
      ∑I∈supportedColumns S,∑J∈supportedColumns S,
        ((β I*rowWeight η m A 1 t I)*star (β J*rowWeight η m A 1 t J))*
          CenteredMomentFirstRetainedSector.retainedKernel I J W K X Z ξ:=by
  unfold CenteredMomentFirstSectorLocalization.retainedEnergy
  conv_rhs=> rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro I hI
  conv_rhs=> rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [retainedKernel_eq I J (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2]

 theorem retained_energy_active (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))
    (β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    CenteredMomentFirstSectorLocalization.retainedEnergy η m A t (activeSource S β) β W K X Z ξ=
      CenteredMomentFirstSectorLocalization.retainedEnergy η m A t S β W K X Z ξ:=by
  rw [retained_energy_sum,retained_energy_sum,supportedColumns_active]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hi:β I=0
  · simp [hi]
  · rw [if_pos hi]
    apply Finset.sum_congr rfl
    intro J hJ
    by_cases hj:β J=0 <;> simp [hj]

end CenteredMomentFirstRetainedActive

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstRetainedNorm
open Eisenstein  HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstRetainedAssembly CenteredMomentFirstRetainedActive
open CenteredMomentFirstSectorTransform CenteredMomentFirstSectors CenteredMomentHeckeExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSourceRow CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentRowNorm
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentLogDyadic
open CenteredMomentActiveSource (activeSource)
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def sector (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    let R:=frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ
    ∑n:Blocks (effectiveScale C D E K) R
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(C.absNorm:ℝ))
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)),
      block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed)
        C D hC hD E (CenteredMomentSecondRetainedRows.retainedRows R 1) W
        (fun _=> logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3))

def sectorMass (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℝ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    let R:=frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ
    ∑n:Blocks (effectiveScale C D E K) R
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(C.absNorm:ℝ))
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)),
      ‖block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed)
        C D hC hD E (CenteredMomentSecondRetainedRows.retainedRows R 1) W
        (fun _=> logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3))‖

omit [DecidableEq ι] in
theorem sector_norm (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    ‖sector s Rbad seed m A t S C D hC hD W K X Z ξ‖≤
      sectorMass s Rbad seed m A t S C D hC hD W K X Z ξ:=by
  unfold sector sectorMass
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro E hE
  exact norm_sum_le _ _

theorem original_active_sectors (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)(m A:O)(t:ℝ)(S:Finset (Ideal O))
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ)(hK:0< K):
    let β:=CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed
    let T:=activeSource S β
    CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A t S β W K X Z ξ=
      ∑p:commonLabels (supportedColumns T) (supportedColumns T),
        rowWeight s.η m A 1 t p.val.1*star (rowWeight s.η m A 1 t p.val.2)*
        sector s Rbad seed m A t T p.val.1 p.val.2
          (commonLabels_supported T p).1 (commonLabels_supported T p).2 W K X Z ξ:=by
  dsimp only
  rw [←retained_energy_active s.η m A t S _ W K X Z ξ]
  exact original_retained_physical s Rbad seed hz₁ hz₂ m A t _ W K X Z ξ hK

theorem original_retained_norm (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)(m A:O)(t:ℝ)(S:Finset (Ideal O))
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ)(hK:0< K):
    let β:=CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed
    let T:=activeSource S β
    ‖CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A t S β W K X Z ξ‖≤
      ∑p:commonLabels (supportedColumns T) (supportedColumns T),
        sectorMass s Rbad seed m A t T p.val.1 p.val.2
          (commonLabels_supported T p).1 (commonLabels_supported T p).2 W K X Z ξ:=by
  dsimp only
  rw [original_active_sectors s Rbad seed hz₁ hz₂ m A t S W K X Z ξ hK]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro p hp
  rw [norm_mul]
  have hw:‖rowWeight s.η m A 1 t p.val.1*star (rowWeight s.η m A 1 t p.val.2)‖≤1:=by
    rw [norm_mul,norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (CenteredMomentAbsoluteEnergy.rowWeight_norm_le_one_all _ _ _ _ _ _)).trans
      (CenteredMomentAbsoluteEnergy.rowWeight_norm_le_one_all _ _ _ _ _ _)
  exact (mul_le_of_le_one_left (norm_nonneg _) hw).trans (sector_norm s Rbad seed m A t _ _ _ _ _ W K X Z ξ)

end CenteredMomentFirstRetainedNorm

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

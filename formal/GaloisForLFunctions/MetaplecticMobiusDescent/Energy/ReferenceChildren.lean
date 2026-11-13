/-
Reference children adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Energy.PositiveHighSources

/-!
# Reference children

Independent profiles and unpunctured states of reference children, divisor norms and reference
profile budgets; weighted deletion energies and low reflected children.
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

namespace CenteredMomentEnergyPositiveHighPhysical
open HeckeFamily  InversePrincipalEnergy
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
open CenteredMomentEnergyPositiveHighSource CenteredMomentEnergyPositiveHighSourceBound
open CenteredMomentEnergyPositiveHighParameters CenteredMomentEnergyPositiveBalancedAdmission
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyStageMargins CenteredMomentEnergyFirstSourceParameters
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyNaturalInputMatches
local notation "O"=> Eisenstein.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem actual_positive_high_physical
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(aslot bslot lo hi a b bΦ:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤ bslot)(ha:0< a)(hb:0≤ b)
    (Mglobal A B Bmask Mparent Mchild Lgoal Lslot rho κ ε:ℝ)(k:ℕ)
    (hMg:0≤ Mglobal)(hA:0≤ A)(hB:0≤ B)(hBm:0≤ Bmask)
    (_hMp:0≤ Mparent)(hMc:0≤ Mchild)(hL:0≤ Lgoal)(hLs:0≤ Lslot)
    (hMA:Mparent≤ A)(hready:readyBudget A Bmask≤ B)
    (hκ:(3/4:ℝ)≤κ)(hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤κ)(hε:0<ε)
    (hslot:Lslot≤ mesh Mglobal B κ ε)
    (hdrop:Mparent-amplification ε/2≤ Mchild)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤ Ideal.span {(72:O)}→
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
    ∀εchild C₀ C₁:ℝ,εchild≤ stageLoss Mglobal B ε k→0≤ C₀→0≤ C₁→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 (max Lgoal Mparent)
        Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 (max Lgoal Mparent)
        Lslot lo hi Mchild εchild κ Z η₀ Q degree S C₁→
      PhysicalHighAt (α:=α) M H hH W hW.continuous aslot bslot lo hi haslot hWs
        a b bΦ Bmask Lgoal Lslot rho Mparent κ (reserve Mglobal B ε/4)
        (physicalLoss Mglobal B ε k) Z ha Ψ η₀ Q U J (C*(C₀+C₁+1)) := by
  let r:=reserve Mglobal B ε
  let N:=Fintype.card α
  let Mslot:=profileBound W hW.continuous aslot bslot lo hi haslot hWs
  let a0:=CenteredMomentSecondInputCapacitySource.lowerFactor N aslot a
  let lp:=(min 1 aslot)^N*a*a
  have hMslot:1≤ Mslot:=profileBound_ge_one W hW.continuous aslot bslot lo hi haslot hWs
  have ha0:0< a0:=CenteredMomentSecondInputCapacitySource.lowerFactor_pos N aslot a haslot ha
  have hlp:0< lp:=by dsimp [lp];positivity
  obtain ⟨hsigma,hsigma1,hr,hxi,hxi1,hes,hes1,hem,hmesh,hmesheta,heta,hetastrict,_,_⟩:=
    parameter_gates Mglobal A B κ ε hMg hA hB hκ hε
  have hrpos:0< r/4:=hr
  have hκsmall:(1/6:ℝ)≤κ:=by linarith
  have hLphys:0≤ max Lgoal Mparent:=hL.trans (le_max_left _ _)
  obtain ⟨U,J,hphysical⟩:=CenteredMomentEnergyCanonicalHighPhysical.actual_high_physical (α:=α)
    M H hH W aslot bslot Mchild Lslot (r/4) lo hi κ a b Mslot (maskEpsilon Mglobal B ε)
    (zero_le_one.trans hMslot) hem ha hb (max Lgoal Mparent) hLphys degree S haslot hWs hW hMc hLs hr
    hκsmall hbeta hκbeta N aslot (max 1 bslot) a0 (r/4) haslot (le_max_left _ _) ha0 hr
    (fun _=> aslot) (fun _=> bslot) (fun _=> hbslot)
    (sourceEpsilon Mglobal A B ε) (r/4) (r/4) (A+1) (r/4) (2*amplification ε+1)
    hes hr hr hr (amplification ε) hsigma hxi A Bmask (amplification ε/12) (r/4) (r/4)
    hA hBm hetastrict hr hsigma1 hxi1 hr hes1 le_rfl Ψ (r/4) lp hr hlp
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,Z₀,hZ₀,hbound⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop Z₀,
    eventually_actual_four_fit Mglobal A Bmask B κ ε hMg hA hBm hB hready hκ hε,
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (by linarith : 0<2*(r/4)))) (max 1 b*max 1 b)]
    with Z hZZ hfit hclipPow
  have hZ:1< Z:=hZ₀.trans_le hZZ
  have hclip:Real.logb Z (max 1 b*max 1 b)≤2*(r/4):=by
    have hh:=Real.logb_le_logb_of_le hZ (by positivity:0< max 1 b*max 1 b) hclipPow
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  refine ⟨hZ,?_⟩
  intro εchild C₀ C₁ hell hC₀ hC₁ hzero hpos
    T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hrho hstate
    p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity hlarge
  dsimp only
  intro hfour
  let inp:=balancedInput M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂
  have hN:Fintype.card T≤ N:=Fintype.card_le_of_injective (fun i:T=> i.val) Subtype.val_injective
  have hm:=balanced_matches M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂
  have hu:=four_upper_scales M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ κ (max Lgoal Mparent)
    hZ hw hκ hcapacity (hstate.trans (le_max_right _ _))
  have hp:=fixed_lower_product M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ N hN
  have hr:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission state
  have hwidth:=actual_width_le state hZ
  have hh:=hbound T θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height (mesh Mglobal B κ ε)
    hmesh.le hw (fun i=>(hwL i).trans hslot)
    (fun i=>((hwL i).trans hslot).trans hmesheta) hwL hσlo hσhi hheight hfreq
    inp hm (fun _=> le_rfl) (fun _=> le_rfl) (fun _=> rfl) (fun _=> rfl) hN le_rfl (le_max_right _ _)
    hb hb (le_max_right _ _) (le_max_right _ _) hp.2 state.puncture 1 state.puncture_ne_zero
    state.puncture_bound (by simp) (by simp) state.radial.scale hr.1 p rfl rfl
    hu.1 hu.2.1 hu.2.2.1 hu.2.2.2 state.width state.width (r/4) (columnLoss Mglobal B ε k)
    hrpos.le (hstate.trans hMA) hcapacity hwidth hwidth (by linarith only [hstate,hdrop])
    hclip le_rfl le_rfl hfour.1 hfour.2.1 hfour.2.2.1 hfour.2.2.2 (hfit.2 k εchild hell)
  have hcost:state.width+columnLoss Mglobal B ε k+r/4=state.width+physicalLoss Mglobal B ε k:=by
    rw [add_assoc]
    exact congrArg (state.width+·) (columnLoss_physical Mglobal B ε k)
  rw [hcost] at hh
  have ht:inp.t=t:=rfl
  rw [ht] at hh
  dsimp only [inp,r] at hh
  have hN1:((1:Ideal O).absNorm:ℝ)=1:=by norm_num
  simpa only [hN1,div_one,mul_assoc] using hh

end CenteredMomentEnergyPositiveHighPhysical

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace CenteredMomentEnergyReferenceReflection
open HeckeFamily HeckeDyadic  InversePrincipalEnergy
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentUniformReflectionProfile CenteredExceptionalProfile CenteredMomentLattice
local notation "O"=> Eisenstein.O

lemma conductorFactor_pos : 0<(fixedConductorFactor:ℝ):=by
  unfold fixedConductorFactor
  norm_cast
  apply Nat.mul_pos
  · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr CenteredMomentSecondHeightFamily.fixedBadMask_ne_zero))
  · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0)))

theorem natural_reference_reflection (a b bΦ epsilon xi saving L:ℝ)
    (ha:0< a)(hb:0≤ b)(hbΦ:0< bΦ)(hepsilon:0< epsilon)(hxi:0< xi)
    (B J:ℕ)(hB:2≤ B):
    ∃n:ℕ,∃S:Finset (ℕ×ℕ),∃C D:ℝ,0< C ∧ 0< D ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Bmask:ℝ)(s:NaturalState Z Bmask bΦ)
        (Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(α:Type*)(F:Finset α)(pool:α→Finset (Ideal O))
        (β:α→Ideal O→ℂ)(P:α→ℝ)(t along bshort E:ℝ),
      s.width≤ L+along → 0≤ E →
      (∀v:ℝ,∀j k:Fin 2,∀x∈Set.Icc 0 (max 0 (s.width-along+xi)*Real.log Z),
        radialEnergy (fun z=> polynomial (naturalCharacter s.character z) false
          (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (naturalCharacter s.character z) false (scaleTest Wshort k)
            (Z^bshort) 0 t *
          ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
          (effectiveState s).radial.keep s.radial.profile s.radial.scale
          ≤ E*(1+‖v‖)^(2*J)) →
      radialEnergy (fun z=> polynomial (naturalCharacter s.character z) false Wlong
          (Z^along) 0 t *
          polynomial (naturalCharacter s.character z) false Wshort (Z^bshort) 0 t *
          ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
          (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (1+S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*(1+‖t‖)^(2*n)*
          (1+2*(max 0 (s.width-along+xi)*Real.log Z))*E +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (1+S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*(1+‖t‖)^(2*n)*Z^(-2*saving)*
          radialEnergy (fun z=> polynomial (naturalCharacter s.character z) false Wshort
            (Z^bshort) 0 t *
            ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
            (effectiveState s).radial.keep s.radial.profile s.radial.scale:=by
  obtain ⟨H,C,D,hC,hD,h⟩:=CenteredMomentUniformRadialComparison.actual_original_radial_comparison
    epsilon ((fixedConductorFactor:ℝ)*bΦ) xi saving L hepsilon
    (mul_pos conductorFactor_pos hbΦ) hxi B J hB
  obtain ⟨n,S,Ct,hCt,hprofile⟩:=
    CenteredMomentFiniteProfileExceptional.normPowerProfile_source_control a b ha H
  refine ⟨n,S,C*Ct^2,D*Ct^2,by positivity,by positivity,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask s Wlong Wshort hsLong hsShort α F pool β P t along bshort E hlength hE hchildren
  let G:=normPowerProfile Wlong a b ha hsLong (Wlong.smooth ⊤) t
  let Src:=Ct*(1+S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)*(1+‖t‖)^n
  have hSrc:0< Src:=by dsimp [Src];positivity
  have hnorm:H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G≤ Src:=by
    apply (hprofile Wlong hsLong t).trans
    dsimp [Src]
    gcongr
    linarith
  obtain ⟨Pbound,hPbound,hbound⟩:=CenteredMomentCommonMaskRadialEnergy.slots_bounded F pool β P
  have hh:=hZ.2 (fun _=> G) (naturalCharacter s.character)
    (fun z=>∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
    (fun _=> t) (effectiveState s).radial.keep s.radial.profile s.radial.scale Pbound
    Wshort a b s.width along bshort E Src
    (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))
    s.radial.scale_pos s.radial.nonneg (fun z=> hbound _)
    (effective_character_nonprincipal s) hb hsShort (Wshort.smooth ⊤)
    hlength (effective_character_cap s hbΦ.le) hE hSrc (fun _ _=> hnorm)
    (le_max_left _ _) (fun z hz=>(effective_character_cap s hbΦ.le z hz).trans (le_max_right _ _))
    hchildren
  have hG:(G:ℝ→ℂ)=normPowerProfile Wlong a b ha hsLong (Wlong.smooth ⊤) t:=rfl
  simp only [hG,CenteredMomentNaturalMaskedFloor.twist_polynomial _ Wlong a b ha hsLong t] at hh
  apply hh.trans_eq
  dsimp only [Src]
  rw [show (1+‖t‖)^(2*n)=((1+‖t‖)^n)^2 by rw [Nat.mul_comm 2 n,pow_mul]]
  ring

end CenteredMomentEnergyReferenceReflection

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentEnergyReferenceChild
open HeckeFamily HeckeDyadic  
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalRowSource
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergySlotHeight
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentInductionEnergy
open CenteredMomentEnergyProfiles CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondHeightFamily CenteredMomentLattice CenteredMomentRetainedProfile CenteredMomentTwist
local notation "O"=> Eisenstein.O

def unpuncturedState {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ):NaturalState Z 0 bΦ where
  character:=s.character
  fixedModulus:=s.fixedModulus
  puncture:=1
  radial:=(effectiveState s).radial
  rowWidth:=s.rowWidth
  characterWidth:=s.characterWidth
  base_ge_one:=s.base_ge_one
  row_nonneg:=s.row_nonneg
  character_nonneg:=s.character_nonneg
  scale_eq:=s.scale_eq
  modulus_bound:=s.modulus_bound
  puncture_ne_zero:=one_ne_zero
  puncture_bound:=by simp
  radial_support:=s.radial_support
  row_ne_zero:=fun z hz=> s.row_ne_zero z hz.1
  nonexceptional:=by
    intro z hz hh
    have hn:=s.row_ne_zero z hz.1
    have hunit:CenteredExceptionalProfile.FixedInducingRow s.character s.fixedModulus fixedBadMask 1 z:=
      (CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff s.character s.fixedModulus
        fixedBadMask (cubicIdealGenerator 1) 1 z fixedBadMask_ne_zero
        (cubicIdealGenerator_ne_zero 1 one_ne_zero) one_ne_zero hn
        (dvd_mul_right _ _) (dvd_mul_left _ _)).mp hh
    exact s.nonexceptional z hz.1
      ((CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff s.character s.fixedModulus
        fixedBadMask (cubicIdealGenerator s.puncture) 1 z fixedBadMask_ne_zero
        (cubicIdealGenerator_ne_zero _ s.puncture_ne_zero) one_ne_zero hn
        (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr hunit)

lemma unpunctured_width {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ):
    (unpuncturedState s).width=s.width:=rfl

def independentProfiles {a b:ℝ}(ha:0< a)(W₁ W₂:𝓢(ℝ,ℂ))
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)(t₁ t₂:ℝ):Profiles a b where
  profile:=fun i=> if i=0 then normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁
    else normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂
  support:=by
    intro i
    split_ifs
    · exact (normPowerProfile_support W₁ a b ha hs₁ (W₁.smooth ⊤) t₁).trans hs₁
    · exact (normPowerProfile_support W₂ a b ha hs₂ (W₂.smooth ⊤) t₂).trans hs₂

theorem independent_child_energy {α:Type*}[Fintype α][DecidableEq α]
    {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(ha:0< a)
    (W₁ W₂:𝓢(ℝ,ℂ))(hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (F:Finset α)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t₁ t₂ X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)(hP:∀i∈F,0< P i):
    radialEnergy (fun z=> polynomial (naturalCharacter s.character z) false W₁ X₁ 0 t₁ *
      polynomial (naturalCharacter s.character z) false W₂ X₂ 0 t₂ *
      ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale=
    energy (unpuncturedState s).character (unpuncturedState s).mask 1 0
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).profile 0)
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).profile 1)
      (fun i:F=> pool i) (fun i:F=>β i) (fun i:F=> P i) X₁ X₂
      (unpuncturedState s).radial.keep (unpuncturedState s).radial.profile (unpuncturedState s).radial.scale:=by
  have hh:=natural_subset_radial_eq_energy s.character (effectiveState s).radial
    (fun z hz=> s.row_ne_zero z hz.1) F
    (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁)
    (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂)
    pool β P X₁ X₂ hX₁ hX₂ hP
  simp only [CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₁ a b ha hs₁ t₁,
    CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₂ a b ha hs₂ t₂] at hh
  simpa only [independentProfiles,unpuncturedState,NaturalState.mask,
    show (1:Fin 2)≠0 by decide,ite_false,ite_true,effectiveState,effectiveRadial] using hh

theorem independent_child_ray_energy {α:Type*}[Fintype α][DecidableEq α]
    {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(ha:0< a)
    (W₁ W₂:𝓢(ℝ,ℂ))(hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (F:Finset α)(pool:α→Finset (Ideal O))(ν:α→Character)(W:α→ℝ→ℂ)(P σ freq:α→ℝ)
    (hp:∀i∈F,∀I∈pool i,Prime I)(hP:∀i∈F,0< P i)
    (t t₁ t₂ X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂):
    radialEnergy (fun z=> polynomial (naturalCharacter s.character z) false W₁ X₁ 0 t₁ *
      polynomial (naturalCharacter s.character z) false W₂ X₂ 0 t₂ *
      ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i)
        (heightCoefficient (fun I=> idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (W i) (P i) (σ i) (freq i) I) t) (P i))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale=
    energy (unpuncturedState s).character (unpuncturedState s).mask 1 0
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).profile 0)
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).profile 1)
      (fun i:F=> pool i)
      (fun (i:F) I=> idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (W i) (P i) (σ i) (t+freq i) I)
      (fun i:F=> P i) X₁ X₂
      (unpuncturedState s).radial.keep (unpuncturedState s).radial.profile (unpuncturedState s).radial.scale:=by
  rw [independent_child_energy s ha W₁ W₂ hs₁ hs₂ F pool _ P t₁ t₂ X₁ X₂ hX₁ hX₂ hP]
  exact inherited_height_energy _ _ _ _ _ (fun i:F=> pool i)
    (fun (i:F) I=> idealCoeff (ν i) I) (fun i:F=> W i)
    (fun i:F=> P i) (fun i:F=>σ i) (fun i:F=> freq i)
    (fun i=> hP i i.property) (fun i I hI=>(hp i i.property I hI).ne_zero)
    t 0 X₁ X₂ _ _ _

end CenteredMomentEnergyReferenceChild

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentEnergyReferenceChildProfiles
open HeckeFamily HeckeDyadic 
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyProfiles
open CenteredMomentAllocatedNaturalRadial CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentInductionEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentFiniteProfileExceptional
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentLattice CenteredMomentRetainedProfile
local notation "O"=> Eisenstein.O

def reflectionProfiles {a b:ℝ}(ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)
    (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)
    (j k:Fin 2)(v t:ℝ):Profiles a b:=
  independentProfiles ha (derivativeChoice (annulusSeed a b hlo hhi).profile j)
    (derivativeChoice W k)
    (derivativeChoice_support _ _ _ (annulusSeed a b hlo hhi).support j)
    (derivativeChoice_support _ _ _ hs k) (-2*Real.pi*v) t

theorem reflected_child_ray_energy {α:Type*}[Fintype α][DecidableEq α]
    {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)
    (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)
    (F:Finset α)(pool:α→Finset (Ideal O))(ν:α→Character)(Wslot:α→ℝ→ℂ)(P σ freq:α→ℝ)
    (hp:∀i∈F,∀I∈pool i,Prime I)(hP:∀i∈F,0< P i)
    (j k:Fin 2)(v t X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂):
    radialEnergy (fun z=> polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v) *
      polynomial (naturalCharacter s.character z) false (scaleTest W k) X₂ 0 t *
      ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i)
        (heightCoefficient (fun I=> idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (Wslot i) (P i) (σ i) (freq i) I) t) (P i))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale=
    energy (unpuncturedState s).character (unpuncturedState s).mask 1 0
      ((reflectionProfiles ha hlo hhi W hs j k v t).profile 0)
      ((reflectionProfiles ha hlo hhi W hs j k v t).profile 1)
      (fun i:F=> pool i)
      (fun (i:F) I=> idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (Wslot i) (P i) (σ i) (t+freq i) I)
      (fun i:F=> P i) X₁ X₂
      (unpuncturedState s).radial.keep (unpuncturedState s).radial.profile (unpuncturedState s).radial.scale:=by
  have hh:=independent_child_ray_energy s ha
    (derivativeChoice (annulusSeed a b hlo hhi).profile j) (derivativeChoice W k)
    (derivativeChoice_support _ _ _ (annulusSeed a b hlo hhi).support j)
    (derivativeChoice_support _ _ _ hs k) F pool ν Wslot P σ freq hp hP
    t (-2*Real.pi*v) t X₁ X₂ hX₁ hX₂
  have he:((annulusSeed a b hlo hhi).profile:ℝ→ℂ)=(fun y:ℝ=>(annulus y:ℂ)):=
    funext annulusTemplate_apply
  simpa only [derivativeChoice_apply,he,reflectionProfiles] using hh

theorem independent_profile_control (a b:ℝ)(ha:0< a)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,∀t₁ t₂:ℝ,
      (independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).control S≤
        C*(sourceControl T W₁*sourceControl T W₂)*(1+‖t₁‖+‖t₂‖)^(2*n):=by
  obtain ⟨n,T,C,hC,hc⟩:=normPowerProfile_source_control a b ha S
  refine ⟨n,T,C ^ 2,sq_pos_of_pos hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ t₁ t₂
  have h₁:=hc W₁ hs₁ t₁
  have h₂:=hc W₂ hs₂ t₂
  have hp₁:(1+‖t₁‖)^n≤(1+‖t₁‖+‖t₂‖)^n:=pow_le_pow_left₀ (by positivity) (by linarith [norm_nonneg t₂]) n
  have hp₂:(1+‖t₂‖)^n≤(1+‖t₁‖+‖t₂‖)^n:=pow_le_pow_left₀ (by positivity) (by linarith [norm_nonneg t₁]) n
  have h₁':S.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁)≤ C*sourceControl T W₁*(1+‖t₁‖+‖t₂‖)^n:=
    h₁.trans (mul_le_mul_of_nonneg_left hp₁ (mul_nonneg hC.le (sourceControl_nonneg _ _)))
  have h₂':S.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂)≤ C*sourceControl T W₂*(1+‖t₁‖+‖t₂‖)^n:=
    h₂.trans (mul_le_mul_of_nonneg_left hp₂ (mul_nonneg hC.le (sourceControl_nonneg _ _)))
  simp only [Profiles.control,independentProfiles,show (1:Fin 2)≠0 by decide,ite_true,ite_false]
  apply (mul_le_mul h₁' h₂' (apply_nonneg _ _)
    (mul_nonneg (mul_nonneg hC.le (sourceControl_nonneg _ _)) (by positivity))).trans_eq
  rw [show (1+‖t₁‖+‖t₂‖)^(2*n)=((1+‖t₁‖+‖t₂‖)^n)^2 by rw [Nat.mul_comm 2 n,pow_mul]]
  ring

lemma derivative_choice_control (S:Finset (ℕ×ℕ)):
    ∃T:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧ ∀W:𝓢(ℝ,ℂ),∀j:Fin 2,
      sourceControl S (derivativeChoice W j)≤ C*sourceControl T W:=by
  obtain ⟨T,C,hC,hc⟩:=scale_source_control S
  refine ⟨S∪T,1+C,by positivity,?_⟩
  intro W j
  have h₁:sourceControl S W≤ sourceControl (S∪T) W:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left:S⊆S∪T)) W
  have h₂:sourceControl T W≤ sourceControl (S∪T) W:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_right:T⊆S∪T)) W
  by_cases hj:j=0
  · simp only [derivativeChoice,if_pos hj]
    exact h₁.trans (le_mul_of_one_le_left (sourceControl_nonneg _ _) (by linarith))
  · simp only [derivativeChoice,if_neg hj]
    exact (hc W).trans (mul_le_mul (by linarith) h₂ (sourceControl_nonneg _ _) (by positivity))

theorem reflected_profile_control (a b:ℝ)(ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)
    (S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀W:𝓢(ℝ,ℂ),∀hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b,
      ∀j k:Fin 2,∀v t:ℝ,
      (reflectionProfiles ha hlo hhi W hs j k v t).control S≤
        C*sourceControl T W*(1+‖v‖+‖t‖)^n:=by
  obtain ⟨n,T,C,hC,hc⟩:=independent_profile_control a b ha S
  obtain ⟨U,D,hD,hd⟩:=derivative_choice_control T
  let A:ℝ:=1+∑j:Fin 2,sourceControl T (derivativeChoice (annulusSeed a b hlo hhi).profile j)
  have hA:0< A:=by
    have hh:=Finset.sum_nonneg (fun (j:Fin 2) (_:j∈Finset.univ)=>
      sourceControl_nonneg T (derivativeChoice (annulusSeed a b hlo hhi).profile j))
    dsimp [A];linarith
  refine ⟨2*n,U,C*A*D*(1+2*Real.pi)^(2*n),by positivity,?_⟩
  intro W hs j k v t
  have haSeed:sourceControl T (derivativeChoice (annulusSeed a b hlo hhi).profile j)≤ A:=by
    have hh:=Finset.single_le_sum (fun (j:Fin 2) (_:j∈Finset.univ)=>
      sourceControl_nonneg T (derivativeChoice (annulusSeed a b hlo hhi).profile j)) (Finset.mem_univ j)
    dsimp [A];linarith
  have hheight:1+‖-2*Real.pi*v‖+‖t‖≤(1+2*Real.pi)*(1+‖v‖+‖t‖):=by
    rw [norm_mul,norm_mul,Real.norm_of_nonneg Real.pi_pos.le]
    norm_num only [norm_neg,Real.norm_of_nonneg (by norm_num:0≤(2:ℝ))]
    nlinarith [Real.pi_pos,norm_nonneg v,norm_nonneg t]
  have hh:=hc (derivativeChoice (annulusSeed a b hlo hhi).profile j) (derivativeChoice W k)
    (derivativeChoice_support _ _ _ (annulusSeed a b hlo hhi).support j)
    (derivativeChoice_support _ _ _ hs k) (-2*Real.pi*v) t
  apply hh.trans
  calc
    _≤ C*(A*(D*sourceControl U W))*((1+2*Real.pi)*(1+‖v‖+‖t‖))^(2*n):=by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (mul_le_mul haSeed (hd W k) (sourceControl_nonneg _ _) hA.le) hC.le
      · exact pow_le_pow_left₀ (by positivity) hheight _
      · positivity
      · exact mul_nonneg hC.le (mul_nonneg hA.le (mul_nonneg hD.le (sourceControl_nonneg _ _)))
    _=_:=by rw [mul_pow];ring

end CenteredMomentEnergyReferenceChildProfiles

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentEnergyReferenceLowControl
open CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentFiniteProfileExceptional

lemma height_product (v t H:ℝ)(hH:0≤ H):
    1+‖v‖+‖t‖≤(1+‖v‖)*(1+|t|+H):=by
  simp only [Real.norm_eq_abs]
  nlinarith [abs_nonneg v,abs_nonneg t]

theorem reflected_child_control (a b:ℝ)(ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)
    (S:Finset (ℕ×ℕ))(degree:ℕ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃D:ℝ,0< D ∧
      ∀W:𝓢(ℝ,ℂ),∀hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b,
      ∀j k:Fin 2,∀v t height:ℝ,0≤ height →
      ((reflectionProfiles ha hlo hhi W hs j k v t).control S)^2*
        (1+|t|+height)^degree≤
        D*(sourceControl T W)^2*(1+|t|+height)^(degree+2*n)*(1+‖v‖)^(2*n):=by
  obtain ⟨n,T,D,hD,hd⟩:=reflected_profile_control a b ha hlo hhi S
  refine ⟨n,T,D^2,sq_pos_of_pos hD,?_⟩
  intro W hs j k v t height hheight
  have hbase:=hd W hs j k v t
  have hgrowth:(1+‖v‖+‖t‖)^n≤((1+‖v‖)*(1+|t|+height))^n:=
    pow_le_pow_left₀ (by positivity) (height_product v t height hheight) n
  have hprof:((reflectionProfiles ha hlo hhi W hs j k v t).control S)^2≤
      (D*sourceControl T W*((1+‖v‖)*(1+|t|+height))^n)^2:=
    pow_le_pow_left₀ (Profiles.control_nonneg _ _) (hbase.trans
      (mul_le_mul_of_nonneg_left hgrowth (mul_nonneg hD.le (sourceControl_nonneg _ _)))) 2
  apply (mul_le_mul_of_nonneg_right hprof (by positivity)).trans_eq
  simp only [mul_pow] at *
  rw [pow_add,show (1+|t|+height)^(2*n)=((1+|t|+height)^n)^2 by rw [Nat.mul_comm 2 n,pow_mul],
    show (1+‖v‖)^(2*n)=((1+‖v‖)^n)^2 by rw [Nat.mul_comm 2 n,pow_mul]]
  ring

end CenteredMomentEnergyReferenceLowControl

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentFiniteProfileExceptional

lemma control_mono {S T:Finset (ℕ×ℕ)}(h:S⊆T)(W:𝓢(ℝ,ℂ)):
    sourceControl S W≤ sourceControl T W:=Seminorm.le_def.mp (Finset.sup_mono h) W

theorem reference_envelopes (a b:ℝ)(ha:0< a)
    (S T Slong:Finset (ℕ×ℕ))(degree n nlong:ℕ)(Cref Dchild Dref:ℝ)
    (hCr:0< Cref)(hDc:0< Dchild)(hDr:0< Dref):
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀W₁ W₂:𝓢(ℝ,ℂ),∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,∀t height:ℝ,0≤ height →
      let E:=C*(sourceControl U W₁*sourceControl U W₂)^2*(1+|t|+height)^J;
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*(1+|t|+height)^degree≤ E ∧
      Cref*Dchild*(sourceControl Slong W₂)^2*(sourceControl T W₁)^2*
        (1+‖t‖)^(2*nlong)*(1+|t|+height)^(degree+2*n)≤ E ∧
      Dref*(sourceControl Slong W₂)^2*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
        (1+‖t‖)^(2*nlong)≤ E:=by
  obtain ⟨na,Ta,Ca,hCa,hprof⟩:=independent_profile_control a b ha S
  let U:=((Ta∪T)∪Slong)∪{(0,0)}
  let J:=degree+4*na+2*n+2*nlong
  let C:=1+Ca^2*2^(4*na)+Cref*Dchild+Dref
  have hC:0< C:=by dsimp only [C];positivity
  refine ⟨J,U,C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ t height hheight
  dsimp only
  let H:=1+|t|+height
  let A:=sourceControl U W₁*sourceControl U W₂
  have hH:1≤ H:=by dsimp only [H];linarith [abs_nonneg t]
  have hH0:0≤ H:=zero_le_one.trans hH
  have hA:0≤ A:=mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have haU:Ta⊆U:=by intro x hx;simp [U,hx]
  have hTU:T⊆U:=by intro x hx;simp [U,hx]
  have hlU:Slong⊆U:=by intro x hx;simp [U,hx]
  have hzU:(0,0)∈U:=by simp [U]
  have hz:(schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁≤ sourceControl U W₁:=
    Seminorm.le_def.mp (Finset.le_sup hzU) W₁
  have hp:(independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S≤ Ca*A*(2*H)^(2*na):=by
    apply (hprof W₁ W₂ hs₁ hs₂ t t).trans
    apply mul_le_mul
    · apply mul_le_mul_of_nonneg_left _ hCa.le
      exact mul_le_mul (control_mono haU W₁) (control_mono haU W₂)
        (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
    · apply pow_le_pow_left₀ (by positivity)
      dsimp only [H]
      simp only [Real.norm_eq_abs]
      linarith [abs_nonneg t]
    · positivity
    · positivity
  have hd:(independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S^2*H^degree≤
      (Ca^2*2^(4*na))*A^2*H^J:=by
    have hsq:=pow_le_pow_left₀ (Profiles.control_nonneg _ _) hp 2
    have hmul:=mul_le_mul_of_nonneg_right hsq (pow_nonneg hH0 degree)
    have hid:(Ca*A*(2*H)^(2*na))^2*H^degree=
        (Ca^2*2^(4*na))*A^2*H^(degree+4*na):=by
      rw [mul_pow,mul_pow,←pow_mul,show (2*na)*2=4*na by omega,mul_pow,pow_add]
      ring_nf
    rw [hid] at hmul
    exact hmul.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hH (by dsimp only [J];omega)) (by positivity))
  have hm:(sourceControl Slong W₂)^2*(sourceControl T W₁)^2≤ A^2:=by
    rw [←mul_pow]
    apply pow_le_pow_left₀ (mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _))
    dsimp only [A]
    simpa only [mul_comm] using mul_le_mul (control_mono hTU W₁) (control_mono hlU W₂)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have he:(sourceControl Slong W₂)^2*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2≤ A^2:=by
    rw [←mul_pow]
    apply pow_le_pow_left₀ (mul_nonneg (sourceControl_nonneg _ _) (apply_nonneg _ _))
    dsimp only [A]
    simpa only [mul_comm] using mul_le_mul hz (control_mono hlU W₂)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hheightpow:(1+‖t‖)^(2*nlong)≤ H^(2*nlong):=by
    apply pow_le_pow_left₀ (by positivity)
    dsimp only [H]
    simp only [Real.norm_eq_abs]
    linarith
  have hcm: Cref*Dchild≤ C:=by dsimp only [C];nlinarith [sq_nonneg Ca,pow_nonneg (show (0:ℝ)≤2 by norm_num) (4*na)]
  have hce:Dref≤ C:=by dsimp only [C];nlinarith [sq_nonneg Ca,pow_nonneg (show (0:ℝ)≤2 by norm_num) (4*na)]
  have hcd:Ca^2*2^(4*na)≤ C:=by dsimp only [C];nlinarith
  refine ⟨hd.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcd (sq_nonneg A)) (pow_nonneg hH0 J)),?_,?_⟩
  · calc
      _=(Cref*Dchild)*((sourceControl Slong W₂)^2*(sourceControl T W₁)^2)*
          ((1+‖t‖)^(2*nlong)*H^(degree+2*n)):=by ring
      _≤ C*A^2*(H^(2*nlong)*H^(degree+2*n)):=by gcongr
      _≤ C*A^2*H^J:=by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (sq_nonneg A))
        rw [←pow_add]
        exact pow_le_pow_right₀ hH (by dsimp only [J];omega)
  · calc
      _=Dref*((sourceControl Slong W₂)^2*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2)*(1+‖t‖)^(2*nlong):=by ring
      _≤ C*A^2*H^(2*nlong):=by gcongr
      _≤ C*A^2*H^J:=mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hH (by dsimp only [J];omega)) (mul_nonneg hC.le (sq_nonneg A))

end CenteredMomentEnergyReferenceProfileBudget

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentEnergyReferenceDivisors
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyReferenceState
local notation "O"=> Eisenstein.O

lemma divisor_norm {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (D:Finset (Ideal O))(hD:D∈(CubicEisenstein.primeSupport s.puncture).powerset):
    1≤((∏P∈D,P).absNorm:ℝ) ∧ ((∏P∈D,P).absNorm:ℝ)≤ Z^Bmask:=by
  have hs:D⊆primeSupport s.puncture:=Finset.mem_powerset.mp hD
  have hn:=support_product_ne_zero hs
  have hp:0<(∏P∈D,P).absNorm:=Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn)
  refine ⟨by exact_mod_cast hp,?_⟩
  apply le_trans _ s.puncture_bound
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.puncture_ne_zero))
    (map_dvd Ideal.absNorm (support_product_dvd s.puncture_ne_zero hs))

lemma divided_scale_power (Z Y N:ℝ)(hZ:1< Z)(hY:0< Y)(hN:0< N):
    Z^(Real.logb Z Y-Real.logb Z N)=Y/N:=by
  rw [Real.rpow_sub (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hY,
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hN]

theorem divisor_reflection_range {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1< Z)(L Y:ℝ)(hwidth:s.width≤ L)(hY:1≤ Y)
    (D:Finset (Ideal O))(hD:D∈(CubicEisenstein.primeSupport s.puncture).powerset):
    let a:=Real.logb Z Y-Real.logb Z ((∏P∈D,P).absNorm:ℝ);
    -Bmask≤ a ∧ s.width≤(L+Bmask)+a ∧
      Z^a=Y/((∏P∈D,P).absNorm:ℝ):=by
  dsimp only
  obtain ⟨hn,hcap⟩:=divisor_norm s D hD
  have hp:0<((∏P∈D,P).absNorm:ℝ):=zero_lt_one.trans_le hn
  have hlogN:Real.logb Z ((∏P∈D,P).absNorm:ℝ)≤ Bmask:=
    (Real.logb_le_iff_le_rpow hZ hp).mpr hcap
  have hlogY:=Real.logb_nonneg hZ hY
  refine ⟨by linarith,by linarith,divided_scale_power Z Y _ hZ (zero_lt_one.trans_le hY) hp⟩

theorem balanced_divisor_range {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1< Z)(L X₁ X₂ ell κ:ℝ)(hwidth:s.width≤ L)
    (hX₁:0< X₁)(hX₂:0< X₂)(hell:0≤ ell)(hκ:3/4≤κ)
    (hlarge:5*s.width/6≤ Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤ s.width)
    (D₁ D₂:Finset (Ideal O))
    (hD₁:D₁∈(CubicEisenstein.primeSupport s.puncture).powerset)
    (hD₂:D₂∈(CubicEisenstein.primeSupport s.puncture).powerset):
    let short:=s.width/4-Real.logb Z ((∏P∈D₁,P).absNorm:ℝ)
    let long:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ);
    -Bmask≤ short ∧ -Bmask≤ long ∧ s.width≤(L+Bmask)+long ∧
    Z^short=comparisonFirst Z s.width/((∏P∈D₁,P).absNorm:ℝ) ∧
    Z^long=comparisonSecond Z s.width X₁ X₂/((∏P∈D₂,P).absNorm:ℝ):=by
  have hg:=balanced_reference_geometry Z s.width X₁ X₂ ell κ hZ s.width_nonneg
    hX₁ hX₂ hell hκ hlarge hcap
  have hfirst:Real.logb Z (comparisonFirst Z s.width)=s.width/4:=by
    exact Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'
  have hs:=divisor_reflection_range s hZ L (comparisonFirst Z s.width) hwidth hg.2.1 D₁ hD₁
  have hl:=divisor_reflection_range s hZ L (comparisonSecond Z s.width X₁ X₂) hwidth
    (hg.2.1.trans hg.2.2.1) D₂ hD₂
  dsimp only at hs hl ⊢
  rw [hfirst] at hs
  rw [hg.2.2.2.1] at hl
  exact ⟨hs.1,hl.1,hl.2.1,hs.2.2,hl.2.2⟩

end CenteredMomentEnergyReferenceDivisors

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentEnergyReferenceSource
open HeckeFamily HeckeDyadic 
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentInductionEnergy
open CenteredMomentRetainedEnergy
local notation "O"=> Eisenstein.O
variable {α:Type*}[Fintype α][DecidableEq α]

def signedCommonSource {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (W₁ W₂:ℝ→ℂ)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(z:O):ℂ:=
  let χ:=naturalCharacter s.character z
  let R:=CubicEisenstein.primeSupport s.puncture
  ∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈(Finset.univ:Finset α).powerset,
    signedCoefficient χ R D₁ D₂ J pool (fun i=> heightCoefficient (β i) t) P *
      (polynomial χ false W₁ (X₁/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
       polynomial χ false W₂ (X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
       ∏i∈Finset.univ\J,naturalSlot χ (pool i) (heightCoefficient (β i) t) (P i))

lemma original_row_eq_signed {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)
    (W₁ W₂:𝓢(ℝ,ℂ))(ha:0< a)
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (pool:α→Finset (Ideal O))(hp:∀i,∀I∈pool i,Prime I)
    (β:α→Ideal O→ℂ)(P:α→ℝ)(hP:∀i,0< P i)
    (t X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)(z:O)(hz:z≠0):
    positiveSlotRow s.character s.mask 1 z W₁ W₂ pool β P t X₁ X₂=
      ((X₁:ℂ)^(Complex.I*t)*(X₂:ℂ)^(Complex.I*t))*
        signedCommonSource s W₁ W₂ pool β P t X₁ X₂ z:=by
  have hh:=original_positive_deletion s.character z hz s.puncture s.puncture_ne_zero
    W₁ W₂ a b a b ha ha hs₁ hs₂ (W₁.smooth ⊤) (W₂.smooth ⊤)
    pool hp β P hP t X₁ X₂ hX₁ hX₂
  dsimp only at hh
  simp only [CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₁ a b ha hs₁ t,
    CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₂ a b ha hs₂ t] at hh
  simpa only [NaturalState.mask,signedCommonSource,naturalCharacter_eq s.character z hz] using hh

theorem original_energy_eq_signed {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)
    (W₁ W₂:𝓢(ℝ,ℂ))(ha:0< a)
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (pool:α→Finset (Ideal O))(hp:∀i,∀I∈pool i,Prime I)
    (β:α→Ideal O→ℂ)(P:α→ℝ)(hP:∀i,0< P i)
    (t X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂):
    energy s.character s.mask 1 t W₁ W₂ pool β P X₁ X₂
      s.radial.keep s.radial.profile s.radial.scale=
    radialEnergy (signedCommonSource s W₁ W₂ pool β P t X₁ X₂)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale:=by
  change _=radialEnergy _ (effectiveRadial s.radial).keep _ _
  rw [radialEnergy_effective]
  unfold energy radialEnergy
  apply tsum_congr
  intro z
  by_cases hz:s.radial.keep z
  · simp only [if_pos hz]
    rw [original_row_eq_signed s W₁ W₂ ha hs₁ hs₂ pool hp β P hP t X₁ X₂ hX₁ hX₂
      z (s.row_ne_zero z hz),norm_mul,norm_mul,
      positive_height_phase_norm X₁ t hX₁,positive_height_phase_norm X₂ t hX₂,one_mul,one_mul]
  · simp only [if_neg hz]

end CenteredMomentEnergyReferenceSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentEnergyReferenceWeightedEnergy
open HeckeFamily  CenteredMomentCommonMaskEnergy
open CenteredMomentOriginalRadialComparison
local notation "O"=> Eisenstein.O

lemma finite_weighted_energy {ι κ:Type*}[Fintype ι][Fintype κ]
    (a f:ι→κ→ℂ)(ρ q:κ→ℝ)(hρ:∀j,0≤ρ j)(hq:∀j,0≤ q j)
    (ha:∀i j,‖a i j‖≤ρ j)(E:ℝ)(hE:0≤ E)
    (hf:∀j,∑i,‖f i j‖^2≤ E*(q j)^2):
    (∑i,‖∑j,a i j*f i j‖^2)≤(∑j,ρ j*q j)^2*E:=by
  have hb(j:κ):(∑i,‖a i j*f i j‖^2)≤(ρ j*q j*Real.sqrt E)^2:=by
    calc
      _≤∑i,(ρ j)^2*‖f i j‖^2:=Finset.sum_le_sum (fun i _=> by
        rw [norm_mul,mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha i j) 2) (sq_nonneg _))
      _=(ρ j)^2*(∑i,‖f i j‖^2):=(Finset.mul_sum _ _ _).symm
      _≤(ρ j)^2*(E*(q j)^2):=mul_le_mul_of_nonneg_left (hf j) (sq_nonneg _)
      _=_:=by rw [mul_pow,Real.sq_sqrt hE];ring
  have hh:=CompletedGauss.finite_tsum_energy_bound (fun j i=> a i j*f i j)
    (fun j=>ρ j*q j*Real.sqrt E) (fun j=> mul_nonneg (mul_nonneg (hρ j) (hq j)) (Real.sqrt_nonneg E))
    (summable_of_hasFiniteSupport (Set.toFinite _)) hb
  simpa only [tsum_fintype,←Finset.sum_mul,mul_pow,Real.sq_sqrt hE] using hh.2

theorem radial_weighted_energy {κ:Type*}[Fintype κ]
    (a f:O→κ→ℂ)(ρ q:κ→ℝ)(hρ:∀j,0≤ρ j)(hq:∀j,0≤ q j)
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K E:ℝ)
    (hΦ:∀z,0≤(Φ (‖ringComplex z‖^2/K)).re)
    (ha:∀z,keep z→∀j,‖a z j‖≤ρ j)(hE:0≤ E)
    (hs:∀j,Summable (fun z:O=> if keep z then ‖f z j‖^2*(Φ (‖ringComplex z‖^2/K)).re else 0))
    (hf:∀j,radialEnergy (fun z=> f z j) keep Φ K≤ E*(q j)^2):
    radialEnergy (fun z=>∑j,a z j*f z j) keep Φ K≤(∑j,ρ j*q j)^2*E:=by
  unfold radialEnergy
  apply Real.tsum_le_of_sum_le (fun z=> by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)
  intro rows
  let S:=rows.filter keep
  let w(z:S):ℂ:=(Real.sqrt ((Φ (‖ringComplex z‖^2/K)).re):ℂ)
  have hh:=finite_weighted_energy (fun z:S=> a z) (fun z:S=> fun j=> f z j*w z) ρ q hρ hq
    (fun z=> ha z (Finset.mem_filter.mp z.property).2) E hE ?_
  · have hsum(z:S):(∑j,a z j*(f z j*w z))=(∑j,a z j*f z j)*w z:=by
      rw [Finset.sum_mul];apply Finset.sum_congr rfl;intro j _;ring
    simp_rw [hsum] at hh
    dsimp only [w] at hh
    rw [CenteredMomentOriginalRadialComparison.finite_weighted rows keep (fun z=>∑j,a z j*f z j) Φ K hΦ] at hh
    exact hh
  · intro j
    dsimp only [w]
    rw [CenteredMomentOriginalRadialComparison.finite_weighted rows keep (fun z=> f z j) Φ K hΦ]
    exact ((hs j).sum_le_tsum rows (fun z _=> by
      split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)).trans (hf j)

end CenteredMomentEnergyReferenceWeightedEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace CenteredMomentEnergyReferenceDeletionBudget
open HeckeFamily CenteredMomentCommonMaskExpansion CenteredMomentReflectionMass
open CenteredMomentReflectionDeletion UniqueFactorizationMonoid
local notation "O"=> Eisenstein.O

lemma product_norm_ge_one (D:Finset (Ideal O))(hD:∀I∈D,Prime I):
    (1:ℝ)≤(∏I∈D,I).absNorm:=by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (subset_product_nonzero D hD))

lemma weighted_inverse_sqrt (I:Ideal O)(hI:I≠0)(t:ℝ)(ht:t≤1/2):
    weight I*(I.absNorm:ℝ)^t≤1:=by
  have hn:(1:ℝ)≤ I.absNorm:=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hp:(0:ℝ)< I.absNorm:=zero_lt_one.trans_le hn
  rw [weight,Real.sqrt_eq_rpow,←Real.rpow_neg hp.le,←Real.rpow_add hp]
  exact Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith)

lemma powerset_square_subpower (eps:ℝ)(heps:0< eps):
    ∃C:ℝ,0< C ∧ ∀(R:Finset (Ideal O))(_hR:∀I∈R,Prime I),
      (R.powerset.card:ℝ)^2≤ C*((∏I∈R,I).absNorm:ℝ)^eps:=by
  obtain ⟨C,hC,hb⟩:=HeckeDeletionBounds.constant_pow_primeSupport_bound 4 eps (by norm_num) heps
  refine ⟨C,hC,?_⟩
  intro R hR
  have hf:normalizedFactors (∏I∈R,I)=R.val:=by
    simpa using normalizedFactors_prod_of_prime (m:=R.val) hR
  have hs:primeSupport (∏I∈R,I)=R:=by
    simp [primeSupport,hf]
  have hh:=hb (∏I∈R,I) (subset_product_nonzero R hR)
  rw [hs] at hh
  convert hh using 1
  rw [Finset.card_powerset,Nat.cast_pow,Nat.cast_ofNat,←pow_mul, mul_comm R.card 2,pow_mul]
  norm_num

variable {α:Type*}

lemma weighted_uniform_term (R D₁ D₂:Finset (Ideal O))
    (hR:∀I∈R,Prime I)(hD₁:D₁⊆R)(hD₂:D₂⊆R)(J:Finset α)
    (b M:α→ℝ)(hM:∀i∈J,0≤ M i)(t:ℝ)(ht:t≤1/2):
    uniformMajorant R D₁ D₂ J b M*((∏I∈D₂,I).absNorm:ℝ)^t≤
      ∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I):=by
  have hn₂:=subset_product_nonzero D₂ (fun I hi=> hR I (hD₂ hi))
  have hw₁:weight (∏I∈D₁,I)≤1:=by
    simpa using weighted_inverse_sqrt (∏I∈D₁,I)
      (subset_product_nonzero D₁ (fun I hi=> hR I (hD₁ hi))) 0 (by norm_num)
  have hw₂:=weighted_inverse_sqrt (∏I∈D₂,I) hn₂ t ht
  have hprod:0≤∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I):=
    Finset.prod_nonneg (fun i hi=> mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hM i hi))
      (Finset.sum_nonneg (fun I _=> weight_nonneg I)))
  unfold uniformMajorant
  calc
    _=(weight (∏I∈D₁,I)*(weight (∏I∈D₂,I)*((∏I∈D₂,I).absNorm:ℝ)^t))*
        (∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)):=by ring
    _≤1*(∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)):=
      mul_le_mul_of_nonneg_right
        ((mul_le_mul hw₁ hw₂ (mul_nonneg (weight_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) t))
          zero_le_one).trans_eq (one_mul 1)) hprod
    _=_:=one_mul _

lemma signed_weighted_term (χ:Character)(R D₁ D₂:Finset (Ideal O))
    (hR:∀I∈R,Prime I)(hD₁:D₁⊆R)(hD₂:D₂⊆R)(J:Finset α)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P b M:α→ℝ)
    (hp:∀i∈J,∀I∈pool i,Prime I)(hP:∀i∈J,0< P i)(hM:∀i∈J,0≤ M i)
    (hβ:∀i∈J,∀I∈pool i,‖β i I‖≤ M i)
    (hs:∀i∈J,∀I∈pool i,β i I≠0→(I.absNorm:ℝ)≤ b i*P i)
    (t:ℝ)(ht:t≤1/2):
    ‖signedCoefficient χ R D₁ D₂ J pool β P‖*((∏I∈D₂,I).absNorm:ℝ)^t≤
      ∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I):=by
  have hn₂:=subset_product_nonzero D₂ (fun I hi=> hR I (hD₂ hi))
  have hw₁:weight (∏I∈D₁,I)≤1:=by
    simpa using weighted_inverse_sqrt (∏I∈D₁,I)
      (subset_product_nonzero D₁ (fun I hi=> hR I (hD₁ hi))) 0 (by norm_num)
  have hw₂:=weighted_inverse_sqrt (∏I∈D₂,I) hn₂ t ht
  have hprod:0≤∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I):=
    Finset.prod_nonneg (fun i hi=> mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hM i hi))
      (Finset.sum_nonneg (fun I _=> weight_nonneg I)))
  apply (mul_le_mul_of_nonneg_right
    (signedCoefficient_uniform χ R hR D₁ D₂ hD₁ hD₂ J pool β P b M hp hP hM hβ hs)
    (Real.rpow_nonneg (Nat.cast_nonneg _) t)).trans
  unfold uniformMajorant
  calc
    _=(weight (∏I∈D₁,I)*(weight (∏I∈D₂,I)*((∏I∈D₂,I).absNorm:ℝ)^t))*
        (∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)):=by ring
    _≤1*(∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)):=
      mul_le_mul_of_nonneg_right
        ((mul_le_mul hw₁ hw₂ (mul_nonneg (weight_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) t))
          zero_le_one).trans_eq (one_mul 1)) hprod
    _=_:=one_mul _

lemma slot_majorant_mass (R:Finset (Ideal O))(hR:∀I∈R,Prime I)
    (F:Finset α)(b M:α→ℝ)(hM:∀i∈F,0≤ M i):
    (∑J∈F.powerset,∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I))≤
      (∏i∈F,max 1 (Real.sqrt (max 1 (b i))*M i))*(∏I∈R,localMass I)^F.card:=by
  rw [←Finset.prod_one_add]
  have he:1+∑I∈R,weight I≤∏I∈R,localMass I:=
    (one_add_sum_weight R).trans (deletion_le_euler R hR)
  have hp (i:α)(hi:i∈F):1+(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)≤
      max 1 (Real.sqrt (max 1 (b i))*M i)*(∏I∈R,localMass I):=by
    have h1:=le_max_left 1 (Real.sqrt (max 1 (b i))*M i)
    have h2:=le_max_right 1 (Real.sqrt (max 1 (b i))*M i)
    have hs:0≤∑I∈R,weight I:=Finset.sum_nonneg (fun I _=> weight_nonneg I)
    nlinarith
  calc
    _≤∏i∈F,max 1 (Real.sqrt (max 1 (b i))*M i)*(∏I∈R,localMass I):=
      Finset.prod_le_prod (fun i hi=> add_nonneg zero_le_one
        (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hM i hi))
          (Finset.sum_nonneg (fun I _=> weight_nonneg I)))) hp
    _=_:=by rw [Finset.prod_mul_distrib,Finset.prod_const]

theorem weighted_uniform_mass_subpower (F:Finset α)(b M:α→ℝ)(hM:∀i∈F,0≤ M i)
    (eps:ℝ)(heps:0< eps):
    ∃C:ℝ,0< C ∧ ∀(R:Finset (Ideal O))(_hR:∀I∈R,Prime I),
      ∀t:ℝ,t≤1/2→
      (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
        uniformMajorant R D₁ D₂ J b M*((∏I∈D₂,I).absNorm:ℝ)^t)≤
        C*((∏I∈R,I).absNorm:ℝ)^eps:=by
  obtain ⟨Cc,hCc,hcard⟩:=powerset_square_subpower (eps/2) (by linarith)
  let delta:=eps/(2*((F.card:ℝ)+1))
  have hd:0< delta:=div_pos heps (by positivity)
  obtain ⟨Ce,hCe,heuler⟩:=euler_mass_subpower delta hd
  let A:ℝ:=∏i∈F,max 1 (Real.sqrt (max 1 (b i))*M i)
  have hA:0< A:=Finset.prod_pos (fun i _=> lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  refine ⟨Cc*A*Ce^F.card,by positivity,?_⟩
  intro R hR t ht
  have hsum:(∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
      uniformMajorant R D₁ D₂ J b M*((∏I∈D₂,I).absNorm:ℝ)^t)≤
      (R.powerset.card:ℝ)^2*(∑J∈F.powerset,
        ∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)):=by
    calc
      _≤∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
          ∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I):=by
        apply Finset.sum_le_sum;intro D₁ hD₁
        apply Finset.sum_le_sum;intro D₂ hD₂
        apply Finset.sum_le_sum;intro J hJ
        have hJF:=Finset.mem_powerset.mp hJ
        exact weighted_uniform_term R D₁ D₂ hR (Finset.mem_powerset.mp hD₁)
          (Finset.mem_powerset.mp hD₂) J b M (fun i hi=> hM i (hJF hi)) t ht
      _=_:=by simp only [Finset.sum_const,nsmul_eq_mul];ring
  let N:ℝ:=(∏I∈R,I).absNorm
  have hN:1≤ N:=product_norm_ge_one R hR
  have hN0:0< N:=zero_lt_one.trans_le hN
  have hmass:0≤∑J∈F.powerset,∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I):=by
    exact Finset.sum_nonneg (fun J hJ=> Finset.prod_nonneg (fun i hi=> mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (hM i ((Finset.mem_powerset.mp hJ) hi)))
      (Finset.sum_nonneg (fun I _=> weight_nonneg I))))
  have hpow:(∏I∈R,localMass I)^F.card≤ Ce^F.card*N^(eps/2):=by
    calc
      _≤(Ce*N^delta)^F.card:=pow_le_pow_left₀
        (Finset.prod_nonneg (fun I hi=> localMass_nonneg I (hR I hi))) (heuler R hR) _
      _=Ce^F.card*N^(delta*(F.card:ℝ)):=by rw [mul_pow,←Real.rpow_mul_natCast hN0.le]
      _≤ _:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN (by
        dsimp [delta]
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ (by positivity:0<2*((F.card:ℝ)+1))).mpr
        nlinarith)) (by positivity)
  calc
    _≤(R.powerset.card:ℝ)^2*(A*(∏I∈R,localMass I)^F.card):=
      hsum.trans (mul_le_mul_of_nonneg_left (slot_majorant_mass R hR F b M hM) (sq_nonneg _))
    _≤(Cc*N^(eps/2))*(A*(Ce^F.card*N^(eps/2))):=
      mul_le_mul (hcard R hR) (mul_le_mul_of_nonneg_left hpow hA.le)
        (mul_nonneg hA.le (pow_nonneg (Finset.prod_nonneg (fun I hi=> localMass_nonneg I (hR I hi))) _))
        (by positivity)
    _=(Cc*A*Ce^F.card)*N^eps:=by
      rw [show (Cc*N^(eps/2))*(A*(Ce^F.card*N^(eps/2)))=
        (Cc*A*Ce^F.card)*(N^(eps/2)*N^(eps/2)) by ring,←Real.rpow_add hN0]
      congr 2
      ring

theorem weighted_signed_mass_subpower (F:Finset α)(b M:α→ℝ)(hM:∀i∈F,0≤ M i)
    (eps:ℝ)(heps:0< eps):
    ∃C:ℝ,0< C ∧ ∀(R:Finset (Ideal O))(_hR:∀I∈R,Prime I)
      (χ:Character)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ),
      (∀i∈F,∀I∈pool i,Prime I)→(∀i∈F,0< P i)→
      (∀i∈F,∀I∈pool i,‖β i I‖≤ M i)→
      (∀i∈F,∀I∈pool i,β i I≠0→(I.absNorm:ℝ)≤ b i*P i)→
      ∀t:ℝ,t≤1/2→
      (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
        ‖signedCoefficient χ R D₁ D₂ J pool β P‖*((∏I∈D₂,I).absNorm:ℝ)^t)≤
        C*((∏I∈R,I).absNorm:ℝ)^eps:=by
  obtain ⟨C,hC,hbound⟩:=weighted_uniform_mass_subpower F b M hM eps heps
  refine ⟨C,hC,?_⟩
  intro R hR χ pool β P hp hP hβ hs t ht
  apply le_trans _ (hbound R hR t ht)
  apply Finset.sum_le_sum;intro D₁ hD₁
  apply Finset.sum_le_sum;intro D₂ hD₂
  apply Finset.sum_le_sum;intro J hJ
  have hJF:=Finset.mem_powerset.mp hJ
  exact mul_le_mul_of_nonneg_right
    (signedCoefficient_uniform χ R hR D₁ D₂ (Finset.mem_powerset.mp hD₁)
      (Finset.mem_powerset.mp hD₂) J pool β P b M
      (fun i hi=> hp i (hJF hi)) (fun i hi=> hP i (hJF hi))
      (fun i hi=> hM i (hJF hi)) (fun i hi=> hβ i (hJF hi))
      (fun i hi=> hs i (hJF hi))) (Real.rpow_nonneg (Nat.cast_nonneg _) t)

end CenteredMomentEnergyReferenceDeletionBudget

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentEnergyReferenceDeletionEnergy
open HeckeFamily HeckeDyadic 
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceSource CenteredMomentEnergyReferenceWeightedEnergy
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentRadialPolynomialEnergy
open CenteredMomentCommonMaskRadialEnergy CenteredMomentInductionEnergy
local notation "O"=> Eisenstein.O
variable {α:Type*}[Fintype α][DecidableEq α]

theorem original_energy_weighted_deletion (bslot M:α→ℝ)(hM:∀i,0≤ M i)
    (ε:ℝ)(hε:0<ε):
    ∃C:ℝ,0< C ∧ ∀(Z Bmask bΦ a b:ℝ)(s:NaturalState Z Bmask bΦ)
      (W₁ W₂:𝓢(ℝ,ℂ)),0< a → 0≤ b →
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
        (t X₁ X₂ E p:ℝ),
      (∀i,∀I∈pool i,Prime I) → (∀i,0< P i) →
      (∀i,∀I∈pool i,‖β i I‖≤ M i) →
      (∀i,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤ bslot i*P i) →
      0< X₁ → 0< X₂ → 0≤ E → p≤1 →
      (∀D₁∈(CubicEisenstein.primeSupport s.puncture).powerset,
       ∀D₂∈(CubicEisenstein.primeSupport s.puncture).powerset,
       ∀J∈(Finset.univ:Finset α).powerset,
        radialEnergy (fun z=> polynomial (naturalCharacter s.character z) false W₁
          (X₁/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
          polynomial (naturalCharacter s.character z) false W₂
          (X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
          ∏i∈Finset.univ\J,naturalSlot (naturalCharacter s.character z) (pool i)
            (heightCoefficient (β i) t) (P i))
          (effectiveState s).radial.keep s.radial.profile s.radial.scale
            ≤ E*((∏I∈D₂,I).absNorm:ℝ)^p) →
      energy s.character s.mask 1 t W₁ W₂ pool β P X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤ C*(s.puncture.radical.absNorm:ℝ)^ε*E:=by
  obtain ⟨C,hC,hmass⟩:=CenteredMomentEnergyReferenceDeletionBudget.weighted_uniform_mass_subpower
    (Finset.univ:Finset α) bslot M (fun i _=> hM i) (ε/2) (by positivity)
  refine ⟨C ^ 2,sq_pos_of_pos hC,?_⟩
  intro Z Bmask bΦ a b s W₁ W₂ ha hb hs₁ hs₂ pool β P t X₁ X₂ E p hp hP hβ hs hX₁ hX₂ hE hple hchildren
  let R:=CubicEisenstein.primeSupport s.puncture
  have hR:∀I∈R,Prime I:=CenteredMomentNaturalRowSource.support_prime s.puncture
  let κ:={D:Finset (Ideal O)//D∈R.powerset}×
    {D:Finset (Ideal O)//D∈R.powerset}×{J:Finset α//J∈(Finset.univ:Finset α).powerset}
  let cf(z:O)(j:κ):=signedCoefficient (naturalCharacter s.character z) R j.1.val j.2.1.val j.2.2.val
    pool (fun i=> heightCoefficient (β i) t) P
  let f(z:O)(j:κ):=polynomial (naturalCharacter s.character z) false W₁
    (X₁/((∏I∈j.1.val,I).absNorm:ℝ)) 0 t *
    polynomial (naturalCharacter s.character z) false W₂
    (X₂/((∏I∈j.2.1.val,I).absNorm:ℝ)) 0 t *
    ∏i∈Finset.univ\j.2.2.val,naturalSlot (naturalCharacter s.character z) (pool i)
      (heightCoefficient (β i) t) (P i)
  let ρ(j:κ):=uniformMajorant R j.1.val j.2.1.val j.2.2.val bslot M
  let q(j:κ):=((∏I∈j.2.1.val,I).absNorm:ℝ)^(p/2)
  have hρ(j:κ):0≤ρ j:=uniformMajorant_nonneg _ _ _ _ _ _ (fun i _=> hM i)
  have hq(j:κ):0≤ q j:=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hn(D:Finset (Ideal O))(hD:D∈R.powerset):0<((∏I∈D,I).absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr (fun I hi=>(hR I (Finset.mem_powerset.mp hD hi)).ne_zero)))
  have hcf(z:O)(j:κ):‖cf z j‖≤ρ j:=by
    apply signedCoefficient_uniform _ R hR _ _ (Finset.mem_powerset.mp j.1.property)
      (Finset.mem_powerset.mp j.2.1.property) _ pool (fun i=> heightCoefficient (β i) t) P bslot M
      (fun i _=> hp i) (fun i _=> hP i) (fun i _=> hM i)
    · intro i _ I hI
      rw [heightCoefficient_norm _ _ _ (hp i I hI).ne_zero]
      exact hβ i I hI
    · intro i _ I hI hnz
      exact hs i I hI (left_ne_zero_of_mul hnz)
  have hsum(j:κ):Summable (fun z:O=> if (effectiveState s).radial.keep z then
      ‖f z j‖^2*(s.radial.profile (‖ringComplex z‖^2/s.radial.scale)).re else 0):=by
    obtain ⟨B,hB,hbound⟩:=slots_bounded (Finset.univ\j.2.2.val) pool (fun i=> heightCoefficient (β i) t) P
    exact pair_radial_summable (naturalCharacter s.character)
      (fun z=>∏i∈Finset.univ\j.2.2.val,naturalSlot (naturalCharacter s.character z) (pool i)
        (heightCoefficient (β i) t) (P i)) (fun _=> t) (fun _=> t) W₁ W₂ a b a b
      (X₁/((∏I∈j.1.val,I).absNorm:ℝ)) (X₂/((∏I∈j.2.1.val,I).absNorm:ℝ)) B hb hb
      (div_pos hX₁ (hn _ j.1.property)) (div_pos hX₂ (hn _ j.2.1.property)) hs₁ hs₂
      (fun z=> hbound _) (effectiveState s).radial.keep s.radial.profile s.radial.scale s.radial.scale_pos
  have hchild(j:κ):radialEnergy (fun z=> f z j) (effectiveState s).radial.keep
      s.radial.profile s.radial.scale≤ E*(q j)^2:=by
    have hh:=hchildren j.1.val j.1.property j.2.1.val j.2.1.property j.2.2.val j.2.2.property
    have hpow:(q j)^2=((∏I∈j.2.1.val,I).absNorm:ℝ)^p:=by
      dsimp only [q]
      rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
      congr 1
      norm_num
    rw [hpow]
    exact hh
  have he:=radial_weighted_energy cf f ρ q hρ hq (effectiveState s).radial.keep s.radial.profile
    s.radial.scale E s.radial.nonneg (fun z _=> hcf z) hE hsum hchild
  have hid(z:O):(∑j:κ,cf z j*f z j)=signedCommonSource s W₁ W₂ pool β P t X₁ X₂ z:=
    triple_sum R.powerset R.powerset (Finset.univ:Finset α).powerset
      (fun D₁ D₂ J=> signedCoefficient (naturalCharacter s.character z) R D₁ D₂ J
        pool (fun i=> heightCoefficient (β i) t) P *
        (polynomial (naturalCharacter s.character z) false W₁ (X₁/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
         polynomial (naturalCharacter s.character z) false W₂ (X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
         ∏i∈Finset.univ\J,naturalSlot (naturalCharacter s.character z) (pool i) (heightCoefficient (β i) t) (P i)))
  simp_rw [hid] at he
  rw [←original_energy_eq_signed s W₁ W₂ ha hs₁ hs₂ pool hp β P hP t X₁ X₂ hX₁ hX₂] at he
  have hm:(∑j:κ,ρ j*q j)≤ C*((∏I∈R,I).absNorm:ℝ)^(ε/2):=by
    exact (triple_sum R.powerset R.powerset (Finset.univ:Finset α).powerset
      (fun D₁ D₂ J=> uniformMajorant R D₁ D₂ J bslot M*((∏I∈D₂,I).absNorm:ℝ)^(p/2))).trans_le
      (hmass R hR (p/2) (by linarith))
  have hr:(((∏I∈R,I).absNorm:ℝ)^(ε/2))^2=(s.puncture.radical.absNorm:ℝ)^ε:=by
    rw [CenteredMomentAllocatedNaturalSource.primeSupport_product_radical s.puncture s.puncture_ne_zero]
    rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    norm_num
  exact he.trans ((mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun j _=> mul_nonneg (hρ j) (hq j))) hm 2) hE).trans_eq
    (by rw [mul_pow,hr]))

end CenteredMomentEnergyReferenceDeletionEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentEnergyReferenceScalarBounds
open HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource

lemma radical_power {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)(d:ℝ)(hd:0≤ d):
    (s.puncture.radical.absNorm:ℝ)^d≤ Z^(Bmask*d):=by
  have hh:=Real.rpow_le_rpow (Nat.cast_nonneg _) s.radical_bound hd
  simpa only [←Real.rpow_mul (zero_lt_one.trans_le s.base_ge_one).le] using hh

lemma conductor_power {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (Mcap d:ℝ)(hs:s.width≤ Mcap)(hd:0≤ d):
    (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d≤
      (max 1 ((fixedConductorFactor:ℝ)*bΦ))^d*Z^(Mcap*d):=by
  have hZ:0< Z:=zero_lt_one.trans_le s.base_ge_one
  have hM:0≤ Mcap:=s.width_nonneg.trans hs
  have hz:1≤ Z^Mcap:=Real.one_le_rpow s.base_ge_one hM
  have hc:1≤ max 1 ((fixedConductorFactor:ℝ)*bΦ):=le_max_left _ _
  have hbase:max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width)≤
      (max 1 ((fixedConductorFactor:ℝ)*bΦ))*Z^Mcap:=by
    apply max_le
    · nlinarith
    · apply le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hZ.le _))
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le s.base_ge_one hs)
        (zero_le_one.trans hc)
  have hh:=Real.rpow_le_rpow (zero_le_one.trans (le_max_left _ _)) hbase hd
  rw [Real.mul_rpow (zero_le_one.trans hc) (Real.rpow_nonneg hZ.le _),←Real.rpow_mul hZ.le] at hh
  exact hh

lemma radial_scale {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ):
    max 1 s.radial.scale≤ Z^s.width:=by
  rw [s.scale_eq]
  apply max_le (Real.one_le_rpow s.base_ge_one s.width_nonneg)
  apply Real.rpow_le_rpow_of_exponent_le s.base_ge_one
  exact le_add_of_nonneg_right s.character_nonneg

lemma physical_slot_product {α:Type*}[Fintype α](Z:ℝ)(hZ:1≤ Z)(w:α→ℝ)(Mcap:ℝ)
    (hwidth:(∑i,w i)≤ Mcap): (∏i,Z^(w i))≤ Z^Mcap:=by
  rw [←Real.rpow_sum_of_pos (zero_lt_one.trans_le hZ)]
  exact Real.rpow_le_rpow_of_exponent_le hZ hwidth

lemma short_slot_mass {α:Type*}[Fintype α]{Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (Mcap:ℝ)(hs:s.width≤ Mcap)(w:α→ℝ)(hwidth:(∑i,w i)≤ Mcap):
    max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))≤ Z^(s.width+5*Mcap/4):=by
  have hz:0< Z:=zero_lt_one.trans_le s.base_ge_one
  calc
    _≤ Z^s.width*Z^(Mcap/4)*Z^Mcap:=by
      apply mul_le_mul (mul_le_mul (radial_scale s)
        (Real.rpow_le_rpow_of_exponent_le s.base_ge_one (by linarith))
        (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _))
        (physical_slot_product Z s.base_ge_one w Mcap hwidth)
        (Finset.prod_nonneg (fun i _=> Real.rpow_nonneg hz.le _)) (by positivity)
    _=Z^(s.width+5*Mcap/4):=by rw [←Real.rpow_add hz,←Real.rpow_add hz];congr 1;ring

lemma log_interval (Z L d:ℝ)(hZ:1≤ Z)(hL:0≤ L)(hd:0< d):
    1+2*(L*Real.log Z)≤(1+2*L/d)*Z^d:=by
  have hlog:=Real.log_le_rpow_div (zero_le_one.trans hZ) hd
  have hone:=Real.one_le_rpow hZ hd.le
  have hh:=mul_le_mul_of_nonneg_left hlog (show 0≤2*L by positivity)
  calc
    _≤ Z^d+2*L*(Z^d/d):=by nlinarith
    _=(1+2*L/d)*Z^d:=by ring

end CenteredMomentEnergyReferenceScalarBounds

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentEnergyReferenceScalarReserve
open HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEnergyReferenceScalarBounds

theorem ledger_bound (Mcap Bmask bΦ L d saving ε:ℝ)
    (hM:0≤ Mcap)(_hB:0≤ Bmask)(hL:0≤ L)(hd:0< d)
    (hmain:d*(Bmask+Mcap+2)≤ε)
    (herror:Bmask*d+Mcap*(2*d)-2*saving+5*Mcap/4≤ε):
    ∃C:ℝ,0< C ∧ ∀Z:ℝ,1≤ Z → ∀s:NaturalState Z Bmask bΦ,s.width≤ Mcap →
      ∀(α:Type*)[Fintype α](w:α→ℝ),(∑i,w i)≤ Mcap →
      (s.puncture.radical.absNorm:ℝ)^d*
        (Z^(s.width+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
           (1+2*(L*Real.log Z))*Z^(s.width+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
           max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))) ≤ C*Z^(s.width+ε):=by
  let A:ℝ:=max 1 ((fixedConductorFactor:ℝ)*bΦ)
  let B:ℝ:=1+2*L/d
  have hA:0< A:=zero_lt_one.trans_le (le_max_left _ _)
  have hBpos:0< B:=by dsimp only [B];positivity
  refine ⟨1+A^d*B+A^(2*d),by positivity,?_⟩
  intro Z hZ s hs α inst w hw
  have hz:0< Z:=zero_lt_one.trans_le hZ
  have hlog:0≤ Real.log Z:=Real.log_nonneg hZ
  have hr:=radical_power s d hd.le
  have hc:=conductor_power s Mcap d hs hd.le
  have hc₂:=conductor_power s Mcap (2*d) hs (by positivity)
  have hl:=log_interval Z L d hZ hL hd
  have hm:=short_slot_mass s Mcap hs w hw
  have hdirect:(s.puncture.radical.absNorm:ℝ)^d*Z^(s.width+d)≤ Z^(s.width+ε):=by
    calc
      _≤ Z^(Bmask*d)*Z^(s.width+d):=mul_le_mul_of_nonneg_right hr (Real.rpow_nonneg hz.le _)
      _=Z^(s.width+d*(Bmask+1)):=by rw [←Real.rpow_add hz];congr 1;ring
      _≤ _:=Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)
  have hreflect:(s.puncture.radical.absNorm:ℝ)^d*
      ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
        (1+2*(L*Real.log Z))*Z^(s.width+d))≤ A^d*B*Z^(s.width+ε):=by
    calc
      _≤ Z^(Bmask*d)*(A^d*Z^(Mcap*d)*(B*Z^d)*Z^(s.width+d)):=by
        gcongr
      _=A^d*B*Z^(s.width+d*(Bmask+Mcap+2)):=by
        calc
          _=A^d*B*(Z^(Bmask*d)*Z^(Mcap*d)*Z^d*Z^(s.width+d)):=by ring
          _=_:=by simp only [←Real.rpow_add hz];congr 2;ring
      _≤ _:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)
  have herrorTerm:(s.puncture.radical.absNorm:ℝ)^d*
      ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
        max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i)))≤ A^(2*d)*Z^(s.width+ε):=by
    calc
      _=(s.puncture.radical.absNorm:ℝ)^d*
        ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          (max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i)))):=by ring
      _≤ Z^(Bmask*d)*(A^(2*d)*Z^(Mcap*(2*d))*Z^(-2*saving)*Z^(s.width+5*Mcap/4)):=by
        gcongr
      _=A^(2*d)*Z^(s.width+(Bmask*d+Mcap*(2*d)-2*saving+5*Mcap/4)):=by
        calc
          _=A^(2*d)*(Z^(Bmask*d)*Z^(Mcap*(2*d))*Z^(-2*saving)*Z^(s.width+5*Mcap/4)):=by ring
          _=_:=by simp only [←Real.rpow_add hz];congr 1;congr 1;ring
      _≤ _:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)
  calc
    _≤ Z^(s.width+ε)+A^d*B*Z^(s.width+ε)+A^(2*d)*Z^(s.width+ε):=by
      simpa only [mul_add] using add_le_add (add_le_add hdirect hreflect) herrorTerm
    _=_:=by ring

theorem exists_reference_reserve (rho ε Mcap Bmask bΦ:ℝ)
    (hrho:0< rho)(hε:0<ε)(hM:0≤ Mcap)(hB:0≤ Bmask):
    ∃d xi saving L C:ℝ,0< d ∧ 0< xi ∧ 0< saving ∧ 0< C ∧
      xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧
      ∀Z:ℝ,1≤ Z → ∀s:NaturalState Z Bmask bΦ,s.width≤ Mcap →
      ∀(α:Type*)[Fintype α](w:α→ℝ),(∑i,w i)≤ Mcap →
      (s.puncture.radical.absNorm:ℝ)^d*
        (Z^(s.width+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
           (1+2*(L*Real.log Z))*Z^(s.width+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
           max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))) ≤ C*Z^(s.width+ε):=by
  let d:=ε/(4*(Bmask+Mcap+2))
  let xi:=rho/100
  let saving:=2*Mcap+Bmask*d+2*Mcap*d+1
  let L:=Mcap+Bmask+xi+1
  have hd:0< d:=by dsimp only [d];positivity
  have hxi:0< xi:=by dsimp only [xi];positivity
  have hsave:0< saving:=by dsimp only [saving];positivity
  have hL:0≤ L:=by dsimp only [L];positivity
  have hmain:d*(Bmask+Mcap+2)≤ε:=by
    dsimp only [d]
    have hp:0< Bmask+Mcap+2:=by positivity
    field_simp
    nlinarith
  have herror:Bmask*d+Mcap*(2*d)-2*saving+5*Mcap/4≤ε:=by
    dsimp only [saving]
    nlinarith [mul_nonneg hB hd.le,mul_nonneg hM hd.le]
  obtain ⟨C,hC,hledger⟩:=ledger_bound Mcap Bmask bΦ L d saving ε hM hB hL hd hmain herror
  exact ⟨d,xi,saving,L,C,hd,hxi,hsave,hC,le_rfl,by dsimp only [L];linarith,hledger⟩

end CenteredMomentEnergyReferenceScalarReserve

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentEnergyStageReserve
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEnergyReferenceScalarReserve

theorem exists_separated_reference_reserve (rho ε Mcap Bmask bΦ:ℝ)
    (hrho:0< rho)(hε:0<ε)(hM:0≤ Mcap)(hB:0≤ Bmask):
    ∃d xi saving L C:ℝ,0< d ∧ 0< xi ∧ 0< saving ∧ 0< C ∧
      xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧
      ∀e:ℝ,0≤ e → ∀Z:ℝ,1≤ Z → ∀s:NaturalState Z Bmask bΦ,s.width≤ Mcap →
      ∀(α:Type*)[Fintype α](w:α→ℝ),(∑i,w i)≤ Mcap →
      (s.puncture.radical.absNorm:ℝ)^d*(
        Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(L*Real.log Z))*Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i)))≤
        C*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,saving,L,C,hd,hxi,hs,hC,hxr,hL,hledger⟩:=
    exists_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hB
  refine ⟨d,xi,saving,L,C,hd,hxi,hs,hC,hxr,hL,?_⟩
  intro e he Z hZ s hwidth α _ w hw
  have hz:0< Z:=zero_lt_one.trans_le hZ
  have hze:1≤ Z^e:=Real.one_le_rpow hZ he
  have hp:Z^(s.width+e)≤ Z^e*Z^(s.width+d):=by
    rw [←Real.rpow_add hz]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  let A:ℝ:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))
  let B:ℝ:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))
  have hLp:0≤ L:=by linarith
  have hlog:0≤ Real.log Z:=Real.log_nonneg hZ
  have hA:0≤ A:=by dsimp [A];positivity
  have hB0:0≤ B:=by dsimp [B];positivity
  have hb:B≤ Z^e*B:=by nlinarith
  have hh:=add_le_add (add_le_add hp (mul_le_mul_of_nonneg_left hp hA)) hb
  have hrad:0≤(s.puncture.radical.absNorm:ℝ)^d:=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hh':=(mul_le_mul_of_nonneg_left hh hrad)
  have hend:=mul_le_mul_of_nonneg_left (hledger Z hZ s hwidth α w hw)
    (Real.rpow_nonneg hz.le e)
  calc
    _≤ Z^e*((s.puncture.radical.absNorm:ℝ)^d*(Z^(s.width+d)+A*Z^(s.width+d)+B)):=by
      convert hh' using 1 <;> first | rfl | (dsimp [A,B]; ring)
    _≤ Z^e*(C*Z^(s.width+ε)):=by
      exact hend
    _=C*Z^(s.width+e+ε):=by
      rw [mul_left_comm,←Real.rpow_add hz]
      congr 2
      ring

lemma inherited_loss_budget (incoming overhead final:ℝ)
    (hin:incoming≤ final/2)(hover:overhead≤ final/2):incoming+overhead≤ final:=by
  linarith

end CenteredMomentEnergyStageReserve

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentEnergyStageReserveBounded
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEnergyStageReserve

theorem exists_bounded_separated_reference_reserve (rho ε Mcap Bmask bΦ:ℝ)
    (hrho:0< rho)(hε:0<ε)(hM:0≤ Mcap)(hB:0≤ Bmask):
    ∃d xi saving L C:ℝ,0< d ∧ 0< xi ∧ 0< saving ∧ 0< C ∧
      xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧ L≤ Mcap+Bmask+rho/100 ∧
      ∀e:ℝ,0≤ e → ∀Z:ℝ,1≤ Z → ∀s:NaturalState Z Bmask bΦ,s.width≤ Mcap →
      ∀(α:Type*)[Fintype α](w:α→ℝ),(∑i,w i)≤ Mcap →
      (s.puncture.radical.absNorm:ℝ)^d*(
        Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(L*Real.log Z))*Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i)))≤
        C*Z^(s.width+e+ε) :=by
  obtain ⟨d,xi,saving,L,C,hd,hxi,hs,hC,hxr,hL,hledger⟩:=
    exists_separated_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hB
  refine ⟨d,xi,saving,Mcap+Bmask+xi,C,hd,hxi,hs,hC,hxr,le_refl _,by linarith,?_⟩
  intro e he Z hZ s hwidth α _ w hw
  apply le_trans _ (hledger e he Z hZ s hwidth α w hw)
  have hlog:0≤ Real.log Z:=Real.log_nonneg hZ
  have hLp:0≤ Mcap+Bmask+xi:=by linarith
  gcongr

end CenteredMomentEnergyStageReserveBounded

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace CenteredMomentEnergyReferenceDeletionCapacity
open HeckeFamily CenteredMomentEnergyReferenceDeletionBudget
open CenteredMomentEnergyReferenceState CenteredMomentEnergyBands

local notation "O"=> Eisenstein.O

lemma deleted_short_length (Z M:ℝ)(hZ:1< Z)(hM:0≤ M)
    (D:Finset (Ideal O))(hD:∀I∈D,Prime I):
    length Z (comparisonFirst Z M/((∏I∈D,I).absNorm:ℝ))≤ M/4:=by
  have hn:=product_norm_ge_one D hD
  have hY:1≤ comparisonFirst Z M:=Real.one_le_rpow hZ.le (by linarith)
  have hdiv:comparisonFirst Z M/((∏I∈D,I).absNorm:ℝ)≤ comparisonFirst Z M:=
    div_le_self (zero_le_one.trans hY) hn
  have hm:max 1 (comparisonFirst Z M/((∏I∈D,I).absNorm:ℝ))≤ comparisonFirst Z M:=max_le hY hdiv
  have he:=Real.logb_le_logb_of_le hZ
    (lt_of_lt_of_le zero_lt_one (le_max_left 1 _)) hm
  simpa only [length,comparisonFirst,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using he


end CenteredMomentEnergyReferenceDeletionCapacity
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentEnergyReferenceLowBranchGeometry
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceDeletionBudget CenteredMomentEnergyReferenceDeletionCapacity
local notation "O"=> Eisenstein.O

lemma slot_budgets (M total ell kappa:ℝ)(_hM:0≤ M)(hell:0≤ ell)(hk:3/4≤ kappa)
    (hlarge:5*M/6≤ total+ell)(hcap:total+ell+(6*kappa-1)*ell≤ M):
    ell≤ M/21 ∧ (6*kappa-1)*ell≤ M/6:=by
  have hkell:7/2*ell≤(6*kappa-1)*ell:=mul_le_mul_of_nonneg_right (by linarith) hell
  constructor <;> nlinarith

theorem reflected_low (M short along ell z kappa xi reflected:ℝ)
    (hM:0≤ M)(_hs:0≤ short)(hsM:short≤ M/4)(_hell:0≤ ell)(_hz:0≤ z)(hze:z≤ ell)
    (hk:3/4≤ kappa)(he:ell≤ M/21)(hbudget:(6*kappa-1)*ell≤ M/6)(hxi:0≤ xi)
    (hhigh:5*M/6< short+max 0 along+z)
    (href:reflected≤ max 0 (M-along+xi)):
    0< along ∧ reflected+short+z≤16*M/21+xi ∧
      reflected+short+6*kappa*z≤13*M/14+xi:=by
  have haz:0< along:=by
    by_contra hn
    have ha:along≤0:=le_of_not_gt hn
    rw [max_eq_left ha] at hhigh
    linarith
  rw [max_eq_right haz.le] at hhigh
  have hzbudget:(6*kappa-1)*z≤ M/6:=
    (mul_le_mul_of_nonneg_left hze (by linarith)).trans hbudget
  have hzcap:z≤ M/21:=hze.trans he
  refine ⟨haz,?_⟩
  by_cases hr:0≤ M-along+xi
  · rw [max_eq_right hr] at href
    constructor <;> nlinarith
  · rw [max_eq_left (le_of_not_ge hr)] at href
    constructor <;> nlinarith

theorem deleted_reference_cases (Z M X₁ X₂ ell z kappa xi reflected:ℝ)
    (hZ:1< Z)(hM:0≤ M)(hX₁:0< X₁)(hX₂:0< X₂)(hell:0≤ ell)(hz:0≤ z)(hze:z≤ ell)
    (hk:3/4≤ kappa)(hxi:0≤ xi)
    (hlarge:5*M/6≤ Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*kappa-1)*ell≤ M)
    (D₁ D₂:Finset (Ideal O))(hD₁:∀I∈D₁,Prime I)(hD₂:∀I∈D₂,Prime I)
    (href:reflected≤ max 0 (M-Real.logb Z
      (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+xi)):
    let short:=length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ));
    let long:=length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ));
    (short+long+z≤5*M/6 ∧ short+long+6*kappa*z≤ M) ∨
    (0< Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ)) ∧
      reflected+short+z≤16*M/21+xi ∧ reflected+short+6*kappa*z≤13*M/14+xi):=by
  dsimp only
  have hg:=balanced_reference_geometry Z M X₁ X₂ ell kappa hZ hM hX₁ hX₂ hell hk hlarge hcap
  have hpos:=comparison_positive Z M X₁ X₂ (zero_lt_one.trans hZ) hX₁ hX₂
  have hn₂:=product_norm_ge_one D₂ hD₂
  have hlongpos:=div_pos hpos.2 (zero_lt_one.trans_le hn₂)
  have hshort:=deleted_short_length Z M hZ hM D₁ hD₁
  have hshort0:=length_nonneg Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ)) hZ
  have hlong:length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))≤
      Real.logb Z (comparisonSecond Z M X₁ X₂):=by
    have hY:1≤ comparisonSecond Z M X₁ X₂:=hg.2.1.trans hg.2.2.1
    have hdiv:=div_le_self hpos.2.le hn₂
    exact Real.logb_le_logb_of_le hZ (lt_of_lt_of_le zero_lt_one (le_max_left 1 _)) (max_le hY hdiv)
  by_cases hlo:length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ))+
      length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+z≤5*M/6
  · refine Or.inl ⟨hlo,?_⟩
    have hzcap:=mul_le_mul_of_nonneg_left hze (by linarith:0≤6*kappa)
    rw [hg.2.2.2.1] at hlong
    nlinarith
  · apply Or.inr
    obtain ⟨he,hbudget⟩:=slot_budgets M (Real.logb Z (X₁*X₂)) ell kappa hM hell hk hlarge hcap
    apply reflected_low M _ _ ell z kappa xi reflected hM hshort0 hshort hell hz hze hk he hbudget hxi _ href
    rw [←CenteredMomentEnergyInputParentCapacity.length_eq_max_log Z _ hZ hlongpos]
    exact lt_of_not_ge hlo

lemma reflected_low_admissible (M xi short reflected z kappa:ℝ)
    (hxi:xi≤ M/14)(ht:reflected+short+z≤16*M/21+xi)
    (hc:reflected+short+6*kappa*z≤13*M/14+xi):
    reflected+short+z≤5*M/6 ∧ reflected+short+6*kappa*z≤ M:=by
  constructor <;> linarith

end CenteredMomentEnergyReferenceLowBranchGeometry

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentEnergyReferenceLowWindow
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceLowBranchGeometry
local notation "O"=> Eisenstein.O

lemma reflection_window_length (Z R x:ℝ)(hZ:1< Z)(hR:0≤ R)
    (hx:x∈Set.Icc 0 (R*Real.log Z)):
    length Z (Real.exp x)≤ R ∧ Real.exp x≤ Z^R:=by
  have hlog:0< Real.log Z:=Real.log_pos hZ
  have hexp:Real.exp x≤ Z^R:=by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hZ)]
    apply Real.exp_le_exp.mpr
    simpa [mul_comm] using hx.2
  refine ⟨?_,hexp⟩
  have hmax:max 1 (Real.exp x)≤ Z^R:=
    max_le (Real.one_le_rpow hZ.le hR) hexp
  have hl:=Real.logb_le_logb_of_le hZ
    (lt_of_lt_of_le zero_lt_one (le_max_left 1 (Real.exp x))) hmax
  simpa only [length,Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] using hl

theorem deleted_reference_window (Z M X₁ X₂ ell z kappa xi:ℝ)
    (hZ:1< Z)(hM:0≤ M)(hX₁:0< X₁)(hX₂:0< X₂)(hell:0≤ ell)(hz:0≤ z)(hze:z≤ ell)
    (hk:3/4≤ kappa)(hxi:0≤ xi)(hxiM:xi≤ M/14)
    (hlarge:5*M/6≤ Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*kappa-1)*ell≤ M)
    (D₁ D₂:Finset (Ideal O))(hD₁:∀I∈D₁,Prime I)(hD₂:∀I∈D₂,Prime I):
    let short:=length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ));
    let along:=Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ));
    (short+length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+z≤5*M/6 ∧
      short+length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+6*kappa*z≤ M) ∨
    (0< along ∧ ∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
      length Z (Real.exp x)+short+z≤5*M/6 ∧
      length Z (Real.exp x)+short+6*kappa*z≤ M):=by
  dsimp only
  let along:=Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))
  rcases deleted_reference_cases Z M X₁ X₂ ell z kappa xi (max 0 (M-along+xi))
    hZ hM hX₁ hX₂ hell hz hze hk hxi hlarge hcap D₁ D₂ hD₁ hD₂ le_rfl with h|h
  · exact Or.inl h
  · refine Or.inr ⟨h.1,?_⟩
    intro x hx
    have hh:=reflection_window_length Z (max 0 (M-along+xi)) x hZ (le_max_left _ _) hx
    have hb:=reflected_low_admissible M xi _ (max 0 (M-along+xi)) z kappa hxiM h.2.1 h.2.2
    constructor <;> linarith [hh.1]

end CenteredMomentEnergyReferenceLowWindow

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentEnergyReferenceLowChild
open HeckeFamily HeckeDyadic 
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentFiniteProfileExceptional InversePrincipalEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentAllocatedNaturalRadial
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
local notation "O"=> Eisenstein.O

def unitBudgetState {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)(hB:0≤ Bmask):
    NaturalState Z Bmask bΦ:=
  {unpuncturedState s with
    puncture_bound:=by simpa only [unpuncturedState,map_one,Nat.cast_one] using Real.one_le_rpow s.base_ge_one hB}

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem reflected_child_from_low
    (Wslot:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hlow:PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
      Mcap ε κ Z η₀ Q degree S C)
    (hB:0≤ Bmask)(ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)
    (F:Finset α)(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ)
    (hw:∀i,0≤ w i)(hwL:∀i,w i≤ Lslot)(hσlo:∀i,lo≤σ i)(hσhi:∀i,σ i≤ hi)
    (hheight:0≤ height)(hfreq:∀i,|freq i|≤ height)
    (s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=internalQ Q η₀)(hs:s.width≤ Mcap)
    (Wshort:𝓢(ℝ,ℂ))(hsW:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b)
    (j k:Fin 2)(v X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)(hc₁:X₁≤ Z^L)(hc₂:X₂≤ Z^L)
    (hcapacity:length Z X₁+length Z X₂+6*κ*(∑i∈F,w i)≤ s.width)
    (hsmall:length Z X₁+length Z X₂+(∑i∈F,w i)≤5*s.width/6):
    radialEnergy (fun z=> polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) X₂ 0 t *
      ∏i∈F,naturalSlot (naturalCharacter s.character z)
        (primePool M H bslot (Z^(w i)))
        (heightCoefficient (fun I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i)))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*
        ((reflectionProfiles ha hlo hhi Wshort hsW j k v t).control S)^2*
        (1+|t|+height)^degree*Z^(s.width+ε):=by
  have hZ:0< Z:=zero_lt_one.trans_le s.base_ge_one
  have hh:=hlow F (fun i=>θ i) (fun i=> w i) (fun i=>σ i) (fun i=> t+freq i)
    0 (|t|+height) (fun i=> hw i) (fun i=> hwL i) (fun i=> hσlo i) (fun i=> hσhi i)
    (add_nonneg (abs_nonneg t) hheight)
    (fun i=>(abs_add_le t (freq i)).trans (add_le_add le_rfl (hfreq i)))
    (unitBudgetState s hB) hQ hs (reflectionProfiles ha hlo hhi Wshort hsW j k v t)
    X₁ X₂ hX₁ hX₂ hc₁ hc₂
    (by simpa only [Finset.sum_coe_sort,unitBudgetState,unpuncturedState,NaturalState.width] using hcapacity)
    (by simpa only [Finset.sum_coe_sort,unitBudgetState,unpuncturedState,NaturalState.width] using hsmall)
  rw [reflected_child_ray_energy s ha hlo hhi Wshort hsW F
    (fun i=> primePool M H bslot (Z^(w i)))
    (fun i=> relativeCharacter M H hH η₀ (θ i)) (fun _=> Wslot)
    (fun i=> Z^(w i)) σ freq
    (fun i _ I hI=>(Finset.mem_filter.mp hI).2.1)
    (fun i _=> Real.rpow_pos_of_pos hZ _) j k v t X₁ X₂ hX₁ hX₂]
  simpa only [unitBudgetState,unpuncturedState,NaturalState.width,
    NaturalState.mask,effectiveState,effectiveRadial,abs_zero,add_zero,add_assoc] using hh

end CenteredMomentEnergyReferenceLowChild

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentEnergyReferenceLowMoments
open HeckeFamily HeckeDyadic 
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentFiniteProfileExceptional InversePrincipalEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentAllocatedNaturalRadial
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
local notation "O"=> Eisenstein.O

open CenteredMomentEnergyReferenceLowChild CenteredMomentEnergyReferenceLowControl
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem reflected_child_uniform_from_low
    (a b:ℝ)(ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)
    (degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃D:ℝ,0< D ∧
    ∀(Wslot:ℝ→ℂ)(bslot bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(C:ℝ)(_hC:0≤ C)
    (_hlow:PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
      Mcap ε κ Z η₀ Q degree S C)
    (_hB:0≤ Bmask)
    (F:Finset α)(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ)
    (_hw:∀i,0≤ w i)(_hwL:∀i,w i≤ Lslot)(_hσlo:∀i,lo≤σ i)(_hσhi:∀i,σ i≤ hi)
    (_hheight:0≤ height)(_hfreq:∀i,|freq i|≤ height)
    (s:NaturalState Z Bmask bΦ)(_hQ:s.fixedModulus=internalQ Q η₀)(_hs:s.width≤ Mcap)
    (Wshort:𝓢(ℝ,ℂ))(_hsW:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b)
    (j k:Fin 2)(v X₁ X₂:ℝ)(_hX₁:0< X₁)(_hX₂:0< X₂)(_hc₁:X₁≤ Z^L)(_hc₂:X₂≤ Z^L)
    (_hcapacity:length Z X₁+length Z X₂+6*κ*(∑i∈F,w i)≤ s.width)
    (_hsmall:length Z X₁+length Z X₂+(∑i∈F,w i)≤5*s.width/6),
    radialEnergy (fun z=> polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) X₂ 0 t *
      ∏i∈F,naturalSlot (naturalCharacter s.character z)
        (primePool M H bslot (Z^(w i)))
        (heightCoefficient (fun I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i)))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      (C*diagonalControl s.radial.profile*D*(sourceControl T Wshort)^2*
        (1+|t|+height)^(degree+2*n)*Z^(s.width+ε))*(1+‖v‖)^(2*n) :=by
  obtain ⟨n,T,D,hD,hd⟩:=reflected_child_control a b ha hlo hhi S degree
  refine ⟨n,T,D,hD,?_⟩
  intro Wslot bslot bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q C hC hlow hB
    F θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs Wshort hsW
    j k v X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity hsmall
  have hh:=reflected_child_from_low M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
    Mcap ε κ Z η₀ Q degree S C hlow hB ha hlo hhi F θ w σ freq t height hw hwL
    hσlo hσhi hheight hfreq s hQ hs Wshort hsW j k v X₁ X₂ hX₁ hX₂ hc₁ hc₂
    hcapacity hsmall
  have hb:=hd Wshort hsW j k v t height hheight
  have hp:0≤ C*diagonalControl s.radial.profile:=mul_nonneg hC (by
    unfold diagonalControl
    positivity)
  have hz:0≤ Z^(s.width+ε):=(Real.rpow_pos_of_pos (zero_lt_one.trans_le s.base_ge_one) _).le
  have hmul:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hp) hz
  apply hh.trans
  convert hmul using 1 <;> first | rfl | ring

end CenteredMomentEnergyReferenceLowMoments

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace CenteredMomentEnergyReferenceHomogeneous
open HeckeFamily HeckeDyadic  InversePrincipalEnergy
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentUniformReflectionProfile CenteredExceptionalProfile CenteredMomentLattice
local notation "O"=> Eisenstein.O

open CenteredMomentEnergyReferenceReflection CenteredMomentFiniteProfileExceptional

theorem natural_reference_reflection_homogeneous (a b bΦ epsilon xi saving L:ℝ)
    (ha:0< a)(hb:0≤ b)(hbΦ:0< bΦ)(hepsilon:0< epsilon)(hxi:0< xi)
    (B J:ℕ)(hB:2≤ B):
    ∃n:ℕ,∃S:Finset (ℕ×ℕ),∃C D:ℝ,0< C ∧ 0< D ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Bmask:ℝ)(s:NaturalState Z Bmask bΦ)
        (Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(α:Type*)(F:Finset α)(pool:α→Finset (Ideal O))
        (β:α→Ideal O→ℂ)(P:α→ℝ)(t along bshort E:ℝ),
      s.width≤ L+along → 0≤ E →
      (∀v:ℝ,∀j k:Fin 2,∀x∈Set.Icc 0 (max 0 (s.width-along+xi)*Real.log Z),
        radialEnergy (fun z=> polynomial (naturalCharacter s.character z) false
          (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (naturalCharacter s.character z) false (scaleTest Wshort k)
            (Z^bshort) 0 t *
          ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
          (effectiveState s).radial.keep s.radial.profile s.radial.scale
          ≤ E*(1+‖v‖)^(2*J)) →
      radialEnergy (fun z=> polynomial (naturalCharacter s.character z) false Wlong
          (Z^along) 0 t *
          polynomial (naturalCharacter s.character z) false Wshort (Z^bshort) 0 t *
          ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
          (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*(1+‖t‖)^(2*n)*
          (1+2*(max 0 (s.width-along+xi)*Real.log Z))*E +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*(1+‖t‖)^(2*n)*Z^(-2*saving)*
          radialEnergy (fun z=> polynomial (naturalCharacter s.character z) false Wshort
            (Z^bshort) 0 t *
            ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
            (effectiveState s).radial.keep s.radial.profile s.radial.scale:=by
  obtain ⟨H,C,D,hC,hD,h⟩:=CenteredMomentUniformRadialComparison.actual_original_radial_comparison
    epsilon ((fixedConductorFactor:ℝ)*bΦ) xi saving L hepsilon
    (mul_pos conductorFactor_pos hbΦ) hxi B J hB
  obtain ⟨n,T,Ct,hCt,hprofile⟩:=
    CenteredMomentFiniteProfileExceptional.normPowerProfile_source_control a b ha H
  let S:=T∪{(0,0)}
  have hS:(0,0)∈S:=by simp [S]
  refine ⟨n,S,C*Ct^2,D*Ct^2,by positivity,by positivity,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask s Wlong Wshort hsLong hsShort α F pool β P t along bshort E hlength hE hchildren
  by_cases hzero:sourceControl S Wlong=0
  · have hw:=sourceControl_zero S hS Wlong hzero
    subst Wlong
    simp [polynomial,HeckeDyadic.summand,radialEnergy]
  have hpos:0< sourceControl S Wlong:=lt_of_le_of_ne (sourceControl_nonneg S Wlong) (Ne.symm hzero)
  let G:=normPowerProfile Wlong a b ha hsLong (Wlong.smooth ⊤) t
  let Src:=Ct*(S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)*(1+‖t‖)^n
  have hSrc:0< Src:=mul_pos (mul_pos hCt hpos) (by positivity)
  have hcontrol:sourceControl T Wlong≤ sourceControl S Wlong:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left:T⊆T∪{(0,0)})) Wlong
  have hnorm:H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G≤ Src:=
    (hprofile Wlong hsLong t).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcontrol hCt.le) (by positivity))
  obtain ⟨Pbound,hPbound,hbound⟩:=CenteredMomentCommonMaskRadialEnergy.slots_bounded F pool β P
  have hh:=hZ.2 (fun _=> G) (naturalCharacter s.character)
    (fun z=>∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
    (fun _=> t) (effectiveState s).radial.keep s.radial.profile s.radial.scale Pbound
    Wshort a b s.width along bshort E Src
    (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))
    s.radial.scale_pos s.radial.nonneg (fun z=> hbound _)
    (effective_character_nonprincipal s) hb hsShort (Wshort.smooth ⊤)
    hlength (effective_character_cap s hbΦ.le) hE hSrc (fun _ _=> hnorm)
    (le_max_left _ _) (fun z hz=>(effective_character_cap s hbΦ.le z hz).trans (le_max_right _ _))
    hchildren
  have hG:(G:ℝ→ℂ)=normPowerProfile Wlong a b ha hsLong (Wlong.smooth ⊤) t:=rfl
  simp only [hG,CenteredMomentNaturalMaskedFloor.twist_polynomial _ Wlong a b ha hsLong t] at hh
  apply hh.trans_eq
  dsimp only [Src]
  rw [show (1+‖t‖)^(2*n)=((1+‖t‖)^n)^2 by rw [Nat.mul_comm 2 n,pow_mul]]
  ring

end CenteredMomentEnergyReferenceHomogeneous

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

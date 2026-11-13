/-
First-stage loss budgets adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.SecondExceptionalFamilies
import GaloisForLFunctions.MetaplecticMobiusDescent.Energy.EnergyBands

/-!
# First-stage loss budgets

Gaussian profile weight losses, natural source admission and low source inputs; paid first-stage
loss budgets and source parameters; column pairings and physical normalization.
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

namespace CenteredMomentEnergyNaturalLowSourceBound
open HeckeFamily  InversePrincipalEnergy
open CenteredMomentCommonRadialData CenteredMomentEnergyNaturalInputMatches
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyZeroComparison CenteredMomentEnergyOriginalProfileControl
open CenteredMomentEnergyLowFixedRadialEntry CenteredMomentEnergyInputParentCapacity
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentAmplificationChildInput CenteredMomentInductionEnergy
open CenteredMomentEnergyBands CenteredMomentSecondHeightFamily
open CenteredMomentPrimeSlot CenteredMomentNaturalFixedRaySource HeckeDyadic HeckePrimeAnnular
local notation "O" => Eisenstein.O
local instance (Q:Ideal O)[NeZero Q]:Finite (O ⧸ Q):=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne Q)
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=
  CenteredMomentEnergyOriginalSource.energyOriginalSourceDecidableSum

section Source
variable (Q:Ideal O)[NeZero Q]
variable (H:Subgroup (O⧸Q)ˣ)(hH:RayOrthogonality.globalUnits Q≤ H)
variable (η₀:Character)(θ:ι→RayQuotient.Characters Q H)
variable (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0< aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:ι→ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(state:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0< a)
variable (t X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)

def sourceInput : Input ι :=
  input Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ
    state p ha t X₁ X₂ X₁ X₂ hX₁ hX₂ hX₁ hX₂ rfl

def zeroSourceInput : Input ι :=
  zeroInput (sourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂)
    (CenteredMomentEnergyLowFixedRadialEntry.support_zero _ a b ha (p.support 0))
    (CenteredMomentEnergyLowFixedRadialEntry.support_zero _ a b ha (p.support 1))
end Source

private lemma control_mono {a b:ℝ}(p:Profiles a b)(S:Finset (ℕ×ℕ)):
    p.control S≤ p.control (insert (0,0) S):=by
  unfold Profiles.control
  exact mul_le_mul
    (Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_insert _ _)) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_insert _ _)) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

theorem natural_low_source_bound
    (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi a b bΦ Mcap εdiag ξ saving:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤ bslot)(ha:0< a)(hb:0≤ b)(hbΦ:0< bΦ)(hMcap:0≤ Mcap)
    (hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧ ∃Cfixed:ℝ,0< Cfixed ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
    ∀(Q:Ideal O)[NeZero Q](H:Subgroup (O⧸Q)ˣ)(hH:RayOrthogonality.globalUnits Q≤ H),
    ∀(η₀:Character)(θ:ι→RayQuotient.Characters Q H),
    ∀(w σ freq:ι→ℝ), (∀i,0≤ w i) → ∀hσ:∀i,σ i∈Set.Icc lo hi,
    ∀(Bmask:ℝ)(state:NaturalState Z Bmask bΦ)(p:Profiles a b)(t X₁ X₂:ℝ),
    ∀hX₁:0< X₁,∀hX₂:0< X₂,∀κ:ℝ,1/6≤κ →
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ Mcap →
    ∀(S:Finset (ℕ×ℕ))(J:ℕ)(Cphysical height e:ℝ),0≤ Cphysical →0≤ height →
    εdiag≤ e → -saving≤ e →
    physicalMass (zeroSourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂) state.puncture 1 fixedBadMask 1
      Ψ state.radial.scale Z ξ /
      volume (sourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
        w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂) ≤
      Cphysical*(p.control S)^2*(1+|t|+height)^J*Z^(state.width+e) →
    energy state.character state.mask 1 t (p.profile 0) (p.profile 1)
      (fun i=> primePool Q H bslot (Z^(w i)))
      (fun i I=> idealCoeff (relativeCharacter Q H hH η₀ (θ i)) I*
        annularWeight W (Z^(w i)) (σ i) (freq i) I)
      (fun i=> Z^(w i)) X₁ X₂ state.radial.keep state.radial.profile state.radial.scale ≤
      Cfixed*(Cphysical+1)*diagonalControl state.radial.profile*
        (p.control (insert (0,0) S))^2*(1+|t|+height)^J*Z^(state.width+e):=by
  obtain ⟨Ψ,hΨs,hΨn,Sd,St,Cd,Ct,hCd,hCt,hred⟩:=
    original_low_reduction (ι:=ι) bΦ hbΦ (fun _=> bslot) a b Mcap εdiag ξ saving
      (fun _=> hbslot) ha hb hMcap hεdiag hξ
  let P:ℝ:=(profileBound W hW aslot bslot lo hi haslot hWs)^(2*Fintype.card ι)
  let D:ℝ:=Cd*P*Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  let T:ℝ:=Ct*P*St.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  have hP:0≤ P:=pow_nonneg (zero_le_one.trans (profileBound_ge_one W hW aslot bslot lo hi haslot hWs)) _
  have hD:0≤ D:=by dsimp [D];positivity
  have hT:0≤ T:=by dsimp [T];positivity
  refine ⟨Ψ,hΨs,hΨn,2*(1+D+T),by positivity,?_⟩
  filter_upwards [hred] with Z hz
  refine ⟨hz.1,?_⟩
  intro Q _ H hH η₀ θ w σ freq hw hσ Bmask state p t X₁ X₂ hX₁ hX₂ κ hκ hcap
    S J Cphysical height e hCphysical hheight he hsave hphysical
  let s:=sourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂
  have hZ:0< Z:=zero_lt_one.trans hz.1
  have hPi:∀i,1≤ s.P i:=fun i=> Real.one_le_rpow hz.1.le (hw i)
  have hv:volume s≤ Z^Mcap:=original_volume_cap s Z κ Mcap hz.1 hκ hPi (by
    change length Z X₁+length Z X₂+6*κ*(∑i,Real.logb Z (Z^(w i)))≤ Mcap
    simpa only [Real.logb_rpow hZ hz.1.ne'] using hcap)
  have hscale:1≤ state.radial.scale:=by rw [state.scale_eq];exact Real.one_le_rpow hz.1.le state.row_nonneg
  have hKi:state.radial.scale⁻¹≤ Z^Mcap:=
    (inv_le_one_of_one_le₀ hscale).trans (Real.one_le_rpow hz.1.le hMcap)
  have hbound:=hz.2 s (p.profile 0) (p.profile 1) rfl rfl (p.support 0) (p.support 1)
    (fun _=> le_rfl) state.puncture state.radial state.radial_support hv hKi
  have hplain:(plainControl s (p.profile 0) (p.profile 1))^2≤ P*(p.control (insert (0,0) S))^2:=
    plain_control_sq_le s p S (Fintype.card ι) _
      (profileBound_ge_one W hW aslot bslot lo hi haslot hWs) le_rfl (fun _=> le_rfl)
  have hsquare:(p.control S)^2≤(p.control (insert (0,0) S))^2:=
    pow_le_pow_left₀ (p.control_nonneg S) (control_mono p S) 2
  let F:ℝ:=(p.control (insert (0,0) S))^2*(1+|t|+height)^J*Z^(state.width+e)
  have hF:0≤ F:=by dsimp [F];positivity
  have hheight1:1≤(1+|t|+height)^J:=one_le_pow₀ (by linarith [abs_nonneg t])
  have hscalePower (x:ℝ)(hx:x≤ e):state.radial.scale*Z^x≤ Z^(state.width+e):=by
    rw [state.scale_eq,←Real.rpow_add hZ]
    exact Real.rpow_le_rpow_of_exponent_le hz.1.le (by unfold NaturalState.width;linarith [state.character_nonneg])
  have hphysical':physicalMass (zeroSourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂) state.puncture 1 fixedBadMask 1
      Ψ state.radial.scale Z ξ/volume s≤ Cphysical*F:=by
    apply hphysical.trans
    calc
      _≤ Cphysical*(p.control (insert (0,0) S))^2*(1+|t|+height)^J*Z^(state.width+e):=by gcongr
      _=Cphysical*F:=by dsimp [F];ring
  have hterm (c A x:ℝ)(hc:0≤ c)(hA:0≤ A)(hx:x≤ e):
      c*(plainControl s (p.profile 0) (p.profile 1))^2*A*state.radial.scale*Z^x≤ c*P*A*F:=by
    calc
      _≤ c*(P*(p.control (insert (0,0) S))^2)*A*(state.radial.scale*Z^x):=by
        rw [←mul_assoc];gcongr
      _≤ c*(P*(p.control (insert (0,0) S))^2)*A*Z^(state.width+e):=by
        gcongr;exact hscalePower x hx
      _≤ c*P*A*F:=by
        have hh:=le_mul_of_one_le_right
          (show 0≤ c*P*A*(p.control (insert (0,0) S))^2*Z^(state.width+e) by positivity) hheight1
        dsimp [F]
        convert hh using 1 <;> first | rfl | ring
  have hd:=hterm Cd (Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) εdiag hCd.le (apply_nonneg _ _) he
  have ht:=hterm Ct (St.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) (-saving) hCt.le (apply_nonneg _ _) hsave
  change energy state.character state.mask 1 t (p.profile 0) (p.profile 1) _ _ _ _ _ _ _ _≤ _ at hbound
  apply hbound.trans
  change 2*diagonalControl state.radial.profile*(_+_+_)≤ _
  have hsum:=add_le_add (add_le_add hphysical' hd) ht
  have hmul:=mul_le_mul_of_nonneg_left hsum
    (mul_nonneg (by norm_num : (0:ℝ)≤2) (diagonalControl_nonneg state.radial.profile))
  apply hmul.trans
  dsimp only [D,T] at *
  have hcoeff:Cphysical+Cd*P*Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ+
      Ct*P*St.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ≤
      (1+Cd*P*Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ+
        Ct*P*St.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ)*(Cphysical+1):=by
    nlinarith [mul_nonneg hCphysical hD,mul_nonneg hCphysical hT]
  have hh:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoeff hF)
    (mul_nonneg (by norm_num : (0:ℝ)≤2) (diagonalControl_nonneg state.radial.profile))
  dsimp [F] at hh ⊢
  nlinarith only [hh]

end CenteredMomentEnergyNaturalLowSourceBound

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentEnergyNaturalSourceAdmission
open HeckeFamily  InversePrincipalEnergy
open CenteredMomentCommonRadialData CenteredMomentEnergyNaturalInputMatches
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentEnergyState
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyZeroComparison
open CenteredMomentEnergyOriginalSource CenteredMomentEnergyOriginalProfileControl
open CenteredMomentEnergyInputParentCapacity CenteredMomentAmplificationChildInput
open CenteredMomentEnergyBands CenteredMomentSecondHeightFamily
open CenteredMomentPrimeSlot CenteredMomentNaturalFixedRaySource HeckeDyadic HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentSourceRow CenteredMomentRetainedEnergy
open CenteredMomentSourceInputTailUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentHeckeExpansion CenteredMomentHeckeHeight
local notation "O" => Eisenstein.O
local instance (Q:Ideal O)[NeZero Q]:Finite (O ⧸ Q):=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne Q)
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := energyOriginalSourceDecidableSum

def lowerProduct (N : ℕ) (aslot a : ℝ) : ℝ := (min 1 aslot)^N*a*a

lemma lowerProduct_pos (N : ℕ) {aslot a : ℝ} (hs : 0 < aslot) (ha : 0 < a) :
    0 < lowerProduct N aslot a := by unfold lowerProduct; positivity

section Source
variable (Q : Ideal O) [NeZero Q]
variable (H : Subgroup (O ⧸ Q)ˣ) (hH : RayOrthogonality.globalUnits Q ≤ H)
variable (η₀ : Character) (θ : ι → RayQuotient.Characters Q H)
variable (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi : ℝ)
variable (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
variable (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)
variable {Z Bmask bΦ a b : ℝ} (state : NaturalState Z Bmask bΦ)
variable (p : Profiles a b) (ha : 0 < a) (t X₁ X₂ : ℝ)
variable (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
local notation "s" => sourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂
local notation "s₀" => zeroSourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂

theorem both_matches :
    CenteredMomentAllocatedRayDictionary.Matches Q H hH s η₀ θ w σ freq W bslot Z ∧
    CenteredMomentAllocatedRayDictionary.Matches Q H hH s₀ η₀ θ w σ freq W bslot Z := by
  constructor <;> constructor <;> intros <;> rfl

lemma source_fields :
    (s).η = state.character ∧ (s₀).η = state.character ∧
    (s).m = state.mask ∧ (s₀).m = state.mask ∧ (s).A = 1 ∧ (s₀).A = 1 ∧
    (s).t = t ∧ (s₀).t = t ∧
    (s).W₁ = p.profile 0 ∧ (s₀).W₁ = p.profile 0 ∧
    (s).W₂ = p.profile 1 ∧ (s₀).W₂ = p.profile 1 ∧
    (s).lower = aslot ∧ (s₀).lower = aslot ∧ (s).upper = bslot ∧ (s₀).upper = bslot := by
  repeat' constructor

lemma slot_fields (i : ι) :
    (s).P i = Z^(w i) ∧ (s₀).P i = Z^(w i) ∧
    (s).lo i = aslot ∧ (s₀).lo i = aslot ∧ (s).hi i = bslot ∧ (s₀).hi i = bslot ∧
    (s).M i = profileBound W hW aslot bslot lo hi haslot hWs ∧
    (s₀).M i = profileBound W hW aslot bslot lo hi haslot hWs ∧
    (s).slots i = primePool Q H bslot (Z^(w i)) ∧
    (s₀).slots i = primePool Q H bslot (Z^(w i)) := by repeat' constructor

lemma slot_coefficient (i : ι) (I : Ideal O) :
    (s).toData.coefficient i I = idealCoeff (relativeCharacter Q H hH η₀ (θ i)) I *
      annularWeight W (Z^(w i)) (σ i) (freq i) I ∧
    (s₀).toData.coefficient i I = (s).toData.coefficient i I := ⟨rfl, rfl⟩

lemma rectangles :
    (s).X₁ = X₁ ∧ (s).X₂ = X₂ ∧ (s).Y₁ = X₁ ∧ (s).Y₂ = X₂ ∧
    (s₀).X₁ = X₁ ∧ (s₀).X₂ = X₂ ∧
    (s₀).Y₁ = smallScale b ∧ (s₀).Y₂ = X₁*X₂/smallScale b ∧
    (s₀).Y₁*(s₀).Y₂ = X₁*X₂ := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  exact (s₀).same_product

lemma raw_volume : volume s = X₁*X₂*∏ i, Z^(w i) ∧ volume s₀ = volume s := ⟨rfl,rfl⟩

lemma volume_log (hZ : 1 < Z) :
    Real.logb Z (volume s) = Real.logb Z X₁ + Real.logb Z X₂ + ∑ i, w i ∧
    Real.logb Z (volume s₀) = Real.logb Z X₁ + Real.logb Z X₂ + ∑ i, w i := by
  have hh := input_volume_log s Z
  change Real.logb Z (volume s) = Real.logb Z X₁ + Real.logb Z X₂ +
    ∑ i, Real.logb Z (Z^(w i)) at hh
  simp only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
  exact ⟨hh,hh⟩

theorem capacity_admission (hZ : 1 < Z) (hw : ∀ i, 0 ≤ w i) (κ : ℝ)
    (hκ : 1/6 ≤ κ)
    (hcap : length Z X₁ + length Z X₂ + 6*κ*(∑ i, w i) ≤ state.width) :
    (∀ i, 1 ≤ (s).P i ∧ 1 ≤ (s₀).P i) ∧
    volume s ≤ Z^state.width ∧ volume s₀ ≤ Z^state.width := by
  have hPi : ∀ i, 1 ≤ (s).P i := fun i => Real.one_le_rpow hZ.le (hw i)
  have hv := original_volume_cap s Z κ state.width hZ hκ hPi (by
    change length Z X₁ + length Z X₂ + 6*κ*(∑ i, Real.logb Z (Z^(w i))) ≤ _
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hcap)
  exact ⟨fun i => ⟨hPi i,hPi i⟩,hv,hv⟩

theorem low_admission (hZ : 1 < Z)
    (hlow : length Z X₁ + length Z X₂ + ∑ i, w i ≤ 5*state.width/6) :
    Real.logb Z (volume s) ≤ 5*state.width/6 ∧
    Real.logb Z (volume s₀) ≤ 5*state.width/6 := by
  have hv := volume_log Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂ hZ
  have h1 := raw_log_le_length Z X₁ hZ hX₁
  have h2 := raw_log_le_length Z X₂ hZ hX₂
  constructor <;> linarith [hv.1,hv.2]

theorem lower_product_admission (N : ℕ) (hN : Fintype.card ι ≤ N) :
    0 < lowerProduct N aslot a ∧
    lowerProduct N aslot a ≤ (∏ i, (s).lo i)*a*a ∧
    lowerProduct N aslot a ≤ (∏ i, (s₀).lo i)*a*a := by
  have hh := lower_product s N aslot haslot hN (fun _ => le_rfl)
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh ha.le) ha.le
  exact ⟨lowerProduct_pos N haslot ha,hb,hb⟩

theorem profile_control_admission (N : ℕ) (hN : Fintype.card ι ≤ N)
    (S : Finset (ℕ×ℕ)) :
    (plainControl s (p.profile 0) (p.profile 1))^2 ≤
      (profileBound W hW aslot bslot lo hi haslot hWs)^(2*N)*
        (p.control (insert (0,0) S))^2 ∧
    (plainControl s₀ (p.profile 0) (p.profile 1))^2 ≤
      (profileBound W hW aslot bslot lo hi haslot hWs)^(2*N)*
        (p.control (insert (0,0) S))^2 := by
  have hh := plain_control_sq_le s p S N _
    (profileBound_ge_one W hW aslot bslot lo hi haslot hWs) hN (fun _ => le_rfl)
  exact ⟨hh,hh⟩

theorem normalized_zero_source (R : Ideal O) (z : O) :
    positiveSlotRow state.character (fixedBadMask*cubicIdealGenerator R) 1 z
      (p.profile 0) (p.profile 1) (s).slots (s).toData.coefficient (s).P t X₁ X₂ =
    (Real.sqrt (volume s) : ℂ)⁻¹ *
      ∑ I ∈ finiteColumns (Fintype.piFinset (s₀).pools),
        CenteredMomentOriginalCommonHarmonic.coefficient s₀ R 1 I * rowWeight state.character fixedBadMask 1 z t I := by
  have hh := normalized_input_difference s₀ R z
  have hz := comparison_row_zero s
    (CenteredMomentEnergyLowFixedRadialEntry.support_zero _ a b ha (p.support 0))
    (CenteredMomentEnergyLowFixedRadialEntry.support_zero _ a b ha (p.support 1)) R z
  change positiveSlotRow state.character (fixedBadMask*cubicIdealGenerator R) 1 z
      (p.profile 0) (p.profile 1) (s).slots (s).toData.coefficient (s).P t X₁ X₂ -
    positiveSlotRow (s).η (fixedBadMask*cubicIdealGenerator R) 1 z (s).W₁ (s).W₂ (s).slots
      (s).toData.coefficient (s).P (s).t (s₀).Y₁ (s₀).Y₂ = _ at hh
  change positiveSlotRow (s).η (fixedBadMask*cubicIdealGenerator R) 1 z (s).W₁ (s).W₂ (s).slots
    (s).toData.coefficient (s).P (s).t (s₀).Y₁ (s₀).Y₂ = 0 at hz
  rw [hz,sub_zero] at hh
  exact hh

end Source

theorem radial_admission {Z Bmask bΦ : ℝ} (state : NaturalState Z Bmask bΦ) :
    1 ≤ state.radial.scale ∧ state.radial.scale⁻¹ ≤ 1 ∧
    state.radial.scale⁻¹ ≤ Z^state.width := by
  have hs : 1 ≤ state.radial.scale := by
    rw [state.scale_eq]
    exact Real.one_le_rpow state.base_ge_one state.row_nonneg
  have hi := inv_le_one_of_one_le₀ hs
  exact ⟨hs,hi,hi.trans (Real.one_le_rpow state.base_ge_one state.width_nonneg)⟩

theorem original_scale_caps {Z X₁ X₂ M L κ : ℝ} (w : ι → ℝ)
    (hZ : 1 < Z) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hw : ∀ i, 0 ≤ w i) (hκ : 1/6 ≤ κ)
    (hcap : length Z X₁ + length Z X₂ + 6*κ*(∑ i, w i) ≤ M)
    (hM : M ≤ L) : X₁ ≤ Z^L ∧ X₂ ≤ Z^L := by
  have hn : 0 ≤ 6*κ*(∑ i, w i) :=
    mul_nonneg (by linarith) (Finset.sum_nonneg (fun i _ => hw i))
  have h1 := raw_log_le_length Z X₁ hZ hX₁
  have h2 := raw_log_le_length Z X₂ hZ hX₂
  constructor
  · apply (Real.logb_le_iff_le_rpow hZ hX₁).mp
    linarith [length_nonneg Z X₂ hZ]
  · apply (Real.logb_le_iff_le_rpow hZ hX₂).mp
    linarith [length_nonneg Z X₁ hZ]

theorem eventually_scale_admission (b L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (ι : Type*) [Fintype ι] [DecidableEq ι],
    ∀ (Q : Ideal O) [NeZero Q] (H : Subgroup (O ⧸ Q)ˣ)
      (hH : RayOrthogonality.globalUnits Q ≤ H) (η₀ : Character)
      (θ : ι → RayQuotient.Characters Q H),
    ∀ (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi : ℝ)
      (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot),
    ∀ (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi),
    ∀ (Bmask bΦ a : ℝ) (state : NaturalState Z Bmask bΦ) (p : Profiles a b)
      (ha : 0 < a) (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (κ : ℝ),
    (∀ i, 0 ≤ w i) → 1/6 ≤ κ → state.width ≤ L →
    length Z X₁ + length Z X₂ + 6*κ*(∑ i, w i) ≤ state.width →
    let s := sourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂
    let s₀ := zeroSourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂
    (s).X₁ ≤ Z^L ∧ (s).X₂ ≤ Z^L ∧ (s).Y₁ ≤ Z^L ∧ (s).Y₂ ≤ Z^L ∧
    (s₀).X₁ ≤ Z^L ∧ (s₀).X₂ ≤ Z^L ∧
    (s₀).Y₁ ≤ Z^(2*L+ε) ∧ (s₀).Y₂ ≤ Z^(2*L+ε) := by
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (2*max 1 b),
    eventually_gt_atTop (1 : ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro ι _ _ Q _ H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ Bmask bΦ a state p ha t X₁ X₂ hX₁ hX₂ κ hw hκ hM hcap
  dsimp only
  have hx := original_scale_caps w hZ hX₁ hX₂ hw hκ hcap hM
  refine ⟨hx.1,hx.2,hx.1,hx.2,hx.1,hx.2,?_,?_⟩
  · exact (smallScale_le_one b).trans (Real.one_le_rpow hZ.le (by positivity))
  · change X₁*X₂/smallScale b ≤ _
    have hp : X₁*X₂ ≤ Z^(2*L) := by
      have hh := mul_le_mul hx.1 hx.2 hX₂.le (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) L).le
      rw [←Real.rpow_add (zero_lt_one.trans hZ)] at hh
      simpa only [two_mul] using hh
    unfold smallScale
    rw [div_div_eq_mul_div,div_one]
    exact (mul_le_mul hp hc (by positivity)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).le).trans_eq
        (Real.rpow_add (zero_lt_one.trans hZ) _ _).symm

end CenteredMomentEnergyNaturalSourceAdmission

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
namespace CenteredMomentEnergyFirstGaussianProfileWeights
def losses (epsilon delta theta B:ℝ):Fin 4→ℝ:=
  ![2*delta+epsilon,2*epsilon+2*delta+2*(5*B+1)*theta,0,0]


end CenteredMomentEnergyFirstGaussianProfileWeights

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentEnergyFirstStageLossBudget
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentSuccessorPaidParameters
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients

def sourcePaid (Bcap emask ell er delta reserveAmp thetaSource thetaClip κ mesh:ℝ):ℝ:=
  (Bcap+Bcap)*emask+ell+er+(delta+reserveAmp+thetaSource)/6+thetaClip/3+κ*mesh

theorem literal_four_budget (M Bcap Bcommon κ ε:ℝ)
    (hM:0≤ M)(hB:0≤ Bcap)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(ell epsSrc epsMask deltaSrc thetaSrc deltaAmp reserveAmp thetaSource thetaClip
      er primeLoss physicalLoss highReflection zeroReflection saving:ℝ)
    (hell:ell≤ stageLoss M Bcap ε k)
    (he0:0≤ epsSrc)(he:epsSrc≤ reserve M Bcap ε)
    (hemask:(Bcap+Bcap)*epsMask≤ reserve M Bcap ε)
    (hdsrc:deltaSrc≤ reserve M Bcap ε)(htsrc:thetaSrc≤ reserve M Bcap ε)
    (hda:0≤ deltaAmp)(hra:0≤ reserveAmp)(hts:0≤ thetaSource)(htc:0≤ thetaClip)
    (hsmall:deltaAmp+reserveAmp+thetaSource≤ reserve M Bcap ε)
    (hclip:thetaClip≤ reserve M Bcap ε)(her:er≤ reserve M Bcap ε)
    (hcommon:epsSrc*Bcommon≤ reserve M Bcap ε)
    (hprime:primeLoss≤ reserve M Bcap ε)(hphysical:physicalLoss≤ reserve M Bcap ε)
    (hhigh:highReflection≤ reserve M Bcap ε)(hzero:zeroReflection≤ reserve M Bcap ε)
    (hsaving:2*amplification ε+deltaAmp+reserveAmp≤ saving):
    ∀j:Fin 4,
      losses epsSrc deltaSrc thetaSrc Bcap j+
        lossVector (amplification ε) deltaAmp reserveAmp
          (sourcePaid Bcap epsMask ell er deltaAmp reserveAmp thetaSource thetaClip κ (mesh M Bcap κ ε))
          epsSrc M saving j+
        epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection≤
      stageLoss M Bcap ε (k+1):=by
  have hb:=bounds M Bcap κ ε hM hB hκ hε
  have hr:0< reserve M Bcap ε:=hb.2.2.2.1
  have hs:0≤ amplification ε:=hb.1.le
  have hother:epsSrc*Bcommon+primeLoss+physicalLoss≤48*reserve M Bcap ε:=by linarith
  have hextra:epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection≤
      50*reserve M Bcap ε:=by linarith
  have hdf:deltaAmp+reserveAmp≤ reserve M Bcap ε:=by linarith
  have hdelta:deltaAmp≤ reserve M Bcap ε:=by linarith
  have hres:reserveAmp≤ reserve M Bcap ε:=by linarith
  have hmain:=successor_with_references M Bcap κ ε hM hB hκ hε k
    er deltaSrc epsSrc (deltaAmp+reserveAmp+thetaSource) ((Bcap+Bcap)*epsMask) thetaClip
    (epsSrc*Bcommon+primeLoss+physicalLoss) highReflection zeroReflection
    her hdsrc he hsmall hemask hclip hother hhigh hzero
  have hone:=actual_one_time_with_new_cost M Bcap κ ε hM hB hκ hε k
    (deltaAmp+reserveAmp) epsSrc deltaSrc thetaSrc reserveAmp M
    (epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection)
    hdf he hdsrc htsrc hres he0 le_rfl hextra
  have hdiag:=actual_one_time_with_new_cost M Bcap κ ε hM hB hκ hε k
    (deltaAmp+reserveAmp) epsSrc deltaAmp thetaSrc reserveAmp M
    (epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection)
    hdf he hdelta htsrc hres he0 le_rfl hextra
  have htail:=one_time_with_new_cost M Bcap κ ε hM hB hκ hε k 0
    (epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection) (by positivity) hextra
  intro j
  fin_cases j <;> simp only [losses,lossVector,Matrix.cons_val,Fin.reduceFinMk]
  · dsimp [sourcePaid,edge] at hmain ⊢
    linarith
  · dsimp [exceptional] at hone
    linarith [hone.1]
  · dsimp [CenteredMomentSuccessorPaidParameters.diagonal] at hdiag
    linarith [hdiag.2]
  · linarith

theorem chosen_four_budget (M Bcap Bcommon κ ε:ℝ)
    (hM:0≤ M)(hB:0≤ Bcap)(hBc:0≤ Bcommon)(hκ:0≤κ)(hε:0<ε):
    let r:=reserve M Bcap ε;
    let es:=r/(Bcommon+1);
    let em:=r/(Bcap+Bcap+1);
    0< es ∧ es≤1 ∧ 0< em ∧ 0< r/4 ∧ 0<2*amplification ε+1 ∧
    ∀(k:ℕ)(ell highReflection zeroReflection:ℝ),ell≤ stageLoss M Bcap ε k→
      highReflection≤ r→zeroReflection≤ r→∀j:Fin 4,
      losses es (r/4) (r/4) Bcap j+
        lossVector (amplification ε) (r/4) (r/4)
          (sourcePaid Bcap em ell (r/4) (r/4) (r/4) (r/4) (r/4) κ (mesh M Bcap κ ε))
          es M (2*amplification ε+1) j+
        es*Bcommon+r/4+r/4+highReflection+zeroReflection≤ stageLoss M Bcap ε (k+1):=by
  dsimp only
  have hb:=bounds M Bcap κ ε hM hB hκ hε
  have hr:0< reserve M Bcap ε:=hb.2.2.2.1
  have hs:0< amplification ε:=hb.1
  have hrsmall:reserve M Bcap ε≤ amplification ε/100:=min_le_left _ _
  have hr1:reserve M Bcap ε≤1:=by linarith [hb.2.1]
  have hes:0< reserve M Bcap ε/(Bcommon+1):=by positivity
  have hem:0< reserve M Bcap ε/(Bcap+Bcap+1):=by positivity
  have hesle:reserve M Bcap ε/(Bcommon+1)≤ reserve M Bcap ε:=by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hemscale:(Bcap+Bcap)*(reserve M Bcap ε/(Bcap+Bcap+1))≤ reserve M Bcap ε:=by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hescale:(reserve M Bcap ε/(Bcommon+1))*Bcommon≤ reserve M Bcap ε:=by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  refine ⟨hes,hesle.trans hr1,hem,by positivity,by positivity,?_⟩
  intro k ell highReflection zeroReflection hell hhigh hzero
  apply literal_four_budget M Bcap Bcommon κ ε hM hB hκ hε k ell
    (reserve M Bcap ε/(Bcommon+1)) (reserve M Bcap ε/(Bcap+Bcap+1))
    (reserve M Bcap ε/4) (reserve M Bcap ε/4) (reserve M Bcap ε/4)
    (reserve M Bcap ε/4) (reserve M Bcap ε/4) (reserve M Bcap ε/4)
    (reserve M Bcap ε/4) (reserve M Bcap ε/4) (reserve M Bcap ε/4)
    highReflection zeroReflection (2*amplification ε+1)
    hell hes.le hesle hemscale
  all_goals first | exact hescale | exact hhigh | exact hzero | positivity | linarith

end CenteredMomentEnergyFirstStageLossBudget

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentEnergyFirstDeclaredCapacityLossBudget
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyFirstStageLossBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients

lemma lossVector_cap (sigma delta reserveAmp paid es M A saving:ℝ)
    (he:0≤ es)(hM:0≤ M)(hA:0≤ A)(j:Fin 4):
    lossVector sigma delta reserveAmp paid es A saving j≤
      lossVector sigma delta reserveAmp paid es M saving j+es*A:=by
  fin_cases j <;> simp only [lossVector,Matrix.cons_val,Fin.reduceFinMk] <;>
    nlinarith [mul_nonneg he hM,mul_nonneg he hA]

theorem chosen_declared_four_budget (M A Bcap Bcommon κ ε:ℝ)
    (hM:0≤ M)(hA:0≤ A)(hB:0≤ Bcap)(hBc:0≤ Bcommon)(hκ:0≤κ)(hε:0<ε):
    let r:=reserve M Bcap ε
    let es:=r/(4*(Bcommon+A+1))
    let em:=r/(Bcap+Bcap+1)
    0< es ∧ es≤1 ∧ 0< em ∧ es*A≤ r/4 ∧ es*Bcommon≤ r/4 ∧
    ∀(k:ℕ)(ell highReflection zeroReflection:ℝ),ell≤ stageLoss M Bcap ε k→
      highReflection≤ r→zeroReflection≤ r→∀j:Fin 4,
      losses es (r/4) (r/4) Bcap j+
        lossVector (amplification ε) (r/4) (r/4)
          (sourcePaid Bcap em ell (r/4) (r/4) (r/4) (r/4) (r/4) κ (mesh M Bcap κ ε))
          es A (2*amplification ε+1) j+
        es*Bcommon+r/4+r/4+highReflection+zeroReflection≤ stageLoss M Bcap ε (k+1):=by
  dsimp only
  let r:=reserve M Bcap ε
  let es:=r/(4*(Bcommon+A+1))
  have hb:=bounds M Bcap κ ε hM hB hκ hε
  have hr:0< r:=hb.2.2.2.1
  have hs:0< amplification ε:=hb.1
  have hrsmall:r≤ amplification ε/100:=min_le_left _ _
  have hr1:r≤1:=by linarith [hb.2.1]
  have hden:0<4*(Bcommon+A+1):=by positivity
  have hes:0< es:=by dsimp [es];positivity
  have hesle:es≤ r/4:=by
    dsimp [es]
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hr.le hBc,mul_nonneg hr.le hA]
  have hescap:es*A≤ r/4:=by
    dsimp [es]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hr.le hBc]
  have hescommon:es*Bcommon≤ r/4:=by
    dsimp [es]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hr.le hA]
  have hemscale:(Bcap+Bcap)*(r/(Bcap+Bcap+1))≤ r:=by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  refine ⟨hes,by linarith,by positivity,hescap,hescommon,?_⟩
  intro k ell highReflection zeroReflection hell hhigh hzero j
  have hh:=literal_four_budget M Bcap Bcommon κ ε hM hB hκ hε k ell
    es (r/(Bcap+Bcap+1)) (r/4) (r/4) (r/4) (r/4) (r/4) (r/4)
    (r/4) (r/4) (r/4+es*A) highReflection zeroReflection (2*amplification ε+1)
    hell hes.le (by dsimp [r] at *;linarith) hemscale
    (by dsimp [r] at *;linarith) (by dsimp [r] at *;linarith)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (by dsimp [r] at *;linarith) (by dsimp [r] at *;linarith)
    (by dsimp [r] at *;linarith) (by dsimp [r] at *;linarith)
    (by dsimp [r] at *;linarith) (by dsimp [r] at *;linarith)
    hhigh hzero (by linarith)
  have hc:=lossVector_cap (amplification ε) (r/4) (r/4)
    (sourcePaid Bcap (r/(Bcap+Bcap+1)) ell (r/4) (r/4) (r/4) (r/4) (r/4)
      κ (mesh M Bcap κ ε)) es M A (2*amplification ε+1) hes.le hM hA j
  have hj:=hh j
  change losses es (r/4) (r/4) Bcap j+_+es*Bcommon+r/4+r/4+highReflection+zeroReflection≤ _
  linarith only [hj,hc]

end CenteredMomentEnergyFirstDeclaredCapacityLossBudget

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open Filter

namespace CenteredMomentEnergyFirstActualFrequencyBudget
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyFirstStageLossBudget CenteredMomentEnergyFirstDeclaredCapacityLossBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentSectorLocalization

theorem eventually_frequency_loss (r:ℝ)(hr:0< r):
    ∀ᶠ Z:ℝ in atTop,1< Z ∧
      0≤ frequencyLoss Z 32 (r/4) ∧ frequencyLoss Z 32 (r/4)≤ r/4:=by
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop (by positivity:0< r/8))) 128,
    eventually_gt_atTop (1:ℝ)] with Z hpow hZ
  have hlog:=Real.logb_le_logb_of_le hZ (by norm_num:(0:ℝ)<128) hpow
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hlog
  refine ⟨hZ,frequencyLoss_nonneg Z 32 (r/4) hZ (by norm_num) (by positivity),?_⟩
  unfold frequencyLoss
  norm_num only [show (4:ℝ)*32=128 by norm_num]
  linarith only [hlog]

lemma paid_frequency_mono
    (sigma delta delta' reserveAmp Bcap emask ell er thetaSource thetaClip κ mesh
      es A saving:ℝ)(hd:delta≤ delta')(j:Fin 4):
    lossVector sigma delta reserveAmp
      (sourcePaid Bcap emask ell er delta reserveAmp thetaSource thetaClip κ mesh)
      es A saving j≤
    lossVector sigma delta' reserveAmp
      (sourcePaid Bcap emask ell er delta' reserveAmp thetaSource thetaClip κ mesh)
      es A saving j:=by
  fin_cases j <;>
    simp only [lossVector,sourcePaid,Matrix.cons_val,Fin.reduceFinMk] <;>
    linarith only [hd]

theorem actual_frequency_four_budget (M A Bcap Bcommon κ ε:ℝ)
    (hM:0≤ M)(hA:0≤ A)(hB:0≤ Bcap)(hBc:0≤ Bcommon)(hκ:0≤κ)(hε:0<ε):
    let r:=reserve M Bcap ε
    let es:=r/(4*(Bcommon+A+1))
    let em:=r/(Bcap+Bcap+1)
    0< es ∧ es≤1 ∧ 0< em ∧ 0< r/4 ∧ r/4≤ amplification ε/4 ∧
    ∀ᶠ Z:ℝ in atTop,1< Z ∧
      0≤ frequencyLoss Z 32 (r/4) ∧ frequencyLoss Z 32 (r/4)≤ r/4 ∧
      ∀(k:ℕ)(ell highReflection zeroReflection:ℝ),ell≤ stageLoss M Bcap ε k→
        highReflection≤ r→zeroReflection≤ r→∀j:Fin 4,
        losses es (r/4) (r/4) Bcap j+
          lossVector (amplification ε) (frequencyLoss Z 32 (r/4)) (r/4)
            (sourcePaid Bcap em ell (r/4) (frequencyLoss Z 32 (r/4))
              (r/4) (r/4) (r/4) κ (mesh M Bcap κ ε))
            es A (2*amplification ε+1) j+
          es*Bcommon+r/4+r/4+highReflection+zeroReflection≤ stageLoss M Bcap ε (k+1):=by
  dsimp only
  let r:=reserve M Bcap ε
  let es:=r/(4*(Bcommon+A+1))
  let em:=r/(Bcap+Bcap+1)
  obtain ⟨hes,hes1,hem,_,_,hbudget⟩:=chosen_declared_four_budget M A Bcap Bcommon κ ε
    hM hA hB hBc hκ hε
  have hb:=bounds M Bcap κ ε hM hB hκ hε
  have hr:0< r:=hb.2.2.2.1
  have hrs:r≤ amplification ε/100:=min_le_left _ _
  refine ⟨hes,hes1,hem,by positivity,by linarith [hb.1],?_⟩
  filter_upwards [eventually_frequency_loss r hr] with Z hZ
  refine ⟨hZ.1,hZ.2.1,hZ.2.2,?_⟩
  intro k ell highReflection zeroReflection hell hhigh hzero j
  have hfixed:=hbudget k ell highReflection zeroReflection hell hhigh hzero j
  have hmono:=paid_frequency_mono (amplification ε) (frequencyLoss Z 32 (r/4)) (r/4)
    (r/4) Bcap em ell (r/4) (r/4) (r/4) κ (mesh M Bcap κ ε) es A
    (2*amplification ε+1) hZ.2.2 j
  change losses es (r/4) (r/4) Bcap j+_+es*Bcommon+r/4+r/4+highReflection+zeroReflection≤ _ at hfixed ⊢
  linarith only [hfixed,hmono]

end CenteredMomentEnergyFirstActualFrequencyBudget

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open Filter

namespace CenteredMomentEnergyFirstSourceParameters
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyFirstStageLossBudget CenteredMomentEnergyFirstActualFrequencyBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentSectorLocalization

def sourceEpsilon (M A B ε:ℝ):ℝ:=reserve M B ε/(4*((A+1)+A+1))
def maskEpsilon (M B ε:ℝ):ℝ:=reserve M B ε/(B+B+1)
def columnLoss (M B ε:ℝ)(k:ℕ):ℝ:=
  stageLoss M B ε (k+1)-2*reserve M B ε-reserve M B ε/4

lemma source_cap_mono (es ds ts Bactual Bschedule sigma delta amp em child er θs θc κ mesh A saving:ℝ)
    (hB:Bactual≤ Bschedule)(ht:0≤ ts)(hem:0≤ em)(j:Fin 4):
    losses es ds ts Bactual j+
      lossVector sigma delta amp (sourcePaid Bactual em child er delta amp θs θc κ mesh) es A saving j≤
    losses es ds ts Bschedule j+
      lossVector sigma delta amp (sourcePaid Bschedule em child er delta amp θs θc κ mesh) es A saving j:=by
  fin_cases j <;>
    simp only [losses,lossVector,sourcePaid,Matrix.cons_val,Fin.reduceFinMk] <;>
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hB),mul_nonneg hem (sub_nonneg.mpr hB)]

theorem parameter_gates (M A B κ ε:ℝ)(hM:0≤ M)(hA:0≤ A)(hB:0≤ B)
    (hκ:(3/4:ℝ)≤κ)(hε:0<ε):
    let sigma:=amplification ε
    let r:=reserve M B ε
    0< sigma ∧ sigma≤1 ∧ 0< r/4 ∧ r/4≤ sigma/4 ∧ r/4≤1 ∧
      0< sourceEpsilon M A B ε ∧ sourceEpsilon M A B ε≤1 ∧
      0< maskEpsilon M B ε ∧ 0< mesh M B κ ε ∧
      mesh M B κ ε≤ sigma/12 ∧ 0≤ sigma/12 ∧ sigma/12< sigma/6 ∧
      0<2*sigma+1 ∧ 0≤ A+1:=by
  dsimp only
  have hκ0:0≤κ:=by linarith
  have hb:=bounds M B κ ε hM hB hκ0 hε
  have hr:=hb.2.2.2.1
  have hrs:reserve M B ε≤ amplification ε/100:=min_le_left _ _
  have hm:=hb.2.2.2.2.2.1
  have hes:0< sourceEpsilon M A B ε:=by unfold sourceEpsilon;positivity
  have hesr:sourceEpsilon M A B ε≤ reserve M B ε:=by
    unfold sourceEpsilon
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg hr.le hA]
  exact ⟨hb.1,hb.2.1,by positivity,by linarith,by linarith,
    hes,by linarith,by unfold maskEpsilon;positivity,hb.2.2.2.2.1,
    by linarith,by linarith [hb.1],by linarith [hb.1],by linarith [hb.1],by linarith⟩

lemma columnLoss_physical (M B ε:ℝ)(k:ℕ):
    columnLoss M B ε k+reserve M B ε/4=
      CenteredMomentEnergyStageMargins.physicalLoss M B ε k:=by
  unfold columnLoss CenteredMomentEnergyStageMargins.physicalLoss
  ring

theorem eventually_actual_four_fit (M A P B κ ε:ℝ)
    (hM:0≤ M)(hA:0≤ A)(_hP:0≤ P)(hB:0≤ B)(hready:readyBudget A P≤ B)
    (hκ:(3/4:ℝ)≤κ)(hε:0<ε):
    let r:=reserve M B ε
    ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(k:ℕ)(εchild:ℝ),εchild≤ stageLoss M B ε k→∀j:Fin 4,
        losses (sourceEpsilon M A B ε) (r/4) (r/4) (readyBudget A P) j+
          lossVector (amplification ε) (frequencyLoss Z 32 (r/4)) (r/4)
            ((readyBudget A P+readyBudget A P)*maskEpsilon M B ε+εchild+r/4+
              (frequencyLoss Z 32 (r/4)+r/4+r/4)/6+(r/4)/3+κ*mesh M B κ ε)
            (sourceEpsilon M A B ε) A (2*amplification ε+1) j+
          sourceEpsilon M A B ε*(A+1)+r/4≤ columnLoss M B ε k:=by
  dsimp only
  have hκ0:0≤κ:=by linarith
  have h:=actual_frequency_four_budget M A B (A+1) κ ε hM hA hB (by linarith) hκ0 hε
  obtain ⟨_,_,hem,_,_,hevent⟩:=h
  have hr:0< reserve M B ε:=(bounds M B κ ε hM hB hκ0 hε).2.2.2.1
  filter_upwards [hevent] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro k εchild hchild j
  have hfit:=hZ.2.2.2 k εchild (reserve M B ε) (reserve M B ε) hchild le_rfl le_rfl j
  have hmono:=source_cap_mono (sourceEpsilon M A B ε) (reserve M B ε/4) (reserve M B ε/4)
    (readyBudget A P) B (amplification ε) (frequencyLoss Z 32 (reserve M B ε/4))
    (reserve M B ε/4) (maskEpsilon M B ε) εchild (reserve M B ε/4)
    (reserve M B ε/4) (reserve M B ε/4) κ (mesh M B κ ε) A (2*amplification ε+1)
    hready (by positivity) hem.le j
  change losses (sourceEpsilon M A B ε) _ _ B j+
    lossVector _ _ _ (sourcePaid B (maskEpsilon M B ε) εchild _ _ _ _ _ _ _) _ _ _ j+
    sourceEpsilon M A B ε*(A+1)+_+_+_+_≤ _ at hfit
  dsimp only [sourcePaid] at hmono hfit
  unfold columnLoss
  dsimp only [sourceEpsilon,maskEpsilon] at hmono hfit ⊢
  linarith only [hmono,hfit]

theorem ready_budget_final (M Bmask L ε A P:ℝ)(hM:0≤ M)(hB:0≤ Bmask)
    (hA:A≤2*CenteredMomentEnergyWidthRanges.range M Bmask L (count M ε)+M+1)
    (hP:P≤ Bmask):
    readyBudget A P≤ CenteredMomentEnergyWidthRanges.finalSourceCap M Bmask L ε:=by
  have hn:1≤ count M ε:=by
    unfold count CenteredMomentFirstSecondLossParameters.depth
    omega
  have hm:=CenteredMomentEnergyWidthRanges.range_mono M Bmask L hM hB hn
  have hr:20≤ CenteredMomentEnergyWidthRanges.range M Bmask L (count M ε):=by
    simp only [CenteredMomentEnergyWidthRanges.range,CenteredMomentEnergyWidthRanges.step] at hm
    linarith [le_max_left (1:ℝ) L]
  unfold readyBudget CenteredMomentEnergyWidthRanges.finalSourceCap CenteredMomentEnergyWidthRanges.sourceCap
  linarith

end CenteredMomentEnergyFirstSourceParameters

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace CenteredMomentEnergyReindex
open HeckeFamily CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
local notation "O"=> Eisenstein.O

/-- An embedding identifies a finite set with its mapped image. -/
def subsetMapEquiv {α β : Type*} (e : α ↪ β) (T : Finset α) : T ≃ T.map e :=
  Equiv.ofBijective
    (fun i => ⟨e i, Finset.mem_map.mpr ⟨i, i.property, rfl⟩⟩)
    ⟨fun a b h => Subtype.ext (e.injective (congrArg Subtype.val h)), by
      intro b
      obtain ⟨a, ha, hab⟩ := Finset.mem_map.mp b.property
      exact ⟨⟨a, ha⟩, Subtype.ext hab⟩⟩

variable {α β:Type*}[Fintype α][Fintype β]

lemma positive_reindex (e:α≃β)(η:Character)(m A z:O)(W₁ W₂:ℝ→ℂ)
    (pool:β→Finset (Ideal O))(coeff:β→Ideal O→ℂ)(P:β→ℝ)(t X₁ X₂:ℝ):
    positiveSlotRow η m A z W₁ W₂ (pool∘e) (coeff∘e) (P∘e) t X₁ X₂=
      positiveSlotRow η m A z W₁ W₂ pool coeff P t X₁ X₂:=by
  unfold positiveSlotRow
  simp only [Function.comp_apply,e.prod_comp P,
    e.prod_comp (fun i=> CenteredMomentHeckeSlots.rowSlot η m A z (pool i) (coeff i) t)]

theorem energy_reindex (e:α≃β)(η:Character)(m A:O)(W₁ W₂:ℝ→ℂ)
    (pool:β→Finset (Ideal O))(coeff:β→Ideal O→ℂ)(P:β→ℝ)(t X₁ X₂:ℝ)
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):
    energy η m A t W₁ W₂ (pool∘e) (coeff∘e) (P∘e) X₁ X₂ keep Φ K=
      energy η m A t W₁ W₂ pool coeff P X₁ X₂ keep Φ K:=by
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_reindex]

omit [Fintype α] [Fintype β] in
theorem energy_subset_map (e:α↪β)(T:Finset α)(η:Character)(m A:O)(W₁ W₂:ℝ→ℂ)
    (pool:β→Finset (Ideal O))(coeff:β→Ideal O→ℂ)(P:β→ℝ)(t X₁ X₂:ℝ)
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):
    energy η m A t W₁ W₂ (fun i:T=> pool (e i)) (fun i:T=> coeff (e i))
      (fun i:T=> P (e i)) X₁ X₂ keep Φ K=
    energy η m A t W₁ W₂ (fun i:T.map e=> pool i) (fun i:T.map e=> coeff i)
      (fun i:T.map e=> P i) X₁ X₂ keep Φ K:=
  energy_reindex (subsetMapEquiv e T) η m A W₁ W₂
    (fun i:T.map e=> pool i) (fun i:T.map e=> coeff i) (fun i:T.map e=> P i)
    t X₁ X₂ keep Φ K

end CenteredMomentEnergyReindex

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentEnergyLowBandEmpty
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentNaturalFixedRaySource
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentFiniteProfileExceptional InversePrincipalEnergy
local notation "O"=> Eisenstein.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

omit [Fintype α] [DecidableEq α] in
theorem positive_low_zero
    (Wslot:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (h:PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q degree S C):
    ZeroLowAt (internalQ Q η₀) a b bΦ Bmask L Mcap ε Z degree S C:=by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hsmall
  let T:Finset α:=∅
  let θ:T→RayQuotient.Characters M H:=fun i=> False.elim (Finset.notMem_empty _ i.property)
  let w:T→ℝ:=fun _=>0
  have hcap:length Z X₁+length Z X₂+6*κ*(∑i:T,w i)≤ s.width:=by
    simp only [T,w,Finset.sum_const_zero,mul_zero,add_zero]
    linarith [s.width_nonneg]
  have hl:length Z X₁+length Z X₂+(∑i:T,w i)≤5*s.width/6:=by
    simpa only [w,Finset.sum_const_zero,add_zero] using hsmall
  have hh:=h T θ w w w t 0 (fun _=> le_rfl)
    (fun i=> False.elim (Finset.notMem_empty _ i.property))
    (fun i=> False.elim (Finset.notMem_empty _ i.property))
    (fun i=> False.elim (Finset.notMem_empty _ i.property)) le_rfl
    (fun _=> by simp [w]) s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hl
  have hid:energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:T=> CenteredMomentPrimeSlot.primePool M H bslot (Z^(w i)))
      (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (w i) (w i) I)
      (fun i=> Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale=
      s.plainEnergy p t X₁ X₂:=by
    simp only [T,energy,positiveSlotRow,NaturalState.plainEnergy,Finset.univ_eq_empty,
      Finset.prod_empty,mul_one]
  rw [hid] at hh
  simpa only [add_zero,Real.norm_eq_abs] using hh

end CenteredMomentEnergyLowBandEmpty

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentEnergyLowBandSubtype
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyState CenteredMomentEnergyReferenceLowBands
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentEnergyReindex
local notation "O" => Eisenstein.O
variable {α β : Type*} [Fintype α] [Fintype β]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

omit [Fintype α] [Fintype β] in
theorem positiveLowAt_embedding (e : β↪α)
    (W : ℝ→ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ)
    (h : PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C) :
    PositiveLowAt (α:=β) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C := by
  intro T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂
    hX₁ hX₂ hcap₁ hcap₂ hcapacity hlow
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
    (by rw [hsum];exact hcapacity) (by rw [hsum];exact hlow)
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
theorem positiveLowAt_subtype (T : Finset α)
    (W : ℝ→ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ)
    (h : PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C) :
    PositiveLowAt (α:=T) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C :=
  positiveLowAt_embedding M H hH ⟨Subtype.val,Subtype.val_injective⟩ W bslot a b bΦ Bmask L
    Lslot lo hi Mcap ε κ Z η₀ Q degree S C h

end CenteredMomentEnergyLowBandSubtype

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentEnergyPositiveLowBandSource
open HeckeFamily  InversePrincipalEnergy
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentFiniteProfileExceptional
open CenteredMomentFirstSourceReduction CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
local notation "O"=> Eisenstein.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

def PhysicalLowAt (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (a b bΦ Bmask L Lslot rho Mcap κ ξ e Z:ℝ)(ha:0< a)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(η₀:Character)(Q:Ideal O)
    (S:Finset (ℕ×ℕ))(J:ℕ)(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ freq:T→ℝ)(t height:ℝ),
    (∀i,0≤ w i)→(∀i,w i≤ Lslot)→∀hσlo:∀i,lo≤σ i,∀hσhi:∀i,σ i≤ hi,
    0≤ height→(∀i,|freq i|≤ height)→
  ∀state:NaturalState Z Bmask bΦ,state.fixedModulus=internalQ Q η₀→ rho≤ state.width→state.width≤ Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0< X₁,∀hX₂:0< X₂,
    X₁≤ Z^L→X₂≤ Z^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ state.width→
    length Z X₁+length Z X₂+(∑i,w i)≤5*state.width/6→
    physicalMass (zeroSourceInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂)
      state.puncture 1 fixedBadMask 1 (Ψ T) state.radial.scale Z ξ /
      volume (sourceInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂)≤
      C*(p.control S)^2*(1+|t|+height)^J*Z^(state.width+e)

theorem actual_low_stages_from_physical
    (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi a b bΦ Mcap εdiag ξ saving:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤ bslot)(ha:0< a)(hb:0≤ b)(hbΦ:0< bΦ)(hMcap:0≤ Mcap)
    (hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:(T:Finset α)→𝓢(ℝ,ℂ),
      (∀T,Function.support (Ψ T:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1)) ∧
      (∀T x,0≤(Ψ T x).re) ∧∃Cfixed:ℝ,0< Cfixed ∧
    ∀ᶠZ:ℝ in atTop,1< Z ∧
    ∀(Bmask L Lslot rho κ e:ℝ)(η₀:Character)(Q:Ideal O)(S:Finset (ℕ×ℕ))(J:ℕ)(Cphysical:ℝ),
      1/6≤κ→0≤ Cphysical→εdiag≤ e→-saving≤ e→
      PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho e κ Z η₀ Q
        J (insert (0,0) S) (Cfixed*(Cphysical+1))→
      PhysicalLowAt (α:=α) M H hH W hW aslot bslot lo hi haslot hWs
        a b bΦ Bmask L Lslot rho Mcap κ ξ e Z ha Ψ η₀ Q S J Cphysical→
      PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q
        J (insert (0,0) S) (Cfixed*(Cphysical+1)) ∧
      ZeroLowAt (internalQ Q η₀) a b bΦ Bmask L Mcap e Z J (insert (0,0) S)
        (Cfixed*(Cphysical+1)):=by
  have hfixed (T:Finset α):=natural_low_source_bound (ι:=T) W hW aslot bslot lo hi
    a b bΦ Mcap εdiag ξ saving haslot hWs hbslot ha hb hbΦ hMcap hεdiag hξ
  choose Ψ hΨs hΨn Cj hCj hbound using hfixed
  let Cfixed:ℝ:=1+∑T:Finset α,Cj T
  have hCfixed:0< Cfixed:=by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCj T).le)
    dsimp [Cfixed];linarith
  have hCC (T:Finset α):Cj T≤ Cfixed:=by
    have hh:=Finset.single_le_sum (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCj T).le)
      (Finset.mem_univ T)
    dsimp [Cfixed];linarith
  refine ⟨Ψ,hΨs,hΨn,Cfixed,hCfixed,?_⟩
  have hall:∀ᶠZ:ℝ in atTop,∀T:Finset α,_:=Filter.eventually_all.mpr hbound
  filter_upwards [hall,eventually_gt_atTop (1:ℝ)] with Z hZ hZ1
  refine ⟨hZ1,?_⟩
  intro Bmask L Lslot rho κ e η₀ Q S J Cphysical hκ hCphysical he hsave hold hmass
  have hpositive:PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q
      J (insert (0,0) S) (Cfixed*(Cphysical+1)):=by
    intro T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hwidth
      p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlow
    by_cases hsmall:state.width≤ rho
    · exact hold T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
        state hQ hsmall p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity
    have hp:=hmass T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
      state hQ (le_of_not_ge hsmall) hwidth p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlow
    have hh:=(hZ T).2 M H hH η₀ θ w σ freq hw (fun i=>⟨hσlo i,hσhi i⟩)
      Bmask state p t X₁ X₂ hX₁ hX₂ κ hκ (hcapacity.trans hwidth)
      S J Cphysical height e hCphysical hheight he hsave hp
    have hc:=hCC T
    have hd:=diagonalControl_nonneg state.radial.profile
    have hz:0≤ Z:=zero_le_one.trans hZ1.le
    apply hh.trans
    gcongr
  exact ⟨hpositive,CenteredMomentEnergyLowBandEmpty.positive_low_zero (α:=α) M H hH
    W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q J (insert (0,0) S)
    (Cfixed*(Cphysical+1)) hpositive⟩

end CenteredMomentEnergyPositiveLowBandSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentEnergyPositiveLowSourceControlled
open HeckeFamily  InversePrincipalEnergy
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentFiniteProfileExceptional
open CenteredMomentFirstSourceReduction CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
local notation "O"=> Eisenstein.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open CenteredMomentEnergyPositiveLowBandSource (PhysicalLowAt)
open CenteredMomentEnergyBandMonotonicity

theorem actual_low_stages_from_physical
    (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi a b bΦ Mcap εdiag ξ saving:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤ bslot)(ha:0< a)(hb:0≤ b)(hbΦ:0< bΦ)(hMcap:0≤ Mcap)
    (hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:(T:Finset α)→𝓢(ℝ,ℂ),
      (∀T,Function.support (Ψ T:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1)) ∧
      (∀T x,0≤(Ψ T x).re) ∧∃Cfixed:ℝ,0< Cfixed ∧
    ∀ᶠZ:ℝ in atTop,1< Z ∧
    ∀(Bmask L Lslot rho κ e:ℝ)(η₀:Character)(Q:Ideal O)(S:Finset (ℕ×ℕ))(J:ℕ)(Cphysical Cprevious:ℝ),
      1/6≤κ→0≤ Cphysical→0≤ Cprevious→εdiag≤ e→-saving≤ e→
      PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho e κ Z η₀ Q
        J S Cprevious→
      PhysicalLowAt (α:=α) M H hH W hW aslot bslot lo hi haslot hWs
        a b bΦ Bmask L Lslot rho Mcap κ ξ e Z ha Ψ η₀ Q S J Cphysical→
      PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q
        J (insert (0,0) S) (Cfixed*(Cphysical+1)+Cprevious) ∧
      ZeroLowAt (internalQ Q η₀) a b bΦ Bmask L Mcap e Z J (insert (0,0) S)
        (Cfixed*(Cphysical+1)+Cprevious) :=by
  obtain ⟨Ψ,hΨs,hΨn,Cfixed,hCfixed,hbound⟩:=
    CenteredMomentEnergyPositiveLowBandSource.actual_low_stages_from_physical (α:=α) M H hH
      W hW aslot bslot lo hi a b bΦ Mcap εdiag ξ saving haslot hWs hbslot ha hb hbΦ
      hMcap hεdiag hξ
  refine ⟨Ψ,hΨs,hΨn,Cfixed,hCfixed,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask L Lslot rho κ e η₀ Q S J Cphysical Cprevious hκ hCphysical hCprevious he hsave hold hmass
  let Cm:=Cphysical+Cprevious/Cfixed
  have hdiv:0≤ Cprevious/Cfixed:=div_nonneg hCprevious hCfixed.le
  have hCm:0≤ Cm:=by dsimp [Cm];positivity
  have hcc:Cphysical≤ Cm:=by dsimp [Cm];linarith
  have heq:Cfixed*(Cm+1)=Cfixed*(Cphysical+1)+Cprevious:=by
    dsimp [Cm]
    field_simp
    ; ring
  have hprev:Cprevious≤ Cfixed*(Cm+1):=by
    rw [heq]
    have hh:0≤ Cfixed*(Cphysical+1):=by positivity
    linarith
  have hold':PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho e κ Z η₀ Q
      J (insert (0,0) S) (Cfixed*(Cm+1)):=
    positiveAt_transport (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho e κ Z
      a b bΦ Bmask L rho e η₀ Q J J S (insert (0,0) S) Cprevious (Cfixed*(Cm+1)) hZ.1.le
      le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (Finset.subset_insert _ _)
      hCprevious hprev hold
  have hmass':PhysicalLowAt (α:=α) M H hH W hW aslot bslot lo hi haslot hWs
      a b bΦ Bmask L Lslot rho Mcap κ ξ e Z ha Ψ η₀ Q S J Cm:=by
    intro T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hlo hs
      p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hlow
    have hh:=hmass T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hlo hs
      p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hlow
    have hz:0≤ Z:=zero_le_one.trans hZ.1.le
    apply hh.trans
    gcongr
  have hh:=hZ.2 Bmask L Lslot rho κ e η₀ Q S J Cm hκ hCm he hsave hold' hmass'
  simpa only [heq] using hh

end CenteredMomentEnergyPositiveLowSourceControlled

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentEnergyFirstPhysicalNormalization
open HeckeFamily CenteredMomentCommonRadialData
open CenteredMomentFirstReferenceEnergy CenteredMomentSecondWindowBudget
open CenteredMomentFirstPhysicalSource

lemma window_pair_le (J₁ J₂ : ℕ) (t L R H : ℝ) (hH : 0 ≤ H)
    (hL : L ≤ H) (hR : R ≤ H) :
    windowBudget J₁ t L * windowBudget J₂ t R ≤
      H * heightEnvelope t ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ := by
  have hs : Real.sqrt L * Real.sqrt R ≤ H := by
    calc
      _ ≤ Real.sqrt H * Real.sqrt H :=
        mul_le_mul (Real.sqrt_le_sqrt hL) (Real.sqrt_le_sqrt hR)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = H := Real.mul_self_sqrt hH
  have hp := mul_le_mul_of_nonneg_right hs
    (show 0 ≤ heightEnvelope t ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ by
      exact mul_nonneg (mul_nonneg (pow_nonneg (heightEnvelope_pos t).le _)
        (profileMoment_nonneg _)) (profileMoment_nonneg _))
  convert hp using 1 <;> (try simp only [windowBudget, pow_add]) <;> (first | rfl | ring)

theorem pairedBudget_le_cap (J₁ J₂ : ℕ) (t H : ℝ) (EL ER : Fin 4 → ℝ)
    (hH : 0 ≤ H) (hL : ∀ i, EL i ≤ H) (hR : ∀ j, ER j ≤ H) :
    pairedBudget J₁ J₂ t EL ER ≤
      16 * H * heightEnvelope t ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ := by
  have hh : pairedBudget J₁ J₂ t EL ER ≤
      ∑ _i : Fin 4, ∑ _j : Fin 4,
        H * heightEnvelope t ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ := by
    exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
      window_pair_le J₁ J₂ t (EL i) (ER j) H hH (hL i) (hR j)))
  apply hh.trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num
  ring

theorem pairedBudget_le_powers (J₁ J₂ : ℕ) (t Z F Mdecl M₀ ell : ℝ)
    (lossL lossR EL ER : Fin 4 → ℝ) (hZ : 1 ≤ Z) (hF : 0 ≤ F)
    (hL : ∀ i, EL i ≤ F * Z ^ (Mdecl - M₀ + lossL i))
    (hR : ∀ j, ER j ≤ F * Z ^ (Mdecl - M₀ + lossR j))
    (hellL : ∀ i, lossL i ≤ ell) (hellR : ∀ j, lossR j ≤ ell) :
    pairedBudget J₁ J₂ t EL ER ≤
      16 * F * Z ^ (Mdecl - M₀ + ell) * heightEnvelope t ^ (J₁ + J₂) *
        profileMoment J₁ * profileMoment J₂ := by
  have hcap := pairedBudget_le_cap J₁ J₂ t (F * Z ^ (Mdecl - M₀ + ell)) EL ER
    (mul_nonneg hF (Real.rpow_nonneg (by linarith) _))
    (fun i => (hL i).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith [hellL i])) hF))
    (fun j => (hR j).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith [hellR j])) hF))
  simpa only [mul_assoc] using hcap

theorem physical_power_identity (Z K q Mdecl ell : ℝ) (hZ : 1 < Z)
    (hK : 0 < K) (hq : 0 < q) :
    K * q * Z ^ (Mdecl - (Real.logb Z K + Real.logb Z q) + ell) =
      Z ^ (Mdecl + ell) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hKq : K * q = Z ^ (Real.logb Z K + Real.logb Z q) := by
    rw [Real.rpow_add hz, Real.rpow_logb hz hZ.ne' hK, Real.rpow_logb hz hZ.ne' hq]
  rw [hKq, ← Real.rpow_add hz]
  congr 1
  ring

lemma character_power_identity (η : Character) (Z K Mdecl ell : ℝ)
    (hZ : 1 < Z) (hK : 0 < K) :
    K * (η.modulus.absNorm : ℝ) *
      Z ^ (Mdecl - (Real.logb Z K + Real.logb Z (η.modulus.absNorm : ℝ)) + ell) =
      Z ^ (Mdecl + ell) := by
  apply physical_power_identity Z K _ Mdecl ell hZ hK
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)

lemma heightEnvelope_le (t : ℝ) :
    heightEnvelope t ≤ (1 + 2 * Real.pi) ^ 2 * (1 + ‖t‖) := by
  unfold heightEnvelope
  nlinarith [norm_nonneg t, Real.pi_pos, mul_nonneg (norm_nonneg t) Real.pi_pos.le]

lemma heightEnvelope_pow_le (J : ℕ) (t : ℝ) :
    heightEnvelope t ^ J ≤ (1 + 2 * Real.pi) ^ (2 * J) * (1 + ‖t‖) ^ J := by
  have hh := pow_le_pow_left₀ (heightEnvelope_pos t).le (heightEnvelope_le t) J
  simpa only [mul_pow, ← pow_mul] using hh

def normalizationConstant (lowerProduct : ℝ) : ℝ :=
  16 * (Real.exp (Real.log 4) / lowerProduct) * fixedPresentationCost

lemma normalizationConstant_pos (lowerProduct : ℝ) (hlower : 0 < lowerProduct) :
    0 < normalizationConstant lowerProduct := by
  unfold normalizationConstant
  exact mul_pos (mul_pos (by norm_num) (div_pos (Real.exp_pos _) hlower))
    fixedPresentationCost_pos

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem sourceFactor_pairedBudget_le (lowerProduct : ℝ) (hlower : 0 < lowerProduct)
    (s : Input ι) (a₁ a₂ K Z F Mdecl ell : ℝ) (J₁ J₂ : ℕ)
    (lossL lossR EL ER : Fin 4 → ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hK : 0 < K) (hZ : 1 < Z) (hF : 0 ≤ F)
    (hsupport : lowerProduct ≤ (∏ i, s.lo i) * a₁ * a₂)
    (hL : ∀ i, EL i ≤ F * Z ^
      (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + lossL i))
    (hR : ∀ j, ER j ≤ F * Z ^
      (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + lossR j))
    (hellL : ∀ i, lossL i ≤ ell) (hellR : ∀ j, lossR j ≤ ell) :
    sourceFactor s a₁ a₂ K * pairedBudget J₁ J₂ s.t EL ER ≤
      normalizationConstant lowerProduct * F * Z ^ (Mdecl + ell) *
        heightEnvelope s.t ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ := by
  have hbudget := pairedBudget_le_powers J₁ J₂ s.t Z F Mdecl
    (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) ell
    lossL lossR EL ER hZ.le hF hL hR hellL hellR
  have hsource := sourceFactor_nonneg s a₁ a₂ K ha₁ ha₂ hK
  have hden := div_le_div_of_nonneg_left (Real.exp_pos (Real.log 4)).le hlower hsupport
  have hmass : 0 ≤ (s.η.modulus.absNorm : ℝ) := Nat.cast_nonneg _
  have hpresent := fixedPresentationCost_pos.le
  have hsource' : sourceFactor s a₁ a₂ K ≤
      (Real.exp (Real.log 4) / lowerProduct) * fixedPresentationCost * K *
        (s.η.modulus.absNorm : ℝ) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hden hpresent) hK.le) hmass
  have hbound := (mul_le_mul_of_nonneg_left hbudget hsource).trans
    (mul_le_mul_of_nonneg_right hsource'
      (show 0 ≤ 16 * F * Z ^
          (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + ell) *
          heightEnvelope s.t ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ by
        have hp₁ := profileMoment_nonneg J₁
        have hp₂ := profileMoment_nonneg J₂
        have hh := (heightEnvelope_pos s.t).le
        have hz := zero_lt_one.trans hZ
        positivity))
  apply hbound.trans_eq
  dsimp [normalizationConstant]
  have hid := character_power_identity s.η Z K Mdecl ell hZ hK
  calc
    _ = (16 * (Real.exp (Real.log 4) / lowerProduct) * fixedPresentationCost) * F *
        (K * (s.η.modulus.absNorm : ℝ) * Z ^
          (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + ell)) *
        heightEnvelope s.t ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ := by ring
    _ = _ := by rw [hid]

def polynomialConstant (lowerProduct : ℝ) (J₁ J₂ : ℕ) : ℝ :=
  normalizationConstant lowerProduct * (1 + 2 * Real.pi) ^ (2 * (J₁ + J₂))

lemma polynomialConstant_pos (lowerProduct : ℝ) (J₁ J₂ : ℕ)
    (hlower : 0 < lowerProduct) : 0 < polynomialConstant lowerProduct J₁ J₂ := by
  exact mul_pos (normalizationConstant_pos lowerProduct hlower) (pow_pos (by positivity) _)

omit [DecidableEq ι] in
theorem sourceFactor_pairedBudget_polynomial (lowerProduct : ℝ) (hlower : 0 < lowerProduct)
    (s : Input ι) (a₁ a₂ K Z F Mdecl ell : ℝ) (J₁ J₂ : ℕ)
    (lossL lossR EL ER : Fin 4 → ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hK : 0 < K) (hZ : 1 < Z) (hF : 0 ≤ F)
    (hsupport : lowerProduct ≤ (∏ i, s.lo i) * a₁ * a₂)
    (hL : ∀ i, EL i ≤ F * Z ^
      (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + lossL i))
    (hR : ∀ j, ER j ≤ F * Z ^
      (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + lossR j))
    (hellL : ∀ i, lossL i ≤ ell) (hellR : ∀ j, lossR j ≤ ell) :
    sourceFactor s a₁ a₂ K * pairedBudget J₁ J₂ s.t EL ER ≤
      polynomialConstant lowerProduct J₁ J₂ * F * Z ^ (Mdecl + ell) *
        (1 + ‖s.t‖) ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ := by
  have hh := sourceFactor_pairedBudget_le lowerProduct hlower s a₁ a₂ K Z F Mdecl ell
    J₁ J₂ lossL lossR EL ER ha₁ ha₂ hK hZ hF hsupport hL hR hellL hellR
  have hm₁ := profileMoment_nonneg J₁
  have hm₂ := profileMoment_nonneg J₂
  have hconst := (normalizationConstant_pos lowerProduct hlower).le
  have hz := zero_lt_one.trans hZ
  apply hh.trans
  calc
    _ ≤ normalizationConstant lowerProduct * F * Z ^ (Mdecl + ell) *
        ((1 + 2 * Real.pi) ^ (2 * (J₁ + J₂)) * (1 + ‖s.t‖) ^ (J₁ + J₂)) *
        profileMoment J₁ * profileMoment J₂ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (heightEnvelope_pow_le (J₁ + J₂) s.t)
          (by positivity)) hm₁) hm₂
    _ = _ := by unfold polynomialConstant; ring

theorem uniform_source_normalization (lowerProduct : ℝ) (hlower : 0 < lowerProduct)
    (J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
    ∀ (s : Input ι) (a₁ a₂ K Z F Mdecl ell : ℝ) (lossL lossR EL ER : Fin 4 → ℝ),
    0 < a₁ → 0 < a₂ → 0 < K → 1 < Z → 0 ≤ F →
    lowerProduct ≤ (∏ i, s.lo i) * a₁ * a₂ →
    (∀ i, EL i ≤ F * Z ^
      (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + lossL i)) →
    (∀ j, ER j ≤ F * Z ^
      (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + lossR j)) →
    (∀ i, lossL i ≤ ell) → (∀ j, lossR j ≤ ell) →
    sourceFactor s a₁ a₂ K * pairedBudget J₁ J₂ s.t EL ER ≤
      C * F * Z ^ (Mdecl + ell) * (1 + ‖s.t‖) ^ (J₁ + J₂) *
        profileMoment J₁ * profileMoment J₂ := by
  refine ⟨polynomialConstant lowerProduct J₁ J₂,
    polynomialConstant_pos lowerProduct J₁ J₂ hlower, ?_⟩
  intro ι _ _ s a₁ a₂ K Z F Mdecl ell lossL lossR EL ER ha₁ ha₂ hK hZ hF hs hL hR heL heR
  exact sourceFactor_pairedBudget_polynomial lowerProduct hlower s a₁ a₂ K Z F Mdecl ell
    J₁ J₂ lossL lossR EL ER ha₁ ha₂ hK hZ hF hs hL hR heL heR

open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentFirstSourceReduction
open CenteredMomentFirstReferenceSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSourceMass CenteredMomentFirstNonexceptionalWeightSum
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem actual_physical_mass_of_columnBounds (W : 𝓢(ℝ, ℂ)) (J₁ J₂ : ℕ)
    (hi : ι → ℝ) (b₁ b₂ B ξ ε lowerProduct : ℝ)
    (hB : 0 ≤ B) (hξ : 0 ≤ ξ) (hε : 0 < ε) (hlower : 0 < lowerProduct) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ s : Input ι, ∀ R seed : Ideal Eisenstein.O,
      Squarefree seed → seed ≠ 0 → (∀ i, |s.hi i| ≤ hi i) → |s.b₁| ≤ b₁ → |s.b₂| ≤ b₂ →
      ∀ a₁ a₂ K : ℝ, 0 < a₁ → 0 < a₂ → 0 < K →
      lowerProduct ≤ (∏ i, s.lo i) * a₁ * a₂ →
      (∀ x, s.W₁ x ≠ 0 → a₁ ≤ x) → (∀ x, s.W₂ x ≠ 0 → a₂ ≤ x) →
      CenteredMomentExceptionalAmplitudePair.volume s.toData ≤ Z ^ B → K⁻¹ ≤ Z ^ B →
      ∀ (F Mdecl ell : ℝ) (lossL lossR EL ER : Fin 4 → ℝ), 0 ≤ F →
      (∀ i, 0 ≤ EL i) → (∀ j, 0 ≤ ER j) →
      (∀ i, EL i ≤ F * Z ^
        (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + lossL i)) →
      (∀ j, ER j ≤ F * Z ^
        (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + lossR j)) →
      (∀ i, lossL i ≤ ell) → (∀ j, lossR j ≤ ell) →
      (∀ p : Labels s R seed, ∀ E ∈ CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
        ∀ n : SourceBlocks s R seed K Z ξ p E,
        originalBlock s R seed W K Z ξ p E n ≠ 0 →
          ColumnBounds s R seed Z J₁ J₂ EL ER p E (fun i => (n i).val)) →
      physicalMass s R seed CenteredMomentSecondHeightFamily.fixedBadMask 1 W K Z ξ /
          CenteredMomentExceptionalAmplitudePair.volume s.toData ≤
        C * F * Z ^ (Mdecl + ell + ε) / (seed.absNorm : ℝ) *
          (1 + ‖s.t‖) ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ := by
  obtain ⟨Cb, hCb, hbound⟩ := actual_physical_mass W J₁ J₂ hi b₁ b₂ B ξ ε hB hξ hε
  refine ⟨Cb * polynomialConstant lowerProduct J₁ J₂,
    mul_pos hCb (polynomialConstant_pos lowerProduct J₁ J₂ hlower), ?_⟩
  filter_upwards [hbound, eventually_gt_atTop (1 : ℝ)] with Z hbound hZ
  intro s R seed hseed hseed₀ hhi hb₁ hb₂ a₁ a₂ K ha₁ ha₂ hK hsupport hs₁ hs₂ hV hKi
    F Mdecl ell lossL lossR EL ER hF hEL hER hL hR heL heR hcols
  have hphysical := hbound s R seed hseed hseed₀ hhi hb₁ hb₂ a₁ a₂ K ha₁ ha₂ hK
    hs₁ hs₂ hV hKi EL ER hEL hER hcols
  have hnormal := sourceFactor_pairedBudget_polynomial lowerProduct hlower s a₁ a₂ K Z
    F Mdecl ell J₁ J₂ lossL lossR EL ER ha₁ ha₂ hK hZ hF hsupport hL hR heL heR
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hp : 0 ≤ Cb * Z ^ ε / (seed.absNorm : ℝ) := by positivity
  calc
    _ ≤ Cb * Z ^ ε / (seed.absNorm : ℝ) * sourceFactor s a₁ a₂ K *
        pairedBudget J₁ J₂ s.t EL ER := hphysical
    _ = (Cb * Z ^ ε / (seed.absNorm : ℝ)) *
        (sourceFactor s a₁ a₂ K * pairedBudget J₁ J₂ s.t EL ER) := by ring
    _ ≤ (Cb * Z ^ ε / (seed.absNorm : ℝ)) *
        (polynomialConstant lowerProduct J₁ J₂ * F * Z ^ (Mdecl + ell) *
          (1 + ‖s.t‖) ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂) :=
      mul_le_mul_of_nonneg_left hnormal hp
    _ = _ := by
      rw [show Z ^ (Mdecl + ell + ε) = Z ^ (Mdecl + ell) * Z ^ ε from
        Real.rpow_add hz (Mdecl + ell) ε]
      ring

end CenteredMomentEnergyFirstPhysicalNormalization

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentEnergyFirstColumnPairing
open HeckeFamily CanonicalQuadraticSieve  CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstReferenceSource CenteredMomentFirstReferenceEnergy
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily CenteredMomentCanonicalFirst
open CenteredMomentAmplificationChildInput CenteredMomentGaussEnergy
open CenteredMomentFirstMixedAllowance CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentSecondRetainedAggregate CenteredMomentChildAssembly
open CenteredMomentFirstNonexceptionalWeightSum
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma fixed_pair_moduli (η:Character)(C D:Ideal O)(hC:Supported C)
    (E:Finset (CommonIndex C D))(χ:RayCharacter):
    (fixedPair η C D hC E χ χ).left.modulus=(fixedPair η C D hC E 1 1).left.modulus ∧
    (fixedPair η C D hC E χ χ).right.modulus=(fixedPair η C D hC E 1 1).right.modulus:=by
  constructor
  · rw [(fixedPair η C D hC E χ χ).left_modulus,
      (fixedPair η C D hC E 1 1).left_modulus]
  · rw [(fixedPair η C D hC E χ χ).right_modulus,
      (fixedPair η C D hC E 1 1).right_modulus]

lemma reference_sum (ref seed front Z:ℝ)(loss:Fin 4→ℝ)(v:ℝ)(J:ℕ):
    (ref/seed)*(front*∑j:Fin 4,Z^(loss j))*(1+|v|)^(2*J)=
      ((∑j:Fin 4,ref*(front*Z^(loss j)))/seed)*(1+‖v‖)^(2*J):=by
  rw [Real.norm_eq_abs]
  simp only [←Finset.mul_sum]
  ring

omit [DecidableEq ι] in
theorem column_bounds_of_reference_sums
    (s:Input ι)(R seed:Ideal O)(Z:ℝ)(Jleft Jright:ℕ)
    (frontLeft frontRight:ℝ)(lossLeft lossRight:Fin 4→ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))(n:Fin 4→ℤ)
    (hleft:∀L:Ideal O,(L.absNorm:ℝ)≤ sourceRadius s/(p.val.2.absNorm:ℝ)→
      Squarefree L→∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy (original s R seed) p.val.1 (supported s R seed p).1
        (fixedPair s.η p.val.1 p.val.2 (supported s R seed p).1 E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
        (((fixedPair s.η p.val.1 p.val.2 (supported s R seed p).1 E χ χ).left.modulus.absNorm:ℝ)*
            (CenteredMomentExceptionalAmplitudePair.volume s.toData/(p.val.1.absNorm:ℝ))^2*Z^(allowance p.val.1 p.val.2 Z)/(L.absNorm:ℝ))*
          (frontLeft*∑j:Fin 4,Z^(lossLeft j))*(1+|v|)^(2*Jleft))
    (hright:∀L:Ideal O,(L.absNorm:ℝ)≤ sourceRadius s/(p.val.2.absNorm:ℝ)→
      Squarefree L→∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy (original s R seed) p.val.2 (supported s R seed p).2
        (fixedPair s.η p.val.1 p.val.2 (supported s R seed p).1 E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
        (((fixedPair s.η p.val.1 p.val.2 (supported s R seed p).1 E χ χ).right.modulus.absNorm:ℝ)*
            (CenteredMomentExceptionalAmplitudePair.volume s.toData/(p.val.2.absNorm:ℝ))^2*Z^(allowance p.val.2 p.val.1 Z)/(L.absNorm:ℝ))*
          (frontRight*∑j:Fin 4,Z^(lossRight j))*(1+|v|)^(2*Jright)):
    ColumnBounds s R seed Z Jleft Jright
      (fun j=> frontLeft*Z^(lossLeft j)) (fun j=> frontRight*Z^(lossRight j)) p E n:=by
  constructor
  · intro L _ hcap hL χ v
    have hh:=hleft L hcap hL χ v
    rw [(fixed_pair_moduli s.η p.val.1 p.val.2 (supported s R seed p).1 E χ).1] at hh
    exact hh.trans_eq (reference_sum _ _ _ _ _ _ _)
  · intro L _ hcap hL χ v
    have hh:=hright L hcap hL χ v
    rw [(fixed_pair_moduli s.η p.val.1 p.val.2 (supported s R seed p).1 E χ).2] at hh
    exact hh.trans_eq (reference_sum _ _ _ _ _ _ _)

end CenteredMomentEnergyFirstColumnPairing

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

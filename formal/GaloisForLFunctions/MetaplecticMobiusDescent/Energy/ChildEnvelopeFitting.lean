/-
Child envelope fitting adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.SecondExceptionalFamilies
import GaloisForLFunctions.MetaplecticMobiusDescent.Energy.EnergyBands

/-!
# Child envelope fitting

Envelope coefficients and paid right-hand sides of child fitting; allocated child energies and
profiles; inherited slot heights, canonical child states and capacity removal.
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

namespace CenteredMomentEnergyCapacityRemoval
open HeckeFamily  CenteredMomentRetainedEnergy
open CenteredMomentInductionEnergy CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot
open CenteredMomentSlotNormalization CenteredMomentRelativeCapacityRemoval
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentEnergyState
open CenteredExceptionalProfile CenteredMomentFixedRowMask
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem compact_radial_summable (f : O→ℂ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ))
    (K b : ℝ) (hK : 0< K) (hs : Function.support (Φ:ℝ→ℂ)⊆Set.Iic b) :
    Summable (fun z : O=> if keep z then ‖f z‖^2*(Φ (‖ringComplex z‖^2/K)).re else 0) := by
  obtain ⟨N,hN⟩:=exists_nat_ge (b*K)
  apply summable_of_ne_finset_zero
    (s := (Eisenstein.finite_norm_sublevel (Real.sqrt (N:ℝ))).toFinset)
  intro z hz
  have hΦ : Φ (‖ringComplex z‖^2/K)=0 := by
    by_contra hn
    have hh : ‖ringComplex z‖^2≤(N:ℝ):=((div_le_iff₀ hK).mp (hs hn)).trans hN
    apply hz
    rw [Set.Finite.mem_toFinset]
    change ‖ringComplex z‖ ≤ Real.sqrt (N:ℝ)
    calc
      _ = Real.sqrt (‖ringComplex z‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt hh
  simp [hΦ]

omit [DecidableEq ι] in

theorem energy_support (η : Character) (m A : O) (t : ℝ) (W₁ W₂ : ℝ→ℂ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K=
      energy η m A t W₁ W₂ S β P X₁ X₂
        (fun z=> keep z ∧ Φ (‖ringComplex z‖^2/K)≠0) Φ K := by
  unfold energy
  apply tsum_congr
  intro z
  by_cases hk : keep z <;> by_cases hp : Φ (‖ringComplex z‖^2/K)=0 <;> simp [hk,hp]

omit [Fintype ι] in

theorem selected_eq_positive (J : Finset ι) (η : Character) (m A z : O)
    (W₁ W₂ : ℝ→ℂ) (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ)
    (P : ι→ℝ) (t X₁ X₂ : ℝ) (hX : 0≤ X₁*X₂) (hP : ∀i,0≤ P i) :
    selectedProduct J η m A z W₁ W₂ S β P t X₁ X₂=
      positiveSlotRow η m A z W₁ W₂ (fun i:J=> S i) (fun i:J=>β i)
        (fun i:J=> P i) t X₁ X₂ := by
  have hh:=selectedProduct_univ η m A z W₁ W₂
    (fun i:J=> S i) (fun i:J=>β i) (fun i:J=> P i) t X₁ X₂ hX (fun i=> hP i)
  have hp : (∏i:J,normalizedSlot η m A z (S i) (β i) t (P i))=
      ∏i∈J,normalizedSlot η m A z (S i) (β i) t (P i) :=
    Finset.prod_coe_sort J (fun i=> normalizedSlot η m A z (S i) (β i) t (P i))
  unfold selectedProduct at hh ⊢
  rw [hp] at hh
  exact hh

theorem unit_puncture_energy (η : Character) (t : ℝ) (W₁ W₂ : ℝ→ℂ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (X₁ X₂ : ℝ)
    (keep : O→Prop) (hz : ∀z,keep z→z≠0) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy η (fixedBadMask*cubicIdealGenerator 1) 1 t W₁ W₂ S β P X₁ X₂ keep Φ K=
      energy η fixedBadMask 1 t W₁ W₂ S β P X₁ X₂ keep Φ K := by
  unfold energy
  apply tsum_congr
  intro z
  by_cases hk : keep z
  · simp only [if_pos hk]
    rw [natural_unit_mask_positive (naturalRow η z (hz z hk))]
  · simp only [if_neg hk]

theorem eventual_state_conductor (bΦ Mcap : ℝ) (hb : 0≤ bΦ) :
    ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀Bmask:ℝ,∀s:NaturalState Z Bmask bΦ,
      s.width≤ Mcap → ∀z:O,∀hz:z≠0,
      s.radial.profile (‖ringComplex z‖^2/s.radial.scale)≠0 →
      ((naturalRow s.character z hz).character.modulus.absNorm:ℝ)≤ Z^(Mcap+1) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_ge_atTop ((fixedConductorFactor:ℝ)*bΦ)] with Z hZ hF
  refine ⟨hZ,?_⟩
  intro Bmask s hwidth z hz hΦ
  have hn : ((Ideal.span {z}).absNorm:ℝ)≤ bΦ*Z^s.rowWidth := by
    rw [←ringComplex_norm_sq_eq_absNorm_span,←s.scale_eq]
    exact (div_le_iff₀ s.radial.scale_pos).mp (s.radial_support hΦ)
  have he:=(naturalRow s.character z hz).modulus_power_bound Z s.characterWidth s.rowWidth bΦ
    (zero_lt_one.trans hZ) hb s.modulus_bound hn
  have hm:Z^(s.characterWidth+s.rowWidth)≤ Z^Mcap:=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by simpa [NaturalState.width,add_comm] using hwidth)
  apply he.trans
  calc
    _≤ Z*Z^Mcap:=mul_le_mul hF hm (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
      (zero_lt_one.trans hZ).le
    _=Z^(Mcap+1):=by rw [Real.rpow_add (zero_lt_one.trans hZ),Real.rpow_one];ring

theorem eventual_row_conductor (bΦ Mrow : ℝ) (hb : 0≤ bΦ) :
    ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀Bmask:ℝ,∀s:NaturalState Z Bmask bΦ,
      s.rowWidth≤ Mrow → ∀q:ℝ,(s.character.modulus.absNorm:ℝ)≤ Z^q →
      ∀z:O,∀hz:z≠0,s.radial.profile (‖ringComplex z‖^2/s.radial.scale)≠0 →
      ((naturalRow s.character z hz).character.modulus.absNorm:ℝ)≤ Z^(Mrow+q+1) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_ge_atTop ((fixedConductorFactor:ℝ)*bΦ)] with Z hZ hF
  refine ⟨hZ,?_⟩
  intro Bmask s hrow q hq z hz hΦ
  have hn : ((Ideal.span {z}).absNorm:ℝ)≤ bΦ*Z^s.rowWidth := by
    rw [←ringComplex_norm_sq_eq_absNorm_span,←s.scale_eq]
    exact (div_le_iff₀ s.radial.scale_pos).mp (s.radial_support hΦ)
  have he:=(naturalRow s.character z hz).modulus_power_bound Z q s.rowWidth bΦ
    (zero_lt_one.trans hZ) hb hq hn
  have hm:Z^(q+s.rowWidth)≤ Z^(Mrow+q):=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  apply he.trans
  calc
    _≤ Z*Z^(Mrow+q):=mul_le_mul hF hm (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
      (zero_lt_one.trans hZ).le
    _=Z^(Mrow+q+1):=by
      conv_rhs => rw [Real.rpow_add (zero_lt_one.trans hZ),Real.rpow_one]
      ring

lemma state_unit_nonexceptional {Z Bmask bΦ : ℝ} (s : NaturalState Z Bmask bΦ)
    (hpuncture : s.puncture=1) (Q : Ideal O) (hQ : s.fixedModulus=Q)
    (z : O) (hk : s.radial.keep z) : ¬FixedInducingRow s.character Q fixedBadMask 1 z := by
  intro hh
  apply s.nonexceptional z hk
  rw [hQ,hpuncture]
  exact (fixedInducingRow_mul_mask_iff s.character Q fixedBadMask
    (cubicIdealGenerator 1) 1 z fixedBadMask_ne_zero
    (cubicIdealGenerator_ne_zero 1 one_ne_zero) one_ne_zero (s.row_ne_zero z hk)
    (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr hh

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
include hH

theorem actual_state_capacity_removal
    (W : ι→ℝ→ℂ) (a b : ι→ℝ) (ha : ∀i,0< a i)
    (hWs : ∀i,Function.support (W i)⊆Set.Icc (a i) (b i))
    (hW : ∀i,ContDiff ℝ ∞ (W i))
    (Mrow bΦ Lmod Lslot ε lo hi κ : ℝ) (hbΦ : 0≤ bΦ)
    (hLm : 0≤ Lmod) (hLs : 0≤ Lslot) (hε : 0<ε)
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ) :
    ∃degree:ℕ,∃C:ℝ,0< C ∧ ∀ν:ι→Character,∃Z₀:ℝ,1< Z₀ ∧
    ∀(J:Finset ι)(w:ι→ℝ)(n₁ n₂ width mesh:ℝ),0≤ mesh →
      (∀i,0≤ w i) → (∀i,w i≤ mesh) → (∀i,w i≤ Lslot) →
    ∃R:Finset ι,R⊆J ∧ (R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤ width) ∧
      κ*(∑i∈R,w i)≤ CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh ∧
    ∀Z:ℝ,Z₀≤ Z → ∀Bmask:ℝ,∀s:NaturalState Z Bmask bΦ,
      s.puncture=1 → s.rowWidth≤ Mrow → ∀q:ℝ,
      (s.character.modulus.absNorm:ℝ)≤ Z^q → Mrow+q+1≤ Lmod →
    ∀Q:Ideal O,s.fixedModulus=Q → Q≤ M → (∀i,Q≤(ν i).modulus) →
    ∀(σ freq:ι→ℝ)(t V:ℝ),(∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ V → (∀i,|freq i|≤ V) →
    ∀(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ),0< X₁ → 0< X₂ →
      let P:=fun i=> Z^(w i)
      let S:=fun i=> primePool M H (b i) (P i)
      let coeff:=fun i I=> idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (W i) (P i) (σ i) (freq i) I
      energy s.character s.mask 1 t W₁ W₂ (fun i:J=> S i) (fun i:J=> coeff i)
        (fun i:J=> P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
        C*(1+|t|+V)^degree*Z^(ε+CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh)*
          energy s.character s.mask 1 t W₁ W₂ (fun i:↥(J\R)=> S i) (fun i:↥(J\R)=> coeff i)
            (fun i:↥(J\R)=> P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale := by
  obtain ⟨degree,C,hC,hbound⟩:=actual_relative_capacity_removal M H hH W a b ha hWs hW
    Lmod Lslot ε lo hi κ hLm hLs hε hbeta hκ
  obtain ⟨Zsupport,hsupport⟩:=eventually_atTop.mp (eventual_row_conductor bΦ Mrow hbΦ)
  refine ⟨degree,C,hC,?_⟩
  intro ν
  obtain ⟨Zbase,hZbase,hbound⟩:=hbound ν
  refine ⟨max Zbase Zsupport,lt_of_lt_of_le hZbase (le_max_left _ _),?_⟩
  intro J w n₁ n₂ width mesh hmesh hw hwm hwcap
  obtain ⟨R,hR,hcapacity,hcost,hpoint⟩:=hbound J w n₁ n₂ width mesh hmesh hw hwm hwcap
  refine ⟨R,hR,hcapacity,hcost,?_⟩
  intro Z hZ Bmask s hpuncture hrow q hmod hLmod Q hQ hQM hQν σ freq t V hσ hσhi hV hfreq W₁ W₂ X₁ X₂ hX₁ hX₂
  dsimp only
  have hZbase' : Zbase≤ Z:=(le_max_left _ _).trans hZ
  have hs:=(hsupport Z ((le_max_right _ _).trans hZ))
  have hZpos:0< Z:=zero_lt_one.trans hs.1
  have hscale (i:ι) : 0≤ Z^(w i):=Real.rpow_nonneg hZpos.le _
  let P:=fun i=> Z^(w i)
  let S:=fun i=> primePool M H (b i) (P i)
  let coeff:=fun i I=> idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (W i) (P i) (σ i) (freq i) I
  let cost:=C*(1+|t|+V)^degree*Z^(ε+CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh)
  have hmask:s.mask=fixedBadMask*cubicIdealGenerator 1:=by rw [NaturalState.mask,hpuncture]
  rw [hmask,unit_puncture_energy _ _ _ _ _ _ _ _ _ _ s.row_ne_zero,
    unit_puncture_energy _ _ _ _ _ _ _ _ _ _ s.row_ne_zero]
  change energy s.character fixedBadMask 1 t W₁ W₂ (fun i:J=> S i) (fun i:J=> coeff i)
    (fun i:J=> P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
    cost*energy s.character fixedBadMask 1 t W₁ W₂ (fun i:↥(J\R)=> S i) (fun i:↥(J\R)=> coeff i)
    (fun i:↥(J\R)=> P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale
  have hsum (T:Finset ι):=compact_radial_summable
    (fun z=> positiveSlotRow s.character fixedBadMask 1 z W₁ W₂ (fun i:T=> S i)
      (fun i:T=> coeff i) (fun i:T=> P i) t X₁ X₂)
    s.radial.keep s.radial.profile s.radial.scale bΦ s.radial.scale_pos s.radial_support
  unfold energy
  rw [←tsum_mul_left]
  apply (hsum J).tsum_le_tsum _ ((hsum (J\R)).mul_left cost)
  intro z
  by_cases hk:s.radial.keep z
  · simp only [if_pos hk]
    by_cases hp:s.radial.profile (‖ringComplex z‖^2/s.radial.scale)=0
    · simp [hp]
    · have hz:=s.row_ne_zero z hk
      have hc:((naturalRow s.character z hz).character.modulus.absNorm:ℝ)≤ Z^Lmod:=
        (hs.2 Bmask s hrow q hmod z hz hp).trans
          (Real.rpow_le_rpow_of_exponent_le hs.1.le hLmod)
      have hh:=hpoint Z hZbase' s.character z hz (naturalRow s.character z hz) hc
        Q hQM hQν (state_unit_nonexceptional s hpuncture Q hQ z hk)
        σ freq t V hσ hσhi hV hfreq W₁ W₂ X₁ X₂
      dsimp only at hh
      rw [selected_eq_positive J s.character fixedBadMask 1 z W₁ W₂ S coeff P t X₁ X₂ (mul_pos hX₁ hX₂).le hscale,
        selected_eq_positive (J\R) s.character fixedBadMask 1 z W₁ W₂ S coeff P t X₁ X₂ (mul_pos hX₁ hX₂).le hscale] at hh
      exact (mul_le_mul_of_nonneg_right hh (s.radial.nonneg z)).trans_eq (by dsimp only [cost];ring)
  · simp only [if_neg hk,mul_zero,le_refl]

theorem actual_relative_state_capacity_removal
    (W : ι→ℝ→ℂ) (a b : ι→ℝ) (ha : ∀i,0< a i)
    (hWs : ∀i,Function.support (W i)⊆Set.Icc (a i) (b i))
    (hW : ∀i,ContDiff ℝ ∞ (W i))
    (Mrow bΦ Lmod Lslot ε lo hi κ : ℝ) (hbΦ : 0≤ bΦ)
    (hLm : 0≤ Lmod) (hLs : 0≤ Lslot) (hε : 0<ε)
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ) :
    ∃degree:ℕ,∃C:ℝ,0< C ∧ ∀η₀:Character,∀θ:ι→RayQuotient.Characters M H,
    let ν:=fun i=> relativeCharacter M H hH η₀ (θ i);
    ∃Z₀:ℝ,1< Z₀ ∧
    ∀(J:Finset ι)(w:ι→ℝ)(n₁ n₂ width mesh:ℝ),0≤ mesh →
      (∀i,0≤ w i) → (∀i,w i≤ mesh) → (∀i,w i≤ Lslot) →
    ∃R:Finset ι,R⊆J ∧ (R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤ width) ∧
      κ*(∑i∈R,w i)≤ CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh ∧
    ∀Z:ℝ,Z₀≤ Z → ∀Bmask:ℝ,∀s:NaturalState Z Bmask bΦ,
      s.puncture=1 → s.rowWidth≤ Mrow → ∀q:ℝ,
      (s.character.modulus.absNorm:ℝ)≤ Z^q → Mrow+q+1≤ Lmod →
    ∀Q:Ideal O,s.fixedModulus=internalQ Q η₀ → Q≤ M →
    ∀(σ freq:ι→ℝ)(t V:ℝ),(∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ V → (∀i,|freq i|≤ V) →
    ∀(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ),0< X₁ → 0< X₂ →
      let P:=fun i=> Z^(w i)
      let S:=fun i=> primePool M H (b i) (P i)
      let coeff:=fun i I=> idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (W i) (P i) (σ i) (freq i) I
      energy s.character s.mask 1 t W₁ W₂ (fun i:J=> S i) (fun i:J=> coeff i)
        (fun i:J=> P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
        C*(1+|t|+V)^degree*Z^(ε+CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh)*
          energy s.character s.mask 1 t W₁ W₂ (fun i:↥(J\R)=> S i) (fun i:↥(J\R)=> coeff i)
            (fun i:↥(J\R)=> P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale := by
  obtain ⟨degree,C,hC,hbound⟩:=actual_state_capacity_removal M H hH W a b ha hWs hW
    Mrow bΦ Lmod Lslot ε lo hi κ hbΦ hLm hLs hε hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro η₀ θ
  dsimp only
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound (fun i=> relativeCharacter M H hH η₀ (θ i))
  refine ⟨Z₀,hZ₀,?_⟩
  intro J w n₁ n₂ width mesh hmesh hw hwm hwcap
  obtain ⟨R,hR,hcapacity,hcost,henergy⟩:=hbound J w n₁ n₂ width mesh hmesh hw hwm hwcap
  refine ⟨R,hR,hcapacity,hcost,?_⟩
  intro Z hZ Bmask s hpuncture hrow q hmod hLmod Q hQ hQM
  exact henergy Z hZ Bmask s hpuncture hrow q hmod hLmod (internalQ Q η₀) hQ
    (inf_le_left.trans hQM)
    (fun i=> relativeCharacter_fixedQ M H hH η₀ (θ i) (internalQ Q η₀)
      (inf_le_left.trans hQM) inf_le_right)

end CenteredMomentEnergyCapacityRemoval

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentEnergyPaidBands
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentPrimeSlot CenteredMomentRetainedEnergy
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource InversePrincipalEnergy
local notation "O" => Eisenstein.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

omit [Fintype α] in
lemma remaining_energy_bound
    (W:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C₀ C₁:ℝ)
    (hC₀:0≤ C₀)(hC₁:0≤ C₁)
    (hzero:ZeroAt (internalQ Q η₀) a b bΦ Bmask L Mcap ε Z degree S C₀)
    (hpositive:PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
      Mcap ε κ Z η₀ Q degree S C₁)
    (J R:Finset α)(θ:α→RayQuotient.Characters M H)(w σ v:α→ℝ)(t height:ℝ)
    (hw:∀i,0≤ w i)(hwL:∀i,w i≤ Lslot)(hσlo:∀i,lo≤σ i)(hσhi:∀i,σ i≤ hi)
    (hheight:0≤ height)(hv:∀i,|v i|≤ height)
    (s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=internalQ Q η₀)(hs:s.width≤ Mcap)
    (p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)(hc₁:X₁≤ Z^L)(hc₂:X₂≤ Z^L)
    (hcapacity:R=J ∨ length Z X₁+length Z X₂+6*κ*(∑i∈J\R,w i)≤ s.width):
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:↥(J\R)=> primePool M H bslot (Z^(w i)))
      (fun (i:↥(J\R)) I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i:↥(J\R)=> Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      (C₀+C₁)*diagonalControl s.radial.profile*(p.control S)^2*
        (1+|t|+height)^degree*Z^(s.width+ε) := by
  have hd:=diagonalControl_nonneg s.radial.profile
  have hp:=sq_nonneg (p.control S)
  have hz:0≤ Z^(s.width+ε):=Real.rpow_nonneg (zero_le_one.trans s.base_ge_one) _
  rcases hcapacity with hR|hcap
  · subst R
    let : IsEmpty ↥(J\J) := ⟨fun i=> by
      have hi:=Finset.mem_sdiff.mp i.property
      exact hi.2 hi.1⟩
    have he:=hzero s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
    have hid : energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i:↥(J\J)=> primePool M H bslot (Z^(w i)))
        (fun (i:↥(J\J)) I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i:↥(J\J)=> Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale =
        s.plainEnergy p t X₁ X₂ := by
      simp only [energy,positiveSlotRow,NaturalState.plainEnergy,
        Fintype.prod_empty,mul_one]
    rw [hid]
    apply he.trans
    simp only [Real.norm_eq_abs]
    have hpow:(1+|t|)^degree≤(1+|t|+height)^degree :=
      pow_le_pow_left₀ (by positivity) (by linarith) degree
    exact mul_le_mul_of_nonneg_right (mul_le_mul
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₁) hd) hp)
      hpow (by positivity) (mul_nonneg (mul_nonneg (add_nonneg hC₀ hC₁) hd) hp)) hz
  · have he:=hpositive (J\R) (fun i=>θ i) (fun i=> w i) (fun i=>σ i) (fun i=> v i)
      t height (fun i=> hw i) (fun i=> hwL i) (fun i=> hσlo i) (fun i=> hσhi i)
      hheight (fun i=> hv i) s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
      (by simpa only [Finset.sum_coe_sort] using hcap)
    apply he.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₀) hd) hp)
        (pow_nonneg (by positivity) _)) hz

end CenteredMomentEnergyPaidBands

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace CenteredMomentEnergyPaidRemoval
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyPaidBands CenteredMomentEnergyCapacityRemoval
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot InversePrincipalEnergy
local notation "O" => Eisenstein.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem actual_paid_bands (W:ℝ→ℂ)(aslot bslot Mcap bΦ Lslot εremove lo hi κ:ℝ)
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
    ∀(J:Finset α)(w σ v:α→ℝ)(t height mesh:ℝ),
    0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) → (∀i,w i≤ Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|v i|≤ height) →
    ∀s:NaturalState Z Bmask bΦ,s.puncture=1 → s.fixedModulus=internalQ Q η₀ → s.width≤ Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,0< X₁ → 0< X₂ → X₁≤ Z^L → X₂≤ Z^L →
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:J=> primePool M H bslot (Z^(w i)))
      (fun (i:J) I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i:J=> Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      Cc*(C₀+C₁)*diagonalControl s.radial.profile*(p.control S)^2*
        (1+|t|+height)^(dc+degree)*
        Z^(s.width+εchild+εremove+
          CenteredMomentLiveCapacity.excess J w (length Z X₁) (length Z X₂) s.width κ/6+κ*mesh) := by
  obtain ⟨dc,Cc,hCc,hrem⟩:=actual_relative_state_capacity_removal (ι:=α) M H hH
    (fun _=> W) (fun _=> aslot) (fun _=> bslot) (fun _=> ha) (fun _=> hWs) (fun _=> hW)
    Mcap bΦ (2*Mcap+1) Lslot εremove lo hi κ hbΦ (by linarith) hLs hε hbeta hκ
  refine ⟨dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hrem⟩:=hrem η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ a b Bmask L εchild Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    J w σ v t height mesh hmesh hw hwm hwL hσlo hσhi hheight hv s hunit hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  obtain ⟨R,hR,hcapacity,hcost,henergy⟩:=hrem J w (length Z X₁) (length Z X₂)
    s.width mesh hmesh hw hwm hwL
  have hrow:s.rowWidth≤ Mcap:=by
    have hc:=s.character_nonneg
    dsimp [NaturalState.width] at hs
    linarith
  have hq:Mcap+s.characterWidth+1≤2*Mcap+1:=by
    have hr:=s.row_nonneg
    dsimp [NaturalState.width] at hs
    linarith
  have he:=henergy Z hZ Bmask s hunit hrow s.characterWidth s.modulus_bound hq Q hQ hQM
    σ v t height hσlo hσhi hheight hv (p.profile 0) (p.profile 1) X₁ X₂ hX₁ hX₂
  dsimp only at he
  have hb:=remaining_energy_bound M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap εchild κ Z
    η₀ Q degree S C₀ C₁ hC₀ hC₁ hzero hpos J R θ w σ v t height
    hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity
  have hZp:0< Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  apply he.trans ((mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq ?_)
  simp only [pow_add,Real.rpow_add hZp]
  ring

end CenteredMomentEnergyPaidRemoval

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace CenteredMomentEnergySlotHeight
open HeckeFamily CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentHeckeSlots CenteredMomentCommonMaskEnergy
open HeckePrimeAnnular CenteredMomentPrimeSlotShift
local notation "O"=> Eisenstein.O

variable {α:Type*}[Fintype α]

lemma height_coefficient (ν:Ideal O→ℂ)(W:ℝ→ℂ)(P σ freq t:ℝ)(hP:0< P)
    (I:Ideal O)(hI:I≠0):
    heightCoefficient (fun J=>ν J*annularWeight W P σ freq J) t I=
      (P:ℂ)^(Complex.I*t)*(ν I*annularWeight W P σ (t+freq) I):=by
  have hN:0<(I.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hh:=norm_height_split (I.absNorm:ℝ) P σ t freq hN hP
  unfold heightCoefficient annularWeight
  calc
    _=(ν I*W ((I.absNorm:ℝ)/P))*
      (((((I.absNorm:ℝ)/P:ℝ):ℂ)^(-HeckeDyadic.shift σ freq))*(I.absNorm:ℂ)^(Complex.I*t)):=by ring
    _=_:=by rw [show (I.absNorm:ℂ)=((I.absNorm:ℝ):ℂ) by simp,hh];ring

lemma row_slot_phase (η:Character)(m A z:O)(pool:Finset (Ideal O))
    (β γ:Ideal O→ℂ)(phase:ℂ)(t:ℝ)(he:∀I∈pool,β I=phase*γ I):
    rowSlot η m A z pool β t=phase*rowSlot η m A z pool γ t:=by
  unfold rowSlot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [he I hI]
  ring

lemma positive_row_phase (η:Character)(m A z:O)(W₁ W₂:ℝ→ℂ)
    (pool:α→Finset (Ideal O))(β γ:α→Ideal O→ℂ)(phase:α→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(he:∀i I,I∈pool i→β i I=phase i*γ i I):
    positiveSlotRow η m A z W₁ W₂ pool β P t X₁ X₂=
      (∏i,phase i)*positiveSlotRow η m A z W₁ W₂ pool γ P t X₁ X₂:=by
  have hs (i:α):rowSlot η m A z (pool i) (β i) t=
      phase i*rowSlot η m A z (pool i) (γ i) t:=
    row_slot_phase η m A z (pool i) (β i) (γ i) (phase i) t (he i)
  unfold positiveSlotRow
  simp_rw [hs]
  rw [Finset.prod_mul_distrib]
  ring

theorem energy_phase (η:Character)(m A:O)(W₁ W₂:ℝ→ℂ)
    (pool:α→Finset (Ideal O))(β γ:α→Ideal O→ℂ)(phase:α→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ)
    (he:∀i I,I∈pool i→β i I=phase i*γ i I)(hp:∀i,‖phase i‖=1):
    energy η m A t W₁ W₂ pool β P X₁ X₂ keep Φ K=
      energy η m A t W₁ W₂ pool γ P X₁ X₂ keep Φ K:=by
  have hprod:‖∏i,phase i‖=1:=by rw [norm_prod];simp only [hp,Finset.prod_const_one]
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_row_phase η m A z W₁ W₂ pool β γ phase P t X₁ X₂ he]
  simp only [norm_mul,hprod,one_mul]

theorem inherited_height_energy (η:Character)(m A:O)(W₁ W₂:ℝ→ℂ)
    (pool:α→Finset (Ideal O))(ν:α→Ideal O→ℂ)(W:α→ℝ→ℂ)
    (P σ freq:α→ℝ)(hP:∀i,0< P i)(hpool:∀i I,I∈pool i→I≠0)
    (t rowt X₁ X₂:ℝ)(keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):
    energy η m A rowt W₁ W₂ pool
      (fun i=> heightCoefficient (fun I=>ν i I*annularWeight (W i) (P i) (σ i) (freq i) I) t)
      P X₁ X₂ keep Φ K=
    energy η m A rowt W₁ W₂ pool
      (fun i I=>ν i I*annularWeight (W i) (P i) (σ i) (t+freq i) I)
      P X₁ X₂ keep Φ K:=by
  apply energy_phase η m A W₁ W₂ pool _ _ (fun i=>(P i:ℂ)^(Complex.I*t)) P rowt X₁ X₂ keep Φ K
  · intro i I hi
    exact height_coefficient (ν i) (W i) (P i) (σ i) (freq i) t (hP i) I (hpool i I hi)
  · intro i
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (hP i) (Complex.I*t)

end CenteredMomentEnergySlotHeight

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace CenteredMomentEnergyChildState
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentEnergyState CenteredMomentSecondNonexceptionalChosenBlock
open CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst
local notation "O" => Eisenstein.O

lemma ball_support : Function.support (ballProfile:ℝ→ℂ)⊆Set.Iic (2:ℝ):=by
  intro x hx
  by_cases h:0≤ x
  · exact (CenteredMomentAmplifiedRetainedRadius.ballProfile_support_upper x h hx).le
  · exact (lt_of_not_ge h).le.trans (by norm_num)

lemma canonical_mask_nonexceptional (τ:Character)(Q R:Ideal O)(hR:R≠0)
    (n:Fin 4→ℤ)(z:O)(hz:(canonicalRadial τ Q n).keep z):
    ¬CenteredExceptionalProfile.FixedInducingRow τ Q
      (fixedBadMask*cubicIdealGenerator R) 1 z:=by
  intro hh
  exact hz.2 ((CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff τ Q
    fixedBadMask (cubicIdealGenerator R) 1 z fixedBadMask_ne_zero
    (cubicIdealGenerator_ne_zero R hR) one_ne_zero hz.1
    (dvd_mul_right _ _) (dvd_mul_left _ _)).mp hh)

def canonicalState (Z Bmask:ℝ)(hZ:1< Z)(τ:Character)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤ Z^Bmask)(n:Fin 4→ℤ)
    (hn:1≤ dyadicScale (n 1)):NaturalState Z Bmask 2 where
  character:=τ
  fixedModulus:=Q
  puncture:=R
  radial:=canonicalRadial τ Q n
  rowWidth:=Real.logb Z (dyadicScale (n 1))
  characterWidth:=Real.logb Z (τ.modulus.absNorm:ℝ)
  base_ge_one:=hZ.le
  row_nonneg:=Real.logb_nonneg hZ hn
  character_nonneg:=Real.logb_nonneg hZ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot))
  scale_eq:=(Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (dyadicScale_pos _)).symm
  modulus_bound:=by
    rw [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (show 0<(τ.modulus.absNorm:ℝ) by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot))]
  puncture_ne_zero:=hR
  puncture_bound:=hRN
  radial_support:=ball_support
  row_ne_zero:=fun _ hz=> hz.1
  nonexceptional:=canonical_mask_nonexceptional τ Q R hR n

lemma canonicalState_width (Z Bmask:ℝ)(hZ:1< Z)(τ:Character)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤ Z^Bmask)(n:Fin 4→ℤ)(hn:1≤ dyadicScale (n 1)):
    (canonicalState Z Bmask hZ τ Q R hR hRN n hn).width=
      Real.logb Z (dyadicScale (n 1))+Real.logb Z (τ.modulus.absNorm:ℝ):=rfl

lemma canonicalState_power (Z Bmask:ℝ)(hZ:1< Z)(τ:Character)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤ Z^Bmask)(n:Fin 4→ℤ)(hn:1≤ dyadicScale (n 1)):
    Z^(canonicalState Z Bmask hZ τ Q R hR hRN n hn).width=
      (τ.modulus.absNorm:ℝ)*dyadicScale (n 1):=by
  rw [canonicalState_width,Real.rpow_add (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (dyadicScale_pos _),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (show 0<(τ.modulus.absNorm:ℝ) by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot))]
  ring

lemma common_puncture_bound (Z Bmask Bsource:ℝ)(hZ:0< Z)(R C:Ideal O)
    (hR:(R.absNorm:ℝ)≤ Z^Bmask)(hC:(C.absNorm:ℝ)≤ Z^Bsource):
    ((R*C).absNorm:ℝ)≤ Z^(Bmask+Bsource):=by
  rw [map_mul,Nat.cast_mul,Real.rpow_add hZ]
  exact mul_le_mul hR hC (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)


end CenteredMomentEnergyChildState

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace CenteredMomentEnergyAllocatedChildren
open HeckeFamily HeckeDyadic 
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentDetectorDictionary CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentSecondHeightFamily CenteredMomentHeckeHeight
open CenteredMomentOriginalRadialComparison CenteredMomentInductionEnergy
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O"=> Eisenstein.O

variable {α:Type*}[Fintype α][DecidableEq α]

lemma natural_product_eq_positive {η:Character}{z:O}(F:NaturalRow η z)
    (W₁ W₂:ℝ→ℂ)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)(hP:∀i,0< P i):
    polynomial F.character false W₁ X₁ 0 0*polynomial F.character false W₂ X₂ 0 0*
      ∏i,naturalSlot F.character (pool i) (β i) (P i)=
      CenteredMomentRetainedEnergy.positiveSlotRow η
        (fixedBadMask*cubicIdealGenerator 1) 1 z
        W₁ W₂ pool β P 0 X₁ X₂:=by
  rw [natural_unit_mask_positive F]
  have hh:=positiveSlotRow_eq_product η F.character fixedBadMask 1 z
    (by simpa only [one_mul] using F.element) W₁ W₂ pool β P X₁ X₂ 0 0 hX₁ hX₂ hP
  rw [twistProfile_zero,twistProfile_zero] at hh
  rw [hh]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hs:=CenteredMomentRayMaskedFloor.natural_slot_eq F (pool i) (β i) (P i) 0
  have he:heightCoefficient (β i) 0=β i:=by
    funext I
    simp only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one]
  rw [he] at hs
  exact hs

lemma natural_radial_eq_energy (η:Character)(r:Radial)(hz:∀z,r.keep z→z≠0)
    (W₁ W₂:ℝ→ℂ)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)(hP:∀i,0< P i):
    radialEnergy (fun z=> polynomial (naturalCharacter η z) false W₁ X₁ 0 0*
      polynomial (naturalCharacter η z) false W₂ X₂ 0 0*
      ∏i,naturalSlot (naturalCharacter η z) (pool i) (β i) (P i))
      r.keep r.profile r.scale=
    CenteredMomentInductionEnergy.energy η
      (fixedBadMask*cubicIdealGenerator 1) 1 0 W₁ W₂ pool β P
      X₁ X₂ r.keep r.profile r.scale:=by
  unfold radialEnergy CenteredMomentInductionEnergy.energy
  apply tsum_congr
  intro z
  by_cases hk:r.keep z
  · simp only [if_pos hk,naturalCharacter_eq η z (hz z hk)]
    rw [natural_product_eq_positive (naturalRow η z (hz z hk)) W₁ W₂ pool β P X₁ X₂ hX₁ hX₂ hP]
  · simp only [if_neg hk]

omit [Fintype α] in
lemma natural_subset_radial_eq_energy (η:Character)(r:Radial)(hz:∀z,r.keep z→z≠0)
    (F:Finset α)(W₁ W₂:ℝ→ℂ)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)(hP:∀i∈F,0< P i):
    radialEnergy (fun z=> polynomial (naturalCharacter η z) false W₁ X₁ 0 0*
      polynomial (naturalCharacter η z) false W₂ X₂ 0 0*
      ∏i∈F,naturalSlot (naturalCharacter η z) (pool i) (β i) (P i))
      r.keep r.profile r.scale=
    CenteredMomentInductionEnergy.energy η
      (fixedBadMask*cubicIdealGenerator 1) 1 0 W₁ W₂
      (fun i:F=> pool i) (fun i:F=>β i) (fun i:F=> P i) X₁ X₂ r.keep r.profile r.scale:=by
  have hh:=natural_radial_eq_energy (α:=F) η r hz W₁ W₂
    (fun i:F=> pool i) (fun i:F=>β i) (fun i:F=> P i) X₁ X₂ hX₁ hX₂
    (fun i=> hP i i.property)
  have hp (z:O):(∏i:F,naturalSlot (naturalCharacter η z) (pool i) (β i) (P i))=
      ∏i∈F,naturalSlot (naturalCharacter η z) (pool i) (β i) (P i):=
    Finset.prod_coe_sort F (fun i:α=> naturalSlot (naturalCharacter η z) (pool i) (β i) (P i))
  simp_rw [hp] at hh
  exact hh

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentRetainedProfile CenteredMomentCommonAllocationSum

def allocatedEnergy (η:Character)(r:Radial)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2))) (V₁ V₂:Plain)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)(D₁ D₂:Finset (Ideal O))(J:Finset α):ℝ:=
  CenteredMomentInductionEnergy.energy (ι := ↥(liveIndices D a\J)) η
    (fixedBadMask*cubicIdealGenerator (1:Ideal O)) 1 0
    (V₁.profile (rawScale D a X₁ 0) (rawScale_pos D a X₁ hX₁ 0) t)
    (V₂.profile (rawScale D a X₂ 1) (rawScale_pos D a X₂ hX₂ 1) t)
    (fun i:↥(liveIndices D a\J)=> pool i) (fun i:↥(liveIndices D a\J)=> heightCoefficient (β i) t)
    (fun i:↥(liveIndices D a\J)=> P i)
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ))
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ))
    r.keep r.profile r.scale

lemma child_radial_eq_energy (η:Character)(r:Radial)(hz:∀z,r.keep z→z≠0)
    (D:Ideal O)(a:Allocation D (Finset.univ:Finset (α⊕Fin 2))) (V₁ V₂:Plain)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)(hP:∀i,0< P i)
    (t X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)(D₁ D₂:Finset (Ideal O))(J:Finset α)
    (hD₁:∀I∈D₁,I≠0)(hD₂:∀I∈D₂,I≠0):
    radialEnergy (fun z=> child (α:=α) (naturalCharacter η z) D a V₁ V₂ pool β P
      t X₁ X₂ hX₁ hX₂ D₁ D₂ J) r.keep r.profile r.scale=
      allocatedEnergy η r D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ D₁ D₂ J:=by
  have hd₁:0<(Ideal.absNorm (∏I∈D₁,I):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.prod_ne_zero_iff.mpr hD₁))
  have hd₂:0<(Ideal.absNorm (∏I∈D₂,I):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.prod_ne_zero_iff.mpr hD₂))
  exact natural_subset_radial_eq_energy η r hz (liveIndices D a\J)
    (V₁.profile (rawScale D a X₁ 0) (rawScale_pos D a X₁ hX₁ 0) t)
    (V₂.profile (rawScale D a X₂ 1) (rawScale_pos D a X₂ hX₂ 1) t)
    pool (fun i=> heightCoefficient (β i) t) P
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ))
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ))
    (div_pos (by unfold clippedScale;positivity) hd₁)
    (div_pos (by unfold clippedScale;positivity) hd₂) (fun i _=> hP i)

def commonAllocatedEnergy (s:Input α)(τ:Character)(v:ℝ)(C R:Ideal O)
    (B:actualAllocations s.pools C)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (V₁ V₂:Plain)(r:Radial)(left:Bool)(D₁ D₂:Finset (Ideal O))
    (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)):ℝ:=
  let d:=commonData (withHeight s τ v) C R B
  if left then allocatedEnergy τ r D a V₁ V₂ d.slots d.coefficient d.P
    v d.X₁ d.X₂ d.X₁_pos d.X₂_pos D₁ D₂ J
  else allocatedEnergy τ r D a V₁ V₂ d.slots d.coefficient d.P
    v d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos D₁ D₂ J

lemma commonChild_energy (s:Input α)(τ:Character)(v:ℝ)(C R:Ideal O)
    (B:actualAllocations s.pools C)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (V₁ V₂:Plain)(r:Radial)(hz:∀z,r.keep z→z≠0)(left:Bool)(D₁ D₂:Finset (Ideal O))
    (J:Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (hD₁:∀I∈D₁,I≠0)(hD₂:∀I∈D₂,I≠0):
    radialEnergy (fun z=> commonChild s τ v C R B D a V₁ V₂ left z D₁ D₂ J)
      r.keep r.profile r.scale=commonAllocatedEnergy s τ v C R B D a V₁ V₂ r left D₁ D₂ J:=by
  let d:=commonData (withHeight s τ v) C R B
  cases left
  · exact child_radial_eq_energy τ r hz D a V₁ V₂ d.slots d.coefficient d.P d.P_pos
      v d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos D₁ D₂ J hD₁ hD₂
  · exact child_radial_eq_energy τ r hz D a V₁ V₂ d.slots d.coefficient d.P d.P_pos
      v d.X₁ d.X₂ d.X₁_pos d.X₂_pos D₁ D₂ J hD₁ hD₂

end CenteredMomentEnergyAllocatedChildren

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace CenteredMomentEnergyAllocatedChildren
open HeckeFamily CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentNaturalRowSource CenteredMomentRadialEligibleEnergy
local notation "O"=> Eisenstein.O
variable {α:Type*}[Fintype α][DecidableEq α]

theorem actual_common_from_energy (b M:α→ℝ)(hM:∀i,0≤ M i)(ε:ℝ)(hε:0<ε):
    ∃C₀:ℝ,0< C₀ ∧ ∀s:Input α,(∀i,s.hi i≤ b i)→(∀i,s.M i≤ M i)→
    ∀(τ:Character)(v:ℝ)(C R:Ideal O),R≠0→∀B:actualAllocations s.pools C,
    ∀(L:Ideal O)(a:Allocation L (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),
    ∀V₁ V₂:Plain,V₁.W=s.W₁→V₂.W=s.W₂→∀r:Radial,(∀z,r.keep z→z≠0)→
    ∀E₁ E₂:ℝ,0≤ E₁→0≤ E₂→
    (∀left:Bool,∀D₁∈(CubicEisenstein.primeSupport (R*C)).powerset,
      ∀D₂∈(CubicEisenstein.primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      commonAllocatedEnergy s τ v C R B L a V₁ V₂ r left D₁ D₂ J≤(if left then E₁ else E₂))→
    childEnergy (commonData (withHeight s τ v) C R B) r L a≤
      C₀*(Ideal.absNorm (R*C).radical:ℝ)^ε*(E₁+E₂):=by
  obtain ⟨C₀,hC₀,hbound⟩:=actual_common_radial_energy b M hM ε hε
  refine ⟨C₀,hC₀,?_⟩
  intro s hhi hMs τ v C R hR B L a V₁ V₂ hV₁ hV₂ r hz E₁ E₂ hE₁ hE₂ he
  apply hbound s hhi hMs τ v C R hR B L a V₁ V₂ hV₁ hV₂ r hz E₁ E₂ hE₁ hE₂
  · intro D₁ hD₁ D₂ hD₂ J hJ
    rw [commonChild_energy s τ v C R B L a V₁ V₂ r hz true D₁ D₂ J
      (fun I hi=>(CenteredMomentNaturalRowSource.support_prime (R*C) I ((Finset.mem_powerset.mp hD₁) hi)).ne_zero)
      (fun I hi=>(CenteredMomentNaturalRowSource.support_prime (R*C) I ((Finset.mem_powerset.mp hD₂) hi)).ne_zero)]
    exact he true D₁ hD₁ D₂ hD₂ J hJ
  · intro D₁ hD₁ D₂ hD₂ J hJ
    rw [commonChild_energy s τ v C R B L a V₁ V₂ r hz false D₁ D₂ J
      (fun I hi=>(CenteredMomentNaturalRowSource.support_prime (R*C) I ((Finset.mem_powerset.mp hD₁) hi)).ne_zero)
      (fun I hi=>(CenteredMomentNaturalRowSource.support_prime (R*C) I ((Finset.mem_powerset.mp hD₂) hi)).ne_zero)]
    exact he false D₁ hD₁ D₂ hD₂ J hJ

end CenteredMomentEnergyAllocatedChildren

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace CenteredMomentEnergyAllocatedProfiles
open CenteredMomentFiniteProfileExceptional

def retainedPair (a b:ℝ)(ha:0< a)(p:Profiles a b)
    (U:Fin 2→ℝ)(hU:∀i,0< U i)(t:ℝ):Profiles (a/max 1 b) b where
  profile:=fun i=>(sourcePlain a b ha (p.profile i) (p.support i)).profile (U i) (hU i) t
  support:=fun i=> sourcePlain_support a b ha (p.profile i) (p.support i) (U i) (hU i) t

theorem retained_pair_control (a b:ℝ)(ha:0< a)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀p:Profiles a b,∀U:Fin 2→ℝ,∀hU:∀i,0< U i,∀t:ℝ,
      (retainedPair a b ha p U hU t).control S≤
        C*p.control T*(1+‖t‖)^(2*n):=by
  obtain ⟨n,T,C,hC,hbound⟩:=plain_profile_source_control a b ha S
  refine ⟨n,T,C ^ 2,sq_pos_of_pos hC,?_⟩
  intro p U hU t
  have h₀:=hbound (p.profile 0) (p.support 0) (U 0) (hU 0) t
  have h₁:=hbound (p.profile 1) (p.support 1) (U 1) (hU 1) t
  have hp₀:=sourceControl_nonneg T (p.profile 0)
  change sourceControl S _*sourceControl S _≤ _
  apply (mul_le_mul h₀ h₁ (sourceControl_nonneg _ _) (by positivity)).trans_eq
  simp only [Profiles.control,show 2*n=n+n by omega,pow_add]
  ring

end CenteredMomentEnergyAllocatedProfiles

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace CenteredMomentEnergyAllocatedZero
open HeckeFamily CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedProfiles
open CenteredMomentAllocatedNaturalSource CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentRetainedProfile CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentRadialEligibleEnergy (Radial)
open InversePrincipalEnergy
local notation "O"=> Eisenstein.O

variable {α:Type*}[Fintype α][DecidableEq α]

lemma allocatedScale_le (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))(X:ℝ)(hX:0< X)
    (j:Fin 2)(F:Finset (Ideal O))(hF:∀I∈F,I≠0):
    clippedScale (rawScale D a X j)/(Ideal.absNorm (∏I∈F,I):ℝ)≤ max 1 X:=by
  have hn:1≤(Ideal.absNorm (CenteredMomentDivisorRectangle.selectedPlain D a j):ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (CenteredMomentDivisorExtraction.selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  have hf:1≤(Ideal.absNorm (∏I∈F,I):ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr hF))
  have hx:rawScale D a X j≤ X:=div_le_self hX.le hn
  exact (div_le_self (by unfold clippedScale;positivity) hf).trans
    (max_le_max_left 1 hx)

lemma allocated_empty (η:Character)(r:Radial)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))(V₁ V₂:Plain)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)(D₁ D₂:Finset (Ideal O)):
    allocatedEnergy η r D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ D₁ D₂ (liveIndices D a)=
      CenteredMomentCoreFloor.zeroEnergy η
        (CenteredMomentSecondHeightFamily.fixedBadMask*cubicIdealGenerator 1) 1 0
        (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t)
        (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t)
        (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ))
        (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ)) r:=by
  let : IsEmpty ↥(liveIndices D a\liveIndices D a):=⟨fun i=> by
    have hi:=Finset.mem_sdiff.mp i.property
    exact hi.2 hi.1⟩
  simp only [allocatedEnergy,energy,CenteredMomentCoreFloor.zeroEnergy,
    CenteredMomentCoreFloor.zeroRow,positiveSlotRow,Fintype.prod_empty,mul_one]

theorem empty_from_zeroAt (lo hi Z Bmask bΦ L Mcap ε:ℝ)(hlo:0< lo)(hL:0≤ L)
    (Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hz:ZeroAt Q (lo/max 1 hi) hi bΦ Bmask L Mcap ε Z degree S C)
    (s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=Q)(hwidth:s.width≤ Mcap)
    (hunit:s.puncture=1)(p:Profiles lo hi)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)(D₁ D₂:Finset (Ideal O))
    (hD₁:∀I∈D₁,I≠0)(hD₂:∀I∈D₂,I≠0)
    (hc₁:X₁≤ Z^L)(hc₂:X₂≤ Z^L):
    let V₁:=sourcePlain lo hi hlo (p.profile 0) (p.support 0)
    let V₂:=sourcePlain lo hi hlo (p.profile 1) (p.support 1)
    let U:Fin 2→ℝ:=![rawScale D a X₁ 0,rawScale D a X₂ 1]
    let hU:∀i,0< U i:=by intro i;fin_cases i;exact rawScale_pos D a X₁ hX₁ 0;exact rawScale_pos D a X₂ hX₂ 1
    allocatedEnergy s.character s.radial D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ D₁ D₂ (liveIndices D a)≤
      C*diagonalControl s.radial.profile*((retainedPair lo hi hlo p U hU t).control S)^2*
        Z^(s.width+ε):=by
  dsimp only
  rw [allocated_empty]
  have hd₁:0<(Ideal.absNorm (∏I∈D₁,I):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.prod_ne_zero_iff.mpr hD₁))
  have hd₂:0<(Ideal.absNorm (∏I∈D₂,I):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.prod_ne_zero_iff.mpr hD₂))
  let U:Fin 2→ℝ:=![rawScale D a X₁ 0,rawScale D a X₂ 1]
  have hU:∀i,0< U i:=by
    intro i;fin_cases i
    · exact rawScale_pos D a X₁ hX₁ 0
    · exact rawScale_pos D a X₂ hX₂ 1
  have hh:=hz s hQ hwidth (retainedPair lo hi hlo p U hU t) 0
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ))
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ))
    (div_pos (by unfold clippedScale;positivity) hd₁)
    (div_pos (by unfold clippedScale;positivity) hd₂)
    ((allocatedScale_le D a X₁ hX₁ 0 D₁ hD₁).trans
      (max_le (Real.one_le_rpow s.base_ge_one hL) hc₁))
    ((allocatedScale_le D a X₂ hX₂ 1 D₂ hD₂).trans
      (max_le (Real.one_le_rpow s.base_ge_one hL) hc₂))
  rw [NaturalState.plainEnergy_eq_zero] at hh
  simpa only [NaturalState.mask,hunit,retainedPair,U,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.head_cons,norm_zero,zero_add,abs_zero,add_zero,one_pow,mul_one] using hh

end CenteredMomentEnergyAllocatedZero

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentEnergyDeletedChildCapacity
open HeckeFamily CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedChildCapacity
open CenteredMomentRetainedProfile CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentDivisorRaw CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity
open CenteredMomentFirstSecondCapacityLedger CenteredMomentLiveCapacity
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma deletion_norm (F : Finset (Ideal O)) (hF : ∀I∈F,I≠0) :
    (1:ℝ) ≤ (∏I∈F,I).absNorm := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Finset.prod_ne_zero_iff.mpr hF))

lemma prime_deletion_norm (F : Finset (Ideal O)) (hF : ∀I∈F,Prime I) :
    (1:ℝ) ≤ (∏I∈F,I).absNorm :=
  deletion_norm F (fun I hI=>(hF I hI).ne_zero)

def postmaskLength (Z U : ℝ) (F : Finset (Ideal O)) : ℝ :=
  length Z (clippedScale U/((∏I∈F,I).absNorm:ℝ))

lemma postmaskLength_eq (Z U : ℝ) (F : Finset (Ideal O))
    (hZ : 1< Z) (hF : ∀I∈F,I≠0) :
    postmaskLength Z U F=Real.logb Z (clippedScale U)-
      min (Real.logb Z ((∏I∈F,I).absNorm:ℝ)) (Real.logb Z (clippedScale U)) :=
  postmask_length Z U _ hZ (deletion_norm F hF)

lemma postmaskLength_le (Z U : ℝ) (F : Finset (Ideal O))
    (hZ : 1< Z) (hF : ∀I∈F,I≠0) :
    postmaskLength Z U F≤ Real.logb Z (clippedScale U) :=
  postmask_length_le Z U _ hZ (deletion_norm F hF)

lemma postmaskLength_nonneg (Z U : ℝ) (F : Finset (Ideal O)) (hZ : 1< Z) :
    0≤ postmaskLength Z U F := length_nonneg Z _ hZ

theorem child_survives (χ : Character) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (t X₁ X₂ : ℝ) (h₁ : 0< X₁) (h₂ : 0< X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hne : child χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J≠0) :
    1≤ rawScale D a X₁ 0*V₁.b ∧ 1≤ rawScale D a X₂ 1*V₂.b := by
  unfold child at hne
  have hp:=left_ne_zero_of_mul hne
  exact ⟨profile_polynomial_survives χ V₁ _ (rawScale_pos D a X₁ h₁ 0) t _ 0 0
    (left_ne_zero_of_mul hp),
    profile_polynomial_survives χ V₂ _ (rawScale_pos D a X₂ h₂ 1) t _ 0 0
      (right_ne_zero_of_mul hp)⟩

def deletedExcess (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ κ M : ℝ) (P : ι→ℝ) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι) : ℝ :=
  excess (liveIndices D a\J) (fun i=> Real.logb Z (P i))
    (postmaskLength Z (rawScale D a X₁ 0) F₁)
    (postmaskLength Z (rawScale D a X₂ 1) F₂) M κ

lemma deletedExcess_le (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ κ M : ℝ) (P : ι→ℝ) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1< Z) (hκ : 0≤κ) (hP : ∀i,1≤ P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0) :
    deletedExcess D a Z X₁ X₂ κ M P F₁ F₂ J≤
      max (plainLogs D a Z X₁ X₂+6*κ*remainingLogs D a Z P-M) 0 := by
  have h₁:=postmaskLength_le Z (rawScale D a X₁ 0) F₁ hZ hF₁
  have h₂:=postmaskLength_le Z (rawScale D a X₂ 1) F₂ hZ hF₂
  have hsum:(∑i∈liveIndices D a\J,Real.logb Z (P i))≤ remainingLogs D a Z P :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun i _ _=> Real.logb_nonneg hZ (hP i))
  have hh:=mul_le_mul_of_nonneg_left hsum (by positivity : 0≤6*κ)
  unfold deletedExcess excess plainLogs
  exact max_le_max (by linarith) le_rfl

theorem child_excess_from_parent (χ : Character) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (t Z X₁ X₂ κ A M Mnom Mactual w ell δ θ : ℝ)
    (h₁ : 0< X₁) (h₂ : 0< X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1< Z) (hκ : 0≤κ) (hP : ∀i,1≤ P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0)
    (hne : child χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J≠0)
    (hparent : A+(6*κ-1)*(∑i,Real.logb Z (P i))≤ M)
    (hshift : Real.logb Z (X₁*X₂*∏i,P i)-Mnom≤ A-M+6*(w+ell)+δ)
    (hclip : Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ) :
    deletedExcess D a Z X₁ X₂ κ Mactual P F₁ F₂ J≤
      max (6*(w+ell)+δ+2*θ+Mnom-Mactual) 0 := by
  obtain ⟨hs₁,hs₂⟩:=child_survives χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J hne
  apply (deletedExcess_le D a Z X₁ X₂ κ Mactual P F₁ F₂ J hZ hκ hP hF₁ hF₂).trans
  apply (excess_le_remaining D a Z X₁ X₂ V₁.b V₂.b κ Mactual hZ h₁ h₂ P
    (fun i=> zero_lt_one.trans_le (hP i)) hs₁ hs₂).trans
  apply max_le_max _ le_rfl
  have hr:=affine_reduction_le_parent D a Z κ hZ hκ P hP
  linarith

theorem child_paid_width (χ : Character) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (t Z X₁ X₂ κ A M Mnom Mactual w ell δ₁ δ₂ θ : ℝ)
    (h₁ : 0< X₁) (h₂ : 0< X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1< Z) (hκ : 0≤κ) (hP : ∀i,1≤ P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0)
    (hne : child χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J≠0)
    (hparent : A+(6*κ-1)*(∑i,Real.logb Z (P i))≤ M)
    (hshift : Real.logb Z (X₁*X₂*∏i,P i)-Mnom≤ A-M+6*(w+ell)+δ₁)
    (hwidth : Mactual-Mnom≤δ₂) (hw : 0≤ w) (hell : 0≤ ell)
    (hδ₁ : 0≤δ₁) (hδ₂ : 0≤δ₂) (hθ : 0≤θ)
    (hclip : Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ) :
    Mactual+deletedExcess D a Z X₁ X₂ κ Mactual P F₁ F₂ J/6≤
      Mnom+δ₂+w+ell+δ₁/6+θ/3 := by
  have he:=child_excess_from_parent χ D a V₁ V₂ pool β P t Z X₁ X₂ κ A M Mnom Mactual
    w ell δ₁ θ h₁ h₂ F₁ F₂ J hZ hκ hP hF₁ hF₂ hne hparent hshift hclip
  have hh:=width_defect_cost (Mactual-Mnom) (6*(w+ell)+δ₁+2*θ) δ₂
    (by positivity) hδ₂ hwidth
  rw [show 6*(w+ell)+δ₁+2*θ-(Mactual-Mnom)=6*(w+ell)+δ₁+2*θ+Mnom-Mactual by ring] at hh
  linarith

lemma eventually_endpoint_cost (b₁ b₂ θ : ℝ) (hθ : 0<θ) :
    ∀ᶠ Z : ℝ in Filter.atTop,1< Z ∧ Real.logb Z (max 1 b₁*max 1 b₂)≤2*θ :=
  CenteredMomentCommonMaskChildCapacity.eventually_fixed_clipping_cost b₁ b₂ (2*θ) (by positivity)

theorem paired_child_excess (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (Z X₁ X₂ Y₁ Y₂ κ A M Mnom Mactual w ell δ θ : ℝ)
    (hX₁ : 0< X₁) (hX₂ : 0< X₂) (hY₁ : 0< Y₁) (hY₂ : 0< Y₂)
    (hsame : Y₁*Y₂=X₁*X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1< Z) (hκ : 0≤κ) (hP : ∀i,1≤ P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0)
    (hparent : A+(6*κ-1)*(∑i,Real.logb Z (P i))≤ M)
    (hshift : Real.logb Z (X₁*X₂*∏i,P i)-Mnom≤ A-M+6*(w+ell)+δ)
    (hclip : Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ) :
    (∀χ t,child χ D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ F₁ F₂ J≠0 →
      deletedExcess D a Z X₁ X₂ κ Mactual P F₁ F₂ J≤
        max (6*(w+ell)+δ+2*θ+Mnom-Mactual) 0) ∧
    (∀χ t,child χ D a V₁ V₂ pool β P t Y₁ Y₂ hY₁ hY₂ F₁ F₂ J≠0 →
      deletedExcess D a Z Y₁ Y₂ κ Mactual P F₁ F₂ J≤
        max (6*(w+ell)+δ+2*θ+Mnom-Mactual) 0) := by
  constructor
  · intro χ t hn
    exact child_excess_from_parent χ D a V₁ V₂ pool β P t Z X₁ X₂ κ A M Mnom Mactual
      w ell δ θ hX₁ hX₂ F₁ F₂ J hZ hκ hP hF₁ hF₂ hn hparent hshift hclip
  · intro χ t hn
    apply child_excess_from_parent χ D a V₁ V₂ pool β P t Z Y₁ Y₂ κ A M Mnom Mactual
      w ell δ θ hY₁ hY₂ F₁ F₂ J hZ hκ hP hF₁ hF₂ hn hparent _ hclip
    simpa only [hsame] using hshift

theorem source_removal_width_cost (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (Z X₁ X₂ κ A M Mnom Mactual w ell δ₁ δ₂ θ mesh : ℝ)
    (h₁ : 0< X₁) (h₂ : 0< X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1< Z) (hκ : 0≤κ) (hP : ∀i,1≤ P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0)
    (hparent : A+(6*κ-1)*(∑i,Real.logb Z (P i))≤ M)
    (hshift : Real.logb Z (X₁*X₂*∏i,P i)-Mnom≤ A-M+6*(w+ell)+δ₁)
    (hwidth : Mactual-Mnom≤δ₂) (hw : 0≤ w) (hell : 0≤ ell)
    (hδ₁ : 0≤δ₁) (hδ₂ : 0≤δ₂) (hθ : 0≤θ)
    (hclip : Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ)
    (hm : 0≤ mesh) (hmesh : ∀i∈liveIndices D a\J,Real.logb Z (P i)≤ mesh) :
    ∃removed : Finset ι,removed⊆liveIndices D a\J ∧
      (removed=liveIndices D a\J ∨
        postmaskLength Z (rawScale D a X₁ 0) F₁+
        postmaskLength Z (rawScale D a X₂ 1) F₂+
        6*κ*(∑i∈(liveIndices D a\J)\removed,Real.logb Z (P i))≤ Mactual) ∧
      ∀χ t,child χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J≠0 →
        Mactual-Mnom+κ*(∑i∈removed,Real.logb Z (P i))≤
          δ₂+w+ell+δ₁/6+θ/3+κ*mesh := by
  by_cases hk : κ=0
  · refine ⟨liveIndices D a\J,Finset.Subset.refl _,Or.inl rfl,?_⟩
    intro χ t _
    simp only [hk,zero_mul,add_zero]
    linarith
  have hkpos : 0<κ := lt_of_le_of_ne hκ (Ne.symm hk)
  obtain ⟨removed,hr,hcap,hcost⟩:=removal_excess_cost (liveIndices D a\J)
    (fun i=> Real.logb Z (P i))
    (postmaskLength Z (rawScale D a X₁ 0) F₁)
    (postmaskLength Z (rawScale D a X₂ 1) F₂) Mactual κ mesh hkpos hm
    (fun i _=> Real.logb_nonneg hZ (hP i)) hmesh
  refine ⟨removed,hr,hcap,?_⟩
  intro χ t hn
  have hp:=child_paid_width χ D a V₁ V₂ pool β P t Z X₁ X₂ κ A M Mnom Mactual
    w ell δ₁ δ₂ θ h₁ h₂ F₁ F₂ J hZ hκ hP hF₁ hF₂ hn hparent hshift
    hwidth hw hell hδ₁ hδ₂ hθ hclip
  change κ*(∑i∈removed,Real.logb Z (P i))≤
    deletedExcess D a Z X₁ X₂ κ Mactual P F₁ F₂ J/6+κ*mesh at hcost
  linarith

lemma postmask_scale_pos (U : ℝ) (F : Finset (Ideal O)) (hF : ∀I∈F,I≠0) :
    0< clippedScale U/((∏I∈F,I).absNorm:ℝ) :=
  div_pos (zero_lt_one.trans_le (clippedScale_ge_one U))
    (zero_lt_one.trans_le (deletion_norm F hF))

theorem input_parent_child_excess (s : CenteredMomentCommonRadialData.Input ι)
    (χ : Character) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) (V₁ V₂ : Plain)
    (t Z X₁ X₂ κ M Mnom Mactual w ell δ θ : ℝ)
    (h₁ : 0< X₁) (h₂ : 0< X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1< Z) (hκ : 0≤κ) (hP : ∀i,1≤ s.P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0)
    (hne : child χ D a V₁ V₂ s.slots s.coefficient s.P t X₁ X₂ h₁ h₂ F₁ F₂ J≠0)
    (hparent : length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤ M)
    (hshift : Real.logb Z (X₁*X₂*∏i,s.P i)-Mnom≤
      Real.logb Z (CenteredMomentAmplificationChildInput.volume s)-M+6*(w+ell)+δ)
    (hclip : Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ) :
    deletedExcess D a Z X₁ X₂ κ Mactual s.P F₁ F₂ J≤
      max (6*(w+ell)+δ+2*θ+Mnom-Mactual) 0 :=
  child_excess_from_parent χ D a V₁ V₂ s.slots s.coefficient s.P t Z X₁ X₂ κ
    (Real.logb Z (CenteredMomentAmplificationChildInput.volume s)) M Mnom Mactual w ell δ θ
    h₁ h₂ F₁ F₂ J hZ hκ hP hF₁ hF₂ hne
    (input_affine_capacity s Z κ M hZ hparent) hshift hclip

end CenteredMomentEnergyDeletedChildCapacity

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentEnergyChildEnvelopeFitting
open HeckeFamily CenteredMomentFiniteProfileExceptional
open CenteredMomentInductionEnergy InversePrincipalEnergy
open CenteredMomentSecondNonexceptionalChosenBlock
local notation "O" => Eisenstein.O

lemma radical_product_power (R C:Ideal O)(hR:R≠0)(hC:C≠0)
    (Z BR BC ε:ℝ)(hZ:0< Z)(hε:0≤ε)
    (hRN:(R.absNorm:ℝ)≤ Z^BR)(hCN:(C.absNorm:ℝ)≤ Z^BC):
    ((R*C).radical.absNorm:ℝ)^ε≤ Z^((BR+BC)*ε):=by
  have hRC:R*C≠0:=mul_ne_zero hR hC
  have hr:((R*C).radical.absNorm:ℝ)≤(R*C).absNorm:=by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hRC))
      (map_dvd Ideal.absNorm (Ideal.dvd_iff_le.mpr (Ideal.le_radical (I:=R*C))))
  have hh:(R*C).absNorm≤ Z^(BR+BC):=by
    rw [map_mul,Nat.cast_mul,Real.rpow_add hZ]
    exact mul_le_mul hRN hCN (Nat.cast_nonneg _) (Real.rpow_pos_of_pos hZ _).le
  rw [Real.rpow_mul hZ.le]
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (hr.trans hh) hε

lemma independent_height (v height:ℝ)(hheight:0≤ height)(degree:ℕ):
    (1+(|v|+height))^degree≤(1+height)^degree*(1+‖v‖)^(2*degree):=by
  have hh:1+(|v|+height)≤(1+height)*(1+‖v‖):=by
    rw [Real.norm_eq_abs]
    nlinarith [mul_nonneg hheight (abs_nonneg v)]
  have hp:=pow_le_pow_left₀ (by positivity:0≤1+(|v|+height)) hh degree
  rw [mul_pow] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by linarith [norm_nonneg v]:1≤1+‖v‖) (by omega:degree≤2*degree)) (by positivity))

def coefficient {a b:ℝ}(Cc C₀ C₁:ℝ)(p:Profiles a b)(T:Finset (ℕ×ℕ))
    (height:ℝ)(degree:ℕ)(Z exponent:ℝ):ℝ:=
  Cc*(C₀+C₁)*diagonalControl CenteredMomentFirstAmplificationChoice.ballProfile*
    (p.control T)^2*(1+height)^degree*Z^exponent

lemma coefficient_nonneg {a b:ℝ}(Cc C₀ C₁:ℝ)(p:Profiles a b)(T:Finset (ℕ×ℕ))
    (height:ℝ)(degree:ℕ)(Z exponent:ℝ)(hC:0≤ Cc)(h₀:0≤ C₀)(h₁:0≤ C₁)
    (hH:0≤ height)(hZ:0≤ Z):0≤ coefficient Cc C₀ C₁ p T height degree Z exponent:=by
  unfold coefficient
  have hd:=diagonalControl_nonneg CenteredMomentFirstAmplificationChoice.ballProfile
  positivity

theorem paid_rhs_fit {a b:ℝ}(Cc C₀ C₁:ℝ)(p:Profiles a b)(T:Finset (ℕ×ℕ))
    (R C:Ideal O)(hR:R≠0)(hC:C≠0)(τ:Character)(Q:Ideal O)(dyad:Fin 4→ℤ)
    (v height:ℝ)(degree:ℕ)(Z BR BC εmask exponent loss reference ratio:ℝ)
    (hCc:0≤ Cc)(h₀:0≤ C₀)(h₁:0≤ C₁)(hH:0≤ height)(hZ:1≤ Z)(hε:0≤εmask)
    (hRN:(R.absNorm:ℝ)≤ Z^BR)(hCN:(C.absNorm:ℝ)≤ Z^BC)
    (hloss:exponent≤ loss)(href:0≤ reference)(hratio:0≤ ratio):
    Cc*((R*C).radical.absNorm:ℝ)^εmask*(C₀+C₁)*
      diagonalControl (canonicalRadial τ Q dyad).profile*(p.control T)^2*
      (1+(|v|+height))^degree*reference*ratio^((1:ℝ)/6)*Z^exponent≤
    coefficient Cc C₀ C₁ p T height degree Z ((BR+BC)*εmask+loss)*
      reference*ratio^((1:ℝ)/6)*(1+‖v‖)^(2*degree):=by
  have hZ0:0< Z:=zero_lt_one.trans_le hZ
  have hr:=radical_product_power R C hR hC Z BR BC εmask hZ0 hε hRN hCN
  have ht:=independent_height v height hH degree
  have hp:=Real.rpow_le_rpow_of_exponent_le hZ hloss
  have hd:=diagonalControl_nonneg CenteredMomentFirstAmplificationChoice.ballProfile
  have hsum:0≤ C₀+C₁:=add_nonneg h₀ h₁
  change Cc*((R*C).radical.absNorm:ℝ)^εmask*(C₀+C₁)*
    diagonalControl CenteredMomentFirstAmplificationChoice.ballProfile*(p.control T)^2*
    (1+(|v|+height))^degree*reference*ratio^((1:ℝ)/6)*Z^exponent≤ _
  calc
    _≤ Cc*Z^((BR+BC)*εmask)*(C₀+C₁)*
      diagonalControl CenteredMomentFirstAmplificationChoice.ballProfile*(p.control T)^2*
      ((1+height)^degree*(1+‖v‖)^(2*degree))*reference*ratio^((1:ℝ)/6)*Z^loss:=by
        gcongr
    _=_:=by
      unfold coefficient
      rw [Real.rpow_add hZ0]
      ring

end CenteredMomentEnergyChildEnvelopeFitting

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

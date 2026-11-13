/-
First sector tails adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.FixedPresentationCosts

/-!
# First sector tails

Retained and discarded energies of the first sector localization, reciprocal radial cutoffs,
arbitrary tail savings of the second input and local discarded pair bounds.
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
namespace CenteredMomentOriginalRadialTail
open HeckeFamily  CenteredMomentAbsoluteEnergy
open CenteredMomentPositiveSummability CenteredMomentOriginalRadialComparison
open SchwartzPlanePoisson
local notation "O" => Eisenstein.O

def tailControl (A : ℕ) (Φ : 𝓢(ℝ,ℂ)) : ℝ :=
  (2:ℝ)^(A+2)*(Finset.Iic (A+2,0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ

lemma cauchy_all (K : ℝ) (hK : 0< K) :
    (∑'z:O,((1+K⁻¹*‖ringComplex z‖^2)^2)⁻¹)≤4*(1+Real.pi)^2*max 1 K := by
  by_cases hk : 1≤ K
  · have hh:=scaled_eisenstein_cauchy_small K⁻¹ (inv_pos.mpr hK) (inv_le_one_of_one_le₀ hk)
    rw [max_eq_right hk]
    have he : K*(K⁻¹*(∑'z:O,((1+K⁻¹*‖ringComplex z‖^2)^2)⁻¹))=
        ∑'z:O,((1+K⁻¹*‖ringComplex z‖^2)^2)⁻¹ := by rw [←mul_assoc,mul_inv_cancel₀ hK.ne',one_mul]
    have hb:=mul_le_mul_of_nonneg_left hh hK.le
    rw [he] at hb
    simpa only [mul_comm K] using hb
  · have hk' : K≤1:=(not_le.mp hk).le
    have hi : 1≤ K⁻¹:=(one_le_inv₀ hK).mpr hk'
    have hs:=scaled_eisenstein_cauchy_summable K⁻¹ (inv_pos.mpr hK)
    have hh:=hs.tsum_le_tsum (g:=fun z:O=>((1+1*‖ringComplex z‖^2)^2)⁻¹) (fun z=> by
      apply inv_anti₀ (by positivity)
      gcongr)
      (scaled_eisenstein_cauchy_summable 1 (by norm_num))
    have hb:=scaled_eisenstein_cauchy_small 1 (by norm_num) (by norm_num)
    rw [max_eq_left hk',mul_one]
    exact hh.trans (by simpa only [one_mul] using hb)

lemma tail_pointwise (A : ℕ) (Φ : 𝓢(ℝ,ℂ)) (x r : ℝ) (hr : 0≤ r) (hx : r≤ x) :
    ‖Φ x‖≤ tailControl A Φ*((1+r)^A)⁻¹*((1+x)^2)⁻¹ := by
  have hxp : 0≤ x:=hr.trans hx
  have hh:=SchwartzMap.one_add_le_sup_seminorm_apply (𝕜:=ℝ)
    (m:=(A+2,0)) (k:=A+2) (n:=0) le_rfl le_rfl Φ x
  simp only [norm_iteratedFDeriv_zero,Real.norm_of_nonneg hxp] at hh
  change (1+x)^(A+2)*‖Φ x‖≤ tailControl A Φ at hh
  have hp : (1+r)^A≤(1+x)^A:=pow_le_pow_left₀ (by positivity) (by linarith) A
  have hb : (1+r)^A*((1+x)^2*‖Φ x‖)≤ tailControl A Φ := by
    apply (mul_le_mul_of_nonneg_right hp (by positivity)).trans
    simpa only [pow_add,mul_assoc] using hh
  have hd : 0<(1+r)^A*(1+x)^2:=by positivity
  rw [show tailControl A Φ*((1+r)^A)⁻¹*((1+x)^2)⁻¹=
    tailControl A Φ/((1+r)^A*(1+x)^2) by field_simp]
  exact (le_div_iff₀ hd).mpr (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hb)

/-- Polynomial radial decay turns a uniform row bound into a summable tail estimate. -/
theorem actual_radial_tail (A : ℕ) (F : O→ℂ) (B : ℝ) (hF : ∀z,‖F z‖≤ B)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0< K) (hR : 0≤ R) :
    radialEnergy F (fun z=> keep z ∧ R<‖ringComplex z‖^2) Φ K≤
      4*(1+Real.pi)^2*tailControl A Φ*B^2*max 1 K*((1+R/K)^A)⁻¹ := by
  let C:=tailControl A Φ*B^2*((1+R/K)^A)⁻¹
  have hC : 0≤ C:=by dsimp [C,tailControl];positivity
  have hs:=bounded_radial_summable F B hF (fun z=> keep z ∧ R<‖ringComplex z‖^2) Φ K hK
  have hp (z:O) :
      (if keep z ∧ R<‖ringComplex z‖^2 then ‖F z‖^2*(Φ (‖ringComplex z‖^2/K)).re else 0)
      ≤ C*((1+K⁻¹*‖ringComplex z‖^2)^2)⁻¹ := by
    split_ifs with hz
    · have ht:=tail_pointwise A Φ (‖ringComplex z‖^2/K) (R/K)
        (div_nonneg hR hK.le) (div_le_div_of_nonneg_right hz.2.le hK.le)
      have hf:=pow_le_pow_left₀ (norm_nonneg _) (hF z) 2
      have hh:=(mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (sq_nonneg _)).trans
        (mul_le_mul hf ht (norm_nonneg _) (sq_nonneg B))
      convert hh using 1 <;> first | rfl | (dsimp only [C]; simp only [div_eq_mul_inv]; ring)
    · exact mul_nonneg hC (by positivity)
  have hb:=Summable.tsum_le_tsum hp (hs.congr (fun z=> by by_cases hz:keep z ∧ R<‖ringComplex z‖^2 <;> simp [hz])) ((scaled_eisenstein_cauchy_summable K⁻¹ (inv_pos.mpr hK)).mul_left C)
  rw [tsum_mul_left] at hb
  have hh:=mul_le_mul_of_nonneg_left (cauchy_all K hK) hC
  have hh' : C*(∑'z:O,((1+K⁻¹*‖ringComplex z‖^2)^2)⁻¹)≤
      4*(1+Real.pi)^2*tailControl A Φ*B^2*max 1 K*((1+R/K)^A)⁻¹ := by
    convert hh using 1 <;> first | rfl | (dsimp only [C]; ring)
  refine le_trans (le_of_eq ?_) (hb.trans hh')
  unfold radialEnergy
  apply tsum_congr
  intro z
  by_cases hz : keep z ∧ R < ‖ringComplex z‖ ^ 2 <;> simp only [hz, if_pos, if_neg]

lemma actual_radial_split (F : O→ℂ) (B : ℝ) (hF : ∀z,‖F z‖≤ B)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0< K) :
    radialEnergy F keep Φ K=
      radialEnergy F (fun z=> keep z ∧ ‖ringComplex z‖^2≤ R) Φ K+
      radialEnergy F (fun z=> keep z ∧ R<‖ringComplex z‖^2) Φ K := by
  unfold radialEnergy
  rw [←Summable.tsum_add (bounded_radial_summable F B hF _ Φ K hK)
    (bounded_radial_summable F B hF _ Φ K hK)]
  apply tsum_congr
  intro z
  by_cases hk:keep z
  · by_cases hr:‖ringComplex z‖^2≤ R
    · simp [hk,hr,not_lt.mpr hr]
    · simp [hk,hr,not_le.mp hr]
  · simp [hk]

theorem actual_positive_row_tail {ι:Type*} [Fintype ι] [DecidableEq ι]
    (order:ℕ) (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (b₁ b₂ B₁ B₂ X₁ X₂:ℝ) (hb₁:0≤ b₁) (hb₂:0≤ b₂) (hB₁:0≤ B₁) (hB₂:0≤ B₂)
    (hX₁:0< X₁) (hX₂:0< X₂) (hs₁:Function.support W₁⊆Set.Iic b₁)
    (hs₂:Function.support W₂⊆Set.Iic b₂) (hW₁:∀x,‖W₁ x‖≤ B₁) (hW₂:∀x,‖W₂ x‖≤ B₂)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b B:ι→ℝ)
    (hP:∀i,0< P i) (hb:∀i,0≤ b i) (hB:∀i,0≤ B i)
    (hβ:∀i,∀I∈S i,‖β i I‖≤ B i)
    (hN:∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤ b i*P i)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K R:ℝ) (hK:0< K) (hR:0≤ R) :
    radialEnergy (fun z=> CenteredMomentRetainedEnergy.positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂)
      (fun z=> keep z ∧ R<‖ringComplex z‖^2) Φ K≤
      4*(1+Real.pi)^2*tailControl order Φ*
        (((128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i))^2*(X₁*X₂*∏i,P i))*
        max 1 K*((1+R/K)^order)⁻¹ := by
  let E:=((128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i))^2*(X₁*X₂*∏i,P i)
  have hE:0≤ E:=mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hX₁.le hX₂.le)
    (Finset.prod_nonneg (fun i _=>(hP i).le)))
  have hp (z:O):‖CenteredMomentRetainedEnergy.positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2≤ E:=
    CenteredMomentInductionEnergy.positive_squared_absolute η m A z t W₁ W₂
      b₁ b₂ B₁ B₂ X₁ X₂ hb₁ hb₂ hB₁ hB₂ hX₁ hX₂ hs₁ hs₂ hW₁ hW₂
      S β P b B hP hb hB hβ hN
  have hh:=actual_radial_tail order _ (Real.sqrt E)
    (fun z=> Real.le_sqrt_of_sq_le (hp z)) keep Φ K R hK hR
  simpa only [Real.sq_sqrt hE] using hh

end CenteredMomentOriginalRadialTail

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace CenteredMomentNaturalRadialCutoff
open HeckeFamily  CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialTail CenteredMomentOriginalRadialComparison
local notation "O" => Eisenstein.O

lemma retained_conductor (η:Character) (Z m q xi Ck K:ℝ) (hZ:0< Z) (hCk:0≤ Ck)
    (hη:(η.modulus.absNorm:ℝ)≤ Z^m) (hK:K≤ Ck*Z^q)
    (z:O) (hz:z≠0) (hrow:‖ringComplex z‖^2≤ K*Z^xi) :
    ((naturalRow η z hz).character.modulus.absNorm:ℝ)≤
      (fixedConductorFactor:ℝ)*Ck*Z^(m+q+xi) := by
  have hn:((Ideal.span {z}).absNorm:ℝ)≤ Ck*Z^(q+xi) := by
    rw [←ringComplex_norm_sq_eq_absNorm_span]
    apply hrow.trans
    have hh:=mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hZ.le xi)
    simpa only [Real.rpow_add hZ,mul_assoc] using hh
  have hh:=(naturalRow η z hz).modulus_power_bound Z m (q+xi) Ck hZ hCk hη hn
  simpa only [add_assoc] using hh

lemma reciprocal_cutoff_bound (Z xi:ℝ) (order:ℕ) (hZ:0< Z) :
    ((1+Z^xi)^order)⁻¹≤ Z^(-xi*(order:ℝ)) := by
  have hp : (Z^xi)^order≤(1+Z^xi)^order:=
    pow_le_pow_left₀ (Real.rpow_nonneg hZ.le _) (by linarith) order
  have hh:=inv_anti₀ (pow_pos (Real.rpow_pos_of_pos hZ _) _) hp
  have he : (Z^xi)^order=Z^(xi*(order:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  apply hh.trans_eq
  rw [he,←Real.rpow_neg hZ.le]
  congr 1
  ring

theorem actual_tail_arbitrary_saving (xi saving mass : ℝ) (hxi:0< xi) :
    ∃order:ℕ,∀(F:O→ℂ)(B:ℝ)(keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K Z:ℝ),
      (∀z,‖F z‖≤ B) → 0< K → 1≤ Z → B^2*max 1 K≤ Z^mass →
      radialEnergy F (fun z=> keep z ∧ K*Z^xi<‖ringComplex z‖^2) Φ K≤
        (4*(1+Real.pi)^2*tailControl order Φ)*Z^(-saving) := by
  obtain ⟨order,horder⟩:=exists_nat_ge ((mass+saving)/xi)
  have ho:mass-xi*(order:ℝ)≤-saving := by
    have hh:mass+saving≤(order:ℝ)*xi:=(div_le_iff₀ hxi).mp horder
    linarith
  refine ⟨order,?_⟩
  intro F B keep Φ K Z hF hK hZ hmass
  have hz:0< Z:=by linarith
  have hh:=actual_radial_tail order F B hF keep Φ K (K*Z^xi) hK (by positivity)
  have hdiv:K*Z^xi/K=Z^xi:=by field_simp
  rw [hdiv] at hh
  have hc:0≤4*(1+Real.pi)^2*tailControl order Φ:=by unfold tailControl;positivity
  have hb:(B^2*max 1 K)*((1+Z^xi)^order)⁻¹≤ Z^(-saving) := by
    calc
      _≤ Z^mass*Z^(-xi*(order:ℝ)) :=
        mul_le_mul hmass (reciprocal_cutoff_bound Z xi order hz) (by positivity) (Real.rpow_nonneg hz.le _)
      _=Z^(mass-xi*(order:ℝ)) := by rw [←Real.rpow_add hz];congr 1;ring
      _≤ Z^(-saving):=Real.rpow_le_rpow_of_exponent_le hZ ho
  apply hh.trans
  convert mul_le_mul_of_nonneg_left hb hc using 1 <;> first | rfl | ring

end CenteredMomentNaturalRadialCutoff

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentFirstSectorLocalization
open Eisenstein  SchwartzPlanePoisson
open CenteredMomentFirstDiscardedEnergy CenteredMomentSectorLocalization CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow CenteredMomentFirstTailAggregate
open CanonicalQuadraticSieve HeckeFamily CenteredMomentHeckeExpansion CenteredMomentFirstEnergy
local notation "O" => Eisenstein.O

open CenteredMomentFirstLocalization

def retainedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalRetainedTerm I J hI hJ E W K
    (firstNominalScale I J (∏ P∈E,P.val) K X) Z ξ

def discardedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalDiscardedTerm I J hI hJ E W K
    (firstNominalScale I J (∏ P∈E,P.val) K X) Z ξ

theorem reducedFirstSum_sector_split (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) (hK : 0< K) :
    reducedFirstSum I J hI hJ W K=canonicalZeroPair I J hI hJ W K+
      retainedPair I J hI hJ W K X Z ξ+discardedPair I J hI hJ W K X Z ξ := by
  unfold reducedFirstSum canonicalZeroPair retainedPair discardedPair
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  let Tsec:=firstNominalScale I J (∏ P∈E,P.val) K X
  dsimp only [canonicalZeroTerm,canonicalRetainedTerm,canonicalDiscardedTerm]
  simp_rw [← normValue_eq_embedding]
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  have ha : a≠0 := supported_element_ne_zero _ (residualGenerator_supported I J hI)
  have hb : b≠0 := supported_element_ne_zero _ (residualGenerator_supported J I hJ)
  have hr : r≠0 := finitePrimeModulus_ne_zero _
  have he : TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) E≠0 := TruncatedPrincipalPoisson.primeSubsetGenerator_ne_zero _ _
  have hk : 0<(K/normValue (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) E))/normValue (a*(b*r)) :=
    div_pos (div_pos hK (norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr he)))
      (norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero ha (mul_ne_zero hb hr))))
  have hh := lattice_fourier_split W _ hk
    (tripleFourier a b r ha hb hr (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI))
    (normValue (a*(b*r)))
    (tripleFourier_norm_le_full a b r ha hb hr _ _ _ (activeFunction_norm_le_one I J hI))
    (frequencyRadius Tsec Z ξ)
  let e := TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let k := (K/normValue e)/normValue (a*(b*r))
  let F := tripleFourier a b r ha hb hr (residualCharacter I J hI)
    (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)
  let d := (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e
  change d*((k:ℂ)*∑' h : O,F h*paperRadialFourier W ((K/normValue e)*normValue h/normValue (a*(b*r))))=
    d*((k:ℂ)*(F 0*paperRadialFourier W 0))+
      d*((k:ℂ)*∑' h : O,(retainedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*F h*paperRadialFourier W (k*normValue h))+
      d*((k:ℂ)*∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*F h*paperRadialFourier W (k*normValue h))
  have heq (h : O) : (K/normValue e)*normValue h/normValue (a*(b*r))=k*normValue h := by dsimp [k];ring
  simp_rw [heq]
  rw [hh]
  ring

def retainedEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      retainedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K X Z ξ

def discardedEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      discardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K X Z ξ

theorem finiteHeckeEnergy_sector_localized (η : Character) (m A : O) (t : ℝ)
    (hmLam : lambda∣m) (hm2 : (2:O)∣m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ))
    (K X Z ξ : ℝ) (hK : 0< K) :
    finiteHeckeEnergy η m A t S c W K=
      zeroEnergy η m A t S c W K+retainedEnergy η m A t S c W K X Z ξ+
        discardedEnergy η m A t S c W K X Z ξ := by
  rw [finiteHeckeEnergy_reduced_poisson η m A t hmLam hm2 S c W K hK]
  simp_rw [reducedFirstSum_sector_split _ _ _ _ W K X Z ξ hK,mul_add,Finset.sum_add_distrib]
  rfl

end CenteredMomentFirstSectorLocalization

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap

namespace CenteredMomentSourceProfileMassUniform
open Eisenstein CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass
local notation "O" => Eisenstein.O

theorem profile_mass_explicit {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (b D : ι → ℝ) (b₁ b₂ D₁ D₂ : ℝ)
    (hb : ∀ j,0≤ b j) (hb₁ : 0≤ b₁) (hb₂ : 0≤ b₂)
    (hD : ∀ j,0≤ D j) (hD₁ : 0≤ D₁) (hD₂ : 0≤ D₂)
    (hzSlot : ∀ j,Wslot j 0=0) (hz₁ : W₁ 0=0) (hz₂ : W₂ 0=0)
    (hsSlot : ∀ j x,Wslot j x≠0→x≤ b j)
    (hs₁ : ∀ x,W₁ x≠0→x≤ b₁) (hs₂ : ∀ x,W₂ x≠0→x≤ b₂)
    (hbound : ∀ j x,‖Wslot j x‖≤ D j)
    (hbound₁ : ∀ x,‖W₁ x‖≤ D₁) (hbound₂ : ∀ x,‖W₂ x‖≤ D₂)
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (hν : ∀ j I,‖ν j I‖≤1)
    (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O)
    (hP : ∀ j,0< P j) (hX₁ : 0< X₁) (hX₂ : 0< X₂) (hY₁ : 0< Y₁) (hY₂ : 0< Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (S : Finset (Tuple ι)) :
    (∑v∈S,‖profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖)≤
      (2*128^(Fintype.card ι+2)*(∏j,D j)*D₁*D₂*(∏j,b j)*b₁*b₂)*
        (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏j,P j) := by
  let e := Fintype.equivFin ι
  have hzero : ∀ i,sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i 0=0 := by
    simpa only [Fin.forall_fin_add,sourceProfiles,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hzSlot (e.symm j)) (And.intro hz₁ hz₂)
  have hs : ∀ i x,sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i x≠0→
      x≤ sourceBounds (fun j => b (e.symm j)) b₁ b₂ i := by
    simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hsSlot (e.symm j)) (And.intro hs₁ hs₂)
  have hbound' : ∀ i x,‖sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i x‖≤
      sourceBounds (fun j => D (e.symm j)) D₁ D₂ i := by
    simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hbound (e.symm j)) (And.intro hbound₁ hbound₂)
  have hm := originalCoefficient_mass (Fintype.card ι) 1 one_ne_zero
    (1 : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) R 0 (fun j => ν (e.symm j))
    (fun j I => hν _ I) (fun j => Wslot (e.symm j)) (fun j => P (e.symm j))
    (fun j => b (e.symm j)) (fun j => D (e.symm j)) W₁ W₂
    b₁ b₂ D₁ D₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s
    (fun j => hb _) hb₁ hb₂ (fun j => hD _) hD₁ hD₂
    (fun j => hP _) hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY hzero hs hbound'
    (S.image (tupleEquiv e))
  rw [finite_original_mass_reindex] at hm
  simp_rw [profileCoefficient_eq_original]
  simpa only [sourceMassConstant,e.symm.prod_comp D,e.symm.prod_comp b,e.symm.prod_comp P] using hm

theorem profile_mass_uniform {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ) (a b : ι → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j,0< a j) (hb : ∀ j,0≤ b j)
    (ha₁ : 0< a₁) (hb₁ : 0≤ b₁) (ha₂ : 0< a₂) (hb₂ : 0≤ b₂)
    (hsSlot : ∀ j,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hWslot : ∀ j,ContDiff ℝ ∞ (Wslot j)) :
    ∃ C : ℝ,0< C ∧ ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁ : ℝ→ℂ)⊆Set.Icc a₁ b₁ →
      Function.support (W₂ : ℝ→ℂ)⊆Set.Icc a₂ b₂ →
      ∀ (R : Ideal O) (ν : ι→Ideal O→ℂ),(∀ j I,‖ν j I‖≤1)→
      ∀ (P : ι→ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0< P j)→0< X₁→0< X₂→0< Y₁→0< Y₂→B₁≠0→B₂≠0→
      X₁*X₂=T→Y₁*Y₂=T→∀ S : Finset (Tuple ι),
      (∑v∈S,‖profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖)≤
        (C*SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)*
          (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏j,P j) := by
  choose D hD hbound hz hs using fun j =>
    smooth_annular_bound (Wslot j) (a j) (b j) (ha j) (hsSlot j) (hWslot j)
  let C₀ := 2*128^(Fintype.card ι+2)*(∏j,D j)*(∏j,b j)*b₁*b₂
  have hprodD : 0≤∏j,D j := Finset.prod_nonneg (fun j _ => hD j)
  have hprodb : 0≤∏j,b j := Finset.prod_nonneg (fun j _ => hb j)
  have hC₀ : 0≤ C₀ := by dsimp [C₀]; positivity
  refine ⟨1+C₀,by positivity,?_⟩
  intro W₁ W₂ hs₁ hs₂ R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  have hzW (W : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0< a)
      (hs : Function.support (W : ℝ→ℂ)⊆Set.Icc a b) : W 0=0 := by
    by_contra hn
    exact (not_le_of_gt ha) (hs hn).1
  have hm := profile_mass_explicit Wslot W₁ W₂ b D b₁ b₂
    (SchwartzMap.seminorm ℝ 0 0 W₁) (SchwartzMap.seminorm ℝ 0 0 W₂)
    hb hb₁ hb₂ hD (apply_nonneg _ _) (apply_nonneg _ _) hz
    (hzW W₁ a₁ b₁ ha₁ hs₁) (hzW W₂ a₂ b₂ ha₂ hs₂) hs
    (fun x hx => (hs₁ hx).2) (fun x hx => (hs₂ hx).2) hbound
    (SchwartzMap.norm_le_seminorm ℝ W₁) (SchwartzMap.norm_le_seminorm ℝ W₂)
    R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  have hT : 0< T := hX ▸ mul_pos hX₁ hX₂
  have hprodP : 0≤∏j,P j := Finset.prod_nonneg (fun j _ => (hP j).le)
  have hpos : 0≤ SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂*
      (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏j,P j) := by positivity
  apply hm.trans
  have hh := mul_le_mul_of_nonneg_right (show C₀≤1+C₀ by linarith) hpos
  dsimp only [C₀] at hh
  nlinarith only [hh]
end CenteredMomentSourceProfileMassUniform

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace CenteredMomentSourceInputTailUniform
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceZeroEnergy CenteredMomentSourceLiveColumn CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceProfileMassUniform CenteredMomentSourceProfileMass
open CenteredMomentSupportedTailAggregate CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair CenteredMomentNaturalRadialCutoff
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

omit [DecidableEq ι] in
lemma volume_pos (s:Input ι):0< volume s.toData:=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=> s.P_pos i))

omit [DecidableEq ι] in
theorem input_mass (hi:ι→ℝ)(whi:ℝ)(hhi:∀i,0≤ hi i)(hwhi:0≤ whi)
    (s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ))(wlo:ℝ)(hwlo:0< wlo)
    (he₁:s.W₁=W₁)(he₂:s.W₂=W₂)
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hshi:∀i,s.hi i≤ hi i)(R seed:Ideal O):
    (∑I∈finiteColumns (Fintype.piFinset s.pools),‖coefficient s R seed I‖)≤
      (2*128^(Fintype.card ι+2)*(∏i,hi i)*whi^2)*plainControl s W₁ W₂*volume s.toData:=by
  have hz (i:ι):s.W i 0=0:=by
    by_contra hn
    exact (not_le_of_gt (s.lo_pos i)) (s.support i hn).1
  have hzW (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc wlo whi):W 0=0:=by
    by_contra hn
    exact (not_le_of_gt hwlo) (hs hn).1
  have hm:=profile_mass_explicit s.W W₁ W₂ hi s.M whi whi
    (SchwartzMap.seminorm ℝ 0 0 W₁) (SchwartzMap.seminorm ℝ 0 0 W₂)
    hhi hwhi hwhi (fun i=> zero_le_one.trans (s.M_ge_one i))
    (apply_nonneg _ _) (apply_nonneg _ _) hz (hzW W₁ hs₁) (hzW W₂ hs₂)
    (fun i x hx=>((s.support i hx).2).trans (hshi i))
    (fun x hx=>(hs₁ hx).2) (fun x hx=>(hs₂ hx).2) s.W_bound
    (SchwartzMap.norm_le_seminorm ℝ W₁) (SchwartzMap.norm_le_seminorm ℝ W₂)
    R s.ν s.ν_bound s.P s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed
    s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos one_ne_zero one_ne_zero
    rfl s.same_product (Fintype.piFinset s.pools)
  have hc:=finiteColumnCoefficient_mass (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P W₁ W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
  unfold coefficient
  rw [he₁,he₂]
  change (∑I∈_,‖finiteColumnCoefficient _ _ I‖)≤ _
  apply (hc.trans hm).trans_eq
  simp only [map_one,Nat.cast_one,one_mul,div_one,plainControl,CenteredMomentExceptionalAmplitudePair.volume]
  ring

omit [DecidableEq ι] in
lemma input_column_bound (hi:ι→ℝ)(whi:ℝ)
    (s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ))(wlo:ℝ)(hwlo:0< wlo)
    (he₁:s.W₁=W₁)(he₂:s.W₂=W₂)
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hshi:∀i,s.hi i≤ hi i)(R seed I:Ideal O)(hn:coefficient s R seed I≠0):
    (Ideal.absNorm I:ℝ)≤((∏i,hi i)*whi^2)*volume s.toData:=by
  obtain ⟨v,hv,hv0,hvI⟩:=finiteColumnCoefficient_witness _ _ I hn
  have hz (i:ι):s.W i 0=0:=by
    by_contra h
    exact (not_le_of_gt (s.lo_pos i)) (s.support i h).1
  have hzW (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc wlo whi):W 0=0:=by
    by_contra h
    exact (not_le_of_gt hwlo) (hs h).1
  unfold coefficient at hn
  rw [he₁,he₂] at hv0
  have hp:=profileCoefficient_product_bound R s.ν s.W s.P hi W₁ W₂ whi whi
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed
    s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos one_ne_zero one_ne_zero rfl s.same_product
    hz (hzW W₁ hs₁) (hzW W₂ hs₂) (fun i x hx=>((s.support i hx).2).trans (hshi i))
    (fun x hx=>(hs₁ hx).2) (fun x hx=>(hs₂ hx).2) v hv0
  rw [hvI] at hp
  apply hp.2.trans_eq
  simp only [map_one,Nat.cast_one,one_mul,div_one,CenteredMomentExceptionalAmplitudePair.volume]
  ring

lemma kernel_inverse_cap (HN Z B Tsec:ℝ)(hZ:1≤ Z)(hB:0≤ B)(hT:0< Tsec)(hcap:Tsec≤ Z^B):
    ((min 1 (kernelReference Tsec HN))^2)⁻¹≤
      (1+Real.exp (2*HN))^2*(Z^B)^2:=by
  have hz:0< Z:=zero_lt_one.trans_le hZ
  have hpow:1≤ Z^B:=Real.one_le_rpow hZ hB
  have he:0< Real.exp (2*HN):=Real.exp_pos _
  have hb:(min 1 (kernelReference Tsec HN))⁻¹≤(1+Real.exp (2*HN))*Z^B:=by
    rw [min_def]
    split_ifs with h
    · simp only [inv_one]
      nlinarith
    · have hi:(kernelReference Tsec HN)⁻¹=Tsec*Real.exp (2*HN):=by
        unfold kernelReference
        rw [show -2*HN= -(2*HN) by ring,Real.exp_neg]
        field_simp
      rw [hi]
      calc
        _≤ Z^B*Real.exp (2*HN):=mul_le_mul_of_nonneg_right hcap he.le
        _≤ _:=by nlinarith [Real.rpow_pos_of_pos hz B]
  rw [←inv_pow]
  exact (pow_le_pow_left₀ (inv_nonneg.mpr (le_of_lt (lt_min zero_lt_one (kernelReference_pos Tsec HN hT)))) hb 2).trans_eq (mul_pow _ _ _)

lemma eventually_tail_threshold (HN ξ:ℝ)(hξ:0<ξ):
    ∀ᶠZ:ℝ in atTop,1< Z ∧ 2*HN/Real.log Z+Real.log (4:ℝ)/Real.log Z<ξ/4:=by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop ((2*HN+Real.log (4:ℝ))/(ξ/4)))] with Z hZ hlog
  refine ⟨hZ,?_⟩
  rw [←add_div]
  apply (div_lt_iff₀ (Real.log_pos hZ)).mpr
  have ht:0<ξ/4:=by linarith
  have hh:2*HN+Real.log (4:ℝ)< Real.log Z*(ξ/4):=(div_lt_iff₀ ht).mp hlog
  nlinarith

lemma choose_tail_order (B ξ saving:ℝ)(hB:0≤ B)(hξ:0<ξ):
    ∃Adec:ℕ,∀(HN Z V Tsec:ℝ),1≤ Z→0< V→V≤ Z^B→0< Tsec→Tsec≤ Z^B→
      V^3*((min 1 (kernelReference Tsec HN))^2)⁻¹*((1+Z^(ξ/4))^Adec)⁻¹≤
        (1+Real.exp (2*HN))^2*Z^(-saving):=by
  obtain ⟨Adec,hAdec⟩:=exists_nat_ge ((5*B+saving)/(ξ/4))
  have horder:5*B-(ξ/4)*(Adec:ℝ)≤-saving:=by
    have hh:5*B+saving≤(Adec:ℝ)*(ξ/4):=(div_le_iff₀ (by linarith:0<ξ/4)).mp hAdec
    linarith
  refine ⟨Adec,?_⟩
  intro HN Z V Tsec hZ hV hVcap hT hTcap
  have hz:0< Z:=zero_lt_one.trans_le hZ
  have hk:=kernel_inverse_cap HN Z B Tsec hZ hB hT hTcap
  have hd:=reciprocal_cutoff_bound Z (ξ/4) Adec hz
  calc
    _≤(Z^B)^3*((1+Real.exp (2*HN))^2*(Z^B)^2)*Z^(-(ξ/4)*(Adec:ℝ)):=by
      apply mul_le_mul _ hd (by positivity) (by positivity)
      apply mul_le_mul (pow_le_pow_left₀ hV.le hVcap 3) hk
        (inv_nonneg.mpr (sq_nonneg _)) (by positivity)
    _=(1+Real.exp (2*HN))^2*Z^(5*B-(ξ/4)*(Adec:ℝ)):=by
      rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_mul_natCast hz.le]
      norm_num only [Nat.cast_ofNat]
      rw [show Z^(B*(3:ℝ))*((1+Real.exp (2*HN))^2*Z^(B*(2:ℝ)))*Z^(-(ξ/4)*(Adec:ℝ))=
        (1+Real.exp (2*HN))^2*(Z^(B*3)*Z^(B*2)*Z^(-(ξ/4)*(Adec:ℝ))) by ring]
      rw [←Real.rpow_add hz,←Real.rpow_add hz]
      congr 2
      ring
    _≤ _:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ horder) (sq_nonneg _)

omit [DecidableEq ι] in
theorem second_input_tail_arbitrary_saving (hi:ι→ℝ)(wlo whi B ξ saving:ℝ)
    (hhi:∀i,0≤ hi i)(hwlo:0< wlo)(hwhi:0≤ whi)(hB:0≤ B)(hξ:0<ξ):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤ hi i)→∀(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K Tsec:ℝ),
      0< K→volume s.toData≤ Z^B→Tsec≤ Z^B→(volume s.toData)^2/K≤ Tsec→
      ‖secondDiscardedEnergy s.η s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K Tsec Z ξ‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving):=by
  obtain ⟨Adec,hdecay⟩:=choose_tail_order B ξ saving hB hξ
  obtain ⟨SΦ,Ctail,hCtail,htail⟩:=second_discarded_energy_bound Adec
  let Cmass:=1+2*128^(Fintype.card ι+2)*(∏i,hi i)*whi^2
  have hprodhi:0≤∏i,hi i:=Finset.prod_nonneg (fun i _=> hhi i)
  have hCmass:0< Cmass:=by dsimp [Cmass];positivity
  let HN:=Real.log (max 1 ((∏i,hi i)*whi^2))
  have hexp:(∏i,hi i)*whi^2≤ Real.exp HN:=by
    dsimp [HN]
    rw [Real.exp_log (zero_lt_one.trans_le (le_max_left _ _))]
    exact le_max_right _ _
  let C:=Cmass^2*Ctail*(Real.exp HN)^2*(1+Real.exp (2*HN))^2
  refine ⟨SΦ,C,by dsimp [C];positivity,?_⟩
  filter_upwards [eventually_tail_threshold HN ξ hξ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi R seed Φ K Tsec hK hVcap hTcap hnom
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
  have ht:=htail s.η s.t (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)
    Φ K V HN Tsec Z 1 ξ hK hV hZ.1 le_rfl hn hnom (by simpa using hZ.2)
  have hsquare:=pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=> norm_nonneg _)) hm 2
  have hp:0< min 1 (kernelReference Tsec HN):=lt_min zero_lt_one (kernelReference_pos _ _ hT)
  have hzpos:0< Z:=zero_lt_one.trans hZ.1
  have hzpower:0< Z^(ξ/4):=Real.rpow_pos_of_pos hzpos _
  have hden:0<(min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec:=by positivity
  have hb:=hdecay HN Z V Tsec hZ.1.le hV hVcap hT hTcap
  calc
    _≤((Cmass*plainControl s W₁ W₂*V)^2*K*(Real.exp HN*V)^2*
        (Ctail*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec))/V:=by
      apply div_le_div_of_nonneg_right _ hV.le
      apply ht.trans
      apply div_le_div_of_nonneg_right _ hden.le
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right hsquare hK.le
    _=(Cmass^2*Ctail*(Real.exp HN)^2*(plainControl s W₁ W₂)^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        (V^3*((min 1 (kernelReference Tsec HN))^2)⁻¹*((1+Z^(ξ/4))^Adec)⁻¹):=by
      field_simp [ne_of_gt hV,ne_of_gt hp]
    _≤(Cmass^2*Ctail*(Real.exp HN)^2*(plainControl s W₁ W₂)^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        ((1+Real.exp (2*HN))^2*Z^(-saving)):=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _=_:=by dsimp [C];ring

end CenteredMomentSourceInputTailUniform

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace CenteredMomentSourceInputZeroUniform
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceZeroEnergy CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceProfileMass CenteredMomentSourceInputTailUniform
open CenteredMomentFirstLocalization SchwartzPlanePoisson
open CenteredMomentExceptionalAmplitudePair CenteredMomentAddedZeroUniform
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

omit [DecidableEq ι] in
theorem first_input_zero_bound (hi:ι→ℝ)(wlo whi ε:ℝ)
    (hhi:∀i,0≤ hi i)(hwlo:0< wlo)(_hwhi:0≤ whi)(hε:0<ε):
    ∃C:ℝ,0< C ∧ ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤ hi i)→∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0≤ K→
      ‖zeroEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*K*‖paperRadialFourier Φ 0‖*(volume s.toData)^ε:=by
  obtain ⟨C₀,hC₀,hbound⟩:=active_tuple_zero_energy_bound (Fintype.card ι) ε hε
  let L:=1+(∏i,hi i)*whi^2
  have hprod:0≤∏i,hi i:=Finset.prod_nonneg (fun i _=> hhi i)
  have hL:0< L:=by dsimp [L];positivity
  refine ⟨4*C₀*L^(1+ε),by positivity,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK
  let V:=volume s.toData
  have hV:0< V:=volume_pos s
  let β:=profileCoefficient R s.ν s.W s.P W₁ W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed
  have hc:coefficient s R seed=finiteColumnCoefficient (Fintype.piFinset s.pools) β:=by
    unfold coefficient;rw [he₁,he₂]
  have hcontrol:=plainControl_nonneg s W₁ W₂
  have hβ (v:Tuple ι):‖β v‖≤2*plainControl s W₁ W₂:=by
    have hb:=profileCoefficient_norm_le R s.ν s.ν_bound s.W s.P s.M W₁ W₂
      (SchwartzMap.seminorm ℝ 0 0 W₁) (SchwartzMap.seminorm ℝ 0 0 W₂)
      (fun i=> zero_le_one.trans (s.M_ge_one i)) (apply_nonneg _ _) (apply_nonneg _ _)
      s.W_bound (SchwartzMap.norm_le_seminorm ℝ W₁) (SchwartzMap.norm_le_seminorm ℝ W₂)
      s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v
    exact hb.trans_eq (by dsimp [plainControl];ring)
  have hz (i:ι):s.W i 0=0:=by
    by_contra hn
    exact (not_le_of_gt (s.lo_pos i)) (s.support i hn).1
  have hzW (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc wlo whi):W 0=0:=by
    by_contra hn
    exact (not_le_of_gt hwlo) (hs hn).1
  have hN (v:Tuple ι)(hv:β v≠0):finiteTupleProduct v≠0 ∧
      (Ideal.absNorm (finiteTupleProduct v):ℝ)≤ L*V:=by
    have hp:=profileCoefficient_product_bound R s.ν s.W s.P hi W₁ W₂ whi whi
      s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed
      s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos one_ne_zero one_ne_zero rfl s.same_product
      hz (hzW W₁ hs₁) (hzW W₂ hs₂) (fun i x hx=>((s.support i hx).2).trans (hshi i))
      (fun x hx=>(hs₁ hx).2) (fun x hx=>(hs₂ hx).2) v hv
    refine ⟨hp.1,hp.2.trans ?_⟩
    simp only [map_one,Nat.cast_one,one_mul,div_one]
    change (∏i,hi i)*whi*whi*(s.X₁*s.X₂)*(∏i,s.P i)≤ _
    have hh:0≤ V:=hV.le
    dsimp [L,V,CenteredMomentExceptionalAmplitudePair.volume] at *
    nlinarith
  rw [hc]
  by_cases hsmall:L*V<1
  · rw [zeroEnergy_eq_zero_of_subunit s.η m A s.t (Fintype.piFinset s.pools) β Φ K
      (L*V) hsmall (fun v _ hv=> hN v hv),norm_zero,zero_div]
    positivity
  have hb:=hbound (le_refl (Fintype.card ι)) s.η m A s.t (Fintype.piFinset s.pools) β Φ
    (L*V) K (2*plainControl s W₁ W₂) (le_of_not_gt hsmall) hK (by positivity)
    (fun v _ _=> hβ v) (fun I _ hI=> by
      obtain ⟨v,hv,hn,he⟩:=finiteColumnCoefficient_witness _ _ I hI
      rw [←he];exact (hN v hn).2)
  apply (div_le_div_of_nonneg_right hb hV.le).trans_eq
  have hp:(L*V)^(1+ε)/V=L^(1+ε)*V^ε:=by
    rw [Real.mul_rpow hL.le hV.le,Real.rpow_add hV,Real.rpow_one]
    field_simp
  change C₀*K*(2*plainControl s W₁ W₂)^2*‖paperRadialFourier Φ 0‖*(L*V)^(1+ε)/V=_
  calc
    _=4*C₀*(plainControl s W₁ W₂)^2*K*‖paperRadialFourier Φ 0‖*((L*V)^(1+ε)/V):=by ring
    _=_:=by rw [hp];ring

omit [DecidableEq ι] in
theorem first_input_zero_uniform (hi:ι→ℝ)(wlo whi ε:ℝ)
    (hhi:∀i,0≤ hi i)(hwlo:0< wlo)(hwhi:0≤ whi)(hε:0<ε):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤ hi i)→∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0≤ K→
      ‖zeroEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*
        (volume s.toData)^ε:=by
  obtain ⟨C₀,hC₀,hb⟩:=first_input_zero_bound hi wlo whi ε hhi hwlo hwhi hε
  obtain ⟨SΦ,D,hD,hd⟩:=paperRadialFourier_euler_source_weighted_bound 0 0
  refine ⟨SΦ,C₀*D,mul_pos hC₀ hD,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK
  have hf:‖paperRadialFourier Φ 0‖≤ D*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ:=by
    simpa only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,pow_zero,one_mul,zero_mul] using
      hd Φ 0 le_rfl 0 le_rfl
  have hVp:0≤(volume s.toData)^ε:=Real.rpow_nonneg (volume_pos s).le _
  apply (hb s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK).trans
  calc
    _≤ C₀*(plainControl s W₁ W₂)^2*K*(D*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)*
        (volume s.toData)^ε:=by gcongr
    _=_:=by ring

omit [DecidableEq ι] in
theorem first_input_zero_capped (hi:ι→ℝ)(wlo whi B ε:ℝ)
    (hhi:∀i,0≤ hi i)(hwlo:0< wlo)(hwhi:0≤ whi)(hB:0≤ B)(hε:0<ε):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧ ∀Z:ℝ,1≤ Z→
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤ hi i)→volume s.toData≤ Z^B→
      ∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0≤ K→
      ‖zeroEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^ε:=by
  let δ:=ε/(B+1)
  have hδ:0<δ:=div_pos hε (by linarith)
  obtain ⟨SΦ,C,hC,hb⟩:=first_input_zero_uniform hi wlo whi δ hhi hwlo hwhi hδ
  refine ⟨SΦ,C,hC,?_⟩
  intro Z hZ s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi hV m A R seed Φ K hK
  have hp:(volume s.toData)^δ≤ Z^ε:=by
    calc
      _≤(Z^B)^δ:=Real.rpow_le_rpow (volume_pos s).le hV hδ.le
      _=Z^(B*δ):=(Real.rpow_mul (zero_le_one.trans hZ) B δ).symm
      _≤ _:=Real.rpow_le_rpow_of_exponent_le hZ (by
        have hh:δ*(B+1)=ε:=by dsimp [δ];field_simp
        nlinarith)
  exact (hb s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK).trans
    (mul_le_mul_of_nonneg_left hp (by positivity))

end CenteredMomentSourceInputZeroUniform

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace CenteredMomentSourceInputFirstTailUniform
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstScale
open Eisenstein
local notation "O" => Eisenstein.O

lemma common_subset_product_dvd_right (I J : Ideal O) (E : Finset (CommonIndex I J)) :
    (∏P∈E,P.val)∣commonPart J I := by
  apply (Finset.prod_dvd_prod_of_subset E Finset.univ
    (fun P : CommonIndex I J=> P.val) (Finset.subset_univ _)).trans
  rw [commonPart_right_product]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  simpa only [pow_one] using pow_dvd_pow P.val (rightExponent_pos I J P)

theorem first_nominal_scale_le (I J : Ideal O) (E : Finset (CommonIndex I J))
    (K X : ℝ) (hK : 0< K) :
    firstNominalScale I J (∏P∈E,P.val) K X≤ X^2/K := by
  have hC := norm_pos (commonPart I J) (commonPart_ne_zero I J)
  have hD := norm_pos (commonPart J I) (commonPart_ne_zero J I)
  have hE : (Ideal.absNorm (∏P∈E,P.val):ℝ)≤ Ideal.absNorm (commonPart J I) := by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero J I)))
      (map_dvd Ideal.absNorm (common_subset_product_dvd_right I J E))
  have hA : (Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)≤ Ideal.absNorm (commonPart I J) := by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero I J)))
      (map_dvd Ideal.absNorm (activeConductor_span_dvd I J))
  unfold firstNominalScale
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul hE hA (by positivity) hD.le) (sq_nonneg X))
    (mul_nonneg (mul_nonneg hK.le hC.le) hD.le)).trans_eq
  field_simp

end CenteredMomentSourceInputFirstTailUniform

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace CenteredMomentSourceInputFirstTailUniform
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

lemma choose_first_tail_order (B ξ saving:ℝ)(hB:0≤ B)(hξ:0<ξ):
    ∃Adec:ℕ,∀(HN Z V Tsec:ℝ),1≤ Z→0< V→V≤ Z^B→0< Tsec→Tsec≤ Z^B→
      V^2*((min 1 (kernelReference Tsec HN))^2)⁻¹*((1+Z^(ξ/4))^Adec)⁻¹≤
        (1+Real.exp (2*HN))^2*Z^(-saving):=by
  obtain ⟨Adec,hAdec⟩:=exists_nat_ge ((4*B+saving)/(ξ/4))
  have horder:4*B-(ξ/4)*(Adec:ℝ)≤-saving:=by
    have hh:4*B+saving≤(Adec:ℝ)*(ξ/4):=(div_le_iff₀ (by linarith:0<ξ/4)).mp hAdec
    linarith
  refine ⟨Adec,?_⟩
  intro HN Z V Tsec hZ hV hVcap hT hTcap
  have hz:0< Z:=zero_lt_one.trans_le hZ
  have hk:=kernel_inverse_cap HN Z B Tsec hZ hB hT hTcap
  have hd:=reciprocal_cutoff_bound Z (ξ/4) Adec hz
  calc
    _≤(Z^B)^2*((1+Real.exp (2*HN))^2*(Z^B)^2)*Z^(-(ξ/4)*(Adec:ℝ)):=by
      apply mul_le_mul _ hd (by positivity) (by positivity)
      apply mul_le_mul (pow_le_pow_left₀ hV.le hVcap 2) hk
        (inv_nonneg.mpr (sq_nonneg _)) (by positivity)
    _=(1+Real.exp (2*HN))^2*Z^(4*B-(ξ/4)*(Adec:ℝ)):=by
      rw [←Real.rpow_mul_natCast hz.le]
      norm_num only [Nat.cast_ofNat]
      rw [show Z^(B*(2:ℝ))*((1+Real.exp (2*HN))^2*Z^(B*(2:ℝ)))*Z^(-(ξ/4)*(Adec:ℝ))=
        (1+Real.exp (2*HN))^2*(Z^(B*2)*Z^(B*2)*Z^(-(ξ/4)*(Adec:ℝ))) by ring]
      rw [←Real.rpow_add hz,←Real.rpow_add hz]
      congr 2
      ring
    _≤ _:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ horder) (sq_nonneg _)


end CenteredMomentSourceInputFirstTailUniform
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentSourceInputFirstSectorTail
open Eisenstein  CubicEisenstein SchwartzPlanePoisson 
open CenteredMomentFirstReduced CenteredMomentSectorLocalization CenteredMomentCorrelation
open CenteredMomentCommonSupport CenteredMomentCanonicalFirst CenteredMomentSupportedCorrelation
open CenteredMomentFirstScale CenteredMomentFirstDiscarded CenteredMomentActive
open CenteredMomentCompleteCommon  CenteredMomentFirstDiscardedEnergy
open CenteredMomentSourceInputFirstTailUniform
local notation "O"=> Eisenstein.O

lemma local_tail_denominator_mono (Tlocal Tupper H Z ξ:ℝ)(A:ℕ)(B:ℝ)
    (hT:0< Tlocal)(hupper:Tlocal≤ Tupper)(hB:0≤ B)(hZ:0≤ Z):
    B/((min 1 (kernelReference Tlocal H))^2*(1+Z^(ξ/4))^A)≤
      B/((min 1 (kernelReference Tupper H))^2*(1+Z^(ξ/4))^A):=by
  have hu:0< Tupper:=hT.trans_le hupper
  have hk:kernelReference Tupper H≤ kernelReference Tlocal H:=by
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hT hupper
  have hm:0< min 1 (kernelReference Tupper H):=lt_min zero_lt_one (kernelReference_pos _ _ hu)
  have hp:0≤ Z^(ξ/4):=Real.rpow_nonneg hZ _
  apply div_le_div_of_nonneg_left hB (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact pow_le_pow_left₀ hm.le (min_le_min_left 1 hk) 2

theorem local_discarded_pair_bound (A : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ),0< C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (I J : Ideal O)
        (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
        (K X HN Tsec Z Csec ξ : ℝ),
      0< K → 0< X → 1< Z → 1≤ Csec →
      (Ideal.absNorm I:ℝ)≤ Real.exp HN*X → (Ideal.absNorm J:ℝ)≤ Real.exp HN*X →
      X^2/K≤ Tsec →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖∑ E∈inactiveSubsets I J,canonicalDiscardedTerm I J hI hJ E W K
        (firstNominalScale I J (∏ P∈E,P.val) K X) Z ξ‖ ≤
      (Ideal.absNorm I:ℝ)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := canonical_discarded_term_bound A
  obtain ⟨D,hD,hsub⟩ := CompletedGauss.prime_support_subsets_bound ε hε
  refine ⟨s,D*C,mul_pos hD hC,?_⟩
  intro W I J hI hJ K X HN Tsec Z Csec ξ hK hX hZ hCs hi hj hsec hthreshold
  have hc : ((inactiveSubsets I J).card:ℝ)≤ D*(Ideal.absNorm I:ℝ)^ε := by
    apply le_trans _ (hsub I hI.1)
    exact_mod_cast inactiveSubsets_card I J
  calc
    _ ≤ ∑ E∈inactiveSubsets I J,‖canonicalDiscardedTerm I J hI hJ E W K
        (firstNominalScale I J (∏ P∈E,P.val) K X) Z ξ‖ := norm_sum_le _ _
    _ ≤ ∑ _E∈inactiveSubsets I J,
        K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A) :=
      Finset.sum_le_sum (fun E hE => by
        let Tlocal:=firstNominalScale I J (∏ P∈E,P.val) K X
        have hE0:(∏ P∈E,P.val)≠(0:Ideal O):=by
          have he:=TruncatedPrincipalPoisson.primeSubsetGenerator_ne_zero (fun P:CommonIndex I J=> P.val) E
          have hh:=Ideal.span_singleton_eq_bot.not.mpr he
          simpa only [TruncatedPrincipalPoisson.primeSubsetGenerator_span,Ideal.zero_eq_bot] using hh
        have hTl:0< Tlocal:=firstNominalScale_pos I J _ hE0 K X hK hX
        have hTu:Tlocal≤ Tsec:=(first_nominal_scale_le I J E K X hK).trans hsec
        have hh:=ht W I J hI hJ E K X HN Tlocal Z Csec ξ hK hX hZ hCs hi hj le_rfl hthreshold
        exact hh.trans (local_tail_denominator_mono Tlocal Tsec HN Z ξ A
          (K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)) hTl hTu (by positivity) (zero_lt_one.trans hZ).le))
    _ = ((inactiveSubsets I J).card:ℝ)*
        (K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A)) := by simp
    _ ≤ (D*(Ideal.absNorm I:ℝ)^ε)*
        (K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

end CenteredMomentSourceInputFirstSectorTail

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentSourceInputFirstSectorTail
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentFirstTailAggregate CenteredMomentFirstDiscardedEnergy
open CenteredMomentFirstScale CenteredMomentSectorLocalization CenteredMomentHeckeExpansion
local notation "O"=> Eisenstein.O

private theorem pair_mass {α : Type*} [Fintype α] (c w : α → ℂ) (F : α → α → ℂ)
    (hw : ∀ i,‖w i‖≤1) (B : ℝ) (_hB : 0≤ B)
    (hF : ∀ i j,c i≠0 → c j≠0 → ‖F i j‖≤ B) :
    ‖∑ i,∑ j,((c i*w i)*star (c j*w j))*F i j‖≤(∑ i,‖c i‖)^2*B := by
  have ht (i j : α) : ‖((c i*w i)*star (c j*w j))*F i j‖≤‖c i‖*‖c j‖*B := by
    by_cases hi : c i=0
    · simp [hi]
    by_cases hj : c j=0
    · simp [hj]
    rw [norm_mul,norm_mul,norm_star]
    apply mul_le_mul _ (hF i j hi hj) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    apply mul_le_mul _ _ (norm_nonneg _) (norm_nonneg _)
    · rw [norm_mul];exact mul_le_of_le_one_right (norm_nonneg _) (hw i)
    · rw [norm_mul];exact mul_le_of_le_one_right (norm_nonneg _) (hw j)
  calc
    _ ≤ ∑ i,‖∑ j,((c i*w i)*star (c j*w j))*F i j‖ := norm_sum_le _ _
    _ ≤ ∑ i,∑ j,‖c i‖*‖c j‖*B := Finset.sum_le_sum (fun i _ => (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ht i j)))
    _ = _ := by rw [pow_two,Finset.sum_mul,Finset.sum_mul];apply Finset.sum_congr rfl;intro i hi;rw [Finset.mul_sum,Finset.sum_mul]

theorem local_discarded_energy_bound (Adec : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0< C ∧
      ∀ (η : Character) (m A : O) (t : ℝ) (S : Finset (Ideal O)) (c : Ideal O → ℂ)
        (W : 𝓢(ℝ,ℂ)) (K X H Tsec Z Csec ξ : ℝ),0< K → 0< X → 1< Z → 1≤ Csec →
      (∀ I∈S,c I≠0 → (Ideal.absNorm I:ℝ)≤ Real.exp H*X) →
      X^2/K≤ Tsec →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖CenteredMomentFirstSectorLocalization.discardedEnergy η m A t S c W K X Z ξ‖≤
        (∑ I∈S,‖c I‖)^2*(Real.exp H*X)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨s,C,hC,ht⟩ := local_discarded_pair_bound Adec ε hε
  refine ⟨s,C,hC,?_⟩
  intro η m A t S c W K X H Tsec Z Csec ξ hK hX hZ hCs hN hsec hthreshold
  let B := (Real.exp H*X)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec)
  have hB : 0≤ B := by dsimp only [B];positivity
  have hpair (I J : supportedColumns S) (hi : c I≠0) (hj : c J≠0) :
      ‖CenteredMomentFirstSectorLocalization.discardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K X Z ξ‖≤ B := by
    have hni := hN I (Finset.mem_filter.mp I.property).1 hi
    have hnj := hN J (Finset.mem_filter.mp J.property).1 hj
    apply (ht W I J (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2
      K X H Tsec Z Csec ξ hK hX hZ hCs hni hnj hsec hthreshold).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _) hni hε.le) hK.le
  have hp := pair_mass (fun I : supportedColumns S => c I)
    (fun I => CenteredMomentHeckeExpansion.rowWeight η m A 1 t I)
    (fun I J => CenteredMomentFirstSectorLocalization.discardedPair I J (Finset.mem_filter.mp I.property).2
      (Finset.mem_filter.mp J.property).2 W K X Z ξ)
    (fun I => CenteredMomentAbsoluteEnergy.rowWeight_norm_le_one_all η m A 1 t I) B hB hpair
  have hm : (∑ I : supportedColumns S,‖c I‖)≤∑ I∈S,‖c I‖ := by
    rw [Finset.sum_coe_sort (supportedColumns S) (fun I => ‖c I‖)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => norm_nonneg _)
  apply hp.trans
  convert mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (show 0 ≤ ∑ I : supportedColumns S, ‖c I‖ from
      Finset.sum_nonneg (fun I _ => norm_nonneg (c I))) hm 2) hB using 1 ; dsimp only [B];ring

end CenteredMomentSourceInputFirstSectorTail

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

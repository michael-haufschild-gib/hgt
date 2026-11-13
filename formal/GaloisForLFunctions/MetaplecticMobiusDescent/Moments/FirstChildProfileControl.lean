/-
First child profile control adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.AmplificationRadicalFamilies

/-!
# First child profile control

Masses, cardinalities and exceptional constants of first child profiles; normalized common
reference powers and conductor caps; frozen controls of the allocation Gauss energy.
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

namespace CenteredMomentFirstMaskedFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open  CompletedGauss RayFourExpansion
open CenteredMomentFixedRowMask
open CenteredMomentFirstFamily CenteredMomentFirstIdealFamily CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstColumns CenteredMomentCanonicalFirst CenteredMomentCommonSupport
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentSourceRow
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationShortening CenteredMomentAmplificationSourceDomain
open CenteredMomentAmplificationFamily CenteredMomentSourceAllocationEnergy
open CenteredMomentAmplificationFamilyEnergy CenteredMomentOriginalChildEnergy
open CenteredMomentGaussEnergy CenteredMomentLiveDomain CenteredMomentPrimaryCharacter
open Eisenstein  CenteredMomentChildAssembly CenteredMomentChildRows
local notation "O" => Eisenstein.O
local notation "fixedBadMask" => (lambda*(2:O))

def rayHeight (p : O) (k : ℕ) (τ : RayCharacter → Character) (t : ℝ) (I : Ideal O) : ℂ :=
  ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I

def extractedSource (η : Character) (u : O) (C : Ideal O)
    (β : Ideal O → ℂ) (t : ℝ) (I : Ideal O) : ℂ :=
  β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t C*idealMask u I

theorem exists_masked_radical_family (η : Character) (p : O)
    (hs : Supported (Ideal.span {p})) (hpp : lambda^2∣p-1) (k : ℕ) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤ radicalBound (childCharacter η χ) fixedBadMask p k) ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        rowWeight η fixedBadMask 1 1 t I*residualCharacter p k (primaryIdealGenerator I)=
          rayHeight p k τ t I) ∧
      (∀ u : O, ∀ I : Ideal O, Supported I → ∀ t : ℝ,
        rowWeight η (fixedBadMask*u) 1 1 t I*residualCharacter p k (primaryIdealGenerator I)=
          idealMask u I*rayHeight p k τ t I) ∧
      ∀ (Q : Finset (Ideal O)) (u : O) (C : Ideal O) (β : Ideal O → ℂ)
        (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ),
        sourceGaussEnergy Q (fun I => β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t (C*I))
          (fun I => residualCharacter p k (primaryIdealGenerator I)) W K =
        sourceGaussEnergy Q (extractedSource η u C β t) (rayHeight p k τ t) W K := by
  obtain ⟨τ,hN,hτ⟩ := exists_radical_family η fixedBadMask p fixed_mask_ne_zero hs hpp
    (dvd_mul_right lambda (2:O)) (dvd_mul_left (2:O) lambda) k
  refine ⟨τ,hN,hτ,?_,?_⟩
  · intro u I hI t
    rw [rowWeight_mask_factor η u I hI t,mul_assoc,hτ I hI t]
    rfl
  · intro Q u C β t W K
    apply sourceGaussEnergy_congr
    intro I _ hI
    rw [extracted_masked_coefficient η u C I hI β t,hτ I hI t]
    rfl

theorem exists_masked_error_source (η : Character) (p : O) (hp : Prime p)
    (hs : Supported (Ideal.span {p})) (hpp : lambda^2∣p-1)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤
        radicalBound (childCharacter η χ) fixedBadMask p (errorMovingExponent n)) ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        rowWeight η fixedBadMask 1 1 t I*
          residualCharacter p (errorMovingExponent n) (primaryIdealGenerator I)=
            rayHeight p (errorMovingExponent n) τ t I) ∧
      ∀ (S : Finset (Ideal O)) (u : O) (C : Ideal O) (β : Ideal O → ℂ)
        (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ),
        sourceGaussEnergy (residualColumns S p hp (n+1))
          (fun I => β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t (C*I))
          (fun I => residualCharacter p (n+1) (primaryIdealGenerator I)) W K =
        sourceGaussEnergy (residualColumns S p hp (n+1))
          (extractedSource η u C β t) (rayHeight p (errorMovingExponent n) τ t) W K := by
  obtain ⟨τ,hN,hτ,_,henergy⟩ := exists_masked_radical_family η p hs hpp (errorMovingExponent n)
  refine ⟨τ,hN,hτ,?_⟩
  intro S u C β t W K
  rw [←henergy (residualColumns S p hp (n+1)) u C β t W K]
  apply sourceGaussEnergy_congr
  intro I hI _
  rw [residual_column_active S p hp hs n hn I hI]

lemma idealMask_mul (u : O) (C I : Ideal O) :
    idealMask u (C*I)=idealMask u C*idealMask u I := by
  simp only [idealMask,IsCoprime.mul_left_iff]
  split_ifs <;> simp_all

lemma extractedSource_whole_mask (η : Character) (u : O) (C : Ideal O)
    (hC : Supported C) (β : Ideal O → ℂ) (t : ℝ) (I : Ideal O) :
    extractedSource η u C β t I =
      maskedSource u β (C*I)*rowWeight η fixedBadMask 1 1 t C := by
  rw [extractedSource,rowWeight_mask_factor η u C hC t,maskedSource,idealMask_mul]
  ring

lemma extracted_gauss_row (η : Character) (p : O) (k : ℕ) (τ : RayCharacter → Character)
    (hτ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      rowWeight η fixedBadMask 1 1 t I*residualCharacter p k (primaryIdealGenerator I)=
        rayHeight p k τ t I)
    (Q : Finset (Ideal O)) (u : O) (C : Ideal O) (β : Ideal O → ℂ) (t : ℝ) (z : O) :
    gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q =>
        (β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t (C*I))*
          residualCharacter p k (primaryIdealGenerator I)) z =
    ∑ χ : RayCharacter, phaseCoeff (amplificationPhase p k) χ *
      gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
        (fun I : supportedColumns Q => extractedSource η u C β t I*heightCoeff (τ χ) t I) z := by
  rw [←gaussPolynomial_allocation]
  apply congrArg (fun c => gaussPolynomial Finset.univ (sourceGenerator Q)
    (sourceGenerator_supported Q) c z)
  funext I
  have hI := (Finset.mem_filter.mp I.property).2
  rw [extracted_masked_coefficient η u C I hI β t,hτ I hI t]
  simp only [rayHeight,Finset.mul_sum,extractedSource]
  apply Finset.sum_congr rfl
  intro χ _
  ring

theorem exists_masked_error_rows (η : Character) (p : O) (hp : Prime p)
    (hs : Supported (Ideal.span {p})) (hpp : lambda^2∣p-1)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤
        radicalBound (childCharacter η χ) fixedBadMask p (errorMovingExponent n)) ∧
      ∀ (S : Finset (Ideal O)) (u : O) (C : Ideal O) (β : Ideal O → ℂ) (t : ℝ) (z : O),
      let Q := residualColumns S p hp (n+1)
      gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
        (fun I : supportedColumns Q =>
          (β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t (C*I))*
            residualCharacter p (n+1) (primaryIdealGenerator I)) z =
      ∑ χ : RayCharacter, phaseCoeff (amplificationPhase p (errorMovingExponent n)) χ *
        gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
          (fun I : supportedColumns Q => extractedSource η u C β t I*heightCoeff (τ χ) t I) z := by
  obtain ⟨τ,hN,hτ,_,_⟩ := exists_masked_radical_family η p hs hpp (errorMovingExponent n)
  refine ⟨τ,hN,?_⟩
  intro S u C β t z
  dsimp only
  rw [←extracted_gauss_row η p (errorMovingExponent n) τ hτ
    (residualColumns S p hp (n+1)) u C β t z]
  apply congrArg (fun c => gaussPolynomial Finset.univ
    (sourceGenerator (residualColumns S p hp (n+1)))
    (sourceGenerator_supported (residualColumns S p hp (n+1))) c z)
  funext I
  rw [residual_column_active S p hp hs n hn I (Finset.mem_filter.mp I.property).1]

lemma paired_gauss_rows (η τ₁ τ₂ : Character) (F₁ F₂ : O → ℂ)
    (h₁ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      heightCoeff τ₁ t I=rowWeight η fixedBadMask 1 1 t I*F₁ (primaryIdealGenerator I))
    (h₂ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      heightCoeff τ₂ t I=rowWeight η fixedBadMask 1 1 t I*F₂ (primaryIdealGenerator I))
    (Q₁ Q₂ : Finset (Ideal O)) (β₁ β₂ : Ideal O → ℂ) (u₁ u₂ : O) (t : ℝ) (z₁ z₂ : O) :
    gaussPolynomial Finset.univ (sourceGenerator Q₁) (sourceGenerator_supported Q₁)
      (fun I : supportedColumns Q₁ => β₁ I*
        (rowWeight η (fixedBadMask*u₁) 1 1 t I*F₁ (primaryIdealGenerator I))) z₁ *
    star (gaussPolynomial Finset.univ (sourceGenerator Q₂) (sourceGenerator_supported Q₂)
      (fun I : supportedColumns Q₂ => β₂ I*
        (rowWeight η (fixedBadMask*u₂) 1 1 t I*F₂ (primaryIdealGenerator I))) z₂) =
    gaussPolynomial Finset.univ (sourceGenerator Q₁) (sourceGenerator_supported Q₁)
      (fun I : supportedColumns Q₁ => maskedSource u₁ β₁ I*heightCoeff τ₁ t I) z₁ *
    star (gaussPolynomial Finset.univ (sourceGenerator Q₂) (sourceGenerator_supported Q₂)
      (fun I : supportedColumns Q₂ => maskedSource u₂ β₂ I*heightCoeff τ₂ t I) z₂) := by
  rw [first_gauss_row η τ₁ F₁ h₁ Q₁ β₁ u₁ t z₁,
    first_gauss_row η τ₂ F₂ h₂ Q₂ β₂ u₂ t z₂]

end CenteredMomentFirstMaskedFamily

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open Filter

namespace CenteredMomentFirstSourceConductorCaps
open Eisenstein   HeckeFamily
open CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentAmplificationRadicalFamily CenteredMomentChildRows
open CenteredMomentSecondHeightFamily
local notation "O"=> Eisenstein.O

def rayCost : ℝ := (Ideal.span {(12:O)}).absNorm*fixedPresentationCost

lemma rayCost_nonneg : 0≤ rayCost :=
  mul_nonneg (Nat.cast_nonneg _) fixedPresentationCost_pos.le

theorem radical_once_cap (ρ υ : Character) (χ : RayCharacter) (p : O) (hp : p≠0) (k : ℕ)
    (hυ : υ.modulus.absNorm≤ radicalBound (childCharacter ρ χ) fixedBadMask p k) :
    (υ.modulus.absNorm:ℝ)≤ rayCost*(ρ.modulus.absNorm:ℝ)*(Ideal.span {p}).absNorm := by
  have hP : (1:ℕ)≤(Ideal.span {p}).absNorm := Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp))
  have ht : (if k=0 then 1 else (Ideal.span {p}).absNorm)≤(Ideal.span {p}).absNorm := by
    split_ifs <;> omega
  have hr:=CenteredMomentSecondRadicalBudget.child_modulus_bound ρ χ
  have hn : υ.modulus.absNorm≤
      (ρ.modulus.absNorm*(Ideal.span {(12:O)}).absNorm)*
      (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*(Ideal.span {p}).absNorm := by
    apply hυ.trans
    unfold radicalBound
    gcongr
  have hh : (υ.modulus.absNorm:ℝ)≤
      ((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*
      (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*(Ideal.span {p}).absNorm := by
    exact_mod_cast hn
  convert hh using 1 <;> first | rfl | (unfold rayCost fixedPresentationCost; ring)

theorem fixed_error_cap (η : Character) (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayCharacter)
    (F : FixedPair η C D hC E ξ₁ ξ₂) (ρ υ : Character)
    (hρ : ρ=F.left ∨ ρ=F.right) (χ : RayCharacter) (p : O) (hp : p≠0) (k : ℕ)
    (hυ : υ.modulus.absNorm≤ radicalBound (childCharacter ρ χ) fixedBadMask p k) :
    (υ.modulus.absNorm:ℝ)≤(rayCost*fixedPresentationCost)*
      (η.modulus.absNorm:ℝ)*(C.absNorm:ℝ)^2*(Ideal.span {p}).absNorm := by
  have hf:=fixed_pair_caps η C D hC E ξ₁ ξ₂ F
  have hr : (ρ.modulus.absNorm:ℝ)≤ fixedPresentationCost*(η.modulus.absNorm:ℝ)*(C.absNorm:ℝ)^2 := by
    rcases hρ with rfl|rfl
    · exact hf.1
    · exact hf.2
  apply (radical_once_cap ρ υ χ p hp k hυ).trans
  have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr rayCost_nonneg)
    (Nat.cast_nonneg (Ideal.span {p}).absNorm)
  convert hh using 1 <;> first | rfl | ring

theorem eventually_caps (ε : ℝ) (hε : 0<ε) :
    ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀η:Character,∀(C D:Ideal O)(hC:Supported C),
    ∀(E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayCharacter)(F:FixedPair η C D hC E ξ₁ ξ₂),
    ∀q B:ℝ,(η.modulus.absNorm:ℝ)≤ Z^q→(C.absNorm:ℝ)≤ Z^B→
    (F.left.modulus.absNorm:ℝ)≤ Z^(q+2*B+ε) ∧
    (F.right.modulus.absNorm:ℝ)≤ Z^(q+2*B+ε) ∧
    ∀(ρ υ:Character), (ρ=F.left∨ρ=F.right)→∀(χ:RayCharacter)(p:O),p≠0→
    ∀(k:ℕ)(r:ℝ),υ.modulus.absNorm≤ radicalBound (childCharacter ρ χ) fixedBadMask p k→
    ((Ideal.span {p}).absNorm:ℝ)≤ Z^r→(υ.modulus.absNorm:ℝ)≤ Z^(q+2*B+r+ε) := by
  have he := (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε))
    (max fixedPresentationCost (rayCost*fixedPresentationCost))
  filter_upwards [he,eventually_gt_atTop (1:ℝ)] with Z hconst hZ
  refine ⟨hZ,?_⟩
  intro η C D hC E ξ₁ ξ₂ F q B hη hCcap
  have hz : 0< Z:=zero_lt_one.trans hZ
  have hm:=fixed_pair_caps η C D hC E ξ₁ ξ₂ F
  have hb : fixedPresentationCost*(η.modulus.absNorm:ℝ)*(C.absNorm:ℝ)^2≤ Z^(q+2*B+ε) := by
    calc
      _≤ Z^ε*Z^q*(Z^B)^2 := by
        gcongr
        exact (le_max_left _ _).trans hconst
      _=_ := by rw [←Real.rpow_natCast,←Real.rpow_mul hz.le,←Real.rpow_add hz,←Real.rpow_add hz];congr 1;ring
  refine ⟨hm.1.trans hb,hm.2.trans hb,?_⟩
  intro ρ υ hρ χ p hp k r hυ hP
  apply (fixed_error_cap η C D hC E ξ₁ ξ₂ F ρ υ hρ χ p hp k hυ).trans
  calc
    _≤ Z^ε*Z^q*(Z^B)^2*Z^r := by
      gcongr
      exact (le_max_right _ _).trans hconst
    _=_ := by rw [←Real.rpow_natCast,←Real.rpow_mul hz.le,←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz];congr 1;ring

end CenteredMomentFirstSourceConductorCaps

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstChildProfileControl
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonRadialPointwise CenteredMomentCommonExceptionalCost
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentFiniteProfileExceptional
open CenteredMomentFiniteProfileExceptionalPhysical
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mass (s : Input ι) : ℝ := ∏ i,s.M i

omit [DecidableEq ι] in
lemma mass_one (s : Input ι) : 1≤ mass s :=
  Finset.one_le_prod (fun i _=> s.M_ge_one i)

omit [DecidableEq ι] in
lemma mass_nonneg (s : Input ι) : 0≤ mass s := zero_le_one.trans (mass_one s)

omit [DecidableEq ι] in
lemma child_mass (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) : mass (child s C R B τ t)≤ mass s := by
  change (∏i:liveIndices B.val,s.M i.val)≤∏i,s.M i
  rw [Finset.prod_coe_sort]
  exact Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _)
    (fun i _=> zero_le_one.trans (s.M_ge_one i)) (fun i _ _=> s.M_ge_one i)

omit [DecidableEq ι] in
lemma child_card (B : CenteredMomentAddedZeroUniform.Tuple ι) :
    Fintype.card (liveIndices B)≤ Fintype.card ι := by
  simpa using Finset.card_le_card (Finset.subset_univ (liveIndices B))

omit [DecidableEq ι] in
lemma slot_control_bound (s : Input ι) (b : ℝ) (hb : 1≤ b) (hu : s.upper≤ b) :
    slotControl s.toData≤(128*b)^Fintype.card ι*mass s^2 := by
  have hpoint (i : ι) : max 1 (128*max 0 (s.hi i)*s.M i)≤(128*b)*s.M i := by
    apply max_le
    · have hM:=s.M_ge_one i
      nlinarith
    · apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans (s.M_ge_one i))
      exact mul_le_mul_of_nonneg_left (max_le (by linarith) ((s.upper_ge i).trans hu)) (by norm_num)
  have hp:=Finset.prod_le_prod (fun i (_:i∈Finset.univ)=> by positivity)
    (fun i (_:i∈Finset.univ)=> hpoint i)
  calc
    slotControl s.toData=mass s*(∏i,max 1 (128*max 0 (s.hi i)*s.M i)):=rfl
    _≤ mass s*(∏i,(128*b)*s.M i):=mul_le_mul_of_nonneg_left hp (mass_nonneg s)
    _=(128*b)^Fintype.card ι*mass s^2:=by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
      unfold mass
      ring

omit [DecidableEq ι] in
lemma profile_cost_bound (s : Input ι) (N : ℕ) (b A : ℝ)
    (hb : 1≤ b) (hu : s.upper≤ b) (hc : Fintype.card ι≤ N) (hm : mass s≤ A) :
    profileCost s≤(2*(max 1 s.b₁*max 1 s.b₂)*b^N*A^2)*mass s^2 := by
  have hb0:0≤ b:=zero_le_one.trans hb
  have hp : (max 1 s.upper)^Fintype.card ι≤ b^N :=
    (pow_le_pow_left₀ (by positivity) (max_le hb hu) _).trans (pow_le_pow_right₀ hb hc)
  have hm2:=pow_le_pow_left₀ (mass_nonneg s) hm 2
  have h:=mul_le_mul hm2 hp (by positivity) (sq_nonneg A)
  have h':=(mul_le_mul_of_nonneg_right h
    (show 0≤2*(max 1 s.b₁*max 1 s.b₂)*mass s^2 by positivity))
  convert h' using 1 <;> first | rfl | ((try simp only [profileCost,Data.profileFactor,mass]); ring)

omit [DecidableEq ι] in
lemma exceptional_slot_bound (s : Input ι) (N : ℕ) (b A : ℝ)
    (hb : 1≤ b) (hu : s.upper≤ b) (hc : Fintype.card ι≤ N) (hm : mass s≤ A) :
    slotControl s.toData^2*frozenProfile s^2≤
      ((128*b)^N)^2*(b^N)^2*A^4*mass s^2 := by
  have hb0:0≤ b:=zero_le_one.trans hb
  have hp : (max 1 s.upper)^Fintype.card ι≤ b^N :=
    (pow_le_pow_left₀ (by positivity) (max_le hb hu) _).trans (pow_le_pow_right₀ hb hc)
  have h128 : (1:ℝ)≤128*b := by linarith
  have hs : slotControl s.toData≤(128*b)^N*mass s^2 :=
    (slot_control_bound s b hb hu).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h128 hc) (sq_nonneg _))
  have hf : frozenProfile s≤ mass s*b^N :=
    mul_le_mul_of_nonneg_left hp (mass_nonneg s)
  have h:=mul_le_mul (pow_le_pow_left₀ (slotControl_nonneg _) hs 2)
    (pow_le_pow_left₀ (frozenProfile_nonneg s) hf 2) (sq_nonneg _) (sq_nonneg _)
  calc
    _≤((128*b)^N*mass s^2)^2*(mass s*b^N)^2:=h
    _=((128*b)^N)^2*(b^N)^2*mass s^4*mass s^2:=by ring
    _≤ _:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mass_nonneg s) hm 4) (by positivity))
      (sq_nonneg _)

omit [DecidableEq ι] in
theorem twice_controls (N : ℕ) (b : ℝ) (hb : 1≤ b)
    (s : Input ι) (hu : s.upper≤ b) (hc : Fintype.card ι≤ N)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :
    let d:=twiceChild s C R B τ t Q k Bp υ v;
    profileCost d≤(2*(max 1 s.b₁*max 1 s.b₂)*b^N*mass s^2)*mass d^2 ∧
    slotControl d.toData^2*frozenProfile d^2≤
      ((128*b)^N)^2*(b^N)^2*mass s^4*mass d^2 := by
  let d:=twiceChild s C R B τ t Q k Bp υ v
  have hm : mass d≤ mass s :=
    (child_mass (child s C R B τ t) (Q^k) (R*C) Bp υ v).trans
      (child_mass s C R B τ t)
  have hn : Fintype.card (liveIndices Bp.val)≤ N :=
    (child_card Bp.val).trans ((child_card B.val).trans hc)
  exact ⟨profile_cost_bound d N b (mass s) hb hu hn hm,
    exceptional_slot_bound d N b (mass s) hb hu hn hm⟩

def exceptionalConstant (N : ℕ) (b : ℝ) (J : ℕ) (Q : Ideal O) (K : ℝ) : ℝ :=
  K*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*
    (1+2*Real.pi)^(4*J)*
    (∫u:ℝ,(1+‖u‖)^J*‖CenteredMomentHeckeColumnWindow.columnDensity
      CenteredMomentLogDyadic.logAnnulus CenteredMomentLogDyadic.logAnnulus_compact
      CenteredMomentLogDyadic.logAnnulus_smooth u‖)^2*
    ((128*b)^N)^2*(b^N)^2

omit [DecidableEq ι] in
lemma exceptional_factor_bound {wlo whi : ℝ}
    (S : Finset (ℕ×ℕ)) (p : Profiles wlo whi) (J : ℕ) (Q : Ideal O) (K : ℝ)
    (hK : 0≤ K) (s : Input ι) (N : ℕ) (b A : ℝ)
    (hb : 1≤ b) (hu : s.upper≤ b) (hc : Fintype.card ι≤ N) (hm : mass s≤ A) :
    profileFactor S s p J Q K≤ exceptionalConstant N b J Q K*
      p.control S^2*(1+‖s.t‖)^(2*J)*A^4*mass s^2 := by
  have h:=exceptional_slot_bound s N b A hb hu hc hm
  let F:=K*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*
    (1+2*Real.pi)^(4*J)*p.control S^2*(1+‖s.t‖)^(2*J)*
    (∫u:ℝ,(1+‖u‖)^J*‖CenteredMomentHeckeColumnWindow.columnDensity
      CenteredMomentLogDyadic.logAnnulus CenteredMomentLogDyadic.logAnnulus_compact
      CenteredMomentLogDyadic.logAnnulus_smooth u‖)^2
  have hF : 0≤ F := by dsimp [F]; positivity
  have hh:=mul_le_mul_of_nonneg_left h hF
  convert hh using 1 <;> first | rfl | ((try simp only [profileFactor,exceptionalConstant,F]); ring)

omit [DecidableEq ι] in
theorem twice_exceptional_factor {wlo whi : ℝ}
    (S : Finset (ℕ×ℕ)) (p : Profiles wlo whi) (J : ℕ) (Qfix : Ideal O) (K : ℝ)
    (hK : 0≤ K) (N : ℕ) (b : ℝ) (hb : 1≤ b)
    (s : Input ι) (hu : s.upper≤ b) (hc : Fintype.card ι≤ N)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :
    let d:=twiceChild s C R B τ t Q k Bp υ v;
    profileFactor S d p J Qfix K≤ exceptionalConstant N b J Qfix K*
      p.control S^2*(1+‖v‖)^(2*J)*mass s^4*mass d^2 := by
  let d:=twiceChild s C R B τ t Q k Bp υ v
  have hm : mass d≤ mass s :=
    (child_mass (child s C R B τ t) (Q^k) (R*C) Bp υ v).trans
      (child_mass s C R B τ t)
  have hn : Fintype.card (liveIndices Bp.val)≤ N :=
    (child_card Bp.val).trans ((child_card B.val).trans hc)
  exact exceptional_factor_bound S p J Qfix K hK d N b (mass s) hb hu hn hm

end CenteredMomentFirstChildProfileControl

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstErrorAllocationPower
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentFirstChildProfileControl
open CenteredMomentAmplificationAllocationCost CenteredMomentCommonProfile
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

lemma child_mass_eq (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (B : actualAllocations s.pools (Q^k)) (τ : Character) (t : ℝ) :
    mass (child s (Q^k) R B τ t)=mass s := by
  change (∏i:liveIndices B.val,s.M i.val)=∏i,s.M i
  rw [Finset.prod_coe_sort,prime_slots_live s Q hQ k hslot B]

lemma allocations_card (s : Input ι) (Q : Ideal O) (hQ : Prime Q) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) :
    Fintype.card (actualAllocations s.pools (Q^k))≤ k+1 := by
  simpa only [Fintype.card_coe] using actual_amplification_allocations_card s.pools Q hQ k
    (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩)

theorem power_sum_eq (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (τ : actualAllocations s.pools (Q^k)→Character)
    (t : actualAllocations s.pools (Q^k)→ℝ) (α : ℝ) :
    (∑B:actualAllocations s.pools (Q^k),
      volume (child s (Q^k) R B (τ B) (t B))^α*mass (child s (Q^k) R B (τ B) (t B))^2)=
    Fintype.card (actualAllocations s.pools (Q^k))*
      (volume s/(Q.absNorm:ℝ)^k)^α*mass s^2 := by
  simp_rw [child_volume s Q hQ k hslot,child_mass_eq s Q hQ k hslot]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

theorem power_sum_le (s : Input ι) (Q : Ideal O) (hQ : Prime Q) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (τ : actualAllocations s.pools (Q^k)→Character)
    (t : actualAllocations s.pools (Q^k)→ℝ) (α : ℝ) :
    (∑B:actualAllocations s.pools (Q^k),
      volume (child s (Q^k) R B (τ B) (t B))^α*mass (child s (Q^k) R B (τ B) (t B))^2)≤
    ((k+1:ℕ):ℝ)*(volume s/(Q.absNorm:ℝ)^k)^α*mass s^2 := by
  rw [power_sum_eq s Q hQ.ne_zero k hslot R τ t α]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_right _
    (Real.rpow_nonneg (div_nonneg (volume_pos s).le (pow_nonneg (Nat.cast_nonneg _) k)) α)
  exact_mod_cast allocations_card s Q hQ k hslot

theorem budget_sum_le (s : Input ι) (Q : Ideal O) (hQ : Prime Q) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (τ : actualAllocations s.pools (Q^k)→Character)
    (t : actualAllocations s.pools (Q^k)→ℝ)
    (n : ℕ) (a α : Fin n→ℝ) (ha : ∀j,0≤ a j) :
    (∑B:actualAllocations s.pools (Q^k),
      (∑j,a j*volume (child s (Q^k) R B (τ B) (t B))^(α j))*
        mass (child s (Q^k) R B (τ B) (t B))^2)≤
    ((k+1:ℕ):ℝ)*(∑j,a j*(volume s/(Q.absNorm:ℝ)^k)^(α j))*mass s^2 := by
  simp_rw [child_volume s Q hQ.ne_zero k hslot,child_mass_eq s Q hQ.ne_zero k hslot]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hs : 0≤∑j,a j*(volume s/(Q.absNorm:ℝ)^k)^(α j) :=
    Finset.sum_nonneg (fun j _=> mul_nonneg (ha j)
      (Real.rpow_nonneg (div_nonneg (volume_pos s).le (pow_nonneg (Nat.cast_nonneg _) k)) _))
  have hc : (Fintype.card (actualAllocations s.pools (Q^k)):ℝ)≤ k+1 := by
    exact_mod_cast allocations_card s Q hQ k hslot
  calc
    _≤((k:ℝ)+1)*((∑j,a j*(volume s/(Q.absNorm:ℝ)^k)^(α j))*mass s^2) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hs (sq_nonneg _))
    _=_ := by push_cast;ring

theorem error_budget_sum_le (s : Input ι) (Q : Ideal O) (hQ : Prime Q) (k : ℕ)
    (hk : k=1 ∨ k=6 ∨ k=7)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (τ : actualAllocations s.pools (Q^k)→Character)
    (t : actualAllocations s.pools (Q^k)→ℝ)
    (n : ℕ) (a α : Fin n→ℝ) (ha : ∀j,0≤ a j) :
    (∑B:actualAllocations s.pools (Q^k),
      (∑j,a j*volume (child s (Q^k) R B (τ B) (t B))^(α j))*
        mass (child s (Q^k) R B (τ B) (t B))^2)≤
    8*(∑j,a j*(volume s/(Q.absNorm:ℝ)^k)^(α j))*mass s^2 := by
  apply (budget_sum_le s Q hQ k hslot R τ t n a α ha).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_right _
    (Finset.sum_nonneg (fun j _=> mul_nonneg (ha j)
      (Real.rpow_nonneg (div_nonneg (volume_pos s).le (pow_nonneg (Nat.cast_nonneg _) k)) _)))
  rcases hk with rfl|rfl|rfl <;> norm_num

end CenteredMomentFirstErrorAllocationPower

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstAllocationGaussEnergy
open HeckeFamily CanonicalQuadraticSieve CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentSourceRow
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentCommonRawScale CenteredMomentAddedZeroUniform
open CenteredMomentGaussEnergy CenteredMomentSmoothedWindowEnergy
open CenteredMomentOriginalChildEnergy CenteredMomentHeckeColumnWindow
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

def commonEnergy (D : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑' z : O, ‖commonGauss D C hC τ t L z‖^2 *
    (W (‖ringComplex z‖^2/K)).re

def allocatedEnergy (D : OriginalData ι) (C L : Ideal O)
    (B : actualAllocations D.S C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  (sourceGaussEnergy (allocatedData D C L B).columns
    (allocatedData D C L B).beta (heightCoeff τ t) W K).re

lemma common_summable (D : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) :
    Summable (fun z : O => ‖commonGauss D C hC τ t L z‖^2 *
      (W (‖ringComplex z‖^2/K)).re) := by
  exact (gaussEnergy_hasSum_re Finset.univ
    (sourceGenerator (CenteredMomentFirstSectors.residualPool C hC.1 D.columns))
    (sourceGenerator_supported _) _ W K hK).summable

lemma allocated_hasSum (D : OriginalData ι) (C L : Ideal O)
    (B : actualAllocations D.S C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) :
    HasSum (fun z : O =>
      ‖gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
        (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z‖^2 *
      (W (‖ringComplex z‖^2/K)).re)
      (allocatedEnergy D C L B τ t W K) :=
  gaussEnergy_hasSum_re _ _ _ _ W K hK

lemma allocated_nonneg (D : OriginalData ι) (C L : Ideal O)
    (B : actualAllocations D.S C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K)
    (hW : ∀ z : O, 0≤(W (‖ringComplex z‖^2/K)).re) :
    0≤ allocatedEnergy D C L B τ t W K := by
  rw [← (allocated_hasSum D C L B τ t W K hK).tsum_eq]
  exact tsum_nonneg (fun z => mul_nonneg (sq_nonneg _) (hW z))

theorem common_energy_allocation (D : OriginalData ι)
    (hS : ∀ i, ∀ I∈D.S i, I≠0) (hp : ∀ i, ∀ I∈D.S (Sum.inl i), Prime I)
    (C : Ideal O) (hC : Supported C) (hseed : D.s∣C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K)
    (hW : ∀ z : O, 0≤(W (‖ringComplex z‖^2/K)).re) :
    commonEnergy D C hC τ t L W K ≤
      ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 * allocatedEnergy D C L B τ t W K := by
  unfold commonEnergy
  apply Real.tsum_le_of_sum_le (fun z => mul_nonneg (sq_nonneg _) (hW z))
  intro rows
  calc
    _ ≤ ∑ z∈rows, ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 *
          (‖gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
            (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z‖^2 *
          (W (‖ringComplex z‖^2/K)).re) := by
      apply Finset.sum_le_sum
      intro z hz
      rw [common_gauss_allocation D hS hp C hC hseed τ t L z]
      have hc := mul_le_mul_of_nonneg_right
        (cover_norm_sum_sq_le_card Finset.univ
          (fun B : actualAllocations D.S C =>
            frozenCoefficient B.val C D.R D.nu D.slot D.lengths *
              gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
                (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z))
        (hW z)
      simpa only [Finset.card_univ,Fintype.card_coe,norm_mul,mul_pow,Finset.sum_mul,mul_assoc] using hc
    _ = ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 *
          ∑ z∈rows, ‖gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
            (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z‖^2 *
            (W (‖ringComplex z‖^2/K)).re := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact sum_le_hasSum rows (fun z _ => mul_nonneg (sq_nonneg _) (hW z))
        (allocated_hasSum D C L B τ t W K hK)

def rawVolume (D : OriginalData ι) : ℝ :=
  (D.X₁*D.X₂/((Ideal.absNorm D.B₁:ℝ)*Ideal.absNorm D.B₂)) * ∏ i,D.lengths i

lemma rawVolume_pos (D : OriginalData ι) (hX₁ : 0< D.X₁) (hX₂ : 0< D.X₂)
    (hB₁ : D.B₁≠0) (hB₂ : D.B₂≠0) (hP : ∀ i,0< D.lengths i) : 0< rawVolume D := by
  apply mul_pos (div_pos (mul_pos hX₁ hX₂) _)
    (Finset.prod_pos (fun i _ => hP i))
  exact mul_pos (CenteredMomentFirstScale.norm_pos _ hB₁) (CenteredMomentFirstScale.norm_pos _ hB₂)

lemma allocated_rawVolume_mul (D : OriginalData ι) (C L : Ideal O)
    (B : actualAllocations D.S C) (hB₁ : D.B₁≠0) (hB₂ : D.B₂≠0) :
    rawVolume (allocatedData D C L B) * rawReduction B.val D.lengths = rawVolume D := by
  have hB := (allocation_data D.S C B.val (Finset.mem_filter.mp B.property).1).1
  have hv := remainingRaw_source B.val hB D.B₁ D.B₂ hB₁ hB₂ (D.X₁*D.X₂) D.lengths
  change _ = rawVolume (allocatedData D C L B) at hv
  rw [← hv]
  exact raw_scale_identity B.val hB _ D.lengths

lemma allocated_rawVolume (D : OriginalData ι) (C L : Ideal O)
    (B : actualAllocations D.S C) (hB₁ : D.B₁≠0) (hB₂ : D.B₂≠0)
    (hP : ∀ i,0< D.lengths i) :
    rawVolume (allocatedData D C L B) = rawVolume D / rawReduction B.val D.lengths := by
  have hr := rawReduction_pos B.val
    (allocation_data D.S C B.val (Finset.mem_filter.mp B.property).1).1 D.lengths hP
  exact (eq_div_iff hr.ne').mpr (allocated_rawVolume_mul D C L B hB₁ hB₂)

lemma rawVolume_both (D : OriginalData ι) (T : ℝ)
    (hX : D.X₁*D.X₂=T) (hY : D.Y₁*D.Y₂=T) :
    rawVolume D=(T/((Ideal.absNorm D.B₁:ℝ)*Ideal.absNorm D.B₂))*∏ i,D.lengths i ∧
    rawVolume D=(D.Y₁*D.Y₂/((Ideal.absNorm D.B₁:ℝ)*Ideal.absNorm D.B₂))*∏ i,D.lengths i := by
  simp only [rawVolume,hX,hY,and_self]

def frozenControl (B : Tuple ι) (M : ι → ℝ) : ℝ :=
  ∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),M i

lemma frozenControl_nonneg (B : Tuple ι) (M : ι → ℝ)
    (hM : ∀ i,0≤ M i) : 0≤ frozenControl B M :=
  Finset.prod_nonneg (fun i _ => hM i)

lemma frozen_norm_bound (D : OriginalData ι) (C : Ideal O)
    (B : actualAllocations D.S C) (M : ι → ℝ) (_hM : ∀ i,0≤ M i)
    (hν : ∀ i I,‖D.nu i I‖≤1) (hW : ∀ i x,‖D.slot i x‖≤ M i) :
    ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖≤ frozenControl B.val M := by
  unfold frozenCoefficient frozenControl
  rw [norm_mul]
  have hc : ‖(if IsCoprime C D.R then (1:ℂ) else 0)‖≤1 := by split_ifs <;> simp
  apply (mul_le_of_le_one_right (norm_nonneg _) hc).trans
  rw [norm_prod]
  apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
  intro i hi
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hν i _)).trans (hW i _)

theorem frozen_normalized_bound (N : ℕ) (a b : ℝ) (ha : 0< a)
    (D : OriginalData ι) (hcard : Fintype.card ι≤ N)
    (C : Ideal O) (hC : C≠0) (B : actualAllocations D.S C)
    (M : ι → ℝ) (hM : ∀ i,0≤ M i) (hP : ∀ i,0< D.lengths i)
    (hν : ∀ i I,‖D.nu i I‖≤1) (hWnorm : ∀ i x,‖D.slot i x‖≤ M i)
    (hW : ∀ i,Function.support (D.slot i)⊆Set.Icc a b) :
    ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2/rawReduction B.val D.lengths ≤
      (max 1 b)^N/(Ideal.absNorm C:ℝ)*(frozenControl B.val M)^2 := by
  have hB := (allocation_data D.S C B.val (Finset.mem_filter.mp B.property).1).1
  have hR := rawReduction_pos B.val hB D.lengths hP
  have hN := CenteredMomentFirstScale.norm_pos C hC
  by_cases hz : frozenCoefficient B.val C D.R D.nu D.slot D.lengths=0
  · rw [hz,norm_zero,zero_pow (by decide : 2≠0),zero_div]
    positivity
  · have hm := frozen_norm_bound D C B M hM hν hWnorm
    have hh := (actual_reduction_norm B.val hB C D.R
      (Finset.mem_filter.mp B.property).2 D.nu D.slot D.lengths hP a b ha hW hz).2
    have he : (max 1 b)^Fintype.card ι≤(max 1 b)^N :=
      pow_le_pow_right₀ (le_max_left _ _) hcard
    have hi : (1:ℝ)/rawReduction B.val D.lengths ≤ (max 1 b)^N/(Ideal.absNorm C:ℝ) := by
      apply (div_le_div_iff₀ hR hN).mpr
      simpa only [one_mul] using hh.trans (mul_le_mul_of_nonneg_right he hR.le)
    calc
      _ ≤ (frozenControl B.val M)^2/rawReduction B.val D.lengths :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hm _) hR.le
      _ = (frozenControl B.val M)^2*(1/rawReduction B.val D.lengths) := by ring
      _ ≤ (frozenControl B.val M)^2*((max 1 b)^N/(Ideal.absNorm C:ℝ)) :=
        mul_le_mul_of_nonneg_left hi (sq_nonneg _)
      _ = _ := by ring

theorem normalized_common_energy_allocation (D : OriginalData ι)
    (hS : ∀ i,∀ I∈D.S i,I≠0) (hp : ∀ i,∀ I∈D.S (Sum.inl i),Prime I)
    (C : Ideal O) (hC : Supported C) (hseed : D.s∣C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K)
    (hW : ∀ z : O,0≤(W (‖ringComplex z‖^2/K)).re)
    (hX₁ : 0< D.X₁) (hX₂ : 0< D.X₂) (hB₁ : D.B₁≠0) (hB₂ : D.B₂≠0)
    (hP : ∀ i,0< D.lengths i) :
    commonEnergy D C hC τ t L W K / rawVolume D ≤
      ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        (‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2/rawReduction B.val D.lengths) *
          (allocatedEnergy D C L B τ t W K/rawVolume (allocatedData D C L B)) := by
  have hV := rawVolume_pos D hX₁ hX₂ hB₁ hB₂ hP
  have he := div_le_div_of_nonneg_right
    (common_energy_allocation D hS hp C hC hseed τ t L W K hK hW) hV.le
  apply he.trans_eq
  rw [mul_div_assoc,Finset.sum_div]
  apply congrArg (fun x : ℝ => ((actualAllocations D.S C).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  have hR := rawReduction_pos B.val
    (allocation_data D.S C B.val (Finset.mem_filter.mp B.property).1).1 D.lengths hP
  rw [allocated_rawVolume D C L B hB₁ hB₂ hP]
  field_simp

theorem normalized_common_energy_bound (N : ℕ) (a b : ℝ) (ha : 0< a)
    (D : OriginalData ι) (hcard : Fintype.card ι≤ N)
    (hS : ∀ i,∀ I∈D.S i,I≠0) (hp : ∀ i,∀ I∈D.S (Sum.inl i),Prime I)
    (C : Ideal O) (hC : Supported C) (hseed : D.s∣C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K)
    (hW : ∀ z : O,0≤(W (‖ringComplex z‖^2/K)).re)
    (hX₁ : 0< D.X₁) (hX₂ : 0< D.X₂) (hB₁ : D.B₁≠0) (hB₂ : D.B₂≠0)
    (hP : ∀ i,0< D.lengths i) (M : ι → ℝ) (hM : ∀ i,0≤ M i)
    (hν : ∀ i I,‖D.nu i I‖≤1) (hWnorm : ∀ i x,‖D.slot i x‖≤ M i)
    (hslot : ∀ i,Function.support (D.slot i)⊆Set.Icc a b) :
    commonEnergy D C hC τ t L W K / rawVolume D ≤
      (max 1 b)^N * ((actualAllocations D.S C).card:ℝ)/(Ideal.absNorm C:ℝ) *
        ∑ B : actualAllocations D.S C, (frozenControl B.val M)^2 *
          (allocatedEnergy D C L B τ t W K/rawVolume (allocatedData D C L B)) := by
  apply (normalized_common_energy_allocation D hS hp C hC hseed τ t L W K hK hW
    hX₁ hX₂ hB₁ hB₂ hP).trans
  calc
    _ ≤ ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        ((max 1 b)^N/(Ideal.absNorm C:ℝ)*(frozenControl B.val M)^2) *
          (allocatedEnergy D C L B τ t W K/rawVolume (allocatedData D C L B)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      have hVa : 0< rawVolume (allocatedData D C L B) := by
        rw [allocated_rawVolume D C L B hB₁ hB₂ hP]
        exact div_pos (rawVolume_pos D hX₁ hX₂ hB₁ hB₂ hP)
          (rawReduction_pos B.val (allocation_data D.S C B.val (Finset.mem_filter.mp B.property).1).1 D.lengths hP)
      exact mul_le_mul_of_nonneg_right
        (frozen_normalized_bound N a b ha D hcard C hC.1 B M hM hP hν hWnorm hslot)
        (div_nonneg (allocated_nonneg D C L B τ t W K hK hW) hVa.le)
    _ = _ := by
      simp only [mul_assoc,← Finset.mul_sum]
      ring

theorem normalized_common_as_tsum (D : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hV : 0< rawVolume D) :
    (∑' z : O, ‖(Real.sqrt (rawVolume D):ℂ)⁻¹ * commonGauss D C hC τ t L z‖^2 *
      (W (‖ringComplex z‖^2/K)).re) =
      commonEnergy D C hC τ t L W K/rawVolume D := by
  have hn (z : O) : ‖(Real.sqrt (rawVolume D):ℂ)⁻¹ * commonGauss D C hC τ t L z‖^2 =
      ‖commonGauss D C hC τ t L z‖^2/rawVolume D := by
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow,inv_pow,Real.sq_sqrt hV.le]
    ring
  simp_rw [hn,div_mul_eq_mul_div]
  exact tsum_div_const

theorem allocated_sum_hasSum (D : OriginalData ι) (C L : Ideal O)
    (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) :
    HasSum (fun z : O => ∑ B : actualAllocations D.S C,
      ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 *
        (‖gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z‖^2 *
        (W (‖ringComplex z‖^2/K)).re))
      (∑ B : actualAllocations D.S C,
        ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 * allocatedEnergy D C L B τ t W K) := by
  exact hasSum_sum (fun B _ => (allocated_hasSum D C L B τ t W K hK).mul_left _)

theorem original_radial_bound (N : ℕ) (a b : ℝ) (ha : 0< a) :
    ∃ F : ℝ,0< F ∧ ∀ {κ : Type*} [Fintype κ],∀ D : OriginalData κ,
      Fintype.card κ≤ N →
      (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
      ∀ (C : Ideal O) (hC : Supported C), D.s∣C →
      ∀ (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K T : ℝ),
      0< K → (∀ z : O,0≤(W (‖ringComplex z‖^2/K)).re) →
      0< D.X₁ → 0< D.X₂ → D.B₁≠0 → D.B₂≠0 →
      (∀ i,0< D.lengths i) → D.X₁*D.X₂=T → D.Y₁*D.Y₂=T →
      ∀ M : κ → ℝ,(∀ i,0≤ M i) → (∀ i I,‖D.nu i I‖≤1) →
      (∀ i x,‖D.slot i x‖≤ M i) →
      (∀ i,Function.support (D.slot i)⊆Set.Icc a b) →
      (∑' z : O,
        ‖(Real.sqrt ((T/((Ideal.absNorm D.B₁:ℝ)*Ideal.absNorm D.B₂))*∏ i,D.lengths i):ℂ)⁻¹ *
          commonGauss D C hC τ t L z‖^2 * (W (‖ringComplex z‖^2/K)).re) ≤
        F*((actualAllocations D.S C).card:ℝ)/(Ideal.absNorm C:ℝ) *
          ∑ B : actualAllocations D.S C,(frozenControl B.val M)^2 *
            (allocatedEnergy D C L B τ t W K/rawVolume (allocatedData D C L B)) := by
  refine ⟨(max 1 b)^N,pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _,?_⟩
  intro κ _ D hcard hS hp C hC hseed τ t L W K T hK hW hX₁ hX₂ hB₁ hB₂ hP hX hY M hM hν hWnorm hslot
  rw [← (rawVolume_both D T hX hY).1,
    normalized_common_as_tsum D C hC τ t L W K (rawVolume_pos D hX₁ hX₂ hB₁ hB₂ hP)]
  exact normalized_common_energy_bound N a b ha D hcard hS hp C hC hseed τ t L W K hK hW
    hX₁ hX₂ hB₁ hB₂ hP M hM hν hWnorm hslot

end CenteredMomentFirstAllocationGaussEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstMaskedInput
open HeckeFamily CanonicalQuadraticSieve 
open CenteredMomentFirstMaskedFamily CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentAmplificationLiveMask
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentRemainingBox
open CenteredMomentSourceLiveColumn CenteredMomentSecondHeightFamily
open CenteredMomentOriginalChildEnergy CenteredMomentHeckeColumnWindow
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

lemma profile_combined_mask (R T seed : Ideal O) (ν : ι→Ideal O→ℂ)
    (Wslot : ι→ℝ→ℂ) (P : ι→ℝ) (W₁ W₂ : ℝ→ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (v : Tuple ι) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed v *
      idealMask (cubicIdealGenerator T) (finiteTupleProduct v) =
    profileCoefficient (R*T) ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed v := by
  rw [idealMask_generator]
  simp only [profileCoefficient, IsCoprime.mul_right_iff]
  split_ifs <;> simp_all

lemma column_combined_mask (S : Finset (Tuple ι)) (R T seed : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ) (W₁ W₂ : ℝ→ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    maskedSource (cubicIdealGenerator T)
      (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed)) =
    finiteColumnCoefficient S (profileCoefficient (R*T) ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed) := by
  funext I
  unfold maskedSource finiteColumnCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  rw [←(Finset.mem_filter.mp hv).2]
  exact profile_combined_mask R T seed ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v

lemma input_combined_mask (s : Input ι) (R T seed : Ideal O) :
    maskedSource (cubicIdealGenerator T) (original s R seed).beta =
      (original s (R*T) seed).beta := by
  simpa only [OriginalData.beta, OriginalData.profile, original] using
    column_combined_mask (Fintype.piFinset s.pools) R T seed s.ν s.W s.P
      s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1

lemma extracted_input (s : Input ι) (η : Character) (R T seed C : Ideal O)
    (hC : Supported C) (t : ℝ) (I : Ideal O) :
    extractedSource η (cubicIdealGenerator T) C (original s R seed).beta t I =
      (original s (R*T) seed).beta (C*I) * rowWeight η fixedBadMask 1 1 t C := by
  rw [extractedSource_whole_mask η (cubicIdealGenerator T) C hC, input_combined_mask]
  rfl

theorem extracted_input_allocations (s : Input ι) (η τ : Character)
    (R T seed C I : Ideal O) (hC : Supported C) (hI : I≠0)
    (hseed : IsCoprime seed C) (t : ℝ) :
    (if IsCoprime C I then
      extractedSource η (cubicIdealGenerator T) C (original s R seed).beta t I else 0) =
    rowWeight η fixedBadMask 1 1 t C *
      ∑ B : actualAllocations s.pools C,
        frozenCoefficient B C (R*T) s.ν s.W s.P *
          (original (child s C (R*T) B τ t) ((R*T)*C) seed).beta I := by
  have hh := original_masked_live_column s.pools s.pools_ne
    (fun i J hJ => s.prime i J hJ) C (R*T) seed I hC.1 hI hseed
    s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1
  rw [extracted_input s η R T seed C hC t I]
  calc
    _ = rowWeight η fixedBadMask 1 1 t C *
        (if IsCoprime C I then (original s (R*T) seed).beta (C*I) else 0) := by
      split_ifs <;> ring
    _ = rowWeight η fixedBadMask 1 1 t C *
        ∑ B : actualAllocations s.pools C, frozenCoefficient B C (R*T) s.ν s.W s.P *
          finiteColumnCoefficient
            (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)
            (maskedLiveProfile B C (R*T) seed s.ν s.W s.P s.W₁ s.W₂
              s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1) I := by
      exact congrArg (fun z : ℂ => rowWeight η fixedBadMask 1 1 t C * z) hh
    _ = _ := by
      apply congrArg (fun z : ℂ => rowWeight η fixedBadMask 1 1 t C * z)
      apply Finset.sum_congr rfl
      intro B _
      exact congrArg (fun z : ℂ => frozenCoefficient B C (R*T) s.ν s.W s.P * z)
        (congrFun (child_columns s C (R*T) seed B τ t).2 I)

lemma normalized_input_mask (s : Input ι) (R T seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (sourceGaussEnergy (original s R seed).columns
      (maskedSource (cubicIdealGenerator T) (original s R seed).beta)
      (heightCoeff s.η s.t) W K).re / volume s =
      normalizedGaussSource s (R*T) seed W K := by
  rw [input_combined_mask]
  rfl

lemma child_input_combined_mask (s : Input ι) (C R T seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    maskedSource (cubicIdealGenerator T)
      (original (child s C R B τ t) (R*C) seed).beta =
      (original (child s C (R*T) B τ t) ((R*T)*C) seed).beta := by
  rw [input_combined_mask]
  simp only [OriginalData.beta, OriginalData.profile, original, child, commonData, Input.pools,
    mul_assoc, mul_comm C T]

lemma normalized_child_mask (s : Input ι) (C R T seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (sourceGaussEnergy (original (child s C R B τ t) (R*C) seed).columns
      (maskedSource (cubicIdealGenerator T)
        (original (child s C R B τ t) (R*C) seed).beta)
      (heightCoeff τ t) W K).re / volume (child s C R B τ t) =
      childNormalizedGaussSource s C (R*T) seed B τ t W K := by
  have hcolumns :
      (original (child s C R B τ t) (R*C) seed).columns =
        (original (child s C (R*T) B τ t) ((R*T)*C) seed).columns :=
    (child_columns s C R seed B τ t).1.symm.trans (child_columns s C (R*T) seed B τ t).1
  have hvolume : volume (child s C R B τ t) = volume (child s C (R*T) B τ t) := by
    simp only [CenteredMomentAmplificationChildInput.volume, child, commonData]
  unfold childNormalizedGaussSource normalizedGaussSource
  rw [child_input_combined_mask, hcolumns, hvolume, child_character, child_height]

end CenteredMomentFirstMaskedInput

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstPhysicalSource
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow 
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentOriginalChildEnergy
open CenteredMomentSmoothedWindowEnergy CenteredMomentGaussEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentAddedZeroUniform
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]
local instance firstAllocatedInputDecidableEq {κ : Type*} : DecidableEq κ := Classical.decEq _

lemma commonEnergy_real (D : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) :
    (commonEnergy D C hC τ t L W K).re =
      CenteredMomentFirstAllocationGaussEnergy.commonEnergy D C hC τ t L W K := by
  exact (gaussEnergy_hasSum_re Finset.univ
    (sourceGenerator (CenteredMomentFirstSectors.residualPool C hC.1 D.columns))
    (sourceGenerator_supported _) _ W K hK).tsum_eq.symm

lemma original_rawVolume (s : Input ι) (R seed : Ideal O) :
    CenteredMomentFirstAllocationGaussEnergy.rawVolume (original s R seed)=volume s := by
  simp [CenteredMomentFirstAllocationGaussEnergy.rawVolume,original,CenteredMomentAmplificationChildInput.volume]

lemma allocated_input_columns (s : Input ι) (C R seed L : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    (allocatedData (original s R seed) C L B).columns=
      (original (child s C R B τ t) (R*C) L).columns ∧
    (allocatedData (original s R seed) C L B).beta=
      (original (child s C R B τ t) (R*C) L).beta := by
  have hh := child_columns s C R L B τ t
  simpa only [OriginalData.columns,OriginalData.beta,allocated_pools,allocated_profile,original] using hh

lemma allocated_input_volume (s : Input ι) (C R seed L : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    CenteredMomentFirstAllocationGaussEnergy.rawVolume (allocatedData (original s R seed) C L B)=
      volume (child s C R B τ t) := by
  simp only [CenteredMomentFirstAllocationGaussEnergy.rawVolume,allocatedData,original,
    CenteredMomentAmplificationChildInput.volume,child,commonData,one_mul,div_mul_div_comm]

lemma allocated_input_energy (s : Input ι) (C R seed L : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    CenteredMomentFirstAllocationGaussEnergy.allocatedEnergy (original s R seed) C L B τ t W K /
      CenteredMomentFirstAllocationGaussEnergy.rawVolume (allocatedData (original s R seed) C L B)=
      childNormalizedGaussSource s C R L B τ t W K := by
  obtain ⟨hc,hb⟩ := allocated_input_columns s C R seed L B τ t
  unfold CenteredMomentFirstAllocationGaussEnergy.allocatedEnergy
  rw [hc,hb,allocated_input_volume s C R seed L B τ t]
  rfl

theorem common_energy_allocated_inputs (N : ℕ) (a b : ℝ) (ha : 0< a)
    (s : Input ι) (hcard : Fintype.card ι≤ N) (haS : a≤ s.lower) (hbS : s.upper≤ b)
    (C R seed : Ideal O) (hC : Supported C) (hseed : seed∣C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K)
    (hW : ∀z : O,0≤(W (‖ringComplex z‖^2/K)).re) :
    (commonEnergy (original s R seed) C hC τ t L W K).re / volume s ≤
      (max 1 b)^N * ((actualAllocations s.pools C).card:ℝ)/(Ideal.absNorm C:ℝ) *
        ∑B : actualAllocations s.pools C,
          (CenteredMomentFirstAllocationGaussEnergy.frozenControl B.val s.M)^2 *
            childNormalizedGaussSource s C R L B τ t W K := by
  have hh := CenteredMomentFirstAllocationGaussEnergy.normalized_common_energy_bound N a b ha
    (original s R seed) hcard s.pools_ne s.prime C hC hseed τ t L W K hK hW
    s.X₁_pos s.X₂_pos one_ne_zero one_ne_zero s.P_pos s.M
    (fun i=> zero_le_one.trans (s.M_ge_one i)) s.ν_bound s.W_bound
    (fun i x hx=>⟨haS.trans (s.slot_support i hx).1,(s.slot_support i hx).2.trans hbS⟩)
  rw [← commonEnergy_real _ _ _ _ _ _ _ _ hK,original_rawVolume] at hh
  change (commonEnergy (original s R seed) C hC τ t L W K).re / volume s ≤
    (max 1 b)^N * ((actualAllocations s.pools C).card:ℝ)/(Ideal.absNorm C:ℝ) *
      ∑B : actualAllocations s.pools C,
        (CenteredMomentFirstAllocationGaussEnergy.frozenControl B.val s.M)^2 *
          (CenteredMomentFirstAllocationGaussEnergy.allocatedEnergy (original s R seed) C L B τ t W K /
            CenteredMomentFirstAllocationGaussEnergy.rawVolume (allocatedData (original s R seed) C L B)) at hh
  simpa only [allocated_input_energy] using hh

lemma allocated_input_masked_energy (s : Input ι) (C R T seed L : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    CenteredMomentFirstAllocationGaussEnergy.allocatedEnergy (original s (R*T) seed) C L B τ t W K /
      CenteredMomentFirstAllocationGaussEnergy.rawVolume (allocatedData (original s (R*T) seed) C L B)=
    (sourceGaussEnergy (original (child s C R B τ t) (R*C) L).columns
      (CenteredMomentFirstMaskedFamily.maskedSource (cubicIdealGenerator T)
        (original (child s C R B τ t) (R*C) L).beta)
      (heightCoeff τ t) W K).re / volume (child s C R B τ t) := by
  rw [allocated_input_energy,CenteredMomentFirstMaskedInput.normalized_child_mask]

end CenteredMomentFirstPhysicalSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstPhysicalSource
open CenteredMomentFirstAllocationGaussEnergy CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentSourceMass
open CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]
local instance firstAllocationControlDecidableEq {κ : Type*} : DecidableEq κ := Classical.decEq _

lemma frozen_live_control (B : Tuple ι) (M : ι→ℝ) :
    frozenControl B M * (∏i : liveIndices B,M i.val) = ∏i,M i := by
  rw [Finset.prod_coe_sort (liveIndices B) M]
  unfold frozenControl liveIndices
  rw [mul_comm]
  exact Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i=> B (Sum.inl i)=1) M

lemma frozen_child_control (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : HeckeFamily.Character) (t : ℝ) :
    (frozenControl B.val s.M)^2 * (∏i,(child s C R B τ t).M i)^2 = (∏i,s.M i)^2 := by
  rw [←mul_pow]
  exact congrArg (fun x:ℝ=> x^2) (frozen_live_control B.val s.M)

lemma allocated_control_sum (s : Input ι) (C R : Ideal O)
    (τ : HeckeFamily.Character) (t : ℝ) :
    (∑B : actualAllocations s.pools C,
      (frozenControl B.val s.M)^2 * (∏i,(child s C R B τ t).M i)^2) =
      ((actualAllocations s.pools C).card:ℝ) * (∏i,s.M i)^2 := by
  simp only [frozen_child_control,Finset.sum_const,Finset.card_univ,Fintype.card_coe,
    nsmul_eq_mul]

theorem allocated_control_mass (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃D : ℝ,0< D ∧ ∀{κ : Type*}[Fintype κ],Fintype.card κ≤ N →
      ∀(s : Input κ)(C R : Ideal O),C≠0 →
      ∀(τ : HeckeFamily.Character)(t : ℝ),
        ((actualAllocations s.pools C).card:ℝ)/(Ideal.absNorm C:ℝ) *
          (∑B : actualAllocations s.pools C,
            (frozenControl B.val s.M)^2 * (∏i,(child s C R B τ t).M i)^2) ≤
          D*(Ideal.absNorm C:ℝ)^(ε-1)*(∏i,s.M i)^2 := by
  obtain ⟨D,hD,hcard⟩ := CenteredMomentAllocationCost.actualAllocations_uniform_small_power
    (N+2) (ε/2) (half_pos hε)
  refine ⟨D^2,sq_pos_of_pos hD,?_⟩
  intro κ _ hn s C R hC τ t
  have hN : (0:ℝ)< Ideal.absNorm C := CenteredMomentFirstScale.norm_pos C hC
  have hh := hcard (ι:=κ⊕Fin 2) (by simp only [Fintype.card_sum,Fintype.card_fin];omega)
    s.pools C hC
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (actualAllocations s.pools C).card) hh 2
  rw [mul_pow,←Real.rpow_mul_natCast hN.le,show ε/2*(2:ℕ)=ε by norm_num] at hs
  rw [allocated_control_sum]
  calc
    _ = (((actualAllocations s.pools C).card:ℝ)^2/(Ideal.absNorm C:ℝ)) * (∏i,s.M i)^2 := by ring
    _ ≤ (D^2*(Ideal.absNorm C:ℝ)^ε/(Ideal.absNorm C:ℝ)) * (∏i,s.M i)^2 :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hs hN.le) (sq_nonneg _)
    _ = _ := by rw [Real.rpow_sub hN,Real.rpow_one];ring

end CenteredMomentFirstPhysicalSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstCommonSourceBudget
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonAllocationSum
open CenteredMomentCommonRawScale CenteredMomentSourceLiveColumn CenteredMomentFirstAllocationGaussEnergy
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

lemma child_nonneg (s:Input ι)(C R seed:Ideal O)(B:actualAllocations s.pools C)
    (τ:Character)(t:ℝ)(W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0< K)
    (hW:∀z:O,0≤(W (‖ringComplex z‖^2/K)).re):
    0≤ childNormalizedGaussSource s C R seed B τ t W K:=by
  rw [←allocated_input_energy s C R seed seed B τ t W K]
  apply div_nonneg
  · exact allocated_nonneg (original s R seed) C seed B τ t W K hK hW
  · rw [allocated_input_volume s C R seed seed B τ t]
    exact (CenteredMomentAmplificationChildInput.volume_pos _).le

theorem common_energy_live_allocations (N:ℕ)(a b:ℝ)(ha:0< a)
    (s:Input ι)(hcard:Fintype.card ι≤ N)(haS:a≤ s.lower)(hbS:s.upper≤ b)
    (C R seed:Ideal O)(hC:Supported C)(hseed:seed∣C)
    (τ:Character)(t:ℝ)(L:Ideal O)(W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0< K)
    (hW:∀z:O,0≤(W (‖ringComplex z‖^2/K)).re):
    (CenteredMomentFirstPhysicalSource.commonEnergy (original s R seed) C hC τ t L W K).re/
      CenteredMomentAmplificationChildInput.volume s≤
    (max 1 b)^N*((actualAllocations s.pools C).card:ℝ)/(C.absNorm:ℝ)*
      ∑B:actualAllocations s.pools C,
        if frozenCoefficient B.val C R s.ν s.W s.P≠0 then
          (frozenControl B.val s.M)^2*childNormalizedGaussSource s C R L B τ t W K
        else 0:=by
  have hh:=normalized_common_energy_allocation (original s R seed) s.pools_ne s.prime C hC hseed
    τ t L W K hK hW s.X₁_pos s.X₂_pos one_ne_zero one_ne_zero s.P_pos
  rw [←commonEnergy_real _ _ _ _ _ _ _ _ hK,original_rawVolume] at hh
  change _ ≤ ((actualAllocations s.pools C).card:ℝ)*
    ∑B:actualAllocations s.pools C,
      (‖frozenCoefficient B.val C R s.ν s.W s.P‖^2/rawReduction B.val s.P)*
        (allocatedEnergy (original s R seed) C L B τ t W K/
          rawVolume (allocatedData (original s R seed) C L B)) at hh
  simp_rw [allocated_input_energy s C R seed L _ τ t W K] at hh
  apply hh.trans
  calc
    _≤((actualAllocations s.pools C).card:ℝ)*
      ∑B:actualAllocations s.pools C,
        ((max 1 b)^N/(C.absNorm:ℝ))*
          (if frozenCoefficient B.val C R s.ν s.W s.P≠0 then
            (frozenControl B.val s.M)^2*childNormalizedGaussSource s C R L B τ t W K
          else 0):=by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      by_cases hz:frozenCoefficient B.val C R s.ν s.W s.P=0
      · simp only [hz,ne_eq,not_true_eq_false,ite_false,norm_zero,zero_pow (by decide:2≠0),zero_div,zero_mul,mul_zero]
        exact le_rfl
      · rw [if_pos hz]
        have hf:=frozen_normalized_bound N a b ha (original s R seed) hcard C hC.1 B s.M
          (fun i=> zero_le_one.trans (s.M_ge_one i)) s.P_pos s.ν_bound s.W_bound
          (fun i x hx=>⟨haS.trans (s.slot_support i hx).1,(s.slot_support i hx).2.trans hbS⟩)
        have hn:=child_nonneg s C R L B τ t W K hK hW
        change ‖frozenCoefficient B.val C R s.ν s.W s.P‖^2/rawReduction B.val s.P≤
          (max 1 b)^N/(C.absNorm:ℝ)*(frozenControl B.val s.M)^2 at hf
        convert mul_le_mul_of_nonneg_right hf hn using 1 <;> first | rfl | ring
    _=_:=by rw [←Finset.mul_sum];ring

theorem common_energy_from_live_children (N:ℕ)(a b ε:ℝ)(ha:0< a)(hε:0<ε):
    ∃Cbound:ℝ,0< Cbound ∧ ∀{κ:Type*}[Fintype κ],∀s:Input κ,
    Fintype.card κ≤ N → a≤ s.lower → s.upper≤ b →
    ∀(C R seed:Ideal O)(hC:Supported C),seed∣C →
    ∀(τ:Character)(t:ℝ)(L:Ideal O)(W:𝓢(ℝ,ℂ))(K E:ℝ),0< K → 0≤ E →
    (∀z:O,0≤(W (‖ringComplex z‖^2/K)).re)→
    (∀B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0 →
      childNormalizedGaussSource s C R L B τ t W K≤ E*(∏i,(child s C R B τ t).M i)^2)→
    (CenteredMomentFirstPhysicalSource.commonEnergy (original s R seed) C hC τ t L W K).re/
      CenteredMomentAmplificationChildInput.volume s≤
        Cbound*(C.absNorm:ℝ)^(ε-1)*E*(∏i,s.M i)^2:=by
  obtain ⟨D,hD,hmass⟩:=allocated_control_mass N ε hε
  refine ⟨(max 1 b)^N*D,mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _) hD,?_⟩
  intro κ _ s hcard haS hbS C R seed hC hseed τ t L W K E hK hE hW hchild
  have hh:=common_energy_live_allocations N a b ha s hcard haS hbS C R seed hC hseed τ t L W K hK hW
  apply hh.trans
  have hc:0≤(max 1 b)^N*((actualAllocations s.pools C).card:ℝ)/(C.absNorm:ℝ):=by positivity
  have hs:(∑B:actualAllocations s.pools C,
      if frozenCoefficient B.val C R s.ν s.W s.P≠0 then
        (frozenControl B.val s.M)^2*childNormalizedGaussSource s C R L B τ t W K else 0)≤
      E*∑B:actualAllocations s.pools C,(frozenControl B.val s.M)^2*(∏i,(child s C R B τ t).M i)^2:=by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro B hB
    split_ifs with hb
    · convert mul_le_mul_of_nonneg_left (hchild B hb) (sq_nonneg (frozenControl B.val s.M)) using 1 <;> first | rfl | ring
    · positivity
  have hm:=hmass hcard s C R hC.1 τ t
  calc
    _≤((max 1 b)^N*((actualAllocations s.pools C).card:ℝ)/(C.absNorm:ℝ))*
        (E*∑B:actualAllocations s.pools C,(frozenControl B.val s.M)^2*(∏i,(child s C R B τ t).M i)^2):=
      mul_le_mul_of_nonneg_left hs hc
    _=((max 1 b)^N*E)*(((actualAllocations s.pools C).card:ℝ)/(C.absNorm:ℝ)*
        ∑B:actualAllocations s.pools C,(frozenControl B.val s.M)^2*(∏i,(child s C R B τ t).M i)^2):=by ring
    _≤((max 1 b)^N*E)*(D*(C.absNorm:ℝ)^(ε-1)*(∏i,s.M i)^2):=
      mul_le_mul_of_nonneg_left hm (mul_nonneg (by positivity) hE)
    _=_:=by ring

end CenteredMomentFirstCommonSourceBudget

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstCommonSourcePowerBudget
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentFirstCommonSourceBudget
local notation "O"=> Eisenstein.O
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

theorem common_energy_power_budget (N:ℕ)(a b ε:ℝ)(ha:0< a)(hb:1≤ b)(hε:0<ε):
    ∃Cbound:ℝ,0< Cbound ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤ N → a≤ s.lower → s.upper≤ b →
    ∀(C R seed:Ideal O)(hC:Supported C),seed∣C →
    ∀(τ:Character)(t:ℝ)(L:Ideal O)(W:𝓢(ℝ,ℂ))(K:ℝ),0< K →
    (∀z:O,0≤(W (‖ringComplex z‖^2/K)).re)→
    ∀(n:ℕ)(E α:Fin n→ℝ),(∀j,0≤ E j)→(∀j,0≤α j)→
    (∀B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0 →
      childNormalizedGaussSource s C R L B τ t W K≤
        (∑j,E j*(CenteredMomentAmplificationChildInput.volume (child s C R B τ t))^(α j))*
          (∏i,(child s C R B τ t).M i)^2)→
    (CenteredMomentFirstPhysicalSource.commonEnergy (original s R seed) C hC τ t L W K).re/
      CenteredMomentAmplificationChildInput.volume s≤
        Cbound*(C.absNorm:ℝ)^(ε-1)*
          (∑j,E j*(b^N*CenteredMomentAmplificationChildInput.volume s/(C.absNorm:ℝ))^(α j))*
            (∏i,s.M i)^2:=by
  obtain ⟨Cbound,hCbound,hbound⟩:=common_energy_from_live_children N a b ε ha hε
  refine ⟨Cbound,hCbound,?_⟩
  intro ι _ s hcard haS hbS C R seed hC hseed τ t L W K hK hW n E α hE hα hchild
  have hv:=CenteredMomentAmplificationChildInput.volume_pos s
  have hn:=CenteredMomentFirstScale.norm_pos C hC.1
  apply hbound s hcard haS hbS C R seed hC hseed τ t L W K _ hK
    (Finset.sum_nonneg (fun j _=> mul_nonneg (hE j) (Real.rpow_nonneg (by positivity) _))) hW
  intro B hB
  apply (hchild B hB).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (hE j)
  exact Real.rpow_le_rpow (CenteredMomentAmplificationChildInput.volume_pos _).le
    (CenteredMomentAmplificationChildSourceCaps.common_volume_le N b hb s hcard hbS C R B τ t hB) (hα j)

theorem common_energy_linear_volume (N:ℕ)(a b ε:ℝ)(ha:0< a)(hb:1≤ b)(hε:0<ε):
    ∃Cbound:ℝ,0< Cbound ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤ N → a≤ s.lower → s.upper≤ b →
    ∀(C R seed:Ideal O)(hC:Supported C),seed∣C →
    ∀(τ:Character)(t:ℝ)(L:Ideal O)(W:𝓢(ℝ,ℂ))(K E:ℝ),0< K → 0≤ E →
    (∀z:O,0≤(W (‖ringComplex z‖^2/K)).re)→
    (∀B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0 →
      childNormalizedGaussSource s C R L B τ t W K≤
        E*CenteredMomentAmplificationChildInput.volume (child s C R B τ t)*
          (∏i,(child s C R B τ t).M i)^2)→
    (CenteredMomentFirstPhysicalSource.commonEnergy (original s R seed) C hC τ t L W K).re/
      CenteredMomentAmplificationChildInput.volume s≤
        Cbound*(C.absNorm:ℝ)^(ε-2)*CenteredMomentAmplificationChildInput.volume s*E*(∏i,s.M i)^2:=by
  obtain ⟨Cbound,hCbound,hbound⟩:=common_energy_from_live_children N a b ε ha hε
  refine ⟨Cbound*b^N,mul_pos hCbound (pow_pos (zero_lt_one.trans_le hb) _),?_⟩
  intro ι _ s hcard haS hbS C R seed hC hseed τ t L W K E hK hE hW hchild
  have hv:=CenteredMomentAmplificationChildInput.volume_pos s
  have hn:=CenteredMomentFirstScale.norm_pos C hC.1
  have hh:=hbound s hcard haS hbS C R seed hC hseed τ t L W K
    (E*(b^N*CenteredMomentAmplificationChildInput.volume s/(C.absNorm:ℝ))) hK
    (mul_nonneg hE (by positivity)) hW (fun B hB=> by
      apply (hchild B hB).trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (CenteredMomentAmplificationChildSourceCaps.common_volume_le N b hb s hcard hbS C R B τ t hB) hE)
        (sq_nonneg _))
  apply hh.trans_eq
  have hp:(C.absNorm:ℝ)^(ε-2)=(C.absNorm:ℝ)^(ε-1)/(C.absNorm:ℝ):=by
    rw [show ε-2=(ε-1)-1 by ring,Real.rpow_sub hn,Real.rpow_one]
  rw [hp]
  ring

end CenteredMomentFirstCommonSourcePowerBudget

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstCommonReferencePower
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentFirstCommonSourceBudget
open CenteredMomentFirstCommonSourcePowerBudget
local notation "O"=> Eisenstein.O
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

def normalizedPower (b V C q Z allowance ε E:ℝ)(N:ℕ)(α:ℝ):ℝ:=
  C ^ ε*(b^N)^α*E/q*(V/C)^(α-1)*Z^(-allowance)

lemma normalizedPower_nonneg (b V C q Z allowance ε E:ℝ)(N:ℕ)(α:ℝ)
    (hb:0≤ b)(hV:0≤ V)(hC:0≤ C)(hq:0≤ q)(hZ:0≤ Z)(hE:0≤ E):
    0≤ normalizedPower b V C q Z allowance ε E N α:=by
  unfold normalizedPower
  positivity

lemma reference_power_identity (b V C q Z allowance ε E:ℝ)(N:ℕ)(α:ℝ)
    (hb:0< b)(hV:0< V)(hC:0< C)(hq:0< q)(hZ:0< Z):
    (q*(V/C)^2*Z^allowance)*normalizedPower b V C q Z allowance ε E N α=
      C ^ (ε-1)*V*E*(b^N*V/C)^α:=by
  have hx:0< V/C:=div_pos hV hC
  have hbN:0< b^N:=pow_pos hb N
  have hprod:Z^allowance*Z^(-allowance)=1:=by
    rw [←Real.rpow_add hZ,add_neg_cancel,Real.rpow_zero]
  unfold normalizedPower
  rw [Real.rpow_sub hx,Real.rpow_one,Real.rpow_sub hC,Real.rpow_one,
    show b^N*V/C=b^N*(V/C) by ring,Real.mul_rpow hbN.le hx.le]
  field_simp
  calc
    _ = E*(Z^allowance*Z^(-allowance)):=by ring
    _ = E:=by rw [hprod,mul_one]

theorem common_energy_reference_powers (N:ℕ)(a b ε:ℝ)(ha:0< a)(hb:1≤ b)(hε:0<ε):
    ∃Cb:ℝ,0< Cb ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤ N→a≤ s.lower→s.upper≤ b→
    ∀(C R seed:Ideal O)(hC:Supported C),seed∣C→
    ∀(τ:Character)(t:ℝ)(L:Ideal O)(W:𝓢(ℝ,ℂ))(K Z allowance:ℝ),0< K→0< Z→
    (∀z:O,0≤(W (‖ringComplex z‖^2/K)).re)→
    ∀(n:ℕ)(E α:Fin n→ℝ),(∀j,0≤ E j)→(∀j,0≤α j)→
    (∀B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0→
      childNormalizedGaussSource s C R L B τ t W K≤
        (∑j,E j*(volume (child s C R B τ t))^(α j))*(∏i,(child s C R B τ t).M i)^2)→
    (commonEnergy (original s R seed) C hC τ t L W K).re≤
      ((τ.modulus.absNorm:ℝ)*(volume s/(C.absNorm:ℝ))^2*Z^allowance)*
        (Cb*(∏i,s.M i)^2*∑j,normalizedPower b (volume s) (C.absNorm:ℝ)
          (τ.modulus.absNorm:ℝ) Z allowance ε (E j) N (α j)):=by
  obtain ⟨Cb,hCb,hbound⟩:=common_energy_power_budget N a b ε ha hb hε
  refine ⟨Cb,hCb,?_⟩
  intro ι _ s hc hlo hhi C R seed hC hseed τ t L W K Z allowance hK hZ hW n E α hE hα hchild
  have hV:=volume_pos s
  have hNC:=CenteredMomentFirstScale.norm_pos C hC.1
  have hq:=CenteredMomentFirstScale.norm_pos τ.modulus τ.modulus_ne_bot
  have hh:=hbound s hc hlo hhi C R seed hC hseed τ t L W K hK hW n E α hE hα hchild
  have hh':=(div_le_iff₀ hV).mp hh
  apply hh'.trans_eq
  calc
    _ = Cb*(∏i,s.M i)^2*∑j,(C.absNorm:ℝ)^(ε-1)*CenteredMomentAmplificationChildInput.volume s*E j*
        (b^N*CenteredMomentAmplificationChildInput.volume s/(C.absNorm:ℝ))^(α j):=by
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = Cb*(∏i,s.M i)^2*∑j,
        ((τ.modulus.absNorm:ℝ)*(CenteredMomentAmplificationChildInput.volume s/(C.absNorm:ℝ))^2*Z^allowance)*
          normalizedPower b (CenteredMomentAmplificationChildInput.volume s) (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ)
            Z allowance ε (E j) N (α j):=by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact (reference_power_identity b (CenteredMomentAmplificationChildInput.volume s) (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ)
        Z allowance ε (E j) N (α j) (zero_lt_one.trans_le hb) hV hNC hq hZ).symm
    _ = _:=by rw [←Finset.mul_sum];ring

end CenteredMomentFirstCommonReferencePower

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

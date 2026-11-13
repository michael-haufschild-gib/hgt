/-
Common radial data adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.SourceRectangles

/-!
# Common radial data

Inputs of the common radial data with pools, slot supports and allocation norms; restricted
source energies, raw reductions of the common scale and source-rectangle heights.
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
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentRestrictedSource
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentRowNorm
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedWindow CenteredMomentRestrictedDomain
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
open CenteredMomentOriginalChildEnergy
local notation "O" => Eisenstein.O

theorem rowPolynomial_allocation {α γ : Type*} [Fintype γ]
    (S : Finset α) (a : α → O) (b : γ → ℂ) (d : γ → α → ℂ) (z : O) :
    rowPolynomial S a (fun i => ∑ B,b B*d B i) z=
      ∑ B,b B*rowPolynomial S a (d B) z := by
  simp only [rowPolynomial,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm

def sourceRestrictedEnergy (keep : O → Prop) (Q : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  restrictedEnergy keep Finset.univ (sourceGenerator Q)
    (fun I : supportedColumns Q => c I*f I) W K

theorem smoothed_restricted_allocation {α γ : Type*} [Fintype γ] (keep : O → Prop)
    (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (b : γ → ℂ) (d : γ → α → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K)
    (hW : ∀ z : O,0≤(W (‖ringComplex z‖^2/K)).re) :
    (restrictedEnergy keep S a (fun i => ∑ B,b B*d B i) W K)≤
      (Fintype.card γ:ℝ)*∑ B,‖b B‖^2*(restrictedEnergy keep S a (d B) W K) := by
  let u := fun z : O => if keep z then (W (‖ringComplex z‖^2/K)).re else 0
  have hu (z : O) : 0≤ u z := by dsimp only [u];split_ifs;exact hW z;exact le_rfl
  have hs := restricted_hasSum_weighted keep S a ha (fun i => ∑ B,b B*d B i) W K hK
  rw [← hs.tsum_eq]
  apply Real.tsum_le_of_sum_le (fun z => mul_nonneg (sq_nonneg _) (hu z))
  intro rows
  calc
    _ ≤ ∑ z∈rows,(Fintype.card γ:ℝ)*∑ B,‖b B‖^2*
        (‖rowPolynomial S a (d B) z‖^2*u z) := by
      apply Finset.sum_le_sum
      intro z hz
      have h := mul_le_mul_of_nonneg_right
        (cover_norm_sum_sq_le_card Finset.univ
          (fun B => b B*rowPolynomial S a (d B) z)) (hu z)
      rw [rowPolynomial_allocation]
      simpa only [Finset.card_univ,norm_mul,mul_pow,Finset.sum_mul,mul_assoc] using h
    _ = (Fintype.card γ:ℝ)*∑ B,‖b B‖^2*
        ∑ z∈rows,‖rowPolynomial S a (d B) z‖^2*u z := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      exact mul_le_mul_of_nonneg_left
        (finite_weighted_le_restricted keep S a ha (d B) W K hK hW rows) (sq_nonneg _)

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem original_restricted_child_energy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (f : Ideal O → ℂ) (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K)
    (hW : ∀ z : O,0≤(W (‖ringComplex z‖^2/K)).re) :
    (sourceRestrictedEnergy keep (residualPool C hC.1 (finiteColumns (Fintype.piFinset S)))
      (fun I => if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0) f W K)≤
      ((actualAllocations S C).card:ℝ)*∑ B : actualAllocations S C,
        ‖frozenCoefficient B C R ν Wslot P‖^2*
          (sourceRestrictedEnergy keep
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K) := by
  let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
  let b := fun B : actualAllocations S C => frozenCoefficient B C R ν Wslot P
  let d := fun (B : actualAllocations S C) (I : supportedColumns Q) =>
    finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I*f I
  have he (I : supportedColumns Q) :
      (if IsCoprime C (I:Ideal O) then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0)*f I=
      ∑ B,b B*d B I := by
    rw [original_source_punctured_column S hS hp C R s I hC.1
      (Finset.mem_filter.mp I.property).2.1 hsC ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂,Finset.sum_mul]
    simp only [b,d,mul_assoc]
  have h := smoothed_restricted_allocation keep Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) b d W K hK hW
  have he' := funext he
  change (restrictedEnergy keep Finset.univ (sourceGenerator Q) _ W K)≤ _
  rw [he']
  apply h.trans_eq
  rw [Fintype.card_coe]
  apply congrArg (fun x : ℝ => ((actualAllocations S C).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  simpa only [b,d,sourceRestrictedEnergy] using
    congrArg (fun x : ℝ => ‖frozenCoefficient B C R ν Wslot P‖^2*x)
    (live_restrictedEnergy S hS hp B
    (allocation_data S C B (Finset.mem_filter.mp B.property).1).1 C R hC
    (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ f keep W K)

end CenteredMomentRestrictedSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentSourceRectangleEnergy
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve 
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily
open CenteredMomentRestrictedDomain CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentSourceRectangle
open CenteredMomentSourceRectangleMask CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentDivisorRowEnergy CenteredMomentDivisorRetained
local notation "O" => Eisenstein.O

theorem height_source_row (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (β : Ideal O→ℂ) (z : O) :
    rowPolynomial Finset.univ (sourceGenerator S)
      (fun I : supportedColumns S=>β I*heightCoeff η t I) z=
      ∑ I∈S,β I*rowWeight η fixedBadMask 1 z t I := by
  rw [source_rowPolynomial S (fun I=>β I*heightCoeff η t I) z]
  calc
    _ = ∑ I∈supportedColumns S,β I*rowWeight η fixedBadMask 1 z t I := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [heightCoeff_eq_fixed_rowWeight η t I (Finset.mem_filter.mp hI).2,
        rowWeight_split η fixedBadMask 1 z t I]
      ring
    _ = _ := Finset.sum_filter_of_ne (fun I hI hn => by
      by_contra hs
      apply hn
      rw [rowWeight_zero_of_not_supported η fixedBadMask 1 z t
        (dvd_mul_right _ _) (dvd_mul_left _ _) I hs,mul_zero])

theorem source_restricted_energy_eq_rectangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : Character) (t : ℝ) (keep : O→Prop)
    (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (h₁ : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (h₂ : PlainCoverage S₂ W₂ B₂ X₂ Y₂)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceRestrictedEnergy keep (finiteColumns (tuplePool slots S₁ S₂))
      (finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L))
      (heightCoeff η t) W K=
      ∑' z : O,if keep z then
        ‖maskedRectangle η (fixedBadMask*cubicIdealGenerator R) 1 z t slots
          (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) L W₁ W₂
          (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
          (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2*
        (W (‖ringComplex z‖^2/K)).re else 0 := by
  unfold sourceRestrictedEnergy restrictedEnergy
  apply tsum_congr
  intro z
  rw [height_source_row]
  rw [CenteredMomentSourceRectangleMask.source_polynomial_eq_maskedRectangle
    η fixedBadMask 1 z t (dvd_mul_right _ _) (dvd_mul_left _ _)
    slots S₁ S₂ R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ h₁ h₂]

end CenteredMomentSourceRectangleEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentRadialSourceDictionary
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentRestrictedSource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow

local notation "O" => Eisenstein.O

 theorem actual_source_energy {ι:Type*} [Fintype ι] [DecidableEq ι]
    (s:Data ι) (r:Radial) (S₁ S₂:Finset (Ideal O)) (R L B₁ B₂:Ideal O)
    (X₁ X₂ Y₁ Y₂:ℝ)
    (hm:s.m=fixedBadMask*cubicIdealGenerator R) (hA:s.A=1)
    (hX₁:s.X₁=X₁/Ideal.absNorm B₁) (hX₂:s.X₂=X₂/Ideal.absNorm B₂)
    (hY₁:s.Y₁=Y₁/Ideal.absNorm B₁) (hY₂:s.Y₂=Y₂/Ideal.absNorm B₂)
    (hcov₁:PlainCoverage S₁ s.W₁ B₁ X₁ Y₁) (hcov₂:PlainCoverage S₂ s.W₂ B₂ X₂ Y₂) :
    sourceRestrictedEnergy r.keep (finiteColumns (tuplePool s.slots S₁ S₂))
      (finiteColumnCoefficient (tuplePool s.slots S₁ S₂)
        (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L))
      (heightCoeff s.η s.t) r.profile r.scale/(s.X₁*s.X₂*∏i,s.P i)=energy s r L := by
  rw [source_restricted_energy_eq_rectangle s.η s.t r.keep s.slots S₁ S₂ R L
    s.ν s.W s.P s.W₁ s.W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hcov₁ hcov₂ r.profile r.scale]
  unfold energy
  rw [←tsum_div_const]
  apply tsum_congr
  intro z
  have ht:0< s.X₁*s.X₂*∏i,s.P i:=mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=> s.P_pos i))
  rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ ht]
  have hc:s.coefficient=(fun i I=> s.ν i I*s.W i ((Ideal.absNorm I:ℝ)/s.P i)):=rfl
  rw [hc]
  dsimp only [Radial.weight]
  rw [hm,hA,hX₁,hX₂,hY₁,hY₂]
  split_ifs <;> ring

end CenteredMomentRadialSourceDictionary

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentActiveSourceRetained
open CenteredMomentActiveAllocation HeckeFamily  CenteredMomentSecondHeightFamily
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentRowNorm CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRaw
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem source_plain_to_active_retained (N : ℕ) (hslots : Fintype.card ι≤ N)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0< C ∧ ∀ (η : Character) (t : ℝ)
      (slots : ι→Finset (Ideal O)),(∀ i,∀ I∈slots i,Prime I) →
      ∀ (S₁ S₂ : Finset (Ideal O)) (R L : Ideal O),Squarefree L →
      ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0< P i) → (∀ i,0≤ M i) →
      (∀ i,∀ I∈slots i,‖ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)‖≤ M i) →
      ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O),
      B₁≠0 → B₂≠0 → Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0< X₁ → 0< X₂ → 0< Y₁ → 0< Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage S₁ W₁ B₁ X₁ Y₁ → PlainCoverage S₂ W₂ B₂ X₂ Y₂ →
      ∀ (rows : Finset O) («ω» : O→ℝ),(∀ z∈rows,0≤«ω» z) →
      let Q := finiteColumns (tuplePool slots S₁ S₂)
      let β := finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L)
      let raw := T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      let coeff := fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)
      (∑ z∈rows,«ω» z*‖(Real.sqrt (raw*∏ i,P i):ℂ)⁻¹*
        rowPolynomial Finset.univ (sourceGenerator Q)
          (fun I : supportedColumns Q=>β I*heightCoeff η t I) z‖^2)≤
      C*(Ideal.absNorm L:ℝ)^ε*
        ∑ a ∈ activeAllocations η (fixedBadMask*cubicIdealGenerator R) 1 t slots coeff L W₁ W₂
          (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂) (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂),
          ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P)*
          ∑ z∈rows,«ω» z*
            (‖allocatedPositiveRow η (fixedBadMask*cubicIdealGenerator R) 1 z t slots coeff P L a W₁ W₂
              (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
             ‖allocatedPositiveRow η (fixedBadMask*cubicIdealGenerator R) 1 z t slots coeff P L a W₁ W₂
              (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2) := by
  obtain ⟨C,hC,hbound⟩ := active_raw_to_retained_energy (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hX hY hcov₁ hcov₂ rows «ω» hω
  dsimp only
  simp_rw [height_source_row]
  simp_rw [CenteredMomentSourceRectangleMask.source_polynomial_eq_maskedRectangle
    η fixedBadMask 1 _ t (dvd_mul_right _ _) (dvd_mul_left _ _)
    slots S₁ S₂ R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hcov₁ hcov₂]
  have hb₁ : (0:ℝ)< Ideal.absNorm B₁ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₁)
  have hb₂ : (0:ℝ)< Ideal.absNorm B₂ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₂)
  obtain ⟨hx,hy⟩ := pullback_same_product X₁ X₂ Y₁ Y₂ T B₁ B₂ hX hY
  exact hbound η (fixedBadMask*cubicIdealGenerator R) 1 t slots hp
    (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) M P hM hP hcoeff L hL
    W₁ W₂ b₁ b₂ _ _ _ _ _ hs₁ hs₂
    (div_pos hX₁ hb₁) (div_pos hX₂ hb₂) (div_pos hY₁ hb₁) (div_pos hY₂ hb₂)
    hx hy rows «ω» hω

end CenteredMomentActiveSourceRetained

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentActiveSmoothedSource
open CenteredMomentActiveAllocation HeckeFamily  CenteredMomentSecondHeightFamily
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentRowNorm CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRaw
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy CenteredMomentPositiveSummability
open CenteredMomentActiveSourceRetained
local notation "O" => Eisenstein.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

theorem source_plain_to_active_smoothed (N : ℕ) (hslots : Fintype.card ι≤ N)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0< C ∧ ∀ (η : Character) (t : ℝ)
      (slots : ι→Finset (Ideal O)),(∀ i,∀ I∈slots i,Prime I) →
      ∀ (S₁ S₂ : Finset (Ideal O)) (R L : Ideal O),Squarefree L →
      ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0< P i) → (∀ i,0≤ M i) →
      (∀ i,∀ I∈slots i,‖ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)‖≤ M i) →
      ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O),
      B₁≠0 → B₂≠0 → Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0< X₁ → 0< X₂ → 0< Y₁ → 0< Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage S₁ W₁ B₁ X₁ Y₁ → PlainCoverage S₂ W₂ B₂ X₂ Y₂ →
      ∀(keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ),0< K →
      (∀z:O,0≤(Φ (‖ringComplex z‖^2/K)).re) →
      let Q := finiteColumns (tuplePool slots S₁ S₂)
      let β := finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L)
      let raw := T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      let coeff := fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)
      sourceRestrictedEnergy keep Q β (heightCoeff η t) Φ K/(raw*∏i,P i)≤
      C*(Ideal.absNorm L:ℝ)^ε*
        ∑ a ∈ activeAllocations η (fixedBadMask*cubicIdealGenerator R) 1 t slots coeff L W₁ W₂
          (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂) (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂),
          ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P)*
          ∑' z:O,(if keep z then (Φ (‖ringComplex z‖^2/K)).re else 0)*
            (‖allocatedPositiveRow η (fixedBadMask*cubicIdealGenerator R) 1 z t slots coeff P L a W₁ W₂
              (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
             ‖allocatedPositiveRow η (fixedBadMask*cubicIdealGenerator R) 1 z t slots coeff P L a W₁ W₂
              (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2) := by
  obtain ⟨C,hC,hbound⟩:=source_plain_to_active_retained (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ keep Φ K hK hΦ
  dsimp only
  let Q:=finiteColumns (tuplePool slots S₁ S₂)
  let β:=finiteColumnCoefficient (tuplePool slots S₁ S₂)
    (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L)
  let raw:=T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
  let coeff:=fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)
  let «ω»:=fun z:O=> if keep z then (Φ (‖ringComplex z‖^2/K)).re else 0
  have hω (z:O):0≤«ω» z:=by dsimp only [«ω»];split_ifs;exact hΦ z;exact le_rfl
  have hbn (B:Ideal O) (hB:B≠0):(0:ℝ)< Ideal.absNorm B:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB)
  have hraw:0< raw:=div_pos (hXT ▸ mul_pos hX₁ hX₂) (mul_pos (hbn B₁ hB₁) (hbn B₂ hB₂))
  have htotal:0< raw*∏i,P i:=mul_pos hraw (Finset.prod_pos (fun i _=> hP i))
  change sourceRestrictedEnergy keep Q β (heightCoeff η t) Φ K/(raw*∏i,P i)≤ _
  unfold sourceRestrictedEnergy restrictedEnergy
  rw [←tsum_div_const]
  have he (z:O):
      (if keep z then ‖rowPolynomial Finset.univ (sourceGenerator Q)
        (fun I:supportedColumns Q=>β I*heightCoeff η t I) z‖^2*
        (Φ (‖ringComplex z‖^2/K)).re else 0)/(raw*∏i,P i)=
      «ω» z*‖(Real.sqrt (raw*∏i,P i):ℂ)⁻¹*rowPolynomial Finset.univ (sourceGenerator Q)
        (fun I:supportedColumns Q=>β I*heightCoeff η t I) z‖^2 := by
    rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ htotal]
    dsimp only [«ω»]
    split_ifs <;> ring
  simp_rw [he]
  apply Real.tsum_le_of_sum_le (fun z=> mul_nonneg (hω z) (sq_nonneg _))
  intro rows
  have hh:=hbound η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂
    rows «ω» (fun z _=> hω z)
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  apply Finset.sum_le_sum
  intro a ha
  have hf:0< formalReductionFactor L a P:=mul_pos (selectedNorm_pos L a)
    (Finset.prod_pos (fun i _=> hP i))
  have hfac:0≤(2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P:=by
    apply div_nonneg _ hf.le
    exact mul_nonneg (by positivity) (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left ?_ hfac
  have hX:=allocated_positive_summable η (fixedBadMask*cubicIdealGenerator R) 1 t W₁ W₂ b₁ b₂ _ _ hs₁ hs₂
    (div_pos hX₁ (hbn B₁ hB₁)) (div_pos hX₂ (hbn B₂ hB₂)) slots coeff P L a keep Φ K hK
  have hY:=allocated_positive_summable η (fixedBadMask*cubicIdealGenerator R) 1 t W₁ W₂ b₁ b₂ _ _ hs₁ hs₂
    (div_pos hY₁ (hbn B₁ hB₁)) (div_pos hY₂ (hbn B₂ hB₂)) slots coeff P L a keep Φ K hK
  have hs:Summable (fun z:O=>«ω» z*
    (‖allocatedPositiveRow η (fixedBadMask*cubicIdealGenerator R) 1 z t slots coeff P L a W₁ W₂
      (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
     ‖allocatedPositiveRow η (fixedBadMask*cubicIdealGenerator R) 1 z t slots coeff P L a W₁ W₂
      (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2)):=by
    convert hX.add hY using 1
    funext z
    dsimp only [«ω»]
    split_ifs <;> ring
  exact sum_le_hasSum rows (fun z _=> mul_nonneg (hω z) (add_nonneg (sq_nonneg _) (sq_nonneg _))) hs.hasSum
end CenteredMomentActiveSmoothedSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentSourceRetainedEnergy
open HeckeFamily  CenteredMomentSecondHeightFamily
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentRowNorm CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRaw
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem source_plain_to_retained (N : ℕ) (hslots : Fintype.card ι≤ N)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0< C ∧ ∀ (η : Character) (t : ℝ)
      (slots : ι→Finset (Ideal O)),(∀ i,∀ I∈slots i,Prime I) →
      ∀ (S₁ S₂ : Finset (Ideal O)) (R L : Ideal O),Squarefree L →
      ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0< P i) → (∀ i,0≤ M i) →
      (∀ i,∀ I∈slots i,‖ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)‖≤ M i) →
      ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O),
      B₁≠0 → B₂≠0 → Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0< X₁ → 0< X₂ → 0< Y₁ → 0< Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage S₁ W₁ B₁ X₁ Y₁ → PlainCoverage S₂ W₂ B₂ X₂ Y₂ →
      ∀ (rows : Finset O) («ω» : O→ℝ),(∀ z∈rows,0≤«ω» z) →
      let Q := finiteColumns (tuplePool slots S₁ S₂)
      let β := finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L)
      let raw := T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      let coeff := fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)
      (∑ z∈rows,«ω» z*‖(Real.sqrt (raw*∏ i,P i):ℂ)⁻¹*
        rowPolynomial Finset.univ (sourceGenerator Q)
          (fun I : supportedColumns Q=>β I*heightCoeff η t I) z‖^2)≤
      C*(Ideal.absNorm L:ℝ)^ε*
        ∑ a : Allocation L (Finset.univ : Finset (ι⊕Fin 2)),
          ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P)*
          ∑ z∈rows,«ω» z*
            (‖allocatedPositiveRow η (fixedBadMask*cubicIdealGenerator R) 1 z t slots coeff P L a W₁ W₂
              (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
             ‖allocatedPositiveRow η (fixedBadMask*cubicIdealGenerator R) 1 z t slots coeff P L a W₁ W₂
              (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2) := by
  obtain ⟨C,hC,hbound⟩ := masked_raw_to_retained_energy (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hX hY hcov₁ hcov₂ rows «ω» hω
  dsimp only
  simp_rw [height_source_row]
  simp_rw [CenteredMomentSourceRectangleMask.source_polynomial_eq_maskedRectangle
    η fixedBadMask 1 _ t (dvd_mul_right _ _) (dvd_mul_left _ _)
    slots S₁ S₂ R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hcov₁ hcov₂]
  have hb₁ : (0:ℝ)< Ideal.absNorm B₁ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₁)
  have hb₂ : (0:ℝ)< Ideal.absNorm B₂ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₂)
  obtain ⟨hx,hy⟩ := pullback_same_product X₁ X₂ Y₁ Y₂ T B₁ B₂ hX hY
  exact hbound η (fixedBadMask*cubicIdealGenerator R) 1 t slots hp
    (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) M P hM hP hcoeff L hL
    W₁ W₂ b₁ b₂ _ _ _ _ _ hs₁ hs₂
    (div_pos hX₁ hb₁) (div_pos hX₂ hb₂) (div_pos hY₁ hb₁) (div_pos hY₂ hb₂)
    hx hy rows «ω» hω

end CenteredMomentSourceRetainedEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentSmoothedRetainedSource
open HeckeFamily  CenteredMomentSecondHeightFamily
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentRowNorm CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRaw
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy CenteredMomentPositiveSummability
open CenteredMomentSourceRetainedEnergy
local notation "O" => Eisenstein.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

theorem source_plain_to_smoothed_retained (N : ℕ) (hslots : Fintype.card ι≤ N)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0< C ∧ ∀ (η : Character) (t : ℝ)
      (slots : ι→Finset (Ideal O)),(∀ i,∀ I∈slots i,Prime I) →
      ∀ (S₁ S₂ : Finset (Ideal O)) (R L : Ideal O),Squarefree L →
      ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0< P i) → (∀ i,0≤ M i) →
      (∀ i,∀ I∈slots i,‖ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)‖≤ M i) →
      ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O),
      B₁≠0 → B₂≠0 → Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0< X₁ → 0< X₂ → 0< Y₁ → 0< Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage S₁ W₁ B₁ X₁ Y₁ → PlainCoverage S₂ W₂ B₂ X₂ Y₂ →
      ∀(keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ),0< K →
      (∀z:O,0≤(Φ (‖ringComplex z‖^2/K)).re) →
      let Q := finiteColumns (tuplePool slots S₁ S₂)
      let β := finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L)
      let raw := T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      let coeff := fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)
      sourceRestrictedEnergy keep Q β (heightCoeff η t) Φ K/(raw*∏i,P i)≤
      C*(Ideal.absNorm L:ℝ)^ε*
        ∑ a : Allocation L (Finset.univ : Finset (ι⊕Fin 2)),
          ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P)*
          ∑' z:O,(if keep z then (Φ (‖ringComplex z‖^2/K)).re else 0)*
            (‖allocatedPositiveRow η (fixedBadMask*cubicIdealGenerator R) 1 z t slots coeff P L a W₁ W₂
              (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
             ‖allocatedPositiveRow η (fixedBadMask*cubicIdealGenerator R) 1 z t slots coeff P L a W₁ W₂
              (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2) := by
  obtain ⟨C,hC,hbound⟩:=source_plain_to_retained (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ keep Φ K hK hΦ
  dsimp only
  let Q:=finiteColumns (tuplePool slots S₁ S₂)
  let β:=finiteColumnCoefficient (tuplePool slots S₁ S₂)
    (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L)
  let raw:=T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
  let coeff:=fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)
  let «ω»:=fun z:O=> if keep z then (Φ (‖ringComplex z‖^2/K)).re else 0
  have hω (z:O):0≤«ω» z:=by dsimp only [«ω»];split_ifs;exact hΦ z;exact le_rfl
  have hbn (B:Ideal O) (hB:B≠0):(0:ℝ)< Ideal.absNorm B:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB)
  have hraw:0< raw:=div_pos (hXT ▸ mul_pos hX₁ hX₂) (mul_pos (hbn B₁ hB₁) (hbn B₂ hB₂))
  have htotal:0< raw*∏i,P i:=mul_pos hraw (Finset.prod_pos (fun i _=> hP i))
  change sourceRestrictedEnergy keep Q β (heightCoeff η t) Φ K/(raw*∏i,P i)≤ _
  unfold sourceRestrictedEnergy restrictedEnergy
  rw [←tsum_div_const]
  have he (z:O):
      (if keep z then ‖rowPolynomial Finset.univ (sourceGenerator Q)
        (fun I:supportedColumns Q=>β I*heightCoeff η t I) z‖^2*
        (Φ (‖ringComplex z‖^2/K)).re else 0)/(raw*∏i,P i)=
      «ω» z*‖(Real.sqrt (raw*∏i,P i):ℂ)⁻¹*rowPolynomial Finset.univ (sourceGenerator Q)
        (fun I:supportedColumns Q=>β I*heightCoeff η t I) z‖^2 := by
    rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ htotal]
    dsimp only [«ω»]
    split_ifs <;> ring
  simp_rw [he]
  apply Real.tsum_le_of_sum_le (fun z=> mul_nonneg (hω z) (sq_nonneg _))
  intro rows
  have hh:=hbound η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂
    rows «ω» (fun z _=> hω z)
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  apply Finset.sum_le_sum
  intro a ha
  have hf:0< formalReductionFactor L a P:=mul_pos (selectedNorm_pos L a)
    (Finset.prod_pos (fun i _=> hP i))
  have hfac:0≤(2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P:=by
    apply div_nonneg _ hf.le
    exact mul_nonneg (by positivity) (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left ?_ hfac
  have hX:=allocated_positive_summable η (fixedBadMask*cubicIdealGenerator R) 1 t W₁ W₂ b₁ b₂ _ _ hs₁ hs₂
    (div_pos hX₁ (hbn B₁ hB₁)) (div_pos hX₂ (hbn B₂ hB₂)) slots coeff P L a keep Φ K hK
  have hY:=allocated_positive_summable η (fixedBadMask*cubicIdealGenerator R) 1 t W₁ W₂ b₁ b₂ _ _ hs₁ hs₂
    (div_pos hY₁ (hbn B₁ hB₁)) (div_pos hY₂ (hbn B₂ hB₂)) slots coeff P L a keep Φ K hK
  have hs:Summable (fun z:O=>«ω» z*
    (‖allocatedPositiveRow η (fixedBadMask*cubicIdealGenerator R) 1 z t slots coeff P L a W₁ W₂
      (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
     ‖allocatedPositiveRow η (fixedBadMask*cubicIdealGenerator R) 1 z t slots coeff P L a W₁ W₂
      (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2)):=by
    convert hX.add hY using 1
    funext z
    dsimp only [«ω»]
    split_ifs <;> ring
  exact sum_le_hasSum rows (fun z _=> mul_nonneg (hω z) (add_nonneg (sq_nonneg _) (sq_nonneg _))) hs.hasSum
end CenteredMomentSmoothedRetainedSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentSecondSectorChildren
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondSourceEnergy
open CenteredMomentSecondSectorColumns CenteredMomentSecondHeightFamily CenteredMomentSupport
open CenteredMomentSecondScaled CenteredMomentSupportedCorrelation CenteredMomentChildAssembly
open CenteredMomentFixedRay CenteredMomentMobiusRegroup RayFourExpansion
local notation "O" => Eisenstein.O

theorem sector_correlation_children (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D)
    (A₀ : O) (rows : Finset O) (q : O → ℂ) (K : O → Ideal O → Ideal O → ℂ) :
    let a := sectorElement C hC.1 S
    let b := sectorElement D hD.1 S
    let c := fun I : sectorPool C hC.1 S => β (C*I)*heightCoeff η t I
    let d := fun J : sectorPool D hD.1 S => β (D*J)*heightCoeff η t J
    (∑ z∈rows,q z*∑ I : sectorPool C hC.1 S,∑ J : sectorPool D hD.1 S,
      (if IsCoprime (I:Ideal O) (J:Ideal O) then
        idealCorrelation (C*I) (D*J)
          ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
          ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A₀*z)
        else 0)*(c I*star (d J))*K z I J)=
      ∑ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S => (J:Ideal O)),
        (UniqueFactorizationMonoid.moebius L:ℂ)*
          ∑ χ : RayCharacter,∑ ξ : RayCharacter,
            pairCoeff (phaseTable (primaryIdealGenerator C) (primaryIdealGenerator D)) χ ξ*
              ∑ z∈rows,(q z*idealCorrelation C D hC hD (A₀*z))*
                ∑ I : sectorPool C hC.1 S,∑ J : sectorPool D hD.1 S,
                  ((divisorCoefficient L a (movingCoefficient A₀ a c) χ I*idealRowHom z I)*
                    star (divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹) J*idealRowHom (-z) J))*K z I J := by
  dsimp only
  have hb (J : sectorPool D hD.1 S) :
      IsCoprime (primaryIdealGenerator C*primaryIdealGenerator D) (sectorElement D hD.1 S J) := by
    simpa only [mul_comm] using sectorElement_coprime D C hD hC hCD.symm S J
  have he := actual_scaled_row_children rows Finset.univ Finset.univ
    (primaryIdealGenerator C) (primaryIdealGenerator D) A₀
    (sectorElement C hC.1 S) (sectorElement D hD.1 S)
    ((supported_span_primaryIdealGenerator_iff C).mpr hC) ((supported_span_primaryIdealGenerator_iff D).mpr hD)
    (sectorElement_supported C hC.1 S) (sectorElement_supported D hD.1 S)
    (primaryIdealGenerator_spec C (supported_primaryIdealGenerator_ne_zero C hC)).2
    (primaryIdealGenerator_spec D (supported_primaryIdealGenerator_ne_zero D hD)).2
    (sectorElement_primary C hC.1 S) (sectorElement_primary D hD.1 S)
    (sectorElement_coprime C D hC hD hCD S) hb q
    (fun I => β (C*I)*heightCoeff η t I) (fun J => β (D*J)*heightCoeff η t J)
    (fun z I J => K z I J)
  have hcop (I : sectorPool C hC.1 S) (J : sectorPool D hD.1 S) :
      IsCoprime (sectorElement C hC.1 S I) (sectorElement D hD.1 S J) ↔ IsCoprime (I:Ideal O) (J:Ideal O) := by
    rw [←Ideal.isCoprime_span_singleton_iff,sectorElement_span,sectorElement_span]
  simp_rw [hcop,sectorElement_span] at he
  simpa only [idealCorrelation,primaryIdealGenerator_mul,sectorElement] using he

end CenteredMomentSecondSectorChildren

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentSecondSectorEnergy
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondSourceEnergy
open CenteredMomentSecondSectorColumns CenteredMomentSecondHeightFamily
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentRestrictedSource CenteredMomentRestrictedDomain CenteredMomentRestrictedEnergy
open CenteredMomentLiveDomain CenteredMomentFirstSectors RayFourExpansion
local notation "O" => Eisenstein.O

theorem sector_divisor_coefficient (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayMonoid χ (primaryIdealGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (t : ℝ) (I : sectorPool C hC.1 S) :
    divisorCoefficient L (sectorElement C hC.1 S)
      (movingCoefficient A (sectorElement C hC.1 S)
        (fun J : sectorPool C hC.1 S => β (C*J)*heightCoeff η t J)) χ I=
      (if L∣(I:Ideal O) then β (C*I) else 0)*heightCoeff τ t I := by
  rw [divisorCoefficient,movingCoefficient,sectorElement_span,hτ I (sectorPool_supported C hC.1 S I) t]
  dsimp only [sectorElement]
  split_ifs <;> ring

theorem sector_rowPolynomial (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (C : Ideal O) (hC : Supported C) (z : O) :
    rowPolynomial Finset.univ (sectorElement C hC.1 S)
      (fun I : sectorPool C hC.1 S => c I) z=
      rowPolynomial Finset.univ (sourceGenerator (residualPool C hC.1 S))
        (fun I : supportedColumns (residualPool C hC.1 S) => if IsCoprime C (I:Ideal O) then c I else 0) z := by
  rw [source_rowPolynomial (residualPool C hC.1 S)
    (fun I => if IsCoprime C I then c I else 0) z]
  unfold rowPolynomial
  simp only [sectorElement_span]
  rw [Finset.sum_coe_sort (sectorPool C hC.1 S) (fun I => c I*idealRowHom z I)]
  rw [sectorPool,Finset.sum_filter,supported_residualPool C hC S]
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs <;> simp

theorem sector_child_row (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayMonoid χ (primaryIdealGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (t : ℝ) (z : O) :
    rowPolynomial Finset.univ (sectorElement C hC.1 S)
      (divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun J : sectorPool C hC.1 S => β (C*J)*heightCoeff η t J)) χ) z=
      rowPolynomial Finset.univ (sourceGenerator (residualPool C hC.1 S))
        (fun I : supportedColumns (residualPool C hC.1 S) =>
          (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then β (C*I) else 0)*heightCoeff τ t I) z := by
  have he := funext (sector_divisor_coefficient η τ χ A hτ S β C hC L t)
  rw [he,sector_rowPolynomial S (fun I => (if L∣I then β (C*I) else 0)*heightCoeff τ t I) C hC z]
  congr 1
  funext I
  split_ifs <;> simp_all

theorem sector_child_energy (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayMonoid χ (primaryIdealGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (t : ℝ) (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
      (divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun J : sectorPool C hC.1 S => β (C*J)*heightCoeff η t J)) χ) W K=
      sourceRestrictedEnergy keep (residualPool C hC.1 S)
        (fun I => if IsCoprime C I ∧ L∣I then β (C*I) else 0) (heightCoeff τ t) W K := by
  unfold restrictedEnergy sourceRestrictedEnergy
  apply tsum_congr
  intro z
  rw [sector_child_row η τ χ A hτ S β C hC L t z]

end CenteredMomentSecondSectorEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentAmplificationLiveMask
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
open CenteredMomentOriginalChildEnergy CenteredMomentRemainingBox CenteredMomentCommonProfile
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

 theorem profile_mask (R : Ideal O) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v=
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ 1 v*
        (if s∣finiteTupleProduct v then 1 else 0) := by
  simp only [profileCoefficient,one_dvd,ite_true,mul_one]

theorem column_mask (S : Finset (Tuple ι)) (R : Ideal O) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s I : Ideal O) :
    finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I=
      finiteColumnCoefficient S
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ 1) I*
          (if s∣I then 1 else 0) := by
  unfold finiteColumnCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  rw [profile_mask,(Finset.mem_filter.mp hv).2]

 def maskedLiveProfile (B : Tuple ι) (C R s : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    Tuple (liveIndices B) → ℂ :=
  profileCoefficient (R*C) (fun i : liveIndices B => ν i.val)
    (fun i => Wslot i.val) (fun i => P i.val) W₁ W₂ X₁ X₂ Y₁ Y₂
    (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) s

theorem original_masked_live_column (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s I : Ideal O) (hC : C≠0) (hI : I≠0) (hsc : IsCoprime s C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    (if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0)=
      ∑ B : actualAllocations S C,frozenCoefficient B C R ν Wslot P*
        finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
          (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I := by
  have he := original_source_punctured_column S hS hp C R 1 I hC hI (one_dvd C)
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
  have hdiv : s ∣ C*I ↔ s ∣ I :=
    ⟨hsc.dvd_of_dvd_mul_left, fun h => dvd_mul_of_dvd_right h C⟩
  rw [column_mask,hdiv]
  have hh := congrArg (fun z : ℂ => z*(if s∣I then 1 else 0)) he
  rw [Finset.sum_mul] at hh
  convert hh using 1
  · split_ifs <;> simp
  · apply Finset.sum_congr rfl
    intro B hB
    rw [maskedLiveProfile,column_mask]
    dsimp only [liveProfile]
    ring

end CenteredMomentAmplificationLiveMask

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentSecondSourceMask
open CanonicalQuadraticSieve CenteredMomentSecondSectorColumns CenteredMomentFirstSectors
open CenteredMomentSourceRow CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentAmplificationLiveMask
open CenteredMomentCompleteCommon
local notation "O" => Eisenstein.O

theorem divisor_dvd_common (C D a b s : Ideal O)
    (hC : C≠0) (hD : D≠0) (ha : a≠0) (hb : b≠0)
    (hCD : primeSupport C=primeSupport D)
    (hCa : IsCoprime C a) (hCb : IsCoprime C b) (hab : IsCoprime a b)
    (hsI : s∣C*a) (hsJ : s∣D*b) : s∣C ∧ s∣D := by
  have hDa := (coprime_of_same_support C D a hC hD ha hCD).mp hCa
  have hDb := (coprime_of_same_support C D b hC hD hb hCD).mp hCb
  have hsa : IsCoprime s a := ((hDa.symm.mul_right hab).of_isCoprime_of_dvd_right hsJ).symm
  have hsb : IsCoprime s b := ((hCb.symm.mul_right hab.symm).of_isCoprime_of_dvd_right hsI).symm
  exact ⟨hsa.dvd_of_dvd_mul_right hsI,hsb.dvd_of_dvd_mul_right hsJ⟩

variable {ι : Type*} [Fintype ι]

theorem column_nonzero_divisor (S : Finset (Tuple ι)) (R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s I : Ideal O)
    (h : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I≠0) : s∣I := by
  rw [column_mask] at h
  by_contra hn
  exact h (by rw [if_neg hn,mul_zero])

theorem source_pair_divisor_common (S : Finset (Tuple ι)) (R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s C D a b : Ideal O)
    (hC : C≠0) (hD : D≠0) (ha : a≠0) (hb : b≠0)
    (hCD : primeSupport C=primeSupport D)
    (hCa : IsCoprime C a) (hCb : IsCoprime C b) (hab : IsCoprime a b)
    (hleft : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*a)≠0)
    (hright : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (D*b)≠0) : s∣C ∧ s∣D :=
  divisor_dvd_common C D a b s hC hD ha hb hCD hCa hCb hab
    (column_nonzero_divisor S R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s _ hleft)
    (column_nonzero_divisor S R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s _ hright)

end CenteredMomentSecondSourceMask

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentSecondLiveEnergy
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRestrictedSource
open CenteredMomentRestrictedEnergy CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass
open CenteredMomentSourceMass CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationLiveMask CenteredMomentFirstSectors RayFourExpansion
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem live_divisor_energy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R L : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (f : Ideal O → ℂ) (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceRestrictedEnergy keep (finiteColumns (liveBox S B hB))
      (finiteColumnCoefficient (liveBox S B hB) (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
      (fun I => (if L∣I then 1 else 0)*f I) W K=
    sourceRestrictedEnergy keep (finiteColumns (liveBox S B hB))
      (finiteColumnCoefficient (liveBox S B hB) (maskedLiveProfile B C R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K := by
  unfold sourceRestrictedEnergy
  congr 1
  funext I
  rw [maskedLiveProfile,column_mask]
  dsimp only [liveProfile]
  ring

theorem actual_second_child_live_energy (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*CanonicalRowCompletion.idealRowHom A I*
        rayMonoid χ (primaryIdealGenerator I))
    (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ L : Ideal O) (t : ℝ)
    (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K)
    (hW : ∀ z : O,0≤(W (‖ringComplex z‖^2/K)).re) :
    let Q := finiteColumns (Fintype.piFinset S)
    let β := finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 Q)
      (divisorCoefficient L (sectorElement C hC.1 Q)
        (movingCoefficient A (sectorElement C hC.1 Q)
          (fun J : sectorPool C hC.1 Q => β (C*J)*heightCoeff η t J)) χ) W K≤
      ((actualAllocations S C).card:ℝ)*∑ B : actualAllocations S C,
        ‖frozenCoefficient B C R ν Wslot P‖^2*
          sourceRestrictedEnergy keep
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B C R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
            (heightCoeff τ t) W K := by
  dsimp only
  rw [sector_child_energy η τ χ A hτ (finiteColumns (Fintype.piFinset S))
    (finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) C hC L t keep W K]
  have he := original_restricted_child_energy S hS hp C R s hC hsC
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
    (fun I => (if L∣I then 1 else 0)*heightCoeff τ t I) keep W K hK hW
  simp_rw [live_divisor_energy] at he
  refine le_trans ?_ he
  apply le_of_eq
  unfold sourceRestrictedEnergy
  congr 1
  funext I
  dsimp only
  split_ifs <;> simp_all

end CenteredMomentSecondLiveEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentAllocationCost
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentAddedZeroUniform
local notation "O" => Eisenstein.O

 theorem actualAllocations_uniform_small_power (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ D : ℝ,0< D ∧ ∀ {ι : Type*} [Fintype ι],Fintype.card ι≤ N →
      ∀ (S : ι → Finset (Ideal O)) (C : Ideal O),C≠0 →
        ((actualAllocations S C).card:ℝ)≤ D*(Ideal.absNorm C:ℝ)^ε := by
  let δ := ε/(N+1:ℕ)
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨(1+D)^(N+1),by positivity,?_⟩
  intro ι _ hn S C hC
  have hNC : (1:ℝ)≤ Ideal.absNorm C := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hb : 1≤(1+D)*(Ideal.absNorm C:ℝ)^δ := by
    nlinarith [Real.one_le_rpow hNC hδ.le]
  have hd : δ*(N+1:ℕ)=ε := by
    dsimp only [δ]
    field_simp
  calc
    _ ≤ ((idealDivisors C).card:ℝ)^Fintype.card ι := by
      exact_mod_cast actualAllocations_card S C hC
    _ ≤ ((1+D)*(Ideal.absNorm C:ℝ)^δ)^Fintype.card ι := by
      apply pow_le_pow_left₀ (Nat.cast_nonneg _) _ _
      exact (hdiv C hC).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    _ ≤ ((1+D)*(Ideal.absNorm C:ℝ)^δ)^(N+1) := pow_le_pow_right₀ hb (by omega)
    _ = _ := by rw [mul_pow,←Real.rpow_mul_natCast (Nat.cast_nonneg _),hd]

 theorem frozenCoefficient_norm {ι : Type*} [Fintype ι]
    (B : Tuple ι) (C R : Ideal O) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P M : ι → ℝ)
    (hν : ∀ i I,‖ν i I‖≤1) (hW : ∀ i x,‖Wslot i x‖≤ M i)
    (hM : ∀ i,1≤ M i) :
    ‖frozenCoefficient B C R ν Wslot P‖≤∏ i,M i := by
  unfold frozenCoefficient
  rw [norm_mul]
  have hc : ‖(if IsCoprime C R then (1:ℂ) else 0)‖≤1 := by split_ifs <;> simp
  apply (mul_le_of_le_one_right (norm_nonneg _) hc).trans
  rw [norm_prod]
  calc
    _ ≤ ∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),M i := by
      apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
      intro i hi
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hν i _)).trans (hW i _)
    _ ≤ ∏ i,M i := Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _)
      (fun i _ => zero_le_one.trans (hM i)) (fun i _ _ => hM i)

end CenteredMomentAllocationCost

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentCommonRawScale
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]

def frozenScale (B : Tuple ι) (P : ι → ℝ) (i : ι) : ℝ :=
  if B (Sum.inl i)=1 then 1 else P i

def plainNorm (B : Tuple ι) : ℝ :=
  (Ideal.absNorm (B (Sum.inr 0)):ℝ)*Ideal.absNorm (B (Sum.inr 1))

def rawReduction (B : Tuple ι) (P : ι → ℝ) : ℝ := plainNorm B*∏ i,frozenScale B P i

def remainingRaw (B : Tuple ι) (T : ℝ) (P : ι → ℝ) : ℝ :=
  (T/plainNorm B)*∏ i : liveIndices B,P i

omit [Fintype ι] in
theorem plainNorm_pos (B : Tuple ι) (hB : ∀ i,B i≠0) : 0< plainNorm B := by
  unfold plainNorm
  apply mul_pos <;> exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hB _))

omit [Fintype ι] in
theorem frozenScale_pos (B : Tuple ι) (P : ι → ℝ) (hP : ∀ i,0< P i) (i : ι) :
    0< frozenScale B P i := by
  unfold frozenScale
  split_ifs
  · exact zero_lt_one
  · exact hP i

theorem rawReduction_pos (B : Tuple ι) (hB : ∀ i,B i≠0) (P : ι → ℝ) (hP : ∀ i,0< P i) :
    0< rawReduction B P := mul_pos (plainNorm_pos B hB) (Finset.prod_pos (fun i _ => frozenScale_pos B P hP i))

theorem slot_scale_split (B : Tuple ι) (P : ι → ℝ) :
    (∏ i,frozenScale B P i)*(∏ i : liveIndices B,P i)=∏ i,P i := by
  rw [Finset.prod_coe_sort (liveIndices B) P]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => B (Sum.inl i)=1) P]
  unfold frozenScale liveIndices
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one,one_mul]
  ring

theorem raw_scale_identity (B : Tuple ι) (hB : ∀ i,B i≠0) (T : ℝ) (P : ι → ℝ) :
    remainingRaw B T P*rawReduction B P=T*∏ i,P i := by
  unfold remainingRaw rawReduction
  have h := slot_scale_split B P
  calc
    _ = T*((∏ i,frozenScale B P i)*(∏ i : liveIndices B,P i)) := by
      field_simp [(plainNorm_pos B hB).ne']
    _ = _ := by rw [h]

theorem remainingRaw_source (B : Tuple ι) (_hB : ∀ i,B i≠0)
    (B₁ B₂ : Ideal O) (_hB₁ : B₁≠0) (_hB₂ : B₂≠0) (T : ℝ) (P : ι → ℝ) :
    remainingRaw B (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)) P=
      (T/((Ideal.absNorm (B₁*B (Sum.inr 0)):ℝ)*Ideal.absNorm (B₂*B (Sum.inr 1))))*
        ∏ i : liveIndices B,P i := by
  unfold remainingRaw plainNorm
  simp only [map_mul,Nat.cast_mul]
  ring

theorem product_norm (B : Tuple ι) :
    (Ideal.absNorm (finiteTupleProduct B):ℝ)=plainNorm B*∏ i,(Ideal.absNorm (B (Sum.inl i)):ℝ) := by
  simp only [finiteTupleProduct,Fintype.prod_sum_type,Fin.prod_univ_two,map_mul,map_prod,
    Nat.cast_mul,Nat.cast_prod,plainNorm]
  ring

theorem frozen_window_ne_zero (B : Tuple ι) (C R : Ideal O) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (hne : frozenCoefficient B C R ν Wslot P≠0) (i : ι) (hi : B (Sum.inl i)≠1) :
    Wslot i ((Ideal.absNorm (B (Sum.inl i)):ℝ)/P i)≠0 := by
  have hp := (mul_ne_zero_iff.mp hne).1
  have hx := Finset.prod_ne_zero_iff.mp hp i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
  exact (mul_ne_zero_iff.mp hx).2

theorem actual_reduction_norm (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O)
    (hprod : finiteTupleProduct B=C) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (hP : ∀ i,0< P i)
    (a b : ℝ) (ha : 0< a) (hW : ∀ i,Function.support (Wslot i)⊆Set.Icc a b)
    (hne : frozenCoefficient B C R ν Wslot P≠0) :
    (min 1 a)^Fintype.card ι*rawReduction B P≤(Ideal.absNorm C:ℝ) ∧
      (Ideal.absNorm C:ℝ)≤(max 1 b)^Fintype.card ι*rawReduction B P := by
  have hi (i : ι) : min 1 a*frozenScale B P i≤(Ideal.absNorm (B (Sum.inl i)):ℝ) ∧
      (Ideal.absNorm (B (Sum.inl i)):ℝ)≤ max 1 b*frozenScale B P i := by
    by_cases h : B (Sum.inl i)=1
    · simp only [frozenScale,h,ite_true,map_one,Nat.cast_one,mul_one]
      exact ⟨min_le_left _ _,le_max_left _ _⟩
    · have hs := hW i (frozen_window_ne_zero B C R ν Wslot P hne i h)
      rw [frozenScale,if_neg h]
      exact ⟨le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (hP i).le)
          ((le_div_iff₀ (hP i)).mp hs.1),
        le_trans ((div_le_iff₀ (hP i)).mp hs.2)
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (hP i).le)⟩
  rw [←hprod,product_norm]
  constructor
  · have hh := Finset.prod_le_prod (s:=Finset.univ)
      (fun i _ => mul_nonneg (le_of_lt (lt_min zero_lt_one ha)) (frozenScale_pos B P hP i).le)
      (fun i _ => (hi i).1)
    simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (plainNorm_pos B hB).le
    simpa only [rawReduction,mul_left_comm,mul_assoc] using hh'
  · have hh := Finset.prod_le_prod (s:=Finset.univ) (fun i _ => Nat.cast_nonneg (Ideal.absNorm (B (Sum.inl i))))
      (fun i _ => (hi i).2)
    simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (plainNorm_pos B hB).le
    simpa only [rawReduction,mul_left_comm,mul_assoc] using hh'

end CenteredMomentCommonRawScale

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentCommonRawCost
open CenteredMomentCommonRawScale CenteredMomentAllocationCost CenteredMomentSourceLiveColumn
open CenteredMomentAddedZeroUniform
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]

theorem frozen_normalized_cost (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O) (hC : C≠0)
    (hprod : finiteTupleProduct B=C) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P M : ι → ℝ) (hP : ∀ i,0< P i)
    (hν : ∀ i I,‖ν i I‖≤1) (hWnorm : ∀ i x,‖Wslot i x‖≤ M i) (hM : ∀ i,1≤ M i)
    (a b : ℝ) (ha : 0< a) (hW : ∀ i,Function.support (Wslot i)⊆Set.Icc a b) :
    ‖frozenCoefficient B C R ν Wslot P‖^2/rawReduction B P≤
      ((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ) := by
  have hN : (0:ℝ)< Ideal.absNorm C := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hR := rawReduction_pos B hB P hP
  by_cases hz : frozenCoefficient B C R ν Wslot P=0
  · rw [hz,norm_zero,zero_pow (by decide : 2≠0),zero_div]
    exact div_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)) hN.le
  · have hm := frozenCoefficient_norm B C R ν Wslot P M hν hWnorm hM
    have hh := (actual_reduction_norm B hB C R hprod ν Wslot P hP a b ha hW hz).2
    have hi : (1:ℝ)/rawReduction B P≤(max 1 b)^Fintype.card ι/(Ideal.absNorm C:ℝ) := by
      apply (div_le_div_iff₀ hR hN).mpr
      simpa only [one_mul] using hh
    calc
      _ ≤ (∏ i,M i)^2/rawReduction B P :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hm _) hR.le
      _ = (∏ i,M i)^2*(1/rawReduction B P) := by ring
      _ ≤ (∏ i,M i)^2*((max 1 b)^Fintype.card ι/(Ideal.absNorm C:ℝ)) :=
        mul_le_mul_of_nonneg_left hi (sq_nonneg _)
      _ = _ := by ring

end CenteredMomentCommonRawCost

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentRestrictedSourceNormalization
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentRestrictedSource
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
open CenteredMomentCommonRawScale CenteredMomentCommonRawCost CenteredMomentRestrictedEnergy
local notation "O" => Eisenstein.O

theorem sourceRestrictedEnergy_nonneg (keep : O → Prop) (Q : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (_hK : 0< K)
    (hW : ∀ z : O,0≤(W (‖ringComplex z‖^2/K)).re) :
    0≤ sourceRestrictedEnergy keep Q c f W K := by
  unfold sourceRestrictedEnergy restrictedEnergy
  apply tsum_nonneg
  intro z
  split_ifs
  · exact mul_nonneg (sq_nonneg _) (hW z)
  · exact le_rfl

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem normalized_restricted_child_energy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (Traw : ℝ) (hTraw : 0< Traw) (hP : ∀ i,0< P i)
    (f : Ideal O → ℂ) (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K)
    (hW : ∀ z : O,0≤(W (‖ringComplex z‖^2/K)).re) :
    (sourceRestrictedEnergy keep (residualPool C hC.1 (finiteColumns (Fintype.piFinset S)))
      (fun I => if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0) f W K)/(Traw*∏ i,P i)≤
      ((actualAllocations S C).card:ℝ)*∑ B : actualAllocations S C,
        (‖frozenCoefficient B C R ν Wslot P‖^2/rawReduction B P)*
          ((sourceRestrictedEnergy keep
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K)/remainingRaw B Traw P) := by
  have h := original_restricted_child_energy S hS hp C R s hC hsC ν Wslot P W₁ W₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ f keep W K hK hW
  have htotal : 0< Traw*∏ i,P i := mul_pos hTraw (Finset.prod_pos (fun i _ => hP i))
  apply (div_le_div_of_nonneg_right h htotal.le).trans_eq
  rw [mul_div_assoc,Finset.sum_div]
  apply congrArg (fun x : ℝ => ((actualAllocations S C).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  have hb := (allocation_data S C B (Finset.mem_filter.mp B.property).1).1
  have hr := raw_scale_identity B hb Traw P
  have hpR := rawReduction_pos B hb P hP
  have hpL : 0< remainingRaw B Traw P := by
    apply (mul_pos_iff_of_pos_right hpR).mp
    exact hr.symm ▸ htotal
  have alg (d e n r l : ℝ) (hr : 0< r) (hl : 0< l) (hn : l*r=n) :
      d*e/n=(d/r)*(e/l) := by
    rw [←hn]
    field_simp [hr.ne',hl.ne']
  exact alg _ _ _ _ _ hpR hpL hr

theorem restricted_child_common_saving (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (Traw : ℝ) (hTraw : 0< Traw) (hP : ∀ i,0< P i)
    (M : ι → ℝ) (hν : ∀ i I,‖ν i I‖≤1) (hWnorm : ∀ i x,‖Wslot i x‖≤ M i)
    (hM : ∀ i,1≤ M i) (a b : ℝ) (ha : 0< a)
    (hslot : ∀ i,Function.support (Wslot i)⊆Set.Icc a b)
    (f : Ideal O → ℂ) (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K)
    (hW : ∀ z : O,0≤(W (‖ringComplex z‖^2/K)).re) :
    (sourceRestrictedEnergy keep (residualPool C hC.1 (finiteColumns (Fintype.piFinset S)))
      (fun I => if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0) f W K)/(Traw*∏ i,P i)≤
      ((actualAllocations S C).card:ℝ)*
        (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))*
          ∑ B : actualAllocations S C, ((sourceRestrictedEnergy keep
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K)/remainingRaw B Traw P) := by
  have h := normalized_restricted_child_energy S hS hp C R s hC hsC ν Wslot P W₁ W₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ Traw hTraw hP f keep W K hK hW
  apply h.trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro B hB
  have hb := (allocation_data S C B (Finset.mem_filter.mp B.property).1).1
  have hprod : finiteTupleProduct (B : Tuple ι)=C := (Finset.mem_filter.mp B.property).2
  have hc := frozen_normalized_cost (ι:=ι) (B : Tuple ι) hb C R hC.1 hprod ν Wslot P M hP hν hWnorm hM a b ha hslot
  apply mul_le_mul_of_nonneg_right hc
  have hr := raw_scale_identity B hb Traw P
  have hpR := rawReduction_pos B hb P hP
  have htotal : 0< Traw*∏ i,P i := mul_pos hTraw (Finset.prod_pos (fun i _ => hP i))
  have hpL : 0< remainingRaw B Traw P := (mul_pos_iff_of_pos_right hpR).mp (hr.symm ▸ htotal)
  exact div_nonneg (sourceRestrictedEnergy_nonneg keep _ _ f W K hK hW) hpL.le

end CenteredMomentRestrictedSourceNormalization

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentSecondSourceCost
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRestrictedSource
open CenteredMomentRestrictedEnergy CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass
open CenteredMomentSourceMass CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationLiveMask CenteredMomentFirstSectors RayFourExpansion
open CenteredMomentSecondLiveEnergy CenteredMomentRestrictedSourceNormalization
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem source_divisor_common_saving (τ : Character)
    (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ L : Ideal O) (t : ℝ)
    (Traw : ℝ) (hTraw : 0< Traw) (hP : ∀ i,0< P i)
    (M : ι → ℝ) (hν : ∀ i I,‖ν i I‖≤1) (hWnorm : ∀ i x,‖Wslot i x‖≤ M i)
    (hM : ∀ i,1≤ M i) (a b : ℝ) (ha : 0< a)
    (hslot : ∀ i,Function.support (Wslot i)⊆Set.Icc a b)
    (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K)
    (hW : ∀ z : O,0≤(W (‖ringComplex z‖^2/K)).re) :
    let Q := finiteColumns (Fintype.piFinset S)
    let β := finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
    sourceRestrictedEnergy keep (residualPool C hC.1 Q)
      (fun I=> if IsCoprime C I ∧ L∣I then β (C*I) else 0)
      (heightCoeff τ t) W K/(Traw*∏ i,P i)≤
      ((actualAllocations S C).card:ℝ)*
        (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))*
          ∑ B : actualAllocations S C, (sourceRestrictedEnergy keep
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B C R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
            (heightCoeff τ t) W K)/CenteredMomentCommonRawScale.remainingRaw B Traw P := by
  dsimp only
  have he := restricted_child_common_saving S hS hp C R s hC hsC
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ Traw hTraw hP M hν hWnorm hM a b ha hslot
    (fun I => (if L∣I then 1 else 0)*heightCoeff τ t I) keep W K hK hW
  simp_rw [live_divisor_energy] at he
  refine le_trans ?_ he
  apply le_of_eq
  congr 1
  unfold sourceRestrictedEnergy
  congr 1
  funext I
  dsimp only
  by_cases hc : IsCoprime C I.val <;> by_cases hd : L ∣ I.val <;>
    simp only [hc, hd, and_true, and_false, true_and, false_and,
      ite_true, ite_false, zero_mul, mul_zero, one_mul]

end CenteredMomentSecondSourceCost

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentCanonicalRetainedSource
open CanonicalQuadraticSieve CenteredMomentFirstSectors
open HeckeFamily  CenteredMomentSecondHeightFamily
open CenteredMomentSourceRectangle CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRaw
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationLiveMask CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CenteredMomentCommonRawScale CenteredMomentRestrictedSourceNormalization
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def positiveChildren (η : Character) (t : ℝ) (slots : ι→Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑ a : Allocation L (Finset.univ : Finset (ι⊕Fin 2)),
    ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P)*
      ∑' z:O,(if keep z then (Φ (‖ringComplex z‖^2/K)).re else 0)*
        (‖allocatedPositiveRow η (fixedBadMask*cubicIdealGenerator R) 1 z t slots
          (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P L a W₁ W₂
          (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
         ‖allocatedPositiveRow η (fixedBadMask*cubicIdealGenerator R) 1 z t slots
          (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P L a W₁ W₂
          (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2)

theorem positiveChildren_nonneg (η : Character) (t : ℝ) (slots : ι→Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
    (hP : ∀ i,0< P i) (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hΦ : ∀ z:O,0≤(Φ (‖ringComplex z‖^2/K)).re) :
    0≤ positiveChildren η t slots R L ν Wslot P M W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K := by
  apply Finset.sum_nonneg
  intro a _
  apply mul_nonneg
  · apply div_nonneg
    · exact mul_nonneg (by positivity) (sq_nonneg _)
    · exact (mul_pos (selectedNorm_pos L a) (Finset.prod_pos (fun i _=> hP i))).le
  · apply tsum_nonneg
    intro z
    apply mul_nonneg
    · split_ifs;exact hΦ z;exact le_rfl
    · exact add_nonneg (sq_nonneg _) (sq_nonneg _)

def SmoothedBound (ι : Type*) [Fintype ι] [DecidableEq ι] (D ε : ℝ) : Prop :=
∀ (η : Character) (t : ℝ)
      (slots : ι→Finset (Ideal O)),(∀ i,∀ I∈slots i,Prime I) →
    ∀ (S₁ S₂ : Finset (Ideal O)) (R L : Ideal O),Squarefree L →
    ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0< P i) → (∀ i,0≤ M i) →
      (∀ i,∀ I∈slots i,‖ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)‖≤ M i) →
    ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O),
      B₁≠0 → B₂≠0 → Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0< X₁ → 0< X₂ → 0< Y₁ → 0< Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage S₁ W₁ B₁ X₁ Y₁ → PlainCoverage S₂ W₂ B₂ X₂ Y₂ →
    ∀(keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ),0< K →
      (∀z:O,0≤(Φ (‖ringComplex z‖^2/K)).re) →
      let Q := finiteColumns (tuplePool slots S₁ S₂)
      let β := finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L)
      let raw := T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      sourceRestrictedEnergy keep Q β (heightCoeff η t) Φ K/(raw*∏i,P i)≤
      D*(Ideal.absNorm L:ℝ)^ε*
        positiveChildren η t slots R L ν Wslot P M W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K

theorem uniform_smoothed_bound (ε : ℝ) (hε : 0<ε) :
    ∃ D:ℝ,0< D ∧ ∀ J:Finset ι,SmoothedBound J D ε := by
  have hex (J:Finset ι) : ∃ D:ℝ,0< D ∧ SmoothedBound J D ε := by
    simpa only [SmoothedBound,positiveChildren] using
      CenteredMomentSmoothedRetainedSource.source_plain_to_smoothed_retained
        (ι:=J) (Fintype.card ι) (by simpa using Finset.card_le_univ J) ε hε
  choose D hD hbound using hex
  let C:ℝ:=1+∑ J:Finset ι,D J
  have hs:0≤∑ J:Finset ι,D J:=Finset.sum_nonneg (fun J _=>(hD J).le)
  have hC:0< C:=by dsimp [C];linarith
  have hDC (J:Finset ι):D J≤ C:=by
    have hh:=Finset.single_le_sum (fun J _=>(hD J).le) (Finset.mem_univ J)
    dsimp [C];linarith
  refine ⟨C,hC,?_⟩
  intro J η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ keep Φ K hK hΦ
  have hh:=hbound J η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ keep Φ K hK hΦ
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hDC J) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (positiveChildren_nonneg η t slots R L ν Wslot P M hP W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K hΦ))

omit [DecidableEq ι] in

theorem live_residual_pool (S : (ι⊕Fin 2)→Finset (Ideal O)) (B : Tuple ι)
    (hB : ∀ j,B j≠0) (i : liveIndices B) :
    residualPool (B (Sum.inl i.val)) (hB _) (S (Sum.inl i.val))=S (Sum.inl i.val) := by
  ext I
  rw [mem_residualPool,(Finset.mem_filter.mp i.property).2,one_mul]

omit [DecidableEq ι] in
theorem liveBox_original_pools (S : (ι⊕Fin 2)→Finset (Ideal O)) (B : Tuple ι)
    (hB : ∀ j,B j≠0) :
    liveBox S B hB=tuplePool (fun i:liveIndices B=> S (Sum.inl i.val))
      (residualPool (B (Sum.inr 0)) (hB _) (S (Sum.inr 0)))
      (residualPool (B (Sum.inr 1)) (hB _) (S (Sum.inr 1))) := by
  rw [liveBox_eq_tuplePool]
  simp_rw [live_residual_pool]

def commonPositiveChildren (τ : Character) (t : ℝ)
    (S : (ι⊕Fin 2)→Finset (Ideal O)) (B : Tuple ι) (C R L : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  positiveChildren τ t (fun i:liveIndices B=> S (Sum.inl i.val)) (R*C) L
    (fun i=>ν i.val) (fun i=> Wslot i.val) (fun i=> P i.val) (fun i=> M i.val)
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) keep Φ K

local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem canonical_source_to_positive (ε : ℝ) (hε : 0<ε) :
    ∃ D:ℝ,0< D ∧ ∀ (τ : Character)
      (S : (ι⊕Fin 2)→Finset (Ideal O)),
      (∀ j,∀ I∈S j,I≠0) → (∀ i,∀ I∈S (Sum.inl i),Prime I) →
      ∀ (C R s : Ideal O) (hC : Supported C),s∣C →
      ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0< P i) → (∀ i I,‖ν i I‖≤1) → (∀ i x,‖Wslot i x‖≤ M i) → (∀ i,1≤ M i) →
      ∀ (a b : ℝ),0< a → (∀ i,Function.support (Wslot i)⊆Set.Icc a b) →
      ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ L : Ideal O),
      B₁≠0 → B₂≠0 → Squarefree L →
      Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0< X₁ → 0< X₂ → 0< Y₁ → 0< Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage (S (Sum.inr 0)) W₁ B₁ X₁ Y₁ →
      PlainCoverage (S (Sum.inr 1)) W₂ B₂ X₂ Y₂ →
      ∀ (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ),0< K →
      (∀ z:O,0≤(Φ (‖ringComplex z‖^2/K)).re) →
      let Q:=finiteColumns (Fintype.piFinset S)
      let β:=finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
      let raw:=T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      sourceRestrictedEnergy keep (residualPool C hC.1 Q)
        (fun I=> if IsCoprime C I ∧ L∣I then β (C*I) else 0)
        (heightCoeff τ t) Φ K/(raw*∏ i,P i)≤
        ((actualAllocations S C).card:ℝ)*
          (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))*
          D*(Ideal.absNorm L:ℝ)^ε*
          ∑ B:actualAllocations S C,
            commonPositiveChildren τ t S B C R L ν Wslot P M W₁ W₂
              b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K := by
  obtain ⟨D,hD,hbound⟩:=uniform_smoothed_bound (ι:=ι) ε hε
  refine ⟨D,hD,?_⟩
  intro τ S hS hp C R s hC hsC ν Wslot P M hP hν hWnorm hM a b ha hslot
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ L hB₁ hB₂ hL hs₁ hs₂
    hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ t keep Φ K hK hΦ
  dsimp only
  have hbn (I:Ideal O) (hI:I≠0):(0:ℝ)< Ideal.absNorm I:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hraw:0< T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂):=
    div_pos (hXT ▸ mul_pos hX₁ hX₂) (mul_pos (hbn B₁ hB₁) (hbn B₂ hB₂))
  have hcommon:=CenteredMomentSecondSourceCost.source_divisor_common_saving τ S hS hp C R s hC hsC
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L t _ hraw hP M hν hWnorm hM a b ha hslot keep Φ K hK hΦ
  dsimp only at hcommon
  refine hcommon.trans ?_
  let pref:ℝ:=((actualAllocations S C).card:ℝ)*
    (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))
  have hpref:0≤ pref:=by dsimp [pref];positivity
  change pref*_≤ pref*D*(Ideal.absNorm L:ℝ)^ε*_
  calc
    _ ≤ pref*∑ B:actualAllocations S C,
      D*(Ideal.absNorm L:ℝ)^ε*commonPositiveChildren τ t S B C R L ν Wslot P M
        W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K := by
      apply mul_le_mul_of_nonneg_left ?_ hpref
      apply Finset.sum_le_sum
      intro B _
      have hB:= (allocation_data S C B (Finset.mem_filter.mp B.property).1).1
      have hcoeff (i:liveIndices (B:Tuple ι)) (I:Ideal O) :
          ‖ν i.val I*Wslot i.val ((Ideal.absNorm I:ℝ)/P i.val)‖≤ M i.val := by
        rw [norm_mul]
        calc
          _ ≤ 1*M i.val := mul_le_mul (hν _ _) (hWnorm _ _) (norm_nonneg _) (by norm_num)
          _ = _ := one_mul _
      have hh:=hbound (liveIndices (B:Tuple ι)) τ t
        (fun i:liveIndices (B:Tuple ι)=> S (Sum.inl i.val))
        (fun i I hI=> hp i.val I hI)
        (residualPool (B.val (Sum.inr 0)) (hB _) (S (Sum.inr 0)))
        (residualPool (B.val (Sum.inr 1)) (hB _) (S (Sum.inr 1)))
        (R*C) L hL (fun i=>ν i.val) (fun i=> Wslot i.val) (fun i=> P i.val) (fun i=> M i.val)
        (fun i=> hP i.val) (fun i=>(hM i.val).trans' zero_le_one) (fun i I _=> hcoeff i I)
        W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T (B₁*B.val (Sum.inr 0)) (B₂*B.val (Sum.inr 1))
        (mul_ne_zero hB₁ (hB _)) (mul_ne_zero hB₂ (hB _)) hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT
        (plainCoverage_residualPool _ W₁ B₁ _ (hB _) X₁ Y₁ hcov₁)
        (plainCoverage_residualPool _ W₂ B₂ _ (hB _) X₂ Y₂ hcov₂) keep Φ K hK hΦ
      dsimp only at hh
      rw [remainingRaw_source B hB B₁ B₂ hB₁ hB₂ T P,liveBox_original_pools]
      exact hh
    _ = _ := by rw [←Finset.mul_sum];ring

def CanonicalBound (ι : Type*) [Fintype ι] [DecidableEq ι] (D ε : ℝ) : Prop :=
∀ (τ : Character)
      (S : (ι⊕Fin 2)→Finset (Ideal O)),
      (∀ j,∀ I∈S j,I≠0) → (∀ i,∀ I∈S (Sum.inl i),Prime I) →
      ∀ (C R s : Ideal O) (hC : Supported C),s∣C →
      ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0< P i) → (∀ i I,‖ν i I‖≤1) → (∀ i x,‖Wslot i x‖≤ M i) → (∀ i,1≤ M i) →
      ∀ (a b : ℝ),0< a → (∀ i,Function.support (Wslot i)⊆Set.Icc a b) →
      ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ L : Ideal O),
      B₁≠0 → B₂≠0 → Squarefree L →
      Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0< X₁ → 0< X₂ → 0< Y₁ → 0< Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage (S (Sum.inr 0)) W₁ B₁ X₁ Y₁ →
      PlainCoverage (S (Sum.inr 1)) W₂ B₂ X₂ Y₂ →
      ∀ (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ),0< K →
      (∀ z:O,0≤(Φ (‖ringComplex z‖^2/K)).re) →
      let Q:=finiteColumns (Fintype.piFinset S)
      let β:=finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
      let raw:=T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      sourceRestrictedEnergy keep (residualPool C hC.1 Q)
        (fun I=> if IsCoprime C I ∧ L∣I then β (C*I) else 0)
        (heightCoeff τ t) Φ K/(raw*∏ i,P i)≤
        ((actualAllocations S C).card:ℝ)*
          (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))*
          D*(Ideal.absNorm L:ℝ)^ε*
          ∑ B:actualAllocations S C,
            commonPositiveChildren τ t S B C R L ν Wslot P M W₁ W₂
              b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K

theorem uniform_canonical_source_to_positive (ε : ℝ) (hε : 0<ε) :
    ∃ D:ℝ,0< D ∧ ∀ J:Finset ι,CanonicalBound J D ε := by
  have hex (J:Finset ι):∃ D:ℝ,0< D ∧ CanonicalBound J D ε:=by
    simpa only [CanonicalBound] using canonical_source_to_positive (ι:=J) ε hε
  choose D hD hbound using hex
  let E:ℝ:=1+∑ J:Finset ι,D J
  have hs:0≤∑ J:Finset ι,D J:=Finset.sum_nonneg (fun J _=>(hD J).le)
  have hE:0< E:=by dsimp [E];linarith
  have hDE (J:Finset ι):D J≤ E:=by
    have hh:=Finset.single_le_sum (fun J _=>(hD J).le) (Finset.mem_univ J)
    dsimp [E];linarith
  refine ⟨E,hE,?_⟩
  intro J τ S hS hp C R s hC hsC ν Wslot P M hP hν hWnorm hM a b ha hslot
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ L hB₁ hB₂ hL hs₁ hs₂
    hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ t keep Φ K hK hΦ
  have hh:=hbound J τ S hS hp C R s hC hsC ν Wslot P M hP hν hWnorm hM a b ha hslot
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ L hB₁ hB₂ hL hs₁ hs₂
    hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ t keep Φ K hK hΦ
  refine hh.trans ?_
  have hsum:0≤∑ B:actualAllocations S C,
      commonPositiveChildren τ t S B C R L ν Wslot P M W₁ W₂
        b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K:=by
    apply Finset.sum_nonneg
    intro B _
    exact positiveChildren_nonneg (ι:=liveIndices (B.val : Tuple J)) τ t
      (fun i=> S (Sum.inl i.val)) (R*C) L (fun i=>ν i.val) (fun i=> Wslot i.val)
      (fun i=> P i.val) (fun i=> M i.val) (fun i=> hP i.val)
      W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ (B₁*B.val (Sum.inr 0)) (B₂*B.val (Sum.inr 1)) keep Φ K hΦ
  apply mul_le_mul_of_nonneg_right ?_ hsum
  apply mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  apply mul_le_mul_of_nonneg_left (hDE J)
  positivity

end CenteredMomentCanonicalRetainedSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentActiveCanonicalSource
open CenteredMomentActiveAllocation
open CanonicalQuadraticSieve CenteredMomentFirstSectors
open HeckeFamily  CenteredMomentSecondHeightFamily
open CenteredMomentSourceRectangle CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRaw
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationLiveMask CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CenteredMomentCommonRawScale CenteredMomentRestrictedSourceNormalization
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def positiveChildren (η : Character) (t : ℝ) (slots : ι→Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑ a ∈ activeAllocations η (fixedBadMask*cubicIdealGenerator R) 1 t slots
    (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) L W₁ W₂
    (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂) (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂),
    ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P)*
      ∑' z:O,(if keep z then (Φ (‖ringComplex z‖^2/K)).re else 0)*
        (‖allocatedPositiveRow η (fixedBadMask*cubicIdealGenerator R) 1 z t slots
          (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P L a W₁ W₂
          (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
         ‖allocatedPositiveRow η (fixedBadMask*cubicIdealGenerator R) 1 z t slots
          (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P L a W₁ W₂
          (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2)

theorem positiveChildren_nonneg (η : Character) (t : ℝ) (slots : ι→Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
    (hP : ∀ i,0< P i) (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hΦ : ∀ z:O,0≤(Φ (‖ringComplex z‖^2/K)).re) :
    0≤ positiveChildren η t slots R L ν Wslot P M W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K := by
  apply Finset.sum_nonneg
  intro a _
  apply mul_nonneg
  · apply div_nonneg
    · exact mul_nonneg (by positivity) (sq_nonneg _)
    · exact (mul_pos (selectedNorm_pos L a) (Finset.prod_pos (fun i _=> hP i))).le
  · apply tsum_nonneg
    intro z
    apply mul_nonneg
    · split_ifs;exact hΦ z;exact le_rfl
    · exact add_nonneg (sq_nonneg _) (sq_nonneg _)

def SmoothedBound (ι : Type*) [Fintype ι] [DecidableEq ι] (D ε : ℝ) : Prop :=
∀ (η : Character) (t : ℝ)
      (slots : ι→Finset (Ideal O)),(∀ i,∀ I∈slots i,Prime I) →
    ∀ (S₁ S₂ : Finset (Ideal O)) (R L : Ideal O),Squarefree L →
    ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0< P i) → (∀ i,0≤ M i) →
      (∀ i,∀ I∈slots i,‖ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)‖≤ M i) →
    ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O),
      B₁≠0 → B₂≠0 → Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0< X₁ → 0< X₂ → 0< Y₁ → 0< Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage S₁ W₁ B₁ X₁ Y₁ → PlainCoverage S₂ W₂ B₂ X₂ Y₂ →
    ∀(keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ),0< K →
      (∀z:O,0≤(Φ (‖ringComplex z‖^2/K)).re) →
      let Q := finiteColumns (tuplePool slots S₁ S₂)
      let β := finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L)
      let raw := T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      sourceRestrictedEnergy keep Q β (heightCoeff η t) Φ K/(raw*∏i,P i)≤
      D*(Ideal.absNorm L:ℝ)^ε*
        positiveChildren η t slots R L ν Wslot P M W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K

theorem uniform_smoothed_bound (ε : ℝ) (hε : 0<ε) :
    ∃ D:ℝ,0< D ∧ ∀ J:Finset ι,SmoothedBound J D ε := by
  have hex (J:Finset ι) : ∃ D:ℝ,0< D ∧ SmoothedBound J D ε := by
    simpa only [SmoothedBound,positiveChildren] using
      CenteredMomentActiveSmoothedSource.source_plain_to_active_smoothed
        (ι:=J) (Fintype.card ι) (by simpa using Finset.card_le_univ J) ε hε
  choose D hD hbound using hex
  let C:ℝ:=1+∑ J:Finset ι,D J
  have hs:0≤∑ J:Finset ι,D J:=Finset.sum_nonneg (fun J _=>(hD J).le)
  have hC:0< C:=by dsimp [C];linarith
  have hDC (J:Finset ι):D J≤ C:=by
    have hh:=Finset.single_le_sum (fun J _=>(hD J).le) (Finset.mem_univ J)
    dsimp [C];linarith
  refine ⟨C,hC,?_⟩
  intro J η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ keep Φ K hK hΦ
  have hh:=hbound J η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ keep Φ K hK hΦ
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hDC J) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (positiveChildren_nonneg η t slots R L ν Wslot P M hP W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K hΦ))

omit [DecidableEq ι] in

def commonPositiveChildren (τ : Character) (t : ℝ)
    (S : (ι⊕Fin 2)→Finset (Ideal O)) (B : Tuple ι) (C R L : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  positiveChildren τ t (fun i:liveIndices B=> S (Sum.inl i.val)) (R*C) L
    (fun i=>ν i.val) (fun i=> Wslot i.val) (fun i=> P i.val) (fun i=> M i.val)
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) keep Φ K

local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem canonical_source_to_positive (ε : ℝ) (hε : 0<ε) :
    ∃ D:ℝ,0< D ∧ ∀ (τ : Character)
      (S : (ι⊕Fin 2)→Finset (Ideal O)),
      (∀ j,∀ I∈S j,I≠0) → (∀ i,∀ I∈S (Sum.inl i),Prime I) →
      ∀ (C R s : Ideal O) (hC : Supported C),s∣C →
      ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0< P i) → (∀ i I,‖ν i I‖≤1) → (∀ i x,‖Wslot i x‖≤ M i) → (∀ i,1≤ M i) →
      ∀ (a b : ℝ),0< a → (∀ i,Function.support (Wslot i)⊆Set.Icc a b) →
      ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ L : Ideal O),
      B₁≠0 → B₂≠0 → Squarefree L →
      Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0< X₁ → 0< X₂ → 0< Y₁ → 0< Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage (S (Sum.inr 0)) W₁ B₁ X₁ Y₁ →
      PlainCoverage (S (Sum.inr 1)) W₂ B₂ X₂ Y₂ →
      ∀ (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ),0< K →
      (∀ z:O,0≤(Φ (‖ringComplex z‖^2/K)).re) →
      let Q:=finiteColumns (Fintype.piFinset S)
      let β:=finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
      let raw:=T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      sourceRestrictedEnergy keep (residualPool C hC.1 Q)
        (fun I=> if IsCoprime C I ∧ L∣I then β (C*I) else 0)
        (heightCoeff τ t) Φ K/(raw*∏ i,P i)≤
        ((actualAllocations S C).card:ℝ)*
          (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))*
          D*(Ideal.absNorm L:ℝ)^ε*
          ∑ B:actualAllocations S C,
            commonPositiveChildren τ t S B C R L ν Wslot P M W₁ W₂
              b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K := by
  obtain ⟨D,hD,hbound⟩:=uniform_smoothed_bound (ι:=ι) ε hε
  refine ⟨D,hD,?_⟩
  intro τ S hS hp C R s hC hsC ν Wslot P M hP hν hWnorm hM a b ha hslot
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ L hB₁ hB₂ hL hs₁ hs₂
    hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ t keep Φ K hK hΦ
  dsimp only
  have hbn (I:Ideal O) (hI:I≠0):(0:ℝ)< Ideal.absNorm I:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hraw:0< T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂):=
    div_pos (hXT ▸ mul_pos hX₁ hX₂) (mul_pos (hbn B₁ hB₁) (hbn B₂ hB₂))
  have hcommon:=CenteredMomentSecondSourceCost.source_divisor_common_saving τ S hS hp C R s hC hsC
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L t _ hraw hP M hν hWnorm hM a b ha hslot keep Φ K hK hΦ
  dsimp only at hcommon
  refine hcommon.trans ?_
  let pref:ℝ:=((actualAllocations S C).card:ℝ)*
    (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))
  have hpref:0≤ pref:=by dsimp [pref];positivity
  change pref*_≤ pref*D*(Ideal.absNorm L:ℝ)^ε*_
  calc
    _ ≤ pref*∑ B:actualAllocations S C,
      D*(Ideal.absNorm L:ℝ)^ε*commonPositiveChildren τ t S B C R L ν Wslot P M
        W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K := by
      apply mul_le_mul_of_nonneg_left ?_ hpref
      apply Finset.sum_le_sum
      intro B _
      have hB:= (allocation_data S C B (Finset.mem_filter.mp B.property).1).1
      have hcoeff (i:liveIndices (B:Tuple ι)) (I:Ideal O) :
          ‖ν i.val I*Wslot i.val ((Ideal.absNorm I:ℝ)/P i.val)‖≤ M i.val := by
        rw [norm_mul]
        calc
          _ ≤ 1*M i.val := mul_le_mul (hν _ _) (hWnorm _ _) (norm_nonneg _) (by norm_num)
          _ = _ := one_mul _
      have hh:=hbound (liveIndices (B:Tuple ι)) τ t
        (fun i:liveIndices (B:Tuple ι)=> S (Sum.inl i.val))
        (fun i I hI=> hp i.val I hI)
        (residualPool (B.val (Sum.inr 0)) (hB _) (S (Sum.inr 0)))
        (residualPool (B.val (Sum.inr 1)) (hB _) (S (Sum.inr 1)))
        (R*C) L hL (fun i=>ν i.val) (fun i=> Wslot i.val) (fun i=> P i.val) (fun i=> M i.val)
        (fun i=> hP i.val) (fun i=>(hM i.val).trans' zero_le_one) (fun i I _=> hcoeff i I)
        W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T (B₁*B.val (Sum.inr 0)) (B₂*B.val (Sum.inr 1))
        (mul_ne_zero hB₁ (hB _)) (mul_ne_zero hB₂ (hB _)) hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT
        (plainCoverage_residualPool _ W₁ B₁ _ (hB _) X₁ Y₁ hcov₁)
        (plainCoverage_residualPool _ W₂ B₂ _ (hB _) X₂ Y₂ hcov₂) keep Φ K hK hΦ
      dsimp only at hh
      rw [remainingRaw_source B hB B₁ B₂ hB₁ hB₂ T P,CenteredMomentCanonicalRetainedSource.liveBox_original_pools]
      exact hh
    _ = _ := by rw [←Finset.mul_sum];ring

def CanonicalBound (ι : Type*) [Fintype ι] [DecidableEq ι] (D ε : ℝ) : Prop :=
∀ (τ : Character)
      (S : (ι⊕Fin 2)→Finset (Ideal O)),
      (∀ j,∀ I∈S j,I≠0) → (∀ i,∀ I∈S (Sum.inl i),Prime I) →
      ∀ (C R s : Ideal O) (hC : Supported C),s∣C →
      ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0< P i) → (∀ i I,‖ν i I‖≤1) → (∀ i x,‖Wslot i x‖≤ M i) → (∀ i,1≤ M i) →
      ∀ (a b : ℝ),0< a → (∀ i,Function.support (Wslot i)⊆Set.Icc a b) →
      ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ L : Ideal O),
      B₁≠0 → B₂≠0 → Squarefree L →
      Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0< X₁ → 0< X₂ → 0< Y₁ → 0< Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage (S (Sum.inr 0)) W₁ B₁ X₁ Y₁ →
      PlainCoverage (S (Sum.inr 1)) W₂ B₂ X₂ Y₂ →
      ∀ (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ),0< K →
      (∀ z:O,0≤(Φ (‖ringComplex z‖^2/K)).re) →
      let Q:=finiteColumns (Fintype.piFinset S)
      let β:=finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
      let raw:=T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      sourceRestrictedEnergy keep (residualPool C hC.1 Q)
        (fun I=> if IsCoprime C I ∧ L∣I then β (C*I) else 0)
        (heightCoeff τ t) Φ K/(raw*∏ i,P i)≤
        ((actualAllocations S C).card:ℝ)*
          (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))*
          D*(Ideal.absNorm L:ℝ)^ε*
          ∑ B:actualAllocations S C,
            commonPositiveChildren τ t S B C R L ν Wslot P M W₁ W₂
              b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K

theorem uniform_canonical_source_to_positive (ε : ℝ) (hε : 0<ε) :
    ∃ D:ℝ,0< D ∧ ∀ J:Finset ι,CanonicalBound J D ε := by
  have hex (J:Finset ι):∃ D:ℝ,0< D ∧ CanonicalBound J D ε:=by
    simpa only [CanonicalBound] using canonical_source_to_positive (ι:=J) ε hε
  choose D hD hbound using hex
  let E:ℝ:=1+∑ J:Finset ι,D J
  have hs:0≤∑ J:Finset ι,D J:=Finset.sum_nonneg (fun J _=>(hD J).le)
  have hE:0< E:=by dsimp [E];linarith
  have hDE (J:Finset ι):D J≤ E:=by
    have hh:=Finset.single_le_sum (fun J _=>(hD J).le) (Finset.mem_univ J)
    dsimp [E];linarith
  refine ⟨E,hE,?_⟩
  intro J τ S hS hp C R s hC hsC ν Wslot P M hP hν hWnorm hM a b ha hslot
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ L hB₁ hB₂ hL hs₁ hs₂
    hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ t keep Φ K hK hΦ
  have hh:=hbound J τ S hS hp C R s hC hsC ν Wslot P M hP hν hWnorm hM a b ha hslot
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ L hB₁ hB₂ hL hs₁ hs₂
    hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ t keep Φ K hK hΦ
  refine hh.trans ?_
  have hsum:0≤∑ B:actualAllocations S C,
      commonPositiveChildren τ t S B C R L ν Wslot P M W₁ W₂
        b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K:=by
    apply Finset.sum_nonneg
    intro B _
    exact positiveChildren_nonneg (ι:=liveIndices (B.val : Tuple J)) τ t
      (fun i=> S (Sum.inl i.val)) (R*C) L (fun i=>ν i.val) (fun i=> Wslot i.val)
      (fun i=> P i.val) (fun i=> M i.val) (fun i=> hP i.val)
      W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ (B₁*B.val (Sum.inr 0)) (B₂*B.val (Sum.inr 1)) keep Φ K hΦ
  apply mul_le_mul_of_nonneg_right ?_ hsum
  apply mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  apply mul_le_mul_of_nonneg_left (hDE J)
  positivity

end CenteredMomentActiveCanonicalSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentCommonRadialData
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentSourceRectangle CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationLiveMask CenteredMomentAddedZeroUniform CenteredMomentCommonRawScale
open CenteredMomentRestrictedSource CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow
open CenteredMomentFirstSectors  CanonicalQuadraticSieve
local notation "O" => Eisenstein.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

structure Input (ι:Type*) [Fintype ι] extends Data ι where
  plain₁ : Finset (Ideal O)
  plain₂ : Finset (Ideal O)
  plain₁_ne : ∀I∈plain₁,I≠0
  plain₂_ne : ∀I∈plain₂,I≠0
  coverage₁ : PlainCoverage plain₁ W₁ 1 X₁ Y₁
  coverage₂ : PlainCoverage plain₂ W₂ 1 X₂ Y₂
  ν_bound : ∀i I,‖ν i I‖≤1
  W_bound : ∀i x,‖W i x‖≤ M i
  lower : ℝ
  upper : ℝ
  lower_pos : 0< lower
  lower_le : ∀i,lower≤ lo i
  upper_ge : ∀i,hi i≤ upper

 def Input.pools (s:Input ι) : (ι⊕Fin 2)→Finset (Ideal O) :=
  Sum.elim s.slots (fun j=> if j=0 then s.plain₁ else s.plain₂)

omit [DecidableEq ι] in
lemma Input.pools_ne (s:Input ι) (j:ι⊕Fin 2) : ∀I∈s.pools j,I≠0 := by
  cases j with
  | inl i => exact fun I hI=>(s.prime i I hI).ne_zero
  | inr j =>
    fin_cases j
    · simpa [Input.pools] using s.plain₁_ne
    · simpa [Input.pools] using s.plain₂_ne

omit [DecidableEq ι] in
lemma Input.slot_support (s:Input ι) (i:ι) : Function.support (s.W i)⊆Set.Icc s.lower s.upper :=
  fun _x hx=>⟨(s.lower_le i).trans (s.support i hx).1,((s.support i hx).2).trans (s.upper_ge i)⟩

omit [DecidableEq ι] in
lemma alloc_ne (s:Input ι) (C:Ideal O) (B:actualAllocations s.pools C)
    (j:ι⊕Fin 2) : B.val j≠0 :=
  (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1 j

omit [DecidableEq ι] in
lemma alloc_norm_pos (s:Input ι) (C:Ideal O) (B:actualAllocations s.pools C)
    (j:ι⊕Fin 2) : (0:ℝ)< Ideal.absNorm (B.val j) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (alloc_ne s C B j))

 def commonData (s:Input ι) (C R:Ideal O) (B:actualAllocations s.pools C) : Data (liveIndices B.val) where
  η:=s.η
  m:=fixedBadMask*cubicIdealGenerator (R*C)
  A:=1
  t:=s.t
  slots:=fun i=> s.slots i.val
  prime:=fun i I hI=> s.prime i.val I hI
  ν:=fun i=> s.ν i.val
  W:=fun i=> s.W i.val
  lo:=fun i=> s.lo i.val
  hi:=fun i=> s.hi i.val
  P:=fun i=> s.P i.val
  lo_pos:=fun i=> s.lo_pos i.val
  P_pos:=fun i=> s.P_pos i.val
  support:=fun i=> s.support i.val
  W₁:=s.W₁
  W₂:=s.W₂
  X₁:=s.X₁/Ideal.absNorm (B.val (Sum.inr 0))
  X₂:=s.X₂/Ideal.absNorm (B.val (Sum.inr 1))
  Y₁:=s.Y₁/Ideal.absNorm (B.val (Sum.inr 0))
  Y₂:=s.Y₂/Ideal.absNorm (B.val (Sum.inr 1))
  M:=fun i=> s.M i.val
  M_ge_one:=fun i=> s.M_ge_one i.val
  coefficient_bound:=fun i I hI=> s.coefficient_bound i.val I hI
  b₁:=s.b₁
  b₂:=s.b₂
  support₁:=s.support₁
  support₂:=s.support₂
  X₁_pos:=div_pos s.X₁_pos (alloc_norm_pos s C B _)
  X₂_pos:=div_pos s.X₂_pos (alloc_norm_pos s C B _)
  Y₁_pos:=div_pos s.Y₁_pos (alloc_norm_pos s C B _)
  Y₂_pos:=div_pos s.Y₂_pos (alloc_norm_pos s C B _)
  same_product:=by rw [div_mul_div_comm,div_mul_div_comm,s.same_product]
  rows:=∅
  weight:=fun _=>0
  weight_nonneg:=by simp

omit [DecidableEq ι] in
lemma common_profile_le (s:Input ι) (C R:Ideal O) (B:actualAllocations s.pools C) :
    (commonData s C R B).profileFactor≤ s.toData.profileFactor := by
  unfold Data.profileFactor
  change (2*(max 1 s.b₁*max 1 s.b₂))*(∏i:liveIndices B.val,s.M i.val)^2≤ _
  rw [Finset.prod_coe_sort]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀ (Finset.prod_nonneg (fun i _=> zero_le_one.trans (s.M_ge_one i)))
  exact Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _)
    (fun i _=> zero_le_one.trans (s.M_ge_one i)) (fun i _ _=> s.M_ge_one i)

end CenteredMomentCommonRadialData

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

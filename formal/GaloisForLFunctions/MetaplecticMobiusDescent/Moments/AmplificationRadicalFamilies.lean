/-
Amplification radical families adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.FirstAnnularInputs

/-!
# Amplification radical families

Radical bounds and error indices of the amplification choice, eventually dyadic amplification
and active factors; retained nominal frequencies and the actual first saving.
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

namespace CenteredMomentAmplificationFamilyEnergy
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion
open  CompletedGauss RayFourExpansion
open CenteredMomentAmplificationShortening CenteredMomentAmplificationFamily
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow
open CenteredMomentSourceRow CenteredMomentChildRows CenteredMomentOriginalChildEnergy
open CenteredMomentGaussEnergy CenteredMomentSourceSmoothedAllocation CenteredMomentGaussNormalization
local notation "O" => Eisenstein.O

theorem amplification_family_energy (η : Character) (m p : O) (k : ℕ)
    (τ : RayCharacter → Character)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      rowWeight η m 1 1 t I*residualCharacter p k (primaryIdealGenerator I)=
        ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I)
    (Q : Finset (Ideal O)) (C : Ideal O) (hC : C≠0) (β : Ideal O → ℂ) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K)
    (hW : ∀ z : O,0≤(W (‖ringComplex z‖^2/K)).re) :
    (sourceGaussEnergy Q (fun I => β (C*I)*rowWeight η m 1 1 t (C*I))
      (fun I => residualCharacter p k (primaryIdealGenerator I)) W K).re≤
      16*∑ χ : RayCharacter,
        (sourceGaussEnergy Q (fun I => β (C*I)) (heightCoeff (τ χ) t) W K).re := by
  let b : RayCharacter → ℂ := fun χ => rowWeight η m 1 1 t C*phaseCoeff (amplificationPhase p k) χ
  let d : RayCharacter → supportedColumns Q → ℂ := fun χ I => β (C*I)*heightCoeff (τ χ) t I
  have he (I : supportedColumns Q) :
      (β (C*I)*rowWeight η m 1 1 t (C*I))*residualCharacter p k (primaryIdealGenerator I)=
        ∑ χ,b χ*d χ I := by
    rw [original_column_family η m p k τ hτ C I (Finset.mem_filter.mp I.property).2 β t,Finset.mul_sum]
    simp only [b,d,mul_assoc]
  have hb (χ : RayCharacter) : ‖b χ‖≤1 := by
    dsimp only [b]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (CenteredMomentAbsoluteEnergy.rowWeight_norm_le_one_all η m 1 1 t C)).trans
      (phaseCoeff_norm_le _ 1 (fun u => amplificationPhase_norm p k u) χ)
  have hd (χ : RayCharacter) : 0≤(sourceGaussEnergy Q (fun I => β (C*I)) (heightCoeff (τ χ) t) W K).re :=
    sourceGaussEnergy_nonneg _ _ _ W K hK hW
  have hh := smoothed_allocation_energy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) b d W K hK hW
  change (gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) _ W K).re≤ _
  rw [funext he]
  apply hh.trans
  apply mul_le_mul
  · exact_mod_cast rayCharacter_card_le
  · apply Finset.sum_le_sum
    intro χ hχ
    apply mul_le_of_le_one_left (hd χ)
    nlinarith [hb χ,norm_nonneg (b χ)]
  · exact Finset.sum_nonneg (fun χ _ => mul_nonneg (sq_nonneg _) (hd χ))
  · norm_num

theorem exists_amplification_energy_family (η : Character) (m p : O)
    (hm : m≠0) (hp : p≠0) (hs : Supported (Ideal.span {p}))
    (hpp : lambda^2 ∣ p-1) (hmLam : lambda∣m) (hm2 : (2:O)∣m) (k : ℕ) :
    ∃ τ : RayCharacter → Character,
      (∀ χ, (τ χ).modulus.absNorm≤ rowConductorBound (childCharacter η χ) m 1 (p^(2*k))) ∧
      ∀ (Q : Finset (Ideal O)) (C : Ideal O),C≠0 → ∀ (β : Ideal O → ℂ) (t : ℝ)
        (W : 𝓢(ℝ,ℂ)) (K : ℝ),0< K →
      (∀ z : O,0≤(W (‖ringComplex z‖^2/K)).re) →
      (sourceGaussEnergy Q (fun I => β (C*I)*rowWeight η m 1 1 t (C*I))
        (fun I => residualCharacter p k (primaryIdealGenerator I)) W K).re≤
        16*∑ χ : RayCharacter,
          (sourceGaussEnergy Q (fun I => β (C*I)) (heightCoeff (τ χ) t) W K).re := by
  obtain ⟨τ,hN,hτ⟩ := exists_amplification_family η m p hm hp hs hpp hmLam hm2 k
  exact ⟨τ,hN,fun Q C hC β t W K hK hW => amplification_family_energy η m p k τ hτ Q C hC β t W K hK hW⟩

end CenteredMomentAmplificationFamilyEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentAmplificationActiveFactor
open CanonicalQuadraticSieve CanonicalRowCompletion  CompletedGauss
open CenteredMomentAmplificationShortening CenteredMomentSupportedCorrelation
open CenteredMomentAmplificationSourceDomain CenteredMomentAmplificationSourcePool
open CenteredMomentSourceRow
local notation "O" => Eisenstein.O

theorem residual_six_unit (p u : O)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hcop : IsCoprime p u) : residualCharacter p 6 u=residualCharacter p 0 u := by
  have hp' := (supported_iff_native _).mp hp
  have hx := idealRowHom_sixth_mask u (Ideal.span {p}) hp'
  rw [idealRowHom_argument_pow u 6 _ hp'.1,Ideal.isCoprime_span_singleton_iff,if_pos hcop] at hx
  have hphase := supported_phase_sq p u hp hu
  unfold residualCharacter
  norm_num only
  calc
    _ = (sexticReciprocityPhase p u^2)^3*(idealRowHom u (Ideal.span {p})^6)^2 := by ring
    _ = 1 := by rw [hphase,hx];norm_num
    _ = _ := by simp

theorem residual_seven_unit (p u : O)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hcop : IsCoprime p u) : residualCharacter p 7 u=residualCharacter p 1 u := by
  have hp' := (supported_iff_native _).mp hp
  have hx := idealRowHom_sixth_mask u (Ideal.span {p}) hp'
  rw [idealRowHom_argument_pow u 6 _ hp'.1,Ideal.isCoprime_span_singleton_iff,if_pos hcop] at hx
  have hphase := supported_phase_sq p u hp hu
  unfold residualCharacter
  norm_num only
  calc
    _ = (sexticReciprocityPhase p u^2)^3*sexticReciprocityPhase p u*
        (idealRowHom u (Ideal.span {p})^6)^2*idealRowHom u (Ideal.span {p})^2 := by ring
    _ = _ := by rw [hphase,hx];ring

theorem error_residual_factor (p u : O)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hcop : IsCoprime p u) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    residualCharacter p (n+1) u=residualCharacter p (errorMovingExponent n) u := by
  rcases hn with rfl|rfl|rfl
  · rfl
  · exact residual_six_unit p u hp hu hcop
  · exact residual_seven_unit p u hp hu hcop

theorem residualColumns_coprime (S : Finset (Ideal O)) (p : O) (hp : Prime p)
    (k : ℕ) (I : Ideal O) (hI : I∈residualColumns S p hp k) :
    IsCoprime (Ideal.span {p}) I := by
  obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
  exact residualIdeal_coprime p hp J (valuationColumns_supported S p k J hJ)

theorem residual_column_active (S : Finset (Ideal O)) (p : O) (hp : Prime p)
    (hs : Supported (Ideal.span {p})) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6)
    (I : Ideal O) (hI : I∈residualColumns S p hp (n+1)) :
    residualCharacter p (n+1) (primaryIdealGenerator I)=
      residualCharacter p (errorMovingExponent n) (primaryIdealGenerator I) := by
  have hsI := residualColumns_supported S p hp (n+1) I hI
  apply error_residual_factor p _ hs _ _ n hn
  · rw [primary_span_supported I hsI];exact hsI
  · apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [primary_span_supported I hsI]
    exact residualColumns_coprime S p hp (n+1) I hI

end CenteredMomentAmplificationActiveFactor

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentAmplificationActiveFamily
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion
open  CompletedGauss RayFourExpansion
open CenteredMomentAmplificationShortening CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationFamilyEnergy CenteredMomentAmplificationSourceDomain
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentSourceRow CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy
local notation "O" => Eisenstein.O

 theorem actual_error_energy_active (S : Finset (Ideal O)) (p : O) (hp : Prime p)
    (hs : Supported (Ideal.span {p})) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6)
    (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy (residualColumns S p hp (n+1)) c
      (fun I => residualCharacter p (n+1) (primaryIdealGenerator I)) W K=
    sourceGaussEnergy (residualColumns S p hp (n+1)) c
      (fun I => residualCharacter p (errorMovingExponent n) (primaryIdealGenerator I)) W K := by
  let Q := residualColumns S p hp (n+1)
  apply congrArg (fun f : supportedColumns Q → ℂ =>
    gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) f W K)
  funext I
  dsimp only
  rw [residual_column_active S p hp hs n hn I (Finset.mem_filter.mp I.property).1]

theorem exists_actual_error_family (η : Character) (m p : O)
    (hm : m≠0) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : lambda^2 ∣ p-1) (hmLam : lambda∣m) (hm2 : (2:O)∣m)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤ rowConductorBound (childCharacter η χ) m 1
        (p^(2*errorMovingExponent n))) ∧
      ∀ (S : Finset (Ideal O)) (C : Ideal O),C≠0 → ∀ (β : Ideal O → ℂ) (t : ℝ)
        (W : 𝓢(ℝ,ℂ)) (K : ℝ),0< K →
      (∀ z : O,0≤(W (‖ringComplex z‖^2/K)).re) →
      (sourceGaussEnergy (residualColumns S p hp (n+1))
        (fun I => β (C*I)*rowWeight η m 1 1 t (C*I))
        (fun I => residualCharacter p (n+1) (primaryIdealGenerator I)) W K).re≤
        16*∑ χ : RayCharacter,
          (sourceGaussEnergy (residualColumns S p hp (n+1))
            (fun I => β (C*I)) (heightCoeff (τ χ) t) W K).re := by
  obtain ⟨τ,hN,hτ⟩ := exists_amplification_energy_family η m p hm hp.ne_zero hs hpp hmLam hm2
    (errorMovingExponent n)
  refine ⟨τ,hN,?_⟩
  intro S C hC β t W K hK hW
  rw [actual_error_energy_active S p hp hs n hn]
  exact hτ (residualColumns S p hp (n+1)) C hC β t W K hK hW

end CenteredMomentAmplificationActiveFamily

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentAmplificationLiveEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentSourceRow
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
open CenteredMomentLiveSupport CenteredMomentLiveDomain CenteredMomentSourceSmoothedAllocation
open CenteredMomentOriginalChildEnergy CenteredMomentAmplificationLiveMask
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

 theorem masked_live_gaussEnergy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R s : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
    let T := finiteColumns (liveBox S B hB)
    gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q => c I*f I) W K=
      gaussEnergy Finset.univ (sourceGenerator T) (sourceGenerator_supported T)
        (fun I : supportedColumns T => c I*f I) W K := by
  dsimp only
  have he (I : Ideal O) : finiteColumnCoefficient (liveBox S B hB)
      (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I=
      finiteColumnCoefficient (liveBox S B hB)
        (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I*
          (if s∣I then 1 else 0) := column_mask _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  simp_rw [he,mul_assoc]
  exact live_gaussEnergy S hS hp B hB C R hC hlabel hprod ν Wslot P W₁ W₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ (fun I => (if s∣I then 1 else 0)*f I) W K

theorem original_masked_child_energy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsc : IsCoprime s C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (f : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K)
    (hW : ∀ z : O,0≤(W (‖ringComplex z‖^2/K)).re) :
    (sourceGaussEnergy (residualPool C hC.1 (finiteColumns (Fintype.piFinset S)))
      (fun I => if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0) f W K).re≤
      ((actualAllocations S C).card:ℝ)*∑ B : actualAllocations S C,
        ‖frozenCoefficient B C R ν Wslot P‖^2*
          (sourceGaussEnergy
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K).re := by
  let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
  let b := fun B : actualAllocations S C => frozenCoefficient B C R ν Wslot P
  let d := fun (B : actualAllocations S C) (I : supportedColumns Q) =>
    finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
      (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I*f I
  have he (I : supportedColumns Q) :
      (if IsCoprime C (I:Ideal O) then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0)*f I=
      ∑ B,b B*d B I := by
    rw [original_masked_live_column S hS hp C R s I hC.1
      (Finset.mem_filter.mp I.property).2.1 hsc ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂,Finset.sum_mul]
    simp only [b,d,mul_assoc]
  have h := smoothed_allocation_energy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) b d W K hK hW
  have he' := funext he
  change (gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) _ W K).re≤ _
  rw [he']
  apply h.trans_eq
  rw [Fintype.card_coe]
  apply congrArg (fun x : ℝ => ((actualAllocations S C).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  simpa only [b,d,sourceGaussEnergy] using
    congrArg (fun x : ℂ => ‖frozenCoefficient B C R ν Wslot P‖^2*x.re)
    (masked_live_gaussEnergy S hS hp B
    (allocation_data S C B (Finset.mem_filter.mp B.property).1).1 C R s hC
    (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ f W K)

end CenteredMomentAmplificationLiveEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentAmplificationChildEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentSourceRow
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
open CenteredMomentOriginalChildEnergy CenteredMomentAmplificationLiveMask
open CenteredMomentAmplificationLiveEnergy CenteredMomentAmplificationAllocationScale
open CenteredMomentAmplificationAllocationCost CenteredMomentGaussNormalization
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem actual_amplification_child_energy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (Q R s : Ideal O) (hQ : Prime Q) (hQs : Supported Q) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime Q I)
    (hsc : IsCoprime s (Q^k))
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (f : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K)
    (hW : ∀ z : O,0≤(W (‖ringComplex z‖^2/K)).re) :
    (sourceGaussEnergy (residualPool (Q^k) (pow_ne_zero k hQ.ne_zero) (finiteColumns (Fintype.piFinset S)))
      (fun I => if IsCoprime (Q^k) I then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) ((Q^k)*I) else 0) f W K).re≤
      (k+1:ℝ)*∑ B : actualAllocations S (Q^k),
        (sourceGaussEnergy
            (finiteColumns (liveBox S B (allocation_data S (Q^k) B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S (Q^k) B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B (Q^k) R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K).re := by
  have hsPow : ∀ n : ℕ,Supported (Q^n) := by
    intro n
    induction n with
    | zero => simpa only [pow_zero] using CenteredMomentAddedZero.supported_one_ideal
    | succ n ih => rw [pow_succ,supported_mul_iff];exact ⟨ih,hQs⟩
  have hC := hsPow k
  have he := original_masked_child_energy S hS hp (Q^k) R s hC hsc ν Wslot P
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ f W K hK hW
  let E : actualAllocations S (Q^k) → ℝ := fun B =>
    (sourceGaussEnergy
      (finiteColumns (liveBox S B (allocation_data S (Q^k) B (Finset.mem_filter.mp B.property).1).1))
      (finiteColumnCoefficient
        (liveBox S B (allocation_data S (Q^k) B (Finset.mem_filter.mp B.property).1).1)
        (maskedLiveProfile B (Q^k) R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K).re
  have hE (B : actualAllocations S (Q^k)) : 0≤ E B := sourceGaussEnergy_nonneg _ _ _ W K hK hW
  have hc : ((actualAllocations S (Q^k)).card:ℝ)≤(k+1:ℝ) := by
    exact_mod_cast actual_amplification_allocations_card S Q hQ k hslot
  have hf (B : actualAllocations S (Q^k)) :
      ‖frozenCoefficient B (Q^k) R ν Wslot P‖^2≤1 := by
    have hh := frozenCoefficient_norm_le S Q hQ.ne_zero k hslot B R ν Wslot P
    nlinarith [norm_nonneg (frozenCoefficient B (Q^k) R ν Wslot P)]
  exact he.trans (mul_le_mul (by exact hc)
    (Finset.sum_le_sum (fun B _ => mul_le_of_le_one_left (hE B) (hf B)))
    (Finset.sum_nonneg (fun B _ => mul_nonneg (sq_nonneg _) (hE B))) (by positivity))

end CenteredMomentAmplificationChildEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentAmplificationOriginalErrors
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion
open  CompletedGauss RayFourExpansion
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationActiveFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationChildEnergy CenteredMomentAmplificationErrorPool
open CenteredMomentAmplificationSourceDomain CenteredMomentOriginalChildEnergy
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentSourceRow CenteredMomentSourceLiveColumn CenteredMomentAmplificationLiveMask
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

/-- Prime extraction bounds each amplification error by the energies of its allocated children. -/
theorem original_errors_to_children (η : Character) (m p : O)
    (hm : m≠0) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hPid : Prime (Ideal.span {p})) (hs : Supported (Ideal.span {p}))
    (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (hpp : lambda^2 ∣ p-1) (hmLam : lambda∣m) (hm2 : (2:O)∣m)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤ rowConductorBound (childCharacter η χ) m 1 (p^(2*errorMovingExponent n))) ∧
      ∀ (S : (ι ⊕ Fin 2) → Finset (Ideal O)),
      (∀ i,∀ I∈S i,I≠0) → (∀ i,∀ I∈S (Sum.inl i),Prime I) →
      (∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime (Ideal.span {p}) I) →
      ∀ (R s : Ideal O),IsCoprime s ((Ideal.span {p})^(n+1)) →
      ∀ (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
        (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (t T : ℝ),0< T →
      ∀ (rows : Finset O),(∀ h∈rows,¬p∣h) →
      ∀ (W : 𝓢(ℝ,ℂ)) (K : ℝ),0< K →
      (∀ z : O,0≤(W (‖ringComplex z‖^2/K)).re) →
      (∀ z∈rows,1≤(W (‖ringComplex z‖^2/K)).re) →
      let β := finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
      let C := (Ideal.span {p})^(n+1)
      (∑ h∈rows,‖amplificationError Finset.univ
        (sourceGenerator (finiteColumns (Fintype.piFinset S)))
        (sourceGenerator_supported (finiteColumns (Fintype.piFinset S)))
        (fun I : supportedColumns (finiteColumns (Fintype.piFinset S)) =>
          (Real.sqrt T:ℂ)⁻¹*(β I*rowWeight η m 1 1 t I))
        (fun I => multiplicity p (sourceGenerator (finiteColumns (Fintype.piFinset S)) I)) p (n+1) h‖^2)≤
        (16*(n+2:ℝ)*localErrorCost p n) *
          ((∑ χ : RayCharacter,∑ B : actualAllocations S C,
            (sourceGaussEnergy
              (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
              (finiteColumnCoefficient
                (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
                (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
              (heightCoeff (τ χ) t) W K).re) /
            (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1))) := by
  obtain ⟨τ,hN,hτ⟩ := exists_actual_error_family η m p hm hp hs hpp hmLam hm2 n hn
  refine ⟨τ,hN,?_⟩
  intro S hS hprime hslot R s hsc ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ t T hT rows hrows W K hK hW hmajor
  dsimp only
  let β := finiteColumnCoefficient (Fintype.piFinset S)
    (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
  let S₀ := finiteColumns (Fintype.piFinset S)
  let C := (Ideal.span {p})^(n+1)
  let Q := residualColumns S₀ p hp (n+1)
  let T' := T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)
  have hC : C≠0 := pow_ne_zero _ hs.1
  have ht : 0< T' := by
    apply div_pos hT
    apply pow_pos
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs.1)
  have he := finite_original_error_energy S₀ (fun I => β I*rowWeight η m 1 1 t I)
    p hp hs hg hc hpp n hn T hT rows hrows W K hK hW hmajor
  have hf := hτ S₀ C hC β t W K hK hW
  have hb (χ : RayCharacter) :
      (sourceGaussEnergy Q (fun I => β (C*I)) (heightCoeff (τ χ) t) W K).re≤
        (n+2:ℝ)*∑ B : actualAllocations S C,
          (sourceGaussEnergy
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
            (heightCoeff (τ χ) t) W K).re := by
    have hpool := residual_energy_eq_punctured S₀ β (heightCoeff (τ χ) t) p hp hs hpp (n+1) (by omega) W K
    change _≤ _
    rw [hpool]
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using
      actual_amplification_child_energy S hS hprime (Ideal.span {p}) R s hPid hs (n+1)
        hslot hsc ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ (heightCoeff (τ χ) t) W K hK hW
  apply he.trans
  apply (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
    (hf.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ _ => hb χ)) (by norm_num))) ht.le)
    (localErrorCost_nonneg p n)).trans_eq
  rw [←Finset.mul_sum]
  ring

end CenteredMomentAmplificationOriginalErrors

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstExtractedLedger
open CanonicalQuadraticSieve CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentRankinRadical
open CenteredMomentFirstCanonicalAllowance CenteredMomentDescentLedger
local notation "O" => Eisenstein.O

theorem actual_extracted_first_saving (I J:Ideal O) (hI:Supported I) (hJ:Supported J)
    (Z:ℝ) (hZ:1< Z):
    let c:=Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d:=Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p:=Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R:=Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let B:=c+d-2*p-R
    ∀D₀ w q wo g ell σ δ:ℝ,0≤ w → 0≤ q → 0≤ wo → 0≤σ → 0≤δ →
      R≤ q → d-δ≤ D₀ → g≤ max (D₀-c-2*w+wo) 0+2*σ → 0≤ ell → w≤7*σ/3 →
      2*(c+w)/3-3*σ-5*δ/6≤ firstSaving c D₀ w q wo B g ell:=by
  dsimp only
  intro D₀ w q wo g ell σ δ hw hq hwo hσ hδ hR hD hg hell hwσ
  have ha:=actual_extracted_common_support_allowance I J hI hJ Z hZ
  dsimp only at ha
  have hn:(1:ℝ)≤((commonPart I J).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (commonPart_supported I J hI).1)
  have hc:0≤ Real.logb Z ((commonPart I J).absNorm:ℝ):=Real.logb_nonneg hZ hn
  have hsecond:0≤ max (3*Real.logb Z ((commonPart J I).absNorm:ℝ)-
      5*Real.logb Z ((commonPart I J).absNorm:ℝ)-
      Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) 0/6:=by positivity
  have hfirst:0≤ max (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
      5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
      Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) 0/6:=by positivity
  exact firstSaving_lower _ _ D₀ w q _ wo _ g ell σ δ hc hw hq hwo
    (by linarith) hσ hδ hR (by linarith) hD hg hell hwσ

end CenteredMomentFirstExtractedLedger

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open Filter

namespace CenteredMomentFirstAmplificationChoice
open HeckeFamily CanonicalQuadraticSieve 
open CenteredMomentSectorLocalization CenteredMomentPrimePool
open CenteredMomentPrimeElements CenteredMomentAmplificationEligibility
open CenteredMomentAmplificationEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceRow CenteredMomentGaussNormalization
open CenteredMomentAmplificationOriginalErrors CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationSlotGap
local notation "O" => Eisenstein.O


def primeTest : ContDiffBump (3/4 : ℝ) where
  rIn := 1/16
  rOut := 1/8
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem primeTest_support : Function.support primeTest ⊆ Set.Ioo (1/2) 1 := by
  intro x hx
  rw [primeTest.support_eq,Metric.mem_ball,Real.dist_eq] at hx
  change |x-3/4|<1/8 at hx
  have hh := abs_lt.mp hx
  constructor <;> linarith

theorem primeTest_tsupport : tsupport primeTest ⊆ Set.Ioi 0 := by
  intro x hx
  rw [primeTest.tsupport_eq,Metric.mem_closedBall,Real.dist_eq] at hx
  change |x-3/4|≤1/8 at hx
  have hh := abs_le.mp hx
  change 0< x
  linarith

theorem primeTest_ne_zero : (primeTest : ℝ→ℝ)≠0 := by
  have h : primeTest (3/4)=1 := primeTest.one_of_mem_closedBall
    (by simp [primeTest,Metric.mem_closedBall])
  intro hz
  have he := congrFun hz (3/4)
  change primeTest (3/4)=0 at he
  linarith

theorem eventually_log_card_power (c ell loss : ℝ)
    (hc : 0< c) (hell : 0< ell) (hloss : 0< loss) :
    ∀ᶠ Z : ℝ in atTop,
      Z^(ell-loss)≤ c*Z^ell/Real.log (Z^ell) := by
  have hb := (isLittleO_log_rpow_atTop hloss).bound (div_pos hc hell)
  filter_upwards [hb,eventually_gt_atTop (1:ℝ)] with Z hbound hZ
  have hz : 0< Z := zero_lt_one.trans hZ
  have hlog : 0< Real.log Z := Real.log_pos hZ
  have hpow : 0< Z^loss := Real.rpow_pos_of_pos hz _
  have hh : ell*Real.log Z≤ c*Z^loss := by
    have hh' : Real.log Z≤(c/ell)*Z^loss := by
      simpa only [Real.norm_eq_abs,abs_of_pos hlog,abs_of_pos hpow] using hbound
    calc
      _ ≤ ell*((c/ell)*Z^loss) := mul_le_mul_of_nonneg_left hh' hell.le
      _ = _ := by field_simp
  rw [Real.log_rpow hz]
  apply (le_div_iff₀ (mul_pos hell hlog)).mpr
  calc
    _ ≤ Z^(ell-loss)*(c*Z^loss) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hz.le _)
    _ = _ := by rw [mul_left_comm,←Real.rpow_add hz,sub_add_cancel]

section Pool
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

include hH

theorem eventually_actual_pool_card (Sbad : Finset (Ideal O))
    (ell loss : ℝ) (hell : 0< ell) (hloss : 0< loss) :
    ∀ᶠ Z : ℝ in atTop,
      Z^(ell-loss)≤(primePool M H Sbad (1/2) 1 (Z^ell)).card := by
  obtain ⟨c,hc,hcard⟩ := eventually_primePool_card M H hH Sbad primeTest
    primeTest.contDiff primeTest.hasCompactSupport primeTest_tsupport
    (fun _ => primeTest.nonneg) primeTest_ne_zero (1/2) 1 1
    (by norm_num) (by norm_num) (by norm_num) primeTest_support (fun _ => primeTest.le_one)
  filter_upwards [(tendsto_rpow_atTop hell).eventually hcard,
    eventually_log_card_power c ell loss hc hell hloss] with Z hcard hpower
  exact hpower.trans hcard

theorem eventually_actual_pool (Sbad : Finset (Ideal O))
    (hbad : fixedBadPrimes⊆Sbad) (ell loss cap b eta : ℝ)
    (hell : 0< ell) (hloss : 0< loss) (hgap : eta< ell/2) :
    ∀ᶠ Z : ℝ in atTop,
      1< Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^ell)
      P.Nonempty ∧ Z^(ell-loss)≤(P.card:ℝ) ∧
      2*(cap/(ell/2))≤(P.card:ℝ) ∧ b*Z^eta< Z^(ell/2) ∧
      ∀ Q∈P,Prime Q ∧ Q∉fixedBadPrimes ∧
        Z^(ell/2)≤(Ideal.absNorm Q:ℝ) ∧ (Ideal.absNorm Q:ℝ)≤ Z^ell := by
  have he : 0< ell/2 := by linarith
  filter_upwards [eventually_actual_pool_card M H hH Sbad ell loss hell hloss,
    eventually_actual_pool_card M H hH Sbad ell (ell/2) hell he,
    (tendsto_rpow_atTop he).eventually (eventually_ge_atTop (2:ℝ)),
    (tendsto_rpow_atTop he).eventually (eventually_ge_atTop (2*(cap/(ell/2)))),
    eventually_scale_gap b eta (ell/2) hgap,eventually_gt_atTop (1:ℝ)]
    with Z hcard hlarge htwo hcap hslot hZ
  have hz : 0< Z := zero_lt_one.trans hZ
  have hlarge' : Z^(ell/2)≤(primePool M H Sbad (1/2) 1 (Z^ell)).card := by
    simpa only [show ell-ell/2=ell/2 by ring] using hlarge
  have hp : (primePool M H Sbad (1/2) 1 (Z^ell)).Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (Real.rpow_pos_of_pos hz (ell/2)).trans_le hlarge'
  refine ⟨hZ,hp,hcard,hcap.trans hlarge',hslot.2,?_⟩
  intro Q hQ
  have hdata := primePool_data M H Sbad hbad (1/2) 1 (Z^ell) Q hQ
  have hn := PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)
    (Real.rpow_pos_of_pos hz ell) (Finset.mem_sdiff.mp hQ).1
  have hs : Z^ell=(Z^(ell/2))^2 := by
    rw [←Real.rpow_mul_natCast hz.le]
    congr 1
    ring
  refine ⟨hdata.1,hdata.2,?_,?_⟩
  · rw [hs] at hn
    nlinarith [sq_nonneg (Z^(ell/2)-2)]
  · simpa only [mul_one] using hn.2

omit hH in
theorem reciprocal_pool_bound (Sbad : Finset (Ideal O)) (ell loss Z : ℝ)
    (hZ : 0< Z)
    (hc : Z^(ell-loss)≤(primePool M H Sbad (1/2) 1 (Z^ell)).card) :
    ((primePool M H Sbad (1/2) 1 (Z^ell)).card:ℝ)⁻¹≤ Z^(-ell+loss) := by
  have hp := Real.rpow_pos_of_pos hZ (ell-loss)
  have he := (inv_le_inv₀ (hp.trans_le hc) hp).mpr hc
  simpa only [←Real.rpow_neg hZ.le,show -(ell-loss)=-ell+loss by ring] using he

end Pool

def dyadRows (n : ℤ) : Finset O :=
  (Eisenstein.finite_norm_sublevel (Real.sqrt (dyadicScale n))).toFinset.filter
    (fun h => dyadicWeight n (normValue h)≠0)

@[simp] theorem mem_dyadRows (n : ℤ) (h : O) :
    h∈dyadRows n ↔ dyadicWeight n (normValue h)≠0 := by
  constructor
  · exact fun hh => (Finset.mem_filter.mp hh).2
  · intro hh
    refine Finset.mem_filter.mpr ⟨?_,hh⟩
    rw [Set.Finite.mem_toFinset]
    change ‖ringComplex h‖ ≤ Real.sqrt (dyadicScale n)
    calc
      _ = Real.sqrt (‖ringComplex h‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by
        rw [←normValue_eq_embedding]
        exact (dyadicWeight_support n hh).2.le)

theorem dyadRows_ne_zero (n : ℤ) (h : O) (hh : h∈dyadRows n) : h≠0 := by
  intro he
  have hn := (mem_dyadRows n h).mp hh
  subst h
  exact hn (by simpa [normValue] using dyadicWeight_zero_nonpos n 0 le_rfl)

theorem dyadRows_norm_lt (n : ℤ) (h : O) (hh : h∈dyadRows n) :
    normValue h< dyadicScale n :=
  (dyadicWeight_support n ((mem_dyadRows n h).mp hh)).2

theorem dyadRows_log_nonneg (Z : ℝ) (hZ : 1< Z) (n : ℤ)
    (hne : (dyadRows n).Nonempty) : 0≤ Real.logb Z (dyadicScale n) := by
  obtain ⟨h,hh⟩ := hne
  exact Real.logb_nonneg hZ
    ((normValue_ge_one h (dyadRows_ne_zero n h hh)).trans (dyadRows_norm_lt n h hh).le)

theorem dyadic_energy_eq_sum (n : ℤ) (f : O→ℂ) :
    (∑' h : O,dyadicWeight n (normValue h)*‖f h‖^2)=
      ∑ h∈dyadRows n,dyadicWeight n (normValue h)*‖f h‖^2 := by
  apply tsum_eq_sum
  intro h hh
  have hz : dyadicWeight n (normValue h)=0 := by
    by_contra hn
    exact hh ((mem_dyadRows n h).mpr hn)
  rw [hz,zero_mul]

theorem dyadic_energy_le_sum (n : ℤ) (f : O→ℂ) :
    (∑' h : O,dyadicWeight n (normValue h)*‖f h‖^2)≤
      ∑ h∈dyadRows n,‖f h‖^2 := by
  rw [dyadic_energy_eq_sum]
  exact Finset.sum_le_sum (fun h _ =>
    mul_le_of_le_one_left (sq_nonneg _) (dyadicWeight_bounds n (normValue h)).2)

theorem dyadic_energy_empty (n : ℤ) (f : O→ℂ) (h : dyadRows n=∅) :
    (∑' z : O,dyadicWeight n (normValue z)*‖f z‖^2)=0 := by
  rw [dyadic_energy_eq_sum,h,Finset.sum_empty]


theorem dyadRows_norm_power (Z : ℝ) (hZ : 1< Z) (n : ℤ)
    (h : O) (hh : h∈dyadRows n) :
    normValue h≤ Z^(Real.logb Z (dyadicScale n)) := by
  rw [Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (dyadicScale_pos n)]
  exact (dyadRows_norm_lt n h hh).le

theorem dyad_ball_majorant (Z : ℝ) (hZ : 1< Z) (n : ℤ) (g : ℝ) (hg : 0≤ g)
    (h : O) (hh : h∈dyadRows n) :
    1≤(ballProfile (‖ringComplex h‖^2/Z^(Real.logb Z (dyadicScale n)+g))).re := by
  apply ballProfile_majorizes _ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  exact (dyadRows_norm_power Z hZ n h hh).trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))

theorem amplified_ball_majorant (Z sigma D0 c : ℝ) (hZ : 1< Z) (hs : 0≤ sigma)
    (n : ℤ) (h p : O) (hh : h∈dyadRows n)
    (hp : normValue p≤ Z^(sigma/3)) :
    1≤(ballProfile (‖ringComplex (p^6*h)‖^2/
      Z^(Real.logb Z (dyadicScale n)+mainGain D0 c sigma))).re := by
  apply ballProfile_majorizes _ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  have hb := outputRow_norm (h,p) Z (Real.logb Z (dyadicScale n)) (sigma/3)
    (zero_lt_one.trans hZ) (dyadRows_norm_power Z hZ n h hh) hp
  change normValue (p^6*h)≤ Z^(Real.logb Z (dyadicScale n)+6*(sigma/3)) at hb
  exact hb.trans (Real.rpow_le_rpow_of_exponent_le hZ.le
    (by linarith [(mainGain_bounds D0 c sigma hs).1]))

theorem gaussEnergy_ball_nonneg {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ) (Y : ℝ) (hY : 0< Y) :
    0≤(gaussEnergy S a ha c ballProfile Y).re := by
  have hs := CenteredMomentSmoothedWindowEnergy.gaussEnergy_hasSum_re S a ha c ballProfile Y hY
  rw [←hs.tsum_eq]
  exact tsum_nonneg (fun h => mul_nonneg (sq_nonneg _) (ballProfile_nonneg _))

theorem errorEnergy_nonneg {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ) (h p : O) :
    0≤ errorEnergy S a ha c h p := by
  unfold errorEnergy
  positivity

theorem eligible_error_sum {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ)
    (rows P : Finset O) (allow : O→O→Prop) :
    (∑x∈eligiblePairs rows P allow,errorEnergy S a ha c x.1 x.2)=
      ∑p∈P,∑h∈rows.filter (fun h => allow h p),errorEnergy S a ha c h p := by
  rw [←sum_eligiblePairs]
  simp only [Finset.sum_filter]
  exact Finset.sum_comm

theorem dyadic_to_ball {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ)
    (Z sigma D0 cLog : ℝ) (hZ : 1< Z) (hsigma : 0≤ sigma) (n : ℤ) :
    (∑' h : O,dyadicWeight n (normValue h)*‖gaussPolynomial S a ha c h‖^2)≤
      (gaussEnergy S a ha c ballProfile
        (Z^(Real.logb Z (dyadicScale n)+(max (D0-cLog) 0+sigma)))).re := by
  apply (dyadic_energy_le_sum n (gaussPolynomial S a ha c)).trans
  apply finite_energy_le_gaussEnergy S a ha c ballProfile _
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) (dyadRows n)
    (fun _ => ballProfile_nonneg _)
  exact dyad_ball_majorant Z hZ n _ (by positivity)

/-- Amplification transfers dyadic energy to a larger radial window and three local errors. -/
theorem dyadic_amplification_to_ball {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ)
    (P : Finset (Ideal O)) (hp : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (hP : P.Nonempty) (R s : Ideal O) (hR0 : R≠0) (hs0 : s≠0)
    (Z sigma BR Bs Mmax D0 cLog : ℝ) (hZ : 1< Z) (hsigma : 0< sigma) (hM : 0≤ Mmax)
    (hlower : ∀Q∈P,Z^(sigma/6)≤(Ideal.absNorm Q:ℝ))
    (hupper : ∀Q∈P,(Ideal.absNorm Q:ℝ)≤ Z^(sigma/3))
    (hR : (Ideal.absNorm R:ℝ)≤ Z^BR) (hs : (Ideal.absNorm s:ℝ)≤ Z^Bs)
    (hsize : 2*((BR+Bs+Mmax)/(sigma/6))≤(P.card:ℝ))
    (n : ℤ) (hK : Real.logb Z (dyadicScale n)≤ Mmax) :
    (∑' h : O,dyadicWeight n (normValue h)*‖gaussPolynomial S a ha c h‖^2)≤
      (8/(P.card:ℝ))*
        (((Mmax+2*sigma)/(sigma/6))*
          (gaussEnergy S a ha c ballProfile
            (Z^(Real.logb Z (dyadicScale n)+mainGain D0 cLog sigma))).re+
          ∑p∈elementPool P,∑h∈(dyadRows n).filter (fun h => eligible R s h p),
            errorEnergy S a ha c h p) := by
  let K := Real.logb Z (dyadicScale n)
  have hY : 0< Z^(K+mainGain D0 cLog sigma) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have henergy := gaussEnergy_ball_nonneg S a ha c _ hY
  by_cases hn : (dyadRows n).Nonempty
  · have hK0 := dyadRows_log_nonneg Z hZ n hn
    have hsize' : 2*((BR+Bs+K)/(sigma/6))≤(P.card:ℝ) := by
      apply le_trans _ hsize
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact div_le_div_of_nonneg_right (by dsimp [K];linarith) (by linarith)
    have he := actual_eligible_amplification S a ha c (dyadRows n)
      (dyadRows_ne_zero n) P hp hbad hP R s hR0 hs0 Z (sigma/6) BR Bs K (sigma/3)
      hZ (by linarith) hlower hupper hR hs hsize' (dyadRows_norm_power Z hZ n)
    have hmajor : (∑y∈(eligiblePairs (dyadRows n) (elementPool P) (eligible R s)).image outputRow,
        ‖gaussPolynomial S a ha c y‖^2)≤
        (gaussEnergy S a ha c ballProfile (Z^(K+mainGain D0 cLog sigma))).re := by
      apply finite_energy_le_gaussEnergy S a ha c ballProfile _ hY _
        (fun _ => ballProfile_nonneg _) _
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      have hx' := Finset.mem_product.mp (Finset.mem_filter.mp hx).1
      have hpx := elementPool_data P hp hbad x.2 hx'.2
      exact amplified_ball_majorant Z sigma D0 cLog hZ hsigma.le n x.1 x.2 hx'.1
        (hupper _ hpx.2.1)
    apply (dyadic_energy_le_sum n (gaussPolynomial S a ha c)).trans (he.trans ?_)
    rw [eligible_error_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add _ le_rfl
    calc
      _ ≤ ((K+6*(sigma/3))/(sigma/6))*
          (gaussEnergy S a ha c ballProfile (Z^(K+mainGain D0 cLog sigma))).re :=
        mul_le_mul_of_nonneg_left hmajor (by dsimp [K];positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by dsimp [K];linarith) (by linarith)) henergy
  · rw [dyadic_energy_empty n _ (Finset.not_nonempty_iff_eq_empty.mp hn)]
    apply mul_nonneg (by positivity)
    apply add_nonneg
    · exact mul_nonneg (by positivity) henergy
    · exact Finset.sum_nonneg (fun p _ => Finset.sum_nonneg
        (fun h _ => errorEnergy_nonneg S a ha c h p))

theorem eventually_dyadic_amplification (M : Ideal O) [NeZero M]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta : ℝ)
    (hsigma : 0< sigma) (hloss : 0< loss) (hM : 0≤ Mmax) (hgap : eta< sigma/6) :
    ∀ᶠ Z : ℝ in atTop, 1< Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧ b*Z^eta< Z^(sigma/6) ∧
      (∀ Q∈P,Prime Q ∧ Q∉fixedBadPrimes ∧
        Z^(sigma/6)≤(Ideal.absNorm Q:ℝ) ∧ (Ideal.absNorm Q:ℝ)≤ Z^(sigma/3)) ∧
      ∀ {α : Type*} (S : Finset α) (a : α→O) (ha : ∀i,Supported (Ideal.span {a i}))
        (c : α→ℂ) (R s : Ideal O), R≠0 → s≠0 →
        (Ideal.absNorm R:ℝ)≤ Z^BR → (Ideal.absNorm s:ℝ)≤ Z^Bs →
        ∀ (n : ℤ),Real.logb Z (dyadicScale n)≤ Mmax → ∀ (D0 cLog : ℝ),
        (∑' h : O,dyadicWeight n (normValue h)*‖gaussPolynomial S a ha c h‖^2)≤
          (8/(P.card:ℝ))*
            (((Mmax+2*sigma)/(sigma/6))*
              (gaussEnergy S a ha c ballProfile
                (Z^(Real.logb Z (dyadicScale n)+mainGain D0 cLog sigma))).re+
              ∑p∈elementPool P,∑h∈(dyadRows n).filter (fun h => eligible R s h p),
                errorEnergy S a ha c h p) := by
  have he := eventually_actual_pool M H hH Sbad hbad (sigma/3) loss
    (BR+Bs+Mmax) b eta (by linarith) hloss (by linarith)
  simp only [show sigma/3/2=sigma/6 by ring] at he
  filter_upwards [he] with Z hz
  obtain ⟨hZ,hP,hcard,hsize,hslot,hdata⟩ := hz
  refine ⟨hZ,hP,hcard,hslot,hdata,?_⟩
  intro α S a ha c R s hR0 hs0 hR hs n hK D0 cLog
  exact dyadic_amplification_to_ball S a ha c _ (fun Q hQ => (hdata Q hQ).1)
    (fun Q hQ => (hdata Q hQ).2.1) hP R s hR0 hs0 Z sigma BR Bs Mmax D0 cLog
    hZ hsigma hM (fun Q hQ => (hdata Q hQ).2.2.1)
    (fun Q hQ => (hdata Q hQ).2.2.2) hR hs hsize n hK


open CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentOriginalChildEnergy
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationLiveMask CenteredMomentHeckeExpansion
open  CanonicalRowCompletion RayFourExpansion
open HeckeRowClosure CenteredMomentChildRows CenteredMomentHeckeColumnWindow
open CenteredMomentAmplificationActiveFamily CenteredMomentAmplificationActiveFactor

local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _


theorem exists_original_error_ball_family {ι : Type*} [Fintype ι]
    (η : Character) (m p : O) (hm : m≠0) (hp : Prime p)
    [(Ideal.span {p}).IsMaximal] (hPid : Prime (Ideal.span {p}))
    (hs : Supported (Ideal.span {p})) (hg : lambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hpp : lambda^2∣p-1)
    (hmLam : lambda∣m) (hm2 : (2:O)∣m) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤ rowConductorBound (childCharacter η χ) m 1 (p^(2*errorMovingExponent n))) ∧
      ∀ (D : OriginalData ι),
        (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
        (∀ i,∀ I∈D.S (Sum.inl i),IsCoprime (Ideal.span {p}) I) →
        ∀ (t T Z sigma D0 cLog : ℝ),0< T → 1< Z → 0≤ sigma → ∀ (j : ℤ),
        (∑ h∈(dyadRows j).filter (fun h => eligible D.R D.s h p),
          ‖amplificationError Finset.univ (sourceGenerator D.columns)
            (sourceGenerator_supported D.columns) (D.coefficient η m t T)
            (fun I => multiplicity p (sourceGenerator D.columns I)) p (n+1) h‖^2)≤
          D.childEnergy τ p n t T
            (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (n+1))) := by
  obtain ⟨τ,hN,hτ⟩ := original_errors_to_children (ι:=ι) η m p hm hp hPid hs hg hc hpp hmLam hm2 n hn
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hslot t T Z sigma D0 cLog hT hZ hsigma j
  have hK : 0< Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (n+1)) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  by_cases he : ((dyadRows j).filter (fun h => eligible D.R D.s h p)).Nonempty
  · obtain ⟨h,hh⟩ := he
    have hsc := (eligible_coprime_divisor D.R D.s h p hPid (Finset.mem_filter.mp hh).2).pow_right (n:=n+1)
    have hfull := hτ D.S hS hprime (fun i I hI => ⟨hS _ _ hI,hslot i I hI⟩) D.R D.s hsc
      D.nu D.slot D.lengths D.W₁ D.W₂ D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂ t T hT
      ((dyadRows j).filter (fun h => eligible D.R D.s h p))
      (fun h hh => eligible_not_dvd_row D.R D.s h p (Finset.mem_filter.mp hh).2)
      ballProfile _ hK (fun _ => ballProfile_nonneg _)
      (fun h hh => dyad_ball_majorant Z hZ j _
        (hsigma.trans (errorGain_bounds D0 cLog sigma Z p (n+1) hsigma).1)
        h (Finset.mem_filter.mp hh).1)
    rw [OriginalData.coefficient_eq]
    dsimp only at hfull
    dsimp only [OriginalData.childEnergy,OriginalData.coefficient,OriginalData.beta,
      OriginalData.columns,OriginalData.profile]
    exact hfull
  · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty]
    exact D.childEnergy_nonneg τ p n t T _ hT.le hK

def errorIndex (i : Fin 3) : ℕ := ![0,5,6] i

theorem errorIndex_cases (i : Fin 3) : errorIndex i=0 ∨ errorIndex i=5 ∨ errorIndex i=6 := by
  fin_cases i <;> simp [errorIndex]

theorem exists_pool_error_families {ι : Type*} [Fintype ι]
    (P : Finset (Ideal O)) (hP : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (η : Character) (m : O) (hm : m≠0) (hmLam : lambda∣m) (hm2 : (2:O)∣m) :
    ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
      (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
        rowConductorBound (childCharacter η χ) m 1 (p.val^(2*errorMovingExponent (errorIndex i)))) ∧
      ∀ (D : OriginalData ι),
        (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
        (∀ p∈elementPool P,∀ i,∀ I∈D.S (Sum.inl i),IsCoprime (Ideal.span {p}) I) →
        ∀ (t T Z sigma D0 cLog : ℝ),0< T → 1< Z → 0≤ sigma → ∀ (j : ℤ),
        (∑p∈elementPool P,∑h∈(dyadRows j).filter (fun h => eligible D.R D.s h p),
          errorEnergy Finset.univ (sourceGenerator D.columns) (sourceGenerator_supported D.columns)
            (D.coefficient η m t T) h p)≤
        ∑p : elementPool P,∑i : Fin 3,D.childEnergy (τ p i) p (errorIndex i) t T
          (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (errorIndex i+1))) := by
  have hf (p : elementPool P) (i : Fin 3) := by
    have hd := elementPool_data P hP hbad p p.property
    have hPid := hP _ hd.2.1
    letI : (Ideal.span {p.val}).IsMaximal :=
      (Ideal.isPrime_of_prime hPid).isMaximal hPid.ne_zero
    exact exists_original_error_ball_family (ι:=ι) η m p hm hd.1 hPid hd.2.2.2.1
      hd.2.2.2.2.1 hd.2.2.2.2.2 hd.2.2.1 hmLam hm2 (errorIndex i) (errorIndex_cases i)
  choose τ hτ using hf
  refine ⟨τ,fun p i => (hτ p i).1,?_⟩
  intro D hS hprime hslot t T Z sigma D0 cLog hT hZ hsigma j
  rw [←Finset.sum_coe_sort (elementPool P)]
  apply Finset.sum_le_sum
  intro p hp
  have h0 := (hτ p 0).2 D hS hprime (hslot p p.property) t T Z sigma D0 cLog hT hZ hsigma j
  have h5 := (hτ p 1).2 D hS hprime (hslot p p.property) t T Z sigma D0 cLog hT hZ hsigma j
  have h6 := (hτ p 2).2 D hS hprime (hslot p p.property) t T Z sigma D0 cLog hT hZ hsigma j
  simpa only [errorEnergy,Finset.sum_add_distrib,Fin.sum_univ_three,
    show errorIndex 0=0 from rfl,show errorIndex 1=5 from rfl,show errorIndex 2=6 from rfl,Nat.reduceAdd] using
    add_le_add (add_le_add h0 h5) h6

theorem original_slot_coprime {ι : Type*} [Fintype ι]
    (D : OriginalData ι) (Z sigma b eta : ℝ) (hZ : 1≤ Z) (hb : 0≤ b)
    (hgap : b*Z^eta< Z^(sigma/6))
    (z : ι → ℝ) (hz : ∀i,z i≤ eta) (hlen : ∀i,D.lengths i=Z^(z i))
    (hsupp : ∀i,Function.support (D.slot i)⊆Set.Iic b)
    (hslot : ∀i,∀I∈D.S (Sum.inl i),D.slot i ((Ideal.absNorm I:ℝ)/D.lengths i)≠0)
    (hprime : ∀i,∀I∈D.S (Sum.inl i),Prime I)
    (Q : Ideal O) (hQ : Prime Q) (hQN : Z^(sigma/6)≤(Ideal.absNorm Q:ℝ)) :
    ∀i,∀I∈D.S (Sum.inl i),IsCoprime Q I := by
  intro i I hI
  have hW := hslot i I hI
  rw [hlen] at hW
  have hN := live_profile_norm_bound (D.slot i) b Z (z i) eta I hb hZ (hz i) (hsupp i) hW
  have hmax := (Ideal.isPrime_of_prime hQ).isMaximal hQ.ne_zero
  apply Ideal.isCoprime_iff_codisjoint.mpr
  apply (Ideal.isMaximal_def.mp hmax).not_le_iff_codisjoint.mp
  intro hle
  exact (amplifier_not_dvd_slot Q I hQ (hprime i I hI) Z (sigma/6) eta b hgap hQN hN)
    (Ideal.dvd_iff_le.mpr hle)

theorem eventually_original_source_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta : ℝ)
    (hsigma : 0< sigma) (hloss : 0< loss) (hM : 0≤ Mmax) (hb : 0≤ b) (hgap : eta< sigma/6) :
    ∀ᶠ Z : ℝ in atTop, 1< Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : Character) (m : O),m≠0 → lambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          rowConductorBound (childCharacter η χ) m 1 (p.val^(2*errorMovingExponent (errorIndex i)))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,∀ I∈D.S (Sum.inl i),D.slot i ((Ideal.absNorm I:ℝ)/D.lengths i)≠0) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤ eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤ Z^BR → (Ideal.absNorm D.s:ℝ)≤ Z^Bs →
          ∀ (t T D0 cLog : ℝ),0< T → ∀ (j : ℤ),Real.logb Z (dyadicScale j)≤ Mmax →
          (∑' h : O,dyadicWeight j (normValue h)*
            ‖gaussPolynomial Finset.univ (sourceGenerator D.columns)
              (sourceGenerator_supported D.columns) (D.coefficient η m t T) h‖^2)≤
            (8/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (D.coefficient η m t T) ballProfile
                  (Z^(Real.logb Z (dyadicScale j)+mainGain D0 cLog sigma))).re+
                ∑p : elementPool P,∑i : Fin 3,D.childEnergy (τ p i) p (errorIndex i) t T
                  (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (errorIndex i+1)))) := by
  filter_upwards [eventually_dyadic_amplification M H hH Sbad hbad sigma loss BR Bs Mmax b eta
    hsigma hloss hM hgap] with Z hz
  obtain ⟨hZ,hP,hcard,hsep,hdata,hamp⟩ := hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hN,herr⟩ := exists_pool_error_families (ι:=ι) _
    (fun Q hQ => (hdata Q hQ).1) (fun Q hQ => (hdata Q hQ).2.1) η m hm hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hslot hsupp z hz hlen hR0 hs0 hR hs t T D0 cLog hT j hK
  have hcop (p : O) (hp : p∈elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3)))) :
      ∀i,∀I∈D.S (Sum.inl i),IsCoprime (Ideal.span {p}) I := by
    have hd := elementPool_data _ (fun Q hQ => (hdata Q hQ).1)
      (fun Q hQ => (hdata Q hQ).2.1) p hp
    exact original_slot_coprime D Z sigma b eta hZ.le hb hsep z hz hlen hsupp hslot hprime
      (Ideal.span {p}) (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
  have he := herr D hS hprime hcop t T Z sigma D0 cLog hT hZ hsigma.le j
  apply (hamp Finset.univ (sourceGenerator D.columns) (sourceGenerator_supported D.columns)
    (D.coefficient η m t T) D.R D.s hR0 hs0 hR hs j hK D0 cLog).trans
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl he) (by positivity)


/-- Removing zero slot coefficients makes the amplification estimate apply to the full source. -/
theorem eventually_original_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta : ℝ)
    (hsigma : 0< sigma) (hloss : 0< loss) (hM : 0≤ Mmax) (hb : 0≤ b) (hgap : eta< sigma/6) :
    ∀ᶠ Z : ℝ in atTop, 1< Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : Character) (m : O),m≠0 → lambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          rowConductorBound (childCharacter η χ) m 1 (p.val^(2*errorMovingExponent (errorIndex i)))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤ eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤ Z^BR → (Ideal.absNorm D.s:ℝ)≤ Z^Bs →
          ∀ (t T D0 cLog : ℝ),0< T → ∀ (j : ℤ),Real.logb Z (dyadicScale j)≤ Mmax →
          (∑' h : O,dyadicWeight j (normValue h)*
            ‖gaussPolynomial Finset.univ (sourceGenerator D.columns)
              (sourceGenerator_supported D.columns) (D.coefficient η m t T) h‖^2)≤
            (8/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (D.coefficient η m t T) ballProfile
                  (Z^(Real.logb Z (dyadicScale j)+mainGain D0 cLog sigma))).re+
                ∑p : elementPool P,∑i : Fin 3,D.active.childEnergy (τ p i) p (errorIndex i) t T
                  (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (errorIndex i+1)))) := by
  filter_upwards [eventually_original_source_amplification (ι:=ι) M H hH Sbad hbad
    sigma loss BR Bs Mmax b eta hsigma hloss hM hb hgap] with Z hz
  obtain ⟨hZ,hP,hcard,hfam⟩ := hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hN,henergy⟩ := hfam η m hm hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T D0 cLog hT j hK
  have he := henergy D.active (fun i I hI => hS i I (D.active_subset i hI))
    (fun i I hI => hprime i I (D.active_subset _ hI)) D.active_slot hsupp z hz hlen
    hR0 hs0 hR hs t T D0 cLog hT j hK
  simpa only [D.active_gaussPolynomial,D.active_gaussEnergy] using he


open CenteredMomentFirstScale CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstExtractedLedger
open CenteredMomentDescentLedger CenteredMomentCommonSupport
open CenteredMomentFirstColumns CenteredMomentRankinRadical Eisenstein


theorem retained_nominal_choice (I J E : Ideal O) (hE : E≠0)
    (K X Z Csec Tsec xi : ℝ) (hK : 0< K) (hX : 0< X) (hZ : 1< Z)
    (hC : 0< Csec) (hsec : Tsec≤ Csec*firstNominalScale I J E K X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z xi) n)
    (hne : (dyadRows n).Nonempty) :
    0≤ Real.logb Z (dyadicScale n) ∧
    Real.logb Z (dyadicScale n)≤ nominalLog I J E K X Z+frequencyLoss Z Csec xi ∧
    Real.logb Z ((commonPart J I).absNorm:ℝ)-frequencyLoss Z Csec xi≤
      Real.logb Z ((commonPart J I).absNorm:ℝ)+nominalLog I J E K X Z-
        Real.logb Z (dyadicScale n) := by
  have hs : Tsec≤ Csec*Z^(nominalLog I J E K X Z) := by
    rw [nominalLog,Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
      (firstNominalScale_pos I J E hE K X hK hX)]
    exact hsec
  have he := retained_first_dyad_enclosure Tsec Z Csec (nominalLog I J E K X Z) xi hZ hC hs n hn
  exact ⟨dyadRows_log_nonneg Z hZ n hne,he,by linarith⟩


theorem retained_main_first_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J) (hE : E≠0)
    (A : Finset (CommonIndex I J)) (K X Z Csec Tsec xi sigma : ℝ)
    (hK : 0< K) (hX : 0< X) (hZ : 1< Z) (hC : 1≤ Csec) (hxi : 0≤ xi) (hsigma : 0≤ sigma)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (hsec : Tsec≤ Csec*firstNominalScale I J E K X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z xi) n) (hne : (dyadRows n).Nonempty) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let D0 := d+nominalLog I J E K X Z-Real.logb Z (dyadicScale n)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    2*c/3-3*sigma-5*frequencyLoss Z Csec xi/6≤
      firstSaving c D0 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0
        (c+d-2*p-R) (mainGain D0 c sigma) (sigma/3) := by
  dsimp only
  have hq := canonical_active_log_le η τ m I J A Z hZ hmod
  have hD := (retained_nominal_choice I J E hE K X Z Csec Tsec xi hK hX hZ
    (zero_lt_one.trans_le hC) hsec n hn hne).2.2
  let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
  let D0 := Real.logb Z ((commonPart J I).absNorm:ℝ)+nominalLog I J E K X Z-
    Real.logb Z (dyadicScale n)
  have he := actual_extracted_first_saving I J hI hJ Z hZ
    D0 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0 (mainGain D0 c sigma) (sigma/3) sigma (frequencyLoss Z Csec xi)
    (by norm_num) hq.1 (by norm_num) hsigma (frequencyLoss_nonneg Z Csec xi hZ hC hxi)
    hq.2 hD (by simp only [mainGain,c,mul_zero,sub_zero,add_zero];exact le_rfl)
    (by positivity) (by positivity)
  simpa only [add_zero] using he


theorem eventually_frequency_loss (Csec xi : ℝ) (hC : 1≤ Csec) (hxi : 0< xi) :
    ∀ᶠ Z : ℝ in atTop, 1< Z ∧ 0≤ frequencyLoss Z Csec xi ∧ frequencyLoss Z Csec xi< xi := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_gt_atTop (2*Real.log (4*Csec)/xi)),eventually_gt_atTop (1:ℝ)] with Z hlog hZ
  have hh := (div_lt_iff₀ hxi).mp hlog
  have hr : Real.log (4*Csec)/Real.log Z< xi/2 := by
    apply (div_lt_iff₀ (Real.log_pos hZ)).mpr
    nlinarith
  refine ⟨hZ,frequencyLoss_nonneg Z Csec xi hZ hC hxi.le,?_⟩
  unfold frequencyLoss Real.logb
  linarith

theorem retained_error_first_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J) (hE : E≠0)
    (A : Finset (CommonIndex I J)) (K X Z Csec Tsec xi sigma : ℝ)
    (hK : 0< K) (hX : 0< X) (hZ : 1< Z) (hC : 1≤ Csec) (hxi : 0≤ xi) (hsigma : 0≤ sigma)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (hsec : Tsec≤ Csec*firstNominalScale I J E K X)
    (j : ℤ) (hj : Retained (frequencyRadius Tsec Z xi) j) (hne : (dyadRows j).Nonempty)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p : O) (hp : p∈elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let D0 := d+nominalLog I J E K X Z-Real.logb Z (dyadicScale j)
    let u := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    2*(c+errorRemoval p Z k)/3-3*sigma-5*frequencyLoss Z Csec xi/6≤
      firstSaving c D0 (errorRemoval p Z k) (Real.logb Z (τ.modulus.absNorm:ℝ))
        (errorMoving p Z k) (c+d-2*u-R) (errorGain D0 c sigma Z p k) 0 := by
  dsimp only
  let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
  let D0 := Real.logb Z ((commonPart J I).absNorm:ℝ)+nominalLog I J E K X Z-
    Real.logb Z (dyadicScale j)
  have hq := canonical_active_log_le η τ m I J A Z hZ hmod
  have hD := (retained_nominal_choice I J E hE K X Z Csec Tsec xi hK hX hZ
    (zero_lt_one.trans_le hC) hsec j hj hne).2.2
  have hl := pool_prime_log_range M H Sbad hbad Z sigma hZ p hp
  have hw := error_lengths p Z sigma hsigma k hk hl.1 hl.2
  have hg := (errorGain_bounds D0 c sigma Z p k hsigma).2.2
  exact actual_extracted_first_saving I J hI hJ Z hZ D0 (errorRemoval p Z k)
    (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p Z k)
    (errorGain D0 c sigma Z p k) 0 sigma (frequencyLoss Z Csec xi)
    (hw.1.trans hw.2.1) hq.1 hw.1 hsigma (frequencyLoss_nonneg Z Csec xi hZ hC hxi)
    hq.2 hD hg (by norm_num) hw.2.2

end CenteredMomentFirstAmplificationChoice

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentAmplifiedRetainedRadius
open HeckeFamily CanonicalQuadraticSieve 
open CenteredMomentFirstAmplificationChoice CenteredMomentGaussEnergy
open CenteredMomentSmoothedWindowEnergy CenteredMomentOriginalChildEnergy
open CenteredMomentAmplificationErrorEnergy CenteredMomentSectorLocalization
open CenteredMomentSourceRow CenteredMomentGaussNormalization CenteredMomentFirstScale
local notation "O" => Eisenstein.O


theorem dyadic_to_common_ball {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (coeff : α→ℂ)
    (Z d K0 c sigma δ reserve : ℝ) (hZ : 1< Z) (hsigma : 0≤ sigma) (hδ : 0≤δ)
    (n : ℤ) (hn : Real.logb Z (dyadicScale n)≤ K0+δ) (hreserve : 2≤ Z^reserve) :
    (∑' h : O,dyadicWeight n (normValue h)*‖gaussPolynomial S a ha coeff h‖^2)≤
      (gaussEnergy S a ha coeff ballProfile (Z^(K0+max (d-c) 0+sigma+δ+reserve))).re := by
  apply (dyadic_to_ball S a ha coeff Z sigma
    (d+K0-Real.logb Z (dyadicScale n)) c hZ hsigma n).trans
  apply gaussEnergy_radius_le _ _ _ _ _ _
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  exact doubled_radius_le Z _ _ reserve hZ
    (envelope_exponent d K0 _ c sigma δ hδ hn) hreserve


open CenteredMomentPrimePool CenteredMomentPrimeElements
open CenteredMomentAmplificationOriginalErrors CenteredMomentAmplificationGlobal

theorem eventually_original_amplification_common {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0< sigma) (hloss : 0< loss) (hM : 0≤ Mmax) (hb : 0≤ b) (hgap : eta< sigma/6)
    (hC : 1≤ Csec) (hxi : 0≤ xi) (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop, 1< Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : Character) (m : O),m≠0 → lambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayFourExpansion.RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          HeckeRowClosure.rowConductorBound (CenteredMomentChildRows.childCharacter η χ) m 1 (p.val^(2*CenteredMomentAmplificationActiveFactor.errorMovingExponent (errorIndex i)))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤ eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤ Z^BR → (Ideal.absNorm D.s:ℝ)≤ Z^Bs →
          ∀ (t T d cLog : ℝ),0< T →
          ∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0< K → 0< X →
          Tsec≤ Csec*firstNominalScale I J E K X →
          ∀ (j : ℤ),Retained (frequencyRadius Tsec Z xi) j →
          Real.logb Z (dyadicScale j)≤ Mmax →
          (∑' h : O,dyadicWeight j (normValue h)*
            ‖gaussPolynomial Finset.univ (sourceGenerator D.columns)
              (sourceGenerator_supported D.columns) (D.coefficient η m t T) h‖^2)≤
            (8/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (D.coefficient η m t T) ballProfile
                  (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z Csec xi) reserve)).re+
                ∑p : elementPool P,∑i : Fin 3,D.active.childEnergy (τ p i) p (errorIndex i) t T
                  (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z Csec xi) reserve p (errorIndex i+1))) := by
  filter_upwards [eventually_original_amplification (ι:=ι) M H hH Sbad hbad
    sigma loss BR Bs Mmax b eta hsigma hloss hM hb hgap,
    eventually_support_reserve reserve hreserve] with Z hz hsupport
  obtain ⟨hZ,hP,hcard,hfam⟩ := hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hN,henergy⟩ := hfam η m hm hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T d cLog hT
    I J E hE K X Tsec hK hX hsec j hj hMdyad
  let K0 := nominalLog I J E K X Z
  let kdyad := Real.logb Z (dyadicScale j)
  have henclose : kdyad≤ K0+frequencyLoss Z Csec xi :=
    retained_nominal_upper I J E hE K X Z Csec Tsec xi hK hX hZ
      (zero_lt_one.trans_le hC) hsec j hj
  have hδ := frequencyLoss_nonneg Z Csec xi hZ hC hxi
  have he := henergy D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T
    (d+K0-kdyad) cLog hT j hMdyad
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact main_energy_common _ _ _ _ Z d K0 kdyad cLog sigma _ reserve hZ hδ henclose hsupport.2
  · apply Finset.sum_le_sum
    intro p _
    apply Finset.sum_le_sum
    intro i _
    exact child_energy_common D.active (τ p i) p (errorIndex i) t T Z d K0 kdyad cLog sigma
      _ reserve hT.le hZ hδ henclose hsupport.2

end CenteredMomentAmplifiedRetainedRadius

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace CenteredMomentAmplificationRadicalFamily
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion
open  CompletedGauss RayFourExpansion
open CenteredMomentRadicalFamily CenteredMomentFirstFamily
open CenteredMomentAmplificationFamily CenteredMomentAmplificationFamilyEnergy
open CenteredMomentAmplificationActiveFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationShortening CenteredMomentAmplificationSourceDomain
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentSourceRow CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy
open CenteredMomentSecondChildProfile
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationChildEnergy CenteredMomentAmplificationErrorPool
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationLiveMask
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum
open CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization CenteredMomentAmplificationEligibility
local notation "O"=> Eisenstein.O
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

def radicalBound (η:Character)(m p:O)(k:ℕ):ℕ :=
  η.modulus.absNorm*(Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm*
    (if k=0 then 1 else (Ideal.span {p}).absNorm)

theorem radicalBound_error_power (η:Character)(m p:O)(hp:p≠0)(Z:ℝ)(hZ:1< Z)
    (n:ℕ)(hn:n=0∨n=5∨n=6):
    (radicalBound η m p (errorMovingExponent n):ℝ)=
      ((η.modulus.absNorm:ℝ)*(Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm)*
        Z^(errorMoving p Z (n+1)):=by
  have hpow:=Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (normValue_pos p hp)
  rcases hn with rfl|rfl|rfl <;>
    norm_num only [radicalBound,errorMovingExponent,errorMoving,Nat.cast_mul,
      Nat.cast_one,Real.rpow_zero,mul_one]
  all_goals simp only [ite_false,ite_true,Nat.one_ne_zero,eq_self,
    Nat.cast_one,Real.rpow_zero,mul_one]
  all_goals rw [hpow]; rfl

theorem exists_radical_row (η:Character)(m p:O)(hm:m≠0)
    (hs:Supported (Ideal.span {p}))(hmLam:lambda∣m)(hm2:(2:O)∣m)(k:ℕ):
    ∃τ:Character,τ.modulus.absNorm≤ radicalBound η m p k ∧
      ∀n:O,elementCoeff τ n=rowTwist (elementHom η) m 1 (p^(2*k)) n:=by
  by_cases hk:k=0
  · obtain ⟨τ,hN,hτ⟩:=exists_supported_row_presentation η m 1 hm
      CenteredMomentAddedZero.supported_one_element hmLam hm2
    refine ⟨τ,?_,?_⟩
    · simp [radicalBound,hk,hN]
    · simpa [hk] using hτ
  · obtain ⟨τ,hM,hN,hτ⟩:=exists_radical_row_presentation η m hm hmLam hm2
      (fun _:Fin 1=> p) (fun _=> hs) (fun _=>2*k)
      (fun _=> Nat.mul_pos (by omega) (Nat.pos_of_ne_zero hk))
    refine ⟨τ,?_,?_⟩
    · simpa [radicalBound,hk] using hN
    · simpa using hτ

theorem exists_radical_height (η:Character)(χ:RayCharacter)(m p:O)(hm:m≠0)
    (hs:Supported (Ideal.span {p}))(hmLam:lambda∣m)(hm2:(2:O)∣m)(k:ℕ):
    ∃τ:Character,τ.modulus.absNorm≤ radicalBound (childCharacter η χ) m p k ∧
      ∀I:Ideal O,Supported I→∀t:ℝ,
        heightCoeff τ t I=rowWeight η m 1 1 t I*idealRowHom (p^(2*k)) I*
          rayMonoid χ (primaryIdealGenerator I):=by
  obtain ⟨τ,hN,hτ⟩:=exists_radical_row (childCharacter η χ) m p hm hs hmLam hm2 k
  refine ⟨τ,hN,?_⟩
  intro I hI t
  have he:=idealCoeff_eq_row (childCharacter η χ) τ m 1 (p^(2*k)) hτ I
  simp only [one_pow,mul_one] at he
  change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
    ((idealCoeff η I*idealRowHom (m^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))*
      idealRowHom (p^(2*k)) I*rayMonoid χ (primaryIdealGenerator I)
  rw [he,child_ideal_primary η χ I hI,idealRowHom_argument_mul]
  simp only [mul_one]
  ring

theorem exists_radical_family (η:Character)(m p:O)(hm:m≠0)
    (hs:Supported (Ideal.span {p}))(hpp:lambda^2∣p-1)
    (hmLam:lambda∣m)(hm2:(2:O)∣m)(k:ℕ):
    ∃τ:RayCharacter→Character,
      (∀χ,(τ χ).modulus.absNorm≤ radicalBound (childCharacter η χ) m p k) ∧
      ∀I:Ideal O,Supported I→∀t:ℝ,
        rowWeight η m 1 1 t I*residualCharacter p k (primaryIdealGenerator I)=
          ∑χ:RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I:=by
  choose τ hN hτ using fun χ:RayCharacter=> exists_radical_height η χ m p hm hs hmLam hm2 k
  refine ⟨τ,hN,?_⟩
  intro I hI t
  have hn:=supported_primaryIdealGenerator_ne_zero I hI
  have hgen:Supported (Ideal.span {primaryIdealGenerator I}):=by
    rw [primary_span_supported I hI];exact hI
  rw [residualCharacter_moving p _ k hs hgen hpp (primaryIdealGenerator_spec I hn).2,
    primary_span_supported I hI,amplificationPhase_expansion p _ k hgen]
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [hτ χ I hI t]
  ring

theorem exists_actual_error_family (η:Character)(m p:O)
    (hm:m≠0)(hp:Prime p)(hs:Supported (Ideal.span {p}))
    (hpp:lambda^2∣p-1)(hmLam:lambda∣m)(hm2:(2:O)∣m)
    (n:ℕ)(hn:n=0∨n=5∨n=6):
    ∃τ:RayCharacter→Character,
      (∀χ,(τ χ).modulus.absNorm≤ radicalBound (childCharacter η χ) m p (errorMovingExponent n)) ∧
      ∀(S:Finset (Ideal O))(C:Ideal O),C≠0→∀(β:Ideal O→ℂ)(t:ℝ)
        (W:𝓢(ℝ,ℂ))(K:ℝ),0< K→
      (∀z:O,0≤(W (‖ringComplex z‖^2/K)).re)→
      (sourceGaussEnergy (residualColumns S p hp (n+1))
        (fun I=>β (C*I)*rowWeight η m 1 1 t (C*I))
        (fun I=> residualCharacter p (n+1) (primaryIdealGenerator I)) W K).re≤
        16*∑χ:RayCharacter,
          (sourceGaussEnergy (residualColumns S p hp (n+1))
            (fun I=>β (C*I)) (heightCoeff (τ χ) t) W K).re:=by
  obtain ⟨τ,hN,hτ⟩:=exists_radical_family η m p hm hs hpp hmLam hm2 (errorMovingExponent n)
  refine ⟨τ,hN,?_⟩
  intro S C hC β t W K hK hW
  rw [actual_error_energy_active S p hp hs n hn]
  exact amplification_family_energy η m p (errorMovingExponent n) τ hτ
    (residualColumns S p hp (n+1)) C hC β t W K hK hW

theorem original_errors_to_children {ι : Type*} [Fintype ι] (η : Character) (m p : O)
    (hm : m≠0) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hPid : Prime (Ideal.span {p})) (hs : Supported (Ideal.span {p}))
    (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (hpp : lambda^2 ∣ p-1) (hmLam : lambda∣m) (hm2 : (2:O)∣m)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤ radicalBound (childCharacter η χ) m p (errorMovingExponent n)) ∧
      ∀ (S : (ι ⊕ Fin 2) → Finset (Ideal O)),
      (∀ i,∀ I∈S i,I≠0) → (∀ i,∀ I∈S (Sum.inl i),Prime I) →
      (∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime (Ideal.span {p}) I) →
      ∀ (R s : Ideal O),IsCoprime s ((Ideal.span {p})^(n+1)) →
      ∀ (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
        (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (t T : ℝ),0< T →
      ∀ (rows : Finset O),(∀ h∈rows,¬p∣h) →
      ∀ (W : 𝓢(ℝ,ℂ)) (K : ℝ),0< K →
      (∀ z : O,0≤(W (‖ringComplex z‖^2/K)).re) →
      (∀ z∈rows,1≤(W (‖ringComplex z‖^2/K)).re) →
      let β := finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
      let C := (Ideal.span {p})^(n+1)
      (∑ h∈rows,‖amplificationError Finset.univ
        (sourceGenerator (finiteColumns (Fintype.piFinset S)))
        (sourceGenerator_supported (finiteColumns (Fintype.piFinset S)))
        (fun I : supportedColumns (finiteColumns (Fintype.piFinset S)) =>
          (Real.sqrt T:ℂ)⁻¹*(β I*rowWeight η m 1 1 t I))
        (fun I => multiplicity p (sourceGenerator (finiteColumns (Fintype.piFinset S)) I)) p (n+1) h‖^2)≤
        (16*(n+2:ℝ)*localErrorCost p n) *
          ((∑ χ : RayCharacter,∑ B : actualAllocations S C,
            (sourceGaussEnergy
              (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
              (finiteColumnCoefficient
                (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
                (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
              (heightCoeff (τ χ) t) W K).re) /
            (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1))) := by
  obtain ⟨τ,hN,hτ⟩ := exists_actual_error_family η m p hm hp hs hpp hmLam hm2 n hn
  refine ⟨τ,hN,?_⟩
  intro S hS hprime hslot R s hsc ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ t T hT rows hrows W K hK hW hmajor
  dsimp only
  let β := finiteColumnCoefficient (Fintype.piFinset S)
    (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
  let S₀ := finiteColumns (Fintype.piFinset S)
  let C := (Ideal.span {p})^(n+1)
  let Q := residualColumns S₀ p hp (n+1)
  let T' := T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)
  have hC : C≠0 := pow_ne_zero _ hs.1
  have ht : 0< T' := by
    apply div_pos hT
    apply pow_pos
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs.1)
  have he := finite_original_error_energy S₀ (fun I => β I*rowWeight η m 1 1 t I)
    p hp hs hg hc hpp n hn T hT rows hrows W K hK hW hmajor
  have hf := hτ S₀ C hC β t W K hK hW
  have hb (χ : RayCharacter) :
      (sourceGaussEnergy Q (fun I => β (C*I)) (heightCoeff (τ χ) t) W K).re≤
        (n+2:ℝ)*∑ B : actualAllocations S C,
          (sourceGaussEnergy
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
            (heightCoeff (τ χ) t) W K).re := by
    have hpool := residual_energy_eq_punctured S₀ β (heightCoeff (τ χ) t) p hp hs hpp (n+1) (by omega) W K
    change _≤ _
    rw [hpool]
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using
      actual_amplification_child_energy S hS hprime (Ideal.span {p}) R s hPid hs (n+1)
        hslot hsc ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ (heightCoeff (τ χ) t) W K hK hW
  apply he.trans
  apply (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
    (hf.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ _ => hb χ)) (by norm_num))) ht.le)
    (localErrorCost_nonneg p n)).trans_eq
  rw [←Finset.mul_sum]
  ring

theorem exists_original_error_ball_family {ι : Type*} [Fintype ι]
    (η : Character) (m p : O) (hm : m≠0) (hp : Prime p)
    [(Ideal.span {p}).IsMaximal] (hPid : Prime (Ideal.span {p}))
    (hs : Supported (Ideal.span {p})) (hg : lambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hpp : lambda^2∣p-1)
    (hmLam : lambda∣m) (hm2 : (2:O)∣m) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤ radicalBound (childCharacter η χ) m p (errorMovingExponent n)) ∧
      ∀ (D : OriginalData ι),
        (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
        (∀ i,∀ I∈D.S (Sum.inl i),IsCoprime (Ideal.span {p}) I) →
        ∀ (t T Z sigma D0 cLog : ℝ),0< T → 1< Z → 0≤ sigma → ∀ (j : ℤ),
        (∑ h∈(dyadRows j).filter (fun h => eligible D.R D.s h p),
          ‖amplificationError Finset.univ (sourceGenerator D.columns)
            (sourceGenerator_supported D.columns) (D.coefficient η m t T)
            (fun I => multiplicity p (sourceGenerator D.columns I)) p (n+1) h‖^2)≤
          D.childEnergy τ p n t T
            (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (n+1))) := by
  obtain ⟨τ,hN,hτ⟩ := original_errors_to_children (ι:=ι) η m p hm hp hPid hs hg hc hpp hmLam hm2 n hn
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hslot t T Z sigma D0 cLog hT hZ hsigma j
  have hK : 0< Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (n+1)) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  by_cases he : ((dyadRows j).filter (fun h => eligible D.R D.s h p)).Nonempty
  · obtain ⟨h,hh⟩ := he
    have hsc := (eligible_coprime_divisor D.R D.s h p hPid (Finset.mem_filter.mp hh).2).pow_right (n:=n+1)
    have hfull := hτ D.S hS hprime (fun i I hI => ⟨hS _ _ hI,hslot i I hI⟩) D.R D.s hsc
      D.nu D.slot D.lengths D.W₁ D.W₂ D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂ t T hT
      ((dyadRows j).filter (fun h => eligible D.R D.s h p))
      (fun h hh => eligible_not_dvd_row D.R D.s h p (Finset.mem_filter.mp hh).2)
      ballProfile _ hK (fun _ => ballProfile_nonneg _)
      (fun h hh => dyad_ball_majorant Z hZ j _
        (hsigma.trans (errorGain_bounds D0 cLog sigma Z p (n+1) hsigma).1)
        h (Finset.mem_filter.mp hh).1)
    rw [OriginalData.coefficient_eq]
    dsimp only at hfull
    dsimp only [OriginalData.childEnergy,OriginalData.coefficient,OriginalData.beta,
      OriginalData.columns,OriginalData.profile]
    exact hfull
  · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty]
    exact D.childEnergy_nonneg τ p n t T _ hT.le hK

end CenteredMomentAmplificationRadicalFamily

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace CenteredMomentAmplificationRadicalChoice
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve 
open  CompletedGauss RayFourExpansion
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplifiedRetainedRadius CenteredMomentAmplificationActiveFactor
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationEligibility
open CenteredMomentAmplificationEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceRow CenteredMomentGaussNormalization
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationGlobal
open CenteredMomentSectorLocalization CenteredMomentOriginalChildEnergy
open CenteredMomentFirstScale
open CenteredMomentChildRows CenteredMomentHeckeExpansion
local notation "O"=> Eisenstein.O
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem exists_pool_error_families {ι : Type*} [Fintype ι]
    (P : Finset (Ideal O)) (hP : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (η : Character) (m : O) (hm : m≠0) (hmLam : lambda∣m) (hm2 : (2:O)∣m) :
    ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
      (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
        radicalBound (childCharacter η χ) m p.val (errorMovingExponent (errorIndex i))) ∧
      ∀ (D : OriginalData ι),
        (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
        (∀ p∈elementPool P,∀ i,∀ I∈D.S (Sum.inl i),IsCoprime (Ideal.span {p}) I) →
        ∀ (t T Z sigma D0 cLog : ℝ),0< T → 1< Z → 0≤ sigma → ∀ (j : ℤ),
        (∑p∈elementPool P,∑h∈(dyadRows j).filter (fun h => eligible D.R D.s h p),
          errorEnergy Finset.univ (sourceGenerator D.columns) (sourceGenerator_supported D.columns)
            (D.coefficient η m t T) h p)≤
        ∑p : elementPool P,∑i : Fin 3,D.childEnergy (τ p i) p (errorIndex i) t T
          (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (errorIndex i+1))) := by
  have hf (p : elementPool P) (i : Fin 3) := by
    have hd := elementPool_data P hP hbad p p.property
    have hPid := hP _ hd.2.1
    letI : (Ideal.span {p.val}).IsMaximal :=
      (Ideal.isPrime_of_prime hPid).isMaximal hPid.ne_zero
    exact CenteredMomentAmplificationRadicalFamily.exists_original_error_ball_family (ι:=ι) η m p hm hd.1 hPid hd.2.2.2.1
      hd.2.2.2.2.1 hd.2.2.2.2.2 hd.2.2.1 hmLam hm2 (errorIndex i) (errorIndex_cases i)
  choose τ hτ using hf
  refine ⟨τ,fun p i => (hτ p i).1,?_⟩
  intro D hS hprime hslot t T Z sigma D0 cLog hT hZ hsigma j
  rw [←Finset.sum_coe_sort (elementPool P)]
  apply Finset.sum_le_sum
  intro p hp
  have h0 := (hτ p 0).2 D hS hprime (hslot p p.property) t T Z sigma D0 cLog hT hZ hsigma j
  have h5 := (hτ p 1).2 D hS hprime (hslot p p.property) t T Z sigma D0 cLog hT hZ hsigma j
  have h6 := (hτ p 2).2 D hS hprime (hslot p p.property) t T Z sigma D0 cLog hT hZ hsigma j
  simpa only [errorEnergy,Finset.sum_add_distrib,Fin.sum_univ_three,
    show errorIndex 0=0 from rfl,show errorIndex 1=5 from rfl,show errorIndex 2=6 from rfl,Nat.reduceAdd] using
    add_le_add (add_le_add h0 h5) h6

theorem eventually_original_source_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta : ℝ)
    (hsigma : 0< sigma) (hloss : 0< loss) (hM : 0≤ Mmax) (hb : 0≤ b) (hgap : eta< sigma/6) :
    ∀ᶠ Z : ℝ in atTop, 1< Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : Character) (m : O),m≠0 → lambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) m p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,∀ I∈D.S (Sum.inl i),D.slot i ((Ideal.absNorm I:ℝ)/D.lengths i)≠0) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤ eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤ Z^BR → (Ideal.absNorm D.s:ℝ)≤ Z^Bs →
          ∀ (t T D0 cLog : ℝ),0< T → ∀ (j : ℤ),Real.logb Z (dyadicScale j)≤ Mmax →
          (∑' h : O,dyadicWeight j (normValue h)*
            ‖gaussPolynomial Finset.univ (sourceGenerator D.columns)
              (sourceGenerator_supported D.columns) (D.coefficient η m t T) h‖^2)≤
            (8/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (D.coefficient η m t T) ballProfile
                  (Z^(Real.logb Z (dyadicScale j)+mainGain D0 cLog sigma))).re+
                ∑p : elementPool P,∑i : Fin 3,D.childEnergy (τ p i) p (errorIndex i) t T
                  (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (errorIndex i+1)))) := by
  filter_upwards [eventually_dyadic_amplification M H hH Sbad hbad sigma loss BR Bs Mmax b eta
    hsigma hloss hM hgap] with Z hz
  obtain ⟨hZ,hP,hcard,hsep,hdata,hamp⟩ := hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hN,herr⟩ := exists_pool_error_families (ι:=ι) _
    (fun Q hQ => (hdata Q hQ).1) (fun Q hQ => (hdata Q hQ).2.1) η m hm hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hslot hsupp z hz hlen hR0 hs0 hR hs t T D0 cLog hT j hK
  have hcop (p : O) (hp : p∈elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3)))) :
      ∀i,∀I∈D.S (Sum.inl i),IsCoprime (Ideal.span {p}) I := by
    have hd := elementPool_data _ (fun Q hQ => (hdata Q hQ).1)
      (fun Q hQ => (hdata Q hQ).2.1) p hp
    exact original_slot_coprime D Z sigma b eta hZ.le hb hsep z hz hlen hsupp hslot hprime
      (Ideal.span {p}) (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
  have he := herr D hS hprime hcop t T Z sigma D0 cLog hT hZ hsigma.le j
  apply (hamp Finset.univ (sourceGenerator D.columns) (sourceGenerator_supported D.columns)
    (D.coefficient η m t T) D.R D.s hR0 hs0 hR hs j hK D0 cLog).trans
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl he) (by positivity)

theorem eventually_original_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta : ℝ)
    (hsigma : 0< sigma) (hloss : 0< loss) (hM : 0≤ Mmax) (hb : 0≤ b) (hgap : eta< sigma/6) :
    ∀ᶠ Z : ℝ in atTop, 1< Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : Character) (m : O),m≠0 → lambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) m p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤ eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤ Z^BR → (Ideal.absNorm D.s:ℝ)≤ Z^Bs →
          ∀ (t T D0 cLog : ℝ),0< T → ∀ (j : ℤ),Real.logb Z (dyadicScale j)≤ Mmax →
          (∑' h : O,dyadicWeight j (normValue h)*
            ‖gaussPolynomial Finset.univ (sourceGenerator D.columns)
              (sourceGenerator_supported D.columns) (D.coefficient η m t T) h‖^2)≤
            (8/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (D.coefficient η m t T) ballProfile
                  (Z^(Real.logb Z (dyadicScale j)+mainGain D0 cLog sigma))).re+
                ∑p : elementPool P,∑i : Fin 3,D.active.childEnergy (τ p i) p (errorIndex i) t T
                  (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (errorIndex i+1)))) := by
  filter_upwards [eventually_original_source_amplification (ι:=ι) M H hH Sbad hbad
    sigma loss BR Bs Mmax b eta hsigma hloss hM hb hgap] with Z hz
  obtain ⟨hZ,hP,hcard,hfam⟩ := hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hN,henergy⟩ := hfam η m hm hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T D0 cLog hT j hK
  have he := henergy D.active (fun i I hI => hS i I (D.active_subset i hI))
    (fun i I hI => hprime i I (D.active_subset _ hI)) D.active_slot hsupp z hz hlen
    hR0 hs0 hR hs t T D0 cLog hT j hK
  simpa only [D.active_gaussPolynomial,D.active_gaussEnergy] using he

theorem eventually_original_amplification_common {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0< sigma) (hloss : 0< loss) (hM : 0≤ Mmax) (hb : 0≤ b) (hgap : eta< sigma/6)
    (hC : 1≤ Csec) (hxi : 0≤ xi) (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop, 1< Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : Character) (m : O),m≠0 → lambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayFourExpansion.RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) m p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤ eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤ Z^BR → (Ideal.absNorm D.s:ℝ)≤ Z^Bs →
          ∀ (t T d cLog : ℝ),0< T →
          ∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0< K → 0< X →
          Tsec≤ Csec*firstNominalScale I J E K X →
          ∀ (j : ℤ),Retained (frequencyRadius Tsec Z xi) j →
          Real.logb Z (dyadicScale j)≤ Mmax →
          (∑' h : O,dyadicWeight j (normValue h)*
            ‖gaussPolynomial Finset.univ (sourceGenerator D.columns)
              (sourceGenerator_supported D.columns) (D.coefficient η m t T) h‖^2)≤
            (8/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (D.coefficient η m t T) ballProfile
                  (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z Csec xi) reserve)).re+
                ∑p : elementPool P,∑i : Fin 3,D.active.childEnergy (τ p i) p (errorIndex i) t T
                  (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z Csec xi) reserve p (errorIndex i+1))) := by
  filter_upwards [eventually_original_amplification (ι:=ι) M H hH Sbad hbad
    sigma loss BR Bs Mmax b eta hsigma hloss hM hb hgap,
    eventually_support_reserve reserve hreserve] with Z hz hsupport
  obtain ⟨hZ,hP,hcard,hfam⟩ := hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hN,henergy⟩ := hfam η m hm hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T d cLog hT
    I J E hE K X Tsec hK hX hsec j hj hMdyad
  let K0 := nominalLog I J E K X Z
  let kdyad := Real.logb Z (dyadicScale j)
  have henclose : kdyad≤ K0+frequencyLoss Z Csec xi :=
    retained_nominal_upper I J E hE K X Z Csec Tsec xi hK hX hZ
      (zero_lt_one.trans_le hC) hsec j hj
  have hδ := frequencyLoss_nonneg Z Csec xi hZ hC hxi
  have he := henergy D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T
    (d+K0-kdyad) cLog hT j hMdyad
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact main_energy_common _ _ _ _ Z d K0 kdyad cLog sigma _ reserve hZ hδ henclose hsupport.2
  · apply Finset.sum_le_sum
    intro p _
    apply Finset.sum_le_sum
    intro i _
    exact child_energy_common D.active (τ p i) p (errorIndex i) t T Z d K0 kdyad cLog sigma
      _ reserve hT.le hZ hδ henclose hsupport.2

end CenteredMomentAmplificationRadicalChoice

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open Filter

namespace CenteredMomentFirstPhysicalLedger
open CenteredMomentFirstScale CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentSectorLocalization CenteredMomentFirstExtractedLedger CenteredMomentDescentLedger
open CanonicalQuadraticSieve CenteredMomentRankinRadical
local notation "O" => Eisenstein.O

theorem nominal_log (I J E : Ideal O) (hE : E≠0)
    (Z H X : ℝ) (hH : 0< H) (hX : 0< X) :
    Real.logb Z (firstNominalScale I J E H X)=
      2*Real.logb Z X-Real.logb Z ((commonPart I J).absNorm:ℝ)-
        Real.logb Z ((commonPart J I).absNorm:ℝ)+
        Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)+
        Real.logb Z (E.absNorm:ℝ)-Real.logb Z H := by
  have hc:=norm_pos _ (commonPart_ne_zero I J)
  have hd:=norm_pos _ (commonPart_ne_zero J I)
  have he:=norm_pos E hE
  have hr:=active_norm_pos I J
  unfold firstNominalScale
  rw [Real.logb_div (mul_pos (mul_pos he hr) (sq_pos_of_pos hX)).ne'
      (mul_pos (mul_pos hH hc) hd).ne',
    Real.logb_mul (mul_pos he hr).ne' (sq_pos_of_pos hX).ne',
    Real.logb_mul he.ne' hr.ne',Real.logb_pow,
    Real.logb_mul (mul_pos hH hc).ne' hd.ne',Real.logb_mul hH.ne' hc.ne']
  push_cast
  ring

theorem retained_nominal_frequency (I J E : Ideal O) (hE : E≠0)
    (Z H X Tsec Csec ξ : ℝ) (hZ : 1< Z) (hH : 0< H) (hX : 0< X)
    (hC : 0< Csec) (hsec : Tsec≤ Csec*firstNominalScale I J E H X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z ξ) n) :
    Real.logb Z (dyadicScale n)≤
      Real.logb Z (firstNominalScale I J E H X)+frequencyLoss Z Csec ξ := by
  apply retained_first_dyad_enclosure Tsec Z Csec _ ξ hZ hC _ n hn
  simpa only [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne'
    (firstNominalScale_pos I J E hE H X hH hX)] using hsec

theorem retained_deficit (I J E : Ideal O) (hE : E≠0)
    (Z H X Tsec Csec ξ : ℝ) (hZ : 1< Z) (hH : 0< H) (hX : 0< X)
    (hC : 0< Csec) (hsec : Tsec≤ Csec*firstNominalScale I J E H X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z ξ) n) :
    Real.logb Z ((commonPart J I).absNorm:ℝ)-frequencyLoss Z Csec ξ≤
      Real.logb Z ((commonPart J I).absNorm:ℝ)+
        Real.logb Z (firstNominalScale I J E H X)-Real.logb Z (dyadicScale n) := by
  linarith [retained_nominal_frequency I J E hE Z H X Tsec Csec ξ hZ hH hX hC hsec n hn]

theorem frequency_loss_eventually (Csec ξ : ℝ) (hC : 0< Csec) (hξ : 0<ξ) :
    ∃Z₀ : ℝ,1< Z₀ ∧ ∀Z : ℝ,Z₀≤ Z → 1< Z ∧ frequencyLoss Z Csec ξ<ξ := by
  have hg := (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (show 0<ξ/4 by linarith))) (4*Csec)
  obtain ⟨Z₀,hZ₀⟩:=Filter.eventually_atTop.1 (hg.and (Filter.eventually_gt_atTop (1:ℝ)))
  refine ⟨max Z₀ 2,by linarith [le_max_right Z₀ (2:ℝ)],?_⟩
  intro Z hZ
  obtain ⟨hb,hZ1⟩:=hZ₀ Z ((le_max_left Z₀ 2).trans hZ)
  have hl:=Real.logb_le_logb_of_le hZ1 (show 0<4*Csec by positivity) hb
  rw [Real.logb_rpow (zero_lt_one.trans hZ1) hZ1.ne'] at hl
  exact ⟨hZ1,by unfold frequencyLoss;linarith⟩

theorem actual_first_saving (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hE : E≠0) (Z H X Tsec Csec ξ q w wo ell σ branch : ℝ)
    (hZ : 1< Z) (hH : 0< H) (hX : 0< X) (hC : 1≤ Csec)
    (hξ : 0≤ξ) (hsec : Tsec≤ Csec*firstNominalScale I J E H X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z ξ) n)
    (hq : 0≤ q) (hw : 0≤ w) (hwo : 0≤ wo) (hell : 0≤ ell) (hσ : 0≤σ)
    (hbranch : branch≤2) (hwσ : w≤7*σ/3) :
    let c:=Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d:=Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p:=Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R:=Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let e:=Real.logb Z (E.absNorm:ℝ)
    let D₀:=d+Real.logb Z (firstNominalScale I J E H X)-Real.logb Z (dyadicScale n)
    2*(c+w)/3-3*σ-5*(frequencyLoss Z Csec ξ)/6≤
      firstSaving c D₀ w (q+R+e) wo (c+d-2*p-R)
        (max (D₀-c-2*w+wo) 0+branch*σ) ell := by
  dsimp only
  have hRn : (1:ℝ)≤((Ideal.span {activeConductor I J}).absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr
        (SchwartzPlanePoisson.finitePrimeModulus_ne_zero _)))
  have hEn : (1:ℝ)≤(E.absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hE)
  have hR:=Real.logb_nonneg hZ hRn
  have he:=Real.logb_nonneg hZ hEn
  apply actual_extracted_first_saving I J hI hJ Z hZ _ _ _ _ _ _ _ _ hw
    (by linarith) hwo hσ (frequencyLoss_nonneg Z Csec ξ hZ hC hξ)
    (by linarith) (retained_deficit I J E hE Z H X Tsec Csec ξ hZ hH hX
      (by linarith) hsec n hn) _ hell hwσ
  nlinarith

end CenteredMomentFirstPhysicalLedger

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

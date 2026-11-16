import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.AngularFrozenSources
import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.OriginalResidualControl

/-!
# Residual-row reconstruction of angular completed sources

Supported slot splitting separates active angular cusp reflection from inactive
prime weights. Exact residual-row reconstruction retains the original finite Fourier
coefficients and frozen weights; only the reflected kernel and unit phases change.
-/

open scoped BigOperators Classical ContDiff MatrixGroups Matrix
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection CanonicalQuadraticSieve
open InverseMoment
namespace InverseReflectedPhase
noncomputable section
local notation "Eis" => Eisenstein.O
section
variable (ℓ : ℕ)
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))

variable (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,lambda∉P)

variable {τ : Type*} [Fintype τ] (Frozen : PrimeFamily τ) {N a c : Eis} {mode : Bool}
variable (T : Finset σ)
    (C : ∀ _b : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ∀ p : supportedSlotChoices (fun i : T => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ControlledStratumArithmetic (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F))
        (residualPart_admissible I (Ideal.span {m}*F) hbad)
        (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator N a c mode)

lemma angularOriginalSplitControlled_value (p : originalSlotChoices D Q₀ L)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : τ→ℕ) (W : ℝ→ℂ) (X : ℝ) :
    angularMixedReflectedValue ℓ
      (originalSplitControlled D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood Frozen T C p) s
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (residualPart_admissible I (Ideal.span {m}*F) hbad)
        ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_ne_zero hc
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (residualPart_admissible I (Ideal.span {m}*F) hbad)
        ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_good
      (reflectedExponent jF) (slotIndices τ (PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) T) W X=
    let q := originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T p
    angularMixedReflectedValue ℓ (C q.1 q.2) s
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (residualPart_admissible I (Ideal.span {m}*F) hbad)
        (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) q.2.val)).generator_ne_zero hc
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (residualPart_admissible I (Ideal.span {m}*F) hbad)
        (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) q.2.val)).generator_good
      (reflectedExponent jF) (slotIndices τ (PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) T) W X := by
  exact angularMixedReflectedValue_cast ℓ _ _ s _ _ hc _ _ _ _ W X

end

section
variable (ℓ : ℕ)
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))

variable (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,lambda∉P)

variable {τ : Type*} [Fintype τ] (Frozen : PrimeFamily τ) {N a c : Eis} {mode : Bool}
variable (T : Finset σ)
    (C : ∀ _b : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ∀ p : supportedSlotChoices (fun i : T => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ControlledStratumArithmetic (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F))
        (residualPart_admissible I (Ideal.span {m}*F) hbad)
        (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator N a c mode)

def angularOriginalSplitPhysical
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : τ→ℕ) (W : ℝ→ℂ) (X : ℝ)
    (q : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
      ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)) ×
      supportedSlotChoices (fun i : T => L i.val)
      ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F))) : ℂ :=
  angularMixedReflectedValue ℓ (C q.1 q.2) s
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (residualPart_admissible I (Ideal.span {m}*F) hbad)
        (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) q.2.val)).generator_ne_zero hc
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (residualPart_admissible I (Ideal.span {m}*F) hbad)
        (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) q.2.val)).generator_good
      (reflectedExponent jF) (slotIndices τ (PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) T) W X
lemma angularOriginalSplitControlled_physical (p : originalSlotChoices D Q₀ L)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : τ→ℕ) (W : ℝ→ℂ) (X : ℝ) :
    angularMixedReflectedValue ℓ
      (originalSplitControlled D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood Frozen T C p) s
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (residualPart_admissible I (Ideal.span {m}*F) hbad)
        ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_ne_zero hc
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (residualPart_admissible I (Ideal.span {m}*F) hbad)
        ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_good
      (reflectedExponent jF) (slotIndices τ (PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) T) W X=
    angularOriginalSplitPhysical ℓ R I F Q₀ hbad L hmax hgood Frozen T C s hc jF W X
      (originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T p) := by
  exact angularOriginalSplitControlled_value ℓ D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
    L hmax hgood Frozen T C p s hc jF W X

end

section
variable (ℓ : ℕ)
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime (Q*Ideal.span {(72:Eis)}) (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,lambda∉P)

theorem angular_actual_marked_slot_split_reflection
    (hS : ∀ p : ∀ i,L i,Pairwise (Function.onFun IsCoprime (slotChoiceFamily L hmax hgood p).ideal))
    (hSodd : ∀ p : ∀ i,L i,∀ i,ringChar (Eis⧸(slotChoiceFamily L hmax hgood p).ideal i)≠2)
    (Ψ : Eis→*ℂ) (hQ : Q≠0)
    (hΨperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (hmLam : lambda∣m) (hm2 : (2:Eis)∣m)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤ Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G : ∀ h : Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h,(9:Eis)*(G h).c0∣N)
    (hNp : ∀ p : ∀ i,L i,∀ i,IsCoprime (Ideal.span {N}) ((markedRowFamily D (slotChoiceFamily L hmax hgood p) Q).ideal i))
    (C : ∀ p : originalSlotChoices D (Q*Ideal.span {(72:Eis)}) L,
      ∀ h : Eis⧸Ideal.span {c},∀ A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
      ∀ T : Finset σ,ControlledStratumArithmetic
        (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected (rowResidualPart I (Ideal.span {m}*F)) (residualPart_admissible I (Ideal.span {m}*F) hbad) ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator
        N (G h).a0 (G h).c0 (G h).mode)
    (w : ∀ i,L i→ℂ) (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0< lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0< X) :
    (∑ p : ∀ i,L i,(∏ i,w i (p i))*markedCompletedT (angularSourceTwist ℓ (rowTwist Ψ m f z)) W X
      (fun A => ∏ i,if (slotChoiceFamily L hmax hgood p).ideal i∣A then (1:ℂ) else 0))=
    let physical := fun (h : Eis⧸Ideal.span {c})
      (A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})))
      (T : Finset σ) (p : originalSlotChoices D (Q*Ideal.span {(72:Eis)}) L) =>
      angularMixedReflectedValue ℓ (C p h A T) (G h).shape
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected (rowResidualPart I (Ideal.span {m}*F)) (residualPart_admissible I (Ideal.span {m}*F) hbad) ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_ne_zero
            (G h).denominator_ne_zero
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected (rowResidualPart I (Ideal.span {m}*F)) (residualPart_admissible I (Ideal.span {m}*F) hbad) ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_good
            (reflectedExponent (fun b : A => completedLocalExponent R F b.val.val))
            (slotIndices A (PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) T) W X
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h*
      ∑ A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
        frozenInactiveWeight R F (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)}) A*
        ∑ T : Finset σ,
          ∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
            ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal)
            (rowResidualPart I (Ideal.span {m}*F)),
            ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*
              ∑ a : supportedSlotChoices (fun i : T => L i.val)
                ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal)
                (rowResidualPart I (Ideal.span {m}*F)),
                (∏ i : T,w i.val (a.val i))*physical h A T
                  ((originalSlotSplit D R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T).symm (b,a)) := by
  dsimp only
  rw [angular_actual_marked_tuple_reflection ℓ D R I F Q hR hI hF hm hf hz hbad hcop hpow hmask
    (fun p : ∀ i,L i => slotChoiceFamily L hmax hgood p) hS hSodd Ψ hQ hΨperiod hmLam hm2
    c hc hcQ G N hN hNp C (fun p => ∏ i,w i (p i)) W hWcompact lo hi hlo hsupp hW X hX]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  congr 1
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  congr 1
  have hs :=
    (original_supported_slot_sum D R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask
      L hmax hgood T w (fun p => angularMixedReflectedValue ℓ (C p h A T) (G h).shape
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected (rowResidualPart I (Ideal.span {m}*F)) (residualPart_admissible I (Ideal.span {m}*F) hbad) ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_ne_zero
            (G h).denominator_ne_zero
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected (rowResidualPart I (Ideal.span {m}*F)) (residualPart_admissible I (Ideal.span {m}*F) hbad) ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_good
            (reflectedExponent (fun b : A => completedLocalExponent R F b.val.val))
            (slotIndices A (PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) T) W X))
  convert hs using 1
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  congr 1
  apply Finset.prod_congr (by ext; simp only [Finset.mem_sdiff,Finset.mem_univ])
  intro t ht
  rfl

end

section
variable (ℓ : ℕ)
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime (Q*Ideal.span {(72:Eis)}) (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,lambda∉P)

include hR hI hF hm hf hz hbad hcop hpow hmask

theorem angular_actual_marked_active_reflection
    (hS : ∀ p : ∀ i,L i,Pairwise (Function.onFun IsCoprime (slotChoiceFamily L hmax hgood p).ideal))
    (hSodd : ∀ p : ∀ i,L i,∀ i,ringChar (Eis⧸(slotChoiceFamily L hmax hgood p).ideal i)≠2)
    (Ψ : Eis→*ℂ) (hQ : Q≠0)
    (hΨperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (hmLam : lambda∣m) (hm2 : (2:Eis)∣m)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤ Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G : ∀ h : Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h,(9:Eis)*(G h).c0∣N)
    (hNp : ∀ p : ∀ i,L i,∀ i,IsCoprime (Ideal.span {N}) ((markedRowFamily D (slotChoiceFamily L hmax hgood p) Q).ideal i))
    (C : ∀ h : Eis⧸Ideal.span {c},
      ∀ A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
      ∀ T : Finset σ,
      ∀ _b : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ∀ p : supportedSlotChoices (fun i : T => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ControlledStratumArithmetic
        (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected
          (rowResidualPart I (Ideal.span {m}*F)) (residualPart_admissible I (Ideal.span {m}*F) hbad)
          (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator
        N (G h).a0 (G h).c0 (G h).mode)
    (w : ∀ i,L i→ℂ) (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0< lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0< X) :
    (∑ p : ∀ i,L i,(∏ i,w i (p i))*markedCompletedT (angularSourceTwist ℓ (rowTwist Ψ m f z)) W X
      (fun A => ∏ i,if (slotChoiceFamily L hmax hgood p).ideal i∣A then (1:ℂ) else 0))=
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h*
      ∑ A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
        frozenInactiveWeight R F (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)}) A*
        ∑ T : Finset σ,
          ∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
            ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal)
            (rowResidualPart I (Ideal.span {m}*F)),
            ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*
              ∑ a : supportedSlotChoices (fun i : T => L i.val)
                ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal)
                (rowResidualPart I (Ideal.span {m}*F)),
                (∏ i : T,w i.val (a.val i))*
                  angularOriginalSplitPhysical ℓ R I F (Q*Ideal.span {(72:Eis)}) hbad L hmax hgood
                    ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A)
                    T (C h A T) (G h).shape (G h).denominator_ne_zero
                    (fun b : A => completedLocalExponent R F b.val.val) W X (b,a) := by
  let Call := fun (p : originalSlotChoices D (Q*Ideal.span {(72:Eis)}) L)
    (h : Eis⧸Ideal.span {c})
    (A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)}))) (T : Finset σ) =>
      originalSplitControlled D R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood
        ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A) T (C h A T) p
  rw [angular_actual_marked_slot_split_reflection ℓ D R I F Q hR hI hF hm hf hz hbad hcop hpow hmask
    L hmax hgood hS hSodd Ψ hQ hΨperiod hmLam hm2 c hc hcQ G N hN hNp Call
    w W hWcompact lo hi hlo hsupp hW X hX]
  dsimp only
  apply congrArg (fun z : ℂ => thetaDerivativeScalar⁻¹*z)
  apply Finset.sum_congr rfl
  intro h hh
  apply congrArg (fun z : ℂ => fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h*z)
  apply Finset.sum_congr rfl
  intro A hA
  apply congrArg (fun z : ℂ => frozenInactiveWeight R F (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)}) A*z)
  apply Finset.sum_congr rfl
  intro T hT
  apply Finset.sum_congr rfl
  intro b hb
  apply congrArg (fun z : ℂ =>
    ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*z)
  apply Finset.sum_congr rfl
  intro a ha
  apply congrArg (fun z : ℂ => (∏ i : T,w i.val (a.val i))*z)
  dsimp only [Call]
  have hv := angularOriginalSplitControlled_physical ℓ D R I F (Q*Ideal.span {(72:Eis)})
    hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood
    ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A) T (C h A T)
    ((originalSlotSplit D R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T).symm (b,a))
    (G h).shape (G h).denominator_ne_zero (fun b : A => completedLocalExponent R F b.val.val) W X
  exact hv.trans (congrArg
    (angularOriginalSplitPhysical ℓ R I F (Q*Ideal.span {(72:Eis)}) hbad L hmax hgood
      ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A) T (C h A T)
      (G h).shape (G h).denominator_ne_zero (fun b : A => completedLocalExponent R F b.val.val) W X)
    ((originalSlotSplit D R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T).apply_symm_apply (b,a)))

end

section
variable (ℓ : ℕ)
variable {σ φ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]
variable {N a c : Eis} {mode : Bool}
variable (G : PrimeFamily τ) (FF : φ→Ideal Eis) (rows : Finset (Ideal Eis)) (hrows : ∀ K∈rows,Admissible K)
    (lists : σ→Finset (Ideal Eis)) (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈lists i,lambda∉P) (T : Finset σ)

def angularOriginalInactivePhysical
    (D : OriginalSplitCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G FF rows hrows lists hmax hgood T)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : τ→ℕ) (W : ℝ→ℂ) (X : ℝ) (w : ∀ i,lists i→ℂ) (K : rows) : ℂ :=
    ∑ b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val) FF K.val,
      ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*
      ∑ p : supportedSlotChoices (fun i : T => lists i.val) FF K.val,
        (∏ i : T,w i.val (p.val i))*angularMixedReflectedValue ℓ (D K b p) s
        (G.reflected K.val (hrows K.val K.property)
          (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_ne_zero hc
        (G.reflected K.val (hrows K.val K.property)
          (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_good
        (reflectedExponent jF) (slotIndices τ (PrimeIndex K.val) T) W X
end

section
variable (ℓ : ℕ)
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable (parents : Finset (Ideal Eis)) (J F : Ideal Eis) (hJ : J≠0) (hF : Squarefree F)
    (m : Eis) (hm : m≠0) (hparents : ∀ I∈parents,I≠0) (v : Eisˣ)
    (hbad : ∀ P∈fixedBadPrimes,P∣Ideal.span {m}*F)

variable (Q : Ideal Eis) (hQ : Q≠0) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G : ∀ h : Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (hcop : ∀ K∈originalResidualRows parents J (Ideal.span {m}*F),IsCoprime (Q*Ideal.span {(72:Eis)}) K)
    (lists : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈lists i,lambda∉P)
    (hdis : Pairwise (fun i j => Disjoint (lists i) (lists j)))
    (hodd : ∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2)
    (hperiod : ∀ i,∀ P∈lists i,IsCoprime (Q*Ideal.span {(72:Eis)}) P)

variable (D : ∀ h : Eis⧸Ideal.span {c},∀ A : Finset (FreeReflection.pool J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
    ∀ T : Finset σ,OriginalSplitCompletion (N:=(9:Eis)*c) (a:=(G h).a0) (c:=(G h).c0) (mode:=(G h).mode)
      ((poolPrimeFamily J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A)
      (poolPrimeFamily J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal
      (originalResidualRows parents J (Ideal.span {m}*F)) (originalResidualAdmissible parents J F m hbad)
      lists hmax hgood T)

include hJ hQ hcQ hcop hdis hodd hperiod

theorem angular_original_completed_residual_source
    (Ψ : Eis→*ℂ) (hΨperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (hmLam : lambda∣m) (hm2 : (2:Eis)∣m)
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W) (lo hi : ℝ) (hlo : 0< lo)
    (hsupp : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0< X)
    (w : ∀ i,lists i→ℂ) (K : originalResidualRows parents J (Ideal.span {m}*F)) :
    (∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (angularSourceTwist ℓ (rowTwist Ψ m (cubicIdealGenerator F)
        (v.val*cubicIdealGenerator (reconstructFiberRow J (Ideal.span {m}*F) K.val)))) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0))=
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c},
      fixedThetaRowCoeff c hc ((residualOriginalData parents J F hF m hm hparents v K).fixedFactor Ψ Q) h*
        ∑ A : Finset (FreeReflection.pool J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
          frozenInactiveWeight J F (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)}) A*
          ∑ T : Finset σ,angularOriginalInactivePhysical ℓ
            ((poolPrimeFamily J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A)
            (poolPrimeFamily J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal
            (originalResidualRows parents J (Ideal.span {m}*F)) (originalResidualAdmissible parents J F m hbad)
            lists hmax hgood T (D h A T) (G h).shape (G h).denominator_ne_zero
            (fun b : A => completedLocalExponent J F b.val.val) W X w K := by
  rcases K with ⟨K,hK⟩
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
  have hI0 := hparents I (Finset.mem_filter.mp hI).1
  have hrec := reconstructFiberRow_of_original parents J (Ideal.span {m}*F) I hI hI0
  obtain ⟨hIp,hpow,hmask⟩ := Finset.mem_filter.mp hI
  let K : originalResidualRows parents J (Ideal.span {m}*F) :=
    ⟨rowResidualPart I (Ideal.span {m}*F),Finset.mem_image.mpr ⟨I,Finset.mem_filter.mpr ⟨hIp,hpow,hmask⟩,rfl⟩⟩
  let D0 := residualOriginalData parents J F hF m hm hparents v K
  have hz : Ideal.span {v.val*cubicIdealGenerator (reconstructFiberRow J (Ideal.span {m}*F) K.val)}=I := by
    rw [Ideal.span_singleton_mul_left_unit v.isUnit,span_cubicIdealGenerator]
    exact hrec
  have hS : ∀ p : ∀ i,lists i,Pairwise (Function.onFun IsCoprime (slotChoiceFamily lists hmax hgood p).ideal) := by
    intro p i j hij
    apply Ideal.isCoprime_of_isMaximal
    intro he
    change (p i).val=(p j).val at he
    exact Finset.disjoint_left.mp (hdis hij) (p i).property (he.symm ▸ (p j).property)
  have he := angular_actual_marked_active_reflection ℓ D0 J I F Q hJ hI0 hF hm
    (span_cubicIdealGenerator F) hz hbad
    (hcop K.val K.property) hpow.symm hmask.symm lists hmax hgood hS
    (fun p i => hodd i _ (p i).property) Ψ hQ hΨperiod hmLam hm2 c hc hcQ.le G ((9:Eis)*c)
    (fun h => mul_dvd_mul_left (9:Eis) (G h).denominator_dvd)
    (fun p => markedRowFamily_period D0 (slotChoiceFamily lists hmax hgood p) Q
      (fun i => hperiod i _ (p i).property) c hcQ)
    (fun h A T b p => D h A T K b p)
    w W hWcompact lo hi hlo hsupp hW X hX
  exact he
end

end
end InverseReflectedPhase
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

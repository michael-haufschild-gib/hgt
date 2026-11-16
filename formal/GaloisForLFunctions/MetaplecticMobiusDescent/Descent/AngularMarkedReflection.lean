import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.AngularMarkedSources
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.AngularControlledReflection
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.MixedReflectedValues

/-!
# Angular reflection of marked completed sources

Prime marking is finite inclusion–exclusion. Angular twisting commutes with every mask,
so Fourier inversion still acts only on the original finite coefficients. Equality of
finite phase multipliers gives equality of actual angular cusp-kernel sums.
-/

open Complex
open scoped BigOperators Classical ContDiff ComplexConjugate
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion NormalizedReflection
open GaloisForLFunctions.FamilyContinuationTheory
namespace InverseMoment
noncomputable section
local notation "Eis" => Eisenstein.O

theorem angular_cusp_kernel_sum_congr (ℓ : ℕ) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d : ι → SourceCuspDatum) (w : ι → ℂ)
    (e : κ → SourceCuspDatum) (z : κ → ℂ)
    (hmult : ∀ n : Eis,
      (∑ i, w i * tracePhase (-cuspFrequency n * (d i).point)) =
        ∑ k, z k * tracePhase (-cuspFrequency n * (e k).point))
    (W : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo)
    (hsupp : Function.support W ⊆ Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    (∑ i, w i * (d i).angularSmoothedKernel ℓ W X) =
      ∑ k, z k * (e k).angularSmoothedKernel ℓ W X := by
  have hsum := weighted_compact_test_norm_summable sourceCuspRadialLength sourceCuspRadialLength_pos
    (fun h => elemPsiSix h ^ ℓ * sourceBarRadialCoefficient 0 h) (3 / 2)
    (angularSourceBar_weighted_summable ℓ 0) (Vstar W) lo hi hlo
    (Vstar_support W lo hi hsupp) (Vstar_contDiff W lo hi hlo hsupp hW) X hX
  have htest : Summable (fun h : Eis => ‖sourceBarRadialCoefficient 0 h *
      (elemPsiSix h ^ ℓ * Vstar W (sourceCuspRadialLength h / X))‖) := by
    simpa only [mul_assoc,mul_left_comm] using hsum
  have he : (∑ i, w i * ∑' h : Eis, sourceBarRadialCoefficient (d i).point h *
      (elemPsiSix h ^ ℓ * Vstar W (sourceCuspRadialLength h / X))) =
      ∑ k, z k * ∑' h : Eis, sourceBarRadialCoefficient (e k).point h *
        (elemPsiSix h ^ ℓ * Vstar W (sourceCuspRadialLength h / X)) := by
    rw [sourceBar_smoothed_phase_translation _ _ _ htest,
      sourceBar_smoothed_phase_translation _ _ _ htest]
    simp_rw [hmult]
  simp_rw [SourceCuspDatum.angularSmoothedKernel_source _ ℓ W lo hi hlo hsupp hW X hX]
  simpa only [mul_assoc,mul_left_comm] using he

theorem angular_markedCompletedT_canonical_reflection (ℓ : ℕ) {ι : Type*} (p : ι → Eis) (S : Finset ι)
    (hp : ∀ i ∈ S, Prime (p i))
    (Ψ : Eis →* ℂ)
    (Q : Ideal Eis) (hperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * (Q * Ideal.span {∏ i ∈ S, p i}))
    (W : ℝ → ℂ) (hWcompact : HasCompactSupport W)
    (v0 v1 : ℝ) (hv0 : 0 < v0) (hWs : Function.support W ⊆ Set.Icc v0 v1)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT (angularSourceTwist ℓ Ψ) W X (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      thetaDerivativeScalar⁻¹ * ∑ h : Eis ⧸ Ideal.span {c},
        finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc) (markedThetaQuotient p S Ψ c) h *
          (finiteTwistCusp c hc h).angularSmoothedKernel ℓ W X := by
  have hper (T : Finset ι) (hT : T ∈ S.powerset) :
      CanonicalCoefficientClass.FactorsModulo (Q * Ideal.span {∏ i ∈ S, p i})
        (markTwist p T * Ψ) := by
    intro x y hxy
    simp only [MonoidHom.mul_apply]
    rw [markTwist_periodic p S T (Finset.mem_powerset.mp hT) x y (Ideal.mul_le_left hxy),
      hperiod x y (Ideal.mul_le_right hxy)]
  have hcoeff (h : Eis ⧸ Ideal.span {c}) :
      finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc) (markedThetaQuotient p S Ψ c) h =
        ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
          finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc)
            (fixedThetaQuotient (markTwist p T * Ψ) c) h := by
    unfold finiteAdditiveFourierCoeff
    simp_rw [markedThetaQuotient_twists p S hp Ψ c]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_div, Finset.mul_sum, mul_div_assoc, mul_assoc]
  rw [markedCompletedT_prime_product_twists S p hp (angularSourceTwist ℓ Ψ) W hWcompact X hX]
  simp_rw [angularSourceTwist_mul_left]
  change (∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * completedIdealT (angularSourceTwist ℓ (markTwist p T * Ψ)) W X) = _
  calc
    _ = ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * (thetaDerivativeScalar⁻¹ *
        ∑ h : Eis ⧸ Ideal.span {c}, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc)
          (fixedThetaQuotient (markTwist p T * Ψ) c) h *
            (finiteTwistCusp c hc h).angularSmoothedKernel ℓ W X) := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [completedIdealT_eq_completedT _ W hWcompact X hX, completedT_angular_canonical_smoothed_reflection ℓ _ _ (hper T hT)
        c hc hcQ W v0 v1 hv0 hWs hW X hX]
    _ = _ := by
      simp_rw [hcoeff]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro T hT
      ring


theorem angular_markedCompletedT_of_cusp_multiplier (ℓ : ℕ) {ι κ : Type*} [Fintype κ]
    (p : ι → Eis) (S : Finset ι) (hp : ∀ i ∈ S, Prime (p i))
    (Ψ : Eis →* ℂ)
    (Q : Ideal Eis) (hperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * (Q * Ideal.span {∏ i ∈ S, p i}))
    (d : κ → SourceCuspDatum) (w : κ → ℂ)
    (hmult : ∀ n : Eis, (∑ k, w k * tracePhase (-cuspFrequency n * (d k).point)) =
      markedThetaQuotient p S Ψ c (Ideal.Quotient.mk _ n))
    (W : ℝ → ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0 < lo) (hsupp : Function.support W ⊆ Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT (angularSourceTwist ℓ Ψ) W X (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      thetaDerivativeScalar⁻¹ * ∑ k, w k * (d k).angularSmoothedKernel ℓ W X := by
  rw [angular_markedCompletedT_canonical_reflection ℓ p S hp Ψ Q hperiod c hc hcQ
    W hWcompact lo hi hlo hsupp hW X hX]
  congr 1
  apply angular_cusp_kernel_sum_congr ℓ (finiteTwistCusp c hc)
    (finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc)
      (markedThetaQuotient p S Ψ c)) d w ?_ W lo hi hlo hsupp hW X hX
  intro n
  simp_rw [finiteTwistCusp_point]
  rw [thetaFourierTranslation_inversion c hc, hmult]


noncomputable local instance angularActiveReflectionQuotientFintype
    (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

theorem angular_markedCompletedT_fixed_active_strata (ℓ : ℕ) {ι : Type*} [Fintype ι]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hprime : ∀ i, Prime (p i))
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι)
    (φ : Eis →* ℂ)
    (Q : Ideal Eis) (hφperiod : CanonicalCoefficientClass.FactorsModulo Q φ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * Q)
    (G : ∀ h : Eis ⧸ Ideal.span {c}, FixedFourierGeometry c h) (N : Eis)
    (hN : ∀ h, (9 : Eis) * (G h).c0 ∣ N)
    (D : ∀ h : Eis ⧸ Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => p i.val) N (G h).a0 (G h).c0 (G h).mode)
    (call : Eis) (hcall : call ≠ 0) [Fintype (Eis ⧸ Ideal.span {call})]
    (hcallQ : Ideal.span {call} ≤ Ideal.span {(9 : Eis)} *
      ((Q * Ideal.span {∏ i, p i}) * Ideal.span {∏ i ∈ S, p i}))
    (W : ℝ → ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0 < lo) (hsupp : Function.support W ⊆ Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT (angularSourceTwist ℓ (φ * unmarkedSexticTwist p hg j S)) W X
      (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      thetaDerivativeScalar⁻¹ * ∑ t : FixedActiveCuspIndex c p,
        fixedActiveFunctionWeight p hp (mixedPrimeFunction p hg j S) c hc φ t *
          (fixedActiveCuspDatum p hp hprimary c G N hN D t).angularSmoothedKernel ℓ W X := by
  have hperiod : CanonicalCoefficientClass.FactorsModulo (Q * Ideal.span {∏ i, p i})
      (φ * unmarkedSexticTwist p hg j S) := by
    intro x y hxy
    simp only [MonoidHom.mul_apply]
    rw [hφperiod x y (Ideal.mul_le_right hxy),
      unmarkedSexticTwist_periodic p hg j S x y (Ideal.mul_le_left hxy)]
  apply angular_markedCompletedT_of_cusp_multiplier ℓ p S (fun i _ => hprime i) _ _ hperiod
    call hcall hcallQ (fixedActiveCuspDatum p hp hprimary c G N hN D)
    (fixedActiveFunctionWeight p hp (mixedPrimeFunction p hg j S) c hc φ) ?_
    W hWcompact lo hi hlo hsupp hW X hX
  intro n
  rw [fixedActiveFunction_multiplier p hp hprimary (mixedPrimeFunction p hg j S)
    c hc G N hN D Q hcQ φ hφperiod,
    markedThetaQuotient_mk p S _ _ hperiod call hcallQ,
    fixedThetaTwist_mul, mixedPrimeFunction_product]
  ring


end
end InverseMoment
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

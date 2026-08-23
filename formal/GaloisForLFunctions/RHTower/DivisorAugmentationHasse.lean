import GaloisForLFunctions.HTGeometry.HasseExactSequence
import GaloisForLFunctions.RHTower.DivisorAugmentationExactSequence

/-!
# Hasse classification of divisor reporter packets

A finite packet of differential symbols has one global common-mode symbol: its augmentation.  The
packet modulo zero-sum relative reporters is therefore the polynomial symbol group.  At a simple
pole the common meromorphic mode detects precisely this quotient, so observational equivalence of
reporter packets is congruence modulo the augmentation kernel.
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-- Differential-symbol packets modulo zero-sum relative reporters are single symbols. -/
noncomputable def differentialSymbolAugmentationHasseQuotientEquiv
    {I : Type*} [Fintype I] [Nonempty I] :
    ((I → Polynomial ℂ) ⧸
      (differentialSymbolAugmentation : (I → Polynomial ℂ) →+ Polynomial ℂ).ker) ≃+
      Polynomial ℂ :=
  QuotientAddGroup.quotientKerEquivOfSurjective differentialSymbolAugmentation
    differentialSymbolAugmentation_surjective

/-- The divisor-packet Hasse equivalence is induced by symbol augmentation. -/
@[simp] theorem differentialSymbolAugmentationHasseQuotientEquiv_mk
    {I : Type*} [Fintype I] [Nonempty I] (L : I → Polynomial ℂ) :
    differentialSymbolAugmentationHasseQuotientEquiv (QuotientAddGroup.mk L) =
      differentialSymbolAugmentation L := by
  rfl

/-- Two reporter packets have the same total symbol exactly when their difference is zero-sum. -/
theorem differentialSymbolAugmentation_congr_hasse_iff
    {I : Type*} [Fintype I] (L M : I → Polynomial ℂ) :
    L - M ∈ (differentialSymbolAugmentation :
      (I → Polynomial ℂ) →+ Polynomial ℂ).ker ↔
      differentialSymbolAugmentation L = differentialSymbolAugmentation M := by
  change differentialSymbolAugmentation (L - M) = 0 ↔ _
  rw [map_sub, sub_eq_zero]

/-- Every common symbol has a packet representative, unique modulo zero-sum relative reporters. -/
theorem differentialSymbolAugmentation_exists_unique_mod_zeroSum
    {I : Type*} [Fintype I] [Nonempty I] (P : Polynomial ℂ) :
    ∃ L : I → Polynomial ℂ, differentialSymbolAugmentation L = P ∧
      ∀ M, differentialSymbolAugmentation M = P ↔
        M - L ∈ (differentialSymbolAugmentation :
          (I → Polynomial ℂ) →+ Polynomial ℂ).ker := by
  obtain ⟨L, hL⟩ := differentialSymbolAugmentation_surjective (I := I) P
  refine ⟨L, hL, fun M => ?_⟩
  rw [← hL]
  exact (differentialSymbolAugmentation_congr_hasse_iff (I := I) M L).symm

/-- At a simple pole, reporter packets are observationally congruent exactly when their difference
is a zero-sum relative packet. -/
theorem commonModeDifferentialOperator_congr_hasse_iff
    {I : Type*} [Fintype I] {f : ℂ → ℂ} {ρ : ℂ}
    (hf : MeromorphicAt f ρ)
    (horder : meromorphicOrderAt f ρ = ((-1 : ℤ) : WithTop ℤ))
    (L M : I → Polynomial ℂ) :
    L - M ∈ (differentialSymbolAugmentation :
      (I → Polynomial ℂ) →+ Polynomial ℂ).ker ↔
      commonModeDifferentialOperatorHom f L = commonModeDifferentialOperatorHom f M := by
  rw [← ker_commonModeDifferentialOperatorHom_eq_ker_augmentation hf horder]
  change commonModeDifferentialOperatorHom f (L - M) = 0 ↔ _
  rw [map_sub, sub_eq_zero]

/-- At a simple pole, quotienting packets by complete common-mode observational equivalence leaves
exactly one polynomial symbol. -/
noncomputable def commonModeDivisorHasseQuotientEquiv
    {I : Type*} [Fintype I] [Nonempty I] {f : ℂ → ℂ} {ρ : ℂ}
    (hf : MeromorphicAt f ρ)
    (horder : meromorphicOrderAt f ρ = ((-1 : ℤ) : WithTop ℤ)) :
    ((I → Polynomial ℂ) ⧸
      (commonModeDifferentialOperatorHom f :
        (I → Polynomial ℂ) →+ (ℂ → ℂ)).ker) ≃+ Polynomial ℂ :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (ker_commonModeDifferentialOperatorHom_eq_ker_augmentation hf horder)).trans
      differentialSymbolAugmentationHasseQuotientEquiv

/-- The common-mode divisor equivalence also sends a packet to its total symbol. -/
@[simp] theorem commonModeDivisorHasseQuotientEquiv_mk
    {I : Type*} [Fintype I] [Nonempty I] {f : ℂ → ℂ} {ρ : ℂ}
    (hf : MeromorphicAt f ρ)
    (horder : meromorphicOrderAt f ρ = ((-1 : ℤ) : WithTop ℤ))
    (L : I → Polynomial ℂ) :
    commonModeDivisorHasseQuotientEquiv hf horder (QuotientAddGroup.mk L) =
      differentialSymbolAugmentation L := by
  simp [commonModeDivisorHasseQuotientEquiv]

end

end RHTower

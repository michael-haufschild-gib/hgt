import GaloisForLFunctions.HTGeometry.EulerOrdinaryDerivationBridge

/-!
# Rescaling a derivation and multiplying by a base element

Differential algebraicity over a differential base field is insensitive to rescaling the
derivation of the extension by an element of the base, and to multiplying the element by a base
element: in both cases the differential field generated does not grow.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [CharZero L]

/-- **Rescaling the derivation of the extension by an element of the base preserves differential
algebraicity.** -/
theorem differentialAlgebraicOver_scaled (C₁ C₂ : Differential K) (D₁ D₂ : Differential L)
    (u : K)
    (hcompat₁ : ∀ y : K, D₁.deriv (algebraMap K L y) = algebraMap K L (C₁.deriv y))
    (hcompat₂ : ∀ y : K, D₂.deriv (algebraMap K L y) = algebraMap K L (C₂.deriv y))
    (hscale : ∀ f : L, D₁.deriv f = algebraMap K L u * D₂.deriv f)
    {x : L} (hx : @DifferentialAlgebraicOver K L _ _ _ D₂ x) :
    @DifferentialAlgebraicOver K L _ _ _ D₁ x := by
  haveI da₂ : @DifferentialAlgebra K L _ _ _ C₂ D₂ :=
    @DifferentialAlgebra.mk K L _ _ _ C₂ D₂ (fun y => hcompat₂ y)
  haveI da₁ : @DifferentialAlgebra K L _ _ _ C₁ D₁ :=
    @DifferentialAlgebra.mk K L _ _ _ C₁ D₁ (fun y => hcompat₁ y)
  set S : IntermediateField K L :=
    @differentialAdjoin K L _ _ _ D₂ ({x} : Set L) with hS
  have hxS : x ∈ S := @subset_differentialAdjoin K L _ _ _ D₂ _ x rfl
  have hclosed₂ : @DerivationClosed K L _ _ _ D₂ S :=
    @derivationClosed_differentialAdjoin K L _ _ C₂ D₂ _ da₂ _
  have hfin : Algebra.trdeg K S < Cardinal.aleph0 :=
    @differentialAdjoin_trdeg_lt_aleph0_of_differentialAlgebraic K L _ _ _ C₂ D₂ da₂ _ _ hx
  have hclosed₁ : @DerivationClosed K L _ _ _ D₁ S := by
    intro y hy
    show D₁.deriv y ∈ S
    rw [hscale]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) (hclosed₂ hy)
  exact @differentialAlgebraicOver_of_mem_derivationClosed_finiteTrdeg K L _ _ _ C₁ D₁ da₁
    inferInstance S hclosed₁ hfin x hxS

/-- **Multiplying by an element of the base preserves differential algebraicity.** -/
theorem differentialAlgebraicOver_base_mul (C : Differential K) (D : Differential L) (c : K)
    (hcompat : ∀ y : K, D.deriv (algebraMap K L y) = algebraMap K L (C.deriv y))
    {x : L} (hx : @DifferentialAlgebraicOver K L _ _ _ D x) :
    @DifferentialAlgebraicOver K L _ _ _ D (algebraMap K L c * x) := by
  haveI da : @DifferentialAlgebra K L _ _ _ C D :=
    @DifferentialAlgebra.mk K L _ _ _ C D (fun y => hcompat y)
  set S : IntermediateField K L :=
    @differentialAdjoin K L _ _ _ D ({x} : Set L) with hS
  have hxS : x ∈ S := @subset_differentialAdjoin K L _ _ _ D _ x rfl
  have hclosed : @DerivationClosed K L _ _ _ D S :=
    @derivationClosed_differentialAdjoin K L _ _ C D _ da _
  have hfin : Algebra.trdeg K S < Cardinal.aleph0 :=
    @differentialAdjoin_trdeg_lt_aleph0_of_differentialAlgebraic K L _ _ _ C D da _ _ hx
  exact @differentialAlgebraicOver_of_mem_derivationClosed_finiteTrdeg K L _ _ _ C D da
    inferInstance S hclosed hfin (algebraMap K L c * x)
    (mul_mem (IntermediateField.algebraMap_mem _ _) hxS)

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionInfinityCompletion
import GaloisForLFunctions.HTGeometry.ABHN.LocalValuationSequence
import GaloisForLFunctions.HTGeometry.MilnorKResidueValuation

/-!
# Valuation sequence at the infinity completion of a rational function field

The image of `t⁻¹` in the completion of `F(t)` at infinity is a uniformizer.  It therefore gives
residue data and the exact unit/valuation sequence for the canonical infinity local model.  This
completes the valuation layer for the finite and infinite places of `F(t)`; it does not construct
the local reciprocity map or the Brauer invariant.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped RatFunc ValuativeRel WithZero WithZeroMulInt

universe u

noncomputable section

section

variable (F : Type u) [Field F] [DecidableEq (RatFunc F)]

local instance rationalFunctionInfinityValuationSequenceLocalInst1 : Valued (RatFunc F) ℤᵐ⁰ := RatFunc.inftyValued F

/-- The image of `t⁻¹` in the completion of `F(t)` at infinity. -/
noncomputable def rationalFunctionCompletionAtInftyUniformizer :
    RatFunc.CompletionAtInfty F :=
  ((1 / RatFunc.X : RatFunc F) : RatFunc.CompletionAtInfty F)

/-- The infinity uniformizer has valuation `-1`. -/
theorem rationalFunctionCompletionAtInftyUniformizer_valuation :
    Valued.v (rationalFunctionCompletionAtInftyUniformizer F) =
      WithZero.exp (-1 : ℤ) := by
  unfold rationalFunctionCompletionAtInftyUniformizer
  rw [RatFunc.valuedCompletionAtInfty.def]
  change Valued.extensionValuation
      ((1 / RatFunc.X : RatFunc F) : UniformSpace.Completion (RatFunc F)) =
    WithZero.exp (-1 : ℤ)
  rw [Valued.extensionValuation_apply_coe]
  change RatFunc.inftyValuation F (1 / RatFunc.X) = WithZero.exp (-1 : ℤ)
  exact RatFunc.inftyValuation.X_inv F

/-- The infinity uniformizer is nonzero. -/
theorem rationalFunctionCompletionAtInftyUniformizer_ne_zero :
    rationalFunctionCompletionAtInftyUniformizer F ≠ 0 := by
  intro h
  have hval := rationalFunctionCompletionAtInftyUniformizer_valuation F
  rw [h, map_zero] at hval
  exact absurd hval.symm (by simp [WithZero.exp])

/-- The infinity uniformizer as a unit of the completed field. -/
noncomputable def rationalFunctionCompletionAtInftyUniformizerUnit :
    (RatFunc.CompletionAtInfty F)ˣ :=
  Units.mk0 (rationalFunctionCompletionAtInftyUniformizer F)
    (rationalFunctionCompletionAtInftyUniformizer_ne_zero F)

/-- The infinity uniformizer maps to `1` under the tame integer valuation. -/
theorem rationalFunctionCompletionAtInftyUniformizer_tameVal :
    Multiplicative.toAdd (tameValHom
      (Valued.v : Valuation (RatFunc.CompletionAtInfty F) ℤᵐ⁰)
      (rationalFunctionCompletionAtInftyUniformizerUnit F)) = 1 := by
  have hcoe : ((tameUnzero (Valued.v : Valuation
      (RatFunc.CompletionAtInfty F) ℤᵐ⁰)
      (rationalFunctionCompletionAtInftyUniformizerUnit F) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
    rw [coe_tameUnzero]
    exact rationalFunctionCompletionAtInftyUniformizer_valuation F
  have hun : tameUnzero (Valued.v : Valuation
      (RatFunc.CompletionAtInfty F) ℤᵐ⁰)
      (rationalFunctionCompletionAtInftyUniformizerUnit F) =
        Multiplicative.ofAdd (-1 : ℤ) :=
    WithZero.coe_inj.1 hcoe
  rw [tameValHom_toAdd, hun]
  simp

/-- Residue data for the canonical infinity completion of `F(t)`. -/
noncomputable def rationalFunctionCompletionAtInftyResidueData :
    ResidueData (RatFunc.CompletionAtInfty F)
      (IsLocalRing.ResidueField
        (Valued.v : Valuation (RatFunc.CompletionAtInfty F) ℤᵐ⁰).valuationSubring) :=
  residueDataOfValuation (Valued.v : Valuation
    (RatFunc.CompletionAtInfty F) ℤᵐ⁰)
    (rationalFunctionCompletionAtInftyUniformizerUnit F)
    (rationalFunctionCompletionAtInftyUniformizer_tameVal F)

/-- The infinity valuation on units is onto the integer value group. -/
theorem rationalFunctionCompletionAtInftyValuation_surjective :
    Function.Surjective (rationalFunctionCompletionAtInftyResidueData F).val :=
  residueDataValuation_surjective _

/-- Units of valuation zero are exactly the kernel of the infinity valuation. -/
theorem rationalFunctionCompletionAtInftyValuation_exact : Function.Exact
    (MonoidHom.toAdditive
      (rationalFunctionCompletionAtInftyResidueData F).val.ker.subtype)
    (MonoidHom.toAdditive (rationalFunctionCompletionAtInftyResidueData F).val) :=
  residueDataValuation_exact _

/-- The unit quotient at infinity is the integer value group. -/
noncomputable def rationalFunctionCompletionAtInftyQuotientKerValuationEquiv :
    (RatFunc.CompletionAtInfty F)ˣ ⧸
      (rationalFunctionCompletionAtInftyResidueData F).val.ker ≃*
        Multiplicative ℤ :=
  residueDataQuotientKerValuationEquiv _

end

end

end GaloisForLFunctions.HTGeometry.ABHN

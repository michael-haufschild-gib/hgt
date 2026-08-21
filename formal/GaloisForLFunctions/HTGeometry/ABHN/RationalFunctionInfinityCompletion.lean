import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionInfinityUniform
import GaloisForLFunctions.HTGeometry.ABHN.LaurentSeriesFiniteLocalField

/-!
# The infinity completion of a rational function field

After the coordinate change `t ↦ t⁻¹`, the completion of `F(t)` at infinity is uniformly
equivalent to the Laurent-series field `F((X))`.  Thus the local-field infrastructure already
proved for Laurent series applies to the infinite place of a rational-function global field.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped RatFunc WithZero

universe u

noncomputable section

section

variable (F : Type u) [Field F] [DecidableEq (RatFunc F)]

local instance : Valued (RatFunc F) ℤᵐ⁰ := RatFunc.inftyValued F

/-- The completion of `F(t)` at infinity is uniformly equivalent to `F((X))`, where the
Laurent-series coordinate `X` represents `t⁻¹`. -/
def rationalFunctionCompletionAtInfty_uniformEquiv_laurentSeries :
    RatFunc.CompletionAtInfty F ≃ᵤ LaurentSeries F :=
  (UniformSpace.Completion.mapEquiv
    ((WithVal.uniformEquiv (v := RatFunc.inftyValuation F)
      (w := RatFunc.inftyValuation F) rfl Valuation.IsEquiv.refl).symm.trans
      (rationalFunctionInftyValuation_uniformEquiv_polynomialValuationX F))).trans
    ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformEquiv (RatFunc F)
      (Polynomial.idealX F)).symm.trans (LaurentSeries.comparePkg F))

/-- The valuation on the infinity completion defines its valuative relation. -/
noncomputable instance rationalFunctionCompletionAtInftyValuativeRel :
    ValuativeRel (RatFunc.CompletionAtInfty F) :=
  .ofValuation (Valued.v : Valuation (RatFunc.CompletionAtInfty F) ℤᵐ⁰)

/-- The extended infinity valuation on the completion remains nontrivial. -/
noncomputable instance rationalFunctionCompletionAtInftyValuationIsNontrivial :
    (Valued.v : Valuation (RatFunc.CompletionAtInfty F) ℤᵐ⁰).IsNontrivial := by
  refine ⟨((RatFunc.X : RatFunc F) : RatFunc.CompletionAtInfty F), ?_⟩
  rw [RatFunc.valuedCompletionAtInfty.def]
  constructor
  · change Valued.extensionValuation
      ((RatFunc.X : RatFunc F) : UniformSpace.Completion (RatFunc F)) ≠ 0
    rw [Valued.extensionValuation_apply_coe]
    change RatFunc.inftyValuation F RatFunc.X ≠ 0
    simp
  · change Valued.extensionValuation
      ((RatFunc.X : RatFunc F) : UniformSpace.Completion (RatFunc F)) ≠ 1
    rw [Valued.extensionValuation_apply_coe]
    change RatFunc.inftyValuation F RatFunc.X ≠ 1
    simp

/-- For finite `F`, the infinity completion of `F(t)` is a nonarchimedean local field. -/
noncomputable instance rationalFunctionCompletionAtInftyIsNonarchimedeanLocalField
    [Finite F] :
    IsNonarchimedeanLocalField (RatFunc.CompletionAtInfty F) := by
  letI : LocallyCompactSpace (RatFunc.CompletionAtInfty F) :=
    (Homeomorph.locallyCompactSpace_iff
      (rationalFunctionCompletionAtInfty_uniformEquiv_laurentSeries F).toHomeomorph).mpr
        inferInstance
  exact isNonarchimedeanLocalField_of_valued_of_locallyCompact
    (RatFunc.CompletionAtInfty F) ℤᵐ⁰

end

end

end GaloisForLFunctions.HTGeometry.ABHN

import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionInfinityUniform
import GaloisForLFunctions.HTGeometry.ABHN.LaurentSeriesFiniteLocalField
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionPlaces

/-!
# The infinity completion of a rational function field

After the coordinate change `t ↦ t⁻¹`, the completion of `F(t)` at infinity is uniformly
equivalent to the Laurent-series field `F((X))`.  Thus the local-field infrastructure already
proved for Laurent series applies to the infinite place of a rational-function global field.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped RatFunc ValuativeRel WithZero WithZeroMulInt

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

/-! ## Packaged infinite-place local-field structure -/

/-- The packaged infinite completion of `F(t)` retains its completion topology. -/
noncomputable instance rationalFunctionInfinitePlaceCompletionTopologicalSpace
    (F : Type u) [Field F] [Finite F] :
    TopologicalSpace (rationalFunctionCompletion F .infinite) := by
  classical
  change TopologicalSpace (RatFunc.CompletionAtInfty F)
  infer_instance

/-- The packaged infinite completion of `F(t)` retains its completion uniform structure. -/
noncomputable instance rationalFunctionInfinitePlaceCompletionUniformSpace
    (F : Type u) [Field F] [Finite F] :
    UniformSpace (rationalFunctionCompletion F .infinite) := by
  classical
  change UniformSpace (RatFunc.CompletionAtInfty F)
  infer_instance

/-- Addition on the packaged infinite completion is uniformly continuous. -/
noncomputable instance rationalFunctionInfinitePlaceCompletionIsUniformAddGroup
    (F : Type u) [Field F] [Finite F] :
    IsUniformAddGroup (rationalFunctionCompletion F .infinite) := by
  classical
  change IsUniformAddGroup (RatFunc.CompletionAtInfty F)
  infer_instance

/-- Addition on the packaged infinite completion is continuous. -/
noncomputable instance rationalFunctionInfinitePlaceCompletionIsTopologicalAddGroup
    (F : Type u) [Field F] [Finite F] :
    IsTopologicalAddGroup (rationalFunctionCompletion F .infinite) := by
  classical
  change IsTopologicalAddGroup (RatFunc.CompletionAtInfty F)
  infer_instance

/-- The packaged infinite completion of `F(t)` is locally compact. -/
noncomputable instance rationalFunctionInfinitePlaceCompletionLocallyCompactSpace
    (F : Type u) [Field F] [Finite F] :
    LocallyCompactSpace (rationalFunctionCompletion F .infinite) := by
  classical
  change LocallyCompactSpace (RatFunc.CompletionAtInfty F)
  infer_instance

/-- The packaged infinite completion retains its infinity-valuative relation. -/
noncomputable instance rationalFunctionInfinitePlaceCompletionValuativeRel
    (F : Type u) [Field F] [Finite F] :
    ValuativeRel (rationalFunctionCompletion F .infinite) := by
  classical
  change ValuativeRel (RatFunc.CompletionAtInfty F)
  infer_instance

/-- The infinite completion of a finite rational-function field is a nonarchimedean local field. -/
noncomputable instance rationalFunctionInfinitePlaceCompletionIsNonarchimedeanLocalField
    (F : Type u) [Field F] [Finite F] :
    IsNonarchimedeanLocalField (rationalFunctionCompletion F .infinite) := by
  classical
  change IsNonarchimedeanLocalField (RatFunc.CompletionAtInfty F)
  infer_instance

/-- The integer ring at infinity is a discrete valuation ring. -/
noncomputable instance rationalFunctionInfinitePlaceCompletionIsDiscreteValuationRing
    (F : Type u) [Field F] [Finite F] :
    IsDiscreteValuationRing 𝒪[rationalFunctionCompletion F .infinite] := by
  classical
  change IsDiscreteValuationRing 𝒪[RatFunc.CompletionAtInfty F]
  infer_instance

/-- The residue field at infinity is finite. -/
noncomputable instance rationalFunctionInfinitePlaceCompletionFiniteResidueField
    (F : Type u) [Field F] [Finite F] :
    Finite 𝓀[rationalFunctionCompletion F .infinite] := by
  classical
  change Finite 𝓀[RatFunc.CompletionAtInfty F]
  infer_instance

/-- The infinite valuation ring is complete for its maximal-ideal adic topology. -/
theorem rationalFunctionInfinitePlaceCompletion_isAdicComplete
    (F : Type u) [Field F] [Finite F] :
    IsAdicComplete 𝓂[rationalFunctionCompletion F .infinite]
      𝒪[rationalFunctionCompletion F .infinite] := by
  classical
  change IsAdicComplete 𝓂[RatFunc.CompletionAtInfty F]
    𝒪[RatFunc.CompletionAtInfty F]
  infer_instance

/-- The infinite valuation ring is henselian. -/
theorem rationalFunctionInfinitePlaceCompletion_henselianRing
    (F : Type u) [Field F] [Finite F] :
    HenselianRing 𝒪[rationalFunctionCompletion F .infinite]
      𝓂[rationalFunctionCompletion F .infinite] := by
  classical
  change HenselianRing 𝒪[RatFunc.CompletionAtInfty F]
    𝓂[RatFunc.CompletionAtInfty F]
  infer_instance

/-- Hensel lifting holds at the packaged infinite completion of `F(t)`. -/
theorem rationalFunctionInfinitePlaceCompletion_henselianLocalRing
    (F : Type u) [Field F] [Finite F] :
    HenselianLocalRing 𝒪[rationalFunctionCompletion F .infinite] := by
  letI : HenselianRing 𝒪[rationalFunctionCompletion F .infinite]
      𝓂[rationalFunctionCompletion F .infinite] :=
    rationalFunctionInfinitePlaceCompletion_henselianRing F
  refine { toIsLocalRing := inferInstance, is_henselian := ?_ }
  intro f hf a₀ ha₀ hderivative
  exact HenselianRing.is_henselian f hf a₀ ha₀ (hderivative.map (Ideal.Quotient.mk _))

end

end GaloisForLFunctions.HTGeometry.ABHN

import GaloisForLFunctions.HTGeometry.FiniteUnitaryHaarMeasureLaw

/-!
# Normalized Haar measure is carried by a reindexing of the coordinates

An equivalence of finite index types induces a continuous group isomorphism of the two finite
unitary groups.  A continuous group isomorphism of compact groups carries normalized Haar measure
to normalized Haar measure, because the pushforward is again a left-invariant probability measure
and Haar measure is unique.  Consequently every Haar integral computed on one index type transfers
verbatim to any index type of the same cardinality.

mathlib has Haar invariance under group translations but nothing that moves Haar measure across a
change of index type of the matrix group.
-/

open MeasureTheory MeasureTheory.Measure TopologicalSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {κ κ' : Type*} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

/-- Reindexing a unitary matrix along an equivalence of index types. -/
def unitaryGroupReindex (e : κ ≃ κ') :
    Matrix.unitaryGroup κ ℂ →* Matrix.unitaryGroup κ' ℂ where
  toFun U := ⟨Matrix.reindexAlgEquiv ℂ ℂ e (U : Matrix κ κ ℂ), by
    rw [Matrix.mem_unitaryGroup_iff]
    have hstar : star (Matrix.reindexAlgEquiv ℂ ℂ e (U : Matrix κ κ ℂ))
        = Matrix.reindexAlgEquiv ℂ ℂ e (star (U : Matrix κ κ ℂ)) := rfl
    rw [hstar, ← map_mul, Matrix.mem_unitaryGroup_iff.mp U.2, map_one]⟩
  map_one' := Subtype.ext (by simpa using map_one (Matrix.reindexAlgEquiv ℂ ℂ e))
  map_mul' U V := Subtype.ext (by simpa using map_mul (Matrix.reindexAlgEquiv ℂ ℂ e)
    (U : Matrix κ κ ℂ) (V : Matrix κ κ ℂ))

theorem unitaryGroupReindex_coe (e : κ ≃ κ') (U : Matrix.unitaryGroup κ ℂ) (i j : κ') :
    ((unitaryGroupReindex e U : Matrix.unitaryGroup κ' ℂ) : Matrix κ' κ' ℂ) i j
      = (U : Matrix κ κ ℂ) (e.symm i) (e.symm j) := rfl

theorem continuous_unitaryGroupReindex (e : κ ≃ κ') :
    Continuous (unitaryGroupReindex e) := by
  refine continuous_induced_rng.2 ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact continuous_finiteUnitaryEntry (e.symm i) (e.symm j)

theorem unitaryGroupReindex_symm_apply (e : κ ≃ κ') (U : Matrix.unitaryGroup κ ℂ) :
    unitaryGroupReindex e.symm (unitaryGroupReindex e U) = U := by
  apply Subtype.ext
  ext i j
  rfl

theorem unitaryGroupReindex_apply_symm (e : κ ≃ κ') (V : Matrix.unitaryGroup κ' ℂ) :
    unitaryGroupReindex e (unitaryGroupReindex e.symm V) = V := by
  apply Subtype.ext
  ext i j
  rfl

theorem surjective_unitaryGroupReindex (e : κ ≃ κ') :
    Function.Surjective (unitaryGroupReindex e) :=
  fun V => ⟨unitaryGroupReindex e.symm V, unitaryGroupReindex_apply_symm e V⟩

/-- **Normalized Haar measure transfers along a reindexing.** -/
theorem measurePreserving_unitaryGroupReindex (e : κ ≃ κ') :
    MeasurePreserving (unitaryGroupReindex e) (finiteUnitaryHaar κ) (finiteUnitaryHaar κ') := by
  have hcont : Continuous (unitaryGroupReindex e) := continuous_unitaryGroupReindex e
  have hmeas : Measurable (unitaryGroupReindex e) := hcont.measurable
  refine ⟨hmeas, ?_⟩
  haveI : IsHaarMeasure (Measure.map (unitaryGroupReindex e) (finiteUnitaryHaar κ)) := by
    refine Measure.isHaarMeasure_map (finiteUnitaryHaar κ) (unitaryGroupReindex e) hcont
      (surjective_unitaryGroupReindex e) ?_
    simp [Filter.cocompact_eq_bot]
  haveI : IsProbabilityMeasure (Measure.map (unitaryGroupReindex e) (finiteUnitaryHaar κ)) :=
    isProbabilityMeasure_map hmeas.aemeasurable
  have huniq := Measure.haarMeasure_unique
    (Measure.map (unitaryGroupReindex e) (finiteUnitaryHaar κ))
    (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts (Matrix.unitaryGroup κ' ℂ))
  rw [measure_univ, one_smul] at huniq
  exact huniq

/-- Every Haar integral is computed on any index type of the same cardinality. -/
theorem integral_finiteUnitaryHaar_reindex (e : κ ≃ κ')
    (f : Matrix.unitaryGroup κ' ℂ → ℝ) (hf : Continuous f) :
    (∫ U, f (unitaryGroupReindex e U) ∂finiteUnitaryHaar κ)
      = ∫ V, f V ∂finiteUnitaryHaar κ' := by
  have hmp := measurePreserving_unitaryGroupReindex e
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hf.aestronglyMeasurable]

end

end GaloisForLFunctions.HTGeometry

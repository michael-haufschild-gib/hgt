import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionReduction
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.LocalUnitFiltration

/-! The valuation-zero units of a finite completion reduce onto the
residue multiplicative group. The kernel is the first principal layer. -/

noncomputable section

open NumberField IsDedekindDomain WithZero

namespace GlobalTheory.Reciprocity

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

def unitsLevelZeroEquivIntegerUnits : unitsLevel (K := K) v 0 ≃* (CompletedIntegers v)ˣ :=
  (MulEquiv.subgroupCongr (unitsLevel_zero (K := K) v)).trans
    (Submonoid.ofClass (v.adicCompletionIntegers K)).unitsEquivUnitsType

@[simp] theorem unitsLevelZeroEquivIntegerUnits_val (x : unitsLevel (K := K) v 0) :
    (((unitsLevelZeroEquivIntegerUnits v x : (CompletedIntegers v)ˣ) :
      CompletedIntegers v) : v.adicCompletion K) = (x.val : v.adicCompletion K) := rfl

def finiteCompletionUnitReduction : unitsLevel (K := K) v 0 →* (𝓞 K ⧸ v.asIdeal)ˣ :=
  (Units.map (completionReduction v).toMonoidHom).comp
    (unitsLevelZeroEquivIntegerUnits v).toMonoidHom

theorem finiteCompletionUnitReduction_surjective :
    Function.Surjective (finiteCompletionUnitReduction v) := by
  intro y
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective y.val
  let x := toCompletedIntegers v r
  have hx : completionReduction v x = y.val := (completionReduction_toCompletedIntegers v r).trans hr
  have hunit : IsUnit x := by
    by_contra h
    have hv : Valued.v (x.val : v.adicCompletion K) < 1 :=
      Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp h
    have he := (completionReduction_eq_iff v x 0).mpr (by simpa only [ZeroMemClass.coe_zero, sub_zero] using hv)
    rw [hx, map_zero] at he
    letI := v.isMaximal
    letI := Ideal.Quotient.field v.asIdeal
    exact Units.ne_zero y he
  refine ⟨(unitsLevelZeroEquivIntegerUnits v).symm hunit.unit, Units.ext ?_⟩
  change completionReduction v
    ((unitsLevelZeroEquivIntegerUnits v) ((unitsLevelZeroEquivIntegerUnits v).symm hunit.unit)).val = y.val
  rw [MulEquiv.apply_symm_apply, hunit.unit_spec]
  exact hx

theorem finiteCompletionUnitReduction_eq_one_iff (x : unitsLevel (K := K) v 0) :
    finiteCompletionUnitReduction v x = 1 ↔ Valued.v ((x.val : v.adicCompletion K) - 1) < 1 := by
  rw [Units.ext_iff, Units.val_one]
  change completionReduction v (unitsLevelZeroEquivIntegerUnits v x).val = 1 ↔ _
  rw [← map_one (completionReduction v), completionReduction_eq_iff]
  rfl

theorem mem_unitsLevel_one_iff_lt_one (x : (v.adicCompletion K)ˣ) :
    x ∈ unitsLevel (K := K) v 1 ↔ Valued.v ((x : v.adicCompletion K) - 1) < 1 := by
  rw [mem_unitsLevel_of_one_le (le_rfl : (1 : ℕ) ≤ 1)]
  change _ ≤ exp (-1 : ℤ) ↔ _
  let a := Valued.v ((x : v.adicCompletion K) - 1)
  change a ≤ exp (-1 : ℤ) ↔ a < 1
  rcases eq_or_ne a 0 with h | h
  · rw [h]
    simp
  · rw [← exp_log h, ← exp_zero, exp_lt_exp, exp_le_exp]
    omega

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.finiteCompletionUnitReduction_surjective
#print axioms GlobalTheory.Reciprocity.finiteCompletionUnitReduction_eq_one_iff

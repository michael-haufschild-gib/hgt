import GaloisForLFunctions.HTGeometry.LoopEisenstein.LaurentFieldMap
import Mathlib.Data.Real.Basic

/-!
# Faithful coefficient-field maps of central loop groups

The naturality of the actual Laurent tame symbol lifts every coefficient-field
inclusion to an injective homomorphism of central loop groups. In particular,
the rational central loop group embeds in the real one, with the expected maps
on the center and on both root subgroups.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable {F E : Type*} [Field F] [Field E]

/-- Entrywise coefficient-field inclusion on Laurent special-linear matrices. -/
def sl2FieldMap (ι : F →+* E) : SL2 (LaurentSeries F) →* SL2 (LaurentSeries E) :=
  Matrix.SpecialLinearGroup.map (laurentFieldMap ι)

@[simp] theorem sl2FieldMap_apply (ι : F →+* E) (g : SL2 (LaurentSeries F)) (i j : Fin 2) :
    sl2FieldMap ι g i j = laurentFieldMap ι (g i j) := rfl

theorem sl2FieldMap_injective (ι : F →+* E) : Function.Injective (sl2FieldMap ι) := by
  intro g h he
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  exact laurentFieldMap_injective ι (congrArg (fun k : SL2 (LaurentSeries E) => k i j) he)

theorem coefficientUnitMap_injective (ι : F →+* E) :
    Function.Injective (Units.map ι.toMonoidHom) := by
  intro a b h
  apply Units.ext
  exact ι.injective (congrArg (fun u : Eˣ => (u : E)) h)

/-- The coefficient-field inclusion on the additive presentation of the center. -/
def centralFieldMap (ι : F →+* E) : Additive Fˣ →+ Additive Eˣ :=
  MonoidHom.toAdditive (Units.map ι.toMonoidHom)

theorem centralFieldMap_injective (ι : F →+* E) : Function.Injective (centralFieldMap ι) := by
  intro a b h
  have hu : Units.map ι.toMonoidHom a.toMul = Units.map ι.toMonoidHom b.toMul :=
    congrArg Additive.toMul h
  exact congrArg Additive.ofMul (coefficientUnitMap_injective ι hu)

theorem kubotaUnit_fieldMap (ι : F →+* E) (g : SL2 (LaurentSeries F)) :
    kubotaUnit (sl2FieldMap ι g) = laurentUnitFieldMap ι (kubotaUnit g) := by
  apply Units.ext
  rw [coe_kubotaUnit, coe_laurentUnitFieldMap, coe_kubotaUnit]
  classical
  by_cases hg : g 1 0 = 0
  · have hmg : sl2FieldMap ι g 1 0 = 0 := by rw [sl2FieldMap_apply, hg, map_zero]
    simp only [kubotaX, hg, hmg, if_true, sl2FieldMap_apply]
  · have hmg : laurentFieldMap ι (g 1 0) ≠ 0 := by
      intro hz
      apply hg
      exact laurentFieldMap_injective ι (hz.trans (map_zero _).symm)
    simp only [kubotaX, sl2FieldMap_apply, hg, hmg, if_false]

/-- The concrete tame image of the Kubota cocycle commutes with coefficient inclusion. -/
theorem tame_kubotaCocycle_fieldMap (ι : F →+* E) (g h : SL2 (LaurentSeries F)) :
    laurentTameHom E (kubotaCocycle (sl2FieldMap ι g) (sl2FieldMap ι h)) =
      centralFieldMap ι (laurentTameHom F (kubotaCocycle g h)) := by
  simp only [kubotaCocycle, laurentTameHom_symbol]
  rw [← (sl2FieldMap ι).map_mul g h, kubotaUnit_fieldMap, kubotaUnit_fieldMap,
    kubotaUnit_fieldMap, ← map_div, ← map_div, laurentTameSymbol_fieldMap]
  rfl

namespace LoopSL2

/-- The coefficient-field map of the actual central loop groups. -/
def fieldMap (ι : F →+* E) : LoopSL2 F →* LoopSL2 E where
  toFun g := ⟨sl2FieldMap ι g.base, centralFieldMap ι g.centralCoord⟩
  map_one' := by
    apply SL2SymbolExtension.ext
    · exact map_one (sl2FieldMap ι)
    · exact map_zero (centralFieldMap ι)
  map_mul' g h := by
    apply SL2SymbolExtension.ext
    · exact map_mul (sl2FieldMap ι) g.base h.base
    · change centralFieldMap ι
        (g.centralCoord + h.centralCoord + laurentTameHom F (kubotaCocycle g.base h.base)) =
      centralFieldMap ι g.centralCoord + centralFieldMap ι h.centralCoord +
        laurentTameHom E (kubotaCocycle (sl2FieldMap ι g.base) (sl2FieldMap ι h.base))
      rw [map_add, map_add, tame_kubotaCocycle_fieldMap]

theorem fieldMap_injective (ι : F →+* E) : Function.Injective (fieldMap ι) := by
  intro g h he
  apply SL2SymbolExtension.ext
  · exact sl2FieldMap_injective ι (congrArg SL2SymbolExtension.base he)
  · exact centralFieldMap_injective ι (congrArg SL2SymbolExtension.centralCoord he)

@[simp] theorem fieldMap_centralEmbedding (ι : F →+* E) (a : Fˣ) :
    fieldMap ι (centralEmbedding F a) = centralEmbedding E (Units.map ι.toMonoidHom a) := by
  apply SL2SymbolExtension.ext
  · exact map_one (sl2FieldMap ι)
  · rfl

theorem fieldMap_upperRoot (ι : F →+* E) (s : LaurentSeries F) :
    fieldMap ι (upperRoot F (Multiplicative.ofAdd s)) =
      upperRoot E (Multiplicative.ofAdd (laurentFieldMap ι s)) := by
  apply SL2SymbolExtension.ext
  · change sl2FieldMap ι (sl2Upper s) = sl2Upper (laurentFieldMap ι s)
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [sl2FieldMap_apply, sl2Upper]
  · exact map_zero (centralFieldMap ι)

theorem fieldMap_lowerRoot (ι : F →+* E) (s : LaurentSeries F) :
    fieldMap ι (lowerRoot F (Multiplicative.ofAdd s)) =
      lowerRoot E (Multiplicative.ofAdd (laurentFieldMap ι s)) := by
  apply SL2SymbolExtension.ext
  · change sl2FieldMap ι (sl2Lower s) = sl2Lower (laurentFieldMap ι s)
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [sl2FieldMap_apply, sl2Lower]
  · exact map_zero (centralFieldMap ι)

/-- The rational central loop group as an actual subgroup of the real group. -/
def rationalEmbedding : LoopSL2 ℚ →* LoopSL2 ℝ := fieldMap (algebraMap ℚ ℝ)

theorem rationalEmbedding_injective : Function.Injective rationalEmbedding :=
  fieldMap_injective (algebraMap ℚ ℝ)

/-- The embedded rational points of the real central loop group. -/
def rationalSubgroup : Subgroup (LoopSL2 ℝ) := rationalEmbedding.range

end LoopSL2

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein

import GaloisForLFunctions.HTGeometry.LoopEisenstein.LaurentRotation
import GaloisForLFunctions.HTGeometry.HahnDilation

/-!
# Coefficient-field maps preserve the Laurent tame symbol

A field inclusion acts coefficientwise on Laurent series. It preserves the
integer valuation, and the tame symbol commutes with it because residue is the
constant coefficient. This supplies the coefficient-field map of the central
loop group, in particular its rational-to-real embedding.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable {F E : Type*} [Field F] [Field E]

/-- Apply a coefficient-field map to every Laurent coefficient. -/
def laurentFieldMap (ι : F →+* E) : LaurentSeries F →+* LaurentSeries E :=
  hahnMapRingHom ι

@[simp] theorem laurentFieldMap_coeff (ι : F →+* E) (f : LaurentSeries F) (n : ℤ) :
    (laurentFieldMap ι f).coeff n = ι (f.coeff n) := coeff_hahnMapRingHom ι f n

theorem laurentFieldMap_injective (ι : F →+* E) : Function.Injective (laurentFieldMap ι) :=
  (laurentFieldMap ι).injective

/-- A coefficient-field inclusion preserves the canonical Laurent valuation. -/
theorem laurentFieldMap_valuation (ι : F →+* E) (f : LaurentSeries F) :
    laurentValuation E (laurentFieldMap ι f) = laurentValuation F f := by
  by_cases hf : f = 0
  · rw [hf, map_zero, map_zero, map_zero]
  have hmf : laurentFieldMap ι f ≠ 0 := by
    intro h
    exact hf ((laurentFieldMap ι).injective (h.trans (map_zero _).symm))
  have hvf := (Valuation.ne_zero_iff (laurentValuation F)).2 hf
  have hvm := (Valuation.ne_zero_iff (laurentValuation E)).2 hmf
  apply le_antisymm
  · apply (LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero E hvf).2
    intro n hn
    rw [laurentFieldMap_coeff,
      (LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero F hvf).1 le_rfl n hn, map_zero]
  · apply (LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero F hvm).2
    intro n hn
    have hz := (LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero E hvm).1 le_rfl n hn
    rw [laurentFieldMap_coeff] at hz
    exact ι.injective (hz.trans (map_zero ι).symm)

/-- The induced map on invertible Laurent series. -/
def laurentUnitFieldMap (ι : F →+* E) : (LaurentSeries F)ˣ →* (LaurentSeries E)ˣ :=
  Units.map (laurentFieldMap ι).toMonoidHom

@[simp] theorem coe_laurentUnitFieldMap (ι : F →+* E) (a : (LaurentSeries F)ˣ) :
    (laurentUnitFieldMap ι a : LaurentSeries E) = laurentFieldMap ι (a : LaurentSeries F) := rfl

theorem laurentUnitFieldMap_tameVal (ι : F →+* E) (a : (LaurentSeries F)ˣ) :
    (tameDataOfValuation (laurentValuation E)).v (laurentUnitFieldMap ι a) =
      (tameDataOfValuation (laurentValuation F)).v a := by
  have hu : tameUnzero (laurentValuation E) (laurentUnitFieldMap ι a) =
      tameUnzero (laurentValuation F) a := by
    apply WithZero.coe_inj.mp
    rw [coe_tameUnzero, coe_tameUnzero, coe_laurentUnitFieldMap, laurentFieldMap_valuation]
  change Multiplicative.toAdd (tameValHom (laurentValuation E) (laurentUnitFieldMap ι a)) =
    Multiplicative.toAdd (tameValHom (laurentValuation F) a)
  rw [tameValHom_toAdd, tameValHom_toAdd, hu]

@[simp] theorem laurentUnitFieldMap_neg_one (ι : F →+* E) :
    laurentUnitFieldMap ι (-1) = -1 := by
  apply Units.ext
  change laurentFieldMap ι (-1) = -1
  rw [map_neg, map_one]

private theorem symbolUnit_fieldMap (ι : F →+* E) (a b : (LaurentSeries F)ˣ) :
    (tameDataOfValuation (laurentValuation E)).symbolUnit
        (laurentUnitFieldMap ι a) (laurentUnitFieldMap ι b) =
      laurentUnitFieldMap ι ((tameDataOfValuation (laurentValuation F)).symbolUnit a b) := by
  simp only [TameData.symbolUnit, laurentUnitFieldMap_tameVal, map_mul, map_zpow,
    laurentUnitFieldMap_neg_one]

/-- The actual Laurent tame symbol is natural under coefficient-field inclusions. -/
theorem laurentTameSymbol_fieldMap (ι : F →+* E) (a b : (LaurentSeries F)ˣ) :
    laurentTameSymbol E (laurentUnitFieldMap ι a) (laurentUnitFieldMap ι b) =
      Units.map ι.toMonoidHom (laurentTameSymbol F a b) := by
  apply Units.ext
  change (laurentTameSymbol E (laurentUnitFieldMap ι a) (laurentUnitFieldMap ι b) : E) =
    ι (laurentTameSymbol F a b : F)
  rw [laurentTameSymbol_coe_eq_coeff_zero, laurentTameSymbol_coe_eq_coeff_zero,
    symbolUnit_fieldMap, coe_laurentUnitFieldMap, laurentFieldMap_coeff]

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein

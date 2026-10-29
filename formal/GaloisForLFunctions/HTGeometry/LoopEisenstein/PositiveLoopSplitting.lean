import GaloisForLFunctions.HTGeometry.LoopEisenstein.PowerSeriesKubota

/-!
# Splitting the central extension on positive loops

The tame correction of the bottom row defines the positive-loop lift. Its
compatibility with elementary roots supplies the multiplicative splitting of
the full power-series matrix group.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable (F : Type*) [Field F]

namespace LoopSL2

/-- The explicit section over positive loops, corrected by the bottom-row tame symbol. -/
def positiveSection (g : PowerSeriesSL2 F) : LoopSL2 F :=
  ⟨powerSeriesSL2Map F g, Additive.ofMul (powerSeriesRowCorrection F (g 1 0) (g 1 1))⟩

@[simp] theorem projection_positiveSection (g : PowerSeriesSL2 F) :
    projection F (positiveSection F g) = powerSeriesSL2Map F g := rfl

theorem positiveSection_injective : Function.Injective (positiveSection F) := by
  intro g h he
  exact powerSeriesSL2Map_injective F (congrArg (projection F) he)

@[simp] theorem positiveSection_one : positiveSection F 1 = 1 := by
  apply SL2SymbolExtension.ext
  · exact map_one _
  · change Additive.ofMul (powerSeriesRowCorrection F 0 1) = 0
    rw [powerSeriesRowCorrection_zero]
    rfl

@[simp] theorem positiveSection_upper (s : PowerSeries F) :
    positiveSection F (FiniteRingSl2.upper s) =
      upperRoot F (Multiplicative.ofAdd (s : LaurentSeries F)) := by
  apply SL2SymbolExtension.ext
  · exact powerSeriesSL2Map_upper F s
  · change Additive.ofMul (powerSeriesRowCorrection F 0 1) = 0
    rw [powerSeriesRowCorrection_zero]
    rfl

@[simp] theorem positiveSection_lower (s : PowerSeries F) :
    positiveSection F (FiniteRingSl2.lower s) =
      lowerRoot F (Multiplicative.ofAdd (s : LaurentSeries F)) := by
  apply SL2SymbolExtension.ext
  · exact powerSeriesSL2Map_lower F s
  · change Additive.ofMul (powerSeriesRowCorrection F s 1) = 0
    rw [powerSeriesRowCorrection_one_right]
    rfl

@[simp] theorem positiveSection_mul_upper (g : PowerSeriesSL2 F) (s : PowerSeries F) :
    positiveSection F (g * FiniteRingSl2.upper s) =
      positiveSection F g * upperRoot F (Multiplicative.ofAdd (s : LaurentSeries F)) := by
  apply SL2SymbolExtension.ext
  · change powerSeriesSL2Map F (g * FiniteRingSl2.upper s) =
      powerSeriesSL2Map F g * sl2Upper (s : LaurentSeries F)
    rw [map_mul, powerSeriesSL2Map_upper]
  · change Additive.ofMul (powerSeriesRowCorrection F
        ((g * FiniteRingSl2.upper s) 1 0) ((g * FiniteRingSl2.upper s) 1 1)) =
      Additive.ofMul (powerSeriesRowCorrection F (g 1 0) (g 1 1)) + 0 +
        laurentTameHom F (kubotaCocycle (powerSeriesSL2Map F g) (sl2Upper (s : LaurentSeries F)))
    rw [powerSeriesSL2_mul_upper_c, powerSeriesSL2_mul_upper_d,
      powerSeriesRowCorrection_upper F _ _ _ (powerSeriesSL2_bottom_constants F g),
      kubotaCocycle_mul_upper, map_zero, add_zero, add_zero]

@[simp] theorem positiveSection_mul_lower (g : PowerSeriesSL2 F) (s : PowerSeries F) :
    positiveSection F (g * FiniteRingSl2.lower s) =
      positiveSection F g * lowerRoot F (Multiplicative.ofAdd (s : LaurentSeries F)) := by
  apply SL2SymbolExtension.ext
  · change powerSeriesSL2Map F (g * FiniteRingSl2.lower s) =
      powerSeriesSL2Map F g * sl2Lower (s : LaurentSeries F)
    rw [map_mul, powerSeriesSL2Map_lower]
  · change Additive.ofMul (powerSeriesRowCorrection F
        ((g * FiniteRingSl2.lower s) 1 0) ((g * FiniteRingSl2.lower s) 1 1)) =
      Additive.ofMul (powerSeriesRowCorrection F (g 1 0) (g 1 1)) + 0 +
        laurentTameHom F (kubotaCocycle (powerSeriesSL2Map F g) (sl2Lower (s : LaurentSeries F)))
    rw [← powerSeriesSL2Map_lower, ← powerSeriesKubotaFactor_eq,
      powerSeriesSL2_mul_lower_c, powerSeriesSL2_mul_lower_d,
      powerSeriesRowCorrection_lower, add_zero]
    rfl

/-- Elementary generation upgrades the two root identities to the full group law. -/
theorem positiveSection_mul (g h : PowerSeriesSL2 F) :
    positiveSection F (g * h) = positiveSection F g * positiveSection F h := by
  obtain ⟨x, y, z, w, rfl⟩ := powerSeriesSL2_four_factors F h
  simp only [← mul_assoc, positiveSection_mul_lower, positiveSection_mul_upper,
    positiveSection_upper]

/-- The actual multiplicative splitting over the full positive power-series group. -/
def positiveEmbedding : PowerSeriesSL2 F →* LoopSL2 F where
  toFun := positiveSection F
  map_one' := positiveSection_one F
  map_mul' := positiveSection_mul F

@[simp] theorem projection_positiveEmbedding (g : PowerSeriesSL2 F) :
    projection F (positiveEmbedding F g) = powerSeriesSL2Map F g := rfl

theorem positiveEmbedding_injective : Function.Injective (positiveEmbedding F) :=
  positiveSection_injective F

@[simp] theorem positiveEmbedding_upper (s : PowerSeries F) :
    positiveEmbedding F (FiniteRingSl2.upper s) =
      upperRoot F (Multiplicative.ofAdd (s : LaurentSeries F)) :=
  positiveSection_upper F s

@[simp] theorem positiveEmbedding_lower (s : PowerSeries F) :
    positiveEmbedding F (FiniteRingSl2.lower s) =
      lowerRoot F (Multiplicative.ofAdd (s : LaurentSeries F)) :=
  positiveSection_lower F s

/-- The positive power-series subgroup inside the central extension. -/
def positiveSubgroup : Subgroup (LoopSL2 F) := (positiveEmbedding F).range

end LoopSL2

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein

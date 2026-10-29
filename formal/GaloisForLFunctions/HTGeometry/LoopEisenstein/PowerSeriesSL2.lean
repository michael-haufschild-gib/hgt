import GaloisForLFunctions.HTGeometry.LoopEisenstein.PowerSeriesTameSymbol
import GaloisForLFunctions.HTGeometry.FiniteRingSl2

/-!
# Positive-loop matrices and elementary generation

Power-series special linear matrices embed faithfully into the Laurent group.
Elementary generation follows from the finite maximal spectrum of the local
power-series ring. The bottom row always contains a power-series unit.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable (F : Type*) [Field F]

/-- The full positive power-series matrix group. -/
abbrev PowerSeriesSL2 := Matrix.SpecialLinearGroup (Fin 2) (PowerSeries F)

/-- Inclusion of positive loops into the Laurent-series matrix group. -/
def powerSeriesSL2Map : PowerSeriesSL2 F →* SL2 (LaurentSeries F) :=
  Matrix.SpecialLinearGroup.map (HahnSeries.ofPowerSeries ℤ F)

@[simp] theorem powerSeriesSL2Map_apply (g : PowerSeriesSL2 F) (i j : Fin 2) :
    powerSeriesSL2Map F g i j = ((g i j : PowerSeries F) : LaurentSeries F) := rfl

theorem powerSeriesSL2Map_injective : Function.Injective (powerSeriesSL2Map F) := by
  intro g h he
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  exact HahnSeries.ofPowerSeries_injective
    (congrArg (fun k : SL2 (LaurentSeries F) => k i j) he)

@[simp] theorem powerSeriesSL2Map_upper (s : PowerSeries F) :
    powerSeriesSL2Map F (FiniteRingSl2.upper s) = sl2Upper (s : LaurentSeries F) :=
  FiniteRingSl2.map_upper _ s

@[simp] theorem powerSeriesSL2Map_lower (s : PowerSeries F) :
    powerSeriesSL2Map F (FiniteRingSl2.lower s) = sl2Lower (s : LaurentSeries F) :=
  FiniteRingSl2.map_lower _ s

/-- Four integral root factors suffice for every positive-loop matrix. -/
theorem powerSeriesSL2_four_factors (g : PowerSeriesSL2 F) :
    ∃ x y z w : PowerSeries F,
      g = FiniteRingSl2.upper x * FiniteRingSl2.lower y *
        FiniteRingSl2.upper z * FiniteRingSl2.lower w :=
  FiniteRingSl2.exists_four_factors g

/-- The bottom row remains unimodular after reduction to the coefficient field. -/
theorem powerSeriesSL2_bottom_constants (g : PowerSeriesSL2 F) :
    PowerSeries.constantCoeff (g 1 0) ≠ 0 ∨ PowerSeries.constantCoeff (g 1 1) ≠ 0 := by
  have hd := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two] at hd
  have h := congrArg (PowerSeries.constantCoeff (R := F)) hd
  simp only [map_sub, map_mul, map_one] at h
  by_cases hc : PowerSeries.constantCoeff (g 1 0) = 0
  · right
    intro hd
    rw [hc, hd, mul_zero, mul_zero, sub_zero] at h
    exact zero_ne_one h
  · exact Or.inl hc

@[simp] theorem powerSeriesSL2_mul_upper_c (g : PowerSeriesSL2 F) (s : PowerSeries F) :
    (g * FiniteRingSl2.upper s) 1 0 = g 1 0 := by
  simp [FiniteRingSl2.upper, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem powerSeriesSL2_mul_upper_d (g : PowerSeriesSL2 F) (s : PowerSeries F) :
    (g * FiniteRingSl2.upper s) 1 1 = g 1 0 * s + g 1 1 := by
  simp [FiniteRingSl2.upper, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem powerSeriesSL2_mul_lower_c (g : PowerSeriesSL2 F) (s : PowerSeries F) :
    (g * FiniteRingSl2.lower s) 1 0 = g 1 0 + g 1 1 * s := by
  simp [FiniteRingSl2.lower, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem powerSeriesSL2_mul_lower_d (g : PowerSeriesSL2 F) (s : PowerSeries F) :
    (g * FiniteRingSl2.lower s) 1 1 = g 1 1 := by
  simp [FiniteRingSl2.lower, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Fin.sum_univ_two]

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein

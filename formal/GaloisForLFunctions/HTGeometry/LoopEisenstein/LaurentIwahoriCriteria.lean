import GaloisForLFunctions.HTGeometry.LoopEisenstein.IwahoriGaussCoordinates
import GaloisForLFunctions.HTGeometry.LoopEisenstein.LaurentMonomialTorus

/-!
# Valuative criteria for the Laurent Iwahori

The power-series Iwahori embeds as exactly the integral Laurent matrices
whose lower-left entry has strictly smaller than unit valuation. This
identifies which elementary shears preserve its double cosets. Every Laurent
unit also splits into its integer monomial and an actual power-series unit.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable (F : Type*) [Field F]

theorem valuation_powerSeries_le_one (p : PowerSeries F) :
    laurentValuation F (p : LaurentSeries F) ≤ 1 :=
  (LaurentSeries.val_le_one_iff_eq_coe F _).2 ⟨p, rfl⟩

/-- Strictly integral Laurent valuation is exactly zero constant coefficient. -/
theorem valuation_powerSeries_lt_one_iff (p : PowerSeries F) :
    laurentValuation F (p : LaurentSeries F) < 1 ↔ PowerSeries.constantCoeff p = 0 := by
  change Valued.v (p : LaurentSeries F) < 1 ↔ _
  rw [LaurentSeries.valuation_def, ← LaurentSeries.coe_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  change p ∈ Ideal.span ({PowerSeries.X} : Set (PowerSeries F)) ↔ _
  rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]

theorem laurentValuation_div_le_one {s t : LaurentSeries F} (ht : t ≠ 0)
    (hst : laurentValuation F s ≤ laurentValuation F t) :
    laurentValuation F (s / t) ≤ 1 := by
  rw [Valuation.map_div]
  exact (div_le_one₀ (pos_iff_ne_zero.2 ((Valuation.ne_zero_iff _).2 ht))).2 hst

theorem laurentValuation_div_lt_one {s t : LaurentSeries F} (ht : t ≠ 0)
    (hst : laurentValuation F s < laurentValuation F t) :
    laurentValuation F (s / t) < 1 := by
  rw [Valuation.map_div]
  exact (div_lt_one₀ (pos_iff_ne_zero.2 ((Valuation.ne_zero_iff _).2 ht))).2 hst

/-- Integral Laurent entries recover a genuine power-series special-linear matrix. -/
theorem exists_powerSeriesSL2_of_integral (g : SL2 (LaurentSeries F))
    (hg : ∀ i j, laurentValuation F (g i j) ≤ 1) :
    ∃ p : PowerSeriesSL2 F, powerSeriesSL2Map F p = g := by
  obtain ⟨a, ha⟩ := (LaurentSeries.val_le_one_iff_eq_coe F _).1 (hg 0 0)
  obtain ⟨b, hb⟩ := (LaurentSeries.val_le_one_iff_eq_coe F _).1 (hg 0 1)
  obtain ⟨c, hc⟩ := (LaurentSeries.val_le_one_iff_eq_coe F _).1 (hg 1 0)
  obtain ⟨d, hd⟩ := (LaurentSeries.val_le_one_iff_eq_coe F _).1 (hg 1 1)
  have hdet : a * d - b * c = 1 := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    rw [map_sub, map_mul, map_mul, map_one, ha, hb, hc, hd]
    have h := Matrix.SpecialLinearGroup.det_coe g
    rw [Matrix.det_fin_two] at h
    exact h
  let p : PowerSeriesSL2 F := ⟨!![a, b; c, d], by simpa [Matrix.det_fin_two] using hdet⟩
  refine ⟨p, ?_⟩
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact ha
  · exact hb
  · exact hc
  · exact hd

/-- The Iwahori viewed inside the full Laurent matrix group. -/
def laurentIwahori : Subgroup (SL2 (LaurentSeries F)) :=
  (iwahoriMatrices F).map (powerSeriesSL2Map F)

/-- Entrywise valuation conditions characterize the actual Iwahori image. -/
theorem mem_laurentIwahori (g : SL2 (LaurentSeries F)) :
    g ∈ laurentIwahori F ↔
      (∀ i j, laurentValuation F (g i j) ≤ 1) ∧ laurentValuation F (g 1 0) < 1 := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨fun i j => valuation_powerSeries_le_one F (p i j), ?_⟩
    exact (valuation_powerSeries_lt_one_iff F (p 1 0)).2 ((mem_iwahoriMatrices F p).1 hp)
  · rintro ⟨hg, hc⟩
    obtain ⟨p, hp⟩ := exists_powerSeriesSL2_of_integral F g hg
    refine ⟨p, ?_, hp⟩
    apply (mem_iwahoriMatrices F p).2
    apply (valuation_powerSeries_lt_one_iff F (p 1 0)).1
    rw [← hp] at hc
    exact hc

/-- Upper shears with integral parameters lie in the Iwahori. -/
theorem sl2Upper_mem_laurentIwahori {s : LaurentSeries F}
    (hs : laurentValuation F s ≤ 1) : sl2Upper s ∈ laurentIwahori F := by
  obtain ⟨p, hp⟩ := (LaurentSeries.val_le_one_iff_eq_coe F s).1 hs
  refine ⟨FiniteRingSl2.upper p,
    positiveUnipotentMatrices_le_iwahori F (upper_mem_positiveUnipotentMatrices F p), ?_⟩
  rw [powerSeriesSL2Map_upper, hp]

/-- Lower shears must have strictly integral parameters. -/
theorem sl2Lower_mem_laurentIwahori {s : LaurentSeries F}
    (hs : laurentValuation F s < 1) : sl2Lower s ∈ laurentIwahori F := by
  obtain ⟨p, hp⟩ := (LaurentSeries.val_le_one_iff_eq_coe F s).1 hs.le
  have hp₀ : PowerSeries.constantCoeff p = 0 := by
    apply (valuation_powerSeries_lt_one_iff F p).1
    rw [hp]
    exact hs
  refine ⟨FiniteRingSl2.lower p,
    positiveUnipotentMatrices_le_iwahori F (lower_mem_positiveUnipotentMatrices F p hp₀), ?_⟩
  rw [powerSeriesSL2Map_lower, hp]

theorem powerSeriesSL2Map_diagonal (a : (PowerSeries F)ˣ) :
    powerSeriesSL2Map F (powerSeriesDiagonal F a) = sl2Diagonal (powerSeriesLaurentUnit F a) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [powerSeriesSL2Map_apply, powerSeriesDiagonal, sl2Diagonal, powerSeriesLaurentUnit]

theorem sl2Diagonal_powerSeriesUnit_mem_laurentIwahori (a : (PowerSeries F)ˣ) :
    sl2Diagonal (powerSeriesLaurentUnit F a) ∈ laurentIwahori F := by
  refine ⟨powerSeriesDiagonal F a, ?_, powerSeriesSL2Map_diagonal F a⟩
  apply (mem_iwahoriMatrices F (powerSeriesDiagonal F a)).2
  change PowerSeries.constantCoeff (0 : PowerSeries F) = 0
  exact map_zero _

private theorem powerSeriesPart_constant_ne_zero (a : (LaurentSeries F)ˣ) :
    PowerSeries.constantCoeff (a : LaurentSeries F).powerSeriesPart ≠ 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, LaurentSeries.powerSeriesPart_coeff,
    Nat.cast_zero, add_zero]
  intro hz
  exact a.ne_zero (HahnSeries.coeff_order_eq_zero.1 hz)

/-- The unit remaining after removal of the lowest Laurent monomial. -/
def laurentUnitPowerSeriesPart (a : (LaurentSeries F)ˣ) : (PowerSeries F)ˣ :=
  powerSeriesUnitOfConstant F (a : LaurentSeries F).powerSeriesPart
    (powerSeriesPart_constant_ne_zero F a)

/-- Every Laurent unit has an actual monomial times power-series-unit factorization. -/
theorem laurentUnit_monomial_factor (a : (LaurentSeries F)ˣ) :
    a = laurentXUnit F ^ (a : LaurentSeries F).order *
      powerSeriesLaurentUnit F (laurentUnitPowerSeriesPart F a) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, coe_laurentXUnit,
    ← RatFunc.single_zpow, coe_powerSeriesLaurentUnit]
  change (a : LaurentSeries F) = HahnSeries.single (a : LaurentSeries F).order 1 *
    ((powerSeriesUnitOfConstant F (a : LaurentSeries F).powerSeriesPart _ : PowerSeries F) :
      LaurentSeries F)
  rw [coe_powerSeriesUnitOfConstant]
  exact (LaurentSeries.single_order_mul_powerSeriesPart (a : LaurentSeries F)).symm

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein

import GaloisForLFunctions.HTGeometry.LoopEisenstein.OppositeIwahoriGauss
import GaloisForLFunctions.HTGeometry.LoopEisenstein.LaurentIwahoriCriteria
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Polynomial coordinates for positive translation cells

Upper–diagonal–lower Gauss factorization and exact power-series truncation
reduce an Iwahori translate by `diag(X^n,X^(-n))` to an upper polynomial
of degree below `2n`. Conjugation leaves the residual factor in Iwahori.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
noncomputable section

private theorem upper_scaled_diagonal {L : Type*} [Field L] (v : Lˣ) (t : L) :
    sl2Upper ((v : L) ^ 2 * t) * sl2Diagonal v = sl2Diagonal v * sl2Upper t := by
  have hv : (v : L) * (v : L)⁻¹ = 1 := mul_inv_cancel₀ v.ne_zero
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Upper, sl2Diagonal, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (v : L) * t * hv

private theorem lower_diagonal_scaled {L : Type*} [Field L] (v : Lˣ) (t : L) :
    sl2Lower t * sl2Diagonal v = sl2Diagonal v * sl2Lower ((v : L) ^ 2 * t) := by
  have hv : (v : L) * (v : L)⁻¹ = 1 := mul_inv_cancel₀ v.ne_zero
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Lower, sl2Diagonal, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination -(v : L) * t * hv

private theorem diagonal_commute {L : Type*} [Field L] (a v : Lˣ) :
    sl2Diagonal a * sl2Diagonal v = sl2Diagonal v * sl2Diagonal a := by
  rw [← sl2Diagonal_mul, ← sl2Diagonal_mul, mul_comm]

private theorem upper_gauss_translation {L : Type*} [Field L]
    (a v : Lˣ) (p t l : L) :
    sl2Upper (p + (v : L) ^ 2 * t) * sl2Diagonal a * sl2Lower l * sl2Diagonal v =
      sl2Upper p * sl2Diagonal v *
        (sl2Upper t * sl2Diagonal a * sl2Lower ((v : L) ^ 2 * l)) := by
  simp only [sl2Upper_add, mul_assoc]
  rw [lower_diagonal_scaled, ← mul_assoc (sl2Diagonal a) (sl2Diagonal v),
    diagonal_commute a v, mul_assoc (sl2Diagonal v) (sl2Diagonal a),
    ← mul_assoc (sl2Upper ((v : L) ^ 2 * t)) (sl2Diagonal v), upper_scaled_diagonal]
  simp only [mul_assoc]

variable (F : Type*) [Field F]

private theorem monomial_squared_mul_series (n : ℕ) (t : PowerSeries F) :
    (((laurentXUnit F ^ n : (LaurentSeries F)ˣ) : LaurentSeries F) ^ 2) *
      (t : LaurentSeries F) =
        ((PowerSeries.X ^ (2 * n) * t : PowerSeries F) : LaurentSeries F) := by
  rw [map_mul, map_pow, HahnSeries.ofPowerSeries_X, Units.val_pow, ← pow_mul]
  change (HahnSeries.single (1 : ℤ) (1 : F)) ^ (n * 2) * (t : LaurentSeries F) = _
  rw [Nat.mul_comm n 2]

private theorem lower_series_mem (l : PowerSeries F) (hl : PowerSeries.constantCoeff l = 0) :
    sl2Lower (l : LaurentSeries F) ∈ laurentIwahori F :=
  sl2Lower_mem_laurentIwahori F ((valuation_powerSeries_lt_one_iff F l).mpr hl)

/-- A positive monomial translation cell has a finite upper-polynomial representative. -/
theorem exists_upper_polynomial_translation_cell (n : ℕ) (g : SL2 (LaurentSeries F))
    (hg : g ∈ laurentIwahori F) :
    ∃ p : Polynomial F, p.degree < 2 * n ∧
      ∃ j ∈ laurentIwahori F,
        g * sl2Diagonal (laurentXUnit F ^ n) =
          sl2Upper ((p : PowerSeries F) : LaurentSeries F) *
            sl2Diagonal (laurentXUnit F ^ n) * j := by
  obtain ⟨g₀, hg₀, rfl⟩ := hg
  obtain ⟨u, a, l, hl, he⟩ := exists_iwahori_upper_diagonal_lower F ⟨g₀, hg₀⟩
  let p := PowerSeries.trunc (2 * n) u
  let t := PowerSeries.mk fun i => PowerSeries.coeff (i + 2 * n) u
  have hu : u = (p : PowerSeries F) + PowerSeries.X ^ (2 * n) * t :=
    (PowerSeries.eq_X_pow_mul_shift_add_trunc (2 * n) u).trans (add_comm _ _)
  let j := sl2Upper (t : LaurentSeries F) * sl2Diagonal (powerSeriesLaurentUnit F a) *
    sl2Lower ((PowerSeries.X ^ (2 * n) * l : PowerSeries F) : LaurentSeries F)
  have hl' : PowerSeries.constantCoeff (PowerSeries.X ^ (2 * n) * l) = 0 := by
    rw [map_mul, hl, mul_zero]
  have hj : j ∈ laurentIwahori F :=
    (laurentIwahori F).mul_mem
      ((laurentIwahori F).mul_mem
        (sl2Upper_mem_laurentIwahori F (valuation_powerSeries_le_one F t))
        (sl2Diagonal_powerSeriesUnit_mem_laurentIwahori F a))
      (lower_series_mem F _ hl')
  refine ⟨p, PowerSeries.degree_trunc_lt u (2 * n), j, hj, ?_⟩
  change FiniteRingSl2.upper u * powerSeriesDiagonal F a * FiniteRingSl2.lower l = g₀ at he
  rw [← he, map_mul, map_mul, powerSeriesSL2Map_upper,
    powerSeriesSL2Map_diagonal, powerSeriesSL2Map_lower]
  have huc : (u : LaurentSeries F) = ((p : PowerSeries F) : LaurentSeries F) +
      (((laurentXUnit F ^ n : (LaurentSeries F)ˣ) : LaurentSeries F) ^ 2) *
        (t : LaurentSeries F) := by
    rw [hu, map_add, monomial_squared_mul_series]
  rw [huc]
  have hex := upper_gauss_translation (powerSeriesLaurentUnit F a) (laurentXUnit F ^ n)
    ((p : PowerSeries F) : LaurentSeries F) (t : LaurentSeries F) (l : LaurentSeries F)
  rw [monomial_squared_mul_series] at hex
  exact hex

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.exists_upper_polynomial_translation_cell

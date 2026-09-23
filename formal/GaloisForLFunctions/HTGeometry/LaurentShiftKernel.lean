import GaloisForLFunctions.HTGeometry.LaurentShiftDerivation
import GaloisForLFunctions.HTGeometry.QDifferenceLaurentModel
import GaloisForLFunctions.HTGeometry.LaurentShiftFixedField
import GaloisForLFunctions.HTGeometry.RatFuncLaurentShift

/-!
# The kernel of the first-order operator in the Laurent field

`d/ds` reads on coefficients as `(d/ds F)_n = -(n-1) F_{n-1}`.  Hence a Laurent series with
vanishing derivative is a constant, and `y′ = λ y` with `λ ≠ 0` forces `y = 0`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

local instance laurentSDifferentialKernel : Differential (LaurentSeries ℂ) :=
  laurentSDifferential

/-- The Laurent Euler-quotient operator. -/
def laurentDX (w : LaurentSeries ℂ) : LaurentSeries ℂ :=
  HahnSeries.single (-1 : ℤ) (1 : ℂ) * innerEuler w

theorem coeff_laurentDX (w : LaurentSeries ℂ) (n : ℤ) :
    (laurentDX w).coeff n = ((n : ℂ) + 1) * w.coeff (n + 1) := by
  rw [laurentDX, HahnSeries.coeff_single_mul, coeff_innerEuler]
  have hidx : n - (-1 : ℤ) = n + 1 := by ring
  rw [hidx]
  push_cast
  ring

theorem laurentDX_add (x y : LaurentSeries ℂ) : laurentDX (x + y) = laurentDX x + laurentDX y := by
  rw [laurentDX, laurentDX, laurentDX, map_add, mul_add]

theorem laurentDX_mul (x y : LaurentSeries ℂ) :
    laurentDX (x * y) = laurentDX x * y + x * laurentDX y := by
  rw [laurentDX, laurentDX, laurentDX, innerEuler_leibniz, mul_add]
  ring

theorem laurentDX_algebraMap (A : PowerSeries ℂ) :
    laurentDX (algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) A)
      = algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) ((PowerSeries.derivative ℂ) A) := by
  ext n
  rw [coeff_laurentDX]
  rcases lt_or_ge n 0 with hn | hn
  · rw [coeff_algebraMap_of_neg _ hn]
    rcases lt_or_ge (n + 1) 0 with hn1 | hn1
    · rw [coeff_algebraMap_of_neg _ hn1, mul_zero]
    · have hn0 : n + 1 = 0 := by omega
      rw [hn0]
      have : ((n : ℂ) + 1) = 0 := by
        have : n = -1 := by omega
        rw [this]
        push_cast
        ring
      rw [this, zero_mul]
  · lift n to ℕ using hn with k
    show _ = ((HahnSeries.ofPowerSeries ℤ ℂ) ((PowerSeries.derivative ℂ) A)).coeff (k : ℤ)
    rw [LaurentSeries.coeff_coe_powerSeries]
    have hcast : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast]
    show ((k : ℂ) + 1) * ((HahnSeries.ofPowerSeries ℤ ℂ) A).coeff ((k + 1 : ℕ) : ℤ) = _
    rw [LaurentSeries.coeff_coe_powerSeries, PowerSeries.coeff_derivative]
    ring

/-- The corpus derivation of the Laurent field is the coefficient Euler operator divided by the
coordinate. -/
theorem formalLaurentDeriv_eq (w : LaurentSeries ℂ) :
    GaloisForLFunctions.formalLaurentDifferential.deriv w = laurentDX w := by
  classical
  obtain ⟨A, B, hB, rfl⟩ := IsFractionRing.div_surjective (A := PowerSeries ℂ) w
  set a : LaurentSeries ℂ := algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) A with ha
  set b : LaurentSeries ℂ := algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) B with hb
  have hbne : b ≠ 0 := by
    rw [hb]
    exact algebraMap_powerSeries_ne_zero (nonZeroDivisors.ne_zero hB)
  set D := GaloisForLFunctions.formalLaurentDifferential.deriv with hD
  have hDa : D a = laurentDX a := by
    rw [hD, ha, GaloisForLFunctions.formalLaurentDifferential_algebraMap, laurentDX_algebraMap]
  have hDb : D b = laurentDX b := by
    rw [hD, hb, GaloisForLFunctions.formalLaurentDifferential_algebraMap, laurentDX_algebraMap]
  have hmul : (a / b) * b = a := div_mul_cancel₀ a hbne
  have hD1 := congrArg D hmul
  simp only [hD, Derivation.leibniz, smul_eq_mul] at hD1
  have hE1 := congrArg laurentDX hmul
  rw [laurentDX_mul] at hE1
  rw [← hD] at hD1
  rw [hDa, hDb] at hD1
  have hzero : b * (D (a / b) - laurentDX (a / b)) = 0 := by
    linear_combination hD1 - hE1
  rcases mul_eq_zero.mp hzero with hc | hc
  · exact absurd hc hbne
  · exact sub_eq_zero.mp hc

/-! ### Coefficients of `d/ds` and its kernel -/

theorem coeff_laurentSDeriv (w : LaurentSeries ℂ) (n : ℤ) :
    (w′).coeff n = -((n : ℂ) - 1) * w.coeff (n - 1) := by
  have key : -(laurentX ^ (2 : ℕ)) * (HahnSeries.single (-1 : ℤ) (1 : ℂ) * innerEuler w)
      = -(HahnSeries.single (1 : ℤ) (1 : ℂ) * innerEuler w) := by
    have hX2 : (laurentX : LaurentSeries ℂ) ^ (2 : ℕ) = HahnSeries.single (2 : ℤ) (1 : ℂ) := by
      rw [laurentX_eq_single, pow_two, HahnSeries.single_mul_single, mul_one]
      norm_num
    have hprod : (HahnSeries.single (2 : ℤ) (1 : ℂ)) * (HahnSeries.single (-1 : ℤ) (1 : ℂ))
        = HahnSeries.single (1 : ℤ) (1 : ℂ) := by
      rw [HahnSeries.single_mul_single, mul_one]
      norm_num
    rw [hX2, ← hprod]
    ring
  rw [laurentSDeriv_apply, formalLaurentDeriv_eq, laurentDX, key, HahnSeries.coeff_neg,
    HahnSeries.coeff_single_mul, coeff_innerEuler]
  push_cast
  ring

theorem exists_laurentC_of_deriv_eq_zero {w : LaurentSeries ℂ} (hw : w′ = 0) :
    ∃ c : ℂ, laurentC c = w := by
  refine ⟨w.coeff 0, ?_⟩
  ext n
  rw [← laurentCHom_apply, laurentCHom_eq_single, HahnSeries.coeff_single]
  by_cases hn : n = 0
  · rw [if_pos hn, hn]
  · rw [if_neg hn]
    have hzero := congrArg (fun z : LaurentSeries ℂ => z.coeff (n + 1)) hw
    simp only [HahnSeries.coeff_zero] at hzero
    rw [coeff_laurentSDeriv] at hzero
    have hidx : n + 1 - 1 = n := by ring
    rw [hidx] at hzero
    have hne : -(((n + 1 : ℤ) : ℂ) - 1) ≠ 0 := by
      intro hc
      have hcast : ((n : ℤ) : ℂ) = 0 := by
        push_cast at hc
        linear_combination -hc
      have : (n : ℤ) = 0 := by exact_mod_cast hcast
      exact hn this
    rcases mul_eq_zero.mp hzero with hc | hc
    · exact absurd hc hne
    · exact hc.symm

theorem eq_zero_of_deriv_eq_const_mul {lam : ℂ} (hlam : lam ≠ 0) {w : LaurentSeries ℂ}
    (hw : w′ = laurentC lam * w) : w = 0 := by
  by_contra hne
  have hcoeff := congrArg (fun z : LaurentSeries ℂ => z.coeff w.order) hw
  rw [coeff_laurentSDeriv, ← laurentCHom_apply, laurentCHom_eq_single,
    HahnSeries.coeff_single_mul, sub_zero] at hcoeff
  have hlow : w.coeff (w.order - 1) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_order (by omega)
  rw [hlow, mul_zero] at hcoeff
  have hord : w.coeff w.order ≠ 0 := fun h => hne (HahnSeries.coeff_order_eq_zero.mp h)
  rcases mul_eq_zero.mp hcoeff.symm with hc | hc
  · exact hlam hc
  · exact hord hc

end

end GaloisForLFunctions.HTGeometry

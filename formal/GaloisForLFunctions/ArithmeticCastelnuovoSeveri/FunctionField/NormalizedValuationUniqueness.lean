import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Order.GroupWithZero.WithZero
import Mathlib.Tactic.Linarith

/-!
# Uniqueness of a surjective integer-valued valuation

Equivalent valuations have the same order comparisons. If both are
surjective onto the integers with zero adjoined, the values of two
primitive poles give positive integers whose product is one. Hence
the scale factor is one and the valuations agree exactly.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable {L : Type*} [Field L]

/-- Equivalent surjective valuations with integer value group are equal, with no rescaling. -/
theorem normalizedValuation_eq_of_isEquiv
    (v w : Valuation L (WithZero (Multiplicative ℤ))) (h : v.IsEquiv w)
    (hv : Function.Surjective v) (hw : Function.Surjective w) : v = w := by
  obtain ⟨t, ht⟩ := hv (WithZero.exp (1 : ℤ))
  obtain ⟨u, hu⟩ := hw (WithZero.exp (1 : ℤ))
  have ht0 : t ≠ 0 := (map_ne_zero v).mp (by rw [ht]; exact WithZero.exp_ne_zero)
  have hu0 : u ≠ 0 := (map_ne_zero w).mp (by rw [hu]; exact WithZero.exp_ne_zero)
  have hwt0 : w t ≠ 0 := (map_ne_zero w).mpr ht0
  have hvu0 : v u ≠ 0 := (map_ne_zero v).mpr hu0
  let k := WithZero.log (w t)
  let l := WithZero.log (v u)
  have hk : 0 < k := by
    have hlt : 1 < w t := h.one_lt_iff_one_lt.mp (by
      rw [ht, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      exact zero_lt_one)
    rw [← WithZero.exp_log hwt0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
    exact hlt
  have hl : 0 < l := by
    have hlt : 1 < v u := h.one_lt_iff_one_lt.mpr (by
      rw [hu, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      exact zero_lt_one)
    rw [← WithZero.exp_log hvu0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
    exact hlt
  have hpower (x : L) (hx : x ≠ 0) : v x = v (t ^ WithZero.log (v x)) := by
    rw [map_zpow₀, ht, ← WithZero.exp_zsmul]
    simpa [zsmul_eq_mul] using (WithZero.exp_log ((map_ne_zero v).mpr hx)).symm
  have hprod : (1 : ℤ) = l * k := by
    have he := congrArg WithZero.log (h.eq_iff.mp (hpower u hu0))
    rw [hu, WithZero.log_exp, map_zpow₀, WithZero.log_zpow, zsmul_eq_mul] at he
    exact he
  have hk1 : k = 1 := by
    have hkge : 1 ≤ k := by omega
    have hlge : 0 ≤ l - 1 := by omega
    have hmul := mul_nonneg (le_of_lt hk) hlge
    nlinarith only [hprod, hkge, hmul]
  have hwt : w t = WithZero.exp (1 : ℤ) := by
    rw [← WithZero.exp_log hwt0]
    change WithZero.exp k = _
    rw [hk1]
  apply Valuation.ext
  intro x
  by_cases hx : x = 0
  · rw [hx, map_zero, map_zero]
  · have he := h.eq_iff.mp (hpower x hx)
    rw [map_zpow₀, hwt, ← WithZero.exp_zsmul] at he
    simpa [zsmul_eq_mul, WithZero.exp_log ((map_ne_zero v).mpr hx)] using he.symm

/-- Two surjective integer-valued valuations with the same valuation ring agree exactly. -/
theorem normalizedValuation_eq_of_valuationSubring_eq
    (v w : Valuation L (WithZero (Multiplicative ℤ)))
    (h : v.valuationSubring = w.valuationSubring)
    (hv : Function.Surjective v) (hw : Function.Surjective w) : v = w :=
  normalizedValuation_eq_of_isEquiv v w
    ((Valuation.isEquiv_iff_valuationSubring v w).mpr h) hv hw

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

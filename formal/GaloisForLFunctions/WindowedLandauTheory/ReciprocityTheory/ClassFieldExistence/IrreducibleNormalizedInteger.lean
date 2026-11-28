import Mathlib.RingTheory.Valuation.Integers
import Mathlib.Algebra.Order.GroupWithZero.WithZero

/-! An integer of valuation exp(-1) in a discrete value group is
irreducible. This also applies to a base uniformizer after unramified
extension of the completion. -/

noncomputable section

open WithZero

namespace GlobalTheory.Reciprocity

theorem irreducible_integer_of_valuation_eq_exp_neg_one {F : Type*} [Field F]
    (v : Valuation F ℤᵐ⁰) (x : v.integer)
    (hx : v x.val = exp (-1 : ℤ)) : Irreducible x := by
  have hl : v x.val < 1 := by
    rw [hx, ← exp_zero, exp_lt_exp]
    omega
  refine ⟨Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr hl, fun a b hab => ?_⟩
  by_contra! hn
  have ha := Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hn.1
  have hb := Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hn.2
  have he : v a.val * v b.val = exp (-1 : ℤ) := by
    have h := congrArg Subtype.val hab
    change x.val = a.val * b.val at h
    rw [← map_mul, ← h, hx]
  have hne : v a.val * v b.val ≠ 0 := he ▸ exp_ne_zero
  obtain ⟨ha0, hb0⟩ := mul_ne_zero_iff.mp hne
  rw [← exp_log ha0, ← exp_zero, exp_lt_exp] at ha
  rw [← exp_log hb0, ← exp_zero, exp_lt_exp] at hb
  rw [← exp_log ha0, ← exp_log hb0, ← exp_add, exp_inj] at he
  exact (show False by omega)

end GlobalTheory.Reciprocity

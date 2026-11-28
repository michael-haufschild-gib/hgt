import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

/-! The class of q modulo q^n - 1 has order n. This gives a cyclotomic
stage detecting divisibility of a Weil degree by n. -/

namespace GlobalTheory.Reciprocity

theorem orderOf_unit_of_val_eq_natCast_pow_sub_one {q n : ℕ}
    (hq : 1 < q) (hn : 0 < n) (x : (ZMod (q ^ n - 1))ˣ)
    (hx : x.val = (q : ZMod (q ^ n - 1))) : orderOf x = n := by
  let c := q ^ n - 1
  have hqn : 1 < q ^ n := one_lt_pow₀ hq hn.ne'
  have he : q ^ n = c + 1 := (Nat.sub_add_cancel hqn.le).symm
  have hxpow : x ^ n = 1 := by
    apply Units.ext
    change (x.val : ZMod c) ^ n = 1
    rw [hx, ← Nat.cast_pow]
    change ((q ^ n : ℕ) : ZMod c) = 1
    calc
      ((q ^ n : ℕ) : ZMod c) = ((c + 1 : ℕ) : ZMod c) :=
        congrArg (fun a : ℕ => (a : ZMod c)) he
      _ = 1 := by rw [Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
  have hdvd : orderOf x ∣ n := orderOf_dvd_of_pow_eq_one hxpow
  have hdpos : 0 < orderOf x := by
    apply Nat.pos_of_ne_zero
    intro he
    rw [he, zero_dvd_iff] at hdvd
    exact hn.ne' hdvd
  refine le_antisymm (Nat.le_of_dvd hn hdvd) (le_of_not_gt fun hd => ?_)
  let d := orderOf x
  have hpow : (q : ZMod c) ^ d = 1 := by
    have h := congrArg (fun z : (ZMod c)ˣ => z.val) (pow_orderOf_eq_one x)
    rw [Units.val_pow_eq_pow_val, hx, Units.val_one] at h
    exact h
  have hqd : 1 < q ^ d := one_lt_pow₀ hq hdpos.ne'
  have h : c ∣ q ^ d - 1 := (ZMod.natCast_eq_zero_iff _ _).mp (by
    rw [Nat.cast_sub hqd.le, Nat.cast_one, Nat.cast_pow, hpow, sub_self])
  have hl : q ^ d < q ^ n := pow_lt_pow_right₀ hq hd
  exact (Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hqd)
    (show q ^ d - 1 < c by dsimp [c]; omega)) h

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.orderOf_unit_of_val_eq_natCast_pow_sub_one

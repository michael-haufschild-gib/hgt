import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Multiples of a fixed modulus in an integer interval

Every sieve applied to a short interval needs one arithmetic input: the number of multiples of a
modulus `d` inside `Ioc a b` equals `b / d - a / d`, and this differs from the archimedean
prediction `(b - a) / d` by strictly less than one.

Mathlib supplies the anchored case `Nat.Ioc_filter_dvd_card_eq_div` for `Ioc 0 n`.  This file
promotes it to a general interval and records the real-valued remainder bound, which is the exact
`R_d` term of a sieve problem.

Everything here is unconditional and holds for every modulus, including `d = 0`.
-/

namespace RHTower.Sieve

open Finset

/-- **Exact interval count.**  The multiples of `d` in `Ioc a b` are counted by the difference of
the two anchored quotients. -/
theorem card_filter_dvd_Ioc (d a b : ℕ) (hab : a ≤ b) :
    #{x ∈ Ioc a b | d ∣ x} = b / d - a / d := by
  have hunion : Ioc 0 a ∪ Ioc a b = Ioc 0 b :=
    Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le a) hab
  have hdisj : Disjoint (Ioc 0 a) (Ioc a b) := by
    refine Finset.disjoint_left.2 ?_
    intro x hx hx'
    exact absurd (Finset.mem_Ioc.1 hx).2 (not_le.2 (Finset.mem_Ioc.1 hx').1)
  have hsplit :
      #{x ∈ Ioc 0 b | d ∣ x} = #{x ∈ Ioc 0 a | d ∣ x} + #{x ∈ Ioc a b | d ∣ x} := by
    rw [← hunion, Finset.filter_union, Finset.card_union_of_disjoint]
    exact hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hb : #{x ∈ Ioc 0 b | d ∣ x} = b / d := Nat.Ioc_filter_dvd_card_eq_div b d
  have ha : #{x ∈ Ioc 0 a | d ∣ x} = a / d := Nat.Ioc_filter_dvd_card_eq_div a d
  omega

/-- Floor sandwich for a natural quotient, in the reals. -/
theorem cast_div_bounds {d n : ℕ} (hd : 0 < d) :
    ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d ∧ (n : ℝ) / d < ((n / d : ℕ) : ℝ) + 1 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hdm := Nat.div_add_mod n d
  have hmod := Nat.mod_lt n hd
  constructor
  · rw [le_div_iff₀ hd0]
    have hle : d * (n / d) ≤ n := by omega
    calc ((n / d : ℕ) : ℝ) * d = ((d * (n / d) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (n : ℝ) := by exact_mod_cast hle
  · rw [div_lt_iff₀ hd0]
    have hlt : n < d * (n / d) + d := by omega
    calc (n : ℝ) < ((d * (n / d) + d : ℕ) : ℝ) := by exact_mod_cast hlt
      _ = (((n / d : ℕ) : ℝ) + 1) * d := by push_cast; ring

/-- **Sieve remainder bound.**  The exact interval count of multiples of `d` differs from the
archimedean main term `(b - a) / d` by strictly less than one, uniformly in `a`, `b` and `d`. -/
theorem abs_card_filter_dvd_Ioc_sub_lt (d a b : ℕ) (hd : 0 < d) (hab : a ≤ b) :
    |(#{x ∈ Ioc a b | d ∣ x} : ℝ) - ((b : ℝ) - a) / d| < 1 := by
  obtain ⟨hb1, hb2⟩ := cast_div_bounds (d := d) (n := b) hd
  obtain ⟨ha1, ha2⟩ := cast_div_bounds (d := d) (n := a) hd
  have hcount : (#{x ∈ Ioc a b | d ∣ x} : ℝ) = ((b / d : ℕ) : ℝ) - ((a / d : ℕ) : ℝ) := by
    rw [card_filter_dvd_Ioc d a b hab]
    have hle : a / d ≤ b / d := Nat.div_le_div_right hab
    push_cast [Nat.cast_sub hle]
    ring
  have hsplit : ((b : ℝ) - a) / d = (b : ℝ) / d - (a : ℝ) / d := by ring
  rw [hcount, hsplit, abs_lt]
  constructor <;> linarith

end RHTower.Sieve

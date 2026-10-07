import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Tactic

/-!
# Relations among the three translated powers in characteristic three

For positive degree, the relation space is zero unless the degree is a power
of three. At those degrees it consists exactly of equal coefficient triples.
The proof combines evaluations at the three field elements with Lucas's
prime-power criterion and the Frobenius converse.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Polynomial
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

def ternaryPowerSum (n : ℕ) : (ZMod 3)[X] := X ^ n + (X - 1) ^ n + (X + 1) ^ n

theorem odd_of_ternaryPowerSum_eq_zero {n : ℕ} (hn : 0 < n)
    (hs : ternaryPowerSum n = 0) : Odd n := by
  have h := congrArg (Polynomial.eval (1 : ZMod 3)) hs
  have hv : (1 : ZMod 3) + (-1) ^ n = 0 := by
    simpa [ternaryPowerSum, hn.ne', show (1 + 1 : ZMod 3) = -1 by decide] using h
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow] at hv
    exact False.elim ((by decide : (2 : ZMod 3) ≠ 0) hv)
  · exact ho

theorem ternaryPowerSum_eq_zero_iff {n : ℕ} (hn : 0 < n) :
    ternaryPowerSum n = 0 ↔ ∃ e : ℕ, n = 3 ^ e := by
  constructor
  · intro hs
    have ho := odd_of_ternaryPowerSum_eq_zero hn hs
    have hoddcoeff (k : ℕ) (hk : k < n) (hko : Odd k) :
        (n.choose k : ZMod 3) = 0 := by
      have heven : Even (n - k) := by
        obtain ⟨a, ha⟩ := ho
        obtain ⟨b, hb⟩ := hko
        exact ⟨a - b, by omega⟩
      have hminus : (((X : (ZMod 3)[X]) - 1) ^ n).coeff k =
          (-1 : ZMod 3) ^ (n - k) * (n.choose k : ZMod 3) := by
        simpa only [map_neg, map_one, sub_eq_add_neg] using
          (Polynomial.coeff_X_add_C_pow (-1 : ZMod 3) n k)
      have hc := congrArg (fun p : (ZMod 3)[X] => p.coeff k) hs
      simp only [ternaryPowerSum, Polynomial.coeff_add, Polynomial.coeff_zero] at hc
      rw [Polynomial.coeff_X_pow, if_neg (ne_of_lt hk), zero_add, hminus,
        Polynomial.coeff_X_add_one_pow, heven.neg_one_pow, one_mul] at hc
      exact (mul_eq_zero.mp (show (2 : ZMod 3) * (n.choose k : ZMod 3) = 0 by
        simpa only [two_mul] using hc)).resolve_left (by decide)
    have hchoose (i : ℕ) (hi : i ∈ Finset.Icc 1 (n - 1)) :
        (n.choose i : ZMod 3) = 0 := by
      have hi1 := (Finset.mem_Icc.mp hi).1
      have hin := (Finset.mem_Icc.mp hi).2
      rcases Nat.even_or_odd i with he | hiodd
      · have hdiff : Odd (n - i) := by
          obtain ⟨a, ha⟩ := ho
          obtain ⟨b, hb⟩ := he
          exact ⟨a - b, by omega⟩
        have h := hoddcoeff (n - i) (by omega) hdiff
        simpa only [Nat.choose_symm (show i ≤ n by omega)] using h
      · exact hoddcoeff i (by omega) hiodd
    refine ⟨multiplicity 3 n, Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat hn ?_⟩
    intro i hi
    exact (ZMod.natCast_eq_natCast_iff (n.choose i) 0 3).mp (by simpa using hchoose i hi)
  · rintro ⟨e, rfl⟩
    unfold ternaryPowerSum
    rw [sub_pow_char_pow (X : (ZMod 3)[X]) 1 e (p := 3),
      add_pow_char_pow (X : (ZMod 3)[X]) 1 3 e, one_pow]
    have h3 : (3 : (ZMod 3)[X]) = 0 := by
      simpa only [Polynomial.C_ofNat, map_zero] using
        congrArg (Polynomial.C : ZMod 3 → (ZMod 3)[X])
          (by decide : (3 : ZMod 3) = 0)
    linear_combination (X ^ (3 ^ e)) * h3

/-- Complete kernel classification, including the zero coefficient vector. -/
theorem ternary_translated_power_relation_iff {n : ℕ} (hn : 0 < n) (a b c : ZMod 3) :
    C a * X ^ n + C b * (X - 1) ^ n + C c * (X + 1) ^ n = (0 : (ZMod 3)[X]) ↔
      (a = 0 ∧ b = 0 ∧ c = 0) ∨ ((∃ e : ℕ, n = 3 ^ e) ∧ a = b ∧ b = c) := by
  constructor
  · intro hrel
    have h0 : b * (-1) ^ n + c = 0 := by
      simpa [hn.ne'] using congrArg (Polynomial.eval (0 : ZMod 3)) hrel
    have h1 : a + c * (-1) ^ n = 0 := by
      simpa [hn.ne', show (1 + 1 : ZMod 3) = -1 by decide] using
        congrArg (Polynomial.eval (1 : ZMod 3)) hrel
    have hm : a * (-1) ^ n + b = 0 := by
      simpa [hn.ne', show (-1 - 1 : ZMod 3) = 1 by decide] using
        congrArg (Polynomial.eval (-1 : ZMod 3)) hrel
    rcases Nat.even_or_odd n with he | ho
    · rw [he.neg_one_pow, mul_one] at h0 h1 hm
      have ha2 : (2 : ZMod 3) * a = 0 := by linear_combination h1 + hm - h0
      have ha : a = 0 := (mul_eq_zero.mp ha2).resolve_left (by decide)
      exact Or.inl ⟨ha, by simpa [ha] using hm, by simpa [ha] using h1⟩
    · rw [ho.neg_one_pow, mul_neg_one] at h0 h1 hm
      have hac : a = c := by linear_combination h1
      have hbc : b = c := by linear_combination -h0
      subst a
      subst b
      by_cases hc : c = 0
      · exact Or.inl ⟨hc, hc, hc⟩
      · have hprod : C c * ternaryPowerSum n = 0 := by
          simpa only [ternaryPowerSum, mul_add] using hrel
        have hs : ternaryPowerSum n = 0 := (mul_eq_zero.mp hprod).resolve_left
          (fun h => hc (Polynomial.C_eq_zero.mp h))
        exact Or.inr ⟨(ternaryPowerSum_eq_zero_iff hn).mp hs, rfl, rfl⟩
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨hp, hab, hbc⟩)
    · simp
    · subst a
      subst b
      have hs := (ternaryPowerSum_eq_zero_iff hn).mpr hp
      calc
        C c * X ^ n + C c * (X - 1) ^ n + C c * (X + 1) ^ n =
            C c * ternaryPowerSum n := by simp only [ternaryPowerSum, mul_add]
        _ = 0 := by rw [hs, mul_zero]

end
end GaloisForLFunctions.HTGeometry

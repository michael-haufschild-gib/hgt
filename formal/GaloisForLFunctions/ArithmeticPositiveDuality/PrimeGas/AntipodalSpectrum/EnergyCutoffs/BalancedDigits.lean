import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Reading base-C digits in base C²

The digit map enumerates the integers whose base-C² digits lie below C.
Its square-root growth has a direct proof using the last digit recursion.
-/

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

/-- The integer obtained by inserting a zero after each base-C digit. -/
def stretchDigits (C n : ℕ) : ℕ := Nat.ofDigits (C^2) (C.digits n)

private theorem recode {a b n : ℕ} (hb : 1 < b) (h : ∀ d ∈ a.digits n, d < b) :
    b.digits (Nat.ofDigits b (a.digits n)) = a.digits n :=
  Nat.digits_ofDigits b hb _ h fun hn => Nat.getLast_digit_ne_zero a (Nat.digits_ne_nil_iff_ne_zero.mp hn)

private theorem base_le_square (C : ℕ) (hc : 1 < C) : C ≤ C^2 := by
  rw [pow_two]
  exact Nat.le_mul_of_pos_right _ (by omega)

theorem stretched_digits (C : {c : ℕ // 1 < c}) (n : ℕ) :
    (C.val^2).digits (stretchDigits C.val n) = C.val.digits n :=
  recode (one_lt_pow₀ C.property (by norm_num : (2:ℕ) ≠ 0))
    fun _ hd => (Nat.digits_lt_base C.property hd).trans_le (base_le_square C.val C.property)

/-- Every restricted digit string decodes uniquely in base C. -/
def stretchEquiv (C : {c : ℕ // 1 < c}) :
    ℕ ≃ {x : ℕ // ∀ d ∈ (C.val^2).digits x, d < C.val} where
  toFun n := ⟨stretchDigits C.val n,fun d hd => Nat.digits_lt_base C.property ((stretched_digits C n) ▸ hd)⟩
  invFun x := Nat.ofDigits C.val ((C.val^2).digits x.val)
  left_inv n := by
    change Nat.ofDigits C.val ((C.val^2).digits (stretchDigits C.val n)) = n
    rw [stretched_digits,Nat.ofDigits_digits]
  right_inv x := by
    apply Subtype.ext
    change Nat.ofDigits (C.val^2) (C.val.digits (Nat.ofDigits C.val ((C.val^2).digits x.val))) = x.val
    rw [recode C.property x.property,Nat.ofDigits_digits]

private theorem word_bounds (C : ℕ) (L : List ℕ) (hd : ∀ d ∈ L, d < C) :
    let n := Nat.ofDigits C L
    let v := Nat.ofDigits (C^2) L
    n*(n+2) ≤ (C+1)*v ∧ v ≤ n^2 := by
  induction L with
  | nil => simp
  | cons d L ih =>
    let m := Nat.ofDigits C L
    let v := Nat.ofDigits (C^2) L
    obtain ⟨hl,hu⟩ := ih (fun d hm => hd d (List.mem_cons_of_mem _ hm))
    change m*(m+2) ≤ (C+1)*v at hl
    change v ≤ m^2 at hu
    have hdc : d+1 ≤ C := hd d List.mem_cons_self
    have hdd : d ≤ d*d := by
      cases d with
      | zero => exact le_rfl
      | succ d => exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    change (d+C*m)*(d+C*m+2) ≤ (C+1)*(d+C^2*v) ∧ d+C^2*v ≤ (d+C*m)^2
    constructor
    · nlinarith only [Nat.mul_le_mul_left (C^2) hl,Nat.mul_le_mul_right (2*C*m+d) hdc]
    · nlinarith only [Nat.mul_le_mul_left (C^2) hu,hdd,Nat.zero_le (2*C*m*d)]

theorem stretch_quadratic_bounds (C : {c : ℕ // 1 < c}) (n : ℕ) :
    n*(n+2) ≤ (C.val+1)*stretchDigits C.val n ∧ stretchDigits C.val n ≤ n^2 := by
  have h := word_bounds C.val (C.val.digits n) fun _ hd => Nat.digits_lt_base C.property hd
  simpa only [Nat.ofDigits_digits,stretchDigits] using h

/-- The digit map carries the first Cᵏ indices onto every admissible cutoff below C²ᵏ. -/
theorem stretch_lt_power (C : {c : ℕ // 1 < c}) (n k : ℕ) :
    stretchDigits C.val n < (C.val^2)^k ↔ n < C.val^k := by
  rw [← Nat.digits_length_le_iff (one_lt_pow₀ C.property (by norm_num : (2:ℕ) ≠ 0)),
    stretched_digits,Nat.digits_length_le_iff C.property]

#print axioms stretchEquiv
#print axioms stretch_quadratic_bounds
#print axioms stretch_lt_power

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

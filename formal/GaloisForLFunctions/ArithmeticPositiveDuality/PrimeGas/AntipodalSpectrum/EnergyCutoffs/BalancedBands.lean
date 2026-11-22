import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedDigits

/-!
# Exact gaps in the balanced digit spectrum

The largest admissible word below a radix power consists entirely of
largest digits. The next radix power is itself admissible.
-/

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

private theorem last_digit (C : {c : ℕ // 1 < c}) : (C.val+1)*(C.val-1)+1 = C.val^2 := by
  have h : C.val-1+1 = C.val := Nat.sub_add_cancel C.property.le
  nlinarith only [congrArg ((C.val+1)*·) h]

private theorem word_cap (C : {c : ℕ // 1 < c}) (L : List ℕ) (hd : ∀ d ∈ L, d < C.val) :
    (C.val+1)*Nat.ofDigits (C.val^2) L+1 ≤ (C.val^2)^L.length := by
  induction L with
  | nil => simp
  | cons d L ih =>
    have h := Nat.mul_le_mul_left (C.val^2) (ih (fun _ ha => hd _ (List.mem_cons_of_mem _ ha)))
    have hd' := hd d List.mem_cons_self
    have h₁ := Nat.mul_le_mul_left (C.val+1) (show d ≤ C.val-1 by omega)
    rw [List.length_cons,Nat.ofDigits_cons,pow_succ' (C.val^2) L.length]
    nlinarith only [h,h₁,last_digit C]

/-- Every admissible label below Bᵏ satisfies (C+1)X+1 ≤ Bᵏ, where B=C². -/
theorem stretched_band_cap (C : {c : ℕ // 1 < c}) (k : ℕ)
    (x : {n : ℕ // n < (C.val^2)^k ∧ ∀ d ∈ (C.val^2).digits n, d < C.val}) :
    (C.val+1)*x.val+1 ≤ (C.val^2)^k := by
  have hb := one_lt_pow₀ C.property (by norm_num : (2:ℕ) ≠ 0)
  have h := word_cap C _ x.property.2
  rw [Nat.ofDigits_digits] at h
  exact h.trans (Nat.pow_le_pow_right hb.le ((Nat.digits_length_le_iff hb x.val).mpr x.property.1))

/-- The largest word padded to k digits. -/
def lastBalancedWord (C k : ℕ) : ℕ := Nat.ofDigits (C^2) (List.replicate k (C-1))

theorem last_balanced_scale (C : {c : ℕ // 1 < c}) (k : ℕ) :
    (C.val+1)*lastBalancedWord C.val k+1 = (C.val^2)^k := by
  induction k with
  | zero => simp [lastBalancedWord]
  | succ k ih =>
    change (C.val+1)*Nat.ofDigits (C.val^2) (List.replicate (k+1) (C.val-1))+1 = _
    rw [List.replicate_succ,Nat.ofDigits_cons,pow_succ' (C.val^2) k]
    change (C.val+1)*(C.val-1+C.val^2*lastBalancedWord C.val k)+1 = _
    nlinarith only [congrArg ((C.val^2)*·) ih,last_digit C]

theorem last_balanced_digits (C : {c : ℕ // 1 < c}) (k : ℕ) :
    (C.val^2).digits (lastBalancedWord C.val k) = List.replicate k (C.val-1) := by
  have hc := C.property
  apply Nat.digits_ofDigits _ (one_lt_pow₀ hc (by norm_num : (2:ℕ) ≠ 0))
  · intro d hd
    have he : d = C.val-1 := List.eq_of_mem_replicate hd
    have hmul := Nat.le_mul_of_pos_right C.val (by omega : 0 < C.val)
    rw [he,pow_two]
    omega
  · intro hn
    have he := List.eq_of_mem_replicate (List.getLast_mem hn)
    omega

/-- Both the last word below Bᵏ and the first word at Bᵏ occur in the admissible spectrum. -/
theorem balanced_gap_endpoints (C : {c : ℕ // 1 < c}) (k : ℕ) :
    (∀ d ∈ (C.val^2).digits (lastBalancedWord C.val k), d < C.val) ∧
    (∀ d ∈ (C.val^2).digits ((C.val^2)^k), d < C.val) := by
  have hc := C.property
  constructor
  · rw [last_balanced_digits]
    intro d hd
    have he := List.eq_of_mem_replicate hd
    omega
  · have hb := one_lt_pow₀ hc (by norm_num : (2:ℕ) ≠ 0)
    have he := Nat.digits_base_pow_mul (k := k) hb (by norm_num : 0 < 1)
    rw [mul_one,Nat.digits_of_lt _ 1 one_ne_zero hb] at he
    rw [he]
    intro d hd
    rcases List.mem_append.mp hd with h | h
    · have he := List.eq_of_mem_replicate h
      omega
    · rw [List.mem_singleton.mp h]
      exact hc

#print axioms stretched_band_cap
#print axioms last_balanced_scale
#print axioms last_balanced_digits
#print axioms balanced_gap_endpoints

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.KummerExponentParity

/-!
# Equality in the maximal Kummer genus bound

The ramification expression is at most `(q-1)Q`, where `Q=q^(n+1)`.
For a positive covering index, `q<Q` makes this strictly smaller than
`Q(Q-1)`. At index zero, parity of the geometric exponent determines
whether the ramification expression vanishes or reaches the bound.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

private theorem base_le_succ_power (q n : ℕ) (hq : 1 ≤ q) : q ≤ q ^ (n + 1) := by
  induction n with
  | zero => rw [pow_one]
  | succ n ih =>
    rw [pow_succ]
    exact ih.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (q ^ (n + 1)) hq)

/-- The Kummer ramification genus reaches the maximal-curve bound exactly at covering index zero and odd branch length. -/
theorem kummer_genus_ihara_equality_iff (q n r : ℕ) (hq : 2 ≤ q) :
    (q - 1) * (q ^ (n + 1) + 1 - Nat.gcd (q ^ (n + 1) + 1) (kummerExponent q r)) =
      q ^ (n + 1) * (q ^ (n + 1) - 1) ↔ n = 0 ∧ Odd r := by
  cases n with
  | zero =>
    simp only [Nat.zero_add, pow_one, true_and]
    have hform : ∃ k, r = 2 * k ∨ r = 2 * k + 1 := by
      refine ⟨r / 2, ?_⟩
      have hd := Nat.div_add_mod r 2
      have hm := Nat.mod_lt r (show 0 < 2 by omega)
      omega
    obtain ⟨k, hk | hk⟩ := hform
    · subst r
      rw [kummerExponent_even_gcd, Nat.sub_self, mul_zero]
      constructor
      · intro h
        have hpos : 0 < q * (q - 1) := Nat.mul_pos (by omega) (by omega)
        omega
      · rintro ⟨t, ht⟩
        omega
    · subst r
      rw [kummerExponent_odd_gcd, Nat.add_sub_cancel, Nat.mul_comm (q - 1) q]
      exact iff_of_true rfl ⟨k, by omega⟩
  | succ n =>
    simp only [Nat.succ_ne_zero, false_and, iff_false]
    intro heq
    let Q := q ^ (n + 1 + 1)
    let δ := Nat.gcd (Q + 1) (kummerExponent q r)
    have hδ : 0 < δ := by
      by_contra h
      have hz : δ = 0 := by omega
      obtain ⟨t, ht⟩ := Nat.gcd_dvd_left (Q + 1) (kummerExponent q r)
      change Q + 1 = δ * t at ht
      rw [hz, zero_mul] at ht
      omega
    have hqQ : q < Q := by
      have hbase := base_le_succ_power q n (by omega)
      have hmul := Nat.mul_le_mul_right q hbase
      have hstrict : q < q * q := by
        simpa only [Nat.one_mul] using
          Nat.mul_lt_mul_of_pos_right (show 1 < q by omega) (show 0 < q by omega)
      exact hstrict.trans_le (by simpa only [Q, pow_succ] using hmul)
    have hupper : (q - 1) * (Q + 1 - δ) ≤ (q - 1) * Q :=
      Nat.mul_le_mul_left (q - 1) (by omega)
    have hstrict : (q - 1) * Q < (Q - 1) * Q :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    change (q - 1) * (Q + 1 - δ) = Q * (Q - 1) at heq
    rw [Nat.mul_comm Q (Q - 1)] at heq
    omega

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

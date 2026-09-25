import GaloisForLFunctions.RHTower.RouteEFixedOrderCofactorLinearization

open Finset
namespace RHTower
noncomputable section

/-- Sharp finite reciprocal-square tail, proved by telescoping. -/
theorem routeE_invSqTail_Ioo_strong (k N : ℕ) (hk : 1 ≤ k) :
    (∑ d ∈ Finset.Ioo k (k + N + 1), 1 / (d : ℝ) ^ (2 : ℕ)) ≤
      1 / (k : ℝ) - 1 / ((k + N : ℕ) : ℝ) := by
  induction N with
  | zero =>
      have hset : Finset.Ioo k (k + 0 + 1) = ∅ := by
        ext d
        simp [Finset.mem_Ioo]
      rw [hset]
      simp
  | succ N ih =>
      have hset : Finset.Ioo k (k + (N + 1) + 1) =
          insert (k + N + 1) (Finset.Ioo k (k + N + 1)) := by
        ext d
        simp only [Finset.mem_Ioo, Finset.mem_insert]
        omega
      have hnot : k + N + 1 ∉ Finset.Ioo k (k + N + 1) := by
        simp only [Finset.mem_Ioo]
        omega
      rw [hset, Finset.sum_insert hnot]
      have hval : (0 : ℝ) < (k + N : ℕ) := by
        exact_mod_cast (show 0 < k + N by omega)
      have hval1 : (0 : ℝ) < (k + N + 1 : ℕ) := by
        exact_mod_cast (show 0 < k + N + 1 by omega)
      have hstep : 1 / ((k + N + 1 : ℕ) : ℝ) ^ (2 : ℕ) ≤
          1 / ((k + N : ℕ) : ℝ) - 1 / ((k + N + 1 : ℕ) : ℝ) := by
        have hkey : 1 / ((k + N : ℕ) : ℝ) -
            1 / ((k + N + 1 : ℕ) : ℝ) =
            1 / (((k + N : ℕ) : ℝ) * ((k + N + 1 : ℕ) : ℝ)) := by
          have hcast : ((k + N + 1 : ℕ) : ℝ) = ((k + N : ℕ) : ℝ) + 1 := by
            push_cast
            ring
          rw [hcast]
          field_simp
          ring
        rw [hkey, div_le_div_iff₀ (by positivity) (by positivity)]
        have hcast : ((k + N + 1 : ℕ) : ℝ) = ((k + N : ℕ) : ℝ) + 1 := by
          push_cast
          ring
        rw [hcast]
        nlinarith [hval, hval1]
      have hcast : ((k + (N + 1) : ℕ) : ℝ) = ((k + N + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      rw [hcast]
      linarith [ih, hstep]

/-- Every finite inverse-square tail beyond `k` is at most `1/k`. -/
theorem routeE_invSqTail_Ioo_le (k q : ℕ) (hk : 1 ≤ k) :
    (∑ d ∈ Finset.Ioo k q, 1 / (d : ℝ) ^ (2 : ℕ)) ≤ 1 / (k : ℝ) := by
  by_cases hq : k + 1 ≤ q
  · have heq : q = k + (q - k - 1) + 1 := by omega
    rw [heq]
    have h := routeE_invSqTail_Ioo_strong k (q - k - 1) hk
    have hnonneg : 0 ≤ 1 / ((k + (q - k - 1) : ℕ) : ℝ) := by positivity
    linarith
  · have hset : Finset.Ioo k q = ∅ := by
      ext d
      simp [Finset.mem_Ioo]; omega
    rw [hset]
    simp

def routeE_momentTerm (s : ℝ) (a d : ℕ) : ℝ :=
  if Nat.Coprime a d then
    (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-s)
  else 0

/-- Signed, coprime-restricted Möbius moment of denominator cofactors. -/
def routeE_coprimeMobiusMoment (s : ℝ) (a q : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ioo 0 q, routeE_momentTerm s a d

theorem routeE_momentTerm_one (s : ℝ) (a : ℕ) :
    routeE_momentTerm s a 1 = 1 := by
  simp [routeE_momentTerm]

theorem routeE_momentTerm_prime_nonpos
    (s : ℝ) (a d : ℕ) (hd : d.Prime) :
    routeE_momentTerm s a d ≤ 0 := by
  by_cases hcop : Nat.Coprime a d
  · unfold routeE_momentTerm
    rw [if_pos hcop, ArithmeticFunction.moebius_apply_prime hd]
    norm_num
    exact Real.rpow_nonneg (Nat.cast_nonneg d) _
  · simp [routeE_momentTerm, hcop]

theorem routeE_momentTerm_four (s : ℝ) (a : ℕ) :
    routeE_momentTerm s a 4 = 0 := by
  have hmu4 : ArithmeticFunction.moebius 4 = 0 := by
    simpa using ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two
      (by omega : 2 ≠ 0)
  simp [routeE_momentTerm, hmu4]

theorem routeE_momentTerm_abs_le_invSq
    {s : ℝ} (hs : 2 ≤ s) (a : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    |routeE_momentTerm s a d| ≤ 1 / (d : ℝ) ^ (2 : ℕ) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  have hpow : (d : ℝ) ^ (-s) ≤ (d : ℝ) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
  have hpow0 : 0 ≤ (d : ℝ) ^ (-s) := Real.rpow_nonneg hd0 _
  by_cases hcop : Nat.Coprime a d
  · rw [routeE_momentTerm, if_pos hcop, abs_mul, abs_of_nonneg hpow0]
    calc
      _ ≤ 1 * (d : ℝ) ^ (-s) :=
        mul_le_mul_of_nonneg_right hmu hpow0
      _ ≤ (d : ℝ) ^ (-2 : ℝ) := by simpa using hpow
      _ = 1 / (d : ℝ) ^ (2 : ℕ) := by
        rw [Real.rpow_neg hd0, Real.rpow_ofNat]
        ring
  · simp [routeE_momentTerm, hcop]

/-- Universal upper bound; the first possible positive cofactor after `1`
is at least `6`. -/
theorem routeE_coprimeMobiusMoment_upper
    {s : ℝ} (hs : 2 ≤ s) (a q : ℕ) (hq : 6 ≤ q) :
    routeE_coprimeMobiusMoment s a q ≤ 6 / 5 := by
  have hset : Finset.Ioo 0 q =
      insert 1 (insert 2 (insert 3 (insert 4 (insert 5 (Finset.Ioo 5 q))))) := by
    ext d
    simp only [Finset.mem_Ioo, Finset.mem_insert]
    omega
  have hsplit : routeE_coprimeMobiusMoment s a q =
      routeE_momentTerm s a 1 + routeE_momentTerm s a 2 +
      routeE_momentTerm s a 3 + routeE_momentTerm s a 4 +
      routeE_momentTerm s a 5 +
      ∑ d ∈ Finset.Ioo 5 q, routeE_momentTerm s a d := by
    unfold routeE_coprimeMobiusMoment
    rw [hset]
    simp [Finset.mem_Ioo]
    ring
  have htail : (∑ d ∈ Finset.Ioo 5 q, routeE_momentTerm s a d) ≤
      1 / (5 : ℝ) := by
    calc
      _ ≤ ∑ d ∈ Finset.Ioo 5 q, 1 / (d : ℝ) ^ (2 : ℕ) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd1 : 1 ≤ d := by have := (Finset.mem_Ioo.mp hd).1; omega
        exact le_trans (le_abs_self _) (routeE_momentTerm_abs_le_invSq hs a hd1)
      _ ≤ 1 / (5 : ℝ) := routeE_invSqTail_Ioo_le 5 q (by omega)
  rw [hsplit, routeE_momentTerm_one, routeE_momentTerm_four]
  have h2 := routeE_momentTerm_prime_nonpos s a 2 Nat.prime_two
  have h3 := routeE_momentTerm_prime_nonpos s a 3 Nat.prime_three
  have h5 := routeE_momentTerm_prime_nonpos s a 5 Nat.prime_five
  linarith

/-- Composite numerators `2a` exclude even cofactors; the first remaining
negative cofactor is `3`. -/
theorem routeE_coprimeMobiusMoment_two_mul_lower
    {s : ℝ} (hs : 2 ≤ s) (a q : ℕ) (hq : 6 ≤ q) :
    23 / 36 ≤ routeE_coprimeMobiusMoment s (2 * a) q := by
  have hset : Finset.Ioo 0 q =
      insert 1 (insert 2 (insert 3 (insert 4 (Finset.Ioo 4 q)))) := by
    ext d
    simp only [Finset.mem_Ioo, Finset.mem_insert]
    omega
  have hsplit : routeE_coprimeMobiusMoment s (2 * a) q =
      routeE_momentTerm s (2 * a) 1 + routeE_momentTerm s (2 * a) 2 +
      routeE_momentTerm s (2 * a) 3 + routeE_momentTerm s (2 * a) 4 +
      ∑ d ∈ Finset.Ioo 4 q, routeE_momentTerm s (2 * a) d := by
    unfold routeE_coprimeMobiusMoment
    rw [hset]
    simp [Finset.mem_Ioo]
    ring
  have hcop2 : ¬Nat.Coprime (2 * a) 2 := by
    intro h
    exact Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 2)
      (by omega : 2 ∣ 2 * a) (by norm_num : 2 ∣ 2) h
  have hterm2 : routeE_momentTerm s (2 * a) 2 = 0 := by
    simp [routeE_momentTerm, hcop2]
  have hterm3 : -(1 / (9 : ℝ)) ≤ routeE_momentTerm s (2 * a) 3 := by
    have h := routeE_momentTerm_abs_le_invSq hs (2 * a) (d := 3) (by omega)
    norm_num at h
    linarith [(abs_le.mp h).1]
  have htail : -(1 / (4 : ℝ)) ≤
      ∑ d ∈ Finset.Ioo 4 q, routeE_momentTerm s (2 * a) d := by
    have hpoint : ∀ d ∈ Finset.Ioo 4 q,
        -(1 / (d : ℝ) ^ (2 : ℕ)) ≤ routeE_momentTerm s (2 * a) d := by
      intro d hd
      have hd1 : 1 ≤ d := by have := (Finset.mem_Ioo.mp hd).1; omega
      have h := routeE_momentTerm_abs_le_invSq hs (2 * a) hd1
      linarith [(abs_le.mp h).1]
    have hsum := Finset.sum_le_sum hpoint
    rw [Finset.sum_neg_distrib] at hsum
    have htailBound := routeE_invSqTail_Ioo_le 4 q (by omega)
    linarith
  rw [hsplit, routeE_momentTerm_one, hterm2, routeE_momentTerm_four]
  linarith

/-- First few literal cofactor signs force a uniform difference between the
prime and adjacent-composite linearized moments. -/
theorem routeE_coprimeMobiusMoment_payment
    {s : ℝ} (hs : 2 ≤ s) (p q : ℕ) (hq : 6 ≤ q) :
    routeE_coprimeMobiusMoment s p q -
      2 * routeE_coprimeMobiusMoment s (2 * p) q ≤ -(7 / 90 : ℝ) := by
  have h1 := routeE_coprimeMobiusMoment_upper hs p q hq
  have h2 := routeE_coprimeMobiusMoment_two_mul_lower hs p q hq
  linarith

end
end RHTower

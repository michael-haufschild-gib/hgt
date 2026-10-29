import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHaarPrimeSourceRetainsItsDivisorSquares

/-!
# Uniform arithmetic coercivity on all balanced complete cells

Choose one prime parent of each odd boundary. The resulting backward map
contracts exact Haar square mass because the odd inverse-square sum is at
most one quarter. Its edge differences belong to the original divisor
squares, including the charged root, and pay every signed coefficient.
-/

noncomputable section
open Finset

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open ArithmeticFunction

private theorem exists_prime_parent {b : ℕ} (hb : 1 ≤ b) :
    ∃ p a : ℕ, p.Prime ∧ a < b ∧ (2 * a + 1) * p = 2 * b + 1 := by
  obtain ⟨p, hp, k, hk⟩ := Nat.exists_prime_and_dvd (by omega : 2 * b + 1 ≠ 1)
  have hodd : Odd k := (show Odd (2 * b + 1) from ⟨b, by omega⟩).of_dvd_nat
    ⟨p, by simpa only [Nat.mul_comm] using hk⟩
  obtain ⟨a, ha⟩ := hodd
  have he : (2 * a + 1) * p = 2 * b + 1 := by rw [hk, ha]; ring
  have h := Nat.mul_le_mul_left (2 * a + 1) hp.two_le
  rw [he] at h
  exact ⟨p, a, hp, by omega, he⟩

private theorem exists_prime_parents : ∃ p a : ℕ → ℕ, ∀ b : ℕ, 1 ≤ b →
    (p b).Prime ∧ a b < b ∧ (2 * a b + 1) * p b = 2 * b + 1 := by
  classical
  have h (b : ℕ) : ∃ p a : ℕ, 1 ≤ b →
      p.Prime ∧ a < b ∧ (2 * a + 1) * p = 2 * b + 1 := by
    by_cases hb : 1 ≤ b
    · obtain ⟨p, a, hp, ha, he⟩ := exists_prime_parent hb
      exact ⟨p, a, fun _ => ⟨hp, ha, he⟩⟩
    · exact ⟨2, 0, fun h => False.elim (hb h)⟩
  choose p a hpa using h
  exact ⟨p, a, hpa⟩

private theorem sum_odd_inverse_square_le_quarter (X : ℕ) :
    (∑ k ∈ Icc 1 X, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2) ≤ 1 / 4 := by
  by_cases hX : X = 0
  · subst X
    simp only [Icc_eq_empty_of_lt (by omega : 0 < 1), sum_empty]
    norm_num
  have hX1 : 1 ≤ X := by omega
  have hterm (k : ℕ) (hk : k ∈ Icc 1 X) :
      1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2 ≤
        (1 / 4 : ℝ) * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
    have hk1 := (mem_Icc.mp hk).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hkR : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hden : 0 < ((2 * k + 1 : ℕ) : ℝ) ^ 2 := by positivity
    have he : (1 / 4 : ℝ) * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) =
        1 / (4 * (k : ℝ) * ((k : ℝ) + 1)) := by
      push_cast
      field_simp [hk0.ne', hkR.ne']
      ring
    rw [he]
    apply (div_le_div_iff₀ hden (by positivity)).mpr
    push_cast
    nlinarith only [sq_nonneg (2 * (k : ℝ) + 1)]
  calc
    _ ≤ ∑ k ∈ Icc 1 X, (1 / 4 : ℝ) * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) :=
      sum_le_sum hterm
    _ = (1 / 4 : ℝ) * (1 - 1 / ((X + 1 : ℕ) : ℝ)) := by
      rw [← mul_sum]
      have hs := Finset.sum_Icc_sub hX1 (fun k : ℕ => -(1 / (k : ℝ)))
      simp only [sub_neg_eq_add, neg_add_eq_sub, Nat.cast_one, div_one] at hs
      exact congrArg (fun x : ℝ => (1 / 4 : ℝ) * x) hs
    _ ≤ 1 / 4 := by
      have h := (show (0 : ℝ) ≤ 1 / ((X + 1 : ℕ) : ℝ) by positivity)
      linarith only [h]

/-- All odd arithmetic parents together contract the exact mass by at least one half. -/
private theorem all_odd_parent_mass_le (d : ℕ → ℝ) (X : ℕ) :
    (∑ b ∈ Icc 1 X, ∑ a ∈ Icc 1 X, ∑ k ∈ Icc 1 X,
      if (2 * a + 1) * (2 * k + 1) = 2 * b + 1 then
        haarMass b / ((2 * k + 1 : ℕ) : ℝ) * d a ^ 2 else 0) ≤
      (1 / 2 : ℝ) * ∑ a ∈ Icc 1 X, haarMass a * d a ^ 2 := by
  classical
  have hrow {a k : ℕ} (ha : 1 ≤ a) (hk : 1 ≤ k) :
      (∑ b ∈ Icc 1 X,
        if (2 * a + 1) * (2 * k + 1) = 2 * b + 1 then
          haarMass b / ((2 * k + 1 : ℕ) : ℝ) * d a ^ 2 else 0) ≤
        (2 * haarMass a * d a ^ 2) * (1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2) := by
    have hm0 : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
    by_cases h : ∃ b ∈ Icc 1 X, (2 * a + 1) * (2 * k + 1) = 2 * b + 1
    · obtain ⟨b, hb, he⟩ := h
      rw [sum_eq_single b, if_pos he]
      · have hmass := haarMass_mul_le ha (mem_Icc.mp hb).1 (by omega) he
        have h := mul_le_mul_of_nonneg_right hmass
          (div_nonneg (sq_nonneg (d a)) (sq_nonneg (((2 * k + 1 : ℕ) : ℝ))))
        calc
          _ = (((2 * k + 1 : ℕ) : ℝ) * haarMass b) *
              (d a ^ 2 / ((2 * k + 1 : ℕ) : ℝ) ^ 2) := by field_simp [hm0.ne']
          _ ≤ (2 * haarMass a) * (d a ^ 2 / ((2 * k + 1 : ℕ) : ℝ) ^ 2) := h
          _ = _ := by ring
      · intro j _hj hjb
        exact if_neg (fun hj => hjb (by omega))
      · exact fun hn => False.elim (hn hb)
    · rw [sum_eq_zero (fun b hb => if_neg (fun he => h ⟨b, hb, he⟩))]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (haarMass_pos ha).le)
        (sq_nonneg _)) (by positivity)
  calc
    _ = ∑ a ∈ Icc 1 X, ∑ k ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
        if (2 * a + 1) * (2 * k + 1) = 2 * b + 1 then
          haarMass b / ((2 * k + 1 : ℕ) : ℝ) * d a ^ 2 else 0 := by
      rw [sum_comm]
      exact sum_congr rfl fun _ _ => sum_comm
    _ ≤ ∑ a ∈ Icc 1 X, ∑ k ∈ Icc 1 X,
        (2 * haarMass a * d a ^ 2) * (1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2) :=
      sum_le_sum fun a ha => sum_le_sum fun k hk => hrow (mem_Icc.mp ha).1 (mem_Icc.mp hk).1
    _ ≤ (1 / 2 : ℝ) * ∑ a ∈ Icc 1 X, haarMass a * d a ^ 2 := by
      rw [mul_sum]
      apply sum_le_sum
      intro a ha
      rw [← mul_sum]
      have h := mul_le_mul_of_nonneg_left (sum_odd_inverse_square_le_quarter X)
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
          (haarMass_pos (mem_Icc.mp ha).1).le) (sq_nonneg (d a)))
      convert h using 1
      ring

private def primeParentValue (p a : ℕ → ℕ) (d : ℕ → ℝ) (b : ℕ) : ℝ :=
  if a b = 0 then 0 else d (a b) / Real.sqrt (p b)

private theorem primeParent_mass_le (p a : ℕ → ℕ) (d : ℕ → ℝ) (X : ℕ)
    (hpa : ∀ b ∈ Icc 1 X, (p b).Prime ∧ a b < b ∧
      (2 * a b + 1) * p b = 2 * b + 1) :
    (∑ b ∈ Icc 1 X, haarMass b * primeParentValue p a d b ^ 2) ≤
      (1 / 2 : ℝ) * ∑ b ∈ Icc 1 X, haarMass b * d b ^ 2 := by
  classical
  apply le_trans ?_ (all_odd_parent_mass_le d X)
  apply sum_le_sum
  intro b hb
  have hb1 := (mem_Icc.mp hb).1
  have hbX := (mem_Icc.mp hb).2
  have hM := (haarMass_pos hb1).le
  have hnn (j k : ℕ) : 0 ≤ (if (2 * j + 1) * (2 * k + 1) = 2 * b + 1 then
      haarMass b / ((2 * k + 1 : ℕ) : ℝ) * d j ^ 2 else 0) := by
    split_ifs
    · exact mul_nonneg (div_nonneg hM (Nat.cast_nonneg _)) (sq_nonneg _)
    · exact le_rfl
  by_cases haz : a b = 0
  · rw [primeParentValue, if_pos haz, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    exact sum_nonneg fun j _ => sum_nonneg fun k _ => hnn j k
  · obtain ⟨hp, hab, he⟩ := hpa b hb
    have haj : a b ∈ Icc 1 X := mem_Icc.mpr ⟨by omega, by omega⟩
    have hodd : Odd (p b) := (show Odd (2 * b + 1) from ⟨b, by omega⟩).of_dvd_nat
      ⟨2 * a b + 1, by simpa only [Nat.mul_comm] using he.symm⟩
    obtain ⟨k, hk⟩ := hodd
    have hpk : p b = 2 * k + 1 := by omega
    have hp2 := hp.two_le
    have hpl := Nat.mul_le_mul_right (p b) (show 1 ≤ 2 * a b + 1 by omega)
    rw [Nat.one_mul, he] at hpl
    have hkI : k ∈ Icc 1 X := mem_Icc.mpr ⟨by omega, by omega⟩
    have hed : (2 * a b + 1) * (2 * k + 1) = 2 * b + 1 := by rwa [← hpk]
    have hinner := Finset.single_le_sum (fun k _ => hnn (a b) k) hkI
    have houter := Finset.single_le_sum
      (fun j _ => sum_nonneg (s := Icc 1 X) fun k _ => hnn j k) haj
    have hbound := hinner.trans houter
    rw [if_pos hed] at hbound
    rw [primeParentValue, if_neg haz, div_pow, Real.sq_sqrt (Nat.cast_nonneg _), hpk]
    convert hbound using 1
    ring

private def incomingDivisorSquares (d : ℕ → ℝ) (X b : ℕ) : ℝ :=
  ∑ m ∈ Icc 2 (2 * X + 1), ∑ j ∈ Icc 1 X,
    if (2 * j + 1) * m = 2 * b + 1 then
      vonMangoldt m * haarMass b * (d j / Real.sqrt m - d b) ^ 2 else 0

private theorem haarPrimeLogDefect_eq_sum_incoming (d : ℕ → ℝ) (X : ℕ) :
    haarPrimeLogDefect d X = ∑ b ∈ Icc 1 X,
      (vonMangoldt (2 * b + 1) * haarMass b * d b ^ 2 + incomingDivisorSquares d X b) := by
  rw [haarPrimeLogDefect_eq, sum_add_distrib, add_comm]
  congr 1
  unfold haarPrimeDivisorSquares incomingDivisorSquares
  calc
    _ = ∑ m ∈ Icc 2 (2 * X + 1), ∑ b ∈ Icc 1 X, ∑ j ∈ Icc 1 X,
        if (2 * j + 1) * m = 2 * b + 1 then
          vonMangoldt m * haarMass b * (d j / Real.sqrt m - d b) ^ 2 else 0 :=
      sum_congr rfl fun _ _ => sum_comm
    _ = _ := sum_comm

private theorem primeParent_difference_paid (p a : ℕ → ℕ) (d : ℕ → ℝ) (X : ℕ)
    (hpa : ∀ b ∈ Icc 1 X, (p b).Prime ∧ a b < b ∧
      (2 * a b + 1) * p b = 2 * b + 1) :
    Real.log 2 * (∑ b ∈ Icc 1 X, haarMass b * (d b - primeParentValue p a d b) ^ 2) ≤
      haarPrimeLogDefect d X := by
  rw [haarPrimeLogDefect_eq_sum_incoming, mul_sum]
  apply sum_le_sum
  intro b hb
  have hb1 := (mem_Icc.mp hb).1
  have hbX := (mem_Icc.mp hb).2
  obtain ⟨hp, hab, he⟩ := hpa b hb
  have hM := (haarMass_pos hb1).le
  have hlog : Real.log 2 ≤ vonMangoldt (p b) := by
    rw [vonMangoldt_apply_prime hp]
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
  have hnn (m j : ℕ) : 0 ≤ (if (2 * j + 1) * m = 2 * b + 1 then
      vonMangoldt m * haarMass b * (d j / Real.sqrt m - d b) ^ 2 else 0) := by
    split_ifs
    · exact mul_nonneg (mul_nonneg vonMangoldt_nonneg hM) (sq_nonneg _)
    · exact le_rfl
  have hQ : 0 ≤ incomingDivisorSquares d X b :=
    sum_nonneg fun m _ => sum_nonneg fun j _ => hnn m j
  have hroot : 0 ≤ vonMangoldt (2 * b + 1) * haarMass b * d b ^ 2 :=
    mul_nonneg (mul_nonneg vonMangoldt_nonneg hM) (sq_nonneg _)
  by_cases haz : a b = 0
  · have hpEq : p b = 2 * b + 1 := by simpa only [haz, mul_zero, zero_add, one_mul] using he
    rw [primeParentValue, if_pos haz, sub_zero]
    rw [hpEq] at hlog
    have h := mul_le_mul_of_nonneg_right hlog (mul_nonneg hM (sq_nonneg (d b)))
    nlinarith only [h, hQ]
  · have haj : a b ∈ Icc 1 X := mem_Icc.mpr ⟨by omega, by omega⟩
    have hpl := Nat.mul_le_mul_right (p b) (show 1 ≤ 2 * a b + 1 by omega)
    rw [Nat.one_mul, he] at hpl
    have hpI : p b ∈ Icc 2 (2 * X + 1) := mem_Icc.mpr ⟨hp.two_le, by omega⟩
    have hinner := Finset.single_le_sum (fun j _ => hnn (p b) j) haj
    have houter := Finset.single_le_sum
      (fun m _ => sum_nonneg (s := Icc 1 X) fun j _ => hnn m j) hpI
    have hbound : vonMangoldt (p b) * haarMass b *
        (d (a b) / Real.sqrt (p b) - d b) ^ 2 ≤ incomingDivisorSquares d X b := by
      simpa only [if_pos he, incomingDivisorSquares] using hinner.trans houter
    have h := mul_le_mul_of_nonneg_right hlog
      (mul_nonneg hM (sq_nonneg (d (a b) / Real.sqrt (p b) - d b)))
    rw [primeParentValue, if_neg haz]
    nlinarith only [h, hbound, hroot]

/-- The actual logarithmic prime defect has a uniform mass floor on every signed Haar
vector, including all low-index coordinates and every original prime-power edge. -/
theorem haarPrimeLogDefect_ge_mass (d : ℕ → ℝ) (X : ℕ) :
    (Real.log 2 / 12) * (∑ b ∈ Icc 1 X, haarMass b * d b ^ 2) ≤
      haarPrimeLogDefect d X := by
  obtain ⟨p, a, hpa⟩ := exists_prime_parents
  have hparents := fun b (hb : b ∈ Icc 1 X) => hpa b (mem_Icc.mp hb).1
  have hcontract := primeParent_mass_le p a d X hparents
  have hpay := primeParent_difference_paid p a d X hparents
  have hmass : (∑ b ∈ Icc 1 X, haarMass b * d b ^ 2) ≤
      3 * (∑ b ∈ Icc 1 X, haarMass b * (d b - primeParentValue p a d b) ^ 2) +
        (3 / 2 : ℝ) * ∑ b ∈ Icc 1 X, haarMass b * primeParentValue p a d b ^ 2 := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro b hb
    have h := mul_nonneg (haarMass_pos (mem_Icc.mp hb).1).le
      (sq_nonneg (2 * d b - 3 * primeParentValue p a d b))
    nlinarith only [h]
  have hE : (∑ b ∈ Icc 1 X, haarMass b * d b ^ 2) ≤
      12 * ∑ b ∈ Icc 1 X, haarMass b * (d b - primeParentValue p a d b) ^ 2 := by
    linarith only [hmass, hcontract]
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h := mul_le_mul_of_nonneg_left hE hl
  linarith only [h, hpay]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells

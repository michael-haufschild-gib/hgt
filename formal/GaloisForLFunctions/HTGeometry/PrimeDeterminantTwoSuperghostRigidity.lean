import Mathlib

/-!
# Prime-determinant two-superghost rigidity

A positive reciprocal pair of determinant `p²` at a prime is reconstructed from its first two
parity-odd power sums.  Integrality at those two levels already forces the neutral pair `(p, p)`;
the all-scale hypothesis is unnecessary.  Composite determinant and parity-even trace both admit
explicit non-neutral survivors.
-/

open scoped BigOperators
open Polynomial

namespace PrimeDeterminantTwoSuperghostRigidity

private lemma rat_eq_int_of_sq_eq_int (q : ℚ) (z : ℤ)
    (h : q ^ 2 = (z : ℚ)) : ∃ k : ℤ, q = (k : ℚ) := by
  have hzQ : IsSquare (z : ℚ) := ⟨q, by simpa [pow_two] using h.symm⟩
  have hzZ : IsSquare z := Rat.isSquare_intCast_iff.mp hzQ
  rcases hzZ with ⟨k, hk⟩
  have hsq : q ^ 2 = (k : ℚ) ^ 2 := by
    rw [h, hk]
    norm_num [pow_two]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hq | hq
  · exact ⟨k, hq⟩
  · exact ⟨-k, by simpa using hq⟩

/-- A prime-square reciprocal pair is neutral once its first two odd power sums are integral. -/
theorem eq_prime_of_primeDeterminant_twoSuperghosts
    (p : ℕ) (hp : p.Prime) (X Y : ℝ)
    (hY1 : 1 < Y) (hYX : Y ≤ X) (hXp2 : X < (p : ℝ) ^ 2)
    (hdet : X * Y = (p : ℝ) ^ 2)
    (hghostOne : ∃ m : ℤ, X - Y = (m : ℝ))
    (hghostTwo : ∃ n : ℤ, X ^ 2 - Y ^ 2 = (n : ℝ)) :
    X = (p : ℝ) ∧ Y = (p : ℝ) := by
  rcases hghostOne with ⟨m, hm⟩
  rcases hghostTwo with ⟨n, hn⟩
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  by_cases hm0 : m = 0
  · have hXY : X = Y := by
      have : X - Y = 0 := by simpa [hm0] using hm
      exact sub_eq_zero.mp this
    constructor <;> nlinarith [hdet]
  · have hmR0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
    have hmul : (m : ℝ) * (X + Y) = (n : ℝ) := by
      rw [← hm, ← hn]
      ring
    have hsumR : X + Y = (n : ℝ) / (m : ℝ) := by
      apply (eq_div_iff hmR0).2
      nlinarith [hmul]
    let q : ℚ := (n : ℚ) / (m : ℚ)
    have hqcast : (q : ℝ) = X + Y := by
      rw [hsumR]
      simp [q]
    let z : ℤ := m ^ 2 + 4 * (p : ℤ) ^ 2
    have hreal : (q : ℝ) ^ 2 = (z : ℝ) := by
      rw [hqcast]
      simp only [z]
      push_cast
      nlinarith [hdet, hm]
    have hrat : q ^ 2 = (z : ℚ) := by exact_mod_cast hreal
    rcases rat_eq_int_of_sq_eq_int q z hrat with ⟨k, hqk⟩
    have hsumK : X + Y = (k : ℝ) := by
      rw [← hqcast, hqk]
      norm_num
    have hkmR : (k : ℝ) ^ 2 - (m : ℝ) ^ 2 = 4 * (p : ℝ) ^ 2 := by
      nlinarith [hdet, hsumK, hm]
    have hkm : k ^ 2 - m ^ 2 = 4 * (p : ℤ) ^ 2 := by exact_mod_cast hkmR
    have hevenDiff : Even (k ^ 2 - m ^ 2) := by
      rw [hkm]
      exact ⟨2 * (p : ℤ) ^ 2, by ring⟩
    have hparity : Even k ↔ Even m := by
      have hsquares : Even (k ^ 2) ↔ Even (m ^ 2) := Int.even_sub.mp hevenDiff
      simpa [Int.even_pow] using hsquares
    have hevenSum : Even (k + m) := Int.even_add.mpr hparity
    have hevenSub : Even (k - m) := Int.even_sub.mpr hparity
    rcases even_iff_two_dvd.mp hevenSum with ⟨d, hd⟩
    rcases even_iff_two_dvd.mp hevenSub with ⟨e, he⟩
    have hdR : (k : ℝ) + (m : ℝ) = 2 * (d : ℝ) := by exact_mod_cast hd
    have heR : (k : ℝ) - (m : ℝ) = 2 * (e : ℝ) := by exact_mod_cast he
    have hXd : X = (d : ℝ) := by nlinarith [hsumK, hm]
    have hYe : Y = (e : ℝ) := by nlinarith [hsumK, hm]
    have hd0 : 0 ≤ d := by
      have : (0 : ℝ) ≤ (d : ℝ) := by rw [← hXd]; nlinarith [hY1, hYX]
      exact_mod_cast this
    have he0 : 0 ≤ e := by
      have : (0 : ℝ) ≤ (e : ℝ) := by rw [← hYe]; nlinarith [hY1]
      exact_mod_cast this
    obtain ⟨A, hA⟩ := Int.eq_ofNat_of_zero_le hd0
    obtain ⟨B, hB⟩ := Int.eq_ofNat_of_zero_le he0
    have hXA : X = (A : ℝ) := by rw [hXd, hA]; norm_num
    have hYB : Y = (B : ℝ) := by rw [hYe, hB]; norm_num
    have hAB : A * B = p ^ 2 := by
      rw [hXA, hYB] at hdet
      exact_mod_cast hdet
    have hAdiv : A ∣ p ^ 2 := ⟨B, hAB.symm⟩
    obtain ⟨j, hj, hAj⟩ := (Nat.dvd_prime_pow hp).mp hAdiv
    have hAone : 1 < A := by
      rw [hXA] at hYX
      have : (1 : ℝ) < (A : ℝ) := lt_of_lt_of_le hY1 hYX
      exact_mod_cast this
    have hAlt : A < p ^ 2 := by
      rw [hXA] at hXp2
      exact_mod_cast hXp2
    have hAeq : A = p := by
      interval_cases j
      · simp at hAj
        omega
      · simpa using hAj
      · have : A = p ^ 2 := by simpa using hAj
        omega
    have hBeq : B = p := by
      rw [hAeq] at hAB
      nlinarith [hp.pos]
    exact ⟨by simpa [hXA] using congrArg (fun t : ℕ => (t : ℝ)) hAeq,
      by simpa [hYB] using congrArg (fun t : ℕ => (t : ℝ)) hBeq⟩

/-- At one prime, integrality of the first two parity-odd conformal ghosts is exactly grade zero. -/
theorem primeConformal_twoSuperghosts_iff_grade_zero
    (p : ℕ) (hp : p.Prime) (b : ℝ) :
    (0 ≤ b ∧ b < 1 ∧
      (∃ m : ℤ, (p : ℝ) ^ (1 + b) - (p : ℝ) ^ (1 - b) = (m : ℝ)) ∧
      (∃ n : ℤ, ((p : ℝ) ^ (1 + b)) ^ 2 - ((p : ℝ) ^ (1 - b)) ^ 2 =
        (n : ℝ))) ↔ b = 0 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_trans (by norm_num) hp1
  constructor
  · rintro ⟨hb0, hb1, hghostOne, hghostTwo⟩
    let X : ℝ := (p : ℝ) ^ (1 + b)
    let Y : ℝ := (p : ℝ) ^ (1 - b)
    have hY1 : 1 < Y := by
      change 1 < (p : ℝ) ^ (1 - b)
      exact Real.one_lt_rpow hp1 (by linarith)
    have hYX : Y ≤ X := by
      change (p : ℝ) ^ (1 - b) ≤ (p : ℝ) ^ (1 + b)
      exact (Real.strictMono_rpow_of_base_gt_one hp1).monotone (by linarith)
    have hXp2 : X < (p : ℝ) ^ 2 := by
      have h := Real.rpow_lt_rpow_of_exponent_lt hp1
        (show 1 + b < (2 : ℝ) by linarith)
      change (p : ℝ) ^ (1 + b) < (p : ℝ) ^ 2
      calc
        (p : ℝ) ^ (1 + b) < (p : ℝ) ^ (2 : ℝ) := h
        _ = (p : ℝ) ^ 2 := Real.rpow_natCast (p : ℝ) 2
    have hdet : X * Y = (p : ℝ) ^ 2 := by
      calc
        X * Y = (p : ℝ) ^ ((1 + b) + (1 - b)) := by
          exact (Real.rpow_add hp0 (1 + b) (1 - b)).symm
        _ = (p : ℝ) ^ 2 := by norm_num [Real.rpow_natCast]
    have hrigid := eq_prime_of_primeDeterminant_twoSuperghosts p hp X Y
      hY1 hYX hXp2 hdet hghostOne hghostTwo
    have hexponents : 1 + b = 1 - b :=
      (Real.strictMono_rpow_of_base_gt_one hp1).injective
        (hrigid.1.trans hrigid.2.symm)
    linarith
  · rintro rfl
    refine ⟨le_rfl, by norm_num, ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;>
      norm_num [Real.rpow_one]

/-- Composite determinant allows a genuine non-neutral two-superghost packet. -/
theorem compositeSix_twoSuperghost_counterexample :
    (9 : ℝ) * 4 = 6 ^ 2 ∧ 1 < (4 : ℝ) ∧ 4 ≤ (9 : ℝ) ∧ 9 < (6 : ℝ) ^ 2 ∧
      (9 : ℝ) - 4 = (5 : ℤ) ∧ (9 : ℝ) ^ 2 - 4 ^ 2 = (65 : ℤ) ∧
      (9 : ℝ) ≠ 4 := by
  norm_num

noncomputable def evenTraceCounterX : ℝ := (7 + Real.sqrt 13) / 2

noncomputable def evenTraceCounterY : ℝ := (7 - Real.sqrt 13) / 2

def evenTraceCounterSeq : ℕ → ℤ
  | 0 => 2
  | 1 => 7
  | n + 2 => 7 * evenTraceCounterSeq (n + 1) - 9 * evenTraceCounterSeq n

lemma evenTraceCounter_sum : evenTraceCounterX + evenTraceCounterY = 7 := by
  simp [evenTraceCounterX, evenTraceCounterY]
  ring

lemma evenTraceCounter_product : evenTraceCounterX * evenTraceCounterY = 9 := by
  have hsqrt : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  dsimp [evenTraceCounterX, evenTraceCounterY]
  nlinarith

lemma evenTraceCounter_bounds :
    1 < evenTraceCounterY ∧ evenTraceCounterY < 3 ∧
      3 < evenTraceCounterX ∧ evenTraceCounterX < 9 := by
  have hsqrt : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have hsqrt0 : 0 ≤ Real.sqrt 13 := Real.sqrt_nonneg 13
  dsimp [evenTraceCounterX, evenTraceCounterY]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

lemma evenTraceCounter_ne : evenTraceCounterX ≠ evenTraceCounterY := by
  have hsqrt : 0 < Real.sqrt 13 := Real.sqrt_pos.2 (by norm_num)
  dsimp [evenTraceCounterX, evenTraceCounterY]
  nlinarith

/-- Every even trace of the non-neutral base-three packet is integral. -/
theorem evenTraceCounterSeq_cast (r : ℕ) :
    (evenTraceCounterSeq r : ℝ) = evenTraceCounterX ^ r + evenTraceCounterY ^ r := by
  induction r using Nat.twoStepInduction with
  | zero => norm_num [evenTraceCounterSeq]
  | one => simpa [evenTraceCounterSeq] using evenTraceCounter_sum.symm
  | more n h0 h1 =>
      rw [evenTraceCounterSeq]
      push_cast
      rw [h1, h0]
      rw [← evenTraceCounter_sum, ← evenTraceCounter_product]
      ring

/-- Closed sharpness packet: even traces do not force neutral grade. -/
theorem evenTrace_integrality_does_not_force_neutrality :
    evenTraceCounterX * evenTraceCounterY = 3 ^ 2 ∧
      1 < evenTraceCounterY ∧ evenTraceCounterY < 3 ∧
      3 < evenTraceCounterX ∧ evenTraceCounterX < 3 ^ 2 ∧
      evenTraceCounterX ≠ evenTraceCounterY ∧
      ∀ r : ℕ, ∃ z : ℤ, evenTraceCounterX ^ r + evenTraceCounterY ^ r = (z : ℝ) := by
  refine ⟨by
      convert evenTraceCounter_product using 1
      norm_num,
    evenTraceCounter_bounds.1,
    evenTraceCounter_bounds.2.1, evenTraceCounter_bounds.2.2.1,
    by
      convert evenTraceCounter_bounds.2.2.2 using 1
      norm_num,
    evenTraceCounter_ne, ?_⟩
  intro r
  exact ⟨evenTraceCounterSeq r, (evenTraceCounterSeq_cast r).symm⟩

end PrimeDeterminantTwoSuperghostRigidity

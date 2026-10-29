import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellPrimeBound

/-!
# Divisor squares in the original Haar prime source

Multiplicative incidence between odd cell boundaries admits a positive
square remainder with the exact proper-divisor potential. The absent
boundary one removes the full von Mangoldt value at the receiving index.
The outgoing charge retains the summable inverse-square prime weight.
-/

noncomputable section
open Finset

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open ArithmeticFunction

/-- Outgoing charge after rescaling a prime edge by its square-root multiplier. -/
def haarPrimeOutgoingCharge (X a : ℕ) : ℝ :=
  ∑ m ∈ Icc 2 (2 * X + 1), ∑ b ∈ Icc 1 X,
    if (2 * a + 1) * m = 2 * b + 1 then
      vonMangoldt m / (m : ℝ) * haarMass b else 0

/-- Positive edge squares of the literal Haar prime incidence graph. -/
def haarPrimeDivisorSquares (d : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑ m ∈ Icc 2 (2 * X + 1), ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
    if (2 * a + 1) * m = 2 * b + 1 then
      vonMangoldt m * haarMass b * (d a / Real.sqrt m - d b) ^ 2 else 0

theorem haarPrimeDivisorSquares_nonneg (d : ℕ → ℝ) (X : ℕ) :
    0 ≤ haarPrimeDivisorSquares d X := by
  apply sum_nonneg
  intro m _
  apply sum_nonneg
  intro a _
  apply sum_nonneg
  intro b hb
  split_ifs
  · exact mul_nonneg (mul_nonneg vonMangoldt_nonneg
      (haarMass_pos (mem_Icc.mp hb).1).le) (sq_nonneg _)
  · exact le_rfl

private theorem incoming_source_of_divisor {b m X : ℕ} (_hb : 1 ≤ b)
    (hbX : b ≤ X) (hm : 2 ≤ m) (hd : m ∣ 2 * b + 1) (hne : m ≠ 2 * b + 1) :
    ∃ a ∈ Icc 1 X, (2 * a + 1) * m = 2 * b + 1 := by
  obtain ⟨k, hk⟩ := hd
  have hk1 : k ≠ 1 := by
    intro h
    apply hne
    simpa only [h, Nat.mul_one] using hk.symm
  have hodd : Odd k := (show Odd (2 * b + 1) from ⟨b, by omega⟩).of_dvd_nat
    ⟨m, by simpa only [Nat.mul_comm] using hk⟩
  obtain ⟨a, ha⟩ := hodd
  have ha1 : 1 ≤ a := by omega
  have he : (2 * a + 1) * m = 2 * b + 1 := by
    rw [hk, ha]
    ring
  have hle := Nat.mul_le_mul_left (2 * a + 1) (show 1 ≤ m by omega)
  rw [Nat.mul_one, he] at hle
  exact ⟨a, mem_Icc.mpr ⟨ha1, by omega⟩, he⟩

private theorem incoming_multiplier_fiber {b m X : ℕ} (hb : 1 ≤ b)
    (hbX : b ≤ X) (hm : 2 ≤ m) :
    (∑ a ∈ Icc 1 X,
      if (2 * a + 1) * m = 2 * b + 1 then vonMangoldt m else 0) =
        if m ∣ 2 * b + 1 ∧ m ≠ 2 * b + 1 then vonMangoldt m else 0 := by
  classical
  by_cases hd : m ∣ 2 * b + 1 ∧ m ≠ 2 * b + 1
  · obtain ⟨a, ha, he⟩ := incoming_source_of_divisor hb hbX hm hd.1 hd.2
    rw [if_pos hd, sum_eq_single a, if_pos he]
    · intro j _hj hja
      apply if_neg
      intro hj
      have h := Nat.eq_of_mul_eq_mul_right (by omega : 0 < m) (hj.trans he.symm)
      exact hja (by omega)
    · exact fun hn => False.elim (hn ha)
  · rw [if_neg hd]
    apply sum_eq_zero
    intro a ha
    apply if_neg
    intro he
    apply hd
    refine ⟨⟨2 * a + 1, by simpa only [Nat.mul_comm] using he.symm⟩, ?_⟩
    have ha1 := (mem_Icc.mp ha).1
    have h := Nat.mul_le_mul_right m (show 3 ≤ 2 * a + 1 by omega)
    rw [he] at h
    omega

private theorem proper_divisor_vonMangoldt_sum {b X : ℕ} (hb : 1 ≤ b) (hbX : b ≤ X) :
    (∑ m ∈ Icc 2 (2 * X + 1),
      if m ∣ 2 * b + 1 ∧ m ≠ 2 * b + 1 then vonMangoldt m else 0) =
        Real.log ((2 * b + 1 : ℕ) : ℝ) - vonMangoldt (2 * b + 1) := by
  classical
  let D := (Icc 2 (2 * X + 1)).filter
    (fun m => m ∣ 2 * b + 1 ∧ m ≠ 2 * b + 1)
  have hsub : D ⊆ (2 * b + 1).divisors.erase (2 * b + 1) := by
    intro m hm
    have h := (mem_filter.mp hm).2
    exact mem_erase.mpr ⟨h.2, Nat.mem_divisors.mpr ⟨h.1, by omega⟩⟩
  have he : (∑ m ∈ D, vonMangoldt m) =
      ∑ m ∈ (2 * b + 1).divisors.erase (2 * b + 1), vonMangoldt m := by
    apply sum_subset hsub
    intro m hm hnot
    have hne := (mem_erase.mp hm).1
    have hd := (Nat.mem_divisors.mp (mem_erase.mp hm).2).1
    have hm0 := Nat.pos_of_dvd_of_pos hd (by omega : 0 < 2 * b + 1)
    obtain ⟨k, hk⟩ := hd
    have hk1 : 1 ≤ k := by
      by_contra h
      have hz : k = 0 := by omega
      rw [hz, Nat.mul_zero] at hk
      omega
    have hmn := Nat.mul_le_mul_left m hk1
    rw [Nat.mul_one, ← hk] at hmn
    have hm1 : m = 1 := by
      by_contra h
      apply hnot
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, ⟨⟨k, hk⟩, hne⟩⟩
    rw [hm1, vonMangoldt_apply_one]
  have hmem : 2 * b + 1 ∈ (2 * b + 1).divisors :=
    Nat.mem_divisors.mpr ⟨dvd_refl _, by omega⟩
  have hsum := sum_erase_add (2 * b + 1).divisors vonMangoldt hmem
  rw [vonMangoldt_sum] at hsum
  calc
    _ = ∑ m ∈ D, vonMangoldt m := by simp only [D, sum_filter]
    _ = _ := by rw [he]; linarith only [hsum]

/-- Every incoming prime edge is a proper divisor, and every proper divisor occurs once.
The absent odd boundary one removes its von Mangoldt value from the incoming potential. -/
theorem haarPrime_incoming_divisor_charge {b X : ℕ} (hb : 1 ≤ b) (hbX : b ≤ X) :
    (∑ m ∈ Icc 2 (2 * X + 1), ∑ a ∈ Icc 1 X,
      if (2 * a + 1) * m = 2 * b + 1 then vonMangoldt m else 0) =
        Real.log ((2 * b + 1 : ℕ) : ℝ) - vonMangoldt (2 * b + 1) := by
  rw [sum_congr rfl fun m hm => incoming_multiplier_fiber hb hbX (mem_Icc.mp hm).1]
  exact proper_divisor_vonMangoldt_sum hb hbX

/-- The signed prime form is its exact proper-divisor potential minus nonnegative edge
squares. Both the missing-root subtraction and the outgoing charge retain their original values. -/
theorem haarPrimeEnergy_add_divisorSquares (d : ℕ → ℝ) (X : ℕ) :
    haarPrimeEnergy d X + haarPrimeDivisorSquares d X =
      ∑ a ∈ Icc 1 X,
        ((Real.log ((2 * a + 1 : ℕ) : ℝ) - vonMangoldt (2 * a + 1)) * haarMass a +
          haarPrimeOutgoingCharge X a) * d a ^ 2 := by
  classical
  have hp : haarPrimeEnergy d X =
      ∑ m ∈ Icc 2 (2 * X + 1), ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
        if (2 * a + 1) * m = 2 * b + 1 then
          2 * vonMangoldt m / Real.sqrt m * haarMass b * d a * d b else 0 := by
    rw [haarPrimeEnergy_eq]
    apply sum_congr rfl
    intro m _
    rw [mul_sum]
    apply sum_congr rfl
    intro a _
    rw [mul_sum]
    apply sum_congr rfl
    intro b _
    split_ifs <;> ring
  have he : haarPrimeEnergy d X + haarPrimeDivisorSquares d X =
      (∑ m ∈ Icc 2 (2 * X + 1), ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
        if (2 * a + 1) * m = 2 * b + 1 then
          vonMangoldt m / (m : ℝ) * haarMass b * d a ^ 2 else 0) +
      ∑ m ∈ Icc 2 (2 * X + 1), ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
        if (2 * a + 1) * m = 2 * b + 1 then
          vonMangoldt m * haarMass b * d b ^ 2 else 0 := by
    rw [hp, haarPrimeDivisorSquares]
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro m _
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro a _
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro b _
    split_ifs
    · rw [sub_sq, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      ring
    · ring
  have hout : (∑ m ∈ Icc 2 (2 * X + 1), ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
      if (2 * a + 1) * m = 2 * b + 1 then
        vonMangoldt m / (m : ℝ) * haarMass b * d a ^ 2 else 0) =
      ∑ a ∈ Icc 1 X, haarPrimeOutgoingCharge X a * d a ^ 2 := by
    rw [sum_comm]
    simp only [haarPrimeOutgoingCharge, sum_mul, ite_mul, zero_mul]
  have hin : (∑ m ∈ Icc 2 (2 * X + 1), ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
      if (2 * a + 1) * m = 2 * b + 1 then
        vonMangoldt m * haarMass b * d b ^ 2 else 0) =
      ∑ b ∈ Icc 1 X,
        (Real.log ((2 * b + 1 : ℕ) : ℝ) - vonMangoldt (2 * b + 1)) * haarMass b * d b ^ 2 := by
    calc
      _ = ∑ m ∈ Icc 2 (2 * X + 1), ∑ b ∈ Icc 1 X, ∑ a ∈ Icc 1 X,
          if (2 * a + 1) * m = 2 * b + 1 then
            vonMangoldt m * haarMass b * d b ^ 2 else 0 :=
        sum_congr rfl fun _ _ => sum_comm
      _ = ∑ b ∈ Icc 1 X, ∑ m ∈ Icc 2 (2 * X + 1), ∑ a ∈ Icc 1 X,
          if (2 * a + 1) * m = 2 * b + 1 then
            vonMangoldt m * haarMass b * d b ^ 2 else 0 := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro b hb
        rw [← haarPrime_incoming_divisor_charge (mem_Icc.mp hb).1 (mem_Icc.mp hb).2]
        simp only [sum_mul, ite_mul, zero_mul]
  rw [he, hout, hin, ← sum_add_distrib]
  apply sum_congr rfl
  intro a _
  ring

/-- The actual proper-divisor potential pays every signed Haar prime vector, with the
positive square reserve displayed in the exact identity above. -/
theorem haarPrimeEnergy_le_divisor_potential (d : ℕ → ℝ) (X : ℕ) :
    haarPrimeEnergy d X ≤ ∑ a ∈ Icc 1 X,
      ((Real.log ((2 * a + 1 : ℕ) : ℝ) - vonMangoldt (2 * a + 1)) * haarMass a +
        haarPrimeOutgoingCharge X a) * d a ^ 2 := by
  rw [← haarPrimeEnergy_add_divisorSquares]
  exact le_add_of_nonneg_right (haarPrimeDivisorSquares_nonneg d X)

/-- The logarithmic prime defect, including its actual outgoing inverse-square charge. -/
def haarPrimeLogDefect (d : ℕ → ℝ) (X : ℕ) : ℝ :=
  (∑ a ∈ Icc 1 X,
    (Real.log ((2 * a + 1 : ℕ) : ℝ) * haarMass a + haarPrimeOutgoingCharge X a) * d a ^ 2) -
      haarPrimeEnergy d X

/-- The logarithmic defect retains the squares and the charges of the missing odd root. -/
theorem haarPrimeLogDefect_eq (d : ℕ → ℝ) (X : ℕ) :
    haarPrimeLogDefect d X = haarPrimeDivisorSquares d X +
      ∑ a ∈ Icc 1 X, vonMangoldt (2 * a + 1) * haarMass a * d a ^ 2 := by
  have he := haarPrimeEnergy_add_divisorSquares d X
  have hs : (∑ a ∈ Icc 1 X,
      (Real.log ((2 * a + 1 : ℕ) : ℝ) * haarMass a + haarPrimeOutgoingCharge X a) * d a ^ 2) =
      (∑ a ∈ Icc 1 X,
        ((Real.log ((2 * a + 1 : ℕ) : ℝ) - vonMangoldt (2 * a + 1)) * haarMass a +
          haarPrimeOutgoingCharge X a) * d a ^ 2) +
        ∑ a ∈ Icc 1 X, vonMangoldt (2 * a + 1) * haarMass a * d a ^ 2 := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun _ _ => by ring
  unfold haarPrimeLogDefect
  rw [hs, ← he]
  ring

theorem haarPrimeLogDefect_nonneg (d : ℕ → ℝ) (X : ℕ) :
    0 ≤ haarPrimeLogDefect d X := by
  rw [haarPrimeLogDefect_eq]
  exact add_nonneg (haarPrimeDivisorSquares_nonneg d X)
    (sum_nonneg fun a ha => mul_nonneg (mul_nonneg vonMangoldt_nonneg
      (haarMass_pos (mem_Icc.mp ha).1).le) (sq_nonneg _))

/-- Vanishing of the exact square reserve means alignment on every positive prime edge. -/
theorem haarPrimeDivisorSquares_eq_zero_iff (d : ℕ → ℝ) (X : ℕ) :
    haarPrimeDivisorSquares d X = 0 ↔
      ∀ m ∈ Icc 2 (2 * X + 1), ∀ a ∈ Icc 1 X, ∀ b ∈ Icc 1 X,
        (2 * a + 1) * m = 2 * b + 1 → 0 < vonMangoldt m →
          d a / Real.sqrt m = d b := by
  have hn (m a : ℕ) (b : ℕ) (hb : b ∈ Icc 1 X) :
      0 ≤ (if (2 * a + 1) * m = 2 * b + 1 then
        vonMangoldt m * haarMass b * (d a / Real.sqrt m - d b) ^ 2 else 0) := by
    split_ifs
    · exact mul_nonneg (mul_nonneg vonMangoldt_nonneg
        (haarMass_pos (mem_Icc.mp hb).1).le) (sq_nonneg _)
    · exact le_rfl
  unfold haarPrimeDivisorSquares
  rw [sum_eq_zero_iff_of_nonneg (fun m _ =>
    sum_nonneg fun a _ => sum_nonneg fun b hb => hn m a b hb)]
  constructor
  · intro hz m hm a ha b hb he hp
    have hmz := (sum_eq_zero_iff_of_nonneg
      (fun a _ => sum_nonneg fun b hb => hn m a b hb)).mp (hz m hm)
    have habz := (sum_eq_zero_iff_of_nonneg (fun b hb => hn m a b hb)).mp (hmz a ha) b hb
    rw [if_pos he] at habz
    have hcoef := mul_pos hp (haarMass_pos (mem_Icc.mp hb).1)
    have hs : (d a / Real.sqrt m - d b) ^ 2 = 0 :=
      (mul_eq_zero.mp habz).resolve_left hcoef.ne'
    nlinarith only [hs]
  · intro hz m hm
    apply sum_eq_zero
    intro a ha
    apply sum_eq_zero
    intro b hb
    by_cases he : (2 * a + 1) * m = 2 * b + 1
    · rw [if_pos he]
      by_cases hp : 0 < vonMangoldt m
      · rw [hz m hm a ha b hb he hp, sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
      · have hzero : vonMangoldt m = 0 := le_antisymm (le_of_not_gt hp) vonMangoldt_nonneg
        rw [hzero, zero_mul, zero_mul]
    · exact if_neg he

/-- Prime-factor descent connects every odd boundary to a charged prime boundary.
Consequently the logarithmic defect has no nonzero vector of zero energy. -/
theorem haarPrimeLogDefect_eq_zero_iff (d : ℕ → ℝ) (X : ℕ) :
    haarPrimeLogDefect d X = 0 ↔ ∀ a ∈ Icc 1 X, d a = 0 := by
  constructor
  · intro hzero
    have hroot : 0 ≤ ∑ a ∈ Icc 1 X, vonMangoldt (2 * a + 1) * haarMass a * d a ^ 2 :=
      sum_nonneg fun a ha => mul_nonneg (mul_nonneg vonMangoldt_nonneg
        (haarMass_pos (mem_Icc.mp ha).1).le) (sq_nonneg _)
    have he := haarPrimeLogDefect_eq d X
    have hq := haarPrimeDivisorSquares_nonneg d X
    have hqz : haarPrimeDivisorSquares d X = 0 := by linarith only [hzero, he, hroot, hq]
    have hrz : (∑ a ∈ Icc 1 X, vonMangoldt (2 * a + 1) * haarMass a * d a ^ 2) = 0 := by
      linarith only [hzero, he, hqz]
    have hcharge := (sum_eq_zero_iff_of_nonneg (fun a ha =>
      mul_nonneg (mul_nonneg vonMangoldt_nonneg
        (haarMass_pos (mem_Icc.mp ha).1).le) (sq_nonneg (d a)))).mp hrz
    have hedge := (haarPrimeDivisorSquares_eq_zero_iff d X).mp hqz
    intro b
    induction b using Nat.strong_induction_on with
    | h b ih =>
      intro hb
      have hb1 := (mem_Icc.mp hb).1
      have hbX := (mem_Icc.mp hb).2
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : 2 * b + 1 ≠ 1)
      have hΛ : 0 < vonMangoldt p := by
        rw [vonMangoldt_apply_prime hp]
        exact Real.log_pos (by exact_mod_cast hp.one_lt)
      by_cases heq : p = 2 * b + 1
      · have hΛb : 0 < vonMangoldt (2 * b + 1) := heq ▸ hΛ
        have hsq : d b ^ 2 = 0 := (mul_eq_zero.mp (hcharge b hb)).resolve_left
          (mul_pos hΛb (haarMass_pos hb1)).ne'
        nlinarith only [hsq]
      · obtain ⟨a, ha, hae⟩ := incoming_source_of_divisor hb1 hbX hp.two_le hpd heq
        have hstep := Nat.mul_le_mul_left (2 * a + 1) hp.two_le
        rw [hae] at hstep
        have hab : a < b := by omega
        have hpX : p ≤ 2 * X + 1 := by
          have hpos := (mem_Icc.mp ha).1
          have h := Nat.mul_le_mul_right p (show 1 ≤ 2 * a + 1 by omega)
          rw [Nat.one_mul, hae] at h
          omega
        have hz := hedge p (mem_Icc.mpr ⟨hp.two_le, hpX⟩) a ha b hb hae hΛ
        rw [ih a hab ha, zero_div] at hz
        exact hz.symm
  · intro hd
    rw [haarPrimeLogDefect_eq]
    have hq : haarPrimeDivisorSquares d X = 0 := by
      apply (haarPrimeDivisorSquares_eq_zero_iff d X).mpr
      intro m _ a ha b hb _ _
      rw [hd a ha, hd b hb, zero_div]
    rw [hq, zero_add]
    apply sum_eq_zero
    intro a ha
    rw [hd a ha, zero_pow (by norm_num : 2 ≠ 0), mul_zero]

/-- Every nonzero signed finite Haar vector has positive logarithmic prime defect,
without deleting any low arithmetic index. -/
theorem haarPrimeLogDefect_pos_iff (d : ℕ → ℝ) (X : ℕ) :
    0 < haarPrimeLogDefect d X ↔ ∃ a ∈ Icc 1 X, d a ≠ 0 := by
  constructor
  · intro hp
    by_contra hn
    have hz : ∀ a ∈ Icc 1 X, d a = 0 := by
      intro a ha
      by_contra h
      exact hn ⟨a, ha, h⟩
    have he := (haarPrimeLogDefect_eq_zero_iff d X).mpr hz
    linarith only [hp, he]
  · rintro ⟨a, ha, hne⟩
    have hn : haarPrimeLogDefect d X ≠ 0 := fun h =>
      hne ((haarPrimeLogDefect_eq_zero_iff d X).mp h a ha)
    exact lt_of_le_of_ne (haarPrimeLogDefect_nonneg d X) (Ne.symm hn)

/-- An outgoing edge has an inverse-square multiplier cost after the same rescaling. -/
theorem haarPrimeOutgoingCharge_le {a : ℕ} (ha : 1 ≤ a) (X : ℕ) :
    haarPrimeOutgoingCharge X a ≤
      2 * (∑ m ∈ Icc 2 (2 * X + 1), vonMangoldt m / (m : ℝ) ^ 2) * haarMass a := by
  unfold haarPrimeOutgoingCharge
  rw [mul_sum, sum_mul]
  apply sum_le_sum
  intro m hm
  have hm2 := (mem_Icc.mp hm).1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  by_cases h : ∃ b ∈ Icc 1 X, (2 * a + 1) * m = 2 * b + 1
  · obtain ⟨b, hb, he⟩ := h
    rw [sum_eq_single b, if_pos he]
    · have hmass := haarMass_mul_le ha (mem_Icc.mp hb).1 hm2 he
      have hs := mul_le_mul_of_nonneg_left hmass
        (div_nonneg (vonMangoldt_nonneg (n := m)) (sq_nonneg (m : ℝ)))
      convert hs using 1 <;> field_simp [hm0.ne']
    · intro j _hj hjb
      exact if_neg (fun hj => hjb (by omega))
    · exact fun hn => False.elim (hn hb)
  · have hz : (∑ b ∈ Icc 1 X,
        if (2 * a + 1) * m = 2 * b + 1 then
          vonMangoldt m / (m : ℝ) * haarMass b else 0) = 0 := by
      apply sum_eq_zero
      intro b hb
      exact if_neg (fun he => h ⟨b, hb, he⟩)
    rw [hz]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (div_nonneg vonMangoldt_nonneg (sq_nonneg _))) (haarMass_pos ha).le

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells

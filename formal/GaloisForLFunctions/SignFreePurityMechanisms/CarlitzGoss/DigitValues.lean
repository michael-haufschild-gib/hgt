import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitAllocations
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Values and residue contents of base-p digits

Reducing digit exponents modulo s preserves their value modulo `p^s−1`.
Thus a nonempty digit block has divisible content exactly when its integer
value is divisible by `p^s−1`. Canonical digit occurrences recover both
`Nat.ofDigits` and the residue-class digit content.

The inverse-content feasibility criterion therefore applies to partitions
of the actual base-p digits of every natural number.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss
variable {s : ℕ} [NeZero s] {α : Type*}

/-- Value of a finite collection of base-p digit occurrences. -/
def tokenValue (p : ℕ) (exponent : α → ℕ) (S : Finset α) : ℤ :=
  ∑ x ∈ S, (p : ℤ) ^ exponent x

/-- The weighted content of digit occurrences is the sum of their reduced exponent weights. -/
theorem cyclicWeighted_tokenContent (p : ℕ) (exponent : α → ℕ) (S : Finset α) :
    cyclicWeighted (p : ℤ) (tokenContent (fun x => (exponent x : ZMod s)) S) 0 =
      ∑ x ∈ S, (p : ℤ) ^ (exponent x : ZMod s).val := by
  unfold cyclicWeighted tokenContent
  simp only [zero_add, card_filter, Nat.cast_sum, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_eq_single (exponent x : ZMod s).val]
  · simp only [ZMod.natCast_zmod_val, ite_true, Nat.cast_one, mul_one]
  · intro k hk hk0
    have hne : (exponent x : ZMod s) ≠ (k : ZMod s) := by
      intro he
      have hh := congrArg ZMod.val he
      rw [ZMod.val_natCast_of_lt (mem_range.mp hk)] at hh
      exact hk0 hh.symm
    simp only [if_neg hne, Nat.cast_zero, mul_zero]
  · intro hnot
    exact (hnot (mem_range.mpr (ZMod.val_lt _))).elim

omit [NeZero s] in
/-- Reducing a digit exponent modulo s preserves its residue modulo `p^s−1`. -/
theorem pow_mod_period_dvd (p : ℕ) (hp : 2 ≤ p) (e : ℕ) :
    ((p : ℤ) ^ s - 1) ∣ (p : ℤ) ^ e - (p : ℤ) ^ (e % s) := by
  let D := p ^ s - 1
  have hps : 1 ≤ p ^ s := one_le_pow₀ (by omega)
  have hD : (D : ℤ) = (p : ℤ) ^ s - 1 := by
    dsimp only [D]
    rw [Nat.cast_sub hps, Nat.cast_pow, Nat.cast_one]
  have hpow : (p : ZMod D) ^ s = 1 := by
    have hz : ((p ^ s - 1 : ℕ) : ZMod D) = 0 := ZMod.natCast_self D
    rw [Nat.cast_sub hps, Nat.cast_pow, Nat.cast_one] at hz
    exact sub_eq_zero.mp hz
  have hper : (p : ZMod D) ^ e = (p : ZMod D) ^ (e % s) := by
    calc (p : ZMod D) ^ e = (p : ZMod D) ^ (e % s + s * (e / s)) :=
        congrArg (fun n => (p : ZMod D) ^ n) (Nat.mod_add_div e s).symm
      _ = _ := by rw [pow_add, pow_mul, hpow, one_pow, mul_one]
  rw [← hD, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_sub, Int.cast_pow, Int.cast_natCast, hper, sub_self]

theorem dvd_tokenValue_sub_weightedContent (p : ℕ) (hp : 2 ≤ p)
    (exponent : α → ℕ) (S : Finset α) :
    ((p : ℤ) ^ s - 1) ∣ tokenValue p exponent S -
      cyclicWeighted (p : ℤ) (tokenContent (fun x => (exponent x : ZMod s)) S) 0 := by
  rw [cyclicWeighted_tokenContent, tokenValue, ← sum_sub_distrib]
  apply dvd_sum
  intro x _
  simpa only [ZMod.val_natCast] using pow_mod_period_dvd (s := s) p hp (exponent x)

/-- Divisible digit content is exactly positive cardinality and divisibility of the actual value. -/
theorem divisibleContent_tokens_iff (p : ℕ) (hp : 2 ≤ p)
    (exponent : α → ℕ) (S : Finset α) :
    DivisibleContent p (tokenContent (fun x => (exponent x : ZMod s)) S) ↔
      S.Nonempty ∧ ((p : ℤ) ^ s - 1) ∣ tokenValue p exponent S := by
  rw [DivisibleContent, positive_tokenContent_iff]
  have hd := dvd_tokenValue_sub_weightedContent (s := s) p hp exponent S
  constructor
  · rintro ⟨hne, hc⟩
    exact ⟨hne, by simpa only [sub_add_cancel] using dvd_add hd hc⟩
  · rintro ⟨hne, hv⟩
    exact ⟨hne, by simpa only [sub_sub_cancel] using dvd_sub hv hd⟩

/-- Individual occurrences of the digits in a base-p expansion, with repeated digits distinguished. -/
abbrev DigitToken (L : List ℕ) := Σ k : Fin L.length, Fin (L.get k)

theorem ofDigits_eq_finSum (p : ℕ) (L : List ℕ) :
    Nat.ofDigits p L = ∑ k : Fin L.length, L.get k * p ^ k.val := by
  induction L with
  | nil => simp [Nat.ofDigits]
  | cons d L ih =>
    simp [Nat.ofDigits, Fin.sum_univ_succ, ih, pow_succ, mul_sum,
      mul_comm, mul_assoc]

omit [NeZero s] in
theorem digitContent_eq_finSum (L : List ℕ) (h : ZMod s) :
    digitContent L h = ∑ k : Fin L.length, if (k.val : ZMod s) = h then L.get k else 0 := by
  induction L generalizing h with
  | nil => simp [digitContent]
  | cons d L ih =>
    change digitContent (d :: L) h =
      ∑ k : Fin (L.length + 1), if (k.val : ZMod s) = h then (d :: L).get k else 0
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.cast_zero]
    change (if h = 0 then d else 0) + digitContent L (h - 1) =
      (if (0 : ZMod s) = h then d else 0) +
        ∑ k : Fin L.length, if ((k.val + 1 : ℕ) : ZMod s) = h then L.get k else 0
    rw [ih]
    apply congrArg₂ (fun a b : ℕ => a + b)
    · by_cases hh : h = 0 <;> simp only [hh, eq_comm, ite_true, ite_false]
    · refine sum_congr rfl fun k _ => ?_
      have he : (((k.val + 1 : ℕ) : ZMod s) = h) ↔ ((k.val : ZMod s) = h - 1) := by
        rw [Nat.cast_add, Nat.cast_one, eq_sub_iff_add_eq]
      simp only [he]

omit [NeZero s] in
theorem tokenContent_digitTokens (L : List ℕ) :
    tokenContent (fun t : DigitToken L => (t.1.val : ZMod s)) univ =
      fun h => (digitContent L h : ℤ) := by
  funext h
  simp only [tokenContent, card_filter, Fintype.sum_sigma]
  apply congrArg (fun n : ℕ => (n : ℤ))
  rw [digitContent_eq_finSum]
  refine sum_congr rfl fun k _ => ?_
  change (∑ _j : Fin (L.get k), if (k.val : ZMod s) = h then 1 else 0) =
    if (k.val : ZMod s) = h then L.get k else 0
  by_cases hk : (k.val : ZMod s) = h
  · simp only [if_pos hk, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  · simp only [if_neg hk, sum_const_zero]

theorem tokenValue_digitTokens (p : ℕ) (L : List ℕ) :
    tokenValue p (fun t : DigitToken L => t.1.val) univ = ((Nat.ofDigits p L : ℕ) : ℤ) := by
  simp only [tokenValue, Fintype.sum_sigma, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [ofDigits_eq_finSum]
  push_cast
  rfl

/-- Exact feasibility criterion for partitions of the actual base-p digits of N. -/
theorem digitTokenPrefix_iff (p k N : ℕ) (hp : 2 ≤ p) :
    TokenPrefix p (fun t : DigitToken (Nat.digits p N) => (t.1.val : ZMod s)) k univ ↔
      ∀ h : ZMod s, (k : ℚ) < inverseContent (p : ℚ)
        (fun j : ZMod s => (contentOf p N j : ℚ)) h := by
  rw [tokenPrefix_iff_inverseContent p k hp, tokenContent_digitTokens]
  simp only [contentOf, Int.cast_natCast]

omit [NeZero s] in
/-- A nonempty collection of positive digit powers has positive value. -/
theorem tokenValue_pos_iff (p : ℕ) (hp : 0 < p) (exponent : α → ℕ) (S : Finset α) :
    0 < tokenValue p exponent S ↔ S.Nonempty := by
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
  constructor
  · intro hv
    by_contra hn
    have he : S = ∅ := not_nonempty_iff_eq_empty.mp hn
    simp only [tokenValue, he, sum_empty, lt_self_iff_false] at hv
  · rintro ⟨x, hx⟩
    apply sum_pos' (fun y _ => (pow_pos hpZ (exponent y)).le)
    exact ⟨x, hx, pow_pos hpZ _⟩

omit [NeZero s] in
theorem tokenValue_subset (p : ℕ) (exponent : α → ℕ) {S T : Finset α} (hT : T ⊆ S) :
    tokenValue p exponent T ≤ tokenValue p exponent S := by
  exact sum_le_sum_of_subset_of_nonneg hT fun x _ _ => pow_nonneg (Nat.cast_nonneg p) _

omit [NeZero s] in
theorem tokenValue_sdiff [DecidableEq α] (p : ℕ) (exponent : α → ℕ)
    {S T : Finset α} (hT : T ⊆ S) :
    tokenValue p exponent (S \ T) + tokenValue p exponent T = tokenValue p exponent S :=
  sum_sdiff hT

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.digitTokenPrefix_iff
#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.divisibleContent_tokens_iff

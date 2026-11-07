import GaloisForLFunctions.goldbach.BalancedProductCollisions
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
open Finset
/-!
# Exact gcd classes in smooth-times-prime collision counts

Let the smooth rows and prime columns lie in `(X, 2X]`, with all row prime
factors at most `y` and every column prime above `y`. A shifted product
identity `m*p + h = m'*p'` forces both row gcds with `h` to equal `gcd m m'`.

For positive `h`, its actual collision count is therefore at most
`sum_{d | h} d * card(A_d(h))^2`, where `A_d(h)` is the exact smooth row
class `gcd(m,h) = d`. Each fixed-row fibre uses the integer interval bound.

A logarithmic window of width `delta` has integer product difference at
most `4*X^2*delta`. Summing these gcd-class costs and adding the exact
diagonal bounds the full ordered fine multiplicative energy.
-/

namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
open GaloisForLFunctions.Goldbach

/-- A prime above the smoothness cutoff is coprime to the smooth integer. -/
theorem smooth_coprime_large_prime {y m p : ℕ}
    (hm : m ∈ Nat.smoothNumbers (y + 1)) (hp : p.Prime) (hyp : y < p) :
    Nat.Coprime m p := by
  apply (hp.coprime_iff_not_dvd.mpr ?_).symm
  intro hd
  have hmem := Nat.mem_primeFactors.mpr ⟨hp, hd, Nat.ne_zero_of_mem_smoothNumbers hm⟩
  have hsmall := (Nat.mem_smoothNumbers_iff_primeFactors_subset.mp hm).2 hmem
  have hlt := (Nat.mem_primesBelow.mp hsmall).1
  omega

private theorem gcd_of_product_difference_left {m m' p p' h : ℕ}
    (hc : Nat.Coprime m p') (he : m * p + h = m' * p') :
    Nat.gcd m h = Nat.gcd m m' := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left m h)
    have hcop : Nat.Coprime (Nat.gcd m h) p' :=
      hc.coprime_dvd_left (Nat.gcd_dvd_left m h)
    apply hcop.dvd_of_dvd_mul_right
    rw [← he]
    exact dvd_add (dvd_mul_of_dvd_left (Nat.gcd_dvd_left m h) p) (Nat.gcd_dvd_right m h)
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left m m')
    have hleft := dvd_mul_of_dvd_left (Nat.gcd_dvd_left m m') p
    have hright := dvd_mul_of_dvd_left (Nat.gcd_dvd_right m m') p'
    rw [← he] at hright
    exact (Nat.dvd_add_right hleft).mp hright

/-- On a smooth-times-prime determinant fibre, both row gcds equal their common gcd. -/
theorem smooth_prime_determinant_gcd {y m m' p p' h : ℕ}
    (hm : m ∈ Nat.smoothNumbers (y + 1)) (hm' : m' ∈ Nat.smoothNumbers (y + 1))
    (hp : p.Prime) (hp' : p'.Prime) (hyp : y < p) (hyp' : y < p')
    (he : m * p + h = m' * p') :
    Nat.gcd m h = Nat.gcd m m' ∧ Nat.gcd m' h = Nat.gcd m m' := by
  refine ⟨gcd_of_product_difference_left (smooth_coprime_large_prime hm hp' hyp') he, ?_⟩
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd ?_ (Nat.gcd_dvd_left m' h)
    have hcop : Nat.Coprime (Nat.gcd m' h) p :=
      (smooth_coprime_large_prime hm' hp hyp).coprime_dvd_left (Nat.gcd_dvd_left m' h)
    apply hcop.dvd_of_dvd_mul_right
    have hright := dvd_mul_of_dvd_left (Nat.gcd_dvd_left m' h) p'
    rw [← he] at hright
    exact (Nat.dvd_add_left (Nat.gcd_dvd_right m' h)).mp hright
  · apply Nat.dvd_gcd (Nat.gcd_dvd_right m m')
    have hleft := dvd_mul_of_dvd_left (Nat.gcd_dvd_left m m') p
    have hright := dvd_mul_of_dvd_left (Nat.gcd_dvd_right m m') p'
    rw [← he] at hright
    exact (Nat.dvd_add_right hleft).mp hright

/-- Smooth rows in the balanced interval. -/
def smoothRows (X y : ℕ) : Finset (Fin X) :=
  univ.filter fun i => balancedIntervalValue i ∈ Nat.smoothNumbers (y + 1)

/-- Prime columns above the smoothness cutoff in the same interval. -/
def roughPrimeColumns (X y : ℕ) : Finset (Fin X) :=
  univ.filter fun i => (balancedIntervalValue i).Prime ∧ y < balancedIntervalValue i

/-- Actual prime-column pairs at a prescribed shifted product difference. -/
def smoothPrimeCollisionFiber {X : ℕ} (y : ℕ) (m₁ m₂ : Fin X) (h : ℕ) :
    Finset (Fin X × Fin X) :=
  (roughPrimeColumns X y ×ˢ roughPrimeColumns X y).filter fun p =>
    balancedIntervalValue m₁ * balancedIntervalValue p.1 + h =
      balancedIntervalValue m₂ * balancedIntervalValue p.2

/-- The actual smooth-times-prime incidence count at one difference. -/
def smoothPrimeCollisionCount (X y h : ℕ) : ℕ :=
  ∑ m₁ ∈ smoothRows X y, ∑ m₂ ∈ smoothRows X y,
    (smoothPrimeCollisionFiber y m₁ m₂ h).card

/-- Disjoint row classes selected by the exact gcd with the difference. -/
def smoothGcdRows (X y h d : ℕ) : Finset (Fin X) :=
  (smoothRows X y).filter fun m => Nat.gcd (balancedIntervalValue m) h = d

private theorem smoothPrimeCollisionFiber_subset {X : ℕ} (y : ℕ) (m₁ m₂ : Fin X) (h : ℕ) :
    smoothPrimeCollisionFiber y m₁ m₂ h ⊆ balancedProductCollisionFiber m₁ m₂ h := by
  intro p hp
  exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hp).2⟩

/-- The gcd class, rather than all multiples of a divisor, controls each actual collision row. -/
theorem smoothPrimeCollisionFiber_le_gcd_classes {X y h : ℕ} (hh : 0 < h)
    (m₁ m₂ : Fin X) (hm₁ : m₁ ∈ smoothRows X y) (hm₂ : m₂ ∈ smoothRows X y) :
    (smoothPrimeCollisionFiber y m₁ m₂ h).card ≤
      ∑ d ∈ h.divisors,
        if Nat.gcd (balancedIntervalValue m₁) h = d ∧
          Nat.gcd (balancedIntervalValue m₂) h = d then d else 0 := by
  by_cases hf : (smoothPrimeCollisionFiber y m₁ m₂ h).Nonempty
  · -- One collision fixes the divisor class for the whole row fibre.
    obtain ⟨p, hp⟩ := hf
    have hp' := mem_filter.mp hp
    have hp₁ := (mem_filter.mp (mem_product.mp hp'.1).1).2
    have hp₂ := (mem_filter.mp (mem_product.mp hp'.1).2).2
    have hg := smooth_prime_determinant_gcd (mem_filter.mp hm₁).2 (mem_filter.mp hm₂).2
      hp₁.1 hp₂.1 hp₁.2 hp₂.2 hp'.2
    have hd : Nat.gcd (balancedIntervalValue m₁) (balancedIntervalValue m₂) ∈ h.divisors := by
      apply Nat.mem_divisors.mpr
      exact ⟨hg.1 ▸ Nat.gcd_dvd_right (balancedIntervalValue m₁) h, hh.ne'⟩
    have hcard := (card_le_card (smoothPrimeCollisionFiber_subset y m₁ m₂ h)).trans
      (card_balancedProductCollisionFiber_le_gcd m₁ m₂ h)
    apply hcard.trans
    have hsingle := single_le_sum (fun d (_ : d ∈ h.divisors) =>
      Nat.zero_le (if Nat.gcd (balancedIntervalValue m₁) h = d ∧
        Nat.gcd (balancedIntervalValue m₂) h = d then d else 0)) hd
    simpa only [if_pos hg] using hsingle
  · rw [not_nonempty_iff_eq_empty.mp hf, card_empty]
    exact Nat.zero_le _

/-- A nonzero shifted-product census restricted to its disjoint smooth gcd classes. -/
theorem smoothPrimeCollisionCount_le_gcd_classes (X y : ℕ) {h : ℕ} (hh : 0 < h) :
    smoothPrimeCollisionCount X y h ≤
      ∑ d ∈ h.divisors, d * (smoothGcdRows X y h d).card ^ 2 := by
  have hdouble (d : ℕ) :
      (∑ m₁ ∈ smoothRows X y, ∑ m₂ ∈ smoothRows X y,
        if Nat.gcd (balancedIntervalValue m₁) h = d ∧
          Nat.gcd (balancedIntervalValue m₂) h = d then d else 0) =
        d * (smoothGcdRows X y h d).card ^ 2 := by
    have he (m₁ m₂ : Fin X) :
        (if Nat.gcd (balancedIntervalValue m₁) h = d ∧
          Nat.gcd (balancedIntervalValue m₂) h = d then d else 0) =
        if Nat.gcd (balancedIntervalValue m₁) h = d then
          (if Nat.gcd (balancedIntervalValue m₂) h = d then d else 0) else 0 := by
      by_cases h₁ : Nat.gcd (balancedIntervalValue m₁) h = d <;>
        by_cases h₂ : Nat.gcd (balancedIntervalValue m₂) h = d <;> simp only [h₁, h₂, and_self,
          and_true, and_false, if_true, if_false]
    simp_rw [he, sum_ite_irrel]
    simp only [sum_const_zero, ← sum_filter, sum_const, nsmul_eq_mul,
      Nat.cast_id, smoothGcdRows]
    ring
  calc
    _ ≤ ∑ m₁ ∈ smoothRows X y, ∑ m₂ ∈ smoothRows X y, ∑ d ∈ h.divisors,
        if Nat.gcd (balancedIntervalValue m₁) h = d ∧
          Nat.gcd (balancedIntervalValue m₂) h = d then d else 0 :=
      sum_le_sum fun m₁ hm₁ => sum_le_sum fun m₂ hm₂ =>
        smoothPrimeCollisionFiber_le_gcd_classes hh m₁ m₂ hm₁ hm₂
    _ = ∑ d ∈ h.divisors, ∑ m₁ ∈ smoothRows X y, ∑ m₂ ∈ smoothRows X y,
        if Nat.gcd (balancedIntervalValue m₁) h = d ∧
          Nat.gcd (balancedIntervalValue m₂) h = d then d else 0 := by
      simp_rw [sum_comm (s := smoothRows X y) (t := h.divisors)]
    _ = _ := sum_congr rfl fun d _ => hdouble d

/-- Prime-column pairs in a positive logarithmic window, with both smooth rows fixed. -/
def smoothPrimeUpperLogFiber {X : ℕ} (y : ℕ) (m₁ m₂ : Fin X) (δ : ℝ) :
    Finset (Fin X × Fin X) :=
  (roughPrimeColumns X y ×ˢ roughPrimeColumns X y).filter fun p =>
    balancedIntervalValue m₁ * balancedIntervalValue p.1 <
      balancedIntervalValue m₂ * balancedIntervalValue p.2 ∧
    Real.log (balancedIntervalValue m₂ * balancedIntervalValue p.2 : ℕ) -
      Real.log (balancedIntervalValue m₁ * balancedIntervalValue p.1 : ℕ) ≤ δ

/-- The positive orientation of the actual off-diagonal logarithmic collision count. -/
def smoothPrimeUpperLogCount (X y : ℕ) (δ : ℝ) : ℕ :=
  ∑ m₁ ∈ smoothRows X y, ∑ m₂ ∈ smoothRows X y,
    (smoothPrimeUpperLogFiber y m₁ m₂ δ).card

private theorem nat_gap_le_of_log_gap {a b : ℕ} (ha : 0 < a) (hab : a < b)
    {δ : ℝ} (hlog : Real.log (b : ℝ) - Real.log (a : ℝ) ≤ δ) :
    ((b - a : ℕ) : ℝ) ≤ (b : ℝ) * δ := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast ha.trans hab
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos hbR haR)
  rw [Real.log_div hbR.ne' haR.ne', inv_div] at hl
  have he : 1 - (a : ℝ) / b = ((b : ℝ) - a) / b := by field_simp
  rw [he] at hl
  have h := (div_le_iff₀ hbR).mp (hl.trans hlog)
  rw [Nat.cast_sub hab.le]
  simpa only [mul_comm] using h

private theorem balanced_product_le (X : ℕ) (m p : Fin X) :
    (balancedIntervalValue m * balancedIntervalValue p : ℕ) ≤ 4 * X ^ 2 := by
  have h := Nat.mul_le_mul (balancedIntervalValue_le m) (balancedIntervalValue_le p)
  calc
    _ ≤ (2 * X) * (2 * X) := h
    _ = _ := by ring

private theorem smoothPrimeUpperLogFiber_le_sum {X y H : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hH : 4 * (X : ℝ) ^ 2 * δ ≤ (H : ℝ)) (m₁ m₂ : Fin X) :
    (smoothPrimeUpperLogFiber y m₁ m₂ δ).card ≤
      ∑ h ∈ Icc 1 H, (smoothPrimeCollisionFiber y m₁ m₂ h).card := by
  have hsub : smoothPrimeUpperLogFiber y m₁ m₂ δ ⊆
      (Icc 1 H).biUnion (fun h => smoothPrimeCollisionFiber y m₁ m₂ h) := by
    intro p hp
    obtain ⟨hpCols, hlt, hlog⟩ := mem_filter.mp hp
    let a := balancedIntervalValue m₁ * balancedIntervalValue p.1
    let b := balancedIntervalValue m₂ * balancedIntervalValue p.2
    have ha : 0 < a := Nat.mul_pos (balancedIntervalValue_pos m₁) (balancedIntervalValue_pos p.1)
    have hb : (b : ℝ) ≤ 4 * (X : ℝ) ^ 2 := by exact_mod_cast balanced_product_le X m₂ p.2
    have hgap : ((b - a : ℕ) : ℝ) ≤ (H : ℝ) :=
      (nat_gap_le_of_log_gap ha hlt hlog).trans ((mul_le_mul_of_nonneg_right hb hδ).trans hH)
    have hNat : b - a ≤ H := by exact_mod_cast hgap
    apply mem_biUnion.mpr
    refine ⟨b - a, mem_Icc.mpr ⟨by omega, hNat⟩, mem_filter.mpr ⟨hpCols, ?_⟩⟩
    change a + (b - a) = b
    omega
  exact (card_le_card hsub).trans card_biUnion_le

/-- Fine logarithmic off-diagonal collisions retain the exact gcd classes of every integer difference. -/
theorem smoothPrimeUpperLogCount_le_gcd_classes (X y : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    smoothPrimeUpperLogCount X y δ ≤
      ∑ h ∈ Icc 1 ⌈4 * (X : ℝ) ^ 2 * δ⌉₊,
        ∑ d ∈ h.divisors, d * (smoothGcdRows X y h d).card ^ 2 := by
  let H := ⌈4 * (X : ℝ) ^ 2 * δ⌉₊
  have hH : 4 * (X : ℝ) ^ 2 * δ ≤ (H : ℝ) := Nat.le_ceil _
  calc
    _ ≤ ∑ m₁ ∈ smoothRows X y, ∑ m₂ ∈ smoothRows X y,
        ∑ h ∈ Icc 1 H, (smoothPrimeCollisionFiber y m₁ m₂ h).card :=
      sum_le_sum fun m₁ _ => sum_le_sum fun m₂ _ => smoothPrimeUpperLogFiber_le_sum hδ hH m₁ m₂
    _ = ∑ h ∈ Icc 1 H, smoothPrimeCollisionCount X y h := by
      simp only [smoothPrimeCollisionCount]
      simp_rw [sum_comm (s := smoothRows X y) (t := Icc 1 H)]
    _ ≤ _ := sum_le_sum fun h hh => smoothPrimeCollisionCount_le_gcd_classes X y (mem_Icc.mp hh).1

/-- Smooth rows and prime columns above the cutoff uniquely determine their product. -/
theorem smooth_prime_product_eq_iff {y m m' p p' : ℕ}
    (hm : m ∈ Nat.smoothNumbers (y + 1)) (hm' : m' ∈ Nat.smoothNumbers (y + 1))
    (hp : p.Prime) (hp' : p'.Prime) (hyp : y < p) (hyp' : y < p') :
    m * p = m' * p' ↔ m = m' ∧ p = p' := by
  constructor
  · intro he
    have hg := smooth_prime_determinant_gcd hm hm' hp hp' hyp hyp'
      (show m * p + 0 = m' * p' by simpa only [Nat.add_zero] using he)
    simp only [Nat.gcd_zero_right] at hg
    have hrow : m = m' := hg.1.trans hg.2.symm
    refine ⟨hrow, ?_⟩
    apply mul_left_cancel₀ (Nat.ne_zero_of_mem_smoothNumbers hm)
    simpa only [← hrow] using he
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The actual zero-difference fibre contains only identical rows and identical columns. -/
theorem smoothPrimeCollisionFiber_zero {X y : ℕ} (m₁ m₂ : Fin X)
    (hm₁ : m₁ ∈ smoothRows X y) (hm₂ : m₂ ∈ smoothRows X y) :
    (smoothPrimeCollisionFiber y m₁ m₂ 0).card =
      if m₁ = m₂ then (roughPrimeColumns X y).card else 0 := by
  have heq : smoothPrimeCollisionFiber y m₁ m₂ 0 =
      if m₁ = m₂ then (roughPrimeColumns X y).diag else ∅ := by
    ext p
    simp only [smoothPrimeCollisionFiber, mem_filter, mem_product, Nat.add_zero]
    by_cases hrow : m₁ = m₂
    · rw [if_pos hrow]
      simp only [mem_diag]
      constructor
      · rintro ⟨⟨hp₁, hp₂⟩, hmul⟩
        have hcol : p.1 = p.2 := by
          apply balancedIntervalValue_injective X
          apply mul_left_cancel₀ (Nat.ne_of_gt (balancedIntervalValue_pos m₁))
          simpa only [← hrow] using hmul
        exact ⟨hp₁, hcol⟩
      · rintro ⟨hp₁, hcol⟩
        refine ⟨⟨hp₁, hcol ▸ hp₁⟩, ?_⟩
        rw [hrow, hcol]
    · rw [if_neg hrow]
      simp only [notMem_empty, iff_false, not_and]
      rintro ⟨hp₁, hp₂⟩ hmul
      have hp₁' := (mem_filter.mp hp₁).2
      have hp₂' := (mem_filter.mp hp₂).2
      have hg := (smooth_prime_product_eq_iff (mem_filter.mp hm₁).2 (mem_filter.mp hm₂).2
        hp₁'.1 hp₂'.1 hp₁'.2 hp₂'.2).mp hmul
      exact hrow (balancedIntervalValue_injective X hg.1)
  rw [heq]
  split_ifs <;> simp only [diag_card, card_empty]

/-- The diagonal contribution is exactly the number of smooth-times-prime products. -/
theorem smoothPrimeCollisionCount_zero (X y : ℕ) :
    smoothPrimeCollisionCount X y 0 = (smoothRows X y).card * (roughPrimeColumns X y).card := by
  unfold smoothPrimeCollisionCount
  calc
    _ = ∑ m₁ ∈ smoothRows X y, ∑ m₂ ∈ smoothRows X y,
        if m₁ = m₂ then (roughPrimeColumns X y).card else 0 :=
      sum_congr rfl fun m₁ hm₁ => sum_congr rfl fun m₂ hm₂ =>
        smoothPrimeCollisionFiber_zero m₁ m₂ hm₁ hm₂
    _ = ∑ _m₁ ∈ smoothRows X y, (roughPrimeColumns X y).card := by
      apply sum_congr rfl
      intro m₁ hm₁
      simp only [sum_ite_eq, if_pos hm₁]
    _ = _ := by simp only [sum_const, nsmul_eq_mul, Nat.cast_id]

/-- All ordered logarithmic near-collisions of the actual smooth-times-prime products. -/
def smoothPrimeLogEnergy (X y : ℕ) (δ : ℝ) : ℕ :=
  ∑ m₁ ∈ smoothRows X y, ∑ m₂ ∈ smoothRows X y,
    ((roughPrimeColumns X y ×ˢ roughPrimeColumns X y).filter fun p =>
      |Real.log (balancedIntervalValue m₁ * balancedIntervalValue p.1 : ℕ) -
        Real.log (balancedIntervalValue m₂ * balancedIntervalValue p.2 : ℕ)| ≤ δ).card

private theorem log_close_indicator_split {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (if |Real.log (a : ℝ) - Real.log (b : ℝ)| ≤ δ then (1 : ℕ) else 0) =
      (if a = b then 1 else 0) +
      (if a < b ∧ Real.log (b : ℝ) - Real.log (a : ℝ) ≤ δ then 1 else 0) +
      (if b < a ∧ Real.log (a : ℝ) - Real.log (b : ℝ) ≤ δ then 1 else 0) := by
  rcases lt_trichotomy a b with hlt | heq | hgt
  · have hl := Real.log_lt_log (by exact_mod_cast ha : (0 : ℝ) < a)
      (by exact_mod_cast hlt : (a : ℝ) < b)
    rw [abs_of_neg (sub_neg.mpr hl), neg_sub]
    simp only [ne_of_lt hlt, hlt, not_lt_of_ge hlt.le, false_and, true_and,
      if_false, zero_add, add_zero]
  · subst b
    simp only [sub_self, abs_zero, hδ, if_true, lt_self_iff_false, false_and, if_false,
      add_zero]
  · have hl := Real.log_lt_log (by exact_mod_cast hb : (0 : ℝ) < b)
      (by exact_mod_cast hgt : (b : ℝ) < a)
    rw [abs_of_pos (sub_pos.mpr hl)]
    simp only [ne_of_gt hgt, hgt, not_lt_of_ge hgt.le, false_and, true_and,
      if_false, zero_add, add_zero]

private theorem reverse_upper_log_fiber_card {X : ℕ} (y : ℕ) (m₁ m₂ : Fin X) (δ : ℝ) :
    ((roughPrimeColumns X y ×ˢ roughPrimeColumns X y).filter fun p =>
      balancedIntervalValue m₂ * balancedIntervalValue p.2 <
        balancedIntervalValue m₁ * balancedIntervalValue p.1 ∧
      Real.log (balancedIntervalValue m₁ * balancedIntervalValue p.1 : ℕ) -
        Real.log (balancedIntervalValue m₂ * balancedIntervalValue p.2 : ℕ) ≤ δ).card =
      (smoothPrimeUpperLogFiber y m₂ m₁ δ).card := by
  apply card_bij (fun p _ => Prod.swap p)
  · intro p hp
    obtain ⟨hpCols, hlt, hlog⟩ := mem_filter.mp hp
    obtain ⟨hp₁, hp₂⟩ := mem_product.mp hpCols
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hp₂, hp₁⟩, hlt, hlog⟩
  · intro p _ q _ he
    exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
  · intro p hp
    obtain ⟨hpCols, hlt, hlog⟩ := mem_filter.mp hp
    obtain ⟨hp₁, hp₂⟩ := mem_product.mp hpCols
    exact ⟨Prod.swap p, mem_filter.mpr ⟨mem_product.mpr ⟨hp₂, hp₁⟩, hlt, hlog⟩, rfl⟩

private theorem log_fiber_card_split {X : ℕ} (y : ℕ) (m₁ m₂ : Fin X)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    ((roughPrimeColumns X y ×ˢ roughPrimeColumns X y).filter fun p =>
      |Real.log (balancedIntervalValue m₁ * balancedIntervalValue p.1 : ℕ) -
        Real.log (balancedIntervalValue m₂ * balancedIntervalValue p.2 : ℕ)| ≤ δ).card =
      (smoothPrimeCollisionFiber y m₁ m₂ 0).card +
      (smoothPrimeUpperLogFiber y m₁ m₂ δ).card +
      (smoothPrimeUpperLogFiber y m₂ m₁ δ).card := by
  rw [← reverse_upper_log_fiber_card y m₁ m₂ δ]
  simp only [smoothPrimeCollisionFiber, smoothPrimeUpperLogFiber, Nat.add_zero,
    card_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  exact log_close_indicator_split
    (Nat.mul_pos (balancedIntervalValue_pos m₁) (balancedIntervalValue_pos p.1))
    (Nat.mul_pos (balancedIntervalValue_pos m₂) (balancedIntervalValue_pos p.2)) hδ

/-- The exact diagonal and twice the positively oriented collisions exhaust the energy. -/
theorem smoothPrimeLogEnergy_eq_diagonal_add_twice (X y : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    smoothPrimeLogEnergy X y δ = (smoothRows X y).card * (roughPrimeColumns X y).card +
      2 * smoothPrimeUpperLogCount X y δ := by
  unfold smoothPrimeLogEnergy
  have hrev : (∑ m₁ ∈ smoothRows X y, ∑ m₂ ∈ smoothRows X y,
      (smoothPrimeUpperLogFiber y m₂ m₁ δ).card) = smoothPrimeUpperLogCount X y δ := by
    exact sum_comm
  simp_rw [log_fiber_card_split y _ _ hδ]
  simp_rw [sum_add_distrib]
  change smoothPrimeCollisionCount X y 0 + smoothPrimeUpperLogCount X y δ +
    (∑ m₁ ∈ smoothRows X y, ∑ m₂ ∈ smoothRows X y,
      (smoothPrimeUpperLogFiber y m₂ m₁ δ).card) = _
  rw [smoothPrimeCollisionCount_zero, hrev]
  ring

/-- A complete fine-energy bound with its exact diagonal and disjoint arithmetic gcd classes. -/
theorem smoothPrimeLogEnergy_le_gcd_classes (X y : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    smoothPrimeLogEnergy X y δ ≤ (smoothRows X y).card * (roughPrimeColumns X y).card +
      2 * ∑ h ∈ Icc 1 ⌈4 * (X : ℝ) ^ 2 * δ⌉₊,
        ∑ d ∈ h.divisors, d * (smoothGcdRows X y h d).card ^ 2 := by
  rw [smoothPrimeLogEnergy_eq_diagonal_add_twice X y hδ]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 2
    (smoothPrimeUpperLogCount_le_gcd_classes X y hδ)) _

/-- The fine-energy estimate at the height resolution `1/T`. -/
theorem smoothPrimeLogEnergy_le_at_height (X y : ℕ) {T : ℝ} (hT : 0 < T) :
    smoothPrimeLogEnergy X y (1 / T) ≤
      (smoothRows X y).card * (roughPrimeColumns X y).card +
      2 * ∑ h ∈ Icc 1 ⌈4 * (X : ℝ) ^ 2 / T⌉₊,
        ∑ d ∈ h.divisors, d * (smoothGcdRows X y h d).card ^ 2 := by
  simpa only [mul_one_div] using
    smoothPrimeLogEnergy_le_gcd_classes X y (div_nonneg zero_le_one hT.le)

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

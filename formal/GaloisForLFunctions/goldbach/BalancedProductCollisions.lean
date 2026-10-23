import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Balanced product collisions

A fixed pair of rows has one reduced congruence class of possible
columns. Its quotient label has fewer than gcd-many values. Nonzero
product differences therefore retain their exact divisor restriction.
-/

namespace GaloisForLFunctions.Goldbach

open Finset
open scoped BigOperators

noncomputable section
set_option autoImplicit false

/-- Coordinates of the actual interval `(X,2X]`. -/
def balancedIntervalValue {X : ℕ} (i : Fin X) : ℕ := X + i.val + 1

theorem balancedIntervalValue_pos {X : ℕ} (i : Fin X) :
    0 < balancedIntervalValue i := by
  unfold balancedIntervalValue
  omega

theorem balancedIntervalValue_gt {X : ℕ} (i : Fin X) :
    X < balancedIntervalValue i := by
  unfold balancedIntervalValue
  omega

theorem balancedIntervalValue_le {X : ℕ} (i : Fin X) :
    balancedIntervalValue i ≤ 2 * X := by
  have := i.is_lt
  unfold balancedIntervalValue
  omega

/-- Column pairs at a prescribed product difference, with both rows fixed. -/
def balancedProductCollisionFiber {X : ℕ} (m₁ m₂ : Fin X) (h : ℕ) :
    Finset (Fin X × Fin X) :=
  univ.filter fun p => balancedIntervalValue m₁ * balancedIntervalValue p.1 + h =
    balancedIntervalValue m₂ * balancedIntervalValue p.2

/-- Every collision fibre injects into its gcd-sized quotient labels. -/
theorem card_balancedProductCollisionFiber_le_gcd {X : ℕ}
    (m₁ m₂ : Fin X) (h : ℕ) :
    (balancedProductCollisionFiber m₁ m₂ h).card ≤
      Nat.gcd (balancedIntervalValue m₁) (balancedIntervalValue m₂) := by
  classical
  let a := balancedIntervalValue m₁
  let b := balancedIntervalValue m₂
  let g := Nat.gcd b a
  let d := b / g
  let F := {p : Fin X × Fin X // p ∈ balancedProductCollisionFiber m₁ m₂ h}
  have hb : 0 < b := balancedIntervalValue_pos m₂
  have hg : 0 < g := Nat.gcd_pos_of_pos_left a hb
  have hd : 0 < d := Nat.div_pos (Nat.gcd_le_left a hb) hg
  have hfac : g * d = b := Nat.mul_div_cancel' (Nat.gcd_dvd_left b a)
  let label : F → Fin g := fun p => ⟨p.val.1.val / d, by
    rw [Nat.div_lt_iff_lt_mul hd, hfac]
    exact lt_trans p.val.1.is_lt (balancedIntervalValue_gt m₂)⟩
  have hinj : Function.Injective label := by
    intro p p' he
    have hp : a * balancedIntervalValue p.val.1 + h = b * balancedIntervalValue p.val.2 :=
      (mem_filter.mp p.property).2
    have hp' : a * balancedIntervalValue p'.val.1 + h = b * balancedIntervalValue p'.val.2 :=
      (mem_filter.mp p'.property).2
    have hsum : Nat.ModEq b (a * balancedIntervalValue p.val.1 + h)
        (a * balancedIntervalValue p'.val.1 + h) := by
      rw [hp, hp']
      simp only [Nat.ModEq, Nat.mul_mod_right]
    have hmul := Nat.ModEq.add_right_cancel' h hsum
    have hrow := Nat.ModEq.cancel_left_div_gcd hb hmul
    have hmod : Nat.ModEq d p.val.1.val p'.val.1.val := by
      change Nat.ModEq d (X + p.val.1.val + 1) (X + p'.val.1.val + 1) at hrow
      exact Nat.ModEq.add_left_cancel' X (Nat.ModEq.add_right_cancel' 1 hrow)
    have hquot : p.val.1.val / d = p'.val.1.val / d := congrArg Fin.val he
    have hi : p.val.1.val = p'.val.1.val := by
      rw [← Nat.mod_add_div p.val.1.val d, ← Nat.mod_add_div p'.val.1.val d]
      rw [show p.val.1.val % d = p'.val.1.val % d from hmod, hquot]
    have hfirst : p.val.1 = p'.val.1 := Fin.ext hi
    have hcols : b * balancedIntervalValue p.val.2 = b * balancedIntervalValue p'.val.2 := by
      rw [← hp, ← hp', hfirst]
    have hj := mul_left_cancel₀ (Nat.ne_of_gt hb) hcols
    have hsecond : p.val.2 = p'.val.2 := by
      apply Fin.ext
      unfold balancedIntervalValue at hj
      omega
    exact Subtype.ext (Prod.ext hfirst hsecond)
  simpa only [F, Fintype.card_coe, Fintype.card_fin, g, Nat.gcd_comm] using
    Fintype.card_le_of_injective label hinj

/-- The gcd must divide the actual difference; no compatibility assumption is supplied. -/
theorem card_balancedProductCollisionFiber_le_gcd_gate {X : ℕ}
    (m₁ m₂ : Fin X) (h : ℕ) :
    (balancedProductCollisionFiber m₁ m₂ h).card ≤
      if Nat.gcd (balancedIntervalValue m₁) (balancedIntervalValue m₂) ∣ h then
        Nat.gcd (balancedIntervalValue m₁) (balancedIntervalValue m₂) else 0 := by
  classical
  split_ifs with hd
  · exact card_balancedProductCollisionFiber_le_gcd m₁ m₂ h
  · have hempty : balancedProductCollisionFiber m₁ m₂ h = ∅ := by
      ext p
      change _ ↔ False
      rw [iff_false]
      intro hp
      have he := (mem_filter.mp hp).2
      have hleft := dvd_mul_of_dvd_left
        (Nat.gcd_dvd_left (balancedIntervalValue m₁) (balancedIntervalValue m₂))
        (balancedIntervalValue p.1)
      have hright := dvd_mul_of_dvd_left
        (Nat.gcd_dvd_right (balancedIntervalValue m₁) (balancedIntervalValue m₂))
        (balancedIntervalValue p.2)
      rw [← he] at hright
      have hh := Nat.dvd_sub' hright hleft
      exact hd (by simpa only [Nat.add_sub_cancel_left] using hh)
    rw [hempty, card_empty]

/-- Number of ordered balanced product pairs separated by `h`. -/
def balancedProductCollisionCount (X h : ℕ) : ℕ :=
  ∑ m₁ : Fin X, ∑ m₂ : Fin X, (balancedProductCollisionFiber m₁ m₂ h).card

theorem balancedIntervalValue_injective (X : ℕ) :
    Function.Injective (balancedIntervalValue : Fin X → ℕ) := by
  intro i j hij
  apply Fin.ext
  unfold balancedIntervalValue at hij
  omega

/-- Actual row coordinates divisible by one integer. -/
def balancedMultipleRows (X g : ℕ) : Finset (Fin X) :=
  univ.filter fun i => g ∣ balancedIntervalValue i

theorem card_balancedMultipleRows_le_div (X g : ℕ) :
    (balancedMultipleRows X g).card ≤ 2 * X / g := by
  classical
  calc
    (balancedMultipleRows X g).card =
        ((balancedMultipleRows X g).image balancedIntervalValue).card :=
      (card_image_of_injective _ (balancedIntervalValue_injective X)).symm
    _ ≤ ((Ioc 0 (2 * X)).filter (g ∣ ·)).card := by
      apply card_le_card
      intro n hn
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hn
      exact mem_filter.mpr ⟨mem_Ioc.mpr
        ⟨balancedIntervalValue_pos i, balancedIntervalValue_le i⟩, (mem_filter.mp hi).2⟩
    _ = _ := by simp only [Nat.Ioc_filter_dvd_card_eq_div]

/-- The actual difference restricts the collision budget to its own divisors. -/
theorem balancedProductCollisionCount_le_divisorMass (X : ℕ) (h : ℕ+) :
    balancedProductCollisionCount X (h : ℕ) ≤
      ∑ g ∈ (h : ℕ).divisors, g * (balancedMultipleRows X g).card ^ 2 := by
  classical
  have hpoint (m₁ m₂ : Fin X) :
      (balancedProductCollisionFiber m₁ m₂ (h : ℕ)).card ≤
        ∑ g ∈ (h : ℕ).divisors,
          if g ∣ balancedIntervalValue m₁ ∧ g ∣ balancedIntervalValue m₂ then g else 0 := by
    apply (card_balancedProductCollisionFiber_le_gcd_gate m₁ m₂ (h : ℕ)).trans
    split_ifs with hd
    · have hm : Nat.gcd (balancedIntervalValue m₁) (balancedIntervalValue m₂) ∈
          (h : ℕ).divisors := Nat.mem_divisors.mpr ⟨hd, h.ne_zero⟩
      have hh := single_le_sum (fun g (_ : g ∈ (h : ℕ).divisors) =>
        Nat.zero_le (if g ∣ balancedIntervalValue m₁ ∧ g ∣ balancedIntervalValue m₂
          then g else 0)) hm
      have hboth : Nat.gcd (balancedIntervalValue m₁) (balancedIntervalValue m₂) ∣
          balancedIntervalValue m₁ ∧
          Nat.gcd (balancedIntervalValue m₁) (balancedIntervalValue m₂) ∣
            balancedIntervalValue m₂ := ⟨Nat.gcd_dvd_left _ _, Nat.gcd_dvd_right _ _⟩
      simpa only [if_pos hboth] using hh
    · exact Nat.zero_le _
  have hdouble (g : ℕ) :
      (∑ m₁ : Fin X, ∑ m₂ : Fin X,
        if g ∣ balancedIntervalValue m₁ ∧ g ∣ balancedIntervalValue m₂ then g else 0) =
          g * (balancedMultipleRows X g).card ^ 2 := by
    have he (m₁ m₂ : Fin X) :
        (if g ∣ balancedIntervalValue m₁ ∧ g ∣ balancedIntervalValue m₂ then g else 0) =
          if g ∣ balancedIntervalValue m₁ then
            (if g ∣ balancedIntervalValue m₂ then g else 0) else 0 := by
      by_cases h₁ : g ∣ balancedIntervalValue m₁ <;>
        by_cases h₂ : g ∣ balancedIntervalValue m₂ <;> simp [h₁, h₂]
    simp_rw [he, sum_ite_irrel]
    simp only [sum_const_zero, ← sum_filter, sum_const, nsmul_eq_mul,
      Nat.cast_id, balancedMultipleRows]
    ring
  calc
    balancedProductCollisionCount X (h : ℕ) ≤
        ∑ m₁ : Fin X, ∑ m₂ : Fin X, ∑ g ∈ (h : ℕ).divisors,
          if g ∣ balancedIntervalValue m₁ ∧ g ∣ balancedIntervalValue m₂ then g else 0 :=
      sum_le_sum fun m₁ _ => sum_le_sum fun m₂ _ => hpoint m₁ m₂
    _ = ∑ g ∈ (h : ℕ).divisors, ∑ m₁ : Fin X, ∑ m₂ : Fin X,
        if g ∣ balancedIntervalValue m₁ ∧ g ∣ balancedIntervalValue m₂ then g else 0 := by
      simp_rw [sum_comm (s := (univ : Finset (Fin X))) (t := (h : ℕ).divisors)]
    _ = _ := sum_congr rfl fun g _ => hdouble g

/-- Uniform nonzero-determinant count with its reciprocal-divisor cost retained. -/
theorem balancedProductCollisionCount_le_reciprocalDivisors (X : ℕ) (h : ℕ+) :
    (balancedProductCollisionCount X (h : ℕ) : ℝ) ≤
      4 * (X : ℝ) ^ 2 * ∑ g ∈ (h : ℕ).divisors, 1 / (g : ℝ) := by
  have hnat := balancedProductCollisionCount_le_divisorMass X h
  have hreal : (balancedProductCollisionCount X (h : ℕ) : ℝ) ≤
      ∑ g ∈ (h : ℕ).divisors, (g : ℝ) * ((balancedMultipleRows X g).card : ℝ) ^ 2 := by
    exact_mod_cast hnat
  apply hreal.trans
  rw [mul_sum]
  apply sum_le_sum
  intro g hg
  have hg0 : 0 < g := Nat.pos_of_mem_divisors hg
  have hgR : 0 < (g : ℝ) := by exact_mod_cast hg0
  have hc : ((balancedMultipleRows X g).card : ℝ) ≤ 2 * (X : ℝ) / g := by
    calc
      ((balancedMultipleRows X g).card : ℝ) ≤ ((2 * X / g : ℕ) : ℝ) := by
        exact_mod_cast card_balancedMultipleRows_le_div X g
      _ ≤ 2 * (X : ℝ) / g := by
        rw [le_div_iff₀ hgR]
        exact_mod_cast Nat.div_mul_le_self (2 * X) g
  calc
    (g : ℝ) * ((balancedMultipleRows X g).card : ℝ) ^ 2 ≤
        (g : ℝ) * (2 * (X : ℝ) / g) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2) hgR.le
    _ = _ := by field_simp; ring

end

end GaloisForLFunctions.Goldbach

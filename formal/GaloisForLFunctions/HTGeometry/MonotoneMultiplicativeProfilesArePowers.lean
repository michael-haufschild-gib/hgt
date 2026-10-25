import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Monotone multiplicative profiles are Archimedean powers

Comparing integer powers forces monotone logarithm-additive profiles to
have one slope. A nonnegative decreasing multiplicative profile is either
augmentation or a single nonincreasing real power.
-/

section

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.HTGeometry

/-- Integer-power comparison forces a monotone logarithm-additive map to have a single slope. -/
theorem monotone_log_additive_eq_log_mul (g : ℕ+ → ℝ)
    (hmono : Monotone g) (hone : g 1 = 0)
    (hmul : ∀ m n, g (m * n) = g m + g n) :
    ∀ n, g n = (g 2 / Real.log 2) * Real.log (n : ℝ) := by
  have hg0 (n : ℕ+) : 0 ≤ g n := by
    rw [← hone]
    exact hmono (show (1 : ℕ+) ≤ n from n.property)
  have hpow (n : ℕ+) (k : ℕ) : g (n ^ k) = (k : ℝ) * g n := by
    induction k with
    | zero => rw [pow_zero, hone, Nat.cast_zero, zero_mul]
    | succ k ih => rw [pow_succ, hmul, ih, Nat.cast_add_one]; ring
  have hslope (n m : ℕ+) (hm : (1 : ℕ+) < m) :
      g n ≤ g m * (Real.log (n : ℝ) / Real.log (m : ℝ)) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast n.property
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.property
    have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
    have hm0 := zero_lt_one.trans hm1
    have hlm : 0 < Real.log (m : ℝ) := Real.log_pos hm1
    have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    have hbound (k : ℕ) : (k : ℝ) * g n ≤
        (k : ℝ) * (g m * (Real.log (n : ℝ) / Real.log (m : ℝ))) + g m := by
      let x := (k : ℝ) * Real.log (n : ℝ) / Real.log (m : ℝ)
      let l := Nat.ceil x
      have hx : 0 ≤ x := div_nonneg (mul_nonneg (Nat.cast_nonneg _) hln) hlm.le
      have hceil : x ≤ (l : ℝ) := Nat.le_ceil x
      have hl : (l : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hx).le
      have hlogs : (k : ℝ) * Real.log (n : ℝ) ≤ (l : ℝ) * Real.log (m : ℝ) :=
        (div_le_iff₀ hlm).mp hceil
      have hpowers : (n : ℝ) ^ k ≤ (m : ℝ) ^ l := by
        apply (Real.log_le_log_iff (pow_pos hn0 k) (pow_pos hm0 l)).mp
        simpa only [Real.log_pow] using hlogs
      have hpowers' : n ^ k ≤ m ^ l := by exact_mod_cast hpowers
      have h := hmono hpowers'
      rw [hpow, hpow] at h
      calc
        _ ≤ (l : ℝ) * g m := h
        _ ≤ (x + 1) * g m := mul_le_mul_of_nonneg_right hl (hg0 m)
        _ = _ := by dsimp only [x]; ring
    by_contra h
    have hgap : 0 < g n - g m * (Real.log (n : ℝ) / Real.log (m : ℝ)) :=
      sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨k, hk⟩ := exists_nat_gt
      (g m / (g n - g m * (Real.log (n : ℝ) / Real.log (m : ℝ))))
    have hlarge := (div_lt_iff₀ hgap).mp hk
    have hsmall := hbound k
    nlinarith only [hlarge, hsmall]
  intro n
  by_cases hn : n = 1
  · subst n
    norm_num [hone]
  · have hn1 : (1 : ℕ+) < n := lt_of_le_of_ne n.property (Ne.symm hn)
    have hln : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn1)
    have htwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hu := hslope n 2 (by decide)
    have hl := hslope 2 n hn1
    change g n ≤ g 2 * (Real.log (n : ℝ) / Real.log 2) at hu
    change g 2 ≤ g n * (Real.log 2 / Real.log (n : ℝ)) at hl
    have hlu : g 2 * Real.log (n : ℝ) ≤ g n * Real.log 2 := by
      apply (le_div_iff₀ hln).mp
      simpa only [mul_div_assoc] using hl
    have hul : g n * Real.log 2 ≤ g 2 * Real.log (n : ℝ) := by
      apply (le_div_iff₀ htwo).mp
      simpa only [mul_div_assoc] using hu
    have heq := le_antisymm hul hlu
    calc
      g n = (g 2 * Real.log (n : ℝ)) / Real.log 2 := (eq_div_iff htwo.ne').mpr heq
      _ = _ := by ring

/-- A nonnegative decreasing multiplicative profile is augmentation or a single real power. -/
theorem antitone_nonnegative_monoidHom_eq_augmentation_or_rpow
    (r : ℕ+ →* ℝ) (hr0 : ∀ n, 0 ≤ r n) (hanti : Antitone r) :
    (∀ n : ℕ+, n ≠ 1 → r n = 0) ∨
      ∃ α : ℝ, 0 ≤ α ∧ ∀ n : ℕ+, r n = (n : ℝ) ^ (-α) := by
  by_cases htwo : r 2 = 0
  · refine Or.inl fun n hn => le_antisymm ?_ (hr0 n)
    have hn2 : (2 : ℕ+) ≤ n := by
      change (2 : ℕ) ≤ (n : ℕ)
      have hpos : 1 ≤ (n : ℕ) := n.property
      have hne : (n : ℕ) ≠ 1 := by intro h; apply hn; exact Subtype.ext h
      exact Nat.succ_le_of_lt (lt_of_le_of_ne hpos (Ne.symm hne))
    simpa only [htwo] using hanti hn2
  · have hr2 : 0 < r 2 := lt_of_le_of_ne (hr0 2) (Ne.symm htwo)
    have hnat : ∀ k : ℕ, k ≤ 2 ^ k := by
      intro k
      induction k with
      | zero => norm_num
      | succ k ih =>
        have hpow : 0 < (2 : ℕ) ^ k := Nat.pow_pos (by decide)
        rw [pow_succ]
        omega
    have hrpos (n : ℕ+) : 0 < r n := by
      have hle : n ≤ (2 : ℕ+) ^ (n : ℕ) := by exact_mod_cast hnat n
      have hp : 0 < r ((2 : ℕ+) ^ (n : ℕ)) := by rw [map_pow]; exact pow_pos hr2 _
      exact hp.trans_le (hanti hle)
    let g (n : ℕ+) : ℝ := -Real.log (r n)
    have hgmono : Monotone g := fun m n h =>
      neg_le_neg ((Real.log_le_log_iff (hrpos n) (hrpos m)).mpr (hanti h))
    have hg1 : g 1 = 0 := by simp only [g, map_one, Real.log_one, neg_zero]
    have hgmul (m n : ℕ+) : g (m * n) = g m + g n := by
      simp only [g, map_mul, Real.log_mul (hrpos m).ne' (hrpos n).ne', neg_add]
    have hg := monotone_log_additive_eq_log_mul g hgmono hg1 hgmul
    let α := g 2 / Real.log 2
    have hα : 0 ≤ α := div_nonneg
      (by rw [← hg1]; exact hgmono (by decide : (1 : ℕ+) ≤ 2))
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    refine Or.inr ⟨α, hα, fun n => ?_⟩
    rw [Real.rpow_def_of_pos (by exact_mod_cast n.property)]
    have hlog : Real.log (r n) = Real.log (n : ℝ) * (-α) := by
      have h := hg n
      change -Real.log (r n) = α * Real.log (n : ℝ) at h
      linarith only [h]
    rw [← hlog, Real.exp_log (hrpos n)]

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.monotone_log_additive_eq_log_mul
#print axioms GaloisForLFunctions.HTGeometry.antitone_nonnegative_monoidHom_eq_augmentation_or_rpow
end
end

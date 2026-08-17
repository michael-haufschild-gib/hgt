import Mathlib
import GaloisForLFunctions.HTGeometry.HelsonZetaEulerProduct

/-!
# The Helson Euler product converges for every unimodular phase

On `Re s > 1` the Euler factors differ from `1` by

```text
(1 - χ_p p^{-s})⁻¹ - 1 = χ_p p^{-s} / (1 - χ_p p^{-s}) ,
```

whose norm is at most `2 p^{-Re s}` because `‖χ_p p^{-s}‖ ≤ p^{-Re s} ≤ 2^{-Re s} < 1/2`.  The prime
sum `∑ p^{-Re s}` converges for `Re s > 1`, so the product is multipliable — for *every* unimodular
phase, not only for the finitely modified ones.

This is what makes the Helson zeta function defined on all of the phase torus.
-/

open Complex Filter

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The prime sum of a negative real power converges above the abscissa one. -/
theorem summable_prime_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-σ)) := by
  have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ σ)⁻¹) := Real.summable_nat_rpow_inv.2 hσ
  have hsub := hbase.subtype (fun n : ℕ => n.Prime)
  refine hsub.congr ?_
  intro p
  show ((((p : ℕ) : ℝ)) ^ σ)⁻¹ = ((p : ℕ) : ℝ) ^ (-σ)
  rw [Real.rpow_neg (Nat.cast_nonneg _)]

/-- Each Euler factor differs from `1` by at most `2 p^{-Re s}`. -/
theorem norm_eulerFactor_sub_one_le {χ : Nat.Primes → ℂ} (hunit : ∀ p, ‖χ p‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    ‖(1 - χ p * (p : ℂ) ^ (-s))⁻¹ - 1‖ ≤ 2 * ((p : ℕ) : ℝ) ^ (-s.re) := by
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
  have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  have hσ0 : (0 : ℝ) < s.re := lt_trans zero_lt_one hs
  have hzn : ‖χ p * (p : ℂ) ^ (-s)‖ ≤ ((p : ℕ) : ℝ) ^ (-s.re) := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re]
    calc ‖χ p‖ * ((p : ℕ) : ℝ) ^ (-s.re) ≤ 1 * ((p : ℕ) : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right (hunit p) (Real.rpow_nonneg hppos.le _)
      _ = ((p : ℕ) : ℝ) ^ (-s.re) := one_mul _
  have hlt : ((p : ℕ) : ℝ) ^ (-s.re) < 1 / 2 := by
    have hmono : (2 : ℝ) ^ s.re ≤ ((p : ℕ) : ℝ) ^ s.re :=
      Real.rpow_le_rpow (by norm_num) hp2 hσ0.le
    have hgt : (2 : ℝ) < (2 : ℝ) ^ s.re := by
      have := Real.rpow_lt_rpow_left_iff (x := (2 : ℝ)) (by norm_num) |>.2 hs
      simpa using this
    have hpow : (0 : ℝ) < ((p : ℕ) : ℝ) ^ s.re := Real.rpow_pos_of_pos hppos _
    rw [Real.rpow_neg hppos.le]
    rw [inv_lt_comm₀ hpow (by norm_num)]
    linarith
  have hden : (1 : ℝ) / 2 < ‖1 - χ p * (p : ℂ) ^ (-s)‖ := by
    have h1 : ‖(1 : ℂ)‖ - ‖χ p * (p : ℂ) ^ (-s)‖ ≤ ‖1 - χ p * (p : ℂ) ^ (-s)‖ :=
      norm_sub_norm_le _ _
    simp only [norm_one] at h1
    linarith
  have hne : (1 : ℂ) - χ p * (p : ℂ) ^ (-s) ≠ 0 :=
    one_sub_phase_prime_cpow_ne_zero hunit hs
  have hsplit : (1 - χ p * (p : ℂ) ^ (-s))⁻¹ - 1
      = (χ p * (p : ℂ) ^ (-s)) * (1 - χ p * (p : ℂ) ^ (-s))⁻¹ := by
    field_simp
    ring
  rw [hsplit, norm_mul, norm_inv]
  have hinv : ‖1 - χ p * (p : ℂ) ^ (-s)‖⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  calc ‖χ p * (p : ℂ) ^ (-s)‖ * ‖1 - χ p * (p : ℂ) ^ (-s)‖⁻¹
      ≤ ((p : ℕ) : ℝ) ^ (-s.re) * 2 :=
        mul_le_mul hzn hinv (by positivity) (Real.rpow_nonneg hppos.le _)
    _ = 2 * ((p : ℕ) : ℝ) ^ (-s.re) := by ring

/-- **The Helson Euler product is multipliable for every unimodular phase.** -/
theorem multipliable_helsonEuler {χ : Nat.Primes → ℂ} (hunit : ∀ p, ‖χ p‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    Multipliable (fun p : Nat.Primes => (1 - χ p * (p : ℂ) ^ (-s))⁻¹) := by
  have hsum : Summable (fun p : Nat.Primes => ‖(1 - χ p * (p : ℂ) ^ (-s))⁻¹ - 1‖) := by
    refine Summable.of_nonneg_of_le (fun p => norm_nonneg _)
      (fun p => norm_eulerFactor_sub_one_le hunit hs p) ?_
    exact (summable_prime_rpow_neg hs).mul_left 2
  have hmul := multipliable_one_add_of_summable hsum
  refine hmul.congr ?_
  intro p
  ring

end GaloisForLFunctions.HTGeometry

end

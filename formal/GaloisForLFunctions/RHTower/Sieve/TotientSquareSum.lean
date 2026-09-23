import GaloisForLFunctions.RHTower.Sieve.GcdSumTotient
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# Bounding the totient-weighted square sum

Each multiple-count in a window obeys `#{d ∈ (a,b] : g ∣ d} < (b-a)/g + 1`, and `φ(g) ≤ g`, so

`φ(g) · (#{d : g ∣ d})² ≤ (b-a)²/g + 2(b-a) + g`.

Summing over `g ≤ M` and using `∑_{g ≤ M} 1/g ≤ 1 + log M` and `∑_{g ≤ M} g ≤ M²` gives an explicit
bound of order `(b-a)² log M`.  Taken with `sum_gcd_eq_sum_totient_mul_sq` and
`sum_inv_lcm_le_gcd_sum` this completes the evaluation of the second moment of the balanced divisor
count.
-/

namespace RHTower.Sieve

open Finset

/-- The per-modulus bound for the totient-weighted square. -/
theorem totient_mul_card_sq_le {a b g : ℕ} (hg : 0 < g) (hab : a ≤ b) :
    ((Nat.totient g : ℕ) : ℝ) * (((Finset.Ioc a b).filter (fun d => g ∣ d)).card : ℝ) ^ (2 : ℕ)
      ≤ ((b : ℝ) - a) ^ (2 : ℕ) / (g : ℝ) + 2 * ((b : ℝ) - a) + (g : ℝ) := by
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have hlen : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
    linarith
  have hcard := abs_card_filter_dvd_Ioc_sub_lt g a b hg hab
  have hup : (((Finset.Ioc a b).filter (fun d => g ∣ d)).card : ℝ) ≤ ((b : ℝ) - a) / (g : ℝ) + 1 := by
    have := (abs_lt.mp hcard).2
    linarith
  have hnn : (0 : ℝ) ≤ (((Finset.Ioc a b).filter (fun d => g ∣ d)).card : ℝ) := Nat.cast_nonneg _
  have hphi : ((Nat.totient g : ℕ) : ℝ) ≤ (g : ℝ) := by
    exact_mod_cast Nat.totient_le g
  have hphi0 : (0 : ℝ) ≤ ((Nat.totient g : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsq : (((Finset.Ioc a b).filter (fun d => g ∣ d)).card : ℝ) ^ (2 : ℕ)
      ≤ (((b : ℝ) - a) / (g : ℝ) + 1) ^ (2 : ℕ) := pow_le_pow_left₀ hnn hup 2
  have hexpand : (g : ℝ) * (((b : ℝ) - a) / (g : ℝ) + 1) ^ (2 : ℕ)
      = ((b : ℝ) - a) ^ (2 : ℕ) / (g : ℝ) + 2 * ((b : ℝ) - a) + (g : ℝ) := by
    field_simp
    ring
  calc ((Nat.totient g : ℕ) : ℝ) * (((Finset.Ioc a b).filter (fun d => g ∣ d)).card : ℝ) ^ (2 : ℕ)
      ≤ ((Nat.totient g : ℕ) : ℝ) * (((b : ℝ) - a) / (g : ℝ) + 1) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hsq hphi0
    _ ≤ (g : ℝ) * (((b : ℝ) - a) / (g : ℝ) + 1) ^ (2 : ℕ) := by
        refine mul_le_mul_of_nonneg_right hphi (by positivity)
    _ = ((b : ℝ) - a) ^ (2 : ℕ) / (g : ℝ) + 2 * ((b : ℝ) - a) + (g : ℝ) := hexpand

/-- **The totient-weighted square sum, with an explicit bound.** -/
theorem sum_totient_mul_card_sq_le (a b M : ℕ) (hab : a ≤ b) :
    ∑ g ∈ Finset.Icc 1 M,
        ((Nat.totient g : ℕ) : ℝ) * (((Finset.Ioc a b).filter (fun d => g ∣ d)).card : ℝ) ^ (2 : ℕ)
      ≤ ((b : ℝ) - a) ^ (2 : ℕ) * (1 + Real.log M) + 2 * ((b : ℝ) - a) * (M : ℝ) + (M : ℝ) ^ (2 : ℕ) := by
  classical
  have hterm : ∀ g ∈ Finset.Icc 1 M,
      ((Nat.totient g : ℕ) : ℝ) * (((Finset.Ioc a b).filter (fun d => g ∣ d)).card : ℝ) ^ (2 : ℕ)
        ≤ ((b : ℝ) - a) ^ (2 : ℕ) * (1 / (g : ℝ)) + 2 * ((b : ℝ) - a) + (g : ℝ) := by
    intro g hg
    rw [Finset.mem_Icc] at hg
    have := totient_mul_card_sq_le (a := a) (b := b) (g := g) hg.1 hab
    calc ((Nat.totient g : ℕ) : ℝ) * (((Finset.Ioc a b).filter (fun d => g ∣ d)).card : ℝ) ^ (2 : ℕ)
        ≤ ((b : ℝ) - a) ^ (2 : ℕ) / (g : ℝ) + 2 * ((b : ℝ) - a) + (g : ℝ) := this
      _ = ((b : ℝ) - a) ^ (2 : ℕ) * (1 / (g : ℝ)) + 2 * ((b : ℝ) - a) + (g : ℝ) := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Nat.card_Icc, nsmul_eq_mul]
  have hharm := sum_Icc_one_div_le_one_add_log M
  have hlen : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
    linarith
  have hg : ∑ g ∈ Finset.Icc 1 M, (g : ℝ) ≤ (M : ℝ) ^ (2 : ℕ) := by
    have hterm2 : ∀ g ∈ Finset.Icc 1 M, (g : ℝ) ≤ (M : ℝ) := by
      intro g hg
      rw [Finset.mem_Icc] at hg
      exact_mod_cast hg.2
    refine le_trans (Finset.sum_le_sum hterm2) ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    have : ((M + 1 - 1 : ℕ) : ℝ) = (M : ℝ) := by
      have : M + 1 - 1 = M := by omega
      rw [this]
    rw [this]
    ring_nf
    exact le_refl _
  have hcard : ((M + 1 - 1 : ℕ) : ℝ) = (M : ℝ) := by
    have : M + 1 - 1 = M := by omega
    rw [this]
  rw [hcard]
  nlinarith [hharm, hlen, hg]

end RHTower.Sieve

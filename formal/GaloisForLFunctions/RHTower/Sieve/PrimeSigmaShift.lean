import GaloisForLFunctions.RHTower.Sieve.MertensFirst

/-!
# Shifting the abscissa in a prime sum

The prime sums of the Halász mechanism are weighted by `1/p`, while the Euler comparison with `ζ` is
available only at an abscissa `σ > 1`.  Moving between the two costs

    0 ≤ 1/p − p^{−σ} ≤ (σ − 1)·log p / p,

because `1 − e^{−u} ≤ u`.  Summing over the primes up to `z` and using Mertens' first theorem,

    | ∑_{p ≤ z} w_p (1/p − p^{−σ}) |  ≤  (σ − 1)·(log z + log 4)

for any weights of modulus at most one.  With the standard choice `σ = 1 + 1/log z` the right side
is bounded by `1 + log 4/log z`: the shift is free.

This is the first of the two comparisons separating `ZetaStripPrimeSum.lean` from a lower bound for
the Möbius distance; the second is the tail `∑_{p > z} p^{−σ}`.
-/

namespace RHTower.Sieve

open Finset

/-- `1 − e^{−u} ≤ u` for `u ≥ 0`, together with nonnegativity. -/
theorem one_sub_exp_neg_mem {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ 1 - Real.exp (-u) ∧ 1 - Real.exp (-u) ≤ u := by
  constructor
  · have : Real.exp (-u) ≤ Real.exp 0 := Real.exp_le_exp.2 (by linarith)
    rw [Real.exp_zero] at this
    linarith
  · have := Real.add_one_le_exp (-u)
    linarith

/-- **The pointwise abscissa shift.** -/
theorem inv_sub_rpow_le {p : ℕ} (hp : 2 ≤ p) {σ : ℝ} (hσ : 1 ≤ σ) :
    0 ≤ 1 / (p : ℝ) - ((p : ℝ)) ^ (-σ)
      ∧ 1 / (p : ℝ) - ((p : ℝ)) ^ (-σ) ≤ (σ - 1) * (Real.log p / (p : ℝ)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
  have hu0 : 0 ≤ (σ - 1) * Real.log (p : ℝ) := by
    have : (0 : ℝ) ≤ σ - 1 := by linarith
    positivity
  obtain ⟨hle0, hle1⟩ := one_sub_exp_neg_mem hu0
  have hinv : 1 / (p : ℝ) = Real.exp (-Real.log (p : ℝ)) := by
    rw [Real.exp_neg, Real.exp_log hp0, one_div]
  have hrpow : ((p : ℝ)) ^ (-σ) = Real.exp (-Real.log (p : ℝ)) * Real.exp (-((σ - 1) * Real.log p)) := by
    rw [Real.rpow_def_of_pos hp0, ← Real.exp_add]
    congr 1
    ring
  have hfac : 1 / (p : ℝ) - ((p : ℝ)) ^ (-σ)
      = Real.exp (-Real.log (p : ℝ)) * (1 - Real.exp (-((σ - 1) * Real.log p))) := by
    rw [hinv, hrpow]
    ring
  have hexp0 : (0 : ℝ) < Real.exp (-Real.log (p : ℝ)) := Real.exp_pos _
  constructor
  · rw [hfac]
    positivity
  · rw [hfac]
    have hstep : Real.exp (-Real.log (p : ℝ)) * (1 - Real.exp (-((σ - 1) * Real.log p)))
        ≤ Real.exp (-Real.log (p : ℝ)) * ((σ - 1) * Real.log p) :=
      mul_le_mul_of_nonneg_left hle1 hexp0.le
    refine le_trans hstep (le_of_eq ?_)
    rw [← hinv]
    ring

/-- **The abscissa shift, summed.**  Weights of modulus at most one cost `(σ−1)(log z + log 4)`. -/
theorem abs_sum_weight_shift_le {z : ℕ} (hz : 1 ≤ z) {σ : ℝ} (hσ : 1 ≤ σ)
    {w : ℕ → ℝ} (hw : ∀ p, |w p| ≤ 1) :
    |∑ p ∈ Nat.primesLE z, w p * (1 / (p : ℝ) - ((p : ℝ)) ^ (-σ))|
      ≤ (σ - 1) * (Real.log z + Real.log 4) := by
  have hσ0 : (0 : ℝ) ≤ σ - 1 := by linarith
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ p ∈ Nat.primesLE z,
      |w p * (1 / (p : ℝ) - ((p : ℝ)) ^ (-σ))|
        ≤ (σ - 1) * (Real.log p / (p : ℝ)) := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    obtain ⟨hle, hprime⟩ := hp
    obtain ⟨hnn, hub⟩ := inv_sub_rpow_le hprime.two_le hσ
    rw [abs_mul, abs_of_nonneg hnn]
    calc |w p| * (1 / (p : ℝ) - ((p : ℝ)) ^ (-σ))
        ≤ 1 * (1 / (p : ℝ) - ((p : ℝ)) ^ (-σ)) :=
          mul_le_mul_of_nonneg_right (hw p) hnn
      _ = 1 / (p : ℝ) - ((p : ℝ)) ^ (-σ) := one_mul _
      _ ≤ (σ - 1) * (Real.log p / (p : ℝ)) := hub
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hσ0
  exact mertensFirst_upper hz

end RHTower.Sieve

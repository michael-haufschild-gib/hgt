import GaloisForLFunctions.BiScaleUncertainty.Robin.StepThreshold
import GaloisForLFunctions.RHTower.RobinExtremalNumbers

/-!
# Divisor factors in threshold coordinates

The exponential gain is exactly the ratio of two successive local Euler
factors already used by Robin's extremal-number construction. Increasing
the existing valuation strictly decreases the next gain.
-/

noncomputable section

open Finset
open RHTower

namespace GaloisForLFunctions.BiScaleUncertainty.Robin

theorem stepDenominator_log (p : Nat.Primes) (v : ℕ) :
    stepDenominator v (Real.log (p : ℕ)) =
      ∑ k ∈ range (v + 1), ((p : ℕ) : ℝ) ^ (k + 1) := by
  unfold stepDenominator
  apply sum_congr rfl
  intro k _
  rw [← Nat.cast_add_one, Real.exp_nat_mul, Real.exp_log (by exact_mod_cast p.property.pos)]

theorem stepDenominator_log_mul (p : Nat.Primes) (v : ℕ) :
    stepDenominator v (Real.log (p : ℕ)) * ((p : ℕ) - 1 : ℝ) =
      (p : ℕ) * (((p : ℕ) : ℝ) ^ (v + 1) - 1) := by
  rw [stepDenominator_log]
  simp_rw [pow_succ]
  rw [← sum_mul]
  have h := geom_sum_mul (((p : ℕ) : ℝ)) (v + 1)
  calc
    _ = ((∑ k ∈ range (v + 1), ((p : ℕ) : ℝ) ^ k) * ((p : ℕ) - 1)) * (p : ℕ) := by ring
    _ = _ := by rw [h]; ring

private theorem robinLocal_pow_form (p : Nat.Primes) (v : ℕ) :
    robinLocal p v = (((p : ℕ) : ℝ) ^ (v + 1) - 1) /
      (((p : ℕ) : ℝ) ^ v * ((p : ℕ) - 1)) := by
  have hp0 : ((p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hp1 : ((p : ℕ) : ℝ) ≠ 1 := by exact_mod_cast p.property.ne_one
  unfold robinLocal
  rw [one_div_pow, pow_succ]
  field_simp

/-- Zimov's exponential gain is the corpus's exact local divisor ratio. -/
theorem stepGain_log_eq_robinLocal_ratio (p : Nat.Primes) (v : ℕ) :
    stepGain v (Real.log (p : ℕ)) = robinLocal p (v + 1) / robinLocal p v := by
  have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.pos
  have hp1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.one_lt
  have hpow : 1 < ((p : ℕ) : ℝ) ^ (v + 1) := one_lt_pow₀ hp1 (Nat.succ_ne_zero v)
  have hden := stepDenominator_log_mul p v
  have hden0 := (stepDenominator_pos v (Real.log (p : ℕ))).ne'
  have hinv : 1 / stepDenominator v (Real.log (p : ℕ)) =
      ((p : ℕ) - 1 : ℝ) / ((p : ℕ) * (((p : ℕ) : ℝ) ^ (v + 1) - 1)) := by
    apply (div_eq_div_iff hden0 (mul_ne_zero hp0.ne' (sub_ne_zero.mpr hpow.ne'))).mpr
    simpa only [one_mul, mul_comm] using hden.symm
  rw [stepGain, hinv, robinLocal_pow_form, robinLocal_pow_form]
  have hpn : ((p : ℕ) : ℝ) ^ (v + 1) - 1 ≠ 0 := sub_ne_zero.mpr hpow.ne'
  have hpm : ((p : ℕ) : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp1.ne'
  field_simp
  simp only [pow_succ]
  ring

/-- Successive local divisor ratios strictly decrease along every prime tower. -/
theorem robinLocal_ratio_succ_lt (p : Nat.Primes) (v : ℕ) :
    robinLocal p (v + 2) / robinLocal p (v + 1) <
      robinLocal p (v + 1) / robinLocal p v := by
  rw [← stepGain_log_eq_robinLocal_ratio p v,
    show v + 2 = (v + 1) + 1 by omega,
    ← stepGain_log_eq_robinLocal_ratio p (v + 1)]
  exact stepGain_succ_lt v _

/-- The local Euler-factor comparison has the exact threshold just constructed. -/
theorem robinLocal_ratio_gt_iff (p : Nat.Primes) (v : ℕ) {L : ℝ} (hL : 1 < L) :
    Real.log (L + Real.log (p : ℕ)) / Real.log L <
        robinLocal p (v + 1) / robinLocal p v ↔
      Real.log (p : ℕ) < stepThreshold v L := by
  rw [← stepGain_log_eq_robinLocal_ratio]
  have hp : 0 < Real.log ((p : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  simpa only [stepBalance, sub_pos] using
    (stepBalance_pos_iff v hL (by linarith only [hL, hp] : -L < Real.log (p : ℕ)))

/-- Strict log-concavity of the local divisor factors along every prime tower. -/
theorem robinLocal_strict_logConcave (p : Nat.Primes) (v : ℕ) :
    robinLocal p v * robinLocal p (v + 2) < robinLocal p (v + 1) ^ 2 := by
  have h := robinLocal_ratio_succ_lt p v
  rw [div_lt_div_iff₀ (robinLocal_pos p.property (v + 1))
    (robinLocal_pos p.property v)] at h
  nlinarith only [h]

end GaloisForLFunctions.BiScaleUncertainty.Robin

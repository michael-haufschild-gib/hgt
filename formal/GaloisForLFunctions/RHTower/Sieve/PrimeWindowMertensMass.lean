import GaloisForLFunctions.RHTower.Sieve.PrimeWindowMeanSquare
import GaloisForLFunctions.RHTower.Sieve.MertensSecondExpRate
import GaloisForLFunctions.RHTower.Sieve.TuranKubiliusRange

/-!
# Exponential-rate Mertens bound for prime windows

Mertens' second theorem with exponential error controls every half-open prime window uniformly
above one fixed threshold. Combined with `PrimeWindowMeanSquare`, this gives an unconditional
second-moment bound for the `c₂,n` block count in terms of its log-log increment and an
exponentially decaying lower-end error.
-/

namespace RHTower.Sieve

open Finset Filter

/-- The half-open prime interval `[a,b)` is the closed Mertens range `(a-1,b-1]`. -/
theorem primesIco_eq_primesRange_pred
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    primesIco a b = primesRange (a - 1) (b - 1) := by
  have hb : 1 ≤ b := ha.trans hab
  ext p
  rw [mem_primesIco]
  simp only [primesRange, Finset.mem_sdiff, mem_primesLE]
  constructor
  · rintro ⟨hap, hpb, hp⟩
    exact ⟨⟨by omega, hp⟩, by
      intro h
      omega⟩
  · rintro ⟨⟨hpb, hp⟩, hpa⟩
    have hpa' : ¬ p ≤ a - 1 := fun h => hpa ⟨h, hp⟩
    exact ⟨by omega, by omega, hp⟩

/-- Reciprocal mass of a half-open prime interval as a Mertens difference. -/
theorem sum_inv_primesIco_eq_mertensS_sub
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ p ∈ primesIco a b, 1 / (p : ℝ) =
      mertensS (b - 1) - mertensS (a - 1) := by
  rw [primesIco_eq_primesRange_pred ha hab]
  exact sum_inv_primesRange (Nat.sub_le_sub_right hab 1)

/-- Uniform exponential-error upper bound for every sufficiently high Mertens prime range. -/
theorem exists_sum_inv_primesRange_le_logLog_diff_add_exp :
    ∃ B c : ℝ, ∃ N₀ : ℕ, 0 < c ∧ 0 ≤ B ∧ 3 ≤ N₀ ∧
      ∀ ⦃u v : ℕ⦄, N₀ ≤ u → u ≤ v →
        ∑ p ∈ primesRange u v, 1 / (p : ℝ) ≤
          logLog v - logLog u +
            2 * B * Real.exp (-c * Real.sqrt (Real.log u)) := by
  obtain ⟨B, c, hc, hB, hrate⟩ := exists_mertensS_sub_logLog_sub_const_exp_rate
  rw [eventually_atTop] at hrate
  obtain ⟨N, hN⟩ := hrate
  refine ⟨B, c, max N 3, hc, hB, le_max_right _ _, ?_⟩
  intro u v hu huv
  have huN : N ≤ u := le_trans (le_max_left _ _) hu
  have hvN : N ≤ v := huN.trans huv
  have hu3 : 3 ≤ u := le_trans (le_max_right _ _) hu
  have hv3 : 3 ≤ v := hu3.trans huv
  have huR : (0 : ℝ) < (u : ℝ) := by positivity
  have huvR : (u : ℝ) ≤ (v : ℝ) := by exact_mod_cast huv
  have hlog : Real.log u ≤ Real.log v := Real.log_le_log huR huvR
  have hsqrt : Real.sqrt (Real.log u) ≤ Real.sqrt (Real.log v) :=
    Real.sqrt_le_sqrt hlog
  have hexp :
      Real.exp (-c * Real.sqrt (Real.log v)) ≤
        Real.exp (-c * Real.sqrt (Real.log u)) := by
    rw [Real.exp_le_exp]
    nlinarith [Real.sqrt_nonneg (Real.log u), Real.sqrt_nonneg (Real.log v)]
  have hBu :
      B * Real.exp (-c * Real.sqrt (Real.log v)) ≤
        B * Real.exp (-c * Real.sqrt (Real.log u)) :=
    mul_le_mul_of_nonneg_left hexp hB
  have huerr := hN u huN
  have hverr := hN v hvN
  rw [abs_le] at huerr hverr
  rw [sum_inv_primesRange huv]
  linarith

/-- Half-open form of the uniform exponential-error Mertens bound. -/
theorem exists_sum_inv_primesIco_le_logLog_diff_add_exp :
    ∃ B c : ℝ, ∃ N₀ : ℕ, 0 < c ∧ 0 ≤ B ∧ 3 ≤ N₀ ∧
      ∀ ⦃a b : ℕ⦄, 1 ≤ a → a ≤ b → N₀ ≤ a - 1 →
        ∑ p ∈ primesIco a b, 1 / (p : ℝ) ≤
          logLog (b - 1) - logLog (a - 1) +
            2 * B * Real.exp (-c * Real.sqrt (Real.log ((a - 1 : ℕ) : ℝ))) := by
  obtain ⟨B, c, N₀, hc, hB, hN₀, hmass⟩ :=
    exists_sum_inv_primesRange_le_logLog_diff_add_exp
  refine ⟨B, c, N₀, hc, hB, hN₀, ?_⟩
  intro a b ha hab hN
  rw [primesIco_eq_primesRange_pred ha hab]
  exact hmass hN (Nat.sub_le_sub_right hab 1)

/-- Unconditional mean-square bound for every sufficiently high prime window. -/
theorem exists_sum_sq_card_primeWindow_le_logLog_diff_add_exp :
    ∃ B c : ℝ, ∃ N₀ : ℕ, 0 < c ∧ 0 ≤ B ∧ 3 ≤ N₀ ∧
      ∀ ⦃a b Y : ℕ⦄, 1 ≤ a → a ≤ b → N₀ ≤ a - 1 →
        ∑ n ∈ Finset.Icc 1 Y, ((primeWindow n a b).card : ℝ) ^ 2 ≤
          (Y : ℝ) *
            ((logLog (b - 1) - logLog (a - 1) +
                2 * B * Real.exp (-c * Real.sqrt (Real.log ((a - 1 : ℕ) : ℝ)))) +
              (logLog (b - 1) - logLog (a - 1) +
                2 * B * Real.exp (-c * Real.sqrt (Real.log ((a - 1 : ℕ) : ℝ)))) ^ 2) := by
  obtain ⟨B, c, N₀, hc, hB, hN₀, hmass⟩ :=
    exists_sum_inv_primesIco_le_logLog_diff_add_exp
  refine ⟨B, c, N₀, hc, hB, hN₀, ?_⟩
  intro a b Y ha hab hN
  let η : ℝ := logLog (b - 1) - logLog (a - 1) +
    2 * B * Real.exp (-c * Real.sqrt (Real.log ((a - 1 : ℕ) : ℝ)))
  have hm : ∑ p ∈ primesIco a b, 1 / (p : ℝ) ≤ η := hmass ha hab hN
  have hmass_nonneg : 0 ≤ ∑ p ∈ primesIco a b, 1 / (p : ℝ) := by
    exact Finset.sum_nonneg fun p _ => by positivity
  have hη : 0 ≤ η := hmass_nonneg.trans hm
  exact sum_sq_card_primeWindow_le_of_mass hη hm

end RHTower.Sieve

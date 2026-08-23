import GaloisForLFunctions.RHTower.Sieve.VonMangoldtPerronSeries
import GaloisForLFunctions.RHTower.Sieve.PerronCutoffComparisons
import GaloisForLFunctions.RHTower.Sieve.DistinctReciprocalSum

/-!
# Splitting the Perron error of an infinite series

Outside the dyadic window the logarithm is bounded below by `log 2`, so the far part of the Perron
error is the whole Dirichlet mass divided by `πT log 2`.  Inside the window the logarithm is
comparable to the displacement, so the near part is a reciprocal-distance sum, which is harmless as
soon as the cutoff avoids the integers.
-/

namespace RHTower.Sieve

open Complex

noncomputable section

/-- **The far part of the Perron error.** -/
theorem perron_error_far_le {c : ℕ → ℂ} {x σ T : ℝ} (hx : 0 < x) (hσ : 0 < σ) (hT : 0 < T)
    (hconv : Summable (fun n : ℕ => ‖c n‖ * (x / n) ^ σ)) :
    ∑' n : ℕ, (if x / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x then 0
        else ‖c n‖ * ((x / n) ^ σ / (Real.pi * T * |Real.log (x / n)|)))
      ≤ (1 / (Real.pi * T * Real.log 2)) * ∑' n : ℕ, ‖c n‖ * (x / n) ^ σ := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hmaj : ∀ n : ℕ,
      (if x / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x then 0
        else ‖c n‖ * ((x / n) ^ σ / (Real.pi * T * |Real.log (x / n)|)))
        ≤ (1 / (Real.pi * T * Real.log 2)) * (‖c n‖ * (x / n) ^ σ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hz : (x / ((0 : ℕ) : ℝ)) = 0 := by simp
      rw [hz, Real.zero_rpow hσ.ne']
      split_ifs <;> simp
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hxn : (0 : ℝ) < x / n := div_pos hx hn0
      have hxσ : (0 : ℝ) ≤ (x / n) ^ σ := Real.rpow_nonneg hxn.le σ
      split_ifs with hnear
      · positivity
      · have hcase : x / n ≤ 1 / 2 ∨ 2 ≤ x / n := by
          by_contra hcon
          push Not at hcon
          have h1 : x < 2 * (n : ℝ) := by
            have h := hcon.2
            rw [div_lt_iff₀ hn0] at h
            linarith
          have h2 : (n : ℝ) < 2 * x := by
            have h := hcon.1
            rw [lt_div_iff₀ hn0] at h
            linarith
          exact hnear ⟨by linarith, by linarith⟩
        have hkey := log_two_le_abs_log hxn hcase
        have hden : (0 : ℝ) < Real.pi * T * Real.log 2 := by positivity
        have hden2 : Real.pi * T * Real.log 2 ≤ Real.pi * T * |Real.log (x / n)| := by
          have hpT : (0 : ℝ) < Real.pi * T := by positivity
          nlinarith [hkey, hpT]
        have hstep : (x / n) ^ σ / (Real.pi * T * |Real.log (x / n)|)
            ≤ (x / n) ^ σ / (Real.pi * T * Real.log 2) := by
          gcongr
        have hid : (1 / (Real.pi * T * Real.log 2)) * (‖c n‖ * (x / n) ^ σ)
            = ‖c n‖ * ((x / n) ^ σ / (Real.pi * T * Real.log 2)) := by ring
        rw [hid]
        exact mul_le_mul_of_nonneg_left hstep (norm_nonneg _)
  refine (Summable.of_nonneg_of_le ?_ hmaj (hconv.mul_left _)).tsum_le_tsum hmaj
    (hconv.mul_left _) |>.trans (le_of_eq ?_)
  · intro n
    split_ifs with h
    · exact le_rfl
    · have hxσ : (0 : ℝ) ≤ (x / n) ^ σ := Real.rpow_nonneg (by positivity) σ
      positivity
  · rw [← tsum_mul_left]

/-- At a half-integer cutoff the reciprocal distances to the integers sum harmonically. -/
theorem sum_inv_dist_halfInt_le (N : ℕ) (s : Finset ℕ) :
    ∑ n ∈ s, 1 / |((N : ℝ) + 1 / 2) - (n : ℝ)| ≤ 4 * (1 + Real.log s.card) := by
  classical
  have hv : ∀ n : ℕ, |((N : ℝ) + 1 / 2) - (n : ℝ)|
      = |((2 * (N : ℤ) + 1 - 2 * (n : ℤ) : ℤ) : ℝ)| / 2 := by
    intro n
    push_cast
    rw [show |2 * (N : ℝ) + 1 - 2 * (n : ℝ)| = |2 * ((N : ℝ) + 1 / 2 - (n : ℝ))| by ring_nf,
      abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    ring
  have hrw : ∑ n ∈ s, 1 / |((N : ℝ) + 1 / 2) - (n : ℝ)|
      = 2 * ∑ n ∈ s, 1 / |((2 * (N : ℤ) + 1 - 2 * (n : ℤ) : ℤ) : ℝ)| := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hv n]
    field_simp
  rw [hrw]
  have hinj : ∀ i ∈ s, ∀ j ∈ s,
      (2 * (N : ℤ) + 1 - 2 * (i : ℤ)) = (2 * (N : ℤ) + 1 - 2 * (j : ℤ)) → i = j := by
    intro i _ j _ h
    have : (i : ℤ) = (j : ℤ) := by omega
    exact_mod_cast this
  have hne : ∀ i ∈ s, (2 * (N : ℤ) + 1 - 2 * (i : ℤ)) ≠ 0 := by
    intro i _ h
    omega
  have hbase := sum_inv_abs_le_of_injOn s (fun i => 2 * (N : ℤ) + 1 - 2 * (i : ℤ)) hinj hne
  linarith

end

end RHTower.Sieve

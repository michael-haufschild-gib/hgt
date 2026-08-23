import GaloisForLFunctions.RHTower.Sieve.VonMangoldtPerronMass
import GaloisForLFunctions.RHTower.Sieve.PerronErrorNearHalfInt

/-!
# The total Perron truncation error for the Chebyshev function

Adding the near and far halves gives the whole truncation error at a half-integer cutoff, with the
Dirichlet mass on one side and the reciprocal-distance sum on the other.
-/

namespace RHTower.Sieve

open Complex ArithmeticFunction

noncomputable section

/-- **The total Perron error for `ψ`.** -/
theorem perron_error_vonMangoldt_total_le {N : ℕ} {σ T : ℝ} (hN : 1 ≤ N)
    (hσ : 1 < σ) (hσ2 : σ ≤ 2) (hT : 0 < T) :
    (∑' n : ℕ, ‖((Λ n : ℝ) : ℂ)‖
        * ((((N : ℝ) + 1 / 2) / n) ^ σ
          / (Real.pi * T * |Real.log (((N : ℝ) + 1 / 2) / n)|)))
      ≤ (1 / (Real.pi * T * Real.log 2)) * (((N : ℝ) + 1 / 2) ^ σ * (8 / (σ - 1) ^ 2))
        + (16 * Real.log (2 * ((N : ℝ) + 1 / 2)) * ((N : ℝ) + 1 / 2) / (Real.pi * T))
          * (4 * (1 + Real.log ((2 * N + 2 : ℕ) : ℝ))) := by
  classical
  have hx : (0 : ℝ) < (N : ℝ) + 1 / 2 := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hxone : (1 : ℝ) ≤ (N : ℝ) + 1 / 2 := by linarith
  have hx1 : (1 : ℝ) ≤ 2 * ((N : ℝ) + 1 / 2) := by linarith
  have hσ0 : (0 : ℝ) < σ := by linarith
  set x : ℝ := (N : ℝ) + 1 / 2 with hxdef
  set F : ℕ → ℝ := fun n => ‖((Λ n : ℝ) : ℂ)‖
    * ((x / n) ^ σ / (Real.pi * T * |Real.log (x / n)|)) with hF
  have hconv := summable_vonMangoldt_perron hx hσ
  have hdef := summable_perron_error (c := fun n : ℕ => ((Λ n : ℝ) : ℂ)) hx hσ0 hT hconv
  have hsplit : F = (fun n : ℕ => if x / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x then F n else 0)
      + fun n : ℕ => if x / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x then 0 else F n := by
    funext n
    simp only [Pi.add_apply]
    split_ifs <;> ring
  have hnearS : Summable (fun n : ℕ => if x / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x then F n else 0) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hdef
    · split_ifs with h
      · have : (0 : ℝ) ≤ (x / n) ^ σ := Real.rpow_nonneg (by positivity) σ
        positivity
      · exact le_rfl
    · split_ifs with h
      · exact le_rfl
      · have : (0 : ℝ) ≤ (x / n) ^ σ := Real.rpow_nonneg (by positivity) σ
        positivity
  have hfarS : Summable (fun n : ℕ => if x / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x then 0 else F n) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hdef
    · split_ifs with h
      · exact le_rfl
      · have : (0 : ℝ) ≤ (x / n) ^ σ := Real.rpow_nonneg (by positivity) σ
        positivity
    · split_ifs with h
      · have : (0 : ℝ) ≤ (x / n) ^ σ := Real.rpow_nonneg (by positivity) σ
        positivity
      · exact le_rfl
  have hsum : ∑' n : ℕ, F n
      = (∑' n : ℕ, if x / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x then F n else 0)
        + ∑' n : ℕ, (if x / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x then 0 else F n) := by
    rw [← hnearS.tsum_add hfarS]
    refine tsum_congr fun n => ?_
    split_ifs <;> ring
  rw [hF] at hsum ⊢
  rw [hsum]
  have hfar := perron_error_far_le (c := fun n : ℕ => ((Λ n : ℝ) : ℂ)) hx hσ0 hT hconv
  have hmass := tsum_vonMangoldt_mass_le hx hσ hσ2
  have hnear := perron_error_near_halfInt_le (c := fun n : ℕ => ((Λ n : ℝ) : ℂ)) (N := N)
    (σ := σ) (T := T) (B := Real.log (2 * x)) hσ0 hσ2 hT
    (Real.log_nonneg hx1) (fun n hn => vonMangoldt_le_log_window hxone hn)
  have hcoef : (0 : ℝ) ≤ 1 / (Real.pi * T * Real.log 2) := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hfar' : (∑' n : ℕ, if x / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x then 0
      else ‖((Λ n : ℝ) : ℂ)‖ * ((x / n) ^ σ / (Real.pi * T * |Real.log (x / n)|)))
      ≤ (1 / (Real.pi * T * Real.log 2)) * (x ^ σ * (8 / (σ - 1) ^ 2)) :=
    hfar.trans (mul_le_mul_of_nonneg_left hmass hcoef)
  linarith [hfar', hnear]

end

end RHTower.Sieve

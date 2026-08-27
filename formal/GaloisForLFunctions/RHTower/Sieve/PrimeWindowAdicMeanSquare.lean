import GaloisForLFunctions.RHTower.Sieve.PrimeWindowMertensMass

/-!
# Mean square on a short multiplicative prime block

This file converts the exponential-rate Mertens estimate into the linear `δ` mean-square bound
needed for a `(1+δ)`-adic block in the Matomäki--Teräväinen `c₂,n` term.
-/

namespace RHTower.Sieve

open Finset Filter

/-- Across a multiplicative interval of relative width `δ`, the log-log increment is at most
`δ / log u`. -/
lemma logLog_sub_le_delta_div_log
    {u v : ℕ} {δ : ℝ} (hu : 3 ≤ u) (huv : u ≤ v)
    (hδ : 0 ≤ δ) (hband : (v : ℝ) ≤ (1 + δ) * (u : ℝ)) :
    logLog v - logLog u ≤ δ / Real.log u := by
  have huR : (0 : ℝ) < (u : ℝ) := by positivity
  have hvR : (0 : ℝ) < (v : ℝ) := by
    have : 3 ≤ v := hu.trans huv
    positivity
  have hlogu : 0 < Real.log u := by
    exact Real.log_pos (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two (by omega : 2 ≤ u)))
  have huvR : (u : ℝ) ≤ (v : ℝ) := by exact_mod_cast huv
  have hloguv : Real.log u ≤ Real.log v := Real.log_le_log huR huvR
  have hlogdiff : Real.log v - Real.log u ≤ δ := by
    have hratio : (v : ℝ) / (u : ℝ) ≤ 1 + δ := by
      rw [div_le_iff₀ huR]
      exact hband
    have hbase : 0 < 1 + δ := by linarith
    have hratio_pos : 0 < (v : ℝ) / (u : ℝ) := by positivity
    have hlogratio : Real.log ((v : ℝ) / (u : ℝ)) ≤ Real.log (1 + δ) :=
      Real.log_le_log hratio_pos hratio
    have hlogone : Real.log (1 + δ) ≤ δ := by
      have := Real.log_le_sub_one_of_pos hbase
      linarith
    rw [Real.log_div hvR.ne' huR.ne'] at hlogratio
    linarith
  have hstep := log_sub_log_le hlogu hloguv
  exact hstep.trans (div_le_div_of_nonneg_right hlogdiff hlogu.le)

/-- Uniform `O(Yδ)` mean square for every sufficiently high `(1+δ)` prime window once the
exponential Mertens error has fallen below `δ`. -/
theorem exists_sum_sq_card_primeWindow_le_six_mul_delta :
    ∃ B c : ℝ, ∃ N₀ : ℕ, 0 < c ∧ 0 ≤ B ∧ 3 ≤ N₀ ∧
      ∀ ⦃a b Y : ℕ⦄ ⦃δ : ℝ⦄,
        1 ≤ a → a ≤ b → N₀ ≤ a - 1 → 0 ≤ δ → δ ≤ 1 →
        ((b - 1 : ℕ) : ℝ) ≤ (1 + δ) * ((a - 1 : ℕ) : ℝ) →
        2 * B * Real.exp (-c * Real.sqrt (Real.log ((a - 1 : ℕ) : ℝ))) ≤ δ →
        ∑ n ∈ Finset.Icc 1 Y, ((primeWindow n a b).card : ℝ) ^ 2 ≤
          6 * (Y : ℝ) * δ := by
  obtain ⟨B, c, N₀, hc, hB, hN₀, hmass⟩ :=
    exists_sum_inv_primesIco_le_logLog_diff_add_exp
  refine ⟨B, c, N₀, hc, hB, hN₀, ?_⟩
  intro a b Y δ ha hab hN hδ hδ1 hband herr
  have hu3 : 3 ≤ a - 1 := hN₀.trans hN
  have huv : a - 1 ≤ b - 1 := Nat.sub_le_sub_right hab 1
  have hlogu : 1 ≤ Real.log ((a - 1 : ℕ) : ℝ) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have hcast : (3 : ℝ) ≤ ((a - 1 : ℕ) : ℝ) := by exact_mod_cast hu3
    linarith [Real.exp_one_lt_d9]
  have hinc := logLog_sub_le_delta_div_log hu3 huv hδ hband
  have hdiv : δ / Real.log ((a - 1 : ℕ) : ℝ) ≤ δ := by
    rw [div_le_iff₀ (by linarith : 0 < Real.log ((a - 1 : ℕ) : ℝ))]
    nlinarith
  let η : ℝ := logLog (b - 1) - logLog (a - 1) +
    2 * B * Real.exp (-c * Real.sqrt (Real.log ((a - 1 : ℕ) : ℝ)))
  have hm : ∑ p ∈ primesIco a b, 1 / (p : ℝ) ≤ η := hmass ha hab hN
  have hmass_nonneg : 0 ≤ ∑ p ∈ primesIco a b, 1 / (p : ℝ) := by
    exact Finset.sum_nonneg fun p _ => by positivity
  have hη : 0 ≤ η := hmass_nonneg.trans hm
  have hηle : η ≤ 2 * δ := by
    dsimp [η]
    linarith
  have hmean := sum_sq_card_primeWindow_le_of_mass (Y := Y) hη hm
  have hY : 0 ≤ (Y : ℝ) := Nat.cast_nonneg Y
  have hsq : η ^ 2 ≤ (2 * δ) ^ 2 :=
    (sq_le_sq₀ hη (by positivity)).2 hηle
  have hbudget : η + η ^ 2 ≤ 6 * δ := by
    nlinarith
  calc
    ∑ n ∈ Finset.Icc 1 Y, ((primeWindow n a b).card : ℝ) ^ 2 ≤
        (Y : ℝ) * (η + η ^ 2) := hmean
    _ ≤ 6 * (Y : ℝ) * δ := by
      have := mul_le_mul_of_nonneg_left hbudget hY
      nlinarith

end RHTower.Sieve

import GaloisForLFunctions.RHTower.Sieve.PolylogLimits
import GaloisForLFunctions.RHTower.Sieve.PrimeWindowAdicMeanSquare

/-!
# Log-power schedule for short prime windows

The exponential square-root-log error in the Mertens estimate beats every fixed negative power of
the lower-end logarithm. This discharges the last error comparison in the `c₂,n` one-block mean
square and supplies an eventual log-power block schedule.
-/

namespace RHTower.Sieve

open Filter Topology

/-- Exponential square-root-log decay beats every negative power of the logarithm. -/
theorem eventually_two_mul_exp_neg_sqrt_log_le_log_rpow_neg
    {B c K : ℝ} (hB : 0 ≤ B) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      2 * B * Real.exp (-c * Real.sqrt (Real.log x)) ≤
        (Real.log x) ^ (-K) := by
  have hsmall := (tendsto_log_rpow_neg (δ := (1 / 6 : ℝ)) (by norm_num)).eventually_lt_const hc
  have hroot : ∀ᶠ x : ℝ in atTop,
      (Real.log x) ^ (1 / 3 : ℝ) ≤ c * Real.sqrt (Real.log x) := by
    filter_upwards [hsmall, Filter.eventually_gt_atTop (1 : ℝ)] with x hs hx
    have hlogx : 0 < Real.log x := Real.log_pos hx
    have hpowhalf : 0 ≤ (Real.log x) ^ (1 / 2 : ℝ) :=
      Real.rpow_nonneg hlogx.le _
    have hs' : (Real.log x) ^ (-1 / 6 : ℝ) ≤ c := by
      simpa only [neg_div] using hs.le
    calc
      (Real.log x) ^ (1 / 3 : ℝ) =
          (Real.log x) ^ ((-1 / 6 : ℝ) + 1 / 2) :=
        congrArg (fun t : ℝ => (Real.log x) ^ t) (by norm_num)
      _ = (Real.log x) ^ (-1 / 6 : ℝ) * (Real.log x) ^ (1 / 2 : ℝ) :=
        Real.rpow_add hlogx _ _
      _ ≤ c * (Real.log x) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hs' hpowhalf
      _ = c * Real.sqrt (Real.log x) := by rw [Real.sqrt_eq_rpow]
  have hlim0 := tendsto_rpow_log_mul_exp_neg (c := K) (a := (1 / 3 : ℝ)) (by norm_num)
  have hlim : Tendsto (fun x : ℝ =>
      2 * B * ((Real.log x) ^ K * Real.exp (-((Real.log x) ^ (1 / 3 : ℝ)))))
      atTop (𝓝 0) := by
    simpa using hlim0.const_mul (2 * B)
  have hone := hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hroot, hone, Filter.eventually_gt_atTop (1 : ℝ)] with x hrootx honex hx
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hpowpos : 0 < (Real.log x) ^ K := Real.rpow_pos_of_pos hlogx _
  have hexp : Real.exp (-c * Real.sqrt (Real.log x)) ≤
      Real.exp (-((Real.log x) ^ (1 / 3 : ℝ))) := by
    rw [Real.exp_le_exp]
    linarith
  have hcoef : 0 ≤ 2 * B * (Real.log x) ^ K := by positivity
  have hbound :
      2 * B * (Real.log x) ^ K * Real.exp (-c * Real.sqrt (Real.log x)) ≤ 1 := by
    calc
      2 * B * (Real.log x) ^ K * Real.exp (-c * Real.sqrt (Real.log x)) ≤
          2 * B * (Real.log x) ^ K *
            Real.exp (-((Real.log x) ^ (1 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_left hexp hcoef
      _ ≤ 1 := by
        have hlt : 2 * B * (Real.log x) ^ K *
            Real.exp (-((Real.log x) ^ (1 / 3 : ℝ))) < 1 := by
          calc
            2 * B * (Real.log x) ^ K *
                Real.exp (-((Real.log x) ^ (1 / 3 : ℝ))) =
              2 * B * ((Real.log x) ^ K *
                Real.exp (-((Real.log x) ^ (1 / 3 : ℝ)))) := by ring
            _ < 1 := honex
        exact hlt.le
  rw [Real.rpow_neg hlogx.le, ← one_div, le_div_iff₀ hpowpos]
  nlinarith

/-- Natural-number form of the log-power absorption. -/
theorem eventually_nat_two_mul_exp_neg_sqrt_log_le_log_rpow_neg
    {B c K : ℝ} (hB : 0 ≤ B) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      2 * B * Real.exp (-c * Real.sqrt (Real.log n)) ≤
        (Real.log n) ^ (-K) := by
  exact (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_two_mul_exp_neg_sqrt_log_le_log_rpow_neg hB hc)

/-- Eventual `O(Y(log u)^{-K})` mean square on every block of the corresponding relative width. -/
theorem exists_primeWindow_logPowerSchedule
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ N : ℕ, 3 ≤ N ∧ ∀ ⦃a b Y : ℕ⦄,
      N ≤ a - 1 → a ≤ b →
      ((b - 1 : ℕ) : ℝ) ≤
        (1 + Real.log ((a - 1 : ℕ) : ℝ) ^ (-K)) * ((a - 1 : ℕ) : ℝ) →
      ∑ n ∈ Finset.Icc 1 Y, ((primeWindow n a b).card : ℝ) ^ 2 ≤
        6 * (Y : ℝ) * Real.log ((a - 1 : ℕ) : ℝ) ^ (-K) := by
  obtain ⟨B, c, N₀, hc, hB, hN₀, hblock⟩ :=
    exists_sum_sq_card_primeWindow_le_six_mul_delta
  have herr := eventually_nat_two_mul_exp_neg_sqrt_log_le_log_rpow_neg
    (K := K) hB hc
  rw [eventually_atTop] at herr
  obtain ⟨N₁, hN₁⟩ := herr
  refine ⟨max N₀ N₁, hN₀.trans (le_max_left _ _), ?_⟩
  intro a b Y ha hab hband
  have hN₀a : N₀ ≤ a - 1 := (le_max_left _ _).trans ha
  have hN₁a : N₁ ≤ a - 1 := (le_max_right _ _).trans ha
  have hu3 : 3 ≤ a - 1 := hN₀.trans hN₀a
  have ha1 : 1 ≤ a := by omega
  have hlog1 : 1 ≤ Real.log ((a - 1 : ℕ) : ℝ) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have hcast : (3 : ℝ) ≤ ((a - 1 : ℕ) : ℝ) := by exact_mod_cast hu3
    linarith [Real.exp_one_lt_d9]
  have hlogpos : 0 < Real.log ((a - 1 : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hlog1
  have hδ0 : 0 ≤ Real.log ((a - 1 : ℕ) : ℝ) ^ (-K) :=
    Real.rpow_nonneg hlogpos.le _
  have hδ1 : Real.log ((a - 1 : ℕ) : ℝ) ^ (-K) ≤ 1 := by
    rw [Real.rpow_neg hlogpos.le]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow hlog1 hK)
  exact hblock ha1 hab hN₀a hδ0 hδ1 hband (hN₁ (a - 1) hN₁a)

end RHTower.Sieve

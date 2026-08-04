import GaloisForLFunctions.RHTower.Sieve.MarkerCountUpper
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The matching criterion holds for all large scales

At the square ratio `Q = M` the headroom of the criterion is *exactly* `log 2`:

`logLog(M²) − logLog M = log(2 log M) − log(log M) = log 2`.

Every loss is smaller by a factor of `log`: the Mertens error decays like `1/log M`, the source
term like `1/log Y`, and the floor loss like `1/log W`.  Taking `M = N²` and all three sieve
parameters equal to `N` makes each loss `O(1/log N)` against a fixed positive main term, so the
criterion holds for every large `N`.
-/

namespace RHTower.Sieve

open Finset Nat Filter

/-- **The square window has headroom exactly `log 2`.** -/
theorem logLog_sq_sub {M : ℕ} (hM : 2 ≤ M) : logLog (M * M) - logLog M = Real.log 2 := by
  have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < (M : ℝ) := by linarith
  have hlogM : 0 < Real.log M := Real.log_pos (by linarith)
  have hcast : ((M * M : ℕ) : ℝ) = (M : ℝ) * (M : ℝ) := by push_cast; ring
  unfold logLog
  rw [hcast, Real.log_mul (by linarith) (by linarith)]
  have htwo : Real.log M + Real.log M = 2 * Real.log M := by ring
  rw [htwo, Real.log_mul (by norm_num) (by linarith)]
  ring

/-- The fourth power of the logarithm is negligible against the square. -/
theorem tendsto_log_rpow_div_sq :
    Filter.Tendsto (fun N : ℕ => (Real.log N) ^ (4 : ℝ) / (N : ℝ) ^ (2 : ℝ))
      Filter.atTop (nhds 0) := by
  have hbase : Filter.Tendsto (fun x : ℝ => (Real.log x) ^ (4 : ℝ) / x ^ (2 : ℝ))
      Filter.atTop (nhds 0) :=
    (_root_.isLittleO_log_rpow_rpow_atTop 4 (by norm_num : (0 : ℝ) < 2)).tendsto_div_nhds_zero
  exact hbase.comp tendsto_natCast_atTop_atTop

/-- The reciprocal logarithm is negligible. -/
theorem tendsto_inv_log_nat :
    Filter.Tendsto (fun N : ℕ => 1 / Real.log N) Filter.atTop (nhds 0) := by
  have hlog : Filter.Tendsto (fun N : ℕ => Real.log N) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine hlog.inv_tendsto_atTop.congr ?_
  intro n
  rw [Pi.inv_apply, one_div]

/-- The total relative loss of the criterion at the square window. -/
noncomputable def matchingGap (N : ℕ) : ℝ :=
  (4 + 3 * (2 * mertensFirstConst + 1 / 2) / 4) * (1 / Real.log N)
    + 17 * Real.exp (4 * mertensSecondUpperConst)
        * ((Real.log N) ^ (4 : ℝ) / (N : ℝ) ^ (2 : ℝ))

theorem tendsto_matchingGap : Filter.Tendsto matchingGap Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto
      (fun N : ℕ => (4 + 3 * (2 * mertensFirstConst + 1 / 2) / 4) * (1 / Real.log N))
      Filter.atTop (nhds 0) := by
    have := tendsto_inv_log_nat.const_mul (4 + 3 * (2 * mertensFirstConst + 1 / 2) / 4)
    simpa using this
  have h2 : Filter.Tendsto
      (fun N : ℕ => 17 * Real.exp (4 * mertensSecondUpperConst)
        * ((Real.log N) ^ (4 : ℝ) / (N : ℝ) ^ (2 : ℝ))) Filter.atTop (nhds 0) := by
    have := tendsto_log_rpow_div_sq.const_mul (17 * Real.exp (4 * mertensSecondUpperConst))
    simpa using this
  have hsum := h1.add h2
  unfold matchingGap
  simpa using hsum

/-- **The relative loss eventually falls below the headroom.** -/
theorem eventually_matchingGap_le :
    ∀ᶠ N : ℕ in Filter.atTop, matchingGap N ≤ Real.log 2 := by
  have hpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  exact Filter.Tendsto.eventually_le_const hpos tendsto_matchingGap

/-- **The matching holds at every large scale.**  At `M = N²`, marker ratio `Q = M`, window
`H = M²` and all three sieve parameters equal to `N`, the primes of the window inject into the
marker block with displacement at most `H`, for every sufficiently large `N`. -/
theorem eventually_exists_hall_injection :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∃ f : ℕ → ℕ,
        Set.InjOn f ↑{p ∈ Finset.Ioc 0 ((N * N) * (N * N)) | p.Prime ∧ N < p}
        ∧ (∀ x ∈ {p ∈ Finset.Ioc 0 ((N * N) * (N * N)) | p.Prime ∧ N < p},
            f x ∈ RHTower.markerBlockTargets (bigPrimeSet (N * N) ((N * N) * (N * N)))
              (windowCell 0 ((N * N) * (N * N))))
        ∧ ∀ x ∈ {p ∈ Finset.Ioc 0 ((N * N) * (N * N)) | p.Prime ∧ N < p},
            |(f x : ℤ) - (x : ℤ)| ≤ (((N * N) * (N * N) : ℕ) : ℤ) := by
  filter_upwards [eventually_matchingGap_le, Filter.eventually_ge_atTop 3] with N hgap hN
  have hN2 : 2 ≤ N := by omega
  have hnR : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hMM : 3 ≤ N * N := by nlinarith
  have hcast2 : ((N * N : ℕ) : ℝ) = (N : ℝ) ^ 2 := by push_cast; ring
  have hcast4 : (((N * N) * (N * N) : ℕ) : ℝ) = (N : ℝ) ^ 4 := by push_cast; ring
  have hlogM : Real.log ((N * N : ℕ) : ℝ) = 2 * Real.log N := by
    rw [hcast2, Real.log_pow]
    push_cast
    ring
  have hlogH : Real.log ((((N * N) * (N * N)) : ℕ) : ℝ) = 4 * Real.log N := by
    rw [hcast4, Real.log_pow]
    push_cast
    ring
  have hhead : logLog (((N * N) * (N * N) : ℕ)) - logLog (N * N) = Real.log 2 :=
    logLog_sq_sub (by omega)
  have hrp : (N : ℝ) ^ (2 : ℝ) = (N : ℝ) ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hP16 : (Real.log ((N * N : ℕ) : ℝ)) ^ (4 : ℝ)
      = 16 * (Real.log N) ^ (4 : ℝ) := by
    rw [hlogM, Real.mul_rpow (by norm_num) hL.le]
    norm_num
  have hkey : (N : ℝ) ^ 4 * (4 + 3 * (2 * mertensFirstConst + 1 / 2) / 4) * (1 / Real.log N)
      + 17 * Real.exp (4 * mertensSecondUpperConst) * ((N : ℝ) ^ 2 * (Real.log N) ^ (4 : ℝ))
      ≤ (N : ℝ) ^ 4 * Real.log 2 := by
    have hmul := mul_le_mul_of_nonneg_left hgap (show (0 : ℝ) ≤ (N : ℝ) ^ 4 by positivity)
    unfold matchingGap at hmul
    rw [hrp] at hmul
    have hrw : (N : ℝ) ^ 4 * ((4 + 3 * (2 * mertensFirstConst + 1 / 2) / 4) * (1 / Real.log N)
          + 17 * Real.exp (4 * mertensSecondUpperConst)
              * ((Real.log N) ^ (4 : ℝ) / (N : ℝ) ^ 2))
        = (N : ℝ) ^ 4 * (4 + 3 * (2 * mertensFirstConst + 1 / 2) / 4) * (1 / Real.log N)
          + 17 * Real.exp (4 * mertensSecondUpperConst)
              * ((N : ℝ) ^ 2 * (Real.log N) ^ (4 : ℝ)) := by
      field_simp
    rw [hrw] at hmul
    exact hmul
  have hgoal : 2 * (N : ℝ) ^ 4 / Real.log N
      + (N : ℝ) ^ 2 * (Real.exp (4 * mertensSecondUpperConst) * (Real.log N) ^ (4 : ℝ))
      + (2 * ((N : ℝ) ^ 4 - (N : ℝ) ^ 2) / Real.log N
          + (N : ℝ) ^ 2 * (Real.exp (4 * mertensSecondUpperConst)
              * (16 * (Real.log N) ^ (4 : ℝ))))
      + (N : ℝ) ^ 4 * ((2 * mertensFirstConst + 1 / 2) / (4 * Real.log N)
          + (2 * mertensFirstConst + 1 / 2) / (2 * Real.log N))
      ≤ (N : ℝ) ^ 4 * Real.log 2 := by
    have e1 : 2 * (N : ℝ) ^ 4 / Real.log N
        + (N : ℝ) ^ 2 * (Real.exp (4 * mertensSecondUpperConst) * (Real.log N) ^ (4 : ℝ))
        + (2 * ((N : ℝ) ^ 4 - (N : ℝ) ^ 2) / Real.log N
            + (N : ℝ) ^ 2 * (Real.exp (4 * mertensSecondUpperConst)
                * (16 * (Real.log N) ^ (4 : ℝ))))
        + (N : ℝ) ^ 4 * ((2 * mertensFirstConst + 1 / 2) / (4 * Real.log N)
            + (2 * mertensFirstConst + 1 / 2) / (2 * Real.log N))
        = (N : ℝ) ^ 4 * (4 + 3 * (2 * mertensFirstConst + 1 / 2) / 4) * (1 / Real.log N)
          - 2 * (N : ℝ) ^ 2 * (1 / Real.log N)
          + 17 * Real.exp (4 * mertensSecondUpperConst)
              * ((N : ℝ) ^ 2 * (Real.log N) ^ (4 : ℝ)) := by
      field_simp
      ring
    rw [e1]
    have hpos : 0 ≤ 2 * (N : ℝ) ^ 2 * (1 / Real.log N) := by positivity
    linarith [hkey]
  obtain ⟨f, hf1, hf2, hf3⟩ :=
    exists_hall_injection_full (X := 0) (H := (N * N) * (N * N)) (M := N * N) (Q := N * N)
      (z := N) (Y := N) (W := N) hMM (by omega) (by omega) (by omega) le_rfl hN2 hL
      (by omega) (Nat.le_mul_of_pos_left N (by omega)) hL
      (by
        rw [hhead, hP16, hlogH, hlogM, hcast4, hcast2]
        linarith [hgoal])
  rw [Nat.zero_add] at hf1 hf2 hf3
  exact ⟨f, hf1, hf2, hf3⟩

end RHTower.Sieve

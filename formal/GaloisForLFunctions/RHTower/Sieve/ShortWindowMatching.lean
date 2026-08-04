import GaloisForLFunctions.RHTower.Sieve.AsymptoticMatching

/-!
# The matching in a genuinely short window

At the square ratio the window has to be the whole range, and a displacement bound of the size of
the window says nothing.  A marker ratio that is a *power* of the marker scale keeps the headroom a
positive constant while shrinking the window: with `M = N²` and `Q = N`,

`logLog(QM) − logLog M = log(3 log N) − log(2 log N) = log(3/2)`,

the markers reach `N³` so the window need only have length `H = N³`, and it sits at height
`X = N⁴ − N³`.  So `H` is about `X^{3/4}`: the injection moves each prime by less than a fixed
power of the window height, which is the content the trivial case lacks.
-/

namespace RHTower.Sieve

open Finset Nat Filter

/-- **The cube-over-square window has headroom exactly `log 3 − log 2`.** -/
theorem logLog_cube_sub_sq {N : ℕ} (hN : 2 ≤ N) :
    logLog (N * (N * N)) - logLog (N * N) = Real.log 3 - Real.log 2 := by
  have hnR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hc3 : ((N * (N * N) : ℕ) : ℝ) = (N : ℝ) ^ 3 := by push_cast; ring
  have hc2 : ((N * N : ℕ) : ℝ) = (N : ℝ) ^ 2 := by push_cast; ring
  unfold logLog
  rw [hc3, hc2, Real.log_pow, Real.log_pow]
  have h3 : ((3 : ℕ) : ℝ) * Real.log N = 3 * Real.log N := by push_cast; ring
  have h2 : ((2 : ℕ) : ℝ) * Real.log N = 2 * Real.log N := by push_cast; ring
  rw [h3, h2, Real.log_mul (by norm_num) hL.ne', Real.log_mul (by norm_num) hL.ne']
  ring

/-- The fourth power of the logarithm is negligible against the first power. -/
theorem tendsto_log_rpow_div_id :
    Filter.Tendsto (fun N : ℕ => (Real.log N) ^ (4 : ℝ) / (N : ℝ) ^ (1 : ℝ))
      Filter.atTop (nhds 0) := by
  have hbase : Filter.Tendsto (fun x : ℝ => (Real.log x) ^ (4 : ℝ) / x ^ (1 : ℝ))
      Filter.atTop (nhds 0) :=
    (_root_.isLittleO_log_rpow_rpow_atTop 4 (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  exact hbase.comp tendsto_natCast_atTop_atTop

/-- The total relative loss of the criterion at the cube-over-square window. -/
noncomputable def shortMatchingGap (N : ℕ) : ℝ :=
  (4 + 5 * (2 * mertensFirstConst + 1 / 2) / 6) * (1 / Real.log N)
    + 17 * Real.exp (4 * mertensSecondUpperConst)
        * ((Real.log N) ^ (4 : ℝ) / (N : ℝ) ^ (1 : ℝ))

theorem tendsto_shortMatchingGap :
    Filter.Tendsto shortMatchingGap Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto
      (fun N : ℕ => (4 + 5 * (2 * mertensFirstConst + 1 / 2) / 6) * (1 / Real.log N))
      Filter.atTop (nhds 0) := by
    have := tendsto_inv_log_nat.const_mul (4 + 5 * (2 * mertensFirstConst + 1 / 2) / 6)
    simpa using this
  have h2 : Filter.Tendsto
      (fun N : ℕ => 17 * Real.exp (4 * mertensSecondUpperConst)
        * ((Real.log N) ^ (4 : ℝ) / (N : ℝ) ^ (1 : ℝ))) Filter.atTop (nhds 0) := by
    have := tendsto_log_rpow_div_id.const_mul (17 * Real.exp (4 * mertensSecondUpperConst))
    simpa using this
  have hsum := h1.add h2
  unfold shortMatchingGap
  simpa using hsum

/-- **The relative loss eventually falls below the headroom.** -/
theorem eventually_shortMatchingGap_le :
    ∀ᶠ N : ℕ in Filter.atTop, shortMatchingGap N ≤ Real.log 3 - Real.log 2 := by
  have hpos : (0 : ℝ) < Real.log 3 - Real.log 2 := by
    have := Real.log_lt_log (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) < 3)
    linarith
  exact Filter.Tendsto.eventually_le_const hpos tendsto_shortMatchingGap

/-- **The matching in a short window, at every large scale.**  The window `(X, X+H]` sits at height
`X = N⁴ − N³` and has length `H = N³`, so the displacement bound is a genuine restriction: each
prime moves by less than `X^{3/4}`. -/
theorem eventually_exists_hall_injection_short :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∃ f : ℕ → ℕ,
        Set.InjOn f
          ↑{p ∈ Finset.Ioc ((N * N) * (N * N) - N * (N * N))
              (((N * N) * (N * N) - N * (N * N)) + N * (N * N)) | p.Prime ∧ N < p}
        ∧ (∀ x ∈ {p ∈ Finset.Ioc ((N * N) * (N * N) - N * (N * N))
              (((N * N) * (N * N) - N * (N * N)) + N * (N * N)) | p.Prime ∧ N < p},
            f x ∈ RHTower.markerBlockTargets (bigPrimeSet (N * N) (N * (N * N)))
              (windowCell ((N * N) * (N * N) - N * (N * N)) (N * (N * N))))
        ∧ ∀ x ∈ {p ∈ Finset.Ioc ((N * N) * (N * N) - N * (N * N))
              (((N * N) * (N * N) - N * (N * N)) + N * (N * N)) | p.Prime ∧ N < p},
            |(f x : ℤ) - (x : ℤ)| ≤ ((N * (N * N) : ℕ) : ℤ) := by
  filter_upwards [eventually_shortMatchingGap_le, Filter.eventually_ge_atTop 3] with N hgap hN
  have hN2 : 2 ≤ N := by omega
  have hnR : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hMM : 3 ≤ N * N := by nlinarith
  have hNM : N ≤ N * N := Nat.le_mul_of_pos_left N (by omega)
  have hcube : N * (N * N) ≤ (N * N) * (N * N) := Nat.mul_le_mul_right _ hNM
  have hc2 : ((N * N : ℕ) : ℝ) = (N : ℝ) ^ 2 := by push_cast; ring
  have hc3 : ((N * (N * N) : ℕ) : ℝ) = (N : ℝ) ^ 3 := by push_cast; ring
  have hlogM : Real.log ((N * N : ℕ) : ℝ) = 2 * Real.log N := by
    rw [hc2, Real.log_pow]; push_cast; ring
  have hlog3 : Real.log ((N * (N * N) : ℕ) : ℝ) = 3 * Real.log N := by
    rw [hc3, Real.log_pow]; push_cast; ring
  have hhead : logLog (N * (N * N)) - logLog (N * N) = Real.log 3 - Real.log 2 :=
    logLog_cube_sub_sq hN2
  have hrp1 : (N : ℝ) ^ (1 : ℝ) = (N : ℝ) := Real.rpow_one _
  have hP16 : (Real.log ((N * N : ℕ) : ℝ)) ^ (4 : ℝ) = 16 * (Real.log N) ^ (4 : ℝ) := by
    rw [hlogM, Real.mul_rpow (by norm_num) hL.le]
    norm_num
  have hkey : (N : ℝ) ^ 3 * (4 + 5 * (2 * mertensFirstConst + 1 / 2) / 6) * (1 / Real.log N)
      + 17 * Real.exp (4 * mertensSecondUpperConst) * ((N : ℝ) ^ 2 * (Real.log N) ^ (4 : ℝ))
      ≤ (N : ℝ) ^ 3 * (Real.log 3 - Real.log 2) := by
    have hmul := mul_le_mul_of_nonneg_left hgap (show (0 : ℝ) ≤ (N : ℝ) ^ 3 by positivity)
    unfold shortMatchingGap at hmul
    rw [hrp1] at hmul
    have hrw : (N : ℝ) ^ 3 * ((4 + 5 * (2 * mertensFirstConst + 1 / 2) / 6) * (1 / Real.log N)
          + 17 * Real.exp (4 * mertensSecondUpperConst) * ((Real.log N) ^ (4 : ℝ) / (N : ℝ)))
        = (N : ℝ) ^ 3 * (4 + 5 * (2 * mertensFirstConst + 1 / 2) / 6) * (1 / Real.log N)
          + 17 * Real.exp (4 * mertensSecondUpperConst)
              * ((N : ℝ) ^ 2 * (Real.log N) ^ (4 : ℝ)) := by
      field_simp
    rw [hrw] at hmul
    exact hmul
  have hgoal : 2 * (N : ℝ) ^ 3 / Real.log N
      + (N : ℝ) ^ 2 * (Real.exp (4 * mertensSecondUpperConst) * (Real.log N) ^ (4 : ℝ))
      + (2 * ((N : ℝ) ^ 3 - (N : ℝ) ^ 2) / Real.log N
          + (N : ℝ) ^ 2 * (Real.exp (4 * mertensSecondUpperConst)
              * (16 * (Real.log N) ^ (4 : ℝ))))
      + (N : ℝ) ^ 3 * ((2 * mertensFirstConst + 1 / 2) / (3 * Real.log N)
          + (2 * mertensFirstConst + 1 / 2) / (2 * Real.log N))
      ≤ (N : ℝ) ^ 3 * (Real.log 3 - Real.log 2) := by
    have e1 : 2 * (N : ℝ) ^ 3 / Real.log N
        + (N : ℝ) ^ 2 * (Real.exp (4 * mertensSecondUpperConst) * (Real.log N) ^ (4 : ℝ))
        + (2 * ((N : ℝ) ^ 3 - (N : ℝ) ^ 2) / Real.log N
            + (N : ℝ) ^ 2 * (Real.exp (4 * mertensSecondUpperConst)
                * (16 * (Real.log N) ^ (4 : ℝ))))
        + (N : ℝ) ^ 3 * ((2 * mertensFirstConst + 1 / 2) / (3 * Real.log N)
            + (2 * mertensFirstConst + 1 / 2) / (2 * Real.log N))
        = (N : ℝ) ^ 3 * (4 + 5 * (2 * mertensFirstConst + 1 / 2) / 6) * (1 / Real.log N)
          - 2 * (N : ℝ) ^ 2 * (1 / Real.log N)
          + 17 * Real.exp (4 * mertensSecondUpperConst)
              * ((N : ℝ) ^ 2 * (Real.log N) ^ (4 : ℝ)) := by
      field_simp
      ring
    rw [e1]
    have hpos : 0 ≤ 2 * (N : ℝ) ^ 2 * (1 / Real.log N) := by positivity
    linarith [hkey]
  exact exists_hall_injection_full (X := (N * N) * (N * N) - N * (N * N))
    (H := N * (N * N)) (M := N * N) (Q := N) (z := N) (Y := N) (W := N)
    hMM (by omega) (by rw [Nat.sub_add_cancel hcube]) (by omega) le_rfl hN2 hL
    (by omega) hNM hL
    (by
      rw [hhead, hP16, hlog3, hlogM, hc3, hc2]
      linarith [hgoal])

/-- **The block occupies a positive proportion of the short window.**  This is the quantitative
content behind the injection, and it does not depend on the source set being inhabited: the marker
block alone contains at least `((log 3 − log 2)/2)·H` integers of the window. -/
theorem eventually_card_markerBlockTargets_ge :
    ∀ᶠ N : ℕ in Filter.atTop,
      (N : ℝ) ^ 3 * ((Real.log 3 - Real.log 2) / 2)
        ≤ (((RHTower.markerBlockTargets (bigPrimeSet (N * N) (N * (N * N)))
              (windowCell ((N * N) * (N * N) - N * (N * N)) (N * (N * N)))).card : ℕ) : ℝ) := by
  have hhalf : (0 : ℝ) < (Real.log 3 - Real.log 2) / 2 := by
    have := Real.log_lt_log (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) < 3)
    linarith
  filter_upwards [Filter.Tendsto.eventually_le_const hhalf tendsto_shortMatchingGap,
    Filter.eventually_ge_atTop 3] with N hgap hN
  have hN2 : 2 ≤ N := by omega
  have hnR : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hMM : 3 ≤ N * N := by nlinarith
  have hNM : N ≤ N * N := Nat.le_mul_of_pos_left N (by omega)
  have hcube : N * (N * N) ≤ (N * N) * (N * N) := Nat.mul_le_mul_right _ hNM
  have hXH : ((N * N) * (N * N) - N * (N * N)) + N * (N * N) = (N * N) * (N * N) :=
    Nat.sub_add_cancel hcube
  have hppos : ∀ p ∈ bigPrimeSet (N * N) (N * (N * N)), 0 < p := fun p hp =>
    (prime_of_mem_bigPrimeSet hp).pos
  have hsmall : ∀ p ∈ bigPrimeSet (N * N) (N * (N * N)),
      ∀ a ∈ windowCell ((N * N) * (N * N) - N * (N * N)) (N * (N * N)) p,
      ∀ r ∈ bigPrimeSet (N * N) (N * (N * N)), a < r := by
    intro p hp a ha r hr
    have hprod := ((mem_windowCell_iff (hppos p hp)).1 ha).2
    have hMp : N * N < p := lt_of_mem_bigPrimeSet hp
    have hMr : N * N < r := lt_of_mem_bigPrimeSet hr
    rw [hXH] at hprod
    have haM : a ≤ N * N := by
      by_contra hcon
      have h1 : N * N + 1 ≤ a := by omega
      have h2 : N * N + 1 ≤ p := by omega
      have h3 : (N * N + 1) * (N * N + 1) ≤ a * p := Nat.mul_le_mul h1 h2
      nlinarith
    omega
  have hexact : ((RHTower.markerBlockTargets (bigPrimeSet (N * N) (N * (N * N)))
        (windowCell ((N * N) * (N * N) - N * (N * N)) (N * (N * N)))).card : ℕ)
      = ∑ p ∈ bigPrimeSet (N * N) (N * (N * N)),
          (windowCell ((N * N) * (N * N) - N * (N * N)) (N * (N * N)) p).card :=
    RHTower.card_markerBlockTargets _ _ (fun p hp => prime_of_mem_bigPrimeSet hp)
      (fun p hp a ha => pos_of_mem_windowCell (hppos p hp) ha) hsmall
  have hc2 : ((N * N : ℕ) : ℝ) = (N : ℝ) ^ 2 := by push_cast; ring
  have hc3 : ((N * (N * N) : ℕ) : ℝ) = (N : ℝ) ^ 3 := by push_cast; ring
  have hlogM : Real.log ((N * N : ℕ) : ℝ) = 2 * Real.log N := by
    rw [hc2, Real.log_pow]; push_cast; ring
  have hlog3 : Real.log ((N * (N * N) : ℕ) : ℝ) = 3 * Real.log N := by
    rw [hc3, Real.log_pow]; push_cast; ring
  have hP16 : (Real.log ((N * N : ℕ) : ℝ)) ^ (4 : ℝ) = 16 * (Real.log N) ^ (4 : ℝ) := by
    rw [hlogM, Real.mul_rpow (by norm_num) hL.le]
    norm_num
  have hrp1 : (N : ℝ) ^ (1 : ℝ) = (N : ℝ) := Real.rpow_one _
  -- the reciprocal sum from below
  have hMcube : N * N ≤ N * (N * N) := Nat.mul_le_mul_left N hNM
  have hrecip := sum_inv_bigPrimeSet_ge_sharp (z := N * N) (b := N * (N * N)) (by omega) hMcube
  rw [logLog_cube_sub_sq hN2, hlog3, hlogM] at hrecip
  have hD : (2 * mertensFirstConst + 1 / 2) / (3 * Real.log N)
      + (2 * mertensFirstConst + 1 / 2) / (2 * Real.log N)
      = (2 * mertensFirstConst + 1 / 2) * (5 / 6) * (1 / Real.log N) := by
    field_simp
    ring
  rw [hD] at hrecip
  -- the marker count from above
  have hcount := card_bigPrimeSet_le_explicit (M := N * N) (b := N * (N * N)) (Y := N)
    hMcube (by omega) hNM (by omega) hL
  rw [hP16, hc3, hc2] at hcount
  -- the cells, summed
  have hcells := sum_card_windowCell_ge (X := (N * N) * (N * N) - N * (N * N))
    (H := N * (N * N)) (bigPrimeSet (N * N) (N * (N * N)))
  rw [hc3] at hcells
  have hcast : (((∑ p ∈ bigPrimeSet (N * N) (N * (N * N)),
        (windowCell ((N * N) * (N * N) - N * (N * N)) (N * (N * N)) p).card : ℕ)) : ℝ)
      = ∑ p ∈ bigPrimeSet (N * N) (N * (N * N)),
          (((windowCell ((N * N) * (N * N) - N * (N * N)) (N * (N * N)) p).card : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hexact, hcast]
  have hmulrecip := mul_le_mul_of_nonneg_left hrecip (show (0:ℝ) ≤ (N:ℝ)^3 by positivity)
  have hEnn : (0:ℝ) ≤ Real.exp (4 * mertensSecondUpperConst) := (Real.exp_pos _).le
  have hPnn : (0:ℝ) ≤ (Real.log N) ^ (4 : ℝ) := Real.rpow_nonneg hL.le _
  have hgap2 : (N : ℝ) ^ 3 * (4 + 5 * (2 * mertensFirstConst + 1 / 2) / 6) * (1 / Real.log N)
      + 17 * Real.exp (4 * mertensSecondUpperConst) * ((N : ℝ) ^ 2 * (Real.log N) ^ (4 : ℝ))
      ≤ (N : ℝ) ^ 3 * ((Real.log 3 - Real.log 2) / 2) := by
    have hmul := mul_le_mul_of_nonneg_left hgap (show (0 : ℝ) ≤ (N : ℝ) ^ 3 by positivity)
    unfold shortMatchingGap at hmul
    rw [hrp1] at hmul
    have hrw : (N : ℝ) ^ 3 * ((4 + 5 * (2 * mertensFirstConst + 1 / 2) / 6) * (1 / Real.log N)
          + 17 * Real.exp (4 * mertensSecondUpperConst) * ((Real.log N) ^ (4 : ℝ) / (N : ℝ)))
        = (N : ℝ) ^ 3 * (4 + 5 * (2 * mertensFirstConst + 1 / 2) / 6) * (1 / Real.log N)
          + 17 * Real.exp (4 * mertensSecondUpperConst)
              * ((N : ℝ) ^ 2 * (Real.log N) ^ (4 : ℝ)) := by
      field_simp
    rw [hrw] at hmul
    exact hmul
  have hn2L : (0:ℝ) ≤ (N : ℝ) ^ 2 * (1 / Real.log N) := by positivity
  have hn3L : (0:ℝ) ≤ (N : ℝ) ^ 3 * (1 / Real.log N) := by positivity
  have hEnP : (0:ℝ) ≤ Real.exp (4 * mertensSecondUpperConst)
      * ((N : ℝ) ^ 2 * (Real.log N) ^ (4 : ℝ)) := by positivity
  set P4 : ℝ := (Real.log (N : ℝ)) ^ (4 : ℝ) with hP4def
  set LL : ℝ := Real.log (N : ℝ) with hLLdef
  calc (N : ℝ) ^ 3 * ((Real.log 3 - Real.log 2) / 2)
      ≤ (N : ℝ) ^ 3 * (Real.log 3 - Real.log 2)
        - ((N : ℝ) ^ 3 * (4 + 5 * (2 * mertensFirstConst + 1 / 2) / 6) * (1 / LL)
          + 17 * Real.exp (4 * mertensSecondUpperConst) * ((N : ℝ) ^ 2 * P4)) := by
        linarith [hgap2]
    _ ≤ (N : ℝ) ^ 3 * (∑ p ∈ bigPrimeSet (N * N) (N * (N * N)), 1 / (p : ℝ))
          - (((bigPrimeSet (N * N) (N * (N * N))).card : ℕ) : ℝ) := by
        ring_nf at hmulrecip hcount hn2L hn3L hEnP ⊢
        linarith
    _ ≤ ∑ p ∈ bigPrimeSet (N * N) (N * (N * N)),
          (((windowCell ((N * N) * (N * N) - N * (N * N)) (N * (N * N)) p).card : ℕ) : ℝ) :=
        hcells

end RHTower.Sieve

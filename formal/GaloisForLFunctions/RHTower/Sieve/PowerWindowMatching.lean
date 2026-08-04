import GaloisForLFunctions.RHTower.Sieve.MarkerSignFlip

/-!
# The window exponent

The marker scale `M` and the marker ratio `Q` set the shape of the window: cofactors below `M`
force `X ≤ M²`, and nonempty cells force `H ≥ QM`.  With `M = N^k` and `Q = N` this gives a window
of length `N^{k+1}` at height `N^{2k}`, that is `H ≍ X^{(k+1)/(2k)}`, while the headroom stays the
positive constant

`logLog(N^{k+1}) − logLog(N^k) = log(k+1) − log k`.

So the block occupies a positive proportion of a window whose length is any fixed power of the
height above `1/2`.  The case `k = 2` is the `X^{3/4}` window; letting `k` grow approaches `X^{1/2}`.
-/

namespace RHTower.Sieve

open Finset Nat Filter

/-- **The headroom of a power window.** -/
theorem logLog_pow_succ_sub {N k : ℕ} (hN : 2 ≤ N) (hk : 1 ≤ k) :
    logLog (N * N ^ k) - logLog (N ^ k) = Real.log (k + 1) - Real.log k := by
  have hnR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hcs : ((N * N ^ k : ℕ) : ℝ) = (N : ℝ) ^ (k + 1) := by push_cast; ring
  have hc2 : ((N * N : ℕ) : ℝ) = (N : ℝ) ^ 2 := by push_cast; ring
  have hck : ((N ^ k : ℕ) : ℝ) = (N : ℝ) ^ k := by push_cast; ring
  unfold logLog
  rw [hcs, hck, Real.log_pow, Real.log_pow]
  have h1 : ((k + 1 : ℕ) : ℝ) * Real.log N = ((k : ℝ) + 1) * Real.log N := by
    push_cast
    ring
  have h2 : ((k : ℕ) : ℝ) * Real.log N = (k : ℝ) * Real.log N := by ring
  rw [h1, h2, Real.log_mul (by linarith) hL.ne', Real.log_mul (by linarith) hL.ne']
  ring

/-- The total relative loss of the criterion at the `k`-th power window. -/
noncomputable def powerMatchingGap (k N : ℕ) : ℝ :=
  (4 + 2 * (2 * mertensFirstConst + 1 / 2) / k) * (1 / Real.log N)
    + (1 + 16 * (k : ℝ) ^ 4) * Real.exp (4 * mertensSecondUpperConst)
        * ((Real.log N) ^ (4 : ℝ) / (N : ℝ) ^ (1 : ℝ))

theorem tendsto_powerMatchingGap (k : ℕ) :
    Filter.Tendsto (powerMatchingGap k) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto
      (fun N : ℕ => (4 + 2 * (2 * mertensFirstConst + 1 / 2) / k) * (1 / Real.log N))
      Filter.atTop (nhds 0) := by
    have := tendsto_inv_log_nat.const_mul (4 + 2 * (2 * mertensFirstConst + 1 / 2) / k)
    simpa using this
  have h2 : Filter.Tendsto
      (fun N : ℕ => (1 + 16 * (k : ℝ) ^ 4) * Real.exp (4 * mertensSecondUpperConst)
        * ((Real.log N) ^ (4 : ℝ) / (N : ℝ) ^ (1 : ℝ))) Filter.atTop (nhds 0) := by
    have := tendsto_log_rpow_div_id.const_mul
      ((1 + 16 * (k : ℝ) ^ 4) * Real.exp (4 * mertensSecondUpperConst))
    simpa using this
  have hsum := h1.add h2
  unfold powerMatchingGap
  simpa using hsum

/-- The headroom of a power window is positive. -/
theorem log_succ_sub_log_pos {k : ℕ} (hk : 1 ≤ k) :
    (0 : ℝ) < Real.log (k + 1) - Real.log k := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have := Real.log_lt_log (by linarith : (0:ℝ) < (k : ℝ)) (by linarith : (k : ℝ) < (k : ℝ) + 1)
  linarith

set_option maxHeartbeats 1000000 in
/-- **The block occupies a positive proportion of a window of length `X^{(k+1)/(2k)}`.**  For every
`k ≥ 2` and every sufficiently large `N`, the marker block of scale `N^k` and ratio `N` fills a
fixed fraction of the window of length `N^{k+1}` at height `N^{2k} − N^{k+1}`. -/
theorem eventually_card_markerBlockTargets_pow_ge {k : ℕ} (hk : 2 ≤ k) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (N : ℝ) ^ (k + 1) * ((Real.log (k + 1) - Real.log k) / 2)
        ≤ (((RHTower.markerBlockTargets (bigPrimeSet (N ^ k) (N * N ^ k))
              (windowCell (N ^ k * N ^ k - N * N ^ k) (N * N ^ k))).card : ℕ) : ℝ) := by
  have hk1 : 1 ≤ k := by omega
  have hhalf : (0 : ℝ) < (Real.log (k + 1) - Real.log k) / 2 := by
    have := log_succ_sub_log_pos hk1
    linarith
  filter_upwards [Filter.Tendsto.eventually_le_const hhalf (tendsto_powerMatchingGap k),
    Filter.eventually_ge_atTop 3] with N hgap hN
  have hN2 : 2 ≤ N := by omega
  have hnR : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hn1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hKR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hK0 : (0 : ℝ) < (k : ℝ) := by linarith
  -- natural-number facts
  have hNk : N ≤ N ^ k := Nat.le_self_pow (by omega) N
  have hMk : 3 ≤ N ^ k := by
    calc 3 ≤ N := hN
      _ ≤ N ^ k := hNk
  have hcube : N * N ^ k ≤ N ^ k * N ^ k := Nat.mul_le_mul_right _ hNk
  have hMcube : N ^ k ≤ N * N ^ k := Nat.le_mul_of_pos_left _ (by omega)
  have hXH : (N ^ k * N ^ k - N * N ^ k) + N * N ^ k = N ^ k * N ^ k :=
    Nat.sub_add_cancel hcube
  -- casts
  have hck : ((N ^ k : ℕ) : ℝ) = (N : ℝ) ^ k := by push_cast; ring
  have hcs : ((N * N ^ k : ℕ) : ℝ) = (N : ℝ) ^ (k + 1) := by push_cast; ring
  have hc2 : ((N * N : ℕ) : ℝ) = (N : ℝ) ^ 2 := by push_cast; ring
  have hlogM : Real.log ((N ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log N := by
    rw [hck, Real.log_pow]
  have hlogH : Real.log ((N * N ^ k : ℕ) : ℝ) = ((k : ℝ) + 1) * Real.log N := by
    rw [hcs, Real.log_pow]
    push_cast
    ring
  have hhead : logLog (N * N ^ k) - logLog (N ^ k)
      = Real.log ((k : ℝ) + 1) - Real.log k := by
    have := logLog_pow_succ_sub hN2 hk1
    exact this
  have hP4 : (Real.log ((N ^ k : ℕ) : ℝ)) ^ (4 : ℝ)
      = (k : ℝ) ^ 4 * (Real.log N) ^ (4 : ℝ) := by
    rw [hlogM, Real.mul_rpow hK0.le hL.le]
    congr 1
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hrp1 : (N : ℝ) ^ (1 : ℝ) = (N : ℝ) := Real.rpow_one _
  -- the three estimates
  have hppos : ∀ p ∈ bigPrimeSet (N ^ k) (N * N ^ k), 0 < p := fun p hp =>
    (prime_of_mem_bigPrimeSet hp).pos
  have hsmall : ∀ p ∈ bigPrimeSet (N ^ k) (N * N ^ k),
      ∀ a ∈ windowCell (N ^ k * N ^ k - N * N ^ k) (N * N ^ k) p,
      ∀ r ∈ bigPrimeSet (N ^ k) (N * N ^ k), a < r := by
    intro p hp a ha r hr
    have hprod := ((mem_windowCell_iff (hppos p hp)).1 ha).2
    have hMp : N ^ k < p := lt_of_mem_bigPrimeSet hp
    have hMr : N ^ k < r := lt_of_mem_bigPrimeSet hr
    rw [hXH] at hprod
    have haM : a ≤ N ^ k := by
      by_contra hcon
      have h1 : N ^ k + 1 ≤ a := by omega
      have h2 : N ^ k + 1 ≤ p := by omega
      have h3 : (N ^ k + 1) * (N ^ k + 1) ≤ a * p := Nat.mul_le_mul h1 h2
      nlinarith
    omega
  have hexact : ((RHTower.markerBlockTargets (bigPrimeSet (N ^ k) (N * N ^ k))
        (windowCell (N ^ k * N ^ k - N * N ^ k) (N * N ^ k))).card : ℕ)
      = ∑ p ∈ bigPrimeSet (N ^ k) (N * N ^ k),
          (windowCell (N ^ k * N ^ k - N * N ^ k) (N * N ^ k) p).card :=
    RHTower.card_markerBlockTargets _ _ (fun p hp => prime_of_mem_bigPrimeSet hp)
      (fun p hp a ha => pos_of_mem_windowCell (hppos p hp) ha) hsmall
  have hcast : (((∑ p ∈ bigPrimeSet (N ^ k) (N * N ^ k),
        (windowCell (N ^ k * N ^ k - N * N ^ k) (N * N ^ k) p).card : ℕ)) : ℝ)
      = ∑ p ∈ bigPrimeSet (N ^ k) (N * N ^ k),
          (((windowCell (N ^ k * N ^ k - N * N ^ k) (N * N ^ k) p).card : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hexact, hcast]
  have hrecip := sum_inv_bigPrimeSet_ge_sharp (z := N ^ k) (b := N * N ^ k) (by omega) hMcube
  rw [hhead, hlogH, hlogM] at hrecip
  have hcount := card_bigPrimeSet_le_explicit (M := N ^ k) (b := N * N ^ k) (Y := N)
    hMcube (by omega) hNk (by omega) hL
  rw [hP4, hcs, hck, hc2] at hcount
  have hcells := sum_card_windowCell_ge (X := N ^ k * N ^ k - N * N ^ k)
    (H := N * N ^ k) (bigPrimeSet (N ^ k) (N * N ^ k))
  rw [hcs] at hcells
  -- assemble
  have hEnn : (0:ℝ) ≤ Real.exp (4 * mertensSecondUpperConst) := (Real.exp_pos _).le
  have hPnn : (0:ℝ) ≤ (Real.log N) ^ (4 : ℝ) := Real.rpow_nonneg hL.le _
  have hmulrecip := mul_le_mul_of_nonneg_left hrecip
    (show (0:ℝ) ≤ (N:ℝ)^(k+1) by positivity)
  have hAnn : (0:ℝ) ≤ 2 * mertensFirstConst + 1 / 2 := by
    have := mertensFirstConst_nonneg
    linarith
  have hgap3 : (N : ℝ) ^ (k + 1) * (4 * (1 / Real.log N))
      + (N : ℝ) ^ (k + 1) * ((2 * (2 * mertensFirstConst + 1 / 2) / (k : ℝ)) * (1 / Real.log N))
      + (N : ℝ) ^ k * ((1 + 16 * (k : ℝ) ^ 4)
          * Real.exp (4 * mertensSecondUpperConst) * (Real.log N) ^ (4 : ℝ))
      ≤ (N : ℝ) ^ (k + 1) * ((Real.log ((k : ℝ) + 1) - Real.log k) / 2) := by
    have hmul := mul_le_mul_of_nonneg_left hgap
      (show (0 : ℝ) ≤ (N : ℝ) ^ (k + 1) by positivity)
    unfold powerMatchingGap at hmul
    rw [hrp1] at hmul
    have hrw : (N : ℝ) ^ (k + 1)
        * ((4 + 2 * (2 * mertensFirstConst + 1 / 2) / (k : ℝ)) * (1 / Real.log N)
          + (1 + 16 * (k : ℝ) ^ 4) * Real.exp (4 * mertensSecondUpperConst)
              * ((Real.log N) ^ (4 : ℝ) / (N : ℝ)))
        = (N : ℝ) ^ (k + 1) * (4 * (1 / Real.log N))
          + (N : ℝ) ^ (k + 1)
              * ((2 * (2 * mertensFirstConst + 1 / 2) / (k : ℝ)) * (1 / Real.log N))
          + (N : ℝ) ^ k * ((1 + 16 * (k : ℝ) ^ 4)
              * Real.exp (4 * mertensSecondUpperConst) * (Real.log N) ^ (4 : ℝ)) := by
      field_simp
      ring
    rw [hrw] at hmul
    linarith only [hmul]
  -- the Mertens loss is dominated by the gap's first term
  have hA : (2 * mertensFirstConst + 1 / 2) / (((k : ℝ) + 1) * Real.log N)
      + (2 * mertensFirstConst + 1 / 2) / ((k : ℝ) * Real.log N)
      ≤ (2 * (2 * mertensFirstConst + 1 / 2) / (k : ℝ)) * (1 / Real.log N) := by
    have hstep : (2 * mertensFirstConst + 1 / 2) / (((k : ℝ) + 1) * Real.log N)
        ≤ (2 * mertensFirstConst + 1 / 2) / ((k : ℝ) * Real.log N) := by
      refine div_le_div_of_nonneg_left hAnn (by positivity) ?_
      nlinarith
    have heq : (2 * (2 * mertensFirstConst + 1 / 2) / (k : ℝ)) * (1 / Real.log N)
        = (2 * mertensFirstConst + 1 / 2) / ((k : ℝ) * Real.log N)
          + (2 * mertensFirstConst + 1 / 2) / ((k : ℝ) * Real.log N) := by
      field_simp
      ring
    linarith only [hstep, heq.le, heq.ge]
  -- the Selberg error is dominated by the gap's second term
  have hn2k : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ k := pow_le_pow_right₀ hn1 hk
  have hB : (N : ℝ) ^ 2 * (Real.exp (4 * mertensSecondUpperConst)
        * ((k : ℝ) ^ 4 * (Real.log N) ^ (4 : ℝ)))
      ≤ (N : ℝ) ^ k * ((1 + 16 * (k : ℝ) ^ 4)
          * Real.exp (4 * mertensSecondUpperConst) * (Real.log N) ^ (4 : ℝ)) := by
    have h1 : (N : ℝ) ^ 2 * (Real.exp (4 * mertensSecondUpperConst)
          * ((k : ℝ) ^ 4 * (Real.log N) ^ (4 : ℝ)))
        ≤ (N : ℝ) ^ k * (Real.exp (4 * mertensSecondUpperConst)
          * ((k : ℝ) ^ 4 * (Real.log N) ^ (4 : ℝ))) := by
      refine mul_le_mul_of_nonneg_right hn2k ?_
      positivity
    have h2 : (N : ℝ) ^ k * (Real.exp (4 * mertensSecondUpperConst)
          * ((k : ℝ) ^ 4 * (Real.log N) ^ (4 : ℝ)))
        ≤ (N : ℝ) ^ k * ((1 + 16 * (k : ℝ) ^ 4)
          * Real.exp (4 * mertensSecondUpperConst) * (Real.log N) ^ (4 : ℝ)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      nlinarith [Real.exp_pos (4 * mertensSecondUpperConst), hPnn,
        pow_nonneg hK0.le 4, mul_nonneg (mul_nonneg hEnn (pow_nonneg hK0.le 4)) hPnn]
    linarith only [h1, h2]
  -- the floor loss is dominated by the gap's constant term
  have hC : 2 * ((N : ℝ) ^ (k + 1) - (N : ℝ) ^ k) / Real.log N
      ≤ (N : ℝ) ^ (k + 1) * (4 * (1 / Real.log N)) := by
    have hpk : (0:ℝ) ≤ (N : ℝ) ^ k := by positivity
    have hpk1 : (0:ℝ) ≤ (N : ℝ) ^ (k + 1) := by positivity
    have hnum : 2 * ((N : ℝ) ^ (k + 1) - (N : ℝ) ^ k) ≤ 4 * (N : ℝ) ^ (k + 1) := by
      linarith only [hpk, hpk1]
    have heq : (N : ℝ) ^ (k + 1) * (4 * (1 / Real.log N))
        = 4 * (N : ℝ) ^ (k + 1) / Real.log N := by
      field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right hnum hL.le
  calc (N : ℝ) ^ (k + 1) * ((Real.log ((k : ℝ) + 1) - Real.log k) / 2)
      ≤ (N : ℝ) ^ (k + 1) * (Real.log ((k : ℝ) + 1) - Real.log k)
        - ((N : ℝ) ^ (k + 1) * (4 * (1 / Real.log N))
          + (N : ℝ) ^ (k + 1)
              * ((2 * (2 * mertensFirstConst + 1 / 2) / (k : ℝ)) * (1 / Real.log N))
          + (N : ℝ) ^ k * ((1 + 16 * (k : ℝ) ^ 4)
              * Real.exp (4 * mertensSecondUpperConst) * (Real.log N) ^ (4 : ℝ))) := by
        linarith only [hgap3]
    _ ≤ (N : ℝ) ^ (k + 1) * (∑ p ∈ bigPrimeSet (N ^ k) (N * N ^ k), 1 / (p : ℝ))
          - (((bigPrimeSet (N ^ k) (N * N ^ k)).card : ℕ) : ℝ) := by
        have hmulA := mul_le_mul_of_nonneg_left hA
          (show (0:ℝ) ≤ (N:ℝ)^(k+1) by positivity)
        rw [mul_sub] at hmulrecip
        linarith only [hmulrecip, hcount, hmulA, hB, hC]
    _ ≤ ∑ p ∈ bigPrimeSet (N ^ k) (N * N ^ k),
          (((windowCell (N ^ k * N ^ k - N * N ^ k) (N * N ^ k) p).card : ℕ) : ℝ) := hcells

end RHTower.Sieve

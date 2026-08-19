import GaloisForLFunctions.RHTower.Sieve.GenericMarkerAnalytic
import GaloisForLFunctions.RHTower.Sieve.FreeScaleWindowCount
import GaloisForLFunctions.RHTower.Sieve.FreeScaleHarmonic

/-!
# The free-scale marker device at explicit parameters

Every analytic input of `Sieve/FreeScaleWindowCount.free_card_sign_window_ge_bounds` is discharged
here at the parameters `m = 2^{K₀+1}u`, `M = X/m`, leaving three numerical inequalities `T₁`, `T₂`,
`T₃` between the exceptional-start density `ε`, the number of blocks `K₀`, the base `M` and the
smallest start `u`.  The essential feature is that `T₂` — the dominant term, coming from the
shifted-pair budget — is a *scale-free* inequality between constants: the `(log M)²` of the pair
sieve cancels the `(log M)²` of the squared harmonic mass exactly.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- **The top of a free-scale marker range is at most `2^{K₀+2}` times its base.** -/
theorem freeRange_top_le {X u K₀ : ℕ} (hu : 0 < u) (hM1 : 1 ≤ X / (2 ^ (K₀ + 1) * u)) :
    X / u ≤ 2 ^ (K₀ + 2) * (X / (2 ^ (K₀ + 1) * u)) := by
  set q : ℕ := 2 ^ (K₀ + 1) with hq
  have hq0 : 0 < q := by rw [hq]; positivity
  have hqu : 0 < q * u := Nat.mul_pos hq0 hu
  set M : ℕ := X / (q * u) with hM
  have hlt : X < (M + 1) * (q * u) := (Nat.div_lt_iff_lt_mul hqu).1 (Nat.lt_succ_self _)
  have hlt' : X < ((M + 1) * q) * u := by rw [mul_assoc]; exact hlt
  have hdiv : X / u < (M + 1) * q := (Nat.div_lt_iff_lt_mul hu).2 hlt'
  have hstep : (M + 1) * q ≤ (2 * M) * q := Nat.mul_le_mul_right q (by omega)
  have hpow : (2 : ℕ) ^ (K₀ + 2) = 2 * q := by rw [hq, pow_succ]; ring
  have hcomm : 2 * M * q = 2 * q * M := by ring
  rw [hpow]
  omega

set_option maxHeartbeats 1600000 in
/-- **The free-scale marker device at explicit parameters.**  `T₁` compares the number of markers
with the squared harmonic mass, `T₂` the shifted-pair budget, `T₃` the sieve remainder. -/
theorem free_count_master {β : ℝ} {K₀ X u m M Mt K H : ℕ} {σ : ℤ} {ε rho : ℝ}
    (hm : m = 2 ^ (K₀ + 1) * u) (hMdef : M = X / m) (hMt : Mt = X / u) (hKdef : K = X / (u * u))
    (hu : 0 < u) (hσ : σ = 1 ∨ σ = -1) (hε : 0 ≤ ε) (hrho : 0 ≤ rho)
    (hharm : 0 < multiHarmConst K₀)
    (hM2 : 2 ≤ M)
    (hlogM : markerLogBound K₀ ≤ Real.log (M : ℝ))
    (hbt : Real.exp (4 * mertensSecondUpperConst) * (Real.log (M : ℝ)) ^ 5
      ≤ 32 * 2 ^ (K₀ + 2) * (M : ℝ) ^ ((3 : ℝ) / 4))
    (hXH : X + H ≤ M * M)
    (hmk2 : ∀ k, k ≤ K₀ → 2 ≤ freeStart m k)
    (hfit : ∀ k, k ≤ K₀ → ∀ p ∈ freeBlock X m k, (freeWindow β m k + 1) * (p : ℝ) ≤ (H : ℝ))
    (hsup : ∀ k, k ≤ K₀ → ∀ p ∈ freeBlock X m k,
      rho * ((H : ℝ) / (p : ℝ) - 1) ≤ (3 / 16) * squarefreeDensity * (freeWindow β m k / 2 - 1))
    (hEbad : (((freeBadStartUnion β m K₀).card : ℕ) : ℝ) ≤ ε * (m : ℝ))
    (hT1 : 192 * ε * (2 : ℝ) ^ (2 * K₀ + 4) * (u : ℝ) * Real.log (M : ℝ)
      ≤ (M : ℝ) * (multiHarmConst K₀ / 2) ^ 2)
    (hT2 : 6 * ε * pairMainConst * (2 : ℝ) ^ (3 * K₀ + 6) ≤ (multiHarmConst K₀ / 2) ^ 2)
    (hT3 : 12 * ε * (2 : ℝ) ^ (2 * K₀ + 4) * (Real.log (M : ℝ)) ^ 2
      ≤ (multiHarmConst K₀ / 2) ^ 2 * (M : ℝ) ^ ((1 : ℝ) / 4)) :
    rho * ((H : ℝ) * (multiHarmConst K₀ / (2 * Real.log (M : ℝ)))
        - 64 * 2 ^ (K₀ + 2) * (M : ℝ) / Real.log (M : ℝ))
      ≤ ((((Finset.Ioc X (X + H)).filter (fun n => moebius n = σ)).card : ℕ) : ℝ) := by
  classical
  -- the geometry of the start ladder
  have hm0 : 0 < m := by rw [hm]; positivity
  have hdvd : 2 ^ (K₀ + 1) ∣ m := by rw [hm]; exact dvd_pow_mul K₀ u
  have hfs0 : freeStart m 0 = m := freeStart_zero m
  have hfsK : freeStart m (K₀ + 1) = u := by
    rw [hm, freeStart_pow_mul (le_refl _)]
    simp
  have hposK : 0 < freeStart m (K₀ + 1) := by rw [hfsK]; exact hu
  have hM' : X / freeStart m 0 = M := by rw [hfs0, hMdef]
  have hMt' : X / freeStart m (K₀ + 1) = Mt := by rw [hfsK, hMt]
  have hM1 : 1 ≤ M := by omega
  have hM0 : 0 < X / freeStart m 0 := by rw [hM']; omega
  have hrange : freeRange X m K₀ = bigPrimeSet M Mt := by rw [freeRange, hM', hMt']
  -- the two-sided span of the marker range
  have hlo : 2 ^ (K₀ + 1) * M ≤ Mt := by
    have := freeRange_top_ge (X := X) (m := m) (K₀ := K₀) hdvd
    rw [hM', hMt'] at this
    exact this
  have hhi : Mt ≤ 2 ^ (K₀ + 2) * M := by
    rw [hMt, hMdef, hm]
    exact freeRange_top_le hu (by rw [← hm, ← hMdef]; exact hM1)
  have hMMt : M ≤ Mt := le_trans (Nat.le_mul_of_pos_left _ (by positivity)) hlo
  -- the logarithm of the base
  set L : ℝ := Real.log (M : ℝ) with hL
  have hbase := markerLogBase_le_bound K₀
  have hbasepos := markerLogBase_pos
  have hL1 : 1 ≤ L := by
    have : markerLogBase ≤ L := le_trans hbase hlogM
    rw [markerLogBase] at this
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    have := mertensFirstConst_nonneg
    linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
  have hMR0 : (0 : ℝ) < (M : ℝ) := by linarith
  have hMtR : (Mt : ℝ) ≤ 2 ^ (K₀ + 2) * (M : ℝ) := by exact_mod_cast hhi
  have hMtR0 : (0 : ℝ) ≤ (Mt : ℝ) := Nat.cast_nonneg _
  have huR : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have huR0 : (0 : ℝ) < (u : ℝ) := by linarith
  set D : ℝ := (2 : ℝ) ^ (K₀ + 2) with hD
  have hD0 : (0 : ℝ) < D := by rw [hD]; positivity
  have hD1 : (1 : ℝ) ≤ D := by rw [hD]; exact one_le_pow₀ (by norm_num)
  -- the number of markers
  have hN : (((freeRange X m K₀).card : ℕ) : ℝ) ≤ 64 * D * (M : ℝ) / L := by
    rw [hrange]
    have hbig16 : 16 * Real.log 2 ≤ L := by
      have : markerLogBase ≤ L := le_trans hbase hlogM
      rw [markerLogBase] at this
      have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
      have := mertensFirstConst_nonneg
      linarith
    exact count_le_generic hM2 hMMt hhi hbig16 hbt
  -- the shifted-pair budget
  have hKle : (K : ℝ) ≤ D * (M : ℝ) / (u : ℝ) := by
    have hsplit : K = X / u / u := by rw [hKdef, Nat.div_div_eq_div_mul]
    have hstep : ((X / u / u : ℕ) : ℝ) ≤ ((X / u : ℕ) : ℝ) / (u : ℝ) := Nat.cast_div_le
    rw [hsplit]
    refine hstep.trans ?_
    rw [div_le_div_iff₀ huR0 huR0, ← hMt]
    nlinarith [hMtR, huR0]
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  have hpair : ∑ d ∈ Finset.Icc 1 K,
      ((((freeRange X m K₀).filter (fun p => p + d ∈ freeRange X m K₀)).card : ℕ) : ℝ)
      ≤ pairMainConst * D ^ 2 * (M : ℝ) ^ 2 / ((u : ℝ) * L ^ 2)
        + 2 * D * (M : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 4) / (u : ℝ) := by
    rw [hrange]
    refine (generic_pair_le' hM2 (le_trans hbase hlogM)).trans ?_
    have h34 : (0 : ℝ) ≤ (M : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hMR0.le _
    have hpc := pairMainConst_pos
    have hone : pairMainConst * (K : ℝ) * (Mt : ℝ) / L ^ 2
        ≤ pairMainConst * D ^ 2 * (M : ℝ) ^ 2 / ((u : ℝ) * L ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : pairMainConst * (K : ℝ) * (Mt : ℝ)
          ≤ pairMainConst * (D * (M : ℝ) / (u : ℝ)) * (D * (M : ℝ)) := by
        have ha : pairMainConst * (K : ℝ) ≤ pairMainConst * (D * (M : ℝ) / (u : ℝ)) :=
          mul_le_mul_of_nonneg_left hKle hpc.le
        have hb : (0 : ℝ) ≤ pairMainConst * (D * (M : ℝ) / (u : ℝ)) := by positivity
        exact mul_le_mul ha hMtR hMtR0 hb
      have hval : pairMainConst * (D * (M : ℝ) / (u : ℝ)) * (D * (M : ℝ)) * ((u : ℝ) * L ^ 2)
          = pairMainConst * D ^ 2 * (M : ℝ) ^ 2 * L ^ 2 := by
        field_simp
        try ring
      have hmul := mul_le_mul_of_nonneg_right h1 (mul_nonneg huR0.le (sq_nonneg L))
      rw [hval] at hmul
      exact hmul
    have htwo : (K : ℝ) * (2 * (M : ℝ) ^ ((3 : ℝ) / 4))
        ≤ 2 * D * (M : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 4) / (u : ℝ) := by
      have hstep : (K : ℝ) * (2 * (M : ℝ) ^ ((3 : ℝ) / 4))
          ≤ (D * (M : ℝ) / (u : ℝ)) * (2 * (M : ℝ) ^ ((3 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_right hKle (by positivity)
      refine hstep.trans (le_of_eq ?_)
      field_simp
      try ring
    linarith [hone, htwo]
  -- the device threshold
  set A : ℝ := multiHarmConst K₀ / 2 with hA
  have hA0 : (0 : ℝ) < A := by rw [hA]; linarith
  set b : ℝ := (M : ℝ) * A / L with hb
  have hb0 : (0 : ℝ) ≤ b := by
    rw [hb]; exact div_nonneg (mul_nonneg hMR0.le hA0.le) hL0.le
  have hE0 : (0 : ℝ) ≤ ε * (m : ℝ) := mul_nonneg hε (Nat.cast_nonneg _)
  have hmR : (m : ℝ) = 2 ^ (K₀ + 1) * (u : ℝ) := by rw [hm]; push_cast; ring
  have hmD : (m : ℝ) = D / 2 * (u : ℝ) := by rw [hmR, hD, pow_succ]; ring
  have hLne : L ≠ 0 := ne_of_gt hL0
  have hune : (u : ℝ) ≠ 0 := ne_of_gt huR0
  have hLsq : (0 : ℝ) < L ^ 2 := pow_pos hL0 2
  have h3L2 : (0 : ℝ) < 3 * L ^ 2 := by linarith
  have hthr : (ε * (m : ℝ))
      * (64 * D * (M : ℝ) / L
        + 2 * (pairMainConst * D ^ 2 * (M : ℝ) ^ 2 / ((u : ℝ) * L ^ 2)
          + 2 * D * (M : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 4) / (u : ℝ))) ≤ b ^ 2 := by
    have hDsq : D ^ 2 = (2 : ℝ) ^ (2 * K₀ + 4) := by
      rw [hD, ← pow_mul]; congr 1; ring
    have hDcube : D ^ 3 = (2 : ℝ) ^ (3 * K₀ + 6) := by
      rw [hD, ← pow_mul]; congr 1; ring
    have h34 : (0 : ℝ) < (M : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hMR0 _
    have hprod : (M : ℝ) ^ ((3 : ℝ) / 4) * (M : ℝ) ^ ((1 : ℝ) / 4) = (M : ℝ) := by
      rw [← Real.rpow_add hMR0]; norm_num
    have hkey1 : 192 * ε * D ^ 2 * (u : ℝ) * L ≤ (M : ℝ) * A ^ 2 := by rw [hDsq, hA]; exact hT1
    have hkey2 : 6 * ε * pairMainConst * D ^ 3 ≤ A ^ 2 := by rw [hDcube, hA]; exact hT2
    have hkey3 : 12 * ε * D ^ 2 * L ^ 2 ≤ A ^ 2 * (M : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [hDsq, hA]; exact hT3
    have hpiece1 : ε * (m : ℝ) * (64 * D * (M : ℝ) / L)
        ≤ (M : ℝ) ^ 2 * A ^ 2 / (3 * L ^ 2) := by
      rw [hmD, le_div_iff₀ h3L2]
      have hexp : ε * (D / 2 * (u : ℝ)) * (64 * D * (M : ℝ) / L) * (3 * L ^ 2)
          = 96 * (ε * D ^ 2 * (u : ℝ) * L * (M : ℝ)) := by
        field_simp
        try ring
      rw [hexp]
      have hnn : (0 : ℝ) ≤ ε * D ^ 2 * (u : ℝ) * L * (M : ℝ) := by
        have h1 : (0 : ℝ) ≤ ε * D ^ 2 := mul_nonneg hε (sq_nonneg D)
        have h2 : (0 : ℝ) ≤ ε * D ^ 2 * (u : ℝ) := mul_nonneg h1 huR0.le
        have h3 : (0 : ℝ) ≤ ε * D ^ 2 * (u : ℝ) * L := mul_nonneg h2 hL0.le
        exact mul_nonneg h3 hMR0.le
      linarith [mul_le_mul_of_nonneg_right hkey1 hMR0.le, hnn]
    have hpiece2 : ε * (m : ℝ) * (2 * (pairMainConst * D ^ 2 * (M : ℝ) ^ 2 / ((u : ℝ) * L ^ 2)))
        ≤ (M : ℝ) ^ 2 * A ^ 2 / (3 * L ^ 2) := by
      rw [hmD, le_div_iff₀ h3L2]
      have hexp : ε * (D / 2 * (u : ℝ))
          * (2 * (pairMainConst * D ^ 2 * (M : ℝ) ^ 2 / ((u : ℝ) * L ^ 2))) * (3 * L ^ 2)
          = 3 * (ε * pairMainConst * D ^ 3 * (M : ℝ) ^ 2) := by
        field_simp
        try ring
      rw [hexp]
      have hnn : (0 : ℝ) ≤ ε * pairMainConst * D ^ 3 * (M : ℝ) ^ 2 := by
        have h1 : (0 : ℝ) ≤ ε * pairMainConst := mul_nonneg hε pairMainConst_pos.le
        have h2 : (0 : ℝ) ≤ ε * pairMainConst * D ^ 3 :=
          mul_nonneg h1 (pow_nonneg hD0.le 3)
        exact mul_nonneg h2 (sq_nonneg _)
      linarith [mul_le_mul_of_nonneg_right hkey2 (sq_nonneg ((M : ℝ))), hnn]
    have hpiece3 : ε * (m : ℝ) * (2 * (2 * D * (M : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 4) / (u : ℝ)))
        ≤ (M : ℝ) ^ 2 * A ^ 2 / (3 * L ^ 2) := by
      rw [hmD, le_div_iff₀ h3L2]
      have hexp : ε * (D / 2 * (u : ℝ))
            * (2 * (2 * D * (M : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 4) / (u : ℝ))) * (3 * L ^ 2)
          = 6 * (ε * D ^ 2 * L ^ 2 * ((M : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 4))) := by
        field_simp
        try ring
      rw [hexp]
      have hmul := mul_le_mul_of_nonneg_right hkey3 (mul_nonneg hMR0.le h34.le)
      have hRHS : A ^ 2 * (M : ℝ) ^ ((1 : ℝ) / 4) * ((M : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 4))
          = A ^ 2 * (M : ℝ) ^ 2 := by
        rw [show A ^ 2 * (M : ℝ) ^ ((1 : ℝ) / 4) * ((M : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 4))
            = A ^ 2 * (M : ℝ) * ((M : ℝ) ^ ((3 : ℝ) / 4) * (M : ℝ) ^ ((1 : ℝ) / 4)) by ring,
          hprod]
        ring
      rw [hRHS] at hmul
      have hnn : (0 : ℝ) ≤ ε * D ^ 2 * L ^ 2 * ((M : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 4)) := by
        have h1 : (0 : ℝ) ≤ ε * D ^ 2 := mul_nonneg hε (sq_nonneg D)
        have h2 : (0 : ℝ) ≤ ε * D ^ 2 * L ^ 2 := mul_nonneg h1 (sq_nonneg L)
        exact mul_nonneg h2 (mul_nonneg hMR0.le h34.le)
      linarith [hmul, hnn]
    have hbsq : b ^ 2 = (M : ℝ) ^ 2 * A ^ 2 / L ^ 2 := by
      rw [hb, div_pow, mul_pow]
    have hsum : (M : ℝ) ^ 2 * A ^ 2 / (3 * L ^ 2) + (M : ℝ) ^ 2 * A ^ 2 / (3 * L ^ 2)
        + (M : ℝ) ^ 2 * A ^ 2 / (3 * L ^ 2) = (M : ℝ) ^ 2 * A ^ 2 / L ^ 2 := by
      have hL2ne : (L : ℝ) ^ 2 ≠ 0 := ne_of_gt hLsq
      field_simp
      try ring
    rw [hbsq, ← hsum]
    have hexpand : ε * (m : ℝ)
        * (64 * D * (M : ℝ) / L
          + 2 * (pairMainConst * D ^ 2 * (M : ℝ) ^ 2 / ((u : ℝ) * L ^ 2)
            + 2 * D * (M : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 4) / (u : ℝ)))
        = ε * (m : ℝ) * (64 * D * (M : ℝ) / L)
          + ε * (m : ℝ) * (2 * (pairMainConst * D ^ 2 * (M : ℝ) ^ 2 / ((u : ℝ) * L ^ 2)))
          + ε * (m : ℝ) * (2 * (2 * D * (M : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 4) / (u : ℝ))) := by
      ring
    rw [hexpand]
    linarith [hpiece1, hpiece2, hpiece3]
  -- the harmonic mass
  have hS : A / L ≤ (∑ p ∈ freeRange X m K₀, 1 / (p : ℝ)) - b / ((X / freeStart m 0 : ℕ) : ℝ) := by
    rw [hrange, hM']
    have hbig : ((K₀ : ℝ) + 1) * Real.log 2 ≤ L := by
      rw [markerLogBound] at hlogM
      linarith [hbasepos]
    have hharmge := harm_ge_generic (K₀ := K₀) hM2 hlo hbig hL1
    have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMR0
    have hbM : b / (M : ℝ) = A / L := by
      rw [hb]
      field_simp
      try ring
    rw [hbM]
    have hAA : multiHarmConst K₀ / L = A / L + A / L := by
      rw [hA]
      field_simp
      try ring
    linarith [hharmge, hAA]
  have hgoal : multiHarmConst K₀ / (2 * L) = A / L := by rw [hA, div_div]
  rw [hgoal]
  exact free_card_sign_window_ge_bounds (rho := rho) (S := A / L) (B := 64 * D * (M : ℝ) / L)
    (E := ε * (m : ℝ)) (N := 64 * D * (M : ℝ) / L)
    (P := pairMainConst * D ^ 2 * (M : ℝ) ^ 2 / ((u : ℝ) * L ^ 2)
      + 2 * D * (M : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 4) / (u : ℝ))
    (b := b) hdvd hσ hposK hM0 (by rw [hM']; exact hXH) hrho hmk2 hfit hsup
    (by rw [hfsK, hKdef]) hpair hEbad hN (le_refl _) hE0 hthr hb0 hS hN

end

end RHTower.Sieve

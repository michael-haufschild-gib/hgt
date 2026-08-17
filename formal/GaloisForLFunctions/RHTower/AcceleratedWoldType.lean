import GaloisForLFunctions.RHTower.EulerHellingerAcceleratedBoundary

/-!
# Accelerated Wold type

The Wold boundary volume `a_N = ∏_{p < N} (1 - 1/p)` tends to zero so slowly that the ordinary
Rees scale cannot separate an essential singularity `exp (C / a_N)` from the reflected Hellinger
sewing cost.  The separating scale is one exponential higher:

`Acc (R) = limsup a_N · ℓ₂ (‖R_N‖)`,     `ℓ₂ y = log (1 + log (1 + y))`.

Every family whose logarithm is bounded by a fixed power of `a_N⁻¹` has accelerated type zero, so
this functional does not see ordinary essential singularities.  It does see the reflected sewing
cost: the accelerated type of `H_N(-c) / H_N(c)` is exactly `2 e^(-γ) c`, a linear function of the
displacement.  Hence no operator family of accelerated type zero, between normed spaces of any
dimension, can carry the drift-`c` prime-valuation vector to its reflection.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The doubly logarithmic scale -/

/-- The doubly logarithmic scale `ℓ₂ y = log (1 + log (1 + y))`. -/
def ell2 (y : ℝ) : ℝ := Real.log (1 + Real.log (1 + y))

theorem one_le_one_add_log_one_add {y : ℝ} (hy : 0 ≤ y) : 1 ≤ 1 + Real.log (1 + y) := by
  have : 0 ≤ Real.log (1 + y) := Real.log_nonneg (by linarith)
  linarith

theorem ell2_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ ell2 y :=
  Real.log_nonneg (one_le_one_add_log_one_add hy)

theorem ell2_mono {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z) : ell2 y ≤ ell2 z := by
  have h1 : (0 : ℝ) < 1 + y := by linarith
  have h2 : Real.log (1 + y) ≤ Real.log (1 + z) := Real.log_le_log h1 (by linarith)
  exact Real.log_le_log (by linarith [one_le_one_add_log_one_add hy]) (by linarith)

/-! ## Accelerated type zero -/

/-- For a positive null sequence, `a · log a⁻¹` tends to zero. -/
theorem tendsto_mul_log_inv_zero {a : ℕ → ℝ} (hpos : ∀ᶠ N in atTop, 0 < a N)
    (ha : Tendsto a atTop (nhds 0)) :
    Tendsto (fun N => a N * Real.log ((a N)⁻¹)) atTop (nhds 0) := by
  have hw : Tendsto a atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within a ha hpos
  have hinv : Tendsto (fun N => (a N)⁻¹) atTop atTop := tendsto_inv_nhdsGT_zero.comp hw
  have hdiv : Tendsto (fun u : ℝ => Real.log u / u) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  refine (hdiv.comp hinv).congr' ?_
  filter_upwards [hpos] with N hN
  simp only [Function.comp_apply]
  rw [div_inv_eq, mul_comm]

/-- **Ordinary essential singularities have accelerated type zero.**  If the logarithm of the family
is bounded by a fixed power of `a_N⁻¹`, the accelerated type vanishes. -/
theorem tendsto_mul_ell2_zero_of_log_le {a : ℕ → ℝ} (hpos : ∀ᶠ N in atTop, 0 < a N)
    (ha : Tendsto a atTop (nhds 0)) {R : ℕ → ℝ} (hR : ∀ N, 0 ≤ R N) {C : ℝ} (hC : 0 ≤ C) {K : ℕ}
    (hbd : ∀ᶠ N in atTop, Real.log (1 + R N) ≤ C * ((a N)⁻¹) ^ K) :
    Tendsto (fun N => a N * ell2 (R N)) atTop (nhds 0) := by
  have hle1 : ∀ᶠ N in atTop, a N ≤ 1 := by
    have := ha.eventually (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [this] with N hN using hN.le
  have hmaj : Tendsto (fun N => a N * Real.log (1 + C)
      + (K : ℝ) * (a N * Real.log ((a N)⁻¹))) atTop (nhds 0) := by
    have h1 : Tendsto (fun N => a N * Real.log (1 + C)) atTop (nhds 0) := by
      simpa using ha.mul_const (Real.log (1 + C))
    have h2 := (tendsto_mul_log_inv_zero hpos ha).const_mul (K : ℝ)
    simpa using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmaj ?_ ?_
  · filter_upwards [hpos] with N hN
    exact mul_nonneg hN.le (ell2_nonneg (hR N))
  · filter_upwards [hpos, hle1, hbd] with N hN hN1 hNb
    have hinv1 : (1 : ℝ) ≤ (a N)⁻¹ := one_le_inv_of_le_one hN hN1
    have hpow : (1 : ℝ) ≤ ((a N)⁻¹) ^ K := one_le_pow₀ hinv1
    have hstep1 : ell2 (R N) ≤ Real.log (1 + C * ((a N)⁻¹) ^ K) := by
      refine Real.log_le_log (by linarith [one_le_one_add_log_one_add (hR N)]) ?_
      linarith
    have hstep2 : (1 : ℝ) + C * ((a N)⁻¹) ^ K ≤ (1 + C) * ((a N)⁻¹) ^ K := by
      nlinarith
    have hposbase : (0 : ℝ) < (a N)⁻¹ := by positivity
    have hstep3 : Real.log ((1 + C) * ((a N)⁻¹) ^ K)
        = Real.log (1 + C) + (K : ℝ) * Real.log ((a N)⁻¹) := by
      rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]
    have hstep4 : ell2 (R N) ≤ Real.log (1 + C) + (K : ℝ) * Real.log ((a N)⁻¹) := by
      refine le_trans hstep1 ?_
      rw [← hstep3]
      exact Real.log_le_log (by positivity) hstep2
    calc a N * ell2 (R N)
        ≤ a N * (Real.log (1 + C) + (K : ℝ) * Real.log ((a N)⁻¹)) :=
          mul_le_mul_of_nonneg_left hstep4 hN.le
      _ = a N * Real.log (1 + C) + (K : ℝ) * (a N * Real.log ((a N)⁻¹)) := by ring

/-! ## The Wold boundary volume -/

theorem mertensPrimeProductBelow_pos (N : ℕ) : 0 < mertensPrimeProductBelow N := by
  refine Finset.prod_pos fun p hp => ?_
  have hprime := Nat.prime_of_mem_primesBelow hp
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
  have : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
    rw [one_div, inv_le_inv₀ (by linarith) (by norm_num)]
    exact h2
  linarith

/-- The Wold boundary volume tends to zero. -/
theorem tendsto_mertensPrimeProductBelow_zero :
    Tendsto (fun N : ℕ => mertensPrimeProductBelow N) atTop (nhds 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdiv := tendsto_mertensPrimeProductBelow_mul_log.div_atTop hlog
  refine hdiv.congr' ?_
  filter_upwards [eventually_gt_atTop 2] with N hN
  have hNr : (2 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hlogN : Real.log (N : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  field_simp

/-! ## The exact accelerated type of the reflected sewing cost -/

theorem logReflectedSewingBelow_nonneg {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2) (N : ℕ) :
    0 ≤ logReflectedSewingBelow c N := by
  have habs : |c| < 1 / 2 := by rw [abs_of_pos hc0]; exact hc
  rw [logReflectedSewingBelow_eq_sum_localSewingLog habs N]
  exact Finset.sum_nonneg fun p hp =>
    (localSewingLog_pos (Nat.prime_of_mem_primesBelow hp) hc0 hc).le

/-- The reflected sewing cost has logarithm tending to infinity. -/
theorem tendsto_logReflectedSewingBelow_atTop {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2) :
    Tendsto (fun N : ℕ => logReflectedSewingBelow c N) atTop atTop := by
  have hL : (0 : ℝ) < 2 * Real.exp (-Real.eulerMascheroniConstant) * c := by positivity
  have hmul := tendsto_mertensProduct_mul_log_logReflectedSewing hc0 hc
  have hinv : Tendsto (fun N : ℕ => (mertensPrimeProductBelow N)⁻¹) atTop atTop := by
    refine tendsto_inv_nhdsGT_zero.comp ?_
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      tendsto_mertensPrimeProductBelow_zero
      (Eventually.of_forall fun N => mertensPrimeProductBelow_pos N)
  have hlog : Tendsto (fun N : ℕ => Real.log (logReflectedSewingBelow c N)) atTop atTop := by
    refine (hmul.mul_atTop hL hinv).congr ?_
    intro N
    have hne : mertensPrimeProductBelow N ≠ 0 := ne_of_gt (mertensPrimeProductBelow_pos N)
    field_simp
  refine tendsto_atTop.mpr fun b => ?_
  filter_upwards [hlog.eventually_ge_atTop (max b 1 + 1)] with N hN
  have hb1 : (1 : ℝ) ≤ Real.log (logReflectedSewingBelow c N) := by
    have : (1 : ℝ) ≤ max b 1 + 1 := by
      have := le_max_right b (1 : ℝ)
      linarith
    linarith
  have hnn := logReflectedSewingBelow_nonneg hc0 hc N
  have hposu : 0 < logReflectedSewingBelow c N := by
    rcases hnn.lt_or_eq with h | h
    · exact h
    · rw [← h] at hb1
      simp at hb1
      linarith
  have hexp : Real.exp (max b 1 + 1) ≤ logReflectedSewingBelow c N := by
    have := Real.exp_le_exp.mpr hN
    rwa [Real.exp_log hposu] at this
  have hlin : max b 1 + 1 ≤ Real.exp (max b 1 + 1) := by
    have := Real.add_one_le_exp (max b 1)
    linarith [Real.exp_le_exp.mpr (show max b 1 ≤ max b 1 + 1 by linarith)]
  have : b ≤ max b 1 + 1 := by
    have := le_max_left b (1 : ℝ)
    linarith
  linarith

/-- **The exact accelerated type of the reflected sewing cost.**  For every drift `0 < c < 1/2`,

`a_N · ℓ₂ (H_N(-c) / H_N(c)) → 2 e^(-γ) c`. -/
theorem tendsto_mertensProduct_mul_ell2_reflectedSewing {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2) :
    Tendsto (fun N : ℕ =>
        mertensPrimeProductBelow N * ell2 (reflectedSewingMultiplierBelow c N))
      atTop (nhds (2 * Real.exp (-Real.eulerMascheroniConstant) * c)) := by
  set L : ℝ := 2 * Real.exp (-Real.eulerMascheroniConstant) * c with hL
  have hlow := tendsto_mertensProduct_mul_log_logReflectedSewing hc0 hc
  have hup : Tendsto (fun N : ℕ => mertensPrimeProductBelow N * Real.log (2 + Real.log 2)
      + mertensPrimeProductBelow N * Real.log (logReflectedSewingBelow c N)) atTop (nhds L) := by
    have h1 : Tendsto (fun N : ℕ =>
        mertensPrimeProductBelow N * Real.log (2 + Real.log 2)) atTop (nhds 0) := by
      simpa using tendsto_mertensPrimeProductBelow_zero.mul_const (Real.log (2 + Real.log 2))
    simpa using h1.add hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [(tendsto_logReflectedSewingBelow_atTop hc0 hc).eventually_ge_atTop 1] with N hN
    refine mul_le_mul_of_nonneg_left ?_ (mertensPrimeProductBelow_pos N).le
    -- `log u ≤ ℓ₂ S` because `log S = u` and `log (1 + S) ≥ log S`
    set u : ℝ := logReflectedSewingBelow c N with hu
    have hSpos : 0 < reflectedSewingMultiplierBelow c N := by
      rw [reflectedSewingMultiplierBelow]
      exact div_pos (primeValuationSquaredHellingerBelow_pos_of_abs_lt
          (by rw [abs_of_neg (by linarith : -c < 0)]; linarith) N)
        (primeValuationSquaredHellingerBelow_pos_of_abs_lt (by rw [abs_of_pos hc0]; exact hc) N)
    have hlogS : Real.log (reflectedSewingMultiplierBelow c N) = u := rfl
    have hSge : (1 : ℝ) ≤ reflectedSewingMultiplierBelow c N := by
      have : Real.exp u ≤ reflectedSewingMultiplierBelow c N := by
        rw [← hlogS, Real.exp_log hSpos]
      have h1u : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp (by linarith)
      linarith
    have hstep : u ≤ Real.log (1 + reflectedSewingMultiplierBelow c N) := by
      rw [← hlogS]
      exact Real.log_le_log hSpos (by linarith)
    exact Real.log_le_log (by linarith) (by linarith)
  · filter_upwards [(tendsto_logReflectedSewingBelow_atTop hc0 hc).eventually_ge_atTop 1] with N hN
    set u : ℝ := logReflectedSewingBelow c N with hu
    have hSpos : 0 < reflectedSewingMultiplierBelow c N := by
      rw [reflectedSewingMultiplierBelow]
      exact div_pos (primeValuationSquaredHellingerBelow_pos_of_abs_lt
          (by rw [abs_of_neg (by linarith : -c < 0)]; linarith) N)
        (primeValuationSquaredHellingerBelow_pos_of_abs_lt (by rw [abs_of_pos hc0]; exact hc) N)
    have hlogS : Real.log (reflectedSewingMultiplierBelow c N) = u := rfl
    have hSge : (1 : ℝ) ≤ reflectedSewingMultiplierBelow c N := by
      have : Real.exp u ≤ reflectedSewingMultiplierBelow c N := by
        rw [← hlogS, Real.exp_log hSpos]
      have h1u : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp (by linarith)
      linarith
    -- `log (1 + S) ≤ log 2 + u`
    have hupper : Real.log (1 + reflectedSewingMultiplierBelow c N) ≤ Real.log 2 + u := by
      have hle : (1 : ℝ) + reflectedSewingMultiplierBelow c N
          ≤ 2 * reflectedSewingMultiplierBelow c N := by linarith
      have := Real.log_le_log (by linarith) hle
      rwa [Real.log_mul (by norm_num) (ne_of_gt hSpos), hlogS] at this
    have hchain : (1 : ℝ) + Real.log (1 + reflectedSewingMultiplierBelow c N)
        ≤ (2 + Real.log 2) * u := by
      have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      nlinarith
    have hfin : ell2 (reflectedSewingMultiplierBelow c N)
        ≤ Real.log (2 + Real.log 2) + Real.log u := by
      have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hpos2 : (0 : ℝ) < 2 + Real.log 2 := by linarith
      have := Real.log_le_log
        (show (0 : ℝ) < 1 + Real.log (1 + reflectedSewingMultiplierBelow c N) by
          have : (0 : ℝ) ≤ Real.log (1 + reflectedSewingMultiplierBelow c N) :=
            Real.log_nonneg (by linarith)
          linarith) hchain
      rwa [Real.log_mul (ne_of_gt hpos2) (by linarith)] at this
    calc mertensPrimeProductBelow N * ell2 (reflectedSewingMultiplierBelow c N)
        ≤ mertensPrimeProductBelow N * (Real.log (2 + Real.log 2) + Real.log u) :=
          mul_le_mul_of_nonneg_left hfin (mertensPrimeProductBelow_pos N).le
      _ = mertensPrimeProductBelow N * Real.log (2 + Real.log 2)
            + mertensPrimeProductBelow N * Real.log u := by ring

/-! ## The universal zero-type no-sewing theorem -/

/-- A bounded operator carrying `v` to `w` has norm at least the ratio of their norms. -/
theorem le_opNorm_of_map_eq {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] (R : E →L[ℝ] F) {v : E} {w : F} (h : R v = w)
    (hv : v ≠ 0) : ‖w‖ / ‖v‖ ≤ ‖R‖ := by
  rw [div_le_iff₀ (norm_pos_iff.mpr hv), ← h]
  exact R.le_opNorm v

/-- **The universal zero-type no-sewing theorem.**  Any family dominating the reflected sewing cost
has accelerated type at least `2 e^(-γ) c` — in particular, no family of accelerated type zero
dominates it.  No restriction on the dimensions of the spaces enters. -/
theorem eventually_lt_mertensProduct_mul_ell2_of_ge {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2)
    {r : ℕ → ℝ} (hr : ∀ᶠ N in atTop, reflectedSewingMultiplierBelow c N ≤ r N)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, 2 * Real.exp (-Real.eulerMascheroniConstant) * c - ε
      < mertensPrimeProductBelow N * ell2 (r N) := by
  have hlim := tendsto_mertensProduct_mul_ell2_reflectedSewing hc0 hc
  have hnear := hlim.eventually
    (eventually_gt_nhds (show 2 * Real.exp (-Real.eulerMascheroniConstant) * c - ε
      < 2 * Real.exp (-Real.eulerMascheroniConstant) * c by linarith))
  filter_upwards [hnear, hr] with N h1 h2
  refine lt_of_lt_of_le h1 ?_
  refine mul_le_mul_of_nonneg_left ?_ (mertensPrimeProductBelow_pos N).le
  refine ell2_mono ?_ h2
  rw [reflectedSewingMultiplierBelow]
  exact le_of_lt (div_pos (primeValuationSquaredHellingerBelow_pos_of_abs_lt
      (by rw [abs_of_neg (by linarith : -c < 0)]; linarith) N)
    (primeValuationSquaredHellingerBelow_pos_of_abs_lt (by rw [abs_of_pos hc0]; exact hc) N))

/-- The limit form of the no-sewing theorem: a dominating family with an accelerated type has that
type at least `2 e^(-γ) c`. -/
theorem le_of_tendsto_mul_ell2_of_ge {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2)
    {r : ℕ → ℝ} (hr : ∀ᶠ N in atTop, reflectedSewingMultiplierBelow c N ≤ r N) {T : ℝ}
    (hT : Tendsto (fun N : ℕ => mertensPrimeProductBelow N * ell2 (r N)) atTop (nhds T)) :
    2 * Real.exp (-Real.eulerMascheroniConstant) * c ≤ T := by
  refine le_of_tendsto_of_tendsto (tendsto_mertensProduct_mul_ell2_reflectedSewing hc0 hc) hT ?_
  filter_upwards [hr] with N h2
  refine mul_le_mul_of_nonneg_left ?_ (mertensPrimeProductBelow_pos N).le
  refine ell2_mono ?_ h2
  rw [reflectedSewingMultiplierBelow]
  exact le_of_lt (div_pos (primeValuationSquaredHellingerBelow_pos_of_abs_lt
      (by rw [abs_of_neg (by linarith : -c < 0)]; linarith) N)
    (primeValuationSquaredHellingerBelow_pos_of_abs_lt (by rw [abs_of_pos hc0]; exact hc) N))

end

end RHTower

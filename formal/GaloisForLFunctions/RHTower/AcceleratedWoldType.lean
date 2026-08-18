import GaloisForLFunctions.RHTower.EulerHellingerAcceleratedBoundary
import Mathlib.Analysis.Complex.Liouville

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
  rw [div_eq_mul_inv, inv_inv, mul_comm]

/-- **Ordinary essential singularities have accelerated type zero.**  If the logarithm of the family
is bounded by a fixed power of `a_N⁻¹`, the accelerated type vanishes. -/
theorem tendsto_mul_ell2_zero_of_log_le {a : ℕ → ℝ} (hpos : ∀ᶠ N in atTop, 0 < a N)
    (ha : Tendsto a atTop (nhds 0)) {R : ℕ → ℝ} (hR : ∀ N, 0 ≤ R N) {C : ℝ} (hC : 0 ≤ C) {K : ℕ}
    (hbd : ∀ᶠ N in atTop, Real.log (1 + R N) ≤ C * ((a N)⁻¹) ^ K) :
    Tendsto (fun N => a N * ell2 (R N)) atTop (nhds 0) := by
  have hle1 : ∀ᶠ N in atTop, a N ≤ 1 := by
    have := ha.eventually (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [this] with N hN using hN
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
    have hinv1 : (1 : ℝ) ≤ (a N)⁻¹ := (one_le_inv₀ hN).mpr hN1
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
    refine ((hmul.pos_mul_atTop hL hinv)).congr ?_
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


/-- **The no-sewing theorem for operator families.**  If a bounded operator carries the drift-`c`
prime-valuation vector to its reflection, with the two Hellinger norms, then its accelerated Wold
type is at least `2 e^(-γ) c`.  The spaces are arbitrary normed spaces, of any dimension, and may
vary with the cutoff. -/
theorem eventually_lt_mertensProduct_mul_ell2_opNorm {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2)
    {E F : ℕ → Type*} [∀ N, NormedAddCommGroup (E N)] [∀ N, NormedSpace ℝ (E N)]
    [∀ N, NormedAddCommGroup (F N)] [∀ N, NormedSpace ℝ (F N)]
    (R : ∀ N, E N →L[ℝ] F N) (v : ∀ N, E N) (w : ∀ N, F N)
    (hRv : ∀ N, R N (v N) = w N)
    (hv : ∀ N, ‖v N‖ = primeValuationSquaredHellingerBelow c N)
    (hw : ∀ N, ‖w N‖ = primeValuationSquaredHellingerBelow (-c) N)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, 2 * Real.exp (-Real.eulerMascheroniConstant) * c - ε
      < mertensPrimeProductBelow N * ell2 ‖R N‖ := by
  refine eventually_lt_mertensProduct_mul_ell2_of_ge hc0 hc (Eventually.of_forall fun N => ?_) hε
  have hcpos : 0 < primeValuationSquaredHellingerBelow c N :=
    primeValuationSquaredHellingerBelow_pos_of_abs_lt (by rw [abs_of_pos hc0]; exact hc) N
  have hvne : v N ≠ 0 := by
    intro hzero
    have := hv N
    rw [hzero, norm_zero] at this
    exact absurd this.symm (ne_of_gt hcpos)
  have hratio := le_opNorm_of_map_eq (R N) (hRv N) hvne
  rwa [hv N, hw N, ← reflectedSewingMultiplierBelow] at hratio


/-! ## Stability of accelerated type zero -/

theorem log_one_add_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.log (1 + x + y) ≤ Real.log (1 + x) + Real.log (1 + y) := by
  have hle : (1 : ℝ) + x + y ≤ (1 + x) * (1 + y) := by nlinarith
  have := Real.log_le_log (by linarith) hle
  rwa [Real.log_mul (by linarith) (by linarith)] at this

theorem ell2_le_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : ell2 (x + y) ≤ ell2 x + ell2 y := by
  have hlx : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  have hly : 0 ≤ Real.log (1 + y) := Real.log_nonneg (by linarith)
  have hstep : Real.log (1 + (x + y)) ≤ Real.log (1 + x) + Real.log (1 + y) := by
    rw [show (1 : ℝ) + (x + y) = 1 + x + y by ring]
    exact log_one_add_add_le hx hy
  have hmono : ell2 (x + y) ≤ Real.log (1 + (Real.log (1 + x) + Real.log (1 + y))) :=
    Real.log_le_log (by linarith [one_le_one_add_log_one_add (show (0:ℝ) ≤ x + y by linarith)])
      (by linarith)
  refine le_trans hmono ?_
  rw [ell2, ell2, show (1 : ℝ) + (Real.log (1 + x) + Real.log (1 + y))
    = 1 + Real.log (1 + x) + Real.log (1 + y) by ring]
  exact log_one_add_add_le hlx hly

/-- **Accelerated type zero is stable under a fixed scalar multiple.**  This is the Cauchy-estimate
step: a fixed multiple `j! r^(-j)` of a compact-uniform type-zero family is still type zero. -/
theorem tendsto_mul_ell2_zero_of_le_const_mul {a : ℕ → ℝ} (hpos : ∀ᶠ N in atTop, 0 < a N)
    (ha : Tendsto a atTop (nhds 0)) {R S : ℕ → ℝ} (hR : ∀ N, 0 ≤ R N) (hS : ∀ N, 0 ≤ S N)
    {C : ℝ} (hC : 0 ≤ C) (hle : ∀ᶠ N in atTop, R N ≤ C * S N)
    (h0 : Tendsto (fun N => a N * ell2 (S N)) atTop (nhds 0)) :
    Tendsto (fun N => a N * ell2 (R N)) atTop (nhds 0) := by
  have hmaj : Tendsto (fun N => a N * ell2 C + a N * ell2 (S N)) atTop (nhds 0) := by
    have h1 : Tendsto (fun N => a N * ell2 C) atTop (nhds 0) := by
      simpa using ha.mul_const (ell2 C)
    simpa using h1.add h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmaj ?_ ?_
  · filter_upwards [hpos] with N hN using mul_nonneg hN.le (ell2_nonneg (hR N))
  · filter_upwards [hpos, hle] with N hN hNle
    have hkey : ell2 (R N) ≤ ell2 C + ell2 (S N) := by
      refine le_trans (ell2_mono (hR N) hNle) ?_
      have hlx : 0 ≤ Real.log (1 + C) := Real.log_nonneg (by linarith)
      have hly : 0 ≤ Real.log (1 + S N) := Real.log_nonneg (by linarith [hS N])
      have hprod : Real.log (1 + C * S N) ≤ Real.log (1 + C) + Real.log (1 + S N) := by
        have hle2 : (1 : ℝ) + C * S N ≤ (1 + C) * (1 + S N) := by nlinarith [hS N]
        have := Real.log_le_log (by nlinarith [hS N]) hle2
        rwa [Real.log_mul (by linarith) (by linarith [hS N])] at this
      have hmono : ell2 (C * S N) ≤ Real.log (1 + (Real.log (1 + C) + Real.log (1 + S N))) :=
        Real.log_le_log
          (by linarith [one_le_one_add_log_one_add (mul_nonneg hC (hS N))]) (by linarith)
      refine le_trans hmono ?_
      rw [ell2, ell2, show (1 : ℝ) + (Real.log (1 + C) + Real.log (1 + S N))
        = 1 + Real.log (1 + C) + Real.log (1 + S N) by ring]
      exact log_one_add_add_le hlx hly
    calc a N * ell2 (R N) ≤ a N * (ell2 C + ell2 (S N)) :=
          mul_le_mul_of_nonneg_left hkey hN.le
      _ = a N * ell2 C + a N * ell2 (S N) := by ring

/-- **Accelerated type zero is stable under finite sums.** -/
theorem tendsto_mul_ell2_zero_of_le_add {a : ℕ → ℝ} (hpos : ∀ᶠ N in atTop, 0 < a N)
    {R S T : ℕ → ℝ} (hR : ∀ N, 0 ≤ R N) (hS : ∀ N, 0 ≤ S N) (hT : ∀ N, 0 ≤ T N)
    (hle : ∀ᶠ N in atTop, R N ≤ S N + T N)
    (hS0 : Tendsto (fun N => a N * ell2 (S N)) atTop (nhds 0))
    (hT0 : Tendsto (fun N => a N * ell2 (T N)) atTop (nhds 0)) :
    Tendsto (fun N => a N * ell2 (R N)) atTop (nhds 0) := by
  have hmaj : Tendsto (fun N => a N * ell2 (S N) + a N * ell2 (T N)) atTop (nhds 0) := by
    simpa using hS0.add hT0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmaj ?_ ?_
  · filter_upwards [hpos] with N hN using mul_nonneg hN.le (ell2_nonneg (hR N))
  · filter_upwards [hpos, hle] with N hN hNle
    have hkey : ell2 (R N) ≤ ell2 (S N) + ell2 (T N) :=
      le_trans (ell2_mono (hR N) hNle) (ell2_le_add (hS N) (hT N))
    calc a N * ell2 (R N) ≤ a N * (ell2 (S N) + ell2 (T N)) :=
          mul_le_mul_of_nonneg_left hkey hN.le
      _ = a N * ell2 (S N) + a N * ell2 (T N) := by ring


/-- **Finite divisor activation cannot create accelerated type.**  If a holomorphic operator-valued
family has accelerated type zero uniformly on the boundary circle of a fixed disc, then every fixed
jet of it at the centre has accelerated type zero.  Cauchy's estimate turns the uniform bound into a
fixed multiple of it, and a fixed multiple does not change zero accelerated type. -/
theorem tendsto_mul_ell2_iteratedDeriv_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {a : ℕ → ℝ} (hpos : ∀ᶠ N in atTop, 0 < a N)
    (ha : Tendsto a atTop (nhds 0)) {T : ℕ → ℂ → F} {ρ : ℂ} {r : ℝ} (hr : 0 < r)
    (hdiff : ∀ N, DiffContOnCl ℂ (T N) (Metric.ball ρ r)) {M : ℕ → ℝ} (hM : ∀ N, 0 ≤ M N)
    (hbd : ∀ N, ∀ z ∈ Metric.sphere ρ r, ‖T N z‖ ≤ M N)
    (h0 : Tendsto (fun N => a N * ell2 (M N)) atTop (nhds 0)) (j : ℕ) :
    Tendsto (fun N => a N * ell2 ‖iteratedDeriv j (T N) ρ‖) atTop (nhds 0) := by
  refine tendsto_mul_ell2_zero_of_le_const_mul hpos ha (fun N => norm_nonneg _) hM
    (C := (j.factorial : ℝ) / r ^ j) (by positivity) (Eventually.of_forall fun N => ?_) h0
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (f := T N) (c := ρ) (R := r) (C := M N) j hr (hdiff N) (hbd N)
  calc ‖iteratedDeriv j (T N) ρ‖ ≤ (j.factorial : ℝ) * M N / r ^ j := hcauchy
    _ = (j.factorial : ℝ) / r ^ j * M N := by ring


/-! ## Accelerated type from the double logarithm -/

/-- **The accelerated type is read off the double logarithm.**  For a family whose logarithm tends
to infinity, the accelerated scale `ℓ₂` and the double logarithm have the same accelerated type. -/
theorem tendsto_mertensProduct_mul_ell2_of_tendsto {S : ℕ → ℝ} {V : ℝ}
    (hSpos : ∀ᶠ N in atTop, 0 < S N)
    (hbig : Tendsto (fun N : ℕ => Real.log (S N)) atTop atTop)
    (hV : Tendsto (fun N : ℕ =>
      mertensPrimeProductBelow N * Real.log (Real.log (S N))) atTop (nhds V)) :
    Tendsto (fun N : ℕ => mertensPrimeProductBelow N * ell2 (S N)) atTop (nhds V) := by
  have hup : Tendsto (fun N : ℕ => mertensPrimeProductBelow N * Real.log (2 + Real.log 2)
      + mertensPrimeProductBelow N * Real.log (Real.log (S N))) atTop (nhds V) := by
    have h1 : Tendsto (fun N : ℕ =>
        mertensPrimeProductBelow N * Real.log (2 + Real.log 2)) atTop (nhds 0) := by
      simpa using tendsto_mertensPrimeProductBelow_zero.mul_const (Real.log (2 + Real.log 2))
    simpa using h1.add hV
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hV hup ?_ ?_
  · filter_upwards [hSpos, hbig.eventually_ge_atTop 1] with N hS hu
    refine mul_le_mul_of_nonneg_left ?_ (mertensPrimeProductBelow_pos N).le
    have hSge : (1 : ℝ) ≤ S N := by
      have hle : Real.exp (Real.log (S N)) ≤ S N := by rw [Real.exp_log hS]
      have : (1 : ℝ) ≤ Real.exp (Real.log (S N)) := Real.one_le_exp (by linarith)
      linarith
    have hstep : Real.log (S N) ≤ Real.log (1 + S N) := Real.log_le_log hS (by linarith)
    exact Real.log_le_log (by linarith) (by linarith)
  · filter_upwards [hSpos, hbig.eventually_ge_atTop 1] with N hS hu
    have hSge : (1 : ℝ) ≤ S N := by
      have hle : Real.exp (Real.log (S N)) ≤ S N := by rw [Real.exp_log hS]
      have : (1 : ℝ) ≤ Real.exp (Real.log (S N)) := Real.one_le_exp (by linarith)
      linarith
    have hupper : Real.log (1 + S N) ≤ Real.log 2 + Real.log (S N) := by
      have hle : (1 : ℝ) + S N ≤ 2 * S N := by linarith
      have := Real.log_le_log (by linarith) hle
      rwa [Real.log_mul (by norm_num) (ne_of_gt hS)] at this
    have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hchain : (1 : ℝ) + Real.log (1 + S N) ≤ (2 + Real.log 2) * Real.log (S N) := by
      nlinarith
    have hfin : ell2 (S N) ≤ Real.log (2 + Real.log 2) + Real.log (Real.log (S N)) := by
      have hpos2 : (0 : ℝ) < 2 + Real.log 2 := by linarith
      have := Real.log_le_log
        (show (0 : ℝ) < 1 + Real.log (1 + S N) by
          have : (0 : ℝ) ≤ Real.log (1 + S N) := Real.log_nonneg (by linarith)
          linarith) hchain
      rwa [Real.log_mul (ne_of_gt hpos2) (by linarith)] at this
    calc mertensPrimeProductBelow N * ell2 (S N)
        ≤ mertensPrimeProductBelow N * (Real.log (2 + Real.log 2) + Real.log (Real.log (S N))) :=
          mul_le_mul_of_nonneg_left hfin (mertensPrimeProductBelow_pos N).le
      _ = mertensPrimeProductBelow N * Real.log (2 + Real.log 2)
            + mertensPrimeProductBelow N * Real.log (Real.log (S N)) := by ring

/-- **Saturation of the accelerated type.**  Every family whose logarithm grows linearly in the
cutoff has accelerated Wold type exactly `e^(-γ)`, whatever the growth constant.  Scalarizing a
reflected displacement therefore erases its magnitude and returns the maximal boundary type. -/
theorem tendsto_mertensProduct_mul_ell2_of_log_linear {S : ℕ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hSpos : ∀ᶠ N in atTop, 0 < S N)
    (hratio : Tendsto (fun N : ℕ => Real.log (S N) / (N : ℝ)) atTop (nhds κ)) :
    Tendsto (fun N : ℕ => mertensPrimeProductBelow N * ell2 (S N)) atTop
      (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
  have hNat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hbig : Tendsto (fun N : ℕ => Real.log (S N)) atTop atTop := by
    refine (hratio.pos_mul_atTop hκ hNat).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNne : ((N : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  have hlogratio : Tendsto (fun N : ℕ => Real.log (Real.log (S N) / (N : ℝ))) atTop
      (nhds (Real.log κ)) := (Real.continuousAt_log (ne_of_gt hκ)).tendsto.comp hratio
  have hzero : Tendsto (fun N : ℕ =>
      mertensPrimeProductBelow N * Real.log (Real.log (S N) / (N : ℝ))) atTop (nhds 0) := by
    simpa using tendsto_mertensPrimeProductBelow_zero.mul hlogratio
  have hsplit : Tendsto (fun N : ℕ =>
      mertensPrimeProductBelow N * Real.log (Real.log (S N))) atTop
      (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
    have hsum := hzero.add tendsto_mertensPrimeProductBelow_mul_log
    rw [zero_add] at hsum
    refine hsum.congr' ?_
    have hpos : ∀ᶠ N : ℕ in atTop, 0 < Real.log (S N) / (N : ℝ) := by
      filter_upwards [hratio.eventually (eventually_gt_nhds hκ)] with N hN using hN
    filter_upwards [hpos, eventually_gt_atTop 1] with N hN hN1
    have hNr : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hNne : ((N : ℝ)) ≠ 0 := by linarith
    have hlogsplit : Real.log (Real.log (S N))
        = Real.log (Real.log (S N) / (N : ℝ)) + Real.log ((N : ℝ)) := by
      rw [← Real.log_mul (ne_of_gt hN) hNne]
      congr 1
      field_simp
    rw [hlogsplit]
    ring
  exact tendsto_mertensProduct_mul_ell2_of_tendsto hSpos hbig hsplit


/-! ## The reflected Wold--Gamma gauge -/

/-- `1 + e^u ≤ 2 e^{|u|}`, the crude two-sided bound behind the gauge estimate. -/
theorem one_add_exp_le (u : ℝ) : 1 + Real.exp u ≤ 2 * Real.exp |u| := by
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu]
    have h1 : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp hu
    linarith
  · rw [abs_of_neg hu]
    have h1 : Real.exp u ≤ 1 := Real.exp_le_one_iff.mpr hu.le
    have h2 : (1 : ℝ) ≤ Real.exp (-u) := Real.one_le_exp (by linarith)
    linarith

/-- **The reflected Wold--Gamma gauge has accelerated type zero.**  Its norm is `exp (2 t / a_N)`,
an ordinary essential singularity relative to the Wold boundary volume, so the accelerated scale
does not see it — for the gauge or for its inverse. -/
theorem tendsto_mertensProduct_mul_ell2_expGauge (t : ℝ) :
    Tendsto (fun N : ℕ => mertensPrimeProductBelow N *
        ell2 (Real.exp (2 * t / mertensPrimeProductBelow N))) atTop (nhds 0) := by
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < mertensPrimeProductBelow N :=
    Filter.Eventually.of_forall fun N => mertensPrimeProductBelow_pos N
  have hle1 : ∀ᶠ N : ℕ in atTop, mertensPrimeProductBelow N ≤ 1 := by
    have := tendsto_mertensPrimeProductBelow_zero.eventually
      (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [this] with N hN using hN
  refine tendsto_mul_ell2_zero_of_log_le hpos tendsto_mertensPrimeProductBelow_zero
    (R := fun N => Real.exp (2 * t / mertensPrimeProductBelow N))
    (fun N => (Real.exp_pos _).le) (C := Real.log 2 + 2 * |t|) (K := 1) (by positivity) ?_
  filter_upwards [hpos, hle1] with N hN hN1
  set a : ℝ := mertensPrimeProductBelow N with hadef
  have hbound : Real.log (1 + Real.exp (2 * t / a)) ≤ Real.log 2 + |2 * t / a| := by
    have h1 := one_add_exp_le (2 * t / a)
    have h2 : Real.log (1 + Real.exp (2 * t / a)) ≤ Real.log (2 * Real.exp |2 * t / a|) :=
      Real.log_le_log (by positivity) h1
    rwa [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at h2
  refine le_trans hbound ?_
  have habs : |2 * t / a| = 2 * |t| / a := by
    rw [abs_div, abs_of_pos hN, abs_mul]
    norm_num
  rw [habs, pow_one]
  have hkey : Real.log 2 + 2 * |t| / a ≤ (Real.log 2 + 2 * |t|) * a⁻¹ := by
    rw [inv_eq_one_div, mul_one_div, le_div_iff₀ hN]
    have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hdiv : 2 * |t| / a * a = 2 * |t| := by field_simp
    nlinarith [hdiv, hlog2, hN1]
  exact hkey



/-- **The accelerated type read backwards.**  A family whose accelerated invariant is at least `κ`
at the cutoff is at least an exponential of an exponential in `a_N⁻¹` there — not a Gamma-type
factor. -/
theorem exp_exp_le_of_mul_ell2_ge {a R κ : ℝ} (ha : 0 < a) (hR : 0 ≤ R)
    (h : κ ≤ a * ell2 R) : Real.exp (Real.exp (κ / a) - 1) - 1 ≤ R := by
  have hdiv : κ / a ≤ ell2 R := by
    rw [div_le_iff₀ ha]
    linarith [h]
  have hpos : (1 : ℝ) ≤ 1 + Real.log (1 + R) := one_le_one_add_log_one_add hR
  have hstep : Real.exp (κ / a) ≤ 1 + Real.log (1 + R) := by
    have := Real.exp_le_exp.mpr hdiv
    rwa [ell2, Real.exp_log (by linarith)] at this
  have hlog : Real.exp (κ / a) - 1 ≤ Real.log (1 + R) := by linarith
  have hfin : Real.exp (Real.exp (κ / a) - 1) ≤ 1 + R := by
    have := Real.exp_le_exp.mpr hlog
    rwa [Real.exp_log (by linarith)] at this
  linarith



/-- **`(14c)`: the compact-uniform gauge bound.**  A comparison built from a unitary factor, an
entry bounded above and below by `C` on the compact set, and the reflected Wold--Gamma gauge has
logarithm at most `log C + 2M/a`, where `M` bounds the real part on the compact set. -/
theorem log_max_gauge_le {C M a t φ : ℝ} (hC : 1 ≤ C) (ha : 0 < a)
    (hφ1 : C⁻¹ ≤ |φ|) (hφ2 : |φ| ≤ C) (ht : |t| ≤ M) :
    Real.log (max (max |φ| (Real.exp (2 * t / a))) (max |φ|⁻¹ (Real.exp (-(2 * t / a)))))
      ≤ Real.log C + 2 * M / a := by
  have hC0 : (0 : ℝ) < C := by linarith
  have hM0 : (0 : ℝ) ≤ M := le_trans (abs_nonneg t) ht
  have hMa : (0 : ℝ) ≤ 2 * M / a := by positivity
  have hφ0 : (0 : ℝ) < |φ| := lt_of_lt_of_le (by positivity) hφ1
  have hinv : |φ|⁻¹ ≤ C := by
    rw [inv_le_comm₀ hφ0 hC0]
    exact hφ1
  have ht1 : 2 * t / a ≤ 2 * M / a := by
    have : t ≤ M := le_trans (le_abs_self t) ht
    gcongr
  have ht2 : -(2 * t / a) ≤ 2 * M / a := by
    have : -t ≤ M := le_trans (neg_le_abs t) ht
    have hstep : -(2 * t / a) = 2 * (-t) / a := by ring
    rw [hstep]
    gcongr
  have hexp1 : Real.exp (2 * t / a) ≤ Real.exp (2 * M / a) := Real.exp_le_exp.mpr ht1
  have hexp2 : Real.exp (-(2 * t / a)) ≤ Real.exp (2 * M / a) := Real.exp_le_exp.mpr ht2
  have hCexp : C ≤ C * Real.exp (2 * M / a) := by
    nlinarith [Real.one_le_exp hMa, hC0]
  have hexpC : Real.exp (2 * M / a) ≤ C * Real.exp (2 * M / a) := by
    nlinarith [Real.exp_pos (2 * M / a), hC]
  have hbound : max (max |φ| (Real.exp (2 * t / a))) (max |φ|⁻¹ (Real.exp (-(2 * t / a))))
      ≤ C * Real.exp (2 * M / a) := by
    refine max_le (max_le (le_trans hφ2 hCexp) (le_trans hexp1 hexpC))
      (max_le (le_trans hinv hCexp) (le_trans hexp2 hexpC))
  refine le_trans (Real.log_le_log (by positivity) hbound) (le_of_eq ?_)
  rw [Real.log_mul (ne_of_gt hC0) (ne_of_gt (Real.exp_pos _)), Real.log_exp]

/-- **`(14)` in compact-uniform form.**  A family whose logarithm obeys `(14c)` with a fixed
constant has accelerated type zero. -/
theorem tendsto_mertensProduct_mul_ell2_zero_of_log_gauge_le {C M : ℝ} (hC : 1 ≤ C) (hM : 0 ≤ M)
    {R : ℕ → ℝ} (hR : ∀ N, 0 ≤ R N)
    (hbd : ∀ᶠ N in atTop, Real.log (1 + R N)
      ≤ Real.log C + 2 * M / mertensPrimeProductBelow N) :
    Tendsto (fun N : ℕ => mertensPrimeProductBelow N * ell2 (R N)) atTop (nhds 0) := by
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < mertensPrimeProductBelow N :=
    Filter.Eventually.of_forall fun N => mertensPrimeProductBelow_pos N
  have hle1 : ∀ᶠ N : ℕ in atTop, mertensPrimeProductBelow N ≤ 1 := by
    have := tendsto_mertensPrimeProductBelow_zero.eventually
      (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [this] with N hN using hN
  have hlogC : (0 : ℝ) ≤ Real.log C := Real.log_nonneg hC
  refine tendsto_mul_ell2_zero_of_log_le hpos tendsto_mertensPrimeProductBelow_zero hR
    (C := Real.log C + 2 * M) (K := 1) (by positivity) ?_
  filter_upwards [hpos, hle1, hbd] with N hN hN1 hNb
  refine le_trans hNb ?_
  rw [pow_one]
  have hinv : (1 : ℝ) ≤ (mertensPrimeProductBelow N)⁻¹ := (one_le_inv₀ hN).mpr hN1
  have hsplit : (Real.log C + 2 * M) * (mertensPrimeProductBelow N)⁻¹
      = Real.log C * (mertensPrimeProductBelow N)⁻¹
        + 2 * M / mertensPrimeProductBelow N := by
    field_simp
  rw [hsplit]
  nlinarith [hlogC, hinv]


end

end RHTower

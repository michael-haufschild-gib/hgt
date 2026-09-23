import GaloisForLFunctions.RHTower.Sieve.RateBridge
import GaloisForLFunctions.RHTower.Sieve.TruncDivisorCount

/-!
# The lower tail with both errors absorbed

`RateBridge.card_omega_le_le_rate` carries three terms: the entropy main term, a tilt error, and a
sieve error.  Neither error is intrinsic.

* The sieve error is `#{d ∣ z# : ω d ≤ r}/t^k`, and `TruncDivisorCount` bounds the numerator by
  `z^r`.
* The tilt error is `exp(λc₁)(log z)^λ/(λ^r t^k)`, which the tilt parameter `λ > 1` drives below the
  main term as soon as `r` is large enough — `λ^r` grows geometrically in `r` while everything else
  is fixed.

Recording that absorption once leaves the lower tail in the shape a parameter optimisation can use:

    #{n ∈ (a,b] : ω n ≤ k}  ≤  2(b−a)·exp((1−t)c₀)·(log z)^{−I(t)}  +  z^r/t^k,

with `I(t) = 1 − t + t log t` the entropy rate, strictly positive for `0 < t < 1`.
-/

namespace RHTower.Sieve

open Finset Filter Topology

/-- **The lower tail with both errors absorbed.**  The hypothesis `habs` is the statement that the
tilt parameter has been taken large enough to bury the tilt error under the main term. -/
theorem card_omega_le_le_absorbed (a b z k r : ℕ) (hab : a ≤ b) (hz : 2 ≤ z) (hr : Even r)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hk : (k : ℝ) = t * logLog z)
    {lam : ℝ} (hlam : 1 ≤ lam)
    (habs : Real.exp (lam * mertensSecondUpperConst) * (Real.log z) ^ lam / (lam ^ r * t ^ k)
      ≤ Real.exp ((1 - t) * mertensSecondLowerConst)
          * (Real.log z) ^ (-woldBreadthDeviationRate t)) :
    ((#{n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k} : ℕ) : ℝ)
      ≤ 2 * ((b : ℝ) - a) * (Real.exp ((1 - t) * mertensSecondLowerConst)
            * (Real.log z) ^ (-woldBreadthDeviationRate t))
        + (z : ℝ) ^ r / t ^ k := by
  have hz1 : 1 ≤ z := by omega
  have hlen : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have htk : (0 : ℝ) < t ^ k := pow_pos ht0 k
  have hbase := card_omega_le_le_rate a b z k r hab hz hr ht0 ht1 hk hlam
  have hmain : ((b : ℝ) - a) * (Real.exp ((1 - t) * mertensSecondLowerConst)
          * (Real.log z) ^ (-woldBreadthDeviationRate t)
        + Real.exp (lam * mertensSecondUpperConst) * (Real.log z) ^ lam / (lam ^ r * t ^ k))
      ≤ 2 * ((b : ℝ) - a) * (Real.exp ((1 - t) * mertensSecondLowerConst)
          * (Real.log z) ^ (-woldBreadthDeviationRate t)) := by
    have hstep : Real.exp ((1 - t) * mertensSecondLowerConst)
            * (Real.log z) ^ (-woldBreadthDeviationRate t)
          + Real.exp (lam * mertensSecondUpperConst) * (Real.log z) ^ lam / (lam ^ r * t ^ k)
        ≤ 2 * (Real.exp ((1 - t) * mertensSecondLowerConst)
            * (Real.log z) ^ (-woldBreadthDeviationRate t)) := by linarith
    have := mul_le_mul_of_nonneg_left hstep hlen
    linarith [this]
  have hsieve : ((truncDivisors (primorial z) r).card : ℝ) / t ^ k ≤ (z : ℝ) ^ r / t ^ k := by
    refine div_le_div_of_nonneg_right ?_ htk.le
    have hnat := card_truncDivisors_primorial_le z r hz1
    have : (((truncDivisors (primorial z) r).card : ℕ) : ℝ) ≤ ((z ^ r : ℕ) : ℝ) := by
      exact_mod_cast hnat
    simpa using this
  linarith

/-- **The absorption hypothesis is satisfiable.**  For any tilt `λ > 1` some even `r` buries the
tilt error, because `λ ^ r` grows without bound while the rest is fixed. -/
theorem exists_even_absorbing (z k : ℕ) (hz : 2 ≤ z) {t : ℝ} (ht0 : 0 < t) {lam : ℝ}
    (hlam : 1 < lam) :
    ∃ r : ℕ, Even r ∧
      Real.exp (lam * mertensSecondUpperConst) * (Real.log z) ^ lam / (lam ^ r * t ^ k)
        ≤ Real.exp ((1 - t) * mertensSecondLowerConst)
            * (Real.log z) ^ (-woldBreadthDeviationRate t) := by
  have hz2 : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos (by linarith)
  have hA0 : (0 : ℝ) < Real.exp ((1 - t) * mertensSecondLowerConst)
      * (Real.log z) ^ (-woldBreadthDeviationRate t) := by positivity
  have hB0 : (0 : ℝ) < Real.exp (lam * mertensSecondUpperConst) * (Real.log z) ^ lam := by
    positivity
  have htk : (0 : ℝ) < t ^ k := pow_pos ht0 k
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt
    ((Real.exp (lam * mertensSecondUpperConst) * (Real.log z) ^ lam)
      / ((Real.exp ((1 - t) * mertensSecondLowerConst)
          * (Real.log z) ^ (-woldBreadthDeviationRate t)) * t ^ k)) hlam
  refine ⟨2 * m, ⟨m, by ring⟩, ?_⟩
  have hmono : lam ^ m ≤ lam ^ (2 * m) := pow_le_pow_right₀ hlam.le (by omega)
  have hkey : (Real.exp (lam * mertensSecondUpperConst) * (Real.log z) ^ lam)
      / ((Real.exp ((1 - t) * mertensSecondLowerConst)
          * (Real.log z) ^ (-woldBreadthDeviationRate t)) * t ^ k) ≤ lam ^ (2 * m) :=
    le_trans hm.le hmono
  rw [div_le_iff₀ (by positivity)] at hkey ⊢
  nlinarith [hkey, hA0, htk, hB0]

/-- **The lower tail, with the tilt error gone.**  Only the entropy main term and the sieve error
`z^r` survive. -/
theorem exists_card_omega_le_le_absorbed (a b z k : ℕ) (hab : a ≤ b) (hz : 2 ≤ z)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hk : (k : ℝ) = t * logLog z) :
    ∃ r : ℕ, ((#{n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k} : ℕ) : ℝ)
      ≤ 2 * ((b : ℝ) - a) * (Real.exp ((1 - t) * mertensSecondLowerConst)
            * (Real.log z) ^ (-woldBreadthDeviationRate t))
        + (z : ℝ) ^ r / t ^ k := by
  obtain ⟨r, hrEven, habs⟩ := exists_even_absorbing z k hz ht0 (by norm_num : (1 : ℝ) < 2)
  exact ⟨r, card_omega_le_le_absorbed a b z k r hab hz hrEven ht0 ht1 hk
    (by norm_num) habs⟩

/-- `t·(−log t) ≤ 1 − t` on `(0,1]`, from `log u ≤ u − 1` at `u = 1/t`. -/
theorem mul_neg_log_le {t : ℝ} (ht0 : 0 < t) : t * (-Real.log t) ≤ 1 - t := by
  have hinv : (0 : ℝ) < 1 / t := by positivity
  have hstep := Real.log_le_sub_one_of_pos hinv
  rw [Real.log_div one_ne_zero (ne_of_gt ht0), Real.log_one, zero_sub] at hstep
  have hmul := mul_le_mul_of_nonneg_left hstep ht0.le
  have hval : t * (1 / t - 1) = 1 - t := by
    field_simp
  linarith [hval ▸ hmul]

/-- **The tilt weight costs at most one logarithm.**  With `k = t·log log z` and `0 < t ≤ 1`,
`t^{-k} ≤ log z`. -/
theorem one_div_pow_le_log {z k : ℕ} (hlogz : (1 : ℝ) ≤ Real.log z) {t : ℝ} (ht0 : 0 < t)
    (hk : (k : ℝ) = t * logLog z) : 1 / t ^ k ≤ Real.log z := by
  have hlogz0 : (0 : ℝ) < Real.log z := by linarith
  have hloglog0 : (0 : ℝ) ≤ logLog z := by
    rw [logLog]
    exact Real.log_nonneg hlogz
  have hpow : t ^ k = Real.exp ((k : ℝ) * Real.log t) := by
    rw [← Real.rpow_natCast t k, Real.rpow_def_of_pos ht0]
    congr 1
    ring
  have hexp : 1 / t ^ k = Real.exp (-((k : ℝ) * Real.log t)) := by
    rw [hpow, one_div, ← Real.exp_neg]
  have hbound : -((k : ℝ) * Real.log t) ≤ logLog z := by
    rw [hk]
    have hstep : t * (-Real.log t) ≤ 1 := by
      have := mul_neg_log_le ht0
      linarith
    have : -(t * logLog z * Real.log t) = (t * (-Real.log t)) * logLog z := by ring
    rw [this]
    nlinarith [hstep, hloglog0]
  rw [hexp]
  refine le_trans (Real.exp_le_exp.2 hbound) (le_of_eq ?_)
  rw [logLog, Real.exp_log hlogz0]

/-- The entropy rate is at most one on `(0,1]`. -/
theorem woldBreadthDeviationRate_le_one {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    woldBreadthDeviationRate t ≤ 1 := by
  rw [woldBreadthDeviationRate]
  have hlog : Real.log t ≤ 0 := Real.log_nonpos (by linarith) ht1
  nlinarith

/-- **An explicit absorbing exponent.**  `2 ^ r ≥ exp(2c₁ + |c₀|)·(log z)^(4 : ℕ)` suffices. -/
theorem absorbing_of_pow_ge {z k r : ℕ} (hlogz : (1 : ℝ) ≤ Real.log z) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t ≤ 1) (hk : (k : ℝ) = t * logLog z)
    (hr : Real.exp (2 * mertensSecondUpperConst + |mertensSecondLowerConst|)
            * (Real.log z) ^ (4 : ℕ) ≤ (2 : ℝ) ^ r) :
    Real.exp (2 * mertensSecondUpperConst) * (Real.log z) ^ (2 : ℝ) / ((2 : ℝ) ^ r * t ^ k)
      ≤ Real.exp ((1 - t) * mertensSecondLowerConst)
          * (Real.log z) ^ (-woldBreadthDeviationRate t) := by
  have hlogz0 : (0 : ℝ) < Real.log z := by linarith
  have htk : (0 : ℝ) < t ^ k := pow_pos ht0 k
  have h2r : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  -- the tilt weight
  have htkinv := one_div_pow_le_log hlogz ht0 hk
  have htklow : 1 / Real.log z ≤ t ^ k := by
    rw [div_le_iff₀ hlogz0]
    rw [div_le_iff₀ htk] at htkinv
    linarith
  -- the entropy weight
  have hrate := woldBreadthDeviationRate_le_one ht0 ht1
  have hexpo : (Real.log z) ^ (-(1 : ℝ)) ≤ (Real.log z) ^ (-woldBreadthDeviationRate t) :=
    Real.rpow_le_rpow_of_exponent_le hlogz (by linarith)
  have hinvlog : (Real.log z) ^ (-(1 : ℝ)) = 1 / Real.log z := by
    rw [Real.rpow_neg_one, one_div]
  -- the constant
  have hconst : Real.exp (-|mertensSecondLowerConst|)
      ≤ Real.exp ((1 - t) * mertensSecondLowerConst) := by
    refine Real.exp_le_exp.2 ?_
    rcases le_or_gt 0 mertensSecondLowerConst with hc | hc
    · have : (0 : ℝ) ≤ (1 - t) * mertensSecondLowerConst := by
        have : (0 : ℝ) ≤ 1 - t := by linarith
        positivity
      have habs : |mertensSecondLowerConst| = mertensSecondLowerConst := abs_of_nonneg hc
      linarith
    · have habs : |mertensSecondLowerConst| = -mertensSecondLowerConst := abs_of_neg hc
      have h1t : (0 : ℝ) ≤ 1 - t := by linarith
      nlinarith
  have hsq : (Real.log z) ^ (2 : ℝ) = (Real.log z) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (Real.log z) 2]
    norm_num
  rw [div_le_iff₀ (by positivity), hsq]
  have hlow : Real.exp (-|mertensSecondLowerConst|) * (1 / Real.log z) * ((2 : ℝ) ^ r
        * (1 / Real.log z))
      ≤ Real.exp ((1 - t) * mertensSecondLowerConst)
          * (Real.log z) ^ (-woldBreadthDeviationRate t) * ((2 : ℝ) ^ r * t ^ k) := by
    have h1 : Real.exp (-|mertensSecondLowerConst|) * (1 / Real.log z)
        ≤ Real.exp ((1 - t) * mertensSecondLowerConst)
            * (Real.log z) ^ (-woldBreadthDeviationRate t) := by
      calc Real.exp (-|mertensSecondLowerConst|) * (1 / Real.log z)
          = Real.exp (-|mertensSecondLowerConst|) * (Real.log z) ^ (-(1 : ℝ)) := by
            rw [hinvlog]
        _ ≤ Real.exp (-|mertensSecondLowerConst|)
              * (Real.log z) ^ (-woldBreadthDeviationRate t) :=
            mul_le_mul_of_nonneg_left hexpo (by positivity)
        _ ≤ Real.exp ((1 - t) * mertensSecondLowerConst)
              * (Real.log z) ^ (-woldBreadthDeviationRate t) :=
            mul_le_mul_of_nonneg_right hconst (by positivity)
    have h2 : (2 : ℝ) ^ r * (1 / Real.log z) ≤ (2 : ℝ) ^ r * t ^ k :=
      mul_le_mul_of_nonneg_left htklow h2r.le
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  refine le_trans ?_ hlow
  have hexpand : Real.exp (-|mertensSecondLowerConst|) * (1 / Real.log z) * ((2 : ℝ) ^ r
        * (1 / Real.log z))
      = Real.exp (-|mertensSecondLowerConst|) * (2 : ℝ) ^ r / (Real.log z) ^ (2 : ℕ) := by
    field_simp
  rw [hexpand, le_div_iff₀ (by positivity)]
  have hkey := mul_le_mul_of_nonneg_left hr (Real.exp_pos (-|mertensSecondLowerConst|)).le
  have hL : Real.exp (-|mertensSecondLowerConst|)
      * (Real.exp (2 * mertensSecondUpperConst + |mertensSecondLowerConst|)
        * (Real.log z) ^ (4 : ℕ))
      = Real.exp (2 * mertensSecondUpperConst) * (Real.log z) ^ (4 : ℕ) := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hL] at hkey
  calc Real.exp (2 * mertensSecondUpperConst) * (Real.log z) ^ (2 : ℕ) * (Real.log z) ^ (2 : ℕ)
      = Real.exp (2 * mertensSecondUpperConst) * (Real.log z) ^ (4 : ℕ) := by ring
    _ ≤ Real.exp (-|mertensSecondLowerConst|) * (2 : ℝ) ^ r := hkey

/-- **The lower tail, fully explicit.**  No `t` survives in the constants and no `t^k` in the
error: the entropy factor `(log z)^{−I(t)}` is the only place the tilt appears. -/
theorem card_omega_le_le_explicit (a b z k r : ℕ) (hab : a ≤ b) (hz : 2 ≤ z)
    (hlogz : (1 : ℝ) ≤ Real.log z) (hrEven : Even r)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hk : (k : ℝ) = t * logLog z)
    (hpow : Real.exp (2 * mertensSecondUpperConst + |mertensSecondLowerConst|)
              * (Real.log z) ^ (4 : ℕ) ≤ (2 : ℝ) ^ r) :
    ((#{n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k} : ℕ) : ℝ)
      ≤ 2 * ((b : ℝ) - a) * (Real.exp |mertensSecondLowerConst|
            * (Real.log z) ^ (-woldBreadthDeviationRate t))
        + (z : ℝ) ^ r * Real.log z := by
  have hlogz0 : (0 : ℝ) < Real.log z := by linarith
  have hlen : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have habs := absorbing_of_pow_ge hlogz ht0 ht1 hk hpow
  have hbase := card_omega_le_le_absorbed a b z k r hab hz hrEven ht0 ht1 hk
    (by norm_num) habs
  -- the constant
  have hconst : Real.exp ((1 - t) * mertensSecondLowerConst)
      ≤ Real.exp |mertensSecondLowerConst| := by
    refine Real.exp_le_exp.2 ?_
    have h1t : (0 : ℝ) ≤ 1 - t := by linarith
    have h1t' : 1 - t ≤ 1 := by linarith
    rcases le_or_gt 0 mertensSecondLowerConst with hc | hc
    · have habs : |mertensSecondLowerConst| = mertensSecondLowerConst := abs_of_nonneg hc
      nlinarith
    · have habs : |mertensSecondLowerConst| = -mertensSecondLowerConst := abs_of_neg hc
      nlinarith
  have hmain : 2 * ((b : ℝ) - a) * (Real.exp ((1 - t) * mertensSecondLowerConst)
        * (Real.log z) ^ (-woldBreadthDeviationRate t))
      ≤ 2 * ((b : ℝ) - a) * (Real.exp |mertensSecondLowerConst|
        * (Real.log z) ^ (-woldBreadthDeviationRate t)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    exact mul_le_mul_of_nonneg_right hconst (by positivity)
  -- the error
  have htkinv := one_div_pow_le_log hlogz ht0 hk
  have htk : (0 : ℝ) < t ^ k := pow_pos ht0 k
  have hzr : (0 : ℝ) ≤ (z : ℝ) ^ r := by positivity
  have herr : (z : ℝ) ^ r / t ^ k ≤ (z : ℝ) ^ r * Real.log z := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left htkinv hzr
  linarith

/-- An even power of two straddling a positive real: the least one above it is below `4C + 1`. -/
theorem exists_even_pow_between (C : ℝ) (hC : 0 < C) :
    ∃ m : ℕ, C ≤ (2 : ℝ) ^ (2 * m) ∧ (2 : ℝ) ^ (2 * m) ≤ 4 * C + 1 := by
  classical
  have hex : ∃ m : ℕ, C ≤ (2 : ℝ) ^ (2 * m) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (by norm_num : (1 : ℝ) < 2)
    exact ⟨n, le_trans hn.le (pow_le_pow_right₀ (by norm_num) (by omega))⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with hm0 | hmpos
  · rw [hm0]
    norm_num
    linarith
  · have hlt : ¬ (C ≤ (2 : ℝ) ^ (2 * (Nat.find hex - 1))) := Nat.find_min hex (by omega)
    push Not at hlt
    have hsplit : (2 : ℝ) ^ (2 * Nat.find hex) = 4 * (2 : ℝ) ^ (2 * (Nat.find hex - 1)) := by
      have hidx : 2 * Nat.find hex = 2 * (Nat.find hex - 1) + 2 := by omega
      rw [hidx, pow_add]
      ring
    rw [hsplit]
    linarith

/-- **The lower tail, fully explicit, with the absorbing exponent supplied.**  The exponent is
`O(log log z)`: `2 ^ r` is pinned between `exp(2c₁+|c₀|)(log z)^(4 : ℕ)` and four times that. -/
theorem exists_card_omega_le_le_explicit (a b z k : ℕ) (hab : a ≤ b) (hz : 2 ≤ z)
    (hlogz : (1 : ℝ) ≤ Real.log z)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hk : (k : ℝ) = t * logLog z) :
    ∃ r : ℕ, (2 : ℝ) ^ r
        ≤ 4 * (Real.exp (2 * mertensSecondUpperConst + |mertensSecondLowerConst|)
            * (Real.log z) ^ (4 : ℕ)) + 1
      ∧ ((#{n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k} : ℕ) : ℝ)
        ≤ 2 * ((b : ℝ) - a) * (Real.exp |mertensSecondLowerConst|
              * (Real.log z) ^ (-woldBreadthDeviationRate t))
          + (z : ℝ) ^ r * Real.log z := by
  have hlogz0 : (0 : ℝ) < Real.log z := by linarith
  have hC : (0 : ℝ) < Real.exp (2 * mertensSecondUpperConst + |mertensSecondLowerConst|)
      * (Real.log z) ^ (4 : ℕ) := by positivity
  obtain ⟨m, hmlow, hmup⟩ := exists_even_pow_between _ hC
  refine ⟨2 * m, hmup, ?_⟩
  exact card_omega_le_le_explicit a b z k (2 * m) hab hz hlogz ⟨m, by ring⟩ ht0 ht1 hk hmlow

/-- **The density form.** -/
theorem card_omega_le_div_le (a b z k r : ℕ) (hab : a ≤ b) (hz : 2 ≤ z)
    (hlogz : (1 : ℝ) ≤ Real.log z) (hrEven : Even r)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hk : (k : ℝ) = t * logLog z)
    (hpow : Real.exp (2 * mertensSecondUpperConst + |mertensSecondLowerConst|)
              * (Real.log z) ^ (4 : ℕ) ≤ (2 : ℝ) ^ r)
    (hH : 0 < (b : ℝ) - a) :
    ((#{n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k} : ℕ) : ℝ) / ((b : ℝ) - a)
      ≤ 2 * (Real.exp |mertensSecondLowerConst|
            * (Real.log z) ^ (-woldBreadthDeviationRate t))
        + (z : ℝ) ^ r * Real.log z / ((b : ℝ) - a) := by
  have hbase := card_omega_le_le_explicit a b z k r hab hz hlogz hrEven ht0 ht1 hk hpow
  rw [div_le_iff₀ hH]
  have hexpand : (2 * (Real.exp |mertensSecondLowerConst|
        * (Real.log z) ^ (-woldBreadthDeviationRate t))
      + (z : ℝ) ^ r * Real.log z / ((b : ℝ) - a)) * ((b : ℝ) - a)
      = 2 * ((b : ℝ) - a) * (Real.exp |mertensSecondLowerConst|
            * (Real.log z) ^ (-woldBreadthDeviationRate t))
        + (z : ℝ) ^ r * Real.log z := by
    field_simp
  rw [hexpand]
  exact hbase

/-- The entropy factor vanishes along any schedule whose sieving level grows. -/
theorem tendsto_rpow_neg_rate {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {L : ℕ → ℝ}
    (hL : Tendsto L atTop atTop) :
    Tendsto (fun X => (L X) ^ (-woldBreadthDeviationRate t)) atTop (𝓝 0) := by
  have hI : 0 < woldBreadthDeviationRate t := woldBreadthDeviationRate_pos_of_lt_one ht0 ht1
  have hpow : Tendsto (fun X => (L X) ^ woldBreadthDeviationRate t) atTop atTop :=
    (tendsto_rpow_atTop hI).comp hL
  have hinv := hpow.inv_tendsto_atTop
  refine hinv.congr' ?_
  filter_upwards [hL.eventually_ge_atTop 0] with X hX
  simp only [Pi.inv_apply]
  rw [Real.rpow_neg hX]

/-- **The low-breadth density vanishes.**  Along any schedule whose sieving level grows and whose
sieve error is small compared with the interval, the integers of few prime factors are a vanishing
fraction. -/
theorem tendsto_card_omega_le_div_zero {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {a b z k r : ℕ → ℕ}
    (hab : ∀ X, a X ≤ b X) (hz : ∀ X, 2 ≤ z X)
    (hlogz : ∀ X, (1 : ℝ) ≤ Real.log (z X)) (hrEven : ∀ X, Even (r X))
    (hk : ∀ X, ((k X : ℕ) : ℝ) = t * logLog (z X))
    (hpow : ∀ X, Real.exp (2 * mertensSecondUpperConst + |mertensSecondLowerConst|)
              * (Real.log (z X)) ^ (4 : ℕ) ≤ (2 : ℝ) ^ (r X))
    (hHpos : ∀ᶠ X in atTop, 0 < (b X : ℝ) - a X)
    (hLtop : Tendsto (fun X => Real.log (z X)) atTop atTop)
    (herr : Tendsto (fun X => (z X : ℝ) ^ (r X) * Real.log (z X) / ((b X : ℝ) - a X))
      atTop (𝓝 0)) :
    Tendsto (fun X => ((#{n ∈ Finset.Ioc (a X) (b X) | n.primeFactors.card ≤ k X} : ℕ) : ℝ)
        / ((b X : ℝ) - a X)) atTop (𝓝 0) := by
  have hent := tendsto_rpow_neg_rate ht0 ht1 hLtop
  have hmaj : Tendsto (fun X => 2 * (Real.exp |mertensSecondLowerConst|
        * (Real.log (z X)) ^ (-woldBreadthDeviationRate t))
      + (z X : ℝ) ^ (r X) * Real.log (z X) / ((b X : ℝ) - a X)) atTop (𝓝 0) := by
    have h1 := (hent.const_mul (Real.exp |mertensSecondLowerConst|)).const_mul (2 : ℝ)
    rw [mul_zero, mul_zero] at h1
    have := h1.add herr
    rwa [add_zero] at this
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [hHpos] with X hX
    positivity
  · filter_upwards [hHpos] with X hX
    exact card_omega_le_div_le (a X) (b X) (z X) (k X) (r X) (hab X) (hz X) (hlogz X)
      (hrEven X) ht0 ht1.le (hk X) (hpow X) hX

/-- **The entropy rate is antitone on `(0,1]`.**  Elementary: `t·log(t'/t) ≤ t' − t` by
`log x ≤ x − 1`, and `−log t' ≥ 0`. -/
theorem woldBreadthDeviationRate_antitone {t t' : ℝ} (ht0 : 0 < t) (htt : t ≤ t')
    (ht1 : t' ≤ 1) : woldBreadthDeviationRate t' ≤ woldBreadthDeviationRate t := by
  have ht'0 : 0 < t' := lt_of_lt_of_le ht0 htt
  have hlogt' : Real.log t' ≤ 0 := Real.log_nonpos ht'0.le ht1
  have hratio : Real.log (t' / t) ≤ t' / t - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hlogdiff : Real.log t' - Real.log t = Real.log (t' / t) :=
    (Real.log_div (ne_of_gt ht'0) (ne_of_gt ht0)).symm
  have hkey : t * (Real.log t' - Real.log t) ≤ t' - t := by
    rw [hlogdiff]
    have hmul := mul_le_mul_of_nonneg_left hratio ht0.le
    have hval : t * (t' / t - 1) = t' - t := by field_simp
    linarith [hval ▸ hmul]
  rw [woldBreadthDeviationRate, woldBreadthDeviationRate]
  nlinarith [hkey, hlogt', sub_nonneg.2 htt]

/-- **The density bound, uniform over all cuts below a fixed one.**  Only the ceiling `t₀` of the
tilt enters the entropy exponent, so a schedule whose cut drifts is covered. -/
theorem card_omega_le_div_le_of_le (a b z k r : ℕ) (hab : a ≤ b) (hz : 2 ≤ z)
    (hlogz : (1 : ℝ) ≤ Real.log z) (hrEven : Even r)
    {t t₀ : ℝ} (ht0 : 0 < t) (htt : t ≤ t₀) (ht1 : t₀ ≤ 1) (hk : (k : ℝ) = t * logLog z)
    (hpow : Real.exp (2 * mertensSecondUpperConst + |mertensSecondLowerConst|)
              * (Real.log z) ^ (4 : ℕ) ≤ (2 : ℝ) ^ r)
    (hH : 0 < (b : ℝ) - a) :
    ((#{n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k} : ℕ) : ℝ) / ((b : ℝ) - a)
      ≤ 2 * (Real.exp |mertensSecondLowerConst|
            * (Real.log z) ^ (-woldBreadthDeviationRate t₀))
        + (z : ℝ) ^ r * Real.log z / ((b : ℝ) - a) := by
  have hbase := card_omega_le_div_le a b z k r hab hz hlogz hrEven ht0 (le_trans htt ht1) hk
    hpow hH
  have hrate := woldBreadthDeviationRate_antitone ht0 htt ht1
  have hexpo : (Real.log z) ^ (-woldBreadthDeviationRate t)
      ≤ (Real.log z) ^ (-woldBreadthDeviationRate t₀) :=
    Real.rpow_le_rpow_of_exponent_le hlogz (by linarith)
  have hstep : 2 * (Real.exp |mertensSecondLowerConst|
        * (Real.log z) ^ (-woldBreadthDeviationRate t))
      ≤ 2 * (Real.exp |mertensSecondLowerConst|
        * (Real.log z) ^ (-woldBreadthDeviationRate t₀)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact mul_le_mul_of_nonneg_left hexpo (by positivity)
  linarith

/-- **The low-breadth density vanishes, with a drifting cut.**  The tilt `t X = k X / log log z X`
need not be constant: it is enough that it stays below a fixed `t₀ < 1`. -/
theorem tendsto_card_omega_le_div_zero_of_le {t₀ : ℝ} (ht₀0 : 0 < t₀) (ht₀1 : t₀ < 1)
    {a b z k r : ℕ → ℕ} {t : ℕ → ℝ}
    (hab : ∀ X, a X ≤ b X) (hz : ∀ X, 2 ≤ z X)
    (hlogz : ∀ X, (1 : ℝ) ≤ Real.log (z X)) (hrEven : ∀ X, Even (r X))
    (ht0 : ∀ X, 0 < t X) (htt : ∀ X, t X ≤ t₀)
    (hk : ∀ X, ((k X : ℕ) : ℝ) = t X * logLog (z X))
    (hpow : ∀ X, Real.exp (2 * mertensSecondUpperConst + |mertensSecondLowerConst|)
              * (Real.log (z X)) ^ (4 : ℕ) ≤ (2 : ℝ) ^ (r X))
    (hHpos : ∀ᶠ X in atTop, 0 < (b X : ℝ) - a X)
    (hLtop : Tendsto (fun X => Real.log (z X)) atTop atTop)
    (herr : Tendsto (fun X => (z X : ℝ) ^ (r X) * Real.log (z X) / ((b X : ℝ) - a X))
      atTop (𝓝 0)) :
    Tendsto (fun X => ((#{n ∈ Finset.Ioc (a X) (b X) | n.primeFactors.card ≤ k X} : ℕ) : ℝ)
        / ((b X : ℝ) - a X)) atTop (𝓝 0) := by
  have hent := tendsto_rpow_neg_rate ht₀0 ht₀1 hLtop
  have hmaj : Tendsto (fun X => 2 * (Real.exp |mertensSecondLowerConst|
        * (Real.log (z X)) ^ (-woldBreadthDeviationRate t₀))
      + (z X : ℝ) ^ (r X) * Real.log (z X) / ((b X : ℝ) - a X)) atTop (𝓝 0) := by
    have h1 := (hent.const_mul (Real.exp |mertensSecondLowerConst|)).const_mul (2 : ℝ)
    rw [mul_zero, mul_zero] at h1
    have := h1.add herr
    rwa [add_zero] at this
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [hHpos] with X hX
    positivity
  · filter_upwards [hHpos] with X hX
    exact card_omega_le_div_le_of_le (a X) (b X) (z X) (k X) (r X) (hab X) (hz X) (hlogz X)
      (hrEven X) (ht0 X) (htt X) ht₀1.le (hk X) (hpow X) hX

/-- **The sieve error, as a single exponent.**  `z^r·log z/H = exp(r log z + log log z − log H)`,
so the whole error hypothesis is the statement that one explicit exponent tends to `−∞`. -/
theorem tendsto_pow_mul_log_div_zero {z r : ℕ → ℕ} {H : ℕ → ℝ}
    (hz : ∀ X, 2 ≤ z X) (hH : ∀ X, 0 < H X)
    (hexp : Tendsto (fun X => (r X : ℝ) * Real.log (z X) + Real.log (Real.log (z X))
        - Real.log (H X)) atTop atBot) :
    Tendsto (fun X => (z X : ℝ) ^ (r X) * Real.log (z X) / H X) atTop (𝓝 0) := by
  have hcongr : ∀ X, Real.exp ((r X : ℝ) * Real.log (z X) + Real.log (Real.log (z X))
        - Real.log (H X)) = (z X : ℝ) ^ (r X) * Real.log (z X) / H X := by
    intro X
    have hz2 : (2 : ℝ) ≤ (z X : ℝ) := by exact_mod_cast hz X
    have hz0 : (0 : ℝ) < (z X : ℝ) := by linarith
    have hlogz0 : (0 : ℝ) < Real.log (z X) := Real.log_pos (by linarith)
    have hpow : ((z X : ℝ)) ^ (r X) = Real.exp ((r X : ℝ) * Real.log (z X)) := by
      rw [← Real.log_pow, Real.exp_log (by positivity)]
    rw [Real.exp_sub, Real.exp_add, Real.exp_log hlogz0, Real.exp_log (hH X), ← hpow]
  refine Tendsto.congr hcongr ?_
  exact Real.tendsto_exp_atBot.comp hexp

/-- A power of two below `M` bounds its exponent by `log M / log 2`. -/
theorem le_of_two_pow_le {r : ℕ} {M : ℝ} (h : (2 : ℝ) ^ r ≤ M) :
    (r : ℝ) ≤ Real.log M / Real.log 2 := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have hlog : Real.log ((2 : ℝ) ^ r) ≤ Real.log M := Real.log_le_log hpos h
  rw [Real.log_pow] at hlog
  rw [le_div_iff₀ h2]
  linarith

/-- **The sieve error vanishes, from any size bound on the absorbing exponent.**  The caller supplies
an upper bound `R` for `r`; only `R` enters the exponent condition. -/
theorem tendsto_pow_mul_log_div_zero_of_exponent {z r : ℕ → ℕ} {H R : ℕ → ℝ}
    (hz : ∀ X, 2 ≤ z X) (hH : ∀ X, 0 < H X) (hrb : ∀ X, (r X : ℝ) ≤ R X)
    (hexp : Tendsto (fun X => R X * Real.log (z X) + Real.log (Real.log (z X))
        - Real.log (H X)) atTop atBot) :
    Tendsto (fun X => (z X : ℝ) ^ (r X) * Real.log (z X) / H X) atTop (𝓝 0) := by
  refine tendsto_pow_mul_log_div_zero hz hH ?_
  refine tendsto_atBot_mono (fun X => ?_) hexp
  have hz2 : (2 : ℝ) ≤ (z X : ℝ) := by exact_mod_cast hz X
  have hlogz0 : (0 : ℝ) ≤ Real.log (z X) := (Real.log_pos (by linarith)).le
  have := mul_le_mul_of_nonneg_right (hrb X) hlogz0
  linarith

/-- The sieving level realised as a natural number: `z = ⌈exp L⌉`. -/
private noncomputable def sieveLevel (L : ℝ) : ℕ := ⌈Real.exp L⌉₊

theorem two_le_sieveLevel {L : ℝ} (hL : 0 < L) : 2 ≤ sieveLevel L := by
  rw [sieveLevel]
  have h1 : (1 : ℝ) < Real.exp L := by
    have := Real.add_one_le_exp L
    linarith
  have := Nat.lt_ceil.2 (by exact_mod_cast h1 : ((1 : ℕ) : ℝ) < Real.exp L)
  omega

/-- **The ceiling of an exponential has logarithm within one.**  This is all the control a schedule
needs: the level is realised exactly up to an additive constant. -/
theorem log_sieveLevel_mem {L : ℝ} (hL : 0 ≤ L) :
    L ≤ Real.log (sieveLevel L) ∧ Real.log (sieveLevel L) ≤ L + 1 := by
  have hexp0 : (0 : ℝ) < Real.exp L := Real.exp_pos L
  have hexp1 : (1 : ℝ) ≤ Real.exp L := by
    have := Real.add_one_le_exp L
    linarith
  have hceil : Real.exp L ≤ ((sieveLevel L : ℕ) : ℝ) := by
    rw [sieveLevel]
    exact Nat.le_ceil _
  have hceil0 : (0 : ℝ) < ((sieveLevel L : ℕ) : ℝ) := by linarith
  constructor
  · have := Real.log_le_log hexp0 hceil
    rwa [Real.log_exp] at this
  · have hup : ((sieveLevel L : ℕ) : ℝ) ≤ Real.exp (L + 1) := by
      have hlt : ((sieveLevel L : ℕ) : ℝ) < Real.exp L + 1 := by
        rw [sieveLevel]
        exact Nat.ceil_lt_add_one hexp0.le
      have htwo : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      have hsplit : Real.exp (L + 1) = Real.exp L * Real.exp 1 := Real.exp_add L 1
      nlinarith [hexp1, hlt, htwo, hsplit.le, hsplit.ge, hexp0]
    have := Real.log_le_log hceil0 hup
    rwa [Real.log_exp] at this

/-- The sieving level is above the threshold the tail lemmas need. -/
theorem one_le_log_sieveLevel {L : ℝ} (hL : 1 ≤ L) : (1 : ℝ) ≤ Real.log (sieveLevel L) :=
  le_trans hL (log_sieveLevel_mem (by linarith)).1

/-- **The schedule error condition.**  With the level realised as `⌈exp L⌉`, the whole sieve error
hypothesis becomes `(L+1)·log(L+1) ≪ log H`. -/
theorem tendsto_schedule_error {L H : ℕ → ℝ} {r : ℕ → ℕ}
    (hL : ∀ X, 1 ≤ L X) (hH : ∀ X, 0 < H X)
    (hr : ∀ X, (2 : ℝ) ^ (r X)
        ≤ 4 * (Real.exp (2 * mertensSecondUpperConst + |mertensSecondLowerConst|)
            * (Real.log (sieveLevel (L X))) ^ (4 : ℕ)) + 1)
    (hcond : Tendsto (fun X =>
        (Real.log (4 * Real.exp (2 * mertensSecondUpperConst + |mertensSecondLowerConst|) + 1)
          + 4 * Real.log (L X + 1)) / Real.log 2 * (L X + 1)
        + Real.log (L X + 1) - Real.log (H X)) atTop atBot) :
    Tendsto (fun X => ((sieveLevel (L X) : ℕ) : ℝ) ^ (r X)
        * Real.log (sieveLevel (L X)) / H X) atTop (𝓝 0) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hz : ∀ X, 2 ≤ sieveLevel (L X) := fun X => two_le_sieveLevel (by linarith [hL X])
  refine tendsto_pow_mul_log_div_zero_of_exponent (R := fun X =>
    (Real.log (4 * Real.exp (2 * mertensSecondUpperConst + |mertensSecondLowerConst|) + 1)
      + 4 * Real.log (L X + 1)) / Real.log 2) hz hH ?_ ?_
  · intro X
    obtain ⟨hlow, hup⟩ := log_sieveLevel_mem (L := L X) (by linarith [hL X])
    have hL1 : (1 : ℝ) ≤ L X := hL X
    have hLp : (2 : ℝ) ≤ L X + 1 := by linarith
    have hlogzpos : (0 : ℝ) < Real.log (sieveLevel (L X)) := by linarith
    have hbase := le_of_two_pow_le (hr X)
    refine le_trans hbase ?_
    refine div_le_div_of_nonneg_right ?_ hlog2.le
    have hpow4 : (Real.log (sieveLevel (L X))) ^ (4 : ℕ) ≤ (L X + 1) ^ (4 : ℕ) :=
      pow_le_pow_left₀ hlogzpos.le hup 4
    have hone : (1 : ℝ) ≤ (L X + 1) ^ (4 : ℕ) := one_le_pow₀ (by linarith)
    have hexp0 : (0 : ℝ) < Real.exp (2 * mertensSecondUpperConst + |mertensSecondLowerConst|) :=
      Real.exp_pos _
    have hprod : 4 * (Real.exp (2 * mertensSecondUpperConst + |mertensSecondLowerConst|)
          * (Real.log (sieveLevel (L X))) ^ (4 : ℕ)) + 1
        ≤ (4 * Real.exp (2 * mertensSecondUpperConst + |mertensSecondLowerConst|) + 1)
            * (L X + 1) ^ (4 : ℕ) := by
      nlinarith [hpow4, hone, hexp0]
    have hposA : (0 : ℝ) < 4 * Real.exp (2 * mertensSecondUpperConst
        + |mertensSecondLowerConst|) + 1 := by positivity
    have hlogle := Real.log_le_log (by positivity) hprod
    refine le_trans hlogle (le_of_eq ?_)
    rw [Real.log_mul (ne_of_gt hposA) (by positivity), Real.log_pow]
    push_cast
    ring
  · refine tendsto_atBot_mono (fun X => ?_) hcond
    obtain ⟨hlow, hup⟩ := log_sieveLevel_mem (L := L X) (by linarith [hL X])
    have hL1 : (1 : ℝ) ≤ L X := hL X
    have hlogzpos : (0 : ℝ) < Real.log (sieveLevel (L X)) := by linarith
    have hR0 : (0 : ℝ) ≤ (Real.log (4 * Real.exp (2 * mertensSecondUpperConst
        + |mertensSecondLowerConst|) + 1) + 4 * Real.log (L X + 1)) / Real.log 2 := by
      have h1 : (0 : ℝ) ≤ Real.log (4 * Real.exp (2 * mertensSecondUpperConst
          + |mertensSecondLowerConst|) + 1) := by
        refine Real.log_nonneg ?_
        have : (0 : ℝ) < Real.exp (2 * mertensSecondUpperConst + |mertensSecondLowerConst|) :=
          Real.exp_pos _
        linarith
      have h2 : (0 : ℝ) ≤ Real.log (L X + 1) := Real.log_nonneg (by linarith)
      positivity
    have hmul : (Real.log (4 * Real.exp (2 * mertensSecondUpperConst
          + |mertensSecondLowerConst|) + 1) + 4 * Real.log (L X + 1)) / Real.log 2
        * Real.log (sieveLevel (L X))
        ≤ (Real.log (4 * Real.exp (2 * mertensSecondUpperConst
          + |mertensSecondLowerConst|) + 1) + 4 * Real.log (L X + 1)) / Real.log 2
        * (L X + 1) := mul_le_mul_of_nonneg_left hup hR0
    have hloglog : Real.log (Real.log (sieveLevel (L X))) ≤ Real.log (L X + 1) :=
      Real.log_le_log hlogzpos hup
    linarith

/-- **The low-breadth density vanishes, for a schedule given by its level.**  Everything is
expressed through the prescribed real level `L` and the cell length: the absorbing exponent is
pinned by the two-sided bound, the cut may drift below a fixed ceiling, and the only analytic
condition is `(L+1)·log(L+1) ≪ log(cell)`. -/
theorem tendsto_card_omega_le_div_zero_schedule {t₀ : ℝ} (ht₀0 : 0 < t₀) (ht₀1 : t₀ < 1)
    {a b k r : ℕ → ℕ} {t L : ℕ → ℝ}
    (hab : ∀ X, a X ≤ b X) (hL : ∀ X, 1 ≤ L X) (hLtop : Tendsto L atTop atTop)
    (ht0 : ∀ X, 0 < t X) (htt : ∀ X, t X ≤ t₀)
    (hk : ∀ X, ((k X : ℕ) : ℝ) = t X * logLog (sieveLevel (L X)))
    (hrEven : ∀ X, Even (r X))
    (hrlow : ∀ X, Real.exp (2 * mertensSecondUpperConst + |mertensSecondLowerConst|)
        * (Real.log (sieveLevel (L X))) ^ (4 : ℕ) ≤ (2 : ℝ) ^ (r X))
    (hrup : ∀ X, (2 : ℝ) ^ (r X)
        ≤ 4 * (Real.exp (2 * mertensSecondUpperConst + |mertensSecondLowerConst|)
            * (Real.log (sieveLevel (L X))) ^ (4 : ℕ)) + 1)
    (hHpos : ∀ X, 0 < (b X : ℝ) - a X)
    (hcond : Tendsto (fun X =>
        (Real.log (4 * Real.exp (2 * mertensSecondUpperConst + |mertensSecondLowerConst|) + 1)
          + 4 * Real.log (L X + 1)) / Real.log 2 * (L X + 1)
        + Real.log (L X + 1) - Real.log ((b X : ℝ) - a X)) atTop atBot) :
    Tendsto (fun X => ((#{n ∈ Finset.Ioc (a X) (b X) | n.primeFactors.card ≤ k X} : ℕ) : ℝ)
        / ((b X : ℝ) - a X)) atTop (𝓝 0) := by
  have hz : ∀ X, 2 ≤ sieveLevel (L X) := fun X => two_le_sieveLevel (by linarith [hL X])
  have hlogz : ∀ X, (1 : ℝ) ≤ Real.log (sieveLevel (L X)) :=
    fun X => one_le_log_sieveLevel (hL X)
  have hLlog : Tendsto (fun X => Real.log (sieveLevel (L X))) atTop atTop := by
    refine tendsto_atTop_mono (fun X => ?_) hLtop
    exact (log_sieveLevel_mem (L := L X) (by linarith [hL X])).1
  have herr := tendsto_schedule_error hL (fun X => hHpos X) hrup hcond
  exact tendsto_card_omega_le_div_zero_of_le ht₀0 ht₀1 hab hz hlogz hrEven ht0 htt hk
    hrlow (Filter.Eventually.of_forall hHpos) hLlog herr

end RHTower.Sieve

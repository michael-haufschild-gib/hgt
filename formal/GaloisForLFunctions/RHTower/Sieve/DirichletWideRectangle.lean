import GaloisForLFunctions.RHTower.Sieve.DirichletWideOrder

/-!
# The rectangle estimate on a wide strip

The rectangle capstone `norm_dirichlet_sigma_littlewood_capstone` holds at any order clearing the
largeness condition, and the strip it produces is `1 - σ ≤ 1/(6·2^K)`.  Two bounds on `2^K`, both
relative to the scale `L = log(t/2π)`,

```text
L < 120·2^K·(log L)²      and      100·2^K ≤ L ,
```

pin the order to `≍ log₂ L` and make the estimate polylogarithmic on the whole strip:

```text
‖∑_{n < 2^(topExponent t + 1)} n^(-σ - it)‖  ≤  L^(34 : ℕ) .
```

The mechanism is that the lower bound on `2^K` forces `√L ≤ 2^K`, hence `log L ≤ 2K log 2`, so the
trade-off exponent `θ = S/(6·2^K)` with `S ≤ L/((K - 4/3) log 2) + 1` is only `O(log L)` — a single
logarithm, although the strip is `(log L)²/L` wide.  The head is then `2^θ·S·log 2 ≤ L^(33 : ℕ)` and the
tail `(T + 1 - S)·2560·2^(-θ) ≤ 12800 L`.

Both hypotheses hold at the wide order, giving the estimate as a function of `t` alone; stating them
separately is what lets one *fixed* order serve a whole disc of heights.
-/

namespace RHTower.Sieve

open Finset

/-! ### Sharper logarithm bounds -/

/-- `(log x)² ≤ 64·x^{1/4}`. -/
theorem wide_log_sq_le_quarter {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ 2 ≤ 64 * Real.sqrt (Real.sqrt x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  set v : ℝ := Real.sqrt (Real.sqrt x) with hv
  have hv0 : (0 : ℝ) < v := Real.sqrt_pos.mpr hsx0
  have hlogv : Real.log v = Real.log x / 4 := by
    rw [hv, Real.log_sqrt hsx0.le, Real.log_sqrt hx0.le]; ring
  have h1 : Real.log v ≤ 2 * Real.sqrt v := wide_log_le_two_sqrt hv0
  have h2 : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv0.le
  have hnn : 0 ≤ Real.log x := Real.log_nonneg hx
  have h3 : Real.log x ≤ 8 * Real.sqrt v := by rw [hlogv] at h1; linarith
  nlinarith [Real.sqrt_nonneg v, h2, h3, hnn]

/-- `120(log x)² ≤ √x` for `x ≥ 10¹⁶`. -/
theorem hundredtwenty_log_sq_le_sqrt {x : ℝ} (hx : (10 : ℝ) ^ 16 ≤ x) :
    120 * Real.log x ^ 2 ≤ Real.sqrt x := by
  have hx1 : (1 : ℝ) ≤ x := by nlinarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hq := wide_log_sq_le_quarter hx1
  have hsx0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hvsq : Real.sqrt (Real.sqrt x) ^ 2 = Real.sqrt x := Real.sq_sqrt hsx0
  have hs : (10 : ℝ) ^ 8 ≤ Real.sqrt x := by
    refine (Real.le_sqrt (by norm_num) hx0.le).mpr ?_
    nlinarith
  have hv : (10000 : ℝ) ≤ Real.sqrt (Real.sqrt x) := by
    refine (Real.le_sqrt (by norm_num) hsx0).mpr ?_
    nlinarith
  nlinarith [hq, hv, hvsq]

/-- `log L ≥ 31` in the range considered. -/
theorem thirtyone_le_log_wideScale {t : ℝ} (hL : (10 : ℝ) ^ 16 ≤ wideScale t) :
    (31 : ℝ) ≤ Real.log (wideScale t) := by
  have hlog2 := Real.log_two_gt_d9
  have h8 : Real.log ((10 : ℝ) ^ 16) = 16 * Real.log 10 := by
    rw [Real.log_pow]; norm_num
  have hle : Real.log ((8 : ℝ)) ≤ Real.log 10 := Real.log_le_log (by norm_num) (by norm_num)
  have h8eq : Real.log ((8 : ℝ)) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; norm_num
  have hmono : Real.log ((10 : ℝ) ^ 16) ≤ Real.log (wideScale t) :=
    Real.log_le_log (by norm_num) hL
  rw [h8eq] at hle
  rw [h8] at hmono
  nlinarith

/-! ### The order is of size `log₂ L` -/

/-- `√L ≤ 2^K` for any order that is not too small. -/
theorem sqrt_wideScale_le_two_pow_of {t : ℝ} {K : ℕ} (hL : (10 : ℝ) ^ 16 ≤ wideScale t)
    (hKlo : wideScale t < 120 * (2 : ℝ) ^ K * Real.log (wideScale t) ^ 2) :
    Real.sqrt (wideScale t) ≤ (2 : ℝ) ^ K := by
  have hL0 : (0 : ℝ) < wideScale t := by nlinarith
  have hsq := hundredtwenty_log_sq_le_sqrt hL
  have hs0 : (0 : ℝ) < Real.sqrt (wideScale t) := Real.sqrt_pos.mpr hL0
  have hss : Real.sqrt (wideScale t) * Real.sqrt (wideScale t) = wideScale t :=
    Real.mul_self_sqrt hL0.le
  have hK0 : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
  nlinarith [hKlo, hsq, hss, hs0, hK0]

/-- `log L ≤ 2K log 2`. -/
theorem log_wideScale_le_two_mul_of {t : ℝ} {K : ℕ} (hL : (10 : ℝ) ^ 16 ≤ wideScale t)
    (hKlo : wideScale t < 120 * (2 : ℝ) ^ K * Real.log (wideScale t) ^ 2) :
    Real.log (wideScale t) ≤ 2 * (K : ℝ) * Real.log 2 := by
  have hL0 : (0 : ℝ) < wideScale t := by nlinarith
  have hs0 : (0 : ℝ) < Real.sqrt (wideScale t) := Real.sqrt_pos.mpr hL0
  have h := Real.log_le_log hs0 (sqrt_wideScale_le_two_pow_of hL hKlo)
  rw [Real.log_sqrt hL0.le, Real.log_pow] at h
  linarith

/-- `(K - 4/3)·log 2 ≥ 0.45·log L`. -/
theorem denom_ge_of {t : ℝ} {K : ℕ} (hL : (10 : ℝ) ^ 16 ≤ wideScale t)
    (hKlo : wideScale t < 120 * (2 : ℝ) ^ K * Real.log (wideScale t) ^ 2) :
    (45 : ℝ) / 100 * Real.log (wideScale t) ≤ ((K : ℝ) - 4 / 3) * Real.log 2 := by
  have h := log_wideScale_le_two_mul_of hL hKlo
  have hx := thirtyone_le_log_wideScale hL
  have hlog2 : Real.log 2 ≤ 1 := by
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-! ### The split point -/

/-- The split point is bounded by `L/(0.45 log L) + 1`. -/
theorem splitExponent_le_of {t : ℝ} {K : ℕ} (hL : (10 : ℝ) ^ 16 ≤ wideScale t)
    (hKlo : wideScale t < 120 * (2 : ℝ) ^ K * Real.log (wideScale t) ^ 2)
    (hKhi : 100 * (2 : ℝ) ^ K ≤ wideScale t) :
    ((splitExponent t K : ℕ) : ℝ)
      ≤ wideScale t / ((45 : ℝ) / 100 * Real.log (wideScale t)) + 1 := by
  have hws : wideScale t = Real.log (t / (2 * Real.pi)) := rfl
  have hL0 : (0 : ℝ) < wideScale t := by nlinarith
  have hx := thirtyone_le_log_wideScale hL
  have hden := denom_ge_of hL hKlo
  have hdenpos : (0 : ℝ) < (45 : ℝ) / 100 * Real.log (wideScale t) := by nlinarith
  have hdenpos2 : (0 : ℝ) < ((K : ℝ) - 4 / 3) * Real.log 2 := by linarith
  have hKlog : (K : ℝ) * Real.log 2 ≤ Real.log (wideScale t) := by
    have hPpos : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
    have hpow : (2 : ℝ) ^ K ≤ wideScale t := by linarith
    have h1 : Real.log ((2 : ℝ) ^ K) ≤ Real.log (wideScale t) :=
      Real.log_le_log hPpos hpow
    rwa [Real.log_pow] at h1
  have hlogle : Real.log (wideScale t) ≤ wideScale t - 1 := Real.log_le_sub_one_of_pos hL0
  have hnum : (0 : ℝ) ≤ wideScale t - (K : ℝ) * Real.log 2 := by linarith
  have hnn : (0 : ℝ) ≤ (Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
      / (((K : ℝ) - 4 / 3) * Real.log 2) := by
    rw [← hws]
    exact div_nonneg hnum hdenpos2.le
  have hle := splitExponent_le (t := t) (K := K) hnn
  rw [← hws] at hle
  refine le_trans hle ?_
  have hstep : (wideScale t - (K : ℝ) * Real.log 2) / (((K : ℝ) - 4 / 3) * Real.log 2)
      ≤ wideScale t / ((45 : ℝ) / 100 * Real.log (wideScale t)) := by
    have hKnn : (0 : ℝ) ≤ (K : ℝ) * Real.log 2 := by positivity
    rw [div_le_div_iff₀ hdenpos2 hdenpos]
    nlinarith [mul_le_mul_of_nonneg_right
        (show wideScale t - (K : ℝ) * Real.log 2 ≤ wideScale t by linarith) hdenpos.le,
      mul_le_mul_of_nonneg_left hden hL0.le]
  linarith

/-- Division-free form of the split-point bound. -/
theorem splitExponent_mul_le_of {t : ℝ} {K : ℕ} (hL : (10 : ℝ) ^ 16 ≤ wideScale t)
    (hKlo : wideScale t < 120 * (2 : ℝ) ^ K * Real.log (wideScale t) ^ 2)
    (hKhi : 100 * (2 : ℝ) ^ K ≤ wideScale t) :
    ((splitExponent t K : ℕ) : ℝ) * ((45 : ℝ) / 100 * Real.log (wideScale t))
      ≤ wideScale t + (45 : ℝ) / 100 * Real.log (wideScale t) := by
  have hx := thirtyone_le_log_wideScale hL
  have hdenpos : (0 : ℝ) < (45 : ℝ) / 100 * Real.log (wideScale t) := by nlinarith
  have h := splitExponent_le_of hL hKlo hKhi
  have hmul := mul_le_mul_of_nonneg_right h hdenpos.le
  have hcancel : wideScale t / ((45 : ℝ) / 100 * Real.log (wideScale t))
      * ((45 : ℝ) / 100 * Real.log (wideScale t)) = wideScale t :=
    div_mul_cancel₀ _ (ne_of_gt hdenpos)
  nlinarith [hmul, hcancel]

/-- `√L ≥ 10⁸`. -/
theorem ten_pow_eight_le_sqrt_wideScale {t : ℝ} (hL : (10 : ℝ) ^ 16 ≤ wideScale t) :
    (10 : ℝ) ^ 8 ≤ Real.sqrt (wideScale t) := by
  have hL0 : (0 : ℝ) < wideScale t := by nlinarith
  refine (Real.le_sqrt (by norm_num) hL0.le).mpr ?_
  nlinarith

/-- **The trade-off exponent is logarithmic.** -/
theorem stripTheta_le_of {t : ℝ} {K : ℕ} (hL : (10 : ℝ) ^ 16 ≤ wideScale t)
    (hKlo : wideScale t < 120 * (2 : ℝ) ^ K * Real.log (wideScale t) ^ 2)
    (hKhi : 100 * (2 : ℝ) ^ K ≤ wideScale t) :
    stripTheta t K ≤ 45 * Real.log (wideScale t) := by
  have hL0 : (0 : ℝ) < wideScale t := by nlinarith
  have hx := thirtyone_le_log_wideScale hL
  have hxpos : (0 : ℝ) < Real.log (wideScale t) := by linarith
  have hP : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
  have hSd := splitExponent_mul_le_of hL hKlo hKhi
  have hs := ten_pow_eight_le_sqrt_wideScale hL
  have hss : Real.sqrt (wideScale t) * Real.sqrt (wideScale t) = wideScale t :=
    Real.mul_self_sqrt hL0.le
  have hxs : Real.log (wideScale t) ≤ 2 * Real.sqrt (wideScale t) := wide_log_le_two_sqrt hL0
  have hsmall : (45 : ℝ) / 100 * Real.log (wideScale t) ≤ (1 : ℝ) / 1000 * wideScale t := by
    nlinarith [hs, hss, hxs, Real.sqrt_nonneg (wideScale t)]
  have hSnn : (0 : ℝ) ≤ ((splitExponent t K : ℕ) : ℝ) := Nat.cast_nonneg _
  have hdenpos : (0 : ℝ) < (45 : ℝ) / 100 * Real.log (wideScale t) := by nlinarith
  have hkey : ((splitExponent t K : ℕ) : ℝ) * ((45 : ℝ) / 100 * Real.log (wideScale t))
      ≤ (270 * Real.log (wideScale t) * (2 : ℝ) ^ K)
        * ((45 : ℝ) / 100 * Real.log (wideScale t)) := by
    have hbig : (1001 : ℝ) / 1000 * wideScale t
        ≤ (270 * Real.log (wideScale t) * (2 : ℝ) ^ K)
          * ((45 : ℝ) / 100 * Real.log (wideScale t)) := by
      nlinarith [hKlo, hP, hxpos]
    linarith
  have hle : ((splitExponent t K : ℕ) : ℝ) ≤ 270 * Real.log (wideScale t) * (2 : ℝ) ^ K :=
    le_of_mul_le_mul_right (by linarith [hkey]) hdenpos
  rw [stripTheta, div_le_iff₀ (by positivity)]
  nlinarith [hle, hP, hxpos]

/-! ### The rectangle bound -/

/-- **The partial sum is polylogarithmic on the wide strip.** -/
theorem norm_dirichlet_wide_rect {σ t : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (ht16 : 16 * Real.pi ≤ t) (hL : (10 : ℝ) ^ 16 ≤ wideScale t) {K : ℕ} (hK10 : 10 ≤ K)
    (hKlo : wideScale t < 120 * (2 : ℝ) ^ K * Real.log (wideScale t) ^ 2)
    (hKhi : 100 * (2 : ℝ) ^ K ≤ wideScale t)
    (hstrip : 1 - σ ≤ 1 / (6 * (2 : ℝ) ^ K)) :
    ‖∑ n ∈ Finset.Ico (1 : ℕ) (2 ^ (topExponent t + 1)),
        (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ wideScale t ^ (34 : ℕ) := by
  have hπ := Real.pi_pos
  have hL0 : (0 : ℝ) < wideScale t := by linarith
  have hx := thirtyone_le_log_wideScale hL
  have hxpos : (0 : ℝ) < Real.log (wideScale t) := by linarith
  have hKR : (10 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK10
  have hP : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
  have hK3 : 3 ≤ K := by omega
  have hcond : largenessBound K < wideScale t := by
    have hlog2 : Real.log 2 ≤ 1 := by
      have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have hlogK : Real.log ((K : ℝ) - 1) ≤ (K : ℝ) - 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (K : ℝ) - 1 by linarith)
      linarith
    have hlogKnn : (0 : ℝ) ≤ Real.log ((K : ℝ) - 1) := Real.log_nonneg (by linarith)
    have hA : (0 : ℝ) ≤ ((K : ℝ) - 1) * ((K : ℝ) - 4 / 3) :=
      mul_nonneg (by linarith) (by linarith)
    have hbound : largenessBound K ≤ (K : ℝ) ^ 3 + (K : ℝ) := by
      rw [largenessBound]
      have h1 : ((K : ℝ) - 1) * ((K : ℝ) - 4 / 3) * Real.log ((K : ℝ) - 1)
          ≤ ((K : ℝ) - 1) * ((K : ℝ) - 4 / 3) * ((K : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left hlogK hA
      have h2 : ((K : ℝ) - 1) * ((K : ℝ) - 4 / 3) * ((K : ℝ) - 1) ≤ (K : ℝ) ^ 3 := by
        linarith [mul_le_mul_of_nonneg_right hKR (by linarith : (0 : ℝ) ≤ (K : ℝ))]
      linarith [mul_le_mul_of_nonneg_left hlog2 (by linarith : (0 : ℝ) ≤ (K : ℝ))]
    have hcube := cube_lt_two_pow hK10
    have hKsq : (1 : ℝ) ≤ (K : ℝ) ^ 2 := one_le_pow₀ (by linarith)
    have hKle : (K : ℝ) ≤ (K : ℝ) ^ 3 := by
      linarith [le_mul_of_one_le_right (by linarith : (0 : ℝ) ≤ (K : ℝ)) hKsq]
    linarith [hbound, hcube, hKle, hKhi, hL0]
  rw [largenessBound] at hcond
  have hmain := norm_dirichlet_sigma_littlewood_capstone hσ0 hσ1 ht16 hK3 hstrip hcond
  set θ : ℝ := stripTheta t K with hθdef
  have hθnn : (0 : ℝ) ≤ θ := by
    rw [hθdef, stripTheta]; positivity
  have hθle : θ ≤ 45 * Real.log (wideScale t) := by
    rw [hθdef]; exact stripTheta_le_of hL hKlo hKhi
  have hlog2lt := Real.log_two_lt_d9
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hhead2 : (2 : ℝ) ^ θ ≤ wideScale t ^ (32 : ℕ) := by
    have hrw : (2 : ℝ) ^ θ = Real.exp (Real.log 2 * θ) :=
      Real.rpow_def_of_pos (by norm_num) θ
    have hexp : Real.log 2 * θ ≤ 32 * Real.log (wideScale t) := by
      linarith [mul_le_mul_of_nonneg_left hθle hlog2pos.le,
        mul_le_mul_of_nonneg_right hlog2lt.le (by linarith : (0 : ℝ) ≤ 45 * Real.log (wideScale t))]
    have hfin : Real.exp (32 * Real.log (wideScale t)) = wideScale t ^ (32 : ℕ) := by
      rw [show (32 : ℝ) * Real.log (wideScale t) = Real.log (wideScale t ^ (32 : ℕ)) by
        rw [Real.log_pow]; norm_num]
      exact Real.exp_log (by positivity)
    calc (2 : ℝ) ^ θ = Real.exp (Real.log 2 * θ) := hrw
      _ ≤ Real.exp (32 * Real.log (wideScale t)) := Real.exp_le_exp.mpr hexp
      _ = wideScale t ^ (32 : ℕ) := hfin
  have htail2 : (2 : ℝ) ^ (-θ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hSd := splitExponent_mul_le_of hL hKlo hKhi
  have hs := ten_pow_eight_le_sqrt_wideScale hL
  have hss : Real.sqrt (wideScale t) * Real.sqrt (wideScale t) = wideScale t :=
    Real.mul_self_sqrt hL0.le
  have hxs : Real.log (wideScale t) ≤ 2 * Real.sqrt (wideScale t) := wide_log_le_two_sqrt hL0
  have hSnn : (0 : ℝ) ≤ ((splitExponent t K : ℕ) : ℝ) := Nat.cast_nonneg _
  have hSlog : ((splitExponent t K : ℕ) : ℝ) * Real.log 2 ≤ wideScale t := by
    have hdenpos : (0 : ℝ) < (45 : ℝ) / 100 * Real.log (wideScale t) := by linarith
    have hb : Real.log 2 ≤ 1 := by
      have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have hmul : ((splitExponent t K : ℕ) : ℝ) * Real.log 2
        * ((45 : ℝ) / 100 * Real.log (wideScale t))
        ≤ wideScale t * ((45 : ℝ) / 100 * Real.log (wideScale t)) := by
      have hstep : ((splitExponent t K : ℕ) : ℝ) * Real.log 2
          * ((45 : ℝ) / 100 * Real.log (wideScale t))
          ≤ (wideScale t + (45 : ℝ) / 100 * Real.log (wideScale t)) * Real.log 2 := by
        linarith [mul_le_mul_of_nonneg_right hSd hlog2pos.le]
      linarith [mul_le_mul_of_nonneg_left hb
          (by linarith : (0 : ℝ) ≤ wideScale t + 45 / 100 * Real.log (wideScale t)),
        mul_le_mul_of_nonneg_left hx hL0.le,
        mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg (wideScale t))]
    exact le_of_mul_le_mul_right hmul hdenpos
  have ht0 : (0 : ℝ) < t := by linarith
  have hT : ((topExponent t : ℕ) : ℝ) ≤ 3 * Real.log (t / (8 * Real.pi)) / Real.log 2 :=
    topExponent_le (by linarith)
  have hTlog : Real.log (t / (8 * Real.pi)) ≤ wideScale t := by
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith [mul_le_mul_of_nonneg_left (by linarith : 2 * Real.pi ≤ 8 * Real.pi) ht0.le]
  have hT2 : ((topExponent t : ℕ) : ℝ) * Real.log 2 ≤ 3 * wideScale t := by
    rw [le_div_iff₀ hlog2pos] at hT
    linarith
  have hlog2gt : (69 : ℝ) / 100 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hTnn : (0 : ℝ) ≤ ((topExponent t : ℕ) : ℝ) := Nat.cast_nonneg _
  have hprod : (69 : ℝ) / 100 * ((topExponent t : ℕ) : ℝ)
      ≤ ((topExponent t : ℕ) : ℝ) * Real.log 2 := by
    have h := mul_nonneg hTnn (by linarith : (0 : ℝ) ≤ Real.log 2 - 69 / 100)
    linarith [h]
  have hTle : ((topExponent t : ℕ) : ℝ) + 1 ≤ 5 * wideScale t := by
    linarith only [hT2, hprod, hL]
  have hcast : ((topExponent t + 1 - splitExponent t K : ℕ) : ℝ)
      ≤ ((topExponent t : ℕ) : ℝ) + 1 := by
    have hsub : (topExponent t + 1 - splitExponent t K) ≤ topExponent t + 1 := Nat.sub_le _ _
    have hc : ((topExponent t + 1 - splitExponent t K : ℕ) : ℝ)
        ≤ ((topExponent t + 1 : ℕ) : ℝ) := Nat.cast_le.mpr hsub
    have he : ((topExponent t + 1 : ℕ) : ℝ) = ((topExponent t : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    linarith [hc, he.le, he.ge]
  have hheadbound : (2 : ℝ) ^ θ * ((splitExponent t K : ℕ) : ℝ) * Real.log 2
      ≤ wideScale t ^ (33 : ℕ) := by
    have h32nn : (0 : ℝ) ≤ wideScale t ^ (32 : ℕ) := by positivity
    have hprod2 : (2 : ℝ) ^ θ * (((splitExponent t K : ℕ) : ℝ) * Real.log 2)
        ≤ wideScale t ^ (32 : ℕ) * wideScale t :=
      mul_le_mul hhead2 hSlog (by positivity) h32nn
    calc (2 : ℝ) ^ θ * ((splitExponent t K : ℕ) : ℝ) * Real.log 2
        = (2 : ℝ) ^ θ * (((splitExponent t K : ℕ) : ℝ) * Real.log 2) := by ring
      _ ≤ wideScale t ^ (32 : ℕ) * wideScale t := hprod2
      _ = wideScale t ^ (33 : ℕ) := by ring
  have htailbound : ((topExponent t + 1 - splitExponent t K : ℕ) : ℝ)
      * (2560 * (2 : ℝ) ^ (-θ)) ≤ 12800 * wideScale t := by
    have h1 : (2560 : ℝ) * (2 : ℝ) ^ (-θ) ≤ 2560 := by linarith [htail2]
    have h2 : (0 : ℝ) ≤ ((topExponent t + 1 - splitExponent t K : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith [mul_le_mul_of_nonneg_left h1 h2, hcast, hTle]
  have hfinal : (2 : ℝ) + wideScale t ^ (33 : ℕ) + 12800 * wideScale t
      ≤ wideScale t ^ (34 : ℕ) := by
    have h33 : (0 : ℝ) < wideScale t ^ (33 : ℕ) := by positivity
    have hone : (1 : ℝ) ≤ wideScale t := by linarith
    have h32 : (12800 : ℝ) ≤ wideScale t ^ (32 : ℕ) := by
      have hstep : wideScale t ≤ wideScale t ^ (32 : ℕ) := by
        calc wideScale t = wideScale t ^ (1 : ℕ) := by ring
          _ ≤ wideScale t ^ (32 : ℕ) := pow_le_pow_right₀ hone (by norm_num)
      linarith
    have hbig : (12800 : ℝ) * wideScale t ≤ wideScale t ^ (33 : ℕ) := by
      have heq : wideScale t ^ (32 : ℕ) * wideScale t = wideScale t ^ (33 : ℕ) := by ring
      linarith [mul_le_mul_of_nonneg_right h32 hL0.le]
    have h2small : (2 : ℝ) ≤ wideScale t ^ (33 : ℕ) := by linarith [h33, hbig, hL0]
    have hmul : (3 : ℝ) * wideScale t ^ (33 : ℕ) ≤ wideScale t * wideScale t ^ (33 : ℕ) := by
      exact mul_le_mul_of_nonneg_right (by linarith) h33.le
    have heq : wideScale t * wideScale t ^ (33 : ℕ) = wideScale t ^ (34 : ℕ) := by ring
    linarith [hmul, heq.le, heq.ge]
  linarith [hmain, hheadbound, htailbound, hfinal]

/-- **The rectangle bound at the wide order**, as a function of `t` alone. -/
theorem norm_dirichlet_wide_le {σ t : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (ht16 : 16 * Real.pi ≤ t) (hL : (10 : ℝ) ^ 16 ≤ wideScale t)
    (hstrip : 1 - σ ≤ wideEta t) :
    ‖∑ n ∈ Finset.Ico (1 : ℕ) (2 ^ (topExponent t + 1)),
        (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ wideScale t ^ (34 : ℕ) := by
  have hL12 : (10 : ℝ) ^ 12 ≤ wideScale t := by nlinarith
  have hK10 := ten_le_wideOrder hL12
  have hx := thirtyone_le_log_wideScale hL
  have hP : (0 : ℝ) < (2 : ℝ) ^ wideOrder t := by positivity
  have hKlo : wideScale t < 120 * (2 : ℝ) ^ wideOrder t * Real.log (wideScale t) ^ 2 := by
    have h := lt_two_pow_wideOrder_succ hL12
    have hpow : (2 : ℝ) ^ (wideOrder t + 1) = 2 * (2 : ℝ) ^ wideOrder t := by ring
    rw [hpow] at h
    nlinarith [h, hP]
  have hKhi : 100 * (2 : ℝ) ^ wideOrder t ≤ wideScale t := by
    have h := wideOrder_spec hL12
    have hgap : (0 : ℝ) ≤ (2 : ℝ) ^ wideOrder t * (Real.log (wideScale t) ^ 2 - 961) :=
      mul_nonneg hP.le (by nlinarith)
    nlinarith [h, hP, hgap]
  exact norm_dirichlet_wide_rect hσ0 hσ1 ht16 hL hK10 hKlo hKhi hstrip

end RHTower.Sieve

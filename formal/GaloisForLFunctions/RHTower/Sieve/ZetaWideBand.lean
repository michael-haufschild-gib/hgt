import GaloisForLFunctions.RHTower.Sieve.ZetaWideRectangle

/-!
# One order for a whole band of heights

`norm_riemannZeta_wide_le` is stated at a fixed order `K`, with the two hypotheses on `2^K` phrased
relative to `wideScale (Im w)`.  A Landau-type estimate needs the growth bound on a *disc*, and the
three-four-one argument needs it at the heights `γ`, `2γ` and `4γ` as well.  All of those live in
the band

```text
γ - 1 ≤ Im w ≤ 5γ ,
```

on which `wideScale` varies by at most a bounded additive amount:
`wideScale γ - 1 ≤ wideScale (Im w) ≤ wideScale γ + 3`.  The two hypotheses on `2^(wideOrder γ)`
survive that variation with room, because the wide order satisfies them with a factor `961 = 31²`
to spare on one side and a factor `1.87` on the other.
-/

namespace RHTower.Sieve

open Complex Metric

/-! ### Variation of the scale over the band -/

/-- `wideScale` is monotone in the height. -/
theorem wideScale_mono {t t' : ℝ} (ht : 0 < t) (h : t ≤ t') : wideScale t ≤ wideScale t' := by
  have hπ := Real.pi_pos
  refine Real.log_le_log (by positivity) ?_
  gcongr

/-- One step down costs at most `1`. -/
theorem wideScale_sub_one_ge {γ : ℝ} (hγ : 2 ≤ γ) : wideScale γ - 1 ≤ wideScale (γ - 1) := by
  have hπ := Real.pi_pos
  have hγ0 : (0 : ℝ) < γ := by linarith
  have hstep : γ / (4 * Real.pi) ≤ (γ - 1) / (2 * Real.pi) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h1 : Real.log (γ / (4 * Real.pi)) ≤ wideScale (γ - 1) :=
    Real.log_le_log (by positivity) hstep
  have h2 : Real.log (γ / (4 * Real.pi)) = wideScale γ - Real.log 2 := by
    have hrw : γ / (4 * Real.pi) = (γ / (2 * Real.pi)) / 2 := by
      rw [div_div]; ring_nf
    rw [hrw, Real.log_div (by positivity) (by norm_num)]
    rfl
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  rw [h2] at h1
  linarith

/-- Five steps up cost at most `3`. -/
theorem wideScale_five_le {γ : ℝ} (hγ : 0 < γ) : wideScale (5 * γ) ≤ wideScale γ + 3 := by
  have hπ := Real.pi_pos
  have hrw : 5 * γ / (2 * Real.pi) = 5 * (γ / (2 * Real.pi)) := by ring
  have hlog : wideScale (5 * γ) = Real.log 5 + wideScale γ := by
    rw [wideScale, hrw, Real.log_mul (by norm_num) (by positivity)]
    rfl
  have h5 : Real.log 5 ≤ 3 := by
    have h8 : Real.log 5 ≤ Real.log 8 := Real.log_le_log (by norm_num) (by norm_num)
    have h8eq : Real.log ((8 : ℝ)) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; norm_num
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    rw [h8eq] at h8
    linarith
  linarith [hlog.le, hlog.ge]

/-! ### The band estimate -/

set_option maxHeartbeats 1000000 in
/-- **`ζ` is polylogarithmic on the whole band, at the single order `wideOrder γ`.** -/
theorem norm_riemannZeta_wide_band {γ : ℝ} (hγ : 16 * Real.pi + 1 ≤ γ)
    (hL : (10 : ℝ) ^ 16 + 1 ≤ wideScale γ) {w : ℂ}
    (hre : 1 - 1 / (6 * (2 : ℝ) ^ wideOrder γ) ≤ w.re) (hre2 : w.re ≤ 2)
    (him1 : γ - 1 ≤ w.im) (him2 : w.im ≤ 5 * γ) :
    ‖riemannZeta w‖ ≤ (wideScale γ + 3) ^ (34 : ℕ) + 5 := by
  have hπ := Real.pi_pos
  have hπd : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hγ2 : (2 : ℝ) ≤ γ := by nlinarith
  have hγ0 : (0 : ℝ) < γ := by linarith
  have hLγ : (10 : ℝ) ^ 16 ≤ wideScale γ := by linarith
  have hL12 : (10 : ℝ) ^ 12 ≤ wideScale γ := by nlinarith
  have hL0 : (0 : ℝ) < wideScale γ := by nlinarith
  have hx := thirtyone_le_log_wideScale hLγ
  have hK10 := ten_le_wideOrder hL12
  have hP : (0 : ℝ) < (2 : ℝ) ^ wideOrder γ := by positivity
  -- the scale at the height of `w`
  have hlow : wideScale γ - 1 ≤ wideScale w.im := by
    have h1 := wideScale_sub_one_ge hγ2
    have h2 : wideScale (γ - 1) ≤ wideScale w.im :=
      wideScale_mono (by linarith) him1
    linarith
  have hhigh : wideScale w.im ≤ wideScale γ + 3 := by
    have h1 : wideScale w.im ≤ wideScale (5 * γ) := by
      refine wideScale_mono (by linarith) him2
    have h2 := wideScale_five_le hγ0
    linarith
  have hMlow : (10 : ℝ) ^ 16 ≤ wideScale w.im := by linarith
  have hM0 : (0 : ℝ) < wideScale w.im := by nlinarith
  have him16 : 16 * Real.pi ≤ w.im := by linarith
  -- the two order hypotheses transfer
  have hKhi : 100 * (2 : ℝ) ^ wideOrder γ ≤ wideScale w.im := by
    have hspec := wideOrder_spec hL12
    have hgap : (0 : ℝ) ≤ (2 : ℝ) ^ wideOrder γ * (Real.log (wideScale γ) ^ 2 - 961) :=
      mul_nonneg hP.le (by nlinarith)
    nlinarith [hspec, hP, hgap, hlow]
  have hKlo : wideScale w.im < 120 * (2 : ℝ) ^ wideOrder γ * Real.log (wideScale w.im) ^ 2 := by
    have hgt := lt_two_pow_wideOrder_succ hL12
    have hpow : (2 : ℝ) ^ (wideOrder γ + 1) = 2 * (2 : ℝ) ^ wideOrder γ := by ring
    rw [hpow] at hgt
    -- `log (wideScale w.im) ≥ log (wideScale γ) - 1`
    have hlogstep : Real.log (wideScale γ) - 1 ≤ Real.log (wideScale w.im) := by
      have h1 : Real.log (wideScale γ - 1) ≤ Real.log (wideScale w.im) :=
        Real.log_le_log (by nlinarith) hlow
      have h2 : Real.log (wideScale γ) - Real.log (wideScale γ - 1) ≤ 1 := by
        have hq : wideScale γ / (wideScale γ - 1) ≤ 2 := by
          rw [div_le_iff₀ (by nlinarith)]
          nlinarith
        have hd : Real.log (wideScale γ / (wideScale γ - 1))
            = Real.log (wideScale γ) - Real.log (wideScale γ - 1) :=
          Real.log_div (ne_of_gt hL0) (ne_of_gt (show (0 : ℝ) < wideScale γ - 1 by nlinarith))
        have hle : Real.log (wideScale γ / (wideScale γ - 1)) ≤ Real.log 2 :=
          Real.log_le_log (div_pos hL0 (by nlinarith)) hq
        have hlog2 : Real.log 2 ≤ 1 := by
          have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
        linarith [hd.le, hd.ge]
      linarith
    have hsqstep : (Real.log (wideScale γ)) ^ 2 * (900 / 961)
        ≤ Real.log (wideScale w.im) ^ 2 := by
      have hnn : (0 : ℝ) ≤ Real.log (wideScale γ) - 1 := by linarith
      have hbig : (Real.log (wideScale γ) - 1) ^ 2
          ≤ Real.log (wideScale w.im) ^ 2 := by nlinarith [hlogstep, hnn]
      nlinarith [hx, hbig]
    nlinarith [hgt, hP, hsqstep, hhigh, hL0]
  have hmain := norm_riemannZeta_wide_le (w := w) (K := wideOrder γ) hre hre2 him16 hMlow
    hK10 hKlo hKhi
  have hmono : wideScale w.im ^ (34 : ℕ) ≤ (wideScale γ + 3) ^ (34 : ℕ) :=
    pow_le_pow_left₀ (by linarith) hhigh 34
  linarith

end RHTower.Sieve

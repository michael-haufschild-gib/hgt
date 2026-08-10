import GaloisForLFunctions.RHTower.Sieve.ZetaLittlewoodRegion

/-!
# The logarithmic derivative on the wide strip

Landau's lemma bounds `−Re ζ'/ζ` by its remainder `16 log M / R` once every retained zero is
discarded — legitimate, because a zero left of the centre contributes a nonnegative real part.  On a
disc of radius `≍ 1` with the crude growth bound the remainder is `≍ log|γ|`, which is the classical
estimate.  On the wide disc of radius `wideEta γ ≍ (log log γ)²/log γ` the growth bound is
polylogarithmic, so the remainder is

```text
16 log M / R  ≍  log log γ · log γ / (log log γ)²  =  log γ / log log γ ,
```

one logarithm better.  Nothing here uses a zero-free region: only the wide rectangle bound and the
three-four-one lower bound for `‖ζ‖` at the centre.
-/

namespace RHTower.Sieve

open Complex Metric

/-- The growth bound on a wide disc centred right of the abscissa. -/
theorem wide_ball_growth {γ δ h : ℝ} (hγ : 16 * Real.pi + 1 ≤ γ)
    (hL : (10 : ℝ) ^ 16 + 1 ≤ wideScale γ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 16)
    (hη : wideEta γ ≤ 1 / 1000) (hh1 : γ ≤ h) (hh2 : h ≤ 4 * γ) :
    ∀ w ∈ ball (((1 + δ : ℝ) : ℂ) + ((h : ℝ) : ℂ) * Complex.I) (wideEta γ),
      ‖riemannZeta w‖ < (wideScale γ + 3) ^ (34 : ℕ) + 6 := by
  intro w hw
  have hπd : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hπ := Real.pi_pos
  have hγ3 : (3 : ℝ) ≤ γ := by nlinarith
  have hd : ‖w - (((1 + δ : ℝ) : ℂ) + ((h : ℝ) : ℂ) * Complex.I)‖ < wideEta γ := by
    simpa [dist_eq_norm] using hw
  have hcre : (((1 + δ : ℝ) : ℂ) + ((h : ℝ) : ℂ) * Complex.I).re = 1 + δ := by simp
  have hcim : (((1 + δ : ℝ) : ℂ) + ((h : ℝ) : ℂ) * Complex.I).im = h := by simp
  have hre : |w.re - (1 + δ)| < wideEta γ := by
    have h1 := Complex.abs_re_le_norm (w - (((1 + δ : ℝ) : ℂ) + ((h : ℝ) : ℂ) * Complex.I))
    rw [Complex.sub_re, hcre] at h1
    linarith
  have him : |w.im - h| < wideEta γ := by
    have h1 := Complex.abs_im_le_norm (w - (((1 + δ : ℝ) : ℂ) + ((h : ℝ) : ℂ) * Complex.I))
    rw [Complex.sub_im, hcim] at h1
    linarith
  have hre' := abs_lt.mp hre
  have him' := abs_lt.mp him
  refine wide_disc_growth hγ hL hδ0 hδ (w := w) ?_ ?_ ?_ ?_
  · linarith [hre'.1]
  · linarith [hre'.2]
  · linarith [him'.1]
  · linarith [him'.2]

set_option maxHeartbeats 800000 in
/-- **The logarithmic derivative on the wide strip.**  The remainder of Landau's estimate at radius
`wideEta γ / 2`, with the polylogarithmic growth bound of the wide rectangle. -/
theorem neg_re_logDeriv_le_wide {γ δ : ℝ} (hγ : 16 * Real.pi + 1 ≤ γ)
    (hL : (10 : ℝ) ^ 16 + 1 ≤ wideScale γ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 16) :
    -(logDeriv riemannZeta (((1 + δ : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).re
      ≤ 32 / wideEta γ
          * (5 / 4 * Real.log ((wideScale γ + 3) ^ (34 : ℕ) + 6)
            + 3 / 4 * Real.log (1 + 1 / δ) + 6) := by
  have hπ := Real.pi_pos
  have hπd : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hγ3 : (3 : ℝ) ≤ γ := by nlinarith
  have hγ0 : (0 : ℝ) < γ := by linarith
  have hL16 : (10 : ℝ) ^ 16 ≤ wideScale γ := by linarith
  have hL12 : (10 : ℝ) ^ 12 ≤ wideScale γ := by nlinarith
  have hL0 : (0 : ℝ) < wideScale γ := by nlinarith
  -- the disc radius
  have hηpos : 0 < wideEta γ := by
    have hx := thirtyone_le_log_wideScale hL16
    have h1 : (0 : ℝ) < 5 * Real.log (wideScale γ) ^ 2 / wideScale γ := by positivity
    have := wideEta_ge hL12
    linarith
  have hηsmall : wideEta γ ≤ 1 / 1000 := by
    have hK := ten_le_wideOrder hL12
    have hbig : (1024 : ℝ) ≤ (2 : ℝ) ^ wideOrder γ := by
      calc (1024 : ℝ) = (2 : ℝ) ^ (10 : ℕ) := by norm_num
        _ ≤ (2 : ℝ) ^ wideOrder γ := pow_le_pow_right₀ (by norm_num) hK
    have hval : wideEta γ = 1 / (6 * (2 : ℝ) ^ wideOrder γ) := rfl
    rw [hval, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  set Φ : ℝ := (wideScale γ + 3) ^ (34 : ℕ) + 6 with hΦdef
  have hΦ1 : (1 : ℝ) ≤ Φ := by
    have : (0 : ℝ) ≤ (wideScale γ + 3) ^ (34 : ℕ) := by positivity
    rw [hΦdef]; linarith
  set c : ℂ := ((1 + δ : ℝ) : ℂ) + (γ : ℂ) * Complex.I with hcdef
  have hcre : c.re = 1 + δ := by rw [hcdef]; simp
  have hcim : c.im = γ := by rw [hcdef]; simp
  -- the ball avoids the pole
  have hne : ∀ w ∈ ball c (wideEta γ), w ≠ 1 := by
    intro w hw hcon
    subst hcon
    have hd : ‖(1 : ℂ) - c‖ < wideEta γ := by simpa [dist_eq_norm] using hw
    have h1 : |((1 : ℂ) - c).im| ≤ ‖(1 : ℂ) - c‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, hcim] at h1
    simp only [Complex.one_im, zero_sub, abs_neg] at h1
    rw [abs_of_pos hγ0] at h1
    linarith
  have hgrow : ∀ w ∈ ball c (wideEta γ), ‖riemannZeta w‖ < Φ := by
    intro w hw
    exact wide_ball_growth hγ hL hδ0 hδ hηsmall le_rfl (by linarith) w (by simpa [hcdef] using hw)
  have hcΦ : ‖riemannZeta c‖ < Φ := hgrow c (Metric.mem_ball_self hηpos)
  have hc1 : (1 : ℝ) ≤ c.re := by rw [hcre]; linarith
  -- Landau at radius `wideEta γ / 2`
  have hmain := neg_re_logDeriv_le_of_bound (c := c) (R := wideEta γ / 2) (R₀ := wideEta γ)
    (Φ := Φ) (by linarith) (by linarith) hne (fun w hw => (hgrow w hw).le) hc1 hcΦ
  -- the lower bound for `‖ζ(c)‖`
  have hz1pos : (0 : ℝ) < ‖riemannZeta c‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re hc1)
  have hB1 : ‖riemannZeta (((1 + δ : ℝ) : ℂ) + (2 * γ : ℂ) * Complex.I)‖ ≤ Φ := by
    have hcast : ((2 * γ : ℂ)) = ((2 * γ : ℝ) : ℂ) := by push_cast; ring
    rw [hcast]
    refine le_of_lt (wide_ball_growth hγ hL hδ0 hδ hηsmall (h := 2 * γ) (by linarith)
      (by linarith) _ (Metric.mem_ball_self hηpos))
  have hden := neg_log_norm_riemannZeta_le_of (σ := 1 + δ) (t := γ) (Φ := Φ)
    (by linarith) hB1
  have hδeq : Real.log (1 + 1 / ((1 + δ) - 1)) = Real.log (1 + 1 / δ) := by
    congr 2
    ring_nf
  rw [hδeq] at hden
  have hM : Real.log (Φ / ‖riemannZeta c‖)
      ≤ 5 / 4 * Real.log Φ + 3 / 4 * Real.log (1 + 1 / δ) + 6 := by
    rw [Real.log_div (by linarith) (ne_of_gt hz1pos)]
    rw [hcdef]
    linarith
  -- combine
  have hηhalf : (0 : ℝ) < wideEta γ / 2 := by linarith
  have hmono : 16 * Real.log (Φ / ‖riemannZeta c‖) / (wideEta γ / 2)
      ≤ 16 * (5 / 4 * Real.log Φ + 3 / 4 * Real.log (1 + 1 / δ) + 6) / (wideEta γ / 2) :=
    div_le_div_of_nonneg_right (by linarith [hM]) hηhalf.le
  have heq : 16 * (5 / 4 * Real.log Φ + 3 / 4 * Real.log (1 + 1 / δ) + 6) / (wideEta γ / 2)
      = 32 / wideEta γ * (5 / 4 * Real.log Φ + 3 / 4 * Real.log (1 + 1 / δ) + 6) := by
    field_simp
    ring
  rw [heq] at hmono
  linarith [hmain, hmono]

set_option maxHeartbeats 800000 in
/-- **`−Re ζ'/ζ ≪ log γ / log log γ`.**  At the abscissa `1 + 1/L`, `L = log(γ/2π)`, the wide
Landau remainder collapses to `288 L / log L` — the classical estimate is `≍ L`. -/
theorem neg_re_logDeriv_le_wide_rate {γ : ℝ} (hγ : 16 * Real.pi + 1 ≤ γ)
    (hL : (10 : ℝ) ^ 16 + 1 ≤ wideScale γ) :
    -(logDeriv riemannZeta (((1 + 1 / wideScale γ : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).re
      ≤ 288 * wideScale γ / Real.log (wideScale γ) := by
  have hL16 : (10 : ℝ) ^ 16 ≤ wideScale γ := by linarith
  have hL12 : (10 : ℝ) ^ 12 ≤ wideScale γ := by nlinarith
  have hL0 : (0 : ℝ) < wideScale γ := by nlinarith
  set L : ℝ := wideScale γ with hLdef
  set x : ℝ := Real.log L with hxdef
  have hx31 : (31 : ℝ) ≤ x := thirtyone_le_log_wideScale hL16
  have hxpos : (0 : ℝ) < x := by linarith
  have hδ0 : (0 : ℝ) < 1 / L := by positivity
  have hδ16 : 1 / L ≤ 1 / 16 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]
    linarith
  have hbase := neg_re_logDeriv_le_wide hγ hL hδ0 hδ16
  -- the two logarithms
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hlogΦ : Real.log ((L + 3) ^ (34 : ℕ) + 6) ≤ 34 * x + 35 := by
    have hpow : (6 : ℝ) ≤ (L + 3) ^ (34 : ℕ) := by
      have h1 : (6 : ℝ) ≤ L + 3 := by linarith
      calc (6 : ℝ) = 6 ^ (1 : ℕ) := by norm_num
        _ ≤ (L + 3) ^ (1 : ℕ) := by simpa using h1
        _ ≤ (L + 3) ^ (34 : ℕ) := pow_le_pow_right₀ (by linarith) (by norm_num)
    have hle : (L + 3) ^ (34 : ℕ) + 6 ≤ 2 * (L + 3) ^ (34 : ℕ) := by linarith
    have h1 : Real.log ((L + 3) ^ (34 : ℕ) + 6) ≤ Real.log (2 * (L + 3) ^ (34 : ℕ)) :=
      Real.log_le_log (by linarith) hle
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
    have h2 : Real.log (L + 3) ≤ Real.log 2 + x := by
      have h3 : Real.log (L + 3) ≤ Real.log (2 * L) :=
        Real.log_le_log (by linarith) (by linarith)
      rwa [Real.log_mul (by norm_num) (ne_of_gt hL0), ← hxdef] at h3
    push_cast at h1
    linarith
  have hlogδ : Real.log (1 + 1 / (1 / L)) ≤ 1 + x := by
    have hrw : 1 + 1 / (1 / L) = 1 + L := by
      rw [one_div_one_div]
    rw [hrw]
    have h1 : Real.log (1 + L) ≤ Real.log (2 * L) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (ne_of_gt hL0), ← hxdef] at h1
    linarith
  have hX : 5 / 4 * Real.log ((L + 3) ^ (34 : ℕ) + 6) + 3 / 4 * Real.log (1 + 1 / (1 / L)) + 6
      ≤ 45 * x := by linarith
  have hXnn : (0 : ℝ) ≤ 5 / 4 * Real.log ((L + 3) ^ (34 : ℕ) + 6)
      + 3 / 4 * Real.log (1 + 1 / (1 / L)) + 6 := by
    have h1 : (0 : ℝ) ≤ Real.log ((L + 3) ^ (34 : ℕ) + 6) := by
      refine Real.log_nonneg ?_
      have : (0 : ℝ) ≤ (L + 3) ^ (34 : ℕ) := by positivity
      linarith
    have h2 : (0 : ℝ) ≤ Real.log (1 + 1 / (1 / L)) := by
      refine Real.log_nonneg ?_
      have : (0 : ℝ) < 1 / (1 / L) := by positivity
      linarith
    linarith
  -- the radius
  have hηge := wideEta_ge hL12
  rw [← hLdef, ← hxdef] at hηge
  have hηpos : 0 < wideEta γ := by
    have : (0 : ℝ) < 5 * x ^ 2 / L := by positivity
    linarith
  have hfac : 32 / wideEta γ ≤ 32 * L / (5 * x ^ 2) := by
    rw [div_le_div_iff₀ hηpos (by positivity)]
    have h3 : 5 * x ^ 2 ≤ wideEta γ * L := by
      rw [div_le_iff₀ hL0] at hηge
      linarith
    nlinarith [h3, hL0, hxpos]
  have hprod : 32 / wideEta γ
      * (5 / 4 * Real.log ((L + 3) ^ (34 : ℕ) + 6) + 3 / 4 * Real.log (1 + 1 / (1 / L)) + 6)
      ≤ 288 * L / x := by
    have hstep : 32 / wideEta γ
        * (5 / 4 * Real.log ((L + 3) ^ (34 : ℕ) + 6) + 3 / 4 * Real.log (1 + 1 / (1 / L)) + 6)
        ≤ (32 * L / (5 * x ^ 2)) * (45 * x) := by
      have hR : (0 : ℝ) < 32 / wideEta γ := by positivity
      calc 32 / wideEta γ
            * (5 / 4 * Real.log ((L + 3) ^ (34 : ℕ) + 6)
              + 3 / 4 * Real.log (1 + 1 / (1 / L)) + 6)
          ≤ 32 / wideEta γ * (45 * x) := mul_le_mul_of_nonneg_left hX hR.le
        _ ≤ (32 * L / (5 * x ^ 2)) * (45 * x) :=
            mul_le_mul_of_nonneg_right hfac (by positivity)
    have heq : (32 * L / (5 * x ^ 2)) * (45 * x) = 288 * L / x := by
      field_simp
      ring
    linarith
  linarith [hbase, hprod]

end RHTower.Sieve

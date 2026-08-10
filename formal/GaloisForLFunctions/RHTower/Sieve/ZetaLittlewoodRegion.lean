import GaloisForLFunctions.RHTower.Sieve.ZetaWideBand
import GaloisForLFunctions.RHTower.Sieve.ZetaWideDLVP
import GaloisForLFunctions.RHTower.Sieve.ZetaPoleLogDeriv

/-!
# Littlewood's zero-free region

Feeding the wide rectangle into the de la Vallée Poussin inequality at the matching radius produces
a zero-free region of width `≍ log log t / log t`, one logarithm better than the classical
`1/log t`.

With `L = wideScale γ = log(γ/2π)` and `x = log L`, the parameters are

```text
R = wideEta γ / 2 ≍ x²/L ,     Φ = (L+3)^34 + 6 ,     δ = x/(4000 L) ,
```

so the remainder of the inequality is `(80/R)·(5/4 log Φ + 3/4 log(1+1/δ) + 6) ≤ 1472 L/x` while the
pole term is `3/δ = 12000 L/x`; a zero at distance `1 − β < x/(32000 L)` makes the left-hand side
exceed `128000 L/(9x) = 14222 L/x`, and `14222 > 13472`.  The margin is what pays for the additive
constant coming from the pole bound.

The width `x/(32000 L)` is `log log γ / (32000 log γ)` up to the shift `log 2π`.
-/

namespace RHTower.Sieve

open Complex Metric

/-- The growth bound on the two Landau discs and at the doubled-doubled height. -/
theorem wide_disc_growth {γ δ : ℝ} (hγ : 16 * Real.pi + 1 ≤ γ)
    (hL : (10 : ℝ) ^ 16 + 1 ≤ wideScale γ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 16)
    {w : ℂ} (hre1 : 1 - wideEta γ < w.re) (hre2 : w.re ≤ 2)
    (him1 : γ - 1 ≤ w.im) (him2 : w.im ≤ 5 * γ) :
    ‖riemannZeta w‖ < (wideScale γ + 3) ^ (34 : ℕ) + 6 := by
  have h := norm_riemannZeta_wide_band hγ hL (w := w) (by
    have : wideEta γ = 1 / (6 * (2 : ℝ) ^ wideOrder γ) := rfl
    rw [← this]; linarith) hre2 him1 him2
  linarith

set_option maxHeartbeats 1000000 in
/-- **Littlewood's zero-free region, with the threshold existential.** -/
theorem exists_littlewood_zero_free_region :
    ∃ T : ℝ, 3 ≤ T ∧
      ∀ β γ : ℝ, T ≤ γ → β ≤ 1 →
        1 - Real.log (wideScale γ) / (32000 * wideScale γ) < β →
        riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨A, hA⟩ := exists_pole_bound
  have hπ := Real.pi_pos
  have hπd : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  set A' : ℝ := max A 0 with hA'def
  have hA'0 : 0 ≤ A' := le_max_right _ _
  have hAA' : A ≤ A' := le_max_left _ _
  set L₀ : ℝ := max ((10 : ℝ) ^ 16 + 1) (4 * (A' + 1) ^ 2) with hL₀def
  have hL₀big : (10 : ℝ) ^ 16 + 1 ≤ L₀ := le_max_left _ _
  have hL₀sq : 4 * (A' + 1) ^ 2 ≤ L₀ := le_max_right _ _
  refine ⟨max (16 * Real.pi + 1) (2 * Real.pi * Real.exp L₀), ?_, ?_⟩
  · exact le_trans (by nlinarith) (le_max_left _ _)
  intro β γ hγT hβ1 hβc hzero
  have hγ16 : 16 * Real.pi + 1 ≤ γ := le_trans (le_max_left _ _) hγT
  have hγ3 : (3 : ℝ) ≤ γ := by nlinarith
  have hγ0 : (0 : ℝ) < γ := by linarith
  -- the scale is past the threshold
  set L : ℝ := wideScale γ with hLdef
  have hLL₀ : L₀ ≤ L := by
    have hexp : Real.exp L₀ ≤ γ / (2 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]
      have := le_trans (le_max_right _ _) hγT
      linarith
    have := Real.log_le_log (Real.exp_pos L₀) hexp
    rwa [Real.log_exp] at this
  have hL1 : (10 : ℝ) ^ 16 + 1 ≤ L := le_trans hL₀big hLL₀
  have hL16 : (10 : ℝ) ^ 16 ≤ L := by linarith
  have hL12 : (10 : ℝ) ^ 12 ≤ L := by nlinarith
  have hLpos : (0 : ℝ) < L := by nlinarith
  set x : ℝ := Real.log L with hxdef
  have hx31 : (31 : ℝ) ≤ x := thirtyone_le_log_wideScale hL16
  have hxpos : (0 : ℝ) < x := by linarith
  have hxL : x ≤ 2 * Real.sqrt L := wide_log_le_two_sqrt hLpos
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLpos.le
  have hsnn : (0 : ℝ) ≤ Real.sqrt L := Real.sqrt_nonneg L
  -- `L ≥ (A' + 1) x`
  have hsqA : 2 * (A' + 1) ≤ Real.sqrt L := by
    have h4 : 4 * (A' + 1) ^ 2 ≤ L := le_trans hL₀sq hLL₀
    nlinarith [hsq, hsnn, hA'0]
  have hLAx : (A' + 1) * x ≤ L := by nlinarith [hxL, hsqA, hsq, hsnn, hA'0]
  -- the parameters
  set δ : ℝ := x / (4000 * L) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ16 : δ ≤ 1 / 16 := by
    rw [hδdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hxL, hsq, hsnn]
  set η : ℝ := wideEta γ with hηdef
  have hηge : 5 * x ^ 2 / L ≤ η := by
    rw [hηdef, hxdef, hLdef]; exact wideEta_ge hL12
  have hηle : η ≤ 10 * x ^ 2 / L := by
    rw [hηdef, hxdef, hLdef]; exact wideEta_le hL12
  have hηpos : 0 < η := by
    have : (0 : ℝ) < 5 * x ^ 2 / L := by positivity
    linarith
  have hηsmall : η ≤ 1 / 1000 := by
    have hK := ten_le_wideOrder hL12
    have hbig : (1024 : ℝ) ≤ (2 : ℝ) ^ wideOrder γ := by
      calc (1024 : ℝ) = (2 : ℝ) ^ (10 : ℕ) := by norm_num
        _ ≤ (2 : ℝ) ^ wideOrder γ := pow_le_pow_right₀ (by norm_num) hK
    have hval : η = 1 / (6 * (2 : ℝ) ^ wideOrder γ) := rfl
    rw [hval, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hη1 : η ≤ 1 := by linarith
  set Φ : ℝ := (L + 3) ^ (34 : ℕ) + 6 with hΦdef
  have hΦ1 : (1 : ℝ) ≤ Φ := by
    have : (0 : ℝ) ≤ (L + 3) ^ (34 : ℕ) := by positivity
    rw [hΦdef]; linarith
  -- the growth bound on the discs
  have hball : ∀ (h : ℝ), γ ≤ h → h ≤ 4 * γ →
      ∀ w ∈ ball (((1 + δ : ℝ) : ℂ) + ((h : ℝ) : ℂ) * Complex.I) η, ‖riemannZeta w‖ < Φ := by
    intro h hh1 hh2 w hw
    have hd : ‖w - (((1 + δ : ℝ) : ℂ) + ((h : ℝ) : ℂ) * Complex.I)‖ < η := by
      simpa [dist_eq_norm] using hw
    have hcre : (((1 + δ : ℝ) : ℂ) + ((h : ℝ) : ℂ) * Complex.I).re = 1 + δ := by simp
    have hcim : (((1 + δ : ℝ) : ℂ) + ((h : ℝ) : ℂ) * Complex.I).im = h := by simp
    have hre : |w.re - (1 + δ)| < η := by
      have h1 := Complex.abs_re_le_norm (w - (((1 + δ : ℝ) : ℂ) + ((h : ℝ) : ℂ) * Complex.I))
      rw [Complex.sub_re, hcre] at h1
      linarith
    have him : |w.im - h| < η := by
      have h1 := Complex.abs_im_le_norm (w - (((1 + δ : ℝ) : ℂ) + ((h : ℝ) : ℂ) * Complex.I))
      rw [Complex.sub_im, hcim] at h1
      linarith
    have hre' := abs_lt.mp hre
    have him' := abs_lt.mp him
    refine wide_disc_growth hγ16 hL1 hδ0 hδ16 (w := w) ?_ ?_ ?_ ?_
    · rw [← hηdef]; linarith [hre'.1]
    · linarith [hre'.2, hηsmall]
    · linarith [him'.1, hηsmall]
    · linarith [him'.2, hηsmall]
  -- the three growth inputs
  have hΦa : ∀ w ∈ ball (((1 + δ : ℝ) : ℂ) + (γ : ℂ) * Complex.I) η, ‖riemannZeta w‖ < Φ := by
    intro w hw
    exact hball γ le_rfl (by linarith) w (by simpa using hw)
  have hΦb : ∀ w ∈ ball (((1 + δ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I) η,
      ‖riemannZeta w‖ < Φ := hball (2 * γ) (by linarith) (by linarith)
  have hΦc : ‖riemannZeta (((1 + δ : ℝ) : ℂ) + ((4 * γ : ℝ) : ℂ) * Complex.I)‖ ≤ Φ := by
    refine le_of_lt (hball (4 * γ) (by linarith) le_rfl _ ?_)
    exact Metric.mem_ball_self hηpos
  -- the zero is close enough
  have hβdist : 1 - β < x / (32000 * L) := by
    rw [hxdef, hLdef] at *
    linarith [hβc]
  have hgap0 : 0 < 1 + δ - β := by linarith
  have hgapsmall : 1 + δ - β < 9 * x / (32000 * L) := by
    have hrw : δ = 8 * x / (32000 * L) := by
      rw [hδdef]
      field_simp
      ring
    rw [hrw]
    have : 8 * x / (32000 * L) + x / (32000 * L) = 9 * x / (32000 * L) := by ring
    linarith [hβdist]
  have hclose : 1 + δ - β ≤ η / 4 := by
    have h1 : 9 * x / (32000 * L) ≤ 5 * x ^ 2 / L / 4 := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (mul_pos hxpos hLpos).le
        (by linarith : (0 : ℝ) ≤ 160000 * x - 36)]
    linarith [hgapsmall, hηge]
  -- the inequality
  have hdlvp := dlvp_inequality_of_bound hA hγ3 hδ0 hδ16 (R := η / 2) (R₀ := η)
    (by linarith) (by linarith) hη1 hΦa hΦb hΦc hΦ1 hβ1 (by linarith [hclose]) hzero
  -- the left side
  have hLHS : 128000 * L / (9 * x) < 4 / (1 + δ - β) := by
    have hpos : (0 : ℝ) < 9 * x / (32000 * L) := by positivity
    have hstep : 4 / (9 * x / (32000 * L)) < 4 / (1 + δ - β) :=
      div_lt_div_of_pos_left (by norm_num) hgap0 hgapsmall
    have heq : 4 / (9 * x / (32000 * L)) = 128000 * L / (9 * x) := by
      field_simp
      ring
    rw [heq] at hstep
    exact hstep
  -- the right side
  have hlogΦ : Real.log Φ ≤ 34 * x + 35 := by
    have hbase : (0 : ℝ) < L + 3 := by linarith
    have hpow : (6 : ℝ) ≤ (L + 3) ^ (34 : ℕ) := by
      have h1 : (6 : ℝ) ≤ L + 3 := by linarith
      calc (6 : ℝ) = 6 ^ (1 : ℕ) := by norm_num
        _ ≤ (L + 3) ^ (1 : ℕ) := by simpa using h1
        _ ≤ (L + 3) ^ (34 : ℕ) := pow_le_pow_right₀ (by linarith) (by norm_num)
    have hΦle : Φ ≤ 2 * (L + 3) ^ (34 : ℕ) := by rw [hΦdef]; linarith
    have h1 : Real.log Φ ≤ Real.log (2 * (L + 3) ^ (34 : ℕ)) :=
      Real.log_le_log (by linarith) hΦle
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have h2 : Real.log (L + 3) ≤ Real.log 2 + x := by
      have h3 : Real.log (L + 3) ≤ Real.log (2 * L) :=
        Real.log_le_log (by linarith) (by linarith)
      rwa [Real.log_mul (by norm_num) (ne_of_gt hLpos), ← hxdef] at h3
    push_cast at h1
    linarith
  have hlogδ : Real.log (1 + 1 / δ) ≤ 13 + x := by
    have hinv : 1 / δ = 4000 * L / x := by
      rw [hδdef]
      field_simp
    have hle : 1 + 1 / δ ≤ 8192 * L := by
      have hstep : 4000 * L / x ≤ 8191 * L := by
        rw [div_le_iff₀ hxpos]
        nlinarith [hx31, hLpos]
      rw [hinv]
      linarith
    have h1 : Real.log (1 + 1 / δ) ≤ Real.log (8192 * L) :=
      Real.log_le_log (by positivity) hle
    rw [Real.log_mul (by norm_num) (ne_of_gt hLpos), ← hxdef] at h1
    have h8 : Real.log ((8192 : ℝ)) = 13 * Real.log 2 := by
      rw [show (8192 : ℝ) = 2 ^ (13 : ℕ) by norm_num, Real.log_pow]; norm_num
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    rw [h8] at h1
    linarith
  set X : ℝ := 5 / 4 * Real.log Φ + 3 / 4 * Real.log (1 + 1 / δ) + 6 with hXdef
  have hX : X ≤ 46 * x := by rw [hXdef]; linarith
  have hXnn : (0 : ℝ) ≤ X := by
    have h1 : (0 : ℝ) ≤ Real.log Φ := Real.log_nonneg hΦ1
    have hinvpos : (0 : ℝ) < 1 / δ := by positivity
    have h2 : (0 : ℝ) ≤ Real.log (1 + 1 / δ) := Real.log_nonneg (by linarith)
    rw [hXdef]; linarith
  have hRfac : 80 / (η / 2) ≤ 32 * L / x ^ 2 := by
    have h1 : 5 * x ^ 2 / L ≤ η := hηge
    have h2 : (0 : ℝ) < η / 2 := by linarith
    rw [div_le_div_iff₀ h2 (by positivity)]
    have h3 : 5 * x ^ 2 ≤ η * L := by
      rw [div_le_iff₀ hLpos] at h1
      linarith
    nlinarith [h3, hLpos, hxpos]
  have hrem : 80 / (η / 2) * X ≤ 1472 * L / x := by
    have h1 : 80 / (η / 2) * X ≤ (32 * L / x ^ 2) * (46 * x) := by
      have hRpos : (0 : ℝ) < 80 / (η / 2) := by positivity
      calc 80 / (η / 2) * X ≤ 80 / (η / 2) * (46 * x) :=
            mul_le_mul_of_nonneg_left hX hRpos.le
        _ ≤ (32 * L / x ^ 2) * (46 * x) := by
            refine mul_le_mul_of_nonneg_right hRfac (by positivity)
    have h2 : (32 * L / x ^ 2) * (46 * x) = 1472 * L / x := by
      field_simp
      ring
    linarith
  have hpole : (3 : ℝ) / δ = 12000 * L / x := by
    rw [hδdef]
    field_simp
    ring
  -- the contradiction
  have hcomb : 128000 * L / (9 * x) < 12000 * L / x + 3 * A' + 1472 * L / x := by
    have := hdlvp
    rw [hpole] at this
    linarith [hLHS, hrem, hAA']
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 9 * x)] at hcomb
  have hexp1 : (12000 * L / x + 3 * A' + 1472 * L / x) * (9 * x)
      = 121248 * L + 27 * A' * x := by
    field_simp
    ring
  rw [hexp1] at hcomb
  nlinarith [hLAx, hA'0, hxpos]

end RHTower.Sieve

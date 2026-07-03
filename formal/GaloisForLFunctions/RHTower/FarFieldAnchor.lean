/-
The far-field anchor for the charge-conservation program (MWM lane, M1 arc — task #118).

Every conservation/deformation argument needs an endpoint where the charge is COMPUTED,
not just transported. This module provides it:

* `deckClass_of_nonvanishing` — a ball without zeros carries zero charge: any local
  `n`-th roots on the two charts have trivial deck class (the `m = 0` instance of
  `deckClass_single_zero`).
* `xi_ne_zero_of_one_lt_re` — ξ does not vanish to the right of `Re s = 1` (Euler
  product territory, via the banked ξ/ζ zero correspondence).
* `xi_deckClass_far_field` — the anchor: far boxes of the actual completed zeta carry
  zero charge at every level `n` (in particular every rung `n = 2^k`). This is the
  computable end the deformation chains of `DeckHomotopy` drain to.
-/
import GaloisForLFunctions.RHTower.XiDeck

namespace RHTower

open Complex Metric

/-- **Zero charge on zero-free balls.** If `f` is analytic and nonvanishing on the ball,
any local `n`-th roots on the two slit charts have trivial deck class. -/
theorem deckClass_of_nonvanishing {f G₁ G₂ : ℂ → ℂ} {a : ℂ} {R : ℝ} (hR : 0 < R)
    {n : ℕ} (hn : 0 < n)
    (hf : AnalyticOnNhd ℂ f (ball a R)) (hf0 : ∀ z ∈ ball a R, f z ≠ 0)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartR a R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartL a R))
    (hpG₁ : ∀ z ∈ chartR a R, G₁ z ^ n = f z)
    (hpG₂ : ∀ z ∈ chartL a R, G₂ z ^ n = f z) :
    deckClass G₁ G₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) = 1 := by
  have h := deckClass_single_zero (m := 0) hR hn hf hf0
    (fun z _ => by simp) hG₁ hG₂ hpG₁ hpG₂
  rw [h]
  simp

/-- ξ does not vanish on `Re s > 1`. -/
theorem xi_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : xi s ≠ 0 := by
  have h0 : 0 < s.re := lt_trans one_pos hs
  have h1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    simp at hs
  intro hxi
  exact riemannZeta_ne_zero_of_one_lt_re hs ((xi_eq_zero_iff h0 h1).mp hxi)

/-- A ball strictly to the right of `Re s = 1` stays there. -/
theorem ball_re_gt_one {a : ℂ} {R : ℝ} (hfar : 1 + R < a.re) :
    ∀ z ∈ ball a R, 1 < z.re := by
  intro z hz
  rw [mem_ball, Complex.dist_eq] at hz
  have h1 : |(z - a).re| ≤ ‖z - a‖ := abs_re_le_norm _
  have h2 : (z - a).re = z.re - a.re := by simp [Complex.sub_re]
  rw [h2] at h1
  have h3 : |z.re - a.re| < R := lt_of_le_of_lt h1 hz
  have h4 := (abs_lt.mp h3).1
  linarith

/-- **The far-field anchor.** Any local `n`-th roots of ξ on the charts of a ball lying
strictly to the right of `Re s = 1` have trivial deck class: far boxes carry zero
charge, at every level. The deformation chains of `DeckHomotopy` drain here. -/
theorem xi_deckClass_far_field {a : ℂ} {R : ℝ} (hR : 0 < R) (hfar : 1 + R < a.re)
    {n : ℕ} (hn : 0 < n) {G₁ G₂ : ℂ → ℂ}
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartR a R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartL a R))
    (hpG₁ : ∀ z ∈ chartR a R, G₁ z ^ n = xi z)
    (hpG₂ : ∀ z ∈ chartL a R, G₂ z ^ n = xi z) :
    deckClass G₁ G₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) = 1 :=
  deckClass_of_nonvanishing hR hn (xi_analyticOnNhd _)
    (fun z hz => xi_ne_zero_of_one_lt_re (ball_re_gt_one hfar z hz))
    hG₁ hG₂ hpG₁ hpG₂

end RHTower

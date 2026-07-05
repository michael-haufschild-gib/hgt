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
import GaloisForLFunctions.RHTower.DeckHomotopy

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

/-- **Far-field deformation anchor.** If a positive dominated deformation chain starts
from ξ on a far-right ball, then every endpoint root pair has trivial deck class. -/
theorem xi_deckClass_eq_one_of_far_field_deformation
    {F : ℕ → ℂ → ℂ} {G₁ G₂ K₁ K₂ : ℂ → ℂ}
    {a : ℂ} {R : ℝ} {n N : ℕ} (hR : 0 < R) (hn : 0 < n) (hN : 0 < N)
    (hfar : 1 + R < a.re)
    (hFan : ∀ i, 0 < i → i ≤ N → AnalyticOnNhd ℂ (F i) (chartR a R ∪ chartL a R))
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartR a R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartL a R))
    (hK₁ : AnalyticOnNhd ℂ K₁ (chartR a R)) (hK₂ : AnalyticOnNhd ℂ K₂ (chartL a R))
    (hpG₁ : ∀ z ∈ chartR a R, G₁ z ^ n = F 0 z)
    (hpG₂ : ∀ z ∈ chartL a R, G₂ z ^ n = F 0 z)
    (hF0R : ∀ z ∈ chartR a R, F 0 z = xi z)
    (hF0L : ∀ z ∈ chartL a R, F 0 z = xi z)
    (hpK₁ : ∀ z ∈ chartR a R, K₁ z ^ n = F N z)
    (hpK₂ : ∀ z ∈ chartL a R, K₂ z ^ n = F N z)
    (hclose : ∀ i, i < N →
      ∀ z ∈ chartR a R ∪ chartL a R, ‖F (i + 1) z - F i z‖ < ‖F i z‖) :
    deckClass K₁ K₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) = 1 := by
  have hdeform :=
    deckClass_deformation_invariant_of_pos_chain hR hn hN hFan hG₁ hG₂ hK₁ hK₂ hpG₁ hpG₂
      hpK₁ hpK₂ hclose
  have hpG₁xi : ∀ z ∈ chartR a R, G₁ z ^ n = xi z := by
    intro z hz
    rw [hpG₁ z hz, hF0R z hz]
  have hpG₂xi : ∀ z ∈ chartL a R, G₂ z ^ n = xi z := by
    intro z hz
    rw [hpG₂ z hz, hF0L z hz]
  exact hdeform.trans (xi_deckClass_far_field hR hfar hn hG₁ hG₂ hpG₁xi hpG₂xi)

end RHTower

namespace RHTower

open Complex Metric

/-- **Far-field relative deformation anchor.** A positive deformation chain that starts
from ξ on a far-right ball and is relatively `r < 1` close at every step has trivial
endpoint deck class, with U0 log control for every correction ratio. -/
theorem xi_deckClass_eq_one_of_far_field_relative_deformation
    {F : ℕ → ℂ → ℂ} {G₁ G₂ K₁ K₂ : ℂ → ℂ}
    {a : ℂ} {R r : ℝ} {n N : ℕ} (hR : 0 < R) (hn : 0 < n) (hN : 0 < N)
    (hr : r < 1) (hfar : 1 + R < a.re)
    (hFan : ∀ i, 0 < i → i ≤ N → AnalyticOnNhd ℂ (F i) (chartR a R ∪ chartL a R))
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartR a R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartL a R))
    (hK₁ : AnalyticOnNhd ℂ K₁ (chartR a R)) (hK₂ : AnalyticOnNhd ℂ K₂ (chartL a R))
    (hpG₁ : ∀ z ∈ chartR a R, G₁ z ^ n = F 0 z)
    (hpG₂ : ∀ z ∈ chartL a R, G₂ z ^ n = F 0 z)
    (hF0R : ∀ z ∈ chartR a R, F 0 z = xi z)
    (hF0L : ∀ z ∈ chartL a R, F 0 z = xi z)
    (hpK₁ : ∀ z ∈ chartR a R, K₁ z ^ n = F N z)
    (hpK₂ : ∀ z ∈ chartL a R, K₂ z ^ n = F N z)
    (hbase : ∀ i, i < N → ∀ z ∈ chartR a R ∪ chartL a R, F i z ≠ 0)
    (hrel : ∀ i, i < N →
      ∀ z ∈ chartR a R ∪ chartL a R, ‖(F (i + 1) z - F i z) / F i z‖ ≤ r) :
    deckClass K₁ K₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) = 1 ∧
      ∀ i, i < N → ∀ z ∈ chartR a R ∪ chartL a R,
        ‖Complex.log (F (i + 1) z / F i z)‖ ≤
          (1 - r)⁻¹ * ‖(F (i + 1) z - F i z) / F i z‖ := by
  have hrel_deform :=
    deckClass_deformation_invariant_of_relative_pos_chain hR hn hN hr hFan hG₁ hG₂ hK₁ hK₂
      hpG₁ hpG₂ hpK₁ hpK₂ hbase hrel
  have hpG₁xi : ∀ z ∈ chartR a R, G₁ z ^ n = xi z := by
    intro z hz
    rw [hpG₁ z hz, hF0R z hz]
  have hpG₂xi : ∀ z ∈ chartL a R, G₂ z ^ n = xi z := by
    intro z hz
    rw [hpG₂ z hz, hF0L z hz]
  constructor
  · exact hrel_deform.1.trans (xi_deckClass_far_field hR hfar hn hG₁ hG₂ hpG₁xi hpG₂xi)
  · exact hrel_deform.2

end RHTower

namespace RHTower

open Complex Metric

/-- **Far-field relative deformation anchor with base nonvanishing discharged.**
The level-0 ξ identity on a far-right ball supplies nonvanishing; relative `r < 1`
control propagates it through the chain before anchoring the endpoint deck class. -/
theorem xi_deckClass_eq_one_of_far_field_relative_base_deformation
    {F : ℕ → ℂ → ℂ} {G₁ G₂ K₁ K₂ : ℂ → ℂ}
    {a : ℂ} {R r : ℝ} {n N : ℕ} (hR : 0 < R) (hn : 0 < n) (hN : 0 < N)
    (hr : r < 1) (hfar : 1 + R < a.re)
    (hFan : ∀ i, 0 < i → i ≤ N → AnalyticOnNhd ℂ (F i) (chartR a R ∪ chartL a R))
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartR a R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartL a R))
    (hK₁ : AnalyticOnNhd ℂ K₁ (chartR a R)) (hK₂ : AnalyticOnNhd ℂ K₂ (chartL a R))
    (hpG₁ : ∀ z ∈ chartR a R, G₁ z ^ n = F 0 z)
    (hpG₂ : ∀ z ∈ chartL a R, G₂ z ^ n = F 0 z)
    (hF0R : ∀ z ∈ chartR a R, F 0 z = xi z)
    (hF0L : ∀ z ∈ chartL a R, F 0 z = xi z)
    (hpK₁ : ∀ z ∈ chartR a R, K₁ z ^ n = F N z)
    (hpK₂ : ∀ z ∈ chartL a R, K₂ z ^ n = F N z)
    (hrel : ∀ i, i < N →
      ∀ z ∈ chartR a R ∪ chartL a R, ‖(F (i + 1) z - F i z) / F i z‖ ≤ r) :
    deckClass K₁ K₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) = 1 ∧
      ∀ i, i < N → ∀ z ∈ chartR a R ∪ chartL a R,
        ‖Complex.log (F (i + 1) z / F i z)‖ ≤
          (1 - r)⁻¹ * ‖(F (i + 1) z - F i z) / F i z‖ := by
  have hF0 : ∀ z ∈ chartR a R ∪ chartL a R, F 0 z ≠ 0 := by
    intro z hz
    rcases hz with hzR | hzL
    · rw [hF0R z hzR]
      exact xi_ne_zero_of_one_lt_re (ball_re_gt_one hfar z hzR.2)
    · rw [hF0L z hzL]
      exact xi_ne_zero_of_one_lt_re (ball_re_gt_one hfar z hzL.2)
  have hrel_deform :=
    RHTower.deckClass_deformation_invariant_of_relative_base_chain hR hn hN hr hFan hG₁ hG₂
      hK₁ hK₂ hpG₁ hpG₂ hpK₁ hpK₂ hF0 hrel
  have hpG₁xi : ∀ z ∈ chartR a R, G₁ z ^ n = xi z := by
    intro z hz
    rw [hpG₁ z hz, hF0R z hz]
  have hpG₂xi : ∀ z ∈ chartL a R, G₂ z ^ n = xi z := by
    intro z hz
    rw [hpG₂ z hz, hF0L z hz]
  constructor
  · exact hrel_deform.1.trans (xi_deckClass_far_field hR hfar hn hG₁ hG₂ hpG₁xi hpG₂xi)
  · exact hrel_deform.2

end RHTower

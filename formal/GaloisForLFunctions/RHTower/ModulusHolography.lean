/-
Modulus-only holography (MWM lane, M6 — task #123).

The deck charge is computable from |f| ALONE on two circles: no phases, no root
choices, no argument principle. The engine is mathlib's zero-free Jensen lemma
(`AnalyticOnNhd.circleAverage_log_norm_of_ne_zero`, the harmonic mean value of
`log ‖h‖`), which pins the circle average of `log ‖f‖` for a peeled function to

  A(r) = m·log r + log ‖h(a)‖,

so the SLOPE of `A` between two radii is exactly the enclosed multiplicity `m`, and
the deck class is `exp(2πi·slope/n)`:

* `circleAverage_log_norm_single_zero` — the single-zero Jensen computation `A(r)`.
* `deckClass_eq_exp_circleAverage_slope` — **the holography formula**: the deck class
  of any roots equals the exponential of the two-circle slope of the circle-average of
  `log ‖f‖`. Boundary modulus determines the interior charge — the charter's
  bulk-from-boundary clause as a theorem.
* `xi_deckClass_eq_circleAverage_slope` — the instance on ξ: |ξ| on two circles
  determines the box charge of the completed zeta. This is what the R-series winding
  engines measured, now formal.
-/
import GaloisForLFunctions.RHTower.XiDeck
import Mathlib.Analysis.Complex.JensenFormula

namespace RHTower

open Complex Metric

/-- **Single-zero Jensen.** For `f = (z−a)^m·h` with `h` analytic nonvanishing on the
ball, the circle average of `log ‖f‖` at radius `r` is `m·log r + log ‖h a‖`. -/
theorem circleAverage_log_norm_single_zero {f h : ℂ → ℂ} {a : ℂ} {R r : ℝ} {m : ℕ}
    (hr : 0 < r) (hrR : r < R)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ ball a R, f z = (z - a) ^ m * h z) :
    Real.circleAverage (fun z => Real.log ‖f z‖) a r
      = (m : ℝ) * Real.log r + Real.log ‖h a‖ := by
  have habs : |r| = r := abs_of_pos hr
  have hcsub : closedBall a |r| ⊆ ball a R := by
    rw [habs]
    exact closedBall_subset_ball hrR
  have hEq : Set.EqOn (fun z => Real.log ‖f z‖)
      (fun z => (m : ℝ) * Real.log r + Real.log ‖h z‖) (sphere a |r|) := by
    intro z hz
    rw [habs] at hz
    have hzball : z ∈ ball a R := by
      rw [mem_ball]
      rw [mem_sphere] at hz
      rw [hz]
      exact hrR
    have hznorm : ‖z - a‖ = r := by
      rw [mem_sphere, Complex.dist_eq] at hz
      exact hz
    show Real.log ‖f z‖ = (m : ℝ) * Real.log r + Real.log ‖h z‖
    rw [hfact z hzball, norm_mul, norm_pow, hznorm,
      Real.log_mul (pow_ne_zero m hr.ne') (norm_ne_zero_iff.mpr (hh0 z hzball)),
      Real.log_pow]
  have hcont : ContinuousOn (fun z => Real.log ‖h z‖) (sphere a r) := by
    intro z hz
    have hzball : z ∈ ball a R := by
      rw [mem_ball]
      rw [mem_sphere] at hz
      rw [hz]
      exact hrR
    have h0 : ‖h z‖ ≠ 0 := norm_ne_zero_iff.mpr (hh0 z hzball)
    exact (ContinuousAt.comp (f := fun w : ℂ => ‖h w‖) (Real.continuousAt_log h0)
      ((hh z hzball).continuousAt.norm)).continuousWithinAt
  have hint : CircleIntegrable (fun z => Real.log ‖h z‖) a r :=
    ContinuousOn.circleIntegrable hr.le hcont
  have hsplit := Real.circleAverage_fun_add
    (f₁ := fun _ : ℂ => (m : ℝ) * Real.log r) (f₂ := fun z => Real.log ‖h z‖)
    (circleIntegrable_const _ _ _) hint
  have hh' : AnalyticOnNhd ℂ h (closedBall a |r|) := fun z hz => hh z (hcsub hz)
  have hh0' : ∀ u ∈ closedBall a |r|, h u ≠ 0 := fun u hu => hh0 u (hcsub hu)
  rw [Real.circleAverage_congr_sphere hEq, hsplit, Real.circleAverage_const,
    hh'.circleAverage_log_norm_of_ne_zero hh0']

/-- **The holography formula.** The deck class of ANY local `n`-th roots of a peeled
function equals the exponential of the two-circle slope of the circle-average of
`log ‖f‖`: the boundary MODULUS on two circles determines the interior charge. -/
theorem deckClass_eq_exp_circleAverage_slope {f h G₁ G₂ : ℂ → ℂ} {a : ℂ}
    {R r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) (hr₂R : r₂ < R)
    {m n : ℕ} (hn : 0 < n)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ ball a R, f z = (z - a) ^ m * h z)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartR a R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartL a R))
    (hpG₁ : ∀ z ∈ chartR a R, G₁ z ^ n = f z)
    (hpG₂ : ∀ z ∈ chartL a R, G₂ z ^ n = f z) :
    deckClass G₁ G₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) =
      exp (2 * (Real.pi : ℂ) * I *
        (((Real.circleAverage (fun z => Real.log ‖f z‖) a r₂ -
            Real.circleAverage (fun z => Real.log ‖f z‖) a r₁) /
          (Real.log r₂ - Real.log r₁) : ℝ) : ℂ) / n) := by
  have hR : 0 < R := hr₁.trans (hr₁₂.trans hr₂R)
  have hslope : (Real.circleAverage (fun z => Real.log ‖f z‖) a r₂ -
      Real.circleAverage (fun z => Real.log ‖f z‖) a r₁) /
      (Real.log r₂ - Real.log r₁) = (m : ℝ) := by
    rw [circleAverage_log_norm_single_zero (hr₁.trans hr₁₂) hr₂R hh hh0 hfact,
      circleAverage_log_norm_single_zero hr₁ (hr₁₂.trans hr₂R) hh hh0 hfact]
    have hlog : Real.log r₁ < Real.log r₂ := Real.log_lt_log hr₁ hr₁₂
    rw [div_eq_iff (sub_ne_zero.mpr hlog.ne')]
    ring
  rw [hslope, show (((m : ℕ) : ℝ) : ℂ) = ((m : ℕ) : ℂ) from by norm_cast]
  exact deckClass_single_zero hR hn hh hh0 hfact hG₁ hG₂ hpG₁ hpG₂

/-- **|ξ| on two circles determines the box charge of the completed zeta.** Around any
point there is `R₀ > 0` such that for all admissible radii, the deck class of any
local `n`-th roots of ξ equals the exponential of the two-circle slope of the
circle-average of `log ‖ξ‖` — the formal version of what the winding measurements
compute. -/
theorem xi_deckClass_eq_circleAverage_slope (ρ₀ : ℂ) :
    ∃ R₀ > 0, ∀ {R r₁ r₂ : ℝ}, 0 < r₁ → r₁ < r₂ → r₂ < R → R ≤ R₀ →
      ∀ {n : ℕ}, 0 < n → ∀ {G₁ G₂ : ℂ → ℂ},
      AnalyticOnNhd ℂ G₁ (chartR ρ₀ R) → AnalyticOnNhd ℂ G₂ (chartL ρ₀ R) →
      (∀ z ∈ chartR ρ₀ R, G₁ z ^ n = xi z) → (∀ z ∈ chartL ρ₀ R, G₂ z ^ n = xi z) →
      deckClass G₁ G₂ (ρ₀ + ((R / 2 : ℝ) : ℂ) * I) (ρ₀ - ((R / 2 : ℝ) : ℂ) * I) =
        exp (2 * (Real.pi : ℂ) * I *
          (((Real.circleAverage (fun z => Real.log ‖xi z‖) ρ₀ r₂ -
              Real.circleAverage (fun z => Real.log ‖xi z‖) ρ₀ r₁) /
            (Real.log r₂ - Real.log r₁) : ℝ) : ℂ) / n) := by
  obtain ⟨R₀, hR₀, h, hhan, hh0, hfact⟩ := xi_peel_ball ρ₀
  refine ⟨R₀, hR₀, ?_⟩
  intro R r₁ r₂ hr₁ hr₁₂ hr₂R hRle n hn G₁ G₂ hG₁ hG₂ hp₁ hp₂
  have hsub : ball ρ₀ R ⊆ ball ρ₀ R₀ := ball_subset_ball hRle
  exact deckClass_eq_exp_circleAverage_slope hr₁ hr₁₂ hr₂R hn
    (fun z hz => hhan z (hsub hz)) (fun z hz => hh0 z (hsub hz))
    (fun z hz => hfact z (hsub hz)) hG₁ hG₂ hp₁ hp₂

end RHTower

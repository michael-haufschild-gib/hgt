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
import GaloisForLFunctions.RHTower.ReflectionParity
import GaloisForLFunctions.RHTower.GermExtension
import GaloisForLFunctions.RHTower.SquareLadder
import GaloisForLFunctions.RHTower.PerturbationZero
import GaloisForLFunctions.RHTower.WindowRelation
import GaloisForLFunctions.RHTower.SeamCocycle
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

namespace RHTower

open Complex Metric

/-- The two-circle modulus slope of ξ is the local vanishing order. -/
theorem xi_circleAverage_slope_eq_order (ρ₀ : ℂ) :
    ∃ R₀ > 0, ∀ {R r₁ r₂ : ℝ}, 0 < r₁ → r₁ < r₂ → r₂ < R → R ≤ R₀ →
      (Real.circleAverage (fun z => Real.log ‖xi z‖) ρ₀ r₂ -
          Real.circleAverage (fun z => Real.log ‖xi z‖) ρ₀ r₁) /
        (Real.log r₂ - Real.log r₁) = ((analyticOrderAt xi ρ₀).toNat : ℝ) := by
  obtain ⟨R₀, hR₀, h, hhan, hh0, hfact⟩ := xi_peel_ball ρ₀
  refine ⟨R₀, hR₀, ?_⟩
  intro R r₁ r₂ hr₁ hr₁₂ hr₂R hRle
  have hsub : ball ρ₀ R ⊆ ball ρ₀ R₀ := ball_subset_ball hRle
  rw [circleAverage_log_norm_single_zero (hr₁.trans hr₁₂) hr₂R
      (fun z hz => hhan z (hsub hz)) (fun z hz => hh0 z (hsub hz))
      (fun z hz => hfact z (hsub hz)),
    circleAverage_log_norm_single_zero hr₁ (hr₁₂.trans hr₂R)
      (fun z hz => hhan z (hsub hz)) (fun z hz => hh0 z (hsub hz))
      (fun z hz => hfact z (hsub hz))]
  have hlog : Real.log r₁ < Real.log r₂ := Real.log_lt_log hr₁ hr₁₂
  rw [div_eq_iff (sub_ne_zero.mpr hlog.ne')]
  ring

/-- Boundary modulus criterion for the local ξ rung: the two-circle slope of
`log ‖ξ‖` has trivial `2^k` exponential exactly when the local ladder divisibility
holds. -/
theorem xi_circleAverage_slope_exp_eq_one_iff_ladder_dvd (ρ₀ : ℂ) (k : ℕ) :
    ∃ R₀ > 0, ∀ {R r₁ r₂ : ℝ}, 0 < r₁ → r₁ < r₂ → r₂ < R → R ≤ R₀ →
      (exp (2 * (Real.pi : ℂ) * I *
          (((Real.circleAverage (fun z => Real.log ‖xi z‖) ρ₀ r₂ -
              Real.circleAverage (fun z => Real.log ‖xi z‖) ρ₀ r₁) /
            (Real.log r₂ - Real.log r₁) : ℝ) : ℂ) / (2 ^ k : ℕ)) = 1 ↔
        ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt xi ρ₀) := by
  obtain ⟨R₀, hR₀, hslope⟩ := xi_circleAverage_slope_eq_order ρ₀
  refine ⟨R₀, hR₀, ?_⟩
  intro R r₁ r₂ hr₁ hr₁₂ hr₂R hRle
  rw [hslope hr₁ hr₁₂ hr₂R hRle]
  have h2k : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hcast : ((((analyticOrderAt xi ρ₀).toNat : ℝ) : ℂ) =
      (((analyticOrderAt xi ρ₀).toNat : ℕ) : ℂ)) := by norm_cast
  rw [hcast, exp_two_pi_mul_div_eq_one_iff h2k]
  set m : ℕ := (analyticOrderAt xi ρ₀).toNat with hm_def
  have hm : (m : ℕ∞) = analyticOrderAt xi ρ₀ := ENat.coe_toNat (xi_orderAt_ne_top ρ₀)
  constructor
  · rintro ⟨c, hc⟩
    rw [← hm, hc]
    exact ⟨(c : ℕ∞), by push_cast; ring⟩
  · intro hdvd
    rw [← hm] at hdvd
    exact natCast_dvd_natCast_of_enat (pow_ne_zero k two_ne_zero) hdvd

end RHTower

namespace RHTower

open Complex Metric

/-- A ladder rung is equivalent to the corresponding modulus-slope root-of-unity
condition at every right-half zero of ξ. -/
theorem rhLadder_iff_circleAverage_slope_exp_eq_one (k : ℕ) :
    RHLadder k ↔
      ∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∃ R₀ > 0, ∀ {R r₁ r₂ : ℝ}, 0 < r₁ → r₁ < r₂ → r₂ < R → R ≤ R₀ →
          exp (2 * (Real.pi : ℂ) * I *
              (((Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₂ -
                  Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₁) /
                (Real.log r₂ - Real.log r₁) : ℝ) : ℂ) / (2 ^ k : ℕ)) = 1 := by
  constructor
  · intro hlad ρ hρ hzero
    obtain ⟨R₀, hR₀, hiff⟩ := xi_circleAverage_slope_exp_eq_one_iff_ladder_dvd ρ k
    refine ⟨R₀, hR₀, ?_⟩
    intro R r₁ r₂ hr₁ hr₁₂ hr₂R hRle
    exact (hiff hr₁ hr₁₂ hr₂R hRle).mpr (hlad ρ hρ hzero)
  · intro hmod ρ hρ hzero
    obtain ⟨R₁, hR₁, hiff⟩ := xi_circleAverage_slope_exp_eq_one_iff_ladder_dvd ρ k
    obtain ⟨R₂, hR₂, hexp⟩ := hmod ρ hρ hzero
    set Rm : ℝ := min R₁ R₂ with hRm_def
    have hRm_pos : 0 < Rm := by
      rw [hRm_def]
      exact lt_min hR₁ hR₂
    have hr₁ : 0 < Rm / 4 := by linarith
    have hr₁₂ : Rm / 4 < Rm / 2 := by linarith
    have hr₂R : Rm / 2 < Rm := by linarith
    have hRle₁ : Rm ≤ R₁ := by
      rw [hRm_def]
      exact min_le_left _ _
    have hRle₂ : Rm ≤ R₂ := by
      rw [hRm_def]
      exact min_le_right _ _
    have hcrit := hiff (R := Rm) (r₁ := Rm / 4) (r₂ := Rm / 2) hr₁ hr₁₂ hr₂R hRle₁
    have hval := hexp (R := Rm) (r₁ := Rm / 4) (r₂ := Rm / 2) hr₁ hr₁₂ hr₂R hRle₂
    exact hcrit.mp hval

/-- RH is equivalent to the all-level modulus-slope root-of-unity condition at
every right-half zero of ξ. -/
theorem rh_iff_forall_circleAverage_slope_exp_eq_one :
    RiemannHypothesis ↔
      ∀ k, ∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∃ R₀ > 0, ∀ {R r₁ r₂ : ℝ}, 0 < r₁ → r₁ < r₂ → r₂ < R → R ≤ R₀ →
          exp (2 * (Real.pi : ℂ) * I *
              (((Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₂ -
                  Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₁) /
                (Real.log r₂ - Real.log r₁) : ℝ) : ℂ) / (2 ^ k : ℕ)) = 1 := by
  rw [rh_iff_forall_ladder]
  constructor
  · intro h k
    exact (rhLadder_iff_circleAverage_slope_exp_eq_one k).mp (h k)
  · intro h k
    exact (rhLadder_iff_circleAverage_slope_exp_eq_one k).mpr (h k)

end RHTower

namespace RHTower

open Complex Metric

/-- The FE fixed-point parity makes the level-2 modulus slope root-of-unity
trivial at the central point. -/
theorem xi_central_circleAverage_slope_exp_eq_one :
    ∃ R₀ > 0, ∀ {R r₁ r₂ : ℝ}, 0 < r₁ → r₁ < r₂ → r₂ < R → R ≤ R₀ →
      exp (2 * (Real.pi : ℂ) * I *
          (((Real.circleAverage (fun z => Real.log ‖xi z‖) (1 / 2 : ℂ) r₂ -
              Real.circleAverage (fun z => Real.log ‖xi z‖) (1 / 2 : ℂ) r₁) /
            (Real.log r₂ - Real.log r₁) : ℝ) : ℂ) / 2) = 1 := by
  obtain ⟨R₀, hR₀, hiff⟩ :=
    xi_circleAverage_slope_exp_eq_one_iff_ladder_dvd (1 / 2 : ℂ) 1
  refine ⟨R₀, hR₀, ?_⟩
  intro R r₁ r₂ hr₁ hr₁₂ hr₂R hRle
  have hdiv : ((2 ^ 1 : ℕ) : ℕ∞) ∣ analyticOrderAt xi (1 / 2 : ℂ) := by
    simpa only [pow_one] using xi_central_ladder_two
  simpa only [pow_one, Nat.cast_ofNat] using (hiff hr₁ hr₁₂ hr₂R hRle).mpr hdiv

end RHTower

namespace RHTower

open Complex Metric

/-- At the FE fixed point, the two-circle modulus slope of ξ is an even integer. -/
theorem xi_central_circleAverage_slope_eq_even_integer :
    ∃ R₀ > 0, ∃ q : ℕ, ∀ {R r₁ r₂ : ℝ}, 0 < r₁ → r₁ < r₂ → r₂ < R → R ≤ R₀ →
      (Real.circleAverage (fun z => Real.log ‖xi z‖) (1 / 2 : ℂ) r₂ -
          Real.circleAverage (fun z => Real.log ‖xi z‖) (1 / 2 : ℂ) r₁) /
        (Real.log r₂ - Real.log r₁) = (2 * q : ℝ) := by
  obtain ⟨R₀, hR₀, hslope⟩ := xi_circleAverage_slope_eq_order (1 / 2 : ℂ)
  obtain ⟨q, hq⟩ := xi_central_order_even
  refine ⟨R₀, hR₀, q, ?_⟩
  intro R r₁ r₂ hr₁ hr₁₂ hr₂R hRle
  rw [hslope hr₁ hr₁₂ hr₂R hRle]
  have hq' : (analyticOrderAt xi (1 / 2 : ℂ)).toNat = 2 * q := by omega
  exact_mod_cast hq'

end RHTower

namespace RHTower

open Complex Metric

/-- Arithmetic germ continuation is equivalent to the boundary-modulus slope
criterion for the same ladder rung. -/
theorem germ_extends_iff_circleAverage_slope_exp_eq_one (k : ℕ) :
    (∀ g₁ : ℂ → ℂ, AnalyticOnNhd ℂ g₁ farHalf →
        (∀ s ∈ farHalf, g₁ s ^ 2 ^ k = xi s) →
        ∃ g, AnalyticOnNhd ℂ g rightHalf ∧ (∀ s ∈ rightHalf, g s ^ 2 ^ k = xi s) ∧
          Set.EqOn g g₁ farHalf) ↔
      ∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∃ R₀ > 0, ∀ {R r₁ r₂ : ℝ}, 0 < r₁ → r₁ < r₂ → r₂ < R → R ≤ R₀ →
          exp (2 * (Real.pi : ℂ) * I *
              (((Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₂ -
                  Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₁) /
                (Real.log r₂ - Real.log r₁) : ℝ) : ℂ) / (2 ^ k : ℕ)) = 1 := by
  rw [← rhLadder_iff_germ_extends k, rhLadder_iff_circleAverage_slope_exp_eq_one k]

end RHTower

namespace RHTower

open Complex Metric

/-- The slit-plane root formulation is equivalent to the boundary-modulus slope
criterion for the same ladder rung. -/
theorem root_slitPlane_iff_circleAverage_slope_exp_eq_one (k : ℕ) :
    (∃ g, AnalyticOnNhd ℂ g slitPlane ∧
        ∀ w ∈ slitPlane, g w ^ 2 ^ k = xiDescent w) ↔
      ∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∃ R₀ > 0, ∀ {R r₁ r₂ : ℝ}, 0 < r₁ → r₁ < r₂ → r₂ < R → R ≤ R₀ →
          exp (2 * (Real.pi : ℂ) * I *
              (((Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₂ -
                  Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₁) /
                (Real.log r₂ - Real.log r₁) : ℝ) : ℂ) / (2 ^ k : ℕ)) = 1 := by
  rw [← rhLadder_iff_root_slitPlane k, rhLadder_iff_circleAverage_slope_exp_eq_one k]

end RHTower

namespace RHTower

open Complex Metric

/-- Zero planting in a right-half ball forces a concrete failure of the all-level
boundary-modulus slope criterion. -/
theorem exists_circleAverage_slope_obstruction_of_sphere_domination_center_margin {g h : ℂ → ℂ}
    {s₀ : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hmargin : 1 / 2 + r < s₀.re)
    (hg : DiffContOnCl ℂ g (Metric.ball s₀ r))
    (hh : DiffContOnCl ℂ h (Metric.ball s₀ r))
    (hcenter : h s₀ = 0) (hg0 : g s₀ ≠ 0)
    (hdom : ∀ z ∈ Metric.sphere s₀ r, 3 * ‖g z‖ ≤ ‖h z‖)
    (hxi : ∀ z ∈ Metric.closedBall s₀ r, xi z = g z + h z) :
    ∃ k, ∃ ρ ∈ rightHalf, xi ρ = 0 ∧
      ¬ ∃ R₀ > 0, ∀ {R r₁ r₂ : ℝ}, 0 < r₁ → r₁ < r₂ → r₂ < R → R ≤ R₀ →
        exp (2 * (Real.pi : ℂ) * I *
            (((Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₂ -
                Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₁) /
              (Real.log r₂ - Real.log r₁) : ℝ) : ℂ) / (2 ^ k : ℕ)) = 1 := by
  classical
  have hnotRH := not_riemannHypothesis_of_sphere_domination_center_margin hr hmargin hg hh
    hcenter hg0 hdom hxi
  by_contra hno
  push Not at hno
  have hmod : ∀ k, ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ R₀ > 0, ∀ {R r₁ r₂ : ℝ}, 0 < r₁ → r₁ < r₂ → r₂ < R → R ≤ R₀ →
        exp (2 * (Real.pi : ℂ) * I *
            (((Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₂ -
                Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₁) /
              (Real.log r₂ - Real.log r₁) : ℝ) : ℂ) / (2 ^ k : ℕ)) = 1 := by
    intro k ρ hρ hzero
    exact hno k ρ hρ hzero
  exact hnotRH (rh_iff_forall_circleAverage_slope_exp_eq_one.mpr hmod)

end RHTower

namespace RHTower

open Complex Metric

/-- Zero planting in a right-half ball forces a local ladder obstruction: at some
right-half zero, a finite dyadic rung fails divisibility of the local ξ order. -/
theorem exists_ladder_order_obstruction_of_sphere_domination_center_margin {g h : ℂ → ℂ}
    {s₀ : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hmargin : 1 / 2 + r < s₀.re)
    (hg : DiffContOnCl ℂ g (Metric.ball s₀ r))
    (hh : DiffContOnCl ℂ h (Metric.ball s₀ r))
    (hcenter : h s₀ = 0) (hg0 : g s₀ ≠ 0)
    (hdom : ∀ z ∈ Metric.sphere s₀ r, 3 * ‖g z‖ ≤ ‖h z‖)
    (hxi : ∀ z ∈ Metric.closedBall s₀ r, xi z = g z + h z) :
    ∃ k, ∃ ρ ∈ rightHalf, xi ρ = 0 ∧ ¬ ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt xi ρ := by
  obtain ⟨k, ρ, hρ, hzero, hnotSlope⟩ :=
    exists_circleAverage_slope_obstruction_of_sphere_domination_center_margin hr hmargin hg hh
      hcenter hg0 hdom hxi
  refine ⟨k, ρ, hρ, hzero, ?_⟩
  intro hdiv
  obtain ⟨R₀, hR₀pos, hiff⟩ := xi_circleAverage_slope_exp_eq_one_iff_ladder_dvd ρ k
  exact hnotSlope ⟨R₀, hR₀pos, fun {R r₁ r₂} hr₁ hr₁₂ hr₂R hRle =>
    (hiff hr₁ hr₁₂ hr₂R hRle).mpr hdiv⟩

end RHTower

namespace RHTower

open Complex Metric

/-- Zero planting in a right-half ball forces a concrete failed two-circle
modulus-slope sample.  The radii are selected to be ξ-zero-free, so the output
is a directly checkable boundary obstruction rather than an all-radius schema. -/
theorem exists_clean_circleAverage_slope_obstruction_of_sphere_domination_center_margin
    {g h : ℂ → ℂ} {s₀ : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hmargin : 1 / 2 + r < s₀.re)
    (hg : DiffContOnCl ℂ g (Metric.ball s₀ r))
    (hh : DiffContOnCl ℂ h (Metric.ball s₀ r))
    (hcenter : h s₀ = 0) (hg0 : g s₀ ≠ 0)
    (hdom : ∀ z ∈ Metric.sphere s₀ r, 3 * ‖g z‖ ≤ ‖h z‖)
    (hxi : ∀ z ∈ Metric.closedBall s₀ r, xi z = g z + h z) :
    ∃ k, ∃ ρ ∈ rightHalf, xi ρ = 0 ∧
      ∃ R r₁ r₂ : ℝ, 0 < R ∧ 0 < r₁ ∧ r₁ < r₂ ∧ r₂ < R ∧
        (∀ z : ℂ, ‖z - ρ‖ = r₁ → xi z ≠ 0) ∧
        (∀ z : ℂ, ‖z - ρ‖ = r₂ → xi z ≠ 0) ∧
        exp (2 * (Real.pi : ℂ) * I *
            (((Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₂ -
                Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₁) /
              (Real.log r₂ - Real.log r₁) : ℝ) : ℂ) / (2 ^ k : ℕ)) ≠ 1 := by
  obtain ⟨k, ρ, hρ, hzero, hnotdiv⟩ :=
    exists_ladder_order_obstruction_of_sphere_domination_center_margin hr hmargin hg hh
      hcenter hg0 hdom hxi
  obtain ⟨R₀, hR₀pos, hiff⟩ := xi_circleAverage_slope_exp_eq_one_iff_ladder_dvd ρ k
  set R : ℝ := R₀ / 2 with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]
    linarith
  have hRle : R ≤ R₀ := by
    rw [hRdef]
    linarith
  obtain ⟨r₁, r₂, hr₁pos, hr₁₂, hr₂R, havoid₁, havoid₂⟩ :=
    exists_two_radii_avoiding_xi_zeros ρ (r := 0) (R := R) hRpos
  have hexp_ne : exp (2 * (Real.pi : ℂ) * I *
          (((Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₂ -
              Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₁) /
            (Real.log r₂ - Real.log r₁) : ℝ) : ℂ) / (2 ^ k : ℕ)) ≠ 1 := by
    intro hexp
    exact hnotdiv ((hiff hr₁pos hr₁₂ hr₂R hRle).mp hexp)
  exact ⟨k, ρ, hρ, hzero, R, r₁, r₂, hRpos, hr₁pos, hr₁₂, hr₂R,
    havoid₁, havoid₂, hexp_ne⟩

end RHTower

namespace RHTower

open Complex Metric

/-- Zero planting in a right-half ball obstructs far-half germ continuation at the
same dyadic level witnessed by a clean two-circle modulus sample. -/
theorem exists_germ_extension_obstruction_with_clean_modulus_witness_of_sphere_domination_center_margin
    {g h : ℂ → ℂ} {s₀ : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hmargin : 1 / 2 + r < s₀.re)
    (hg : DiffContOnCl ℂ g (Metric.ball s₀ r))
    (hh : DiffContOnCl ℂ h (Metric.ball s₀ r))
    (hcenter : h s₀ = 0) (hg0 : g s₀ ≠ 0)
    (hdom : ∀ z ∈ Metric.sphere s₀ r, 3 * ‖g z‖ ≤ ‖h z‖)
    (hxi : ∀ z ∈ Metric.closedBall s₀ r, xi z = g z + h z) :
    ∃ k,
      (¬ (∀ g₁ : ℂ → ℂ, AnalyticOnNhd ℂ g₁ farHalf →
        (∀ s ∈ farHalf, g₁ s ^ 2 ^ k = xi s) →
        ∃ G, AnalyticOnNhd ℂ G rightHalf ∧ (∀ s ∈ rightHalf, G s ^ 2 ^ k = xi s) ∧
          Set.EqOn G g₁ farHalf)) ∧
      ∃ ρ ∈ rightHalf, xi ρ = 0 ∧
        ∃ R r₁ r₂ : ℝ, 0 < R ∧ 0 < r₁ ∧ r₁ < r₂ ∧ r₂ < R ∧
          (∀ z : ℂ, ‖z - ρ‖ = r₁ → xi z ≠ 0) ∧
          (∀ z : ℂ, ‖z - ρ‖ = r₂ → xi z ≠ 0) ∧
          exp (2 * (Real.pi : ℂ) * I *
              (((Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₂ -
                  Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₁) /
                (Real.log r₂ - Real.log r₁) : ℝ) : ℂ) / (2 ^ k : ℕ)) ≠ 1 := by
  obtain ⟨k, ρ, hρ, hzero, hnotdiv⟩ :=
    exists_ladder_order_obstruction_of_sphere_domination_center_margin hr hmargin hg hh
      hcenter hg0 hdom hxi
  have hnotGerm : ¬ (∀ g₁ : ℂ → ℂ, AnalyticOnNhd ℂ g₁ farHalf →
        (∀ s ∈ farHalf, g₁ s ^ 2 ^ k = xi s) →
        ∃ G, AnalyticOnNhd ℂ G rightHalf ∧ (∀ s ∈ rightHalf, G s ^ 2 ^ k = xi s) ∧
          Set.EqOn G g₁ farHalf) := by
    intro hgerm
    have hlad : RHLadder k := (rhLadder_iff_germ_extends k).mpr hgerm
    exact hnotdiv (hlad ρ hρ hzero)
  obtain ⟨R₀, hR₀pos, hiff⟩ := xi_circleAverage_slope_exp_eq_one_iff_ladder_dvd ρ k
  set R : ℝ := R₀ / 2 with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]
    linarith
  have hRle : R ≤ R₀ := by
    rw [hRdef]
    linarith
  obtain ⟨r₁, r₂, hr₁pos, hr₁₂, hr₂R, havoid₁, havoid₂⟩ :=
    exists_two_radii_avoiding_xi_zeros ρ (r := 0) (R := R) hRpos
  have hexp_ne : exp (2 * (Real.pi : ℂ) * I *
          (((Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₂ -
              Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₁) /
            (Real.log r₂ - Real.log r₁) : ℝ) : ℂ) / (2 ^ k : ℕ)) ≠ 1 := by
    intro hexp
    exact hnotdiv ((hiff hr₁pos hr₁₂ hr₂R hRle).mp hexp)
  exact ⟨k, hnotGerm, ρ, hρ, hzero, R, r₁, r₂, hRpos, hr₁pos, hr₁₂, hr₂R,
    havoid₁, havoid₂, hexp_ne⟩

end RHTower

namespace RHTower

open Complex Metric

/-- **Clean two-circle modulus criterion.** In every sufficiently small nondegenerate
radius interval around `ρ₀`, Bottcher zero-avoidance selects two ξ-zero-free circles
whose modulus slope detects the same local dyadic ladder obstruction. -/
theorem exists_clean_radii_circleAverage_slope_exp_eq_one_iff_ladder_dvd
    (ρ₀ : ℂ) (k : ℕ) :
    ∃ R₀ > 0, ∀ {r R : ℝ}, 0 < r → r < R → R ≤ R₀ →
      ∃ r₁ r₂ : ℝ, r < r₁ ∧ r₁ < r₂ ∧ r₂ < R ∧
        (∀ z : ℂ, ‖z - ρ₀‖ = r₁ → xi z ≠ 0) ∧
        (∀ z : ℂ, ‖z - ρ₀‖ = r₂ → xi z ≠ 0) ∧
        (exp (2 * (Real.pi : ℂ) * I *
            (((Real.circleAverage (fun z => Real.log ‖xi z‖) ρ₀ r₂ -
                Real.circleAverage (fun z => Real.log ‖xi z‖) ρ₀ r₁) /
              (Real.log r₂ - Real.log r₁) : ℝ) : ℂ) / (2 ^ k : ℕ)) = 1 ↔
          ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt xi ρ₀) := by
  obtain ⟨R₀, hR₀pos, hiff⟩ := xi_circleAverage_slope_exp_eq_one_iff_ladder_dvd ρ₀ k
  refine ⟨R₀, hR₀pos, ?_⟩
  intro r R hr hrR hRle
  obtain ⟨r₁, r₂, hr₁, hr₁₂, hr₂R, havoid₁, havoid₂⟩ :=
    exists_two_radii_avoiding_xi_zeros ρ₀ hrR
  exact ⟨r₁, r₂, hr₁, hr₁₂, hr₂R, havoid₁, havoid₂,
    hiff (lt_trans hr hr₁) hr₁₂ hr₂R hRle⟩

end RHTower

namespace RHTower

open Complex Metric

/-- A ladder rung is equivalent to having arbitrarily small clean two-circle
modulus samples at every right-half ξ-zero.  The circles are chosen ξ-zero-free,
so the criterion is a boundary constraint rather than a local root-choice datum. -/
theorem rhLadder_iff_clean_circleAverage_slope_exp_eq_one (k : ℕ) :
    RHLadder k ↔
      ∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∃ R₀ > 0, ∀ {r R : ℝ}, 0 < r → r < R → R ≤ R₀ →
          ∃ r₁ r₂ : ℝ, r < r₁ ∧ r₁ < r₂ ∧ r₂ < R ∧
            (∀ z : ℂ, ‖z - ρ‖ = r₁ → xi z ≠ 0) ∧
            (∀ z : ℂ, ‖z - ρ‖ = r₂ → xi z ≠ 0) ∧
            exp (2 * (Real.pi : ℂ) * I *
                (((Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₂ -
                    Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₁) /
                  (Real.log r₂ - Real.log r₁) : ℝ) : ℂ) / (2 ^ k : ℕ)) = 1 := by
  constructor
  · intro hlad ρ hρ hzero
    obtain ⟨R₀, hR₀pos, hclean⟩ :=
      exists_clean_radii_circleAverage_slope_exp_eq_one_iff_ladder_dvd ρ k
    refine ⟨R₀, hR₀pos, ?_⟩
    intro r R hr hrR hRle
    obtain ⟨r₁, r₂, hr₁, hr₁₂, hr₂R, havoid₁, havoid₂, hiff⟩ :=
      hclean hr hrR hRle
    exact ⟨r₁, r₂, hr₁, hr₁₂, hr₂R, havoid₁, havoid₂,
      hiff.mpr (hlad ρ hρ hzero)⟩
  · intro hclean ρ hρ hzero
    obtain ⟨R₁, hR₁pos, hiff⟩ := xi_circleAverage_slope_exp_eq_one_iff_ladder_dvd ρ k
    obtain ⟨R₂, hR₂pos, hcleanρ⟩ := hclean ρ hρ hzero
    set Rm : ℝ := min R₁ R₂ with hRm_def
    have hRm_pos : 0 < Rm := by
      rw [hRm_def]
      exact lt_min hR₁pos hR₂pos
    have hr : 0 < Rm / 4 := by linarith
    have hrR : Rm / 4 < Rm / 2 := by linarith
    have hRle₁ : Rm / 2 ≤ R₁ := by
      have hRmle : Rm ≤ R₁ := by
        rw [hRm_def]
        exact min_le_left _ _
      linarith
    have hRle₂ : Rm / 2 ≤ R₂ := by
      have hRmle : Rm ≤ R₂ := by
        rw [hRm_def]
        exact min_le_right _ _
      linarith
    obtain ⟨r₁, r₂, hr₁, hr₁₂, hr₂R, _havoid₁, _havoid₂, hexp⟩ :=
      hcleanρ (r := Rm / 4) (R := Rm / 2) hr hrR hRle₂
    exact (hiff (R := Rm / 2) (r₁ := r₁) (r₂ := r₂)
      (lt_trans hr hr₁) hr₁₂ hr₂R hRle₁).mp hexp

end RHTower

namespace RHTower

open Complex Metric

/-- Clean two-circle modulus samples force the finite reflection-window relation.
This connects the boundary-modulus reader to the window-parity node without passing
through local root choices: the clean samples give the ladder rung, and the rung gives
the finite congruence for any reflection-closed ξ-zero configuration. -/
theorem xi_window_relation_of_clean_circleAverage_slope_exp_eq_one {k : ℕ}
    (hclean : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ R₀ > 0, ∀ {r R : ℝ}, 0 < r → r < R → R ≤ R₀ →
        ∃ r₁ r₂ : ℝ, r < r₁ ∧ r₁ < r₂ ∧ r₂ < R ∧
          (∀ z : ℂ, ‖z - ρ‖ = r₁ → xi z ≠ 0) ∧
          (∀ z : ℂ, ‖z - ρ‖ = r₂ → xi z ≠ 0) ∧
          exp (2 * (Real.pi : ℂ) * I *
              (((Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₂ -
                  Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₁) /
                (Real.log r₂ - Real.log r₁) : ℝ) : ℂ) / (2 ^ k : ℕ)) = 1)
    {t : Finset ℂ} {m : ℂ → ℕ}
    (hzero : ∀ z ∈ t, xi z = 0)
    (hm : ∀ z ∈ t, (m z : ℕ∞) = analyticOrderAt xi z)
    (hclosed : ∀ z ∈ t, lineReflect z ∈ t) :
    ∑ z ∈ t, m z ≡
      ∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z [MOD 2 ^ (k + 1)] := by
  have hlad : RHLadder k := (rhLadder_iff_clean_circleAverage_slope_exp_eq_one k).mpr hclean
  exact xi_window_relation_of_ladder hlad hzero hm hclosed

end RHTower

namespace RHTower

open Complex Metric Finset

/-- **Clean boundary modulus equals the complete finite-window surface.**  All-level
clean two-circle modulus samples around right-half ξ-zeros are equivalent to the
all-level congruence for every finite reflection-closed ξ-zero window.  The bridge is
constraint-only: clean boundary data gives each ladder rung, and the window surface
is the complete all-rung finite obstruction. -/
theorem all_clean_circleAverage_slope_exp_eq_one_iff_all_finite_window_relations_all_levels :
    (∀ k : ℕ, ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ R₀ > 0, ∀ {r R : ℝ}, 0 < r → r < R → R ≤ R₀ →
        ∃ r₁ r₂ : ℝ, r < r₁ ∧ r₁ < r₂ ∧ r₂ < R ∧
          (∀ z : ℂ, ‖z - ρ‖ = r₁ → xi z ≠ 0) ∧
          (∀ z : ℂ, ‖z - ρ‖ = r₂ → xi z ≠ 0) ∧
          exp (2 * (Real.pi : ℂ) * I *
              (((Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₂ -
                  Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₁) /
                (Real.log r₂ - Real.log r₁) : ℝ) : ℂ) / (2 ^ k : ℕ)) = 1) ↔
      ∀ k : ℕ, ∀ (t : Finset ℂ) (m : ℂ → ℕ),
        (∀ z ∈ t, xi z = 0) →
        (∀ z ∈ t, (m z : ℕ∞) = analyticOrderAt xi z) →
        (∀ z ∈ t, lineReflect z ∈ t) →
        (∑ z ∈ t, m z ≡
          ∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z [MOD 2 ^ (k + 1)]) := by
  constructor
  · intro hclean k t m hzero hm hclosed
    exact xi_window_relation_of_clean_circleAverage_slope_exp_eq_one (hclean k)
      hzero hm hclosed
  · intro hwin k
    have hRH : RiemannHypothesis :=
      (rh_iff_all_finite_window_relations_all_levels).mpr hwin
    exact (rhLadder_iff_clean_circleAverage_slope_exp_eq_one k).mp
      ((rh_iff_forall_ladder.mp hRH) k)

end RHTower

namespace RHTower

open Complex Metric

/-- **Far-field relative deformation gives endpoint boundary zero-charge.**  If the
relative chain starts from ξ on a far-right ball and the endpoint admits a local peel
at the chart centre, then the endpoint's two-circle boundary-modulus slope has
trivial level-`n` exponential; the U0 log bounds for the chain are preserved. -/
theorem endpoint_circleAverage_slope_exp_eq_one_of_far_field_relative_base_deformation
    {F : ℕ → ℂ → ℂ} {G₁ G₂ K₁ K₂ H : ℂ → ℂ}
    {a : ℂ} {R r r₁ r₂ : ℝ} {n N m : ℕ}
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) (hr₂R : r₂ < R)
    (hn : 0 < n) (hN : 0 < N) (hr : r < 1) (hfar : 1 + R < a.re)
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
      ∀ z ∈ chartR a R ∪ chartL a R, ‖(F (i + 1) z - F i z) / F i z‖ ≤ r)
    (hH : AnalyticOnNhd ℂ H (ball a R)) (hH0 : ∀ z ∈ ball a R, H z ≠ 0)
    (hfactN : ∀ z ∈ ball a R, F N z = (z - a) ^ m * H z) :
    exp (2 * (Real.pi : ℂ) * I *
        (((Real.circleAverage (fun z => Real.log ‖F N z‖) a r₂ -
            Real.circleAverage (fun z => Real.log ‖F N z‖) a r₁) /
          (Real.log r₂ - Real.log r₁) : ℝ) : ℂ) / n) = 1 ∧
      ∀ i, i < N → ∀ z ∈ chartR a R ∪ chartL a R,
        ‖Complex.log (F (i + 1) z / F i z)‖ ≤
          (1 - r)⁻¹ * ‖(F (i + 1) z - F i z) / F i z‖ := by
  have hR : 0 < R := lt_trans hr₁ (lt_trans hr₁₂ hr₂R)
  have hfarDeck :=
    xi_deckClass_eq_one_of_far_field_relative_base_deformation hR hn hN hr hfar hFan hG₁ hG₂
      hK₁ hK₂ hpG₁ hpG₂ hF0R hF0L hpK₁ hpK₂ hrel
  have hmod :=
    deckClass_eq_exp_circleAverage_slope (f := F N) (h := H) (G₁ := K₁) (G₂ := K₂)
      (a := a) (R := R) (r₁ := r₁) (r₂ := r₂) (m := m) (n := n)
      hr₁ hr₁₂ hr₂R hn hH hH0 hfactN hK₁ hK₂ hpK₁ hpK₂
  constructor
  · rw [← hmod]
    exact hfarDeck.1
  · exact hfarDeck.2

end RHTower

namespace RHTower

open Complex Metric Finset

/-- **Clean modulus is the u-plane coherent tower surface.**  The coherent dyadic
Kummer tower for `xiDescent` on the slit plane is equivalent to all-level clean
two-circle modulus certificates around right-half ξ zeros. -/
theorem xiDescent_coherentTower_slitPlane_iff_all_clean_circleAverage_slope_exp_eq_one :
    Nonempty (CoherentTower xiDescent slitPlane) ↔
      ∀ k : ℕ, ∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∃ R₀ > 0, ∀ {r R : ℝ}, 0 < r → r < R → R ≤ R₀ →
          ∃ r₁ r₂ : ℝ, r < r₁ ∧ r₁ < r₂ ∧ r₂ < R ∧
            (∀ z : ℂ, ‖z - ρ‖ = r₁ → xi z ≠ 0) ∧
            (∀ z : ℂ, ‖z - ρ‖ = r₂ → xi z ≠ 0) ∧
            exp (2 * (Real.pi : ℂ) * I *
                (((Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₂ -
                    Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₁) /
                  (Real.log r₂ - Real.log r₁) : ℝ) : ℂ) / (2 ^ k : ℕ)) = 1 := by
  have hclean : RiemannHypothesis ↔
      ∀ k : ℕ, ∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∃ R₀ > 0, ∀ {r R : ℝ}, 0 < r → r < R → R ≤ R₀ →
          ∃ r₁ r₂ : ℝ, r < r₁ ∧ r₁ < r₂ ∧ r₂ < R ∧
            (∀ z : ℂ, ‖z - ρ‖ = r₁ → xi z ≠ 0) ∧
            (∀ z : ℂ, ‖z - ρ‖ = r₂ → xi z ≠ 0) ∧
            exp (2 * (Real.pi : ℂ) * I *
                (((Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₂ -
                    Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₁) /
                  (Real.log r₂ - Real.log r₁) : ℝ) : ℂ) / (2 ^ k : ℕ)) = 1 := by
    rw [rh_iff_forall_ladder]
    exact forall_congr' fun k => rhLadder_iff_clean_circleAverage_slope_exp_eq_one k
  exact (rh_iff_xiDescent_coherentTower_slitPlane).symm.trans hclean

/-- **Finite window relations are the u-plane coherent tower surface.**  The coherent
dyadic Kummer tower for `xiDescent` on the slit plane is equivalent to the complete
all-level finite reflection-window congruence surface. -/
theorem xiDescent_coherentTower_slitPlane_iff_all_finite_window_relations_all_levels :
    Nonempty (CoherentTower xiDescent slitPlane) ↔
      ∀ k : ℕ, ∀ (t : Finset ℂ) (m : ℂ → ℕ),
        (∀ z ∈ t, xi z = 0) →
        (∀ z ∈ t, (m z : ℕ∞) = analyticOrderAt xi z) →
        (∀ z ∈ t, lineReflect z ∈ t) →
        (∑ z ∈ t, m z ≡
          ∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z [MOD 2 ^ (k + 1)]) := by
  exact (rh_iff_xiDescent_coherentTower_slitPlane).symm.trans
    rh_iff_all_finite_window_relations_all_levels

end RHTower

namespace RHTower

open Complex Metric

/-- **Euler-side germ continuation is the u-plane coherent tower surface.**  The
all-level continuation of every far-half dyadic ξ root germ is equivalent to the
coherent dyadic Kummer tower for `xiDescent` on the slit plane. -/
theorem all_farHalf_germs_extend_all_levels_iff_xiDescent_coherentTower_slitPlane :
    (∀ k : ℕ, ∀ g₁ : ℂ → ℂ, AnalyticOnNhd ℂ g₁ farHalf →
      (∀ s ∈ farHalf, g₁ s ^ 2 ^ k = xi s) →
      ∃ g, AnalyticOnNhd ℂ g rightHalf ∧ (∀ s ∈ rightHalf, g s ^ 2 ^ k = xi s) ∧
        Set.EqOn g g₁ farHalf) ↔
      Nonempty (CoherentTower xiDescent slitPlane) := by
  exact (rh_iff_all_farHalf_germs_extend_all_levels).symm.trans
    rh_iff_xiDescent_coherentTower_slitPlane

end RHTower

namespace RHTower

open Complex Metric

/-- The two-circle modulus slope of `xiDescent` is the local vanishing order.
This is the u-plane version of `xi_circleAverage_slope_eq_order`, using the
Bottcher-backed descent and the seam-cocycle peel of the descended divisor. -/
theorem xiDescent_circleAverage_slope_eq_order (w₀ : ℂ) :
    ∃ R₀ > 0, ∀ {R r₁ r₂ : ℝ}, 0 < r₁ → r₁ < r₂ → r₂ < R → R ≤ R₀ →
      (Real.circleAverage (fun z => Real.log ‖xiDescent z‖) w₀ r₂ -
          Real.circleAverage (fun z => Real.log ‖xiDescent z‖) w₀ r₁) /
        (Real.log r₂ - Real.log r₁) = ((analyticOrderAt xiDescent w₀).toNat : ℝ) := by
  obtain ⟨R₀, hR₀, h, hhan, hh0, hfact⟩ := xiDescent_peel_ball w₀
  refine ⟨R₀, hR₀, ?_⟩
  intro R r₁ r₂ hr₁ hr₁₂ hr₂R hRle
  have hsub : ball w₀ R ⊆ ball w₀ R₀ := ball_subset_ball hRle
  rw [circleAverage_log_norm_single_zero (hr₁.trans hr₁₂) hr₂R
      (fun z hz => hhan z (hsub hz)) (fun z hz => hh0 z (hsub hz))
      (fun z hz => hfact z (hsub hz)),
    circleAverage_log_norm_single_zero hr₁ (hr₁₂.trans hr₂R)
      (fun z hz => hhan z (hsub hz)) (fun z hz => hh0 z (hsub hz))
      (fun z hz => hfact z (hsub hz))]
  have hlog : Real.log r₁ < Real.log r₂ := Real.log_lt_log hr₁ hr₁₂
  rw [div_eq_iff (sub_ne_zero.mpr hlog.ne')]
  ring

/-- Local `xiDescent` modulus criterion for a dyadic rung.  The root-of-unity value
of the two-circle slope of `log ‖xiDescent‖` is trivial exactly when the descended
zero order is divisible by `2^k`. -/
theorem xiDescent_circleAverage_slope_exp_eq_one_iff_order_dvd (w₀ : ℂ) (k : ℕ) :
    ∃ R₀ > 0, ∀ {R r₁ r₂ : ℝ}, 0 < r₁ → r₁ < r₂ → r₂ < R → R ≤ R₀ →
      (exp (2 * (Real.pi : ℂ) * I *
          (((Real.circleAverage (fun z => Real.log ‖xiDescent z‖) w₀ r₂ -
              Real.circleAverage (fun z => Real.log ‖xiDescent z‖) w₀ r₁) /
            (Real.log r₂ - Real.log r₁) : ℝ) : ℂ) / (2 ^ k : ℕ)) = 1 ↔
        ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt xiDescent w₀) := by
  obtain ⟨R₀, hR₀, hslope⟩ := xiDescent_circleAverage_slope_eq_order w₀
  refine ⟨R₀, hR₀, ?_⟩
  intro R r₁ r₂ hr₁ hr₁₂ hr₂R hRle
  rw [hslope hr₁ hr₁₂ hr₂R hRle]
  have h2k : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hcast : ((((analyticOrderAt xiDescent w₀).toNat : ℝ) : ℂ) =
      (((analyticOrderAt xiDescent w₀).toNat : ℕ) : ℂ)) := by norm_cast
  rw [hcast, exp_two_pi_mul_div_eq_one_iff h2k]
  set m : ℕ := (analyticOrderAt xiDescent w₀).toNat with hm_def
  have hm : (m : ℕ∞) = analyticOrderAt xiDescent w₀ :=
    ENat.coe_toNat (xiDescent_orderAt_ne_top w₀)
  constructor
  · rintro ⟨c, hc⟩
    rw [← hm, hc]
    exact ⟨(c : ℕ∞), by push_cast; ring⟩
  · intro hdvd
    rw [← hm] at hdvd
    exact natCast_dvd_natCast_of_enat (pow_ne_zero k two_ne_zero) hdvd

/-- **The u-plane coherent tower is exactly the all-level `xiDescent` modulus surface.**
On the slit plane, the coherent dyadic Kummer tower exists iff every descended zero
has trivial two-circle modulus-slope root-of-unity at every finite dyadic level. -/
theorem xiDescent_coherentTower_slitPlane_iff_all_circleAverage_slope_exp_eq_one :
    Nonempty (CoherentTower xiDescent slitPlane) ↔
      ∀ k : ℕ, ∀ w ∈ slitPlane, xiDescent w = 0 →
        ∃ R₀ > 0, ∀ {R r₁ r₂ : ℝ}, 0 < r₁ → r₁ < r₂ → r₂ < R → R ≤ R₀ →
          exp (2 * (Real.pi : ℂ) * I *
              (((Real.circleAverage (fun z => Real.log ‖xiDescent z‖) w r₂ -
                  Real.circleAverage (fun z => Real.log ‖xiDescent z‖) w r₁) /
                (Real.log r₂ - Real.log r₁) : ℝ) : ℂ) / (2 ^ k : ℕ)) = 1 := by
  rw [xiDescent_coherentTower_slitPlane_iff_all_order_dvd]
  constructor
  · intro hdiv k w hw hwzero
    obtain ⟨R₀, hR₀, hiff⟩ := xiDescent_circleAverage_slope_exp_eq_one_iff_order_dvd w k
    exact ⟨R₀, hR₀, fun {R r₁ r₂} hr₁ hr₁₂ hr₂R hRle =>
      (hiff hr₁ hr₁₂ hr₂R hRle).mpr (hdiv k w hw hwzero)⟩
  · intro hmod k w hw hwzero
    obtain ⟨R₁, hR₁, hiff⟩ := xiDescent_circleAverage_slope_exp_eq_one_iff_order_dvd w k
    obtain ⟨R₂, hR₂, hexp⟩ := hmod k w hw hwzero
    set Rm : ℝ := min R₁ R₂ with hRm_def
    have hRm_pos : 0 < Rm := by
      rw [hRm_def]
      exact lt_min hR₁ hR₂
    have hr₁ : 0 < Rm / 4 := by linarith
    have hr₁₂ : Rm / 4 < Rm / 2 := by linarith
    have hr₂R : Rm / 2 < Rm := by linarith
    have hRle₁ : Rm ≤ R₁ := by
      rw [hRm_def]
      exact min_le_left _ _
    have hRle₂ : Rm ≤ R₂ := by
      rw [hRm_def]
      exact min_le_right _ _
    have hcrit := hiff (R := Rm) (r₁ := Rm / 4) (r₂ := Rm / 2) hr₁ hr₁₂ hr₂R hRle₁
    have hval := hexp (R := Rm) (r₁ := Rm / 4) (r₂ := Rm / 2) hr₁ hr₁₂ hr₂R hRle₂
    exact hcrit.mp hval

end RHTower

namespace RHTower

open Complex Metric

/-- **The descended seam ledger is modulus-readable.**  The seam jump of bank roots of
`xiDescent` can be written using only the two-circle slope of `log ‖xiDescent‖`, so the
u-plane seam charge is a boundary-modulus constraint rather than an internal order count. -/
theorem xiDescent_seam_jump_eq_circleAverage_slope (x₀ : ℂ) :
    ∃ R₀ > 0, ∀ {R r₁ r₂ : ℝ}, 0 < r₁ → r₁ < r₂ → r₂ < R → R ≤ R₀ →
      ∀ {n : ℕ}, 0 < n →
      ∀ {GU GD G₁ G₂ : ℂ → ℂ},
      AnalyticOnNhd ℂ G₁ (chartR x₀ R) → AnalyticOnNhd ℂ G₂ (chartL x₀ R) →
      (∀ z ∈ chartR x₀ R, G₁ z ^ n = xiDescent z) →
      (∀ z ∈ chartL x₀ R, G₂ z ^ n = xiDescent z) →
      ∀ {qP qM : ℂ}, qP ∈ overlapU x₀ R → qM ∈ overlapD x₀ R →
      GU qP ^ n = xiDescent qP → GD qM ^ n = xiDescent qM →
      (GU qP / G₂ qP) / (GD qM / G₂ qM) =
        exp (2 * (Real.pi : ℂ) * I *
            (((Real.circleAverage (fun z => Real.log ‖xiDescent z‖) x₀ r₂ -
                Real.circleAverage (fun z => Real.log ‖xiDescent z‖) x₀ r₁) /
              (Real.log r₂ - Real.log r₁) : ℝ) : ℂ) / n) *
          ((GU qP / G₁ qP) / (GD qM / G₁ qM)) := by
  obtain ⟨Rs, hRs, hseam⟩ := xiDescent_seam_jump x₀
  obtain ⟨Rm, hRm, hslope⟩ := xiDescent_circleAverage_slope_eq_order x₀
  refine ⟨min Rs Rm, lt_min hRs hRm, ?_⟩
  intro R r₁ r₂ hr₁ hr₁₂ hr₂R hRle n hn GU GD G₁ G₂ hG₁ hG₂ hpG₁ hpG₂ qP qM hqP hqM hpGU hpGD
  have hRpos : 0 < R := lt_trans hr₁ (lt_trans hr₁₂ hr₂R)
  have hRleS : R ≤ Rs := le_trans hRle (min_le_left _ _)
  have hRleM : R ≤ Rm := le_trans hRle (min_le_right _ _)
  have hjump := hseam hRpos hRleS hn hG₁ hG₂ hpG₁ hpG₂ hqP hqM hpGU hpGD
  have hs := hslope hr₁ hr₁₂ hr₂R hRleM
  rw [hjump, hs]
  norm_cast

end RHTower

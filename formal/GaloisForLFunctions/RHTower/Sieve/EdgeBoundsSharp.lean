import GaloisForLFunctions.RHTower.Sieve.VerticalMassSharp
import GaloisForLFunctions.RHTower.Sieve.TruncationError

/-!
# The other two edges, with constants taken where they are used

The audit that repaired the left edge applies to the horizontal edges and to the truncation error as
well: each is controlled by a decay constant for the cutoff's transform, and that constant grows
like `(N+H)^{σmax}`, so `σmax` must be the abscissa actually met on that edge, not a fixed number
above it.

For these two the relevant abscissa is the right one, `d`, since both edges reach it.  The
statements below take the decay constant as a hypothesis, so the caller fixes `σmax = d` and the
constant moves with `d` — which it must, because `d` depends on the contour parameter.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Set Filter Topology GaloisForLFunctions.HTGeometry

/-- **A horizontal edge, with the decay constant supplied.** -/
theorem norm_horizontal_edge_le {N H : ℝ} (j : ℕ) {c d T M C : ℝ}
    (hc : 0 < c) (hcd : c ≤ d) (hT : T ≠ 0) (hM : 0 ≤ M)
    (hbd : ∀ s : ℂ, 0 < s.re → s.re ≤ d →
      |s.im| ^ (j + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C)
    {F : ℂ → ℂ}
    (hF : ∀ x ∈ Set.Ioc c d, ‖F ((x : ℂ) + (T : ℝ) * Complex.I)‖ ≤ M) :
    ‖∫ x : ℝ in c..d, F ((x : ℂ) + (T : ℝ) * Complex.I)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((x : ℂ) + (T : ℝ) * Complex.I)‖
      ≤ M * C / |T| ^ (j + 1) * (d - c) := by
  have hTabs : (0 : ℝ) < |T| := abs_pos.2 hT
  have hkey : ∀ x ∈ Set.uIoc c d,
      ‖F ((x : ℂ) + (T : ℝ) * Complex.I)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((x : ℂ) + (T : ℝ) * Complex.I)‖ ≤ M * C / |T| ^ (j + 1) := by
    intro x hx
    rw [Set.uIoc_of_le hcd] at hx
    have hre : ((x : ℂ) + (T : ℝ) * Complex.I).re = x := by simp
    have him : ((x : ℂ) + (T : ℝ) * Complex.I).im = T := by simp
    have hW : ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
        ((x : ℂ) + (T : ℝ) * Complex.I)‖ ≤ C / |T| ^ (j + 1) := by
      have h := norm_mellin_smoothWeight_le_div j hbd
        (s := (x : ℂ) + (T : ℝ) * Complex.I) (by rw [hre]; linarith [hx.1])
        (by rw [hre]; exact hx.2) (by rw [him]; exact hTabs)
      rwa [him] at h
    rw [norm_mul]
    calc ‖F ((x : ℂ) + (T : ℝ) * Complex.I)‖ *
          ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((x : ℂ) + (T : ℝ) * Complex.I)‖
        ≤ M * (C / |T| ^ (j + 1)) := mul_le_mul (hF x hx) hW (norm_nonneg _) hM
      _ = M * C / |T| ^ (j + 1) := by ring
  have hres := intervalIntegral.norm_integral_le_of_norm_le_const hkey
  rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ d - c)] at hres

/-- **The truncation error, with the decay constant supplied.** -/
theorem norm_truncation_error_le {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {d T M C : ℝ}
    (hd : 0 < d) (hT : 1 ≤ T) (hM : 0 ≤ M)
    (hbd : ∀ s : ℂ, 0 < s.re → s.re ≤ d →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C)
    {F : ℂ → ℂ}
    (hFcont : Continuous (fun y : ℝ => F ((d : ℂ) + (y : ℝ) * Complex.I)))
    (hF : ∀ y : ℝ, ‖F ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ M) :
    ‖(∫ y : ℝ, F ((d : ℂ) + (y : ℝ) * Complex.I)
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I))
        - ∫ y : ℝ in (-T)..T, F ((d : ℂ) + (y : ℝ) * Complex.I)
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((d : ℂ) + (y : ℝ) * Complex.I)‖
      ≤ 2 * (M * C) / T := by
  have hT0 : (0 : ℝ) < T := by linarith
  set g : ℝ → ℂ := fun y => F ((d : ℂ) + (y : ℝ) * Complex.I)
    * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I)
    with hgdef
  have hWcont : Continuous fun y : ℝ =>
      mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I) :=
    continuous_mellin_smoothWeight_line hH hd
  have hgcont : Continuous g := hFcont.mul hWcont
  have hgint : Integrable g := by
    refine Integrable.mono' ((verticalIntegrable_mellin_smoothWeight hN hH hd).norm.const_mul M)
      hgcont.aestronglyMeasurable ?_
    filter_upwards with y
    rw [hgdef, norm_mul]
    exact mul_le_mul_of_nonneg_right (hF y) (norm_nonneg _)
  have hgii : ∀ a b : ℝ, IntervalIntegrable g volume a b :=
    fun a b => hgcont.intervalIntegrable a b
  have hkey : ∀ R : ℝ, T ≤ R →
      ‖(∫ y : ℝ in (-R)..R, g y) - ∫ y : ℝ in (-T)..T, g y‖ ≤ 2 * (M * C) / T := by
    intro R hTR
    have hsplit : (∫ y : ℝ in (-R)..(-T), g y) + ((∫ y : ℝ in (-T)..T, g y)
        + (∫ y : ℝ in T..R, g y)) = ∫ y : ℝ in (-R)..R, g y := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hgii (-T) T) (hgii T R),
        intervalIntegral.integral_add_adjacent_intervals (hgii (-R) (-T)) (hgii (-T) R)]
    have heq : (∫ y : ℝ in (-R)..R, g y) - ∫ y : ℝ in (-T)..T, g y
        = (∫ y : ℝ in (-R)..(-T), g y) + ∫ y : ℝ in T..R, g y := by
      rw [← hsplit]; ring
    have hbound : ∀ a b : ℝ, a ≤ b →
        (∫ y : ℝ in a..b, ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I)‖) ≤ C / T →
        ‖∫ y : ℝ in a..b, g y‖ ≤ M * C / T := by
      intro a b hab hmass
      refine le_trans (intervalIntegral.norm_integral_le_integral_norm hab) ?_
      have hstep : (∫ y : ℝ in a..b, ‖g y‖)
          ≤ ∫ y : ℝ in a..b, M * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((d : ℂ) + (y : ℝ) * Complex.I)‖ := by
        refine intervalIntegral.integral_mono_on hab
          (hgcont.norm.intervalIntegrable _ _)
          ((hWcont.norm.intervalIntegrable _ _).const_mul M) (fun y _ => ?_)
        rw [hgdef, norm_mul]
        exact mul_le_mul_of_nonneg_right (hF y) (norm_nonneg _)
      refine le_trans hstep ?_
      rw [intervalIntegral.integral_const_mul, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hmass hM
    have h1 := hbound (-R) (-T) (by linarith)
      (integral_tail_norm_mellin_le' hd le_rfl hT hTR hbd hH)
    have h2 := hbound T R hTR (integral_tail_norm_mellin_le hd le_rfl hT hTR hbd hH)
    rw [heq]
    refine le_trans (norm_add_le _ _) ?_
    have : M * C / T + M * C / T = 2 * (M * C) / T := by ring
    linarith
  have htend : Tendsto (fun R : ℝ => (∫ y : ℝ in (-R)..R, g y) - ∫ y : ℝ in (-T)..T, g y)
      atTop (𝓝 ((∫ y : ℝ, g y) - ∫ y : ℝ in (-T)..T, g y)) :=
    (MeasureTheory.intervalIntegral_tendsto_integral hgint
      (tendsto_neg_atTop_atBot) tendsto_id).sub tendsto_const_nhds
  refine le_of_tendsto htend.norm ?_
  filter_upwards [eventually_ge_atTop T] with R hR using hkey R hR

end RHTower.Sieve

import GaloisForLFunctions.RHTower.Sieve.VerticalEdgeBound

/-!
# Truncating the Perron line

The smoothed Perron formula is an exact identity on the *whole* line `Re s = d`, with no truncation
error of its own.  Truncation enters only because the contour cannot be shifted across a full strip
for `1/ζ`, so the identity must first be cut at height `T`.

The cost of that cut is governed by the cutoff alone.  Beyond height `1` its transform decays like
`y^{-2}`, whose tails converge, so cutting at `T` costs `2MC/T` when the other factor is bounded by
`M` on the line — with no hypothesis on that factor beyond the bound and continuity.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Set Filter Topology GaloisForLFunctions.HTGeometry

/-- The tail of the vertical mass beyond height `T`, on a half-line of length `R - T`. -/
theorem integral_tail_norm_mellin_le {N H σmax C c T R : ℝ} (hc : 0 < c) (hcmax : c ≤ σmax)
    (hT : 1 ≤ T) (hTR : T ≤ R)
    (hbd : ∀ s : ℂ, 0 < s.re → s.re ≤ σmax →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C)
    (hH : 0 < H) :
    (∫ y : ℝ in T..R, ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
        ((c : ℂ) + (y : ℝ) * Complex.I)‖) ≤ C / T := by
  have hC : 0 ≤ C := by
    have h := hbd ((c : ℂ) + (1 : ℝ) * Complex.I) (by simp; exact hc) (by simp; exact hcmax)
    refine le_trans ?_ h
    positivity
  have h0 : (0 : ℝ) ∉ Set.uIcc T R := by
    rw [Set.uIcc_of_le hTR]
    intro hmem
    linarith [hmem.1]
  have hcont : Continuous fun y : ℝ => ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
      ((c : ℂ) + (y : ℝ) * Complex.I)‖ := (continuous_mellin_smoothWeight_line hH hc).norm
  have hzi : IntervalIntegrable (fun y : ℝ => C * y ^ (-2 : ℤ)) volume T R :=
    (intervalIntegral.intervalIntegrable_zpow (Or.inr h0)).const_mul C
  have h := intervalIntegral.integral_mono_on (μ := volume) hTR
    (hcont.intervalIntegrable _ _) hzi
    (fun x hx => norm_mellin_smoothWeight_line_tail hc hcmax
      (by rw [abs_of_pos (by linarith [hx.1] : (0 : ℝ) < x)]; linarith [hx.1]) hbd)
  rw [intervalIntegral.integral_const_mul, integral_zpow (Or.inr ⟨by norm_num, h0⟩)] at h
  refine le_trans h ?_
  have hT0 : (0 : ℝ) < T := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hval : (R ^ ((-2 : ℤ) + 1) - T ^ ((-2 : ℤ) + 1)) / (((-2 : ℤ) : ℝ) + 1) = T⁻¹ - R⁻¹ := by
    rw [show (-2 : ℤ) + 1 = -1 from rfl, zpow_neg, zpow_neg, zpow_one, zpow_one]
    push_cast
    ring
  rw [hval, div_eq_mul_inv]
  have : (0 : ℝ) < R⁻¹ := by positivity
  nlinarith [hC]

/-- The same for the tail below `-T`. -/
theorem integral_tail_norm_mellin_le' {N H σmax C c T R : ℝ} (hc : 0 < c) (hcmax : c ≤ σmax)
    (hT : 1 ≤ T) (hTR : T ≤ R)
    (hbd : ∀ s : ℂ, 0 < s.re → s.re ≤ σmax →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C)
    (hH : 0 < H) :
    (∫ y : ℝ in (-R)..(-T), ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
        ((c : ℂ) + (y : ℝ) * Complex.I)‖) ≤ C / T := by
  have hC : 0 ≤ C := by
    have h := hbd ((c : ℂ) + (1 : ℝ) * Complex.I) (by simp; exact hc) (by simp; exact hcmax)
    refine le_trans ?_ h
    positivity
  have h0 : (0 : ℝ) ∉ Set.uIcc (-R) (-T) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro hmem
    linarith [hmem.2]
  have hcont : Continuous fun y : ℝ => ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
      ((c : ℂ) + (y : ℝ) * Complex.I)‖ := (continuous_mellin_smoothWeight_line hH hc).norm
  have hzi : IntervalIntegrable (fun y : ℝ => C * y ^ (-2 : ℤ)) volume (-R) (-T) :=
    (intervalIntegral.intervalIntegrable_zpow (Or.inr h0)).const_mul C
  have h := intervalIntegral.integral_mono_on (μ := volume) (by linarith)
    (hcont.intervalIntegrable _ _) hzi
    (fun x hx => norm_mellin_smoothWeight_line_tail hc hcmax
      (by
        rw [abs_of_neg (by linarith [hx.2] : x < 0)]
        linarith [hx.2]) hbd)
  rw [intervalIntegral.integral_const_mul, integral_zpow (Or.inr ⟨by norm_num, h0⟩)] at h
  refine le_trans h ?_
  have hT0 : (0 : ℝ) < T := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hval : (((-T : ℝ)) ^ ((-2 : ℤ) + 1) - (-R) ^ ((-2 : ℤ) + 1)) / (((-2 : ℤ) : ℝ) + 1)
      = T⁻¹ - R⁻¹ := by
    rw [show (-2 : ℤ) + 1 = -1 from rfl, zpow_neg, zpow_neg, zpow_one, zpow_one, inv_neg, inv_neg]
    push_cast
    ring
  rw [hval, div_eq_mul_inv]
  have : (0 : ℝ) < R⁻¹ := by positivity
  nlinarith [hC]

/-- **The cost of truncating the Perron line.**  Cutting the exact vertical integral at height `T`
costs at most `2MC/T`, where `M` bounds the other factor on the line and `C` depends only on the
cutoff and the abscissa range. -/
theorem exists_bound_truncation_error {N H : ℝ} (hN : 0 < N) (hH : 0 < H) (σmax : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : ℂ → ℂ) (c T M : ℝ), 0 < c → c ≤ σmax → 1 ≤ T → 0 ≤ M →
      Continuous (fun y : ℝ => F ((c : ℂ) + (y : ℝ) * Complex.I)) →
      (∀ y : ℝ, ‖F ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤ M) →
      ‖(∫ y : ℝ, F ((c : ℂ) + (y : ℝ) * Complex.I)
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((c : ℂ) + (y : ℝ) * Complex.I))
          - ∫ y : ℝ in (-T)..T, F ((c : ℂ) + (y : ℝ) * Complex.I)
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((c : ℂ) + (y : ℝ) * Complex.I)‖
        ≤ 2 * (M * C) / T := by
  obtain ⟨C, hC, hbd⟩ := exists_bound_mellin_smoothWeight_im_pow hN hH 1 σmax
  refine ⟨C, hC, fun F c T M hc hcmax hT hM hFcont hF => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  set g : ℝ → ℂ := fun y => F ((c : ℂ) + (y : ℝ) * Complex.I)
    * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((c : ℂ) + (y : ℝ) * Complex.I)
    with hgdef
  have hWcont : Continuous fun y : ℝ =>
      mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((c : ℂ) + (y : ℝ) * Complex.I) :=
    continuous_mellin_smoothWeight_line hH hc
  have hgcont : Continuous g := hFcont.mul hWcont
  have hgint : Integrable g := by
    refine Integrable.mono' ((verticalIntegrable_mellin_smoothWeight hN hH hc).norm.const_mul M)
      hgcont.aestronglyMeasurable ?_
    filter_upwards with y
    rw [hgdef, norm_mul]
    exact mul_le_mul_of_nonneg_right (hF y) (norm_nonneg _)
  have hgii : ∀ a b : ℝ, IntervalIntegrable g volume a b :=
    fun a b => hgcont.intervalIntegrable a b
  -- the truncated tails, uniformly in the outer height
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
            ((c : ℂ) + (y : ℝ) * Complex.I)‖) ≤ C / T →
        ‖∫ y : ℝ in a..b, g y‖ ≤ M * C / T := by
      intro a b hab hmass
      refine le_trans (intervalIntegral.norm_integral_le_integral_norm hab) ?_
      have hstep : (∫ y : ℝ in a..b, ‖g y‖)
          ≤ ∫ y : ℝ in a..b, M * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((c : ℂ) + (y : ℝ) * Complex.I)‖ := by
        refine intervalIntegral.integral_mono_on hab
          (hgcont.norm.intervalIntegrable _ _)
          ((hWcont.norm.intervalIntegrable _ _).const_mul M) (fun y _ => ?_)
        rw [hgdef, norm_mul]
        exact mul_le_mul_of_nonneg_right (hF y) (norm_nonneg _)
      refine le_trans hstep ?_
      rw [intervalIntegral.integral_const_mul, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hmass hM
    have h1 := hbound (-R) (-T) (by linarith)
      (integral_tail_norm_mellin_le' hc hcmax hT hTR hbd hH)
    have h2 := hbound T R hTR (integral_tail_norm_mellin_le hc hcmax hT hTR hbd hH)
    rw [heq]
    refine le_trans (norm_add_le _ _) ?_
    have : M * C / T + M * C / T = 2 * (M * C) / T := by ring
    linarith
  -- pass to the limit in the outer height
  have htend : Tendsto (fun R : ℝ => (∫ y : ℝ in (-R)..R, g y) - ∫ y : ℝ in (-T)..T, g y)
      atTop (𝓝 ((∫ y : ℝ, g y) - ∫ y : ℝ in (-T)..T, g y)) :=
    (MeasureTheory.intervalIntegral_tendsto_integral hgint
      (tendsto_neg_atTop_atBot) tendsto_id).sub tendsto_const_nhds
  refine le_of_tendsto htend.norm ?_
  filter_upwards [eventually_ge_atTop T] with R hR using hkey R hR

end RHTower.Sieve

/-
# Green pinch at the critical scale (mixed-pair wiring, step A)

For `‖c‖ ≥ 100`, the dynamical Green function is pinched near the critical level on the two
balls that matter to the mixed-pair tower: `closedBall 0 2` (which contains every connected
filled Julia set) sits at level `G_c(0) ± 1/8`, and `closedBall c 4` (its image under `f_c`,
the shadow patch of the scaffold slit) at `2·G_c(0) ± 1/4`.  One `f_c`-iterate throws either
ball into the deep far field at norm `≈ ‖c‖²`, where the crude asymptotic
`|G − log‖·‖| ≤ 2‖c‖/‖·‖²` is effective; the functional equation `G(f_c z) = 2·G(z)` halves
back.  Numerically pre-certified (measured pinches ≈ 0.02–0.04 against 1/8, 1/4).
Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.GreenPullback

open Complex Set

namespace Bottcher

/-- **Core pinch.**  Every point within `4` of `c` has Green value `log‖c‖ ± 1/8`: its
`f_c`-image has norm within a factor `[91/100, 11/10]` of `‖c‖²`, deep in the far field. -/
theorem abs_greenFunctionDyn_sub_log_le_of_near {c w : ℂ} (hc : (100:ℝ) ≤ ‖c‖)
    (hw : ‖w - c‖ ≤ 4) :
    |greenFunctionDyn c w - Real.log ‖c‖| ≤ 1/8 := by
  set R : ℝ := ‖c‖ with hRdef
  have hR0 : (0:ℝ) < R := by linarith
  -- norm window for `w`
  have hwhi : ‖w‖ ≤ R + 4 := by
    have h1 : ‖(w - c) + c‖ ≤ ‖w - c‖ + ‖c‖ := norm_add_le _ _
    rw [sub_add_cancel] at h1
    linarith
  have hwlo : R - 4 ≤ ‖w‖ := by
    have h1 : ‖(c - w) + w‖ ≤ ‖c - w‖ + ‖w‖ := norm_add_le _ _
    rw [sub_add_cancel, norm_sub_rev] at h1
    linarith
  -- norm window for the image `f_c w = w² + c`
  set fw : ℂ := quadratic c w with hfwdef
  have hfweq : fw = w ^ 2 + c := rfl
  have hsqhi : ‖w‖ ^ 2 ≤ (R + 4) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg w) hwhi 2
  have hsqlo : (R - 4) ^ 2 ≤ ‖w‖ ^ 2 :=
    pow_le_pow_left₀ (by linarith) hwlo 2
  have hfwhi : ‖fw‖ ≤ (11/10) * R ^ 2 := by
    have h1 : ‖w ^ 2 + c‖ ≤ ‖w ^ 2‖ + ‖c‖ := norm_add_le _ _
    rw [norm_pow] at h1
    rw [hfweq]
    nlinarith
  have hfwlo : (91/100) * R ^ 2 ≤ ‖fw‖ := by
    have h1 : ‖(w ^ 2 + c) + (-c)‖ ≤ ‖w ^ 2 + c‖ + ‖-c‖ := norm_add_le _ _
    rw [add_neg_cancel_right, norm_neg, norm_pow] at h1
    rw [hfweq]
    nlinarith
  have hfwc : ‖c‖ ≤ ‖fw‖ := by
    rw [← hRdef]
    nlinarith
  have hfw2 : (2:ℝ) < ‖fw‖ := by nlinarith
  have hfwK : fw ∉ filledJulia c := not_mem_filledJulia hfwc hfw2
  -- crude asymptotic at the image, with the effective error `≤ 1/40`
  have hcrude : |greenLimit c fw - Real.log ‖fw‖| ≤ 2 * ‖c‖ / ‖fw‖ ^ 2 :=
    greenLimit_abs_sub_log hfwc hfw2
  have herr : 2 * ‖c‖ / ‖fw‖ ^ 2 ≤ 1/40 := by
    rw [div_le_iff₀ (by positivity)]
    have hsq : ((91/100) * R ^ 2) ^ 2 ≤ ‖fw‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hfwlo 2
    rw [← hRdef]
    nlinarith [sq_nonneg R, sq_nonneg (R - 100), pow_pos hR0 4]
  have hcrude' := abs_le.mp (le_trans hcrude herr)
  -- log window for the image norm
  have hlogfw_hi : Real.log ‖fw‖ ≤ 2 * Real.log R + 1/10 := by
    have h1 : Real.log ‖fw‖ ≤ Real.log ((11/10) * R ^ 2) :=
      Real.log_le_log (by nlinarith) hfwhi
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Nat.cast_ofNat] at h1
    have h2 : Real.log (11/10) ≤ 1/10 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 11/10 by norm_num)
      linarith
    linarith
  have hlogfw_lo : 2 * Real.log R - 1/10 ≤ Real.log ‖fw‖ := by
    have h1 : Real.log ((91/100) * R ^ 2) ≤ Real.log ‖fw‖ :=
      Real.log_le_log (by positivity) hfwlo
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Nat.cast_ofNat] at h1
    have h2 : -(1/10) ≤ Real.log (91/100) := by
      have h3 : Real.log (100/91) ≤ 100/91 - 1 :=
        Real.log_le_sub_one_of_pos (by norm_num)
      have h4 : Real.log (91/100) = -Real.log (100/91) := by
        rw [show (91/100:ℝ) = (100/91)⁻¹ by norm_num, Real.log_inv]
      rw [h4]
      have : (100:ℝ)/91 - 1 ≤ 1/10 := by norm_num
      linarith
    linarith
  -- halve back through the functional equation
  have hGfw : greenFunctionDyn c fw = greenLimit c fw := by
    unfold greenFunctionDyn
    rw [if_neg hfwK]
  have hdouble : greenFunctionDyn c fw = 2 * greenFunctionDyn c w :=
    greenFunctionDyn_quadratic c w
  have hkey : 2 * greenFunctionDyn c w = greenLimit c fw := by
    rw [← hdouble, hGfw]
  rw [abs_le]
  constructor <;> nlinarith [hcrude'.1, hcrude'.2]

/-- **Critical-value pinch**: `2·G_c(0) = G_c(c) = log‖c‖ ± 1/8`. -/
theorem abs_two_greenCritical_sub_log_le {c : ℂ} (hc : (100:ℝ) ≤ ‖c‖) :
    |2 * greenFunctionDyn c 0 - Real.log ‖c‖| ≤ 1/8 := by
  have h1 : ‖c - c‖ ≤ 4 := by simp
  have h2 := abs_greenFunctionDyn_sub_log_le_of_near hc h1
  have h3 : quadratic c 0 = c := by simp [quadratic]
  have h4 := greenFunctionDyn_quadratic c 0
  rw [h3] at h4
  rw [h4] at h2
  exact h2

/-- **`closedBall c 4` pinch**: on the critical-value ball, `G_c = 2·G_c(0) ± 1/4`. -/
theorem abs_greenFunctionDyn_sub_two_crit_le {c w : ℂ} (hc : (100:ℝ) ≤ ‖c‖)
    (hw : ‖w - c‖ ≤ 4) :
    |greenFunctionDyn c w - 2 * greenFunctionDyn c 0| ≤ 1/4 := by
  have h1 := abs_le.mp (abs_greenFunctionDyn_sub_log_le_of_near hc hw)
  have h2 := abs_le.mp (abs_two_greenCritical_sub_log_le hc)
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **`closedBall 0 2` pinch**: on the ball containing every connected filled Julia set,
`G_c = G_c(0) ± 1/8`. -/
theorem abs_greenFunctionDyn_sub_crit_le {c z : ℂ} (hc : (100:ℝ) ≤ ‖c‖)
    (hz : ‖z‖ ≤ 2) :
    |greenFunctionDyn c z - greenFunctionDyn c 0| ≤ 1/8 := by
  have hfz : ‖quadratic c z - c‖ ≤ 4 := by
    have h1 : quadratic c z - c = z ^ 2 := by simp [quadratic]
    rw [h1, norm_pow]
    nlinarith [norm_nonneg z]
  have h1 := abs_greenFunctionDyn_sub_two_crit_le hc hfz
  rw [greenFunctionDyn_quadratic c z] at h1
  have h2 := abs_le.mp h1
  rw [abs_le]
  constructor <;> linarith [h2.1, h2.2]

/-- **`M ⊆ closedBall 0 2`**: a connected parameter has norm at most `2` (its critical value
`c = f_c(0)` lies in `K_c`, which crude escape confines to `‖·‖ ≤ max 2 ‖c‖`). -/
theorem norm_le_two_of_mem_mandelbrot {c : ℂ} (hc : c ∈ mandelbrot) : ‖c‖ ≤ 2 := by
  by_contra hcon
  push Not at hcon
  have h1 : c ∈ filledJulia c := by
    have h0 : (0:ℂ) ∈ filledJulia c := hc
    have h2 := (quadratic_mem_filledJulia_iff c 0).mpr h0
    simpa [quadratic] using h2
  exact not_mem_filledJulia le_rfl hcon h1

/-- **Connected filled Julia sets live in `closedBall 0 2`** — the avoidance target of the
mixed-pair tower. -/
theorem filledJulia_subset_closedBall_two_of_mem_mandelbrot {c : ℂ} (hc : c ∈ mandelbrot) :
    filledJulia c ⊆ Metric.closedBall 0 2 := by
  intro z hz
  have h1 := filledJulia_subset_closedBall c hz
  rw [Metric.mem_closedBall, dist_zero_right] at h1 ⊢
  rwa [max_eq_left (norm_le_two_of_mem_mandelbrot hc)] at h1

end Bottcher

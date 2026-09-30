import GaloisForLFunctions.RHTower.ZetaTypicalScaleBounds
import GaloisForLFunctions.HTGeometry.LogDerivativeBound

/-!
# `ζ'/ζ` and `1/ζ` on a disc of radius `≍ R` at displacement `≍ R`

Fix a height `t ≥ 8` and a scale `0 < R ≤ 1/16`, and suppose

* no zero `ρ` with `Re ρ ≥ ½ + R/10` has `|Im ρ − t| ≤ 3R`;
* `|ζ| ≤ M` on `½ ≤ Re z ≤ ½ + 6R`, `|Im z − t| ≤ 6R`;
* `log|ζ(c)| ≥ −W` at the centre `c = ½ + 3R + it`.

Then the disc `|s − c| < 2.9R` is zero-free with `|ζ| ≤ M` and `|ζ(c)| ≥ e^{−W}`, and
Borel–Carathéodory with Cauchy's estimate (`HTGeometry.norm_logDeriv_le`,
`HTGeometry.norm_lower_bound_of_ball`) gives, for `|s − c| ≤ 2.3R`,

* `|ζ'/ζ(s)| ≤ 58 (log M + W + 1)/R`,
* `|ζ(s)| ≥ exp(−W − 8(log M + W + 1))`.
-/

noncomputable section

open Complex Set Metric

namespace RHTower

/-- The centre of the scale-`R` disc at height `t`. -/
def scaleCentre (R t : ℝ) : ℂ := (((1 / 2 + 3 * R : ℝ)) : ℂ) + (t : ℂ) * I

theorem scale_disc_geometry {R t : ℝ} {s : ℂ} (hs : s ∈ ball (scaleCentre R t) (29 / 10 * R)) :
    1 / 2 + R / 10 < s.re ∧ s.re < 1 / 2 + 6 * R ∧ |s.im - t| < 3 * R := by
  rw [mem_ball, dist_eq_norm] at hs
  have h1 := abs_lt.mp ((Complex.abs_re_le_norm _).trans_lt hs)
  have h2 := abs_lt.mp ((Complex.abs_im_le_norm _).trans_lt hs)
  simp only [scaleCentre, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.sub_im, Complex.add_im,
    Complex.mul_im] at h1 h2
  norm_num at h1 h2
  exact ⟨by linarith, by linarith, abs_lt.mpr ⟨by linarith, by linarith⟩⟩

/-- **Borel–Carathéodory hypotheses at scale `R`.** -/
theorem scale_disc_hypotheses {R t M W : ℝ} (hR : 0 < R) (hR16 : R ≤ 1 / 16) (ht : 8 ≤ t)
    (hZ : ∀ w : ℂ, riemannZeta w = 0 → 1 / 2 + R / 10 ≤ w.re → 3 * R < |w.im - t|)
    (hU : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 1 / 2 + 6 * R → |z.im - t| ≤ 6 * R →
      ‖riemannZeta z‖ ≤ M)
    (hL : -W ≤ Real.log ‖riemannZeta (scaleCentre R t)‖) :
    DifferentiableOn ℂ riemannZeta (ball (scaleCentre R t) (29 / 10 * R))
      ∧ (∀ s ∈ ball (scaleCentre R t) (29 / 10 * R), riemannZeta s ≠ 0)
      ∧ (∀ s ∈ ball (scaleCentre R t) (29 / 10 * R), ‖riemannZeta s‖ ≤ M)
      ∧ Real.exp (-W) ≤ ‖riemannZeta (scaleCentre R t)‖ := by
  refine ⟨?_, fun s hs => ?_, fun s hs => ?_, ?_⟩
  · intro s hs
    obtain ⟨-, -, him⟩ := scale_disc_geometry hs
    have hne : s ≠ 1 := by
      intro h; rw [h] at him; simp at him
      have := abs_lt.mp him; linarith
    exact (differentiableAt_riemannZeta hne).differentiableWithinAt
  · obtain ⟨h1, -, him⟩ := scale_disc_geometry hs
    intro h0
    have := hZ s h0 h1.le
    linarith
  · obtain ⟨h1, h2, him⟩ := scale_disc_geometry hs
    exact hU s (by linarith) h2.le (by linarith)
  · have hc0 : riemannZeta (scaleCentre R t) ≠ 0 := by
      intro h0
      have := hZ _ h0 (by simp [scaleCentre]; linarith)
      simp [scaleCentre] at this
      linarith
    have hpos : 0 < ‖riemannZeta (scaleCentre R t)‖ := norm_pos_iff.mpr hc0
    calc Real.exp (-W) ≤ Real.exp (Real.log ‖riemannZeta (scaleCentre R t)‖) :=
          Real.exp_le_exp.mpr hL
      _ = ‖riemannZeta (scaleCentre R t)‖ := Real.exp_log hpos

theorem log_ratio_scale {M W : ℝ} (hM : 0 < M) :
    Real.log (M / Real.exp (-W)) = Real.log M + W := by
  rw [Real.log_div hM.ne' (Real.exp_pos _).ne', Real.log_exp]; ring

/-- **`ζ'/ζ` at scale `R`.** -/
theorem norm_logDeriv_le_scale {R t M W : ℝ} (hR : 0 < R) (hR16 : R ≤ 1 / 16) (ht : 8 ≤ t)
    (hZ : ∀ w : ℂ, riemannZeta w = 0 → 1 / 2 + R / 10 ≤ w.re → 3 * R < |w.im - t|)
    (hU : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 1 / 2 + 6 * R → |z.im - t| ≤ 6 * R →
      ‖riemannZeta z‖ ≤ M)
    (hL : -W ≤ Real.log ‖riemannZeta (scaleCentre R t)‖) {s : ℂ}
    (hs : ‖s - scaleCentre R t‖ ≤ 23 / 10 * R) :
    ‖logDeriv riemannZeta s‖ ≤ 58 * (Real.log M + W + 1) / R := by
  obtain ⟨hd, hne, hMb, hm⟩ := scale_disc_hypotheses hR hR16 ht hZ hU hL
  have hMpos : 0 < M := lt_of_lt_of_le (Real.exp_pos _)
    (hm.trans (hMb _ (mem_ball_self (by positivity))))
  have hb := GaloisForLFunctions.HTGeometry.norm_logDeriv_le (ρ := 23 / 10 * R)
    (r := 26 / 10 * R) (by positivity) (by linarith) (by linarith) hd hne hMb (Real.exp_pos _) hm hs
  rw [logDeriv_apply]
  refine hb.trans ?_
  rw [log_ratio_scale hMpos]
  have hmc : Real.exp (-W) ≤ M := hm.trans (hMb _ (mem_ball_self (by positivity)))
  have h0 : 0 ≤ Real.log M + W + 1 := by
    have := Real.log_le_log (Real.exp_pos _) hmc
    rw [Real.log_exp] at this; linarith
  have e : 2 * (Real.log M + W + 1) * (26 / 10 * R) / (29 / 10 * R - 26 / 10 * R)
      / (26 / 10 * R - 23 / 10 * R) = 5200 / 90 * (Real.log M + W + 1) / R := by
    field_simp; ring
  rw [e]
  have : (5200 / 90 : ℝ) ≤ 58 := by norm_num
  have hR' : 0 < R := hR
  gcongr

/-- **`1/ζ` at scale `R`.** -/
theorem norm_ge_scale {R t M W : ℝ} (hR : 0 < R) (hR16 : R ≤ 1 / 16) (ht : 8 ≤ t)
    (hZ : ∀ w : ℂ, riemannZeta w = 0 → 1 / 2 + R / 10 ≤ w.re → 3 * R < |w.im - t|)
    (hU : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 1 / 2 + 6 * R → |z.im - t| ≤ 6 * R →
      ‖riemannZeta z‖ ≤ M)
    (hL : -W ≤ Real.log ‖riemannZeta (scaleCentre R t)‖) {s : ℂ}
    (hs : ‖s - scaleCentre R t‖ ≤ 23 / 10 * R) :
    Real.exp (-W - 8 * (Real.log M + W + 1)) ≤ ‖riemannZeta s‖ := by
  obtain ⟨hd, hne, hMb, hm⟩ := scale_disc_hypotheses hR hR16 ht hZ hU hL
  have hMpos : 0 < M := lt_of_lt_of_le (Real.exp_pos _)
    (hm.trans (hMb _ (mem_ball_self (by positivity))))
  have hb := GaloisForLFunctions.HTGeometry.norm_lower_bound_of_ball (r := 23 / 10 * R)
    (by positivity) (by linarith) hd hne hMb (Real.exp_pos _) hm hs
  refine le_trans ?_ hb
  rw [log_ratio_scale hMpos, ← Real.exp_add]
  have hmc : Real.exp (-W) ≤ M := hm.trans (hMb _ (mem_ball_self (by positivity)))
  have h0 : 0 ≤ Real.log M + W + 1 := by
    have := Real.log_le_log (Real.exp_pos _) hmc
    rw [Real.log_exp] at this; linarith
  apply Real.exp_le_exp.mpr
  have e : 2 * (Real.log M + W + 1) * (23 / 10 * R) / (29 / 10 * R - 23 / 10 * R)
      = 46 / 6 * (Real.log M + W + 1) := by field_simp; ring
  rw [e]
  nlinarith

end RHTower

end

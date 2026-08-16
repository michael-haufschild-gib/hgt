import GaloisForLFunctions.RHTower.XiMassShellRelativeRadius

/-!
# The shell amplitude ratio

Writing the propagation radius as `z = q u · w`, the window bound `‖z − q u‖ ≤ D_L` says exactly
that `w` is within `D_L/(q u)` of `1`.  Since `w ↦ w √w` is Lipschitz at `1` and inversion of a
near-unit costs only a factor two, the whole `z^{-3/2}` amplitude is within `O(1/u)` of its pure
rapidity value `(q u)^{-3/2}`.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The explicit window constant for the shell radius. -/
def shellRadiusBound (sigma kappa L : ℝ) : ℝ :=
  (sigma ^ 2 + L ^ 2 + (kappa * L + sigma) ^ 2 / shellQ kappa ^ 2) / (2 * shellQ kappa)
    + (kappa * L + sigma) / shellQ kappa

theorem shellRadiusBound_nonneg {sigma kappa L : ℝ} (hkappa : 1 < kappa) (hsigma : 0 ≤ sigma)
    (hL : 0 ≤ L) : 0 ≤ shellRadiusBound sigma kappa L := by
  have hq : 0 < shellQ kappa := shellQ_pos hkappa
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  rw [shellRadiusBound]
  have h1 : (0 : ℝ) ≤ (sigma ^ 2 + L ^ 2 + (kappa * L + sigma) ^ 2 / shellQ kappa ^ 2)
      / (2 * shellQ kappa) := by
    have hnum : (0 : ℝ) ≤ sigma ^ 2 + L ^ 2 + (kappa * L + sigma) ^ 2 / shellQ kappa ^ 2 := by
      have := div_nonneg (sq_nonneg (kappa * L + sigma)) (sq_nonneg (shellQ kappa))
      nlinarith [sq_nonneg sigma, sq_nonneg L]
    exact div_nonneg hnum (by linarith)
  have h2 : (0 : ℝ) ≤ (kappa * L + sigma) / shellQ kappa := by
    have : (0 : ℝ) ≤ kappa * L + sigma := by nlinarith
    exact div_nonneg this hq.le
  linarith

theorem norm_shellRadius_ratio_sub_one_le {sigma kappa u s L : ℝ} (hkappa : 1 < kappa)
    (hu : 1 ≤ u) (hs : 0 ≤ s) (hsL : s ≤ L) (hsigma : 0 < sigma) :
    ‖HTGeometry.csqrt (xiMassShellArgument sigma kappa u s) / ((shellQ kappa * u : ℝ) : ℂ) - 1‖
      ≤ shellRadiusBound sigma kappa L / (shellQ kappa * u) := by
  have hq : 0 < shellQ kappa := shellQ_pos hkappa
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  have hqu : (0 : ℝ) < shellQ kappa * u := mul_pos hq hu0
  have hquC : ((shellQ kappa * u : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hqu
  have hval : HTGeometry.csqrt (xiMassShellArgument sigma kappa u s)
        / ((shellQ kappa * u : ℝ) : ℂ) - 1
      = (HTGeometry.csqrt (xiMassShellArgument sigma kappa u s)
          - ((shellQ kappa * u : ℝ) : ℂ)) / ((shellQ kappa * u : ℝ) : ℂ) := by
    field_simp
  rw [hval, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqu]
  rw [div_le_div_iff₀ hqu hqu]
  have hmain := norm_csqrt_shellArgument_sub_rapidity_le hkappa hu hs hsL hsigma
  have hb : ‖HTGeometry.csqrt (xiMassShellArgument sigma kappa u s)
      - ((shellQ kappa * u : ℝ) : ℂ)‖ ≤ shellRadiusBound sigma kappa L := by
    simpa only [shellRadiusBound] using hmain
  nlinarith [hb, hqu]

/-- Factoring a positive real scalar out of the `z √z` amplitude. -/
theorem mul_csqrt_ofReal_mul {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : 0 < w.re) :
    (((r : ℝ) : ℂ) * w) * HTGeometry.csqrt (((r : ℝ) : ℂ) * w)
      = ((r : ℝ) : ℂ) * ((Real.sqrt r : ℝ) : ℂ) * (w * HTGeometry.csqrt w) := by
  rw [HTGeometry.csqrt_ofReal_mul hr hw]
  ring

end

end RHTower

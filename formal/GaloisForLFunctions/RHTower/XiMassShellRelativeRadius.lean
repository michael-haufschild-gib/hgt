import GaloisForLFunctions.RHTower.XiMassShellPhase

/-!
# The relative size of the shell propagation radius

The shell defect is bounded on every window `0 ≤ s ≤ L` by an explicit constant, so the principal
root of the propagation argument satisfies

`‖z − q u‖ ≤ D_L`  and hence  `‖z/(q u) − 1‖ ≤ D_L/(q u)`

with `D_L` independent of the height.  Both statements are what the shell asymptotic needs: the
first controls the exponential factor, the second the `z^{-3/2}` amplitude.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- An explicit window bound for the shell defect. -/
theorem norm_xiMassShellDefect_le {sigma kappa s L : ℝ} (hkappa : 1 < kappa) (hs : 0 ≤ s)
    (hsL : s ≤ L) (hsigma : 0 ≤ sigma) :
    ‖xiMassShellDefect sigma kappa s‖
      ≤ sigma ^ (2 : ℕ) + L ^ (2 : ℕ) + (kappa * L + sigma) ^ (2 : ℕ) / shellQ kappa ^ (2 : ℕ) := by
  have hq : 0 < shellQ kappa := shellQ_pos hkappa
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have hL : 0 ≤ L := le_trans hs hsL
  have hQC : ((shellQ kappa : ℝ) : ℂ) ≠ 0 := by simpa [shellQ] using ne_of_gt hq
  have hden : ‖(((Real.sqrt (kappa ^ (2 : ℕ) - 1) : ℝ) : ℂ)) ^ (2 : ℕ)‖ = shellQ kappa ^ (2 : ℕ) := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by simpa [shellQ] using hq)]
    rw [shellQ]
  have hnum : ‖((kappa : ℂ) * (s : ℂ) + (sigma : ℂ) * I) ^ (2 : ℕ)‖ ≤ (kappa * L + sigma) ^ (2 : ℕ) := by
    rw [norm_pow]
    have hle : ‖(kappa : ℂ) * (s : ℂ) + (sigma : ℂ) * I‖ ≤ kappa * L + sigma := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
        Complex.norm_I, mul_one, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos hkappa0, abs_of_nonneg hs, abs_of_nonneg hsigma]
      nlinarith
    have hnn : (0 : ℝ) ≤ ‖(kappa : ℂ) * (s : ℂ) + (sigma : ℂ) * I‖ := norm_nonneg _
    nlinarith [hle, hnn]
  have hsig : ‖((sigma : ℂ)) ^ (2 : ℕ)‖ = sigma ^ (2 : ℕ) := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsigma]
  have hs2 : ‖((s : ℂ)) ^ (2 : ℕ)‖ ≤ L ^ (2 : ℕ) := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
    nlinarith
  rw [xiMassShellDefect]
  refine le_trans (norm_sub_le _ _) ?_
  refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
  rw [norm_div, hden]
  have hq2 : (0 : ℝ) < shellQ kappa ^ (2 : ℕ) := by positivity
  have hdivle : ‖((kappa : ℂ) * (s : ℂ) + (sigma : ℂ) * I) ^ (2 : ℕ)‖ / shellQ kappa ^ (2 : ℕ)
      ≤ (kappa * L + sigma) ^ (2 : ℕ) / shellQ kappa ^ (2 : ℕ) := by
    rw [div_le_div_iff₀ hq2 hq2]
    nlinarith [hnum, hq2]
  linarith [hsig.le, hs2, hdivle, hsig.ge]

/-- The distance from the propagation radius to the pure rapidity term is bounded on every
window. -/
theorem norm_csqrt_shellArgument_sub_rapidity_le {sigma kappa u s L : ℝ} (hkappa : 1 < kappa)
    (hu : 1 ≤ u) (hs : 0 ≤ s) (hsL : s ≤ L) (hsigma : 0 < sigma) :
    ‖HTGeometry.csqrt (xiMassShellArgument sigma kappa u s) - ((shellQ kappa * u : ℝ) : ℂ)‖
      ≤ (sigma ^ (2 : ℕ) + L ^ (2 : ℕ) + (kappa * L + sigma) ^ (2 : ℕ) / shellQ kappa ^ (2 : ℕ))
          / (2 * shellQ kappa)
        + (kappa * L + sigma) / shellQ kappa := by
  have hq : 0 < shellQ kappa := shellQ_pos hkappa
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have hL : 0 ≤ L := le_trans hs hsL
  have hshellq : Real.sqrt (kappa ^ (2 : ℕ) - 1) = shellQ kappa := rfl
  have hstep1 := norm_csqrt_shellArgument_sub_shellRadius_le hkappa hu0 hs hsigma
  rw [hshellq] at hstep1
  have hdefect := norm_xiMassShellDefect_le hkappa hs hsL hsigma.le
  have hsplit : ‖xiMassShellRadius sigma kappa u s - ((shellQ kappa * u : ℝ) : ℂ)‖
      ≤ (kappa * L + sigma) / shellQ kappa := by
    have hval : xiMassShellRadius sigma kappa u s - ((shellQ kappa * u : ℝ) : ℂ)
        = ((kappa : ℂ) * (s : ℂ) + (sigma : ℂ) * I) / ((shellQ kappa : ℝ) : ℂ) := by
      rw [xiMassShellRadius, hshellq]
      ring
    rw [hval, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq,
      div_le_div_iff₀ hq hq]
    refine mul_le_mul_of_nonneg_right ?_ hq.le
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
      Complex.norm_I, mul_one, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hkappa0, abs_of_nonneg hs, abs_of_nonneg hsigma.le]
    nlinarith
  have htri : ‖HTGeometry.csqrt (xiMassShellArgument sigma kappa u s)
      - ((shellQ kappa * u : ℝ) : ℂ)‖
      ≤ ‖HTGeometry.csqrt (xiMassShellArgument sigma kappa u s)
          - xiMassShellRadius sigma kappa u s‖
        + ‖xiMassShellRadius sigma kappa u s - ((shellQ kappa * u : ℝ) : ℂ)‖ := by
    have := norm_add_le (HTGeometry.csqrt (xiMassShellArgument sigma kappa u s)
      - xiMassShellRadius sigma kappa u s)
      (xiMassShellRadius sigma kappa u s - ((shellQ kappa * u : ℝ) : ℂ))
    simpa using this
  have hfirst : ‖HTGeometry.csqrt (xiMassShellArgument sigma kappa u s)
      - xiMassShellRadius sigma kappa u s‖
      ≤ (sigma ^ (2 : ℕ) + L ^ (2 : ℕ) + (kappa * L + sigma) ^ (2 : ℕ) / shellQ kappa ^ (2 : ℕ)) / (2 * shellQ kappa) := by
    refine le_trans hstep1 ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hbound0 : (0 : ℝ) ≤ sigma ^ (2 : ℕ) + L ^ (2 : ℕ) + (kappa * L + sigma) ^ (2 : ℕ) / shellQ kappa ^ (2 : ℕ) := by
      have hdiv : (0 : ℝ) ≤ (kappa * L + sigma) ^ (2 : ℕ) / shellQ kappa ^ (2 : ℕ) :=
        div_nonneg (sq_nonneg _) (sq_nonneg _)
      nlinarith [sq_nonneg sigma, sq_nonneg L]
    have h1 := mul_le_mul_of_nonneg_right hdefect (by linarith : (0 : ℝ) ≤ 2 * shellQ kappa)
    have h2 : (0 : ℝ) ≤ (sigma ^ (2 : ℕ) + L ^ (2 : ℕ) + (kappa * L + sigma) ^ (2 : ℕ) / shellQ kappa ^ (2 : ℕ))
        * (2 * shellQ kappa) * (u - 1) :=
      mul_nonneg (mul_nonneg hbound0 (by linarith)) (by linarith)
    nlinarith [h1, h2]
  linarith [htri, hfirst, hsplit]

end

end RHTower

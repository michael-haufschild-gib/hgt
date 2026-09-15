import GaloisForLFunctions.RHTower.PrimeArchFinitePrefixLogHeightNoGo

open Complex Set Filter

namespace RHTower
noncomputable section

/-- Every truncation schedule below any constant strictly larger than the Chebyshev threshold
`42` still misses every common D2 defect floor cofinally. -/
theorem finiteVonMangoldtPrimeLogHeightDefect_subcriticalSchedule_cofinally_unboundedBelow
    (depth : ℕ → ℕ) (c : ℝ) (hc : 42 < c)
    (hpos : ∀ᶠ n : ℕ in atTop, 1 ≤ depth n)
    (hslow : ∀ᶠ n : ℕ in atTop,
      c * (depth n : ℝ) ^ ((3 : ℝ) / 4) ≤ Real.log n) :
    ∀ (L : ℝ) (U : ℕ), ∃ n : ℕ, 12 ≤ n ∧ U ≤ n ∧
      finiteVonMangoldtPrimeLogHeightDefect (depth n)
        (gaussianRatPoint ((1 / 4, n) : ℚ × ℚ)) < L := by
  intro L U
  have hgap : 0 < c - 42 := by linarith
  have hcpos : 0 < c := by linarith
  have hlogTendsto : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ n : ℕ in atTop,
      (-c * L) / (c - 42) < Real.log n :=
    hlogTendsto.eventually_gt_atTop ((-c * L) / (c - 42))
  have hn12 : ∀ᶠ n : ℕ in atTop, 12 ≤ n := eventually_ge_atTop 12
  have hnU : ∀ᶠ n : ℕ in atTop, U ≤ n := eventually_ge_atTop U
  have hevent : ∀ᶠ n : ℕ in atTop, 12 ≤ n ∧ U ≤ n ∧
      finiteVonMangoldtPrimeLogHeightDefect (depth n)
        (gaussianRatPoint ((1 / 4, n) : ℚ × ℚ)) < L := by
    filter_upwards [hpos, hslow, hlarge, hn12, hnU] with n hnPos hnSlow hnLarge hnTwelve hnUpper
    let q : ℚ × ℚ := (1 / 4, n)
    have hqre : (gaussianRatPoint q).re = 1 / 4 := by
      simp [q, gaussianRatPoint]
    have hqim : (gaussianRatPoint q).im = n := by
      simp [q, gaussianRatPoint]
    have hnorm := norm_finiteVonMangoldtPrimeFlux_le_quarterEnvelope
      (depth n) hqre
    have hre : (finiteVonMangoldtPrimeFlux (depth n)
        (gaussianRatPoint q)).re ≤
        finiteVonMangoldtPrimeFluxQuarterEnvelope (depth n) :=
      (Complex.re_le_norm _).trans hnorm
    have henv :=
      finiteVonMangoldtPrimeFluxQuarterEnvelope_le_twentyOne_mul_depth_rpow_threeQuarter
        (depth n) hnPos
    have hnLarge' : -c * L < Real.log n * (c - 42) :=
      (div_lt_iff₀ hgap).mp hnLarge
    refine ⟨hnTwelve, hnUpper, ?_⟩
    change finiteVonMangoldtPrimeLogHeightDefect (depth n)
        (gaussianRatPoint q) < L
    rw [finiteVonMangoldtPrimeLogHeightDefect, hqim]
    nlinarith
  exact hevent.exists

/-- The exact pointwise Chebyshev envelope for the finite-prefix D2 defect. -/
theorem finiteVonMangoldtPrimeLogHeightDefect_le_criticalEnvelope_sub_logHeight
    (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs : s.re = 1 / 4) :
    finiteVonMangoldtPrimeLogHeightDefect N s ≤
      42 * (N : ℝ) ^ ((3 : ℝ) / 4) - Real.log s.im := by
  have hnorm := norm_finiteVonMangoldtPrimeFlux_le_quarterEnvelope N hs
  have hre : (finiteVonMangoldtPrimeFlux N s).re ≤
      finiteVonMangoldtPrimeFluxQuarterEnvelope N :=
    (Complex.re_le_norm _).trans hnorm
  have henv :=
    finiteVonMangoldtPrimeFluxQuarterEnvelope_le_twentyOne_mul_depth_rpow_threeQuarter
      N hN
  rw [finiteVonMangoldtPrimeLogHeightDefect]
  linarith

/-- Residual-slack form of the sharp finite-prefix no-go. If the log height outruns the exact
Chebyshev envelope by an unbounded additive amount, then the finite-prefix D2 defect tends to
minus infinity along the quarter line. -/
theorem finiteVonMangoldtPrimeLogHeightDefect_criticalSlack_tendsto_atBot
    (depth : ℕ → ℕ)
    (hpos : ∀ᶠ n : ℕ in atTop, 1 ≤ depth n)
    (hslack : Tendsto
      (fun n : ℕ =>
        Real.log n - 42 * (depth n : ℝ) ^ ((3 : ℝ) / 4))
      atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        finiteVonMangoldtPrimeLogHeightDefect (depth n)
          (gaussianRatPoint ((1 / 4, n) : ℚ × ℚ)))
      atTop atBot := by
  apply Filter.tendsto_atBot.2
  intro B
  have hlarge : ∀ᶠ n : ℕ in atTop,
      -B < Real.log n - 42 * (depth n : ℝ) ^ ((3 : ℝ) / 4) :=
    hslack.eventually_gt_atTop (-B)
  filter_upwards [hpos, hlarge] with n hnPos hnLarge
  let q : ℚ × ℚ := (1 / 4, n)
  have hqre : (gaussianRatPoint q).re = 1 / 4 := by
    simp [q, gaussianRatPoint]
  have hqim : (gaussianRatPoint q).im = n := by
    simp [q, gaussianRatPoint]
  have hbound :=
    finiteVonMangoldtPrimeLogHeightDefect_le_criticalEnvelope_sub_logHeight
      (depth n) hnPos hqre
  rw [hqim] at hbound
  exact (hbound.trans_lt (by linarith)).le

end
end RHTower

import GaloisForLFunctions.SurfaceOfSpecZ.TheStepanovBoundIsAPrimeCount

/-!
# The prime number theorem in every window

The trivial Stepanov exponent is `½`, and it holds with `o(·)`: for a tempered configuration in the
open strip every exponent has `Re z < ½`, so `F(u) = 2 Re S(u) e^{−u/2} = Σ_z e_z e^{(z − ½)u} → 0` by
dominated convergence (`tendsto_normTrace_half_of_re_lt_one`). For `ζ` (`ζ(1 + it) ≠ 0`):

  `(P(d) − A(d))/√d → 0`   (`tendsto_primeWindow_sub_archPoleWindow_div_sqrt`),

the smoothed prime count in the window of `d` is its archimedean-plus-pole prediction up to `o(√d)`.
RH is the same statement with `O(1)` in place of `o(√d)`, already at one degree set with power-saving
gaps (`TheStepanovBoundIsAPrimeCount`); an exponent `σ < ½` is a zero-free strip
(`TheWidthLawAtEveryGapSet`). Positivity of `Λ` gives only the exponent `½`.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-- **The normalized trace at depth `½` tends to `0`** in the open strip. -/
theorem tendsto_normTrace_half_of_re_lt_one {Z : ZeroConfig} (hZ : TemperedConfig Z)
    (hlt : ∀ ρ ∈ Z.carrier, ρ.re < 1) :
    Tendsto (normTrace Z (1 / 2)) atTop (𝓝 0) := by
  set e := evenCoeff Z (boxSpline 1 3) with hedef
  have hE := summable_norm_evenCoeff_spline hZ
  have hre : ∀ z, e z ≠ 0 → z.re < 1 / 2 := by
    intro z hz
    rcases mem_of_evenCoeff_ne_zero hz with h | h
    · have := hlt _ h; simp at this; linarith
    · have := hlt _ h; simp at this; linarith
  have htop : TopDepth Z (1 / 2) := fun z hz => (hre z hz).le
  have hc : Tendsto (fun u : ℝ => ∑' z, e z * cexp ((z - (1 / 2 : ℝ)) * u)) atTop
      (𝓝 (∑' _z : ℂ, (0 : ℂ))) := by
    refine tendsto_tsum_of_dominated_convergence hE (fun z => ?_) ?_
    · by_cases hz : e z = 0
      · simp [hz]
      have hlt' := hre z hz
      have hexp : Tendsto (fun u : ℝ => cexp ((z - (1 / 2 : ℝ)) * u)) atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have hn : ∀ u : ℝ, ‖cexp ((z - (1 / 2 : ℝ)) * u)‖ = Real.exp ((z.re - 1 / 2) * u) := by
          intro u; rw [Complex.norm_exp]; simp
        simp only [hn]
        exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
      simpa using hexp.const_mul (e z)
    · filter_upwards [eventually_ge_atTop 0] with u hu
      intro z
      exact norm_evenCoeff_mul_cexp_le htop z hu
  rw [tsum_zero] at hc
  have hc' := (Complex.continuous_re.tendsto _).comp hc
  rw [Complex.zero_re] at hc'
  refine hc'.congr' (Eventually.of_forall fun u => ?_)
  simp only [Function.comp_def]
  rw [← ofReal_normTrace hZ u, Complex.ofReal_re]

/-- **The prime number theorem in every window.** -/
theorem tendsto_primeWindow_sub_archPoleWindow_div_sqrt :
    Tendsto (fun n : ℕ => (primeWindow n - archPoleWindow n) / Real.sqrt n) atTop (𝓝 0) := by
  have h := (tendsto_normTrace_half_of_re_lt_one temperedConfig_zetaZeroConfig
    (fun _ hρ => hρ.2.2)).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h2 := h.const_mul (-(1 / 2 : ℝ))
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp_def]
  rw [normTrace, ← orbitCorr_eq_re_lagStructure_spline,
    orbitCorr_log_eq_archPoleWindow_sub_primeWindow,
    show Real.exp (-(1 / 2 * Real.log n)) = (Real.sqrt n)⁻¹ by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0, ← Real.exp_neg]; ring_nf]
  ring

end GaloisForLFunctions.SurfaceOfSpecZ

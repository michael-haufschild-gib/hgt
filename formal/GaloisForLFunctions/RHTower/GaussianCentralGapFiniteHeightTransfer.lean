import GaloisForLFunctions.RHTower.GaussianCentralGapFilterLightCone

/-!
# Finite-height transfer for the central Gaussian budget

Let `G(u) = P_½(e^{-u}) − C_½(e^{-u})`.  The Gamma factor `½Γ((ρ−½)/2)` of a zero of height `γ` decays
like `e^{-π|γ|/4}`, while the zero contributes at most `e^{u/4}` at scale `u`.  Hence the budget at
scale `u` only sees zeros of height `≲ 2u/π`.

**Theorem** (`exists_abs_gaussianCentralGapLog_le_of_criticalUpTo`).  There is a universal constant
`C` such that for every `T ≥ 2`: if every zero of `ξ` with `|Im ρ| ≤ T` lies on the critical line,
then `|G(u)| ≤ C` for all `0 < u ≤ πT/2`.

So a verification of RH up to height `T` is a verification of the central Gaussian budget on the scale
range `(0, πT/2]`, with a constant independent of `T`; letting `T → ∞` recovers the budget.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

open XiAtlasFinitePart

/-- **Finite-height transfer.**  A universal `C` bounds the central gap on `(0, πT/2]` as soon as all
zeros up to height `T` are critical. -/
theorem exists_abs_gaussianCentralGapLog_le_of_criticalUpTo :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
      (∀ q : XiZeroCopy, |(xiZero q).im| ≤ T → (xiZero q).re = 1 / 2) →
      ∀ u : ℝ, 0 < u → u ≤ Real.pi * T / 2 → |gaussianCentralGapLog u| ≤ C := by
  obtain ⟨C₀, hC₀, hC₀b⟩ := exists_norm_gaussianCentralGapLog_add_zeroSeries_le
  obtain ⟨W, hW0, hW⟩ := exists_norm_zeroBohrAmplitude_le_inv_sq
  obtain ⟨D, hD0, hD⟩ := exists_norm_zeroBohrAmplitude_mul_exp_le
  have hSs : Summable fun q : XiZeroCopy => ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 :=
    summable_norm_inv_xiZero_sub_half_sq
  set S : ℝ := ∑' q : XiZeroCopy, ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 with hS
  refine ⟨C₀ + (W + D) * S, fun T hT hcrit u hu huT => ?_⟩
  have hterm : ∀ q : XiZeroCopy, ‖zeroBohrAmplitude q * Complex.exp ((xiZero q - 1 / 2) / 2 * u)‖ ≤
      (W + D) * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := by
    intro q
    have hn : 0 ≤ ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := by positivity
    rw [norm_mul, Complex.norm_exp]
    have hre : ((xiZero q - 1 / 2) / 2 * (u : ℂ)).re = ((xiZero q).re - 1 / 2) / 2 * u := by simp
    rw [hre]
    by_cases hlow : |(xiZero q).im| ≤ T
    · rw [hcrit q hlow, sub_self, zero_div, zero_mul, Real.exp_zero, mul_one]
      nlinarith [hW q]
    · push Not at hlow
      have hγ2 : 2 ≤ |(xiZero q).im| := by linarith
      have hdec := hD q hγ2
      have hβ1 := xiZero_re_le_one q
      have hexp : Real.exp (((xiZero q).re - 1 / 2) / 2 * u) ≤
          Real.exp (Real.pi * |(xiZero q).im| / 8) := by
        refine Real.exp_le_exp.2 ?_
        have h1 : ((xiZero q).re - 1 / 2) / 2 * u ≤ u / 4 := by nlinarith
        have h2 : u / 4 ≤ Real.pi * T / 8 := by linarith
        have h3 : Real.pi * T / 8 ≤ Real.pi * |(xiZero q).im| / 8 := by nlinarith [Real.pi_pos]
        linarith
      calc ‖zeroBohrAmplitude q‖ * Real.exp (((xiZero q).re - 1 / 2) / 2 * u)
          ≤ ‖zeroBohrAmplitude q‖ * Real.exp (Real.pi * |(xiZero q).im| / 8) := by gcongr
        _ ≤ D * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := hdec
        _ ≤ (W + D) * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := by nlinarith
  have hsZ : Summable fun q : XiZeroCopy =>
      ‖zeroBohrAmplitude q * Complex.exp ((xiZero q - 1 / 2) / 2 * u)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hSs.mul_left _)
  have hZ : ‖∑' q : XiZeroCopy, zeroBohrAmplitude q * Complex.exp ((xiZero q - 1 / 2) / 2 * u)‖ ≤
      (W + D) * S := by
    refine (norm_tsum_le_tsum_norm hsZ).trans ?_
    rw [hS, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hterm hsZ (hSs.mul_left _)
  have h1 := hC₀b u hu
  have htri := norm_sub_le ((gaussianCentralGapLog u : ℂ) + ∑' q : XiZeroCopy,
      zeroBohrAmplitude q * Complex.exp ((xiZero q - 1 / 2) / 2 * u))
    (∑' q : XiZeroCopy, zeroBohrAmplitude q * Complex.exp ((xiZero q - 1 / 2) / 2 * u))
  rw [add_sub_cancel_right, Complex.norm_real, Real.norm_eq_abs] at htri
  linarith

end

end RHTower

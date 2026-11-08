import GaloisForLFunctions.SelbergClass.Primon.AveragedPrimePowers
import GaloisForLFunctions.RHTower.RVCumulantAverage
import GaloisForLFunctions.RHTower.Sieve.GhsTotalErrorBound

/-!
# Square-root growth of the averaged arithmetic explicit formula

The exact prime-power defect is negligible compared with its square-root
cutoff. The unconditional prime number theorem therefore gives `A(N)/N → 1`.
At a real cutoff `x`, the mass is `A(floor(sqrt(x)))`, and its ratio to
`sqrt(x)` tends to one. These statements concern the integrated positive
arithmetic staircase obtained by phase averaging.
-/

open Filter Topology

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The exact tower deficit is sublinear in the square-root cutoff. -/
theorem tendsto_averagedPrimePowerDefect_div :
    Tendsto (fun N : ℕ => averagedPrimePowerDefect N / N) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun N => div_nonneg (averagedPrimePowerDefect_nonneg N) (Nat.cast_nonneg N))
    (fun N => div_le_div_of_nonneg_right (averagedPrimePowerDefect_le_log_sq N)
      (Nat.cast_nonneg N))
  exact RHTower.Sieve.tendsto_sq_log_div_atTop.comp tendsto_natCast_atTop_atTop

/-- The integrated averaged prime-power mass has the same leading term as Chebyshev's theta. -/
theorem tendsto_averagedPrimePowerCount_div :
    Tendsto (fun N : ℕ => averagedPrimePowerCount N / N) atTop (𝓝 1) := by
  have ht := (RHTower.tendsto_chebyshevTheta_div (c := 1) zero_lt_one).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simp only [one_mul] at ht
  simp_rw [averagedPrimePowerCount_eq_theta_sub_defect, sub_div]
  simpa only [Function.comp_apply, sub_zero] using ht.sub tendsto_averagedPrimePowerDefect_div

/-- Integrated averaged arithmetic mass at a real prime-power cutoff. -/
def averagedExplicitFormulaMass (x : ℝ) : ℝ :=
  averagedPrimePowerCount ⌊Real.sqrt x⌋₊

/-- The averaged arithmetic staircase is everywhere nonnegative. -/
theorem averagedExplicitFormulaMass_nonneg (x : ℝ) : 0 ≤ averagedExplicitFormulaMass x :=
  averagedPrimePowerCount_nonneg _

/-- Increasing the real cutoff only adds positive averaged prime-power mass. -/
theorem averagedExplicitFormulaMass_mono : Monotone averagedExplicitFormulaMass :=
  averagedPrimePowerCount_mono.comp (Nat.floor_mono.comp (fun _ _ h => Real.sqrt_le_sqrt h))

/-- Squared integer cutoffs recover the exact finite prime-power sum. -/
theorem averagedExplicitFormulaMass_nat_sq (N : ℕ) :
    averagedExplicitFormulaMass ((N : ℝ) ^ 2) = averagedPrimePowerCount N := by
  rw [averagedExplicitFormulaMass, Real.sqrt_sq_eq_abs, abs_of_nonneg (Nat.cast_nonneg N),
    Nat.floor_natCast]

/-- The real averaged arithmetic mass grows as the square root of its cutoff. -/
theorem tendsto_averagedExplicitFormulaMass_div_sqrt :
    Tendsto (fun x : ℝ => averagedExplicitFormulaMass x / Real.sqrt x) atTop (𝓝 1) := by
  have hf : Tendsto (fun x : ℝ => ⌊Real.sqrt x⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp Real.tendsto_sqrt_atTop
  have h := (tendsto_averagedPrimePowerCount_div.comp hf).mul
    (tendsto_nat_floor_div_atTop.comp Real.tendsto_sqrt_atTop)
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [hf.eventually (eventually_ge_atTop 1)] with x hx
  have hn : ((⌊Real.sqrt x⌋₊ : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : ⌊Real.sqrt x⌋₊ ≠ 0)
  change averagedPrimePowerCount ⌊Real.sqrt x⌋₊ / (⌊Real.sqrt x⌋₊ : ℝ) *
    ((⌊Real.sqrt x⌋₊ : ℝ) / Real.sqrt x) =
      averagedPrimePowerCount ⌊Real.sqrt x⌋₊ / Real.sqrt x
  field_simp [hn]

end
end GaloisForLFunctions.SelbergClass.Primon

import GaloisForLFunctions.HTGeometry.SzegoOuterBoundary

/-!
# The Szegő outer function is bounded on the disk (`D ∈ H^∞`)

For a weight bounded above by `C`, the Szegő outer function satisfies `‖D(re^{iφ})‖² ≤ C` on the
whole open disk.  This is the exact mirror of the reciprocal bound `‖1/D‖² ≤ c⁻¹`: the Poisson mean
of `log w` is a probability average, so it inherits any pointwise bound on `log w`.  Together the two
bounds give `0 < c ≤ ‖D‖² ≤ C`, i.e. both `D` and `1/D` are bounded analytic — the multiplier
property behind `D · Sₙ → 1`.
-/

open MeasureTheory Complex Filter Topology
open scoped Real

namespace GaloisForLFunctions.HTGeometry

/-- **Poisson-mean upper bound** (symmetric interval).  If `g ≤ M` pointwise, the normalized Poisson
average of `g` over `[-π,π]` is `≤ M`.  Poisson is a probability kernel. -/
theorem poissonMean_symm_le {g : ℝ → ℝ} {M : ℝ}
    (hgI : IntervalIntegrable g volume (-π) π) (hgM : ∀ θ, g θ ≤ M)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (2 * π)⁻¹ * ∫ t in (-π)..π, poissonKer r t * g t ≤ M := by
  have habs : |r| < 1 := by rw [abs_of_nonneg hr0]; exact hr1
  have hcont : Continuous (poissonKer r) := poissonKer_continuous habs
  have hnn : ∀ t, 0 ≤ poissonKer r t := fun t => poissonKer_nonneg hr0 hr1 t
  have hπ : (0:ℝ) < π := Real.pi_pos
  have hle : (∫ t in (-π)..π, poissonKer r t * g t) ≤ ∫ t in (-π)..π, poissonKer r t * M := by
    apply intervalIntegral.integral_mono_on (by linarith)
      (hgI.continuousOn_mul hcont.continuousOn)
      ((hcont.mul continuous_const).intervalIntegrable _ _)
    intro t _
    exact mul_le_mul_of_nonneg_left (hgM t) (hnn t)
  rw [intervalIntegral.integral_mul_const, poissonKer_integral_symm hr0 hr1] at hle
  have h2π : (0:ℝ) < 2 * π := by linarith
  rw [inv_mul_eq_div, div_le_iff₀ h2π]
  linarith [hle]

/-- **Disk `H^∞` bound for the outer function.**  For a positive weight bounded above by `C`,
`‖D(r e^{iφ})‖² ≤ C` on the whole disk.  With the reciprocal bound `‖1/D‖² ≤ c⁻¹`, this makes `D` a
bounded analytic multiplier. -/
theorem normSq_szegoOuter_le {w : ℝ → ℝ} {C : ℝ} (hC : 0 < C)
    (hlog : IntervalIntegrable (fun θ => Real.log (w θ)) volume 0 (2 * π))
    (hper : Function.Periodic (fun θ => Real.log (w θ)) (2 * π))
    (hlogφ : ∀ φ, IntervalIntegrable (fun t => Real.log (w (φ + t))) volume (-π) π)
    (hwpos : ∀ θ, 0 < w θ) (hwC : ∀ θ, w θ ≤ C) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (φ : ℝ) :
    ‖szegoOuter w (circleMap 0 r φ)‖ ^ (2 : ℕ) ≤ C := by
  rw [normSq_szegoOuter_eq_poissonConv hlog hper hr0 hr1 φ,
    show C = Real.exp (Real.log C) from (Real.exp_log hC).symm]
  apply Real.exp_le_exp.mpr
  exact poissonMean_symm_le (hlogφ φ)
    (fun t => Real.log_le_log (hwpos (φ + t)) (hwC (φ + t))) hr0 hr1

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseValuationAnalytic
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseValuationTwistSummability
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseLogSquareEnergy
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseDiskHurwitz

/-!
# Zero-free local residue functions of the actual Weil source

Original Weil positivity alone pays every source estimate. Twisted logarithmic
absolute convergence gives nonvanishing approximants; compact convergence and
the positive constant endpoint prevent zeros in the square-root disk.
-/

open Complex Filter Topology Metric Set
noncomputable section
namespace RHTower.WeilSingularArithmetic
open WeilWorkSettledPhase IntegerMassRigidity

theorem source_valuationTwist_LSeries {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {p : ℕ} (hp : p.Prime) {s : ℝ} (hs : 1 < s) {z : ℂ}
    (hz : ‖z‖ < Real.sqrt (p : ℝ)) :
    LSeriesSummable (valuationTwist p z (sourceCoeff lam)) (s : ℂ) ∧
      LSeries (valuationTwist p z (sourceCoeff lam)) (s : ℂ) =
        Complex.exp (LSeries (valuationTwist p z (lamLog lam)) (s : ℂ)) := by
  have hf : LSeriesSummable (lamLog lam) (s : ℂ) :=
    lseriesSummable_of_le (norm_lamLog_le lam)
      (fun _ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ)
      (by simpa only [Complex.ofReal_re] using hs)
  exact LSeries_valuationTwist_dirichletExp p z (lamLog_zero lam) (lamLog_one lam)
    (summable_valuationTwist_of_square hp hs hf (summable_lamLog_sq_div_rpow hW hs) hz)

theorem valuationRatioSeries_eq_twisted_LSeries {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {p : ℕ} (hp : p.Prime) {s : ℝ} (hs : 1 < s)
    {z : ℂ} (hz : ‖z‖ < Real.sqrt (p : ℝ)) :
    valuationRatioSeries lam p s z =
      LSeries (valuationTwist p z (sourceCoeff lam)) (s : ℂ) /
        LSeries (sourceCoeff lam) (s : ℂ) := by
  rw [LSeries_valuationTwist_eq_tsum hp z (source_valuationTwist_LSeries hW hp hs hz).1,
    ← tsum_div_const]
  exact tsum_congr fun k => by ring

theorem valuationRatioSeries_ne_zero {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {p : ℕ} (hp : p.Prime) {s : ℝ} (hs : 1 < s)
    {z : ℂ} (hz : ‖z‖ < Real.sqrt (p : ℝ)) : valuationRatioSeries lam p s z ≠ 0 := by
  rw [valuationRatioSeries_eq_twisted_LSeries hW hp hs hz,
    (source_valuationTwist_LSeries hW hp hs hz).2,
    (sourceCoeff_LSeries hW (s := (s : ℂ)) (by simpa using hs)).2, zetaOf]
  exact div_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)

/-- The actual signed valuation endpoints form a normalized zero-free
holomorphic function throughout the square-root disk. -/
theorem exists_forward_valuation_zero_free {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {p : ℕ} (hp : p.Prime) :
    ∃ u : ℕ → ℝ, 0 < u 0 ∧ HasSum u 1 ∧
      (∀ k : ℕ, Tendsto (fun s : ℝ =>
        LSeries (valuationPart p k (sourceCoeff lam)) (s : ℂ) /
          LSeries (sourceCoeff lam) (s : ℂ)) (𝓝[>] 1) (𝓝 (u k : ℂ))) ∧
      valuationResidueSeries u 0 = (u 0 : ℂ) ∧ valuationResidueSeries u 1 = 1 ∧
      DifferentiableOn ℂ (valuationResidueSeries u) (ball 0 (Real.sqrt (p : ℝ))) ∧
      (∀ z : ℂ, ‖z‖ < Real.sqrt (p : ℝ) → valuationResidueSeries u z ≠ 0) ∧
      ∀ R : ℝ, 0 ≤ R → R < Real.sqrt (p : ℝ) →
        TendstoUniformlyOn (valuationRatioSeries lam p) (valuationResidueSeries u)
          (𝓝[>] 1) (closedBall 0 R) := by
  obtain ⟨u, hu0, hsum, hu, hU0, hU1, hdiff, _, hconv⟩ :=
    exists_forward_valuation_analytic hW hp
  refine ⟨u, hu0, hsum, hu, hU0, hU1, hdiff, ?_, hconv⟩
  have hroot : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  have hne0 : valuationResidueSeries u 0 ≠ 0 := by
    rw [hU0]
    exact_mod_cast ne_of_gt hu0
  have happrox : ∀ᶠ s : ℝ in 𝓝[>] 1,
      DifferentiableOn ℂ (valuationRatioSeries lam p s) (ball 0 (Real.sqrt (p : ℝ))) := by
    obtain ⟨C, hC, hb⟩ := exists_forward_valuation_ratio_geometric hW hp
    filter_upwards [hb] with s hs
    exact valuation_powerSeries_differentiableOn hp hC hs
  have hnone : ∀ᶠ s : ℝ in 𝓝[>] 1, ∀ z ∈ ball (0 : ℂ) (Real.sqrt (p : ℝ)),
      valuationRatioSeries lam p s z ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with s hs z hz
    exact valuationRatioSeries_ne_zero hW hp hs
      (by simpa only [mem_ball, dist_zero_right] using hz)
  have hh := disk_zero_free_of_uniform_limit hroot hdiff hne0 happrox hnone hconv
  intro z hz
  exact hh z (by simpa only [mem_ball, dist_zero_right] using hz)

end RHTower.WeilSingularArithmetic

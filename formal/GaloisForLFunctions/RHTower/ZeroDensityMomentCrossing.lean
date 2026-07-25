import Mathlib

/-!
# The moment-bound crossing for zero-density estimates

For a Dirichlet polynomial of length `N` at height `T = N^{τ}` with `τ ∈ (k, k+1)`, two moment bounds
compete: raising to the `k+1`-st power (valid once `N^{k+1} ≥ T`) and the `k`-th mean value (valid
while `N^{k} ≤ T`).  They agree at `τ = k + 2 - 2σ`, and there the common value exceeds the
density-hypothesis target `(2 - 2σ)τ` by `(2 - 2σ)(2σ - 1)`, a quantity **independent of `k`**.
-/

/-- The "power" branch of the moment bound on the window `(k, k+1)`: raising to the `k+1`-st power. -/
noncomputable def powerBranch (σ k : ℝ) : ℝ := (k + 1) * (2 - 2 * σ)

/-- The "mean value" branch of the moment bound at abscissa `τ`. -/
noncomputable def meanValueBranch (σ k τ : ℝ) : ℝ := τ + k * (1 - 2 * σ)

/-- The Density-Hypothesis requirement at abscissa `τ`. -/
noncomputable def densityTarget (σ τ : ℝ) : ℝ := (2 - 2 * σ) * τ

/-- The two moment branches agree at `τ = k + 2 - 2σ`. -/
theorem powerBranch_eq_meanValueBranch (σ k : ℝ) :
    powerBranch σ k = meanValueBranch σ k (k + 2 - 2 * σ) := by
  unfold powerBranch meanValueBranch
  ring

/-- At the crossing `τ = k + 2 - 2σ` the moment bound exceeds the Density-Hypothesis target by
`(2 - 2σ)(2σ - 1)`, **independently of `k`**. -/
theorem crossing_shortfall (σ k : ℝ) :
    powerBranch σ k - densityTarget σ (k + 2 - 2 * σ) = (2 - 2 * σ) * (2 * σ - 1) := by
  unfold powerBranch densityTarget
  ring

/-- The shortfall is positive exactly when `1/2 < σ < 1`. -/
theorem crossing_shortfall_pos {σ : ℝ} (h₁ : 1 / 2 < σ) (h₂ : σ < 1) (k : ℝ) :
    0 < powerBranch σ k - densityTarget σ (k + 2 - 2 * σ) := by
  rw [crossing_shortfall]
  have h3 : 0 < 2 - 2 * σ := by linarith
  have h4 : 0 < 2 * σ - 1 := by linarith
  positivity

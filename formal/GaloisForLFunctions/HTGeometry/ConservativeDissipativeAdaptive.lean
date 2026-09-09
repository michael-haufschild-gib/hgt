import GaloisForLFunctions.HTGeometry.ConservativeDissipativeResolvent

set_option autoImplicit false

/-!
# Adaptive nonlinear Cayley energy accounting

The Schaffer–Exl split (arXiv:2609.04530) yields discrete trajectories
with unrestricted changes of raw coefficients, including state dependence.
Every step has an exact physical damping identity. Telescoping gives
summable total loss, a precise limiting energy, and vanishing per-step
loss, without assuming convergence or regularity of the coefficients.
-/
open scoped InnerProductSpace NNReal BigOperators
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- A nonlinear discrete orbit with arbitrary state-dependent, time-dependent raw coefficients. -/
def adaptiveCayleyOrbit (A : ℕ → E → E →L[𝕜] E) (B : ℕ → E → E →L[𝕜] F)
    (t : ℕ → ℝ≥0) (x : E) : ℕ → E
  | 0 => x
  | n + 1 => let y := adaptiveCayleyOrbit A B t x n
    cayleyStep (A n y) (B n y) (t n) y

/-- The physical observation loss at each adaptive midpoint. -/
def adaptiveCayleyLoss (A : ℕ → E → E →L[𝕜] E) (B : ℕ → E → E →L[𝕜] F)
    (t : ℕ → ℝ≥0) (x : E) (n : ℕ) : ℝ :=
  let y := adaptiveCayleyOrbit A B t x n
  4 * (t n : ℝ) * ‖B n y (implicitStep (A n y) (B n y) (t n) y)‖ ^ 2

/-- No continuity, boundedness, or differentiability premise on the coefficient schedule is needed. -/
theorem adaptiveCayley_step_energy (A : ℕ → E → E →L[𝕜] E) (B : ℕ → E → E →L[𝕜] F)
    (t : ℕ → ℝ≥0) (x : E) (n : ℕ) :
    ‖adaptiveCayleyOrbit A B t x (n + 1)‖ ^ 2 + adaptiveCayleyLoss A B t x n =
      ‖adaptiveCayleyOrbit A B t x n‖ ^ 2 := by
  exact cayleyStep_energy _ _ _ _

theorem adaptiveCayleyLoss_nonneg (A : ℕ → E → E →L[𝕜] E) (B : ℕ → E → E →L[𝕜] F)
    (t : ℕ → ℝ≥0) (x : E) (n : ℕ) : 0 ≤ adaptiveCayleyLoss A B t x n := by
  unfold adaptiveCayleyLoss
  exact mul_nonneg (mul_nonneg (by positivity) (t n).coe_nonneg) (sq_nonneg _)

/-- Exact accumulated physical damping along every nonlinear adaptive orbit. -/
theorem adaptiveCayley_energy_balance (A : ℕ → E → E →L[𝕜] E) (B : ℕ → E → E →L[𝕜] F)
    (t : ℕ → ℝ≥0) (x : E) (n : ℕ) :
    ‖adaptiveCayleyOrbit A B t x n‖ ^ 2 + ∑ k ∈ Finset.range n, adaptiveCayleyLoss A B t x k =
      ‖x‖ ^ 2 := by
  induction n with
  | zero => simp [adaptiveCayleyOrbit]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    linarith [adaptiveCayley_step_energy A B t x n]

/-- Arbitrary changes of coefficients and step sizes cannot increase the quadratic energy. -/
theorem adaptiveCayley_energy_antitone (A : ℕ → E → E →L[𝕜] E) (B : ℕ → E → E →L[𝕜] F)
    (t : ℕ → ℝ≥0) (x : E) : Antitone (fun n => ‖adaptiveCayleyOrbit A B t x n‖ ^ 2) := by
  apply antitone_nat_of_succ_le
  intro n
  linarith [adaptiveCayley_step_energy A B t x n, adaptiveCayleyLoss_nonneg A B t x n]

/-- An infinite adaptive trajectory has finite total physical loss, bounded by its initial energy. -/
theorem adaptiveCayleyLoss_summable (A : ℕ → E → E →L[𝕜] E) (B : ℕ → E → E →L[𝕜] F)
    (t : ℕ → ℝ≥0) (x : E) : Summable (adaptiveCayleyLoss A B t x) := by
  apply summable_of_sum_range_le (fun n => adaptiveCayleyLoss_nonneg A B t x n) (c := ‖x‖ ^ 2)
  intro n
  linarith [adaptiveCayley_energy_balance A B t x n, sq_nonneg ‖adaptiveCayleyOrbit A B t x n‖]

/-- Total dissipation cannot exceed the initial quadratic energy. -/
theorem adaptiveCayleyLoss_tsum_le (A : ℕ → E → E →L[𝕜] E) (B : ℕ → E → E →L[𝕜] F)
    (t : ℕ → ℝ≥0) (x : E) : ∑' n, adaptiveCayleyLoss A B t x n ≤ ‖x‖ ^ 2 := by
  apply (adaptiveCayleyLoss_summable A B t x).tsum_le_of_sum_range_le
  intro n
  linarith [adaptiveCayley_energy_balance A B t x n, sq_nonneg ‖adaptiveCayleyOrbit A B t x n‖]

/-- Every adaptive orbit has an exact limiting energy, including arbitrarily changing coefficients. -/
theorem adaptiveCayley_energy_tendsto (A : ℕ → E → E →L[𝕜] E) (B : ℕ → E → E →L[𝕜] F)
    (t : ℕ → ℝ≥0) (x : E) :
    Filter.Tendsto (fun n => ‖adaptiveCayleyOrbit A B t x n‖ ^ 2) Filter.atTop
      (nhds (‖x‖ ^ 2 - ∑' n, adaptiveCayleyLoss A B t x n)) := by
  have h : Filter.Tendsto
      (fun n => ‖x‖ ^ 2 - ∑ k ∈ Finset.range n, adaptiveCayleyLoss A B t x k) Filter.atTop
      (nhds (‖x‖ ^ 2 - ∑' n, adaptiveCayleyLoss A B t x n)) :=
    tendsto_const_nhds.sub (adaptiveCayleyLoss_summable A B t x).hasSum.tendsto_sum_nat
  convert h using 1
  funext n
  linarith [adaptiveCayley_energy_balance A B t x n]

/-- The physical loss per adaptive step tends to zero; no convergence of the state is asserted. -/
theorem adaptiveCayleyLoss_tendsto_zero (A : ℕ → E → E →L[𝕜] E) (B : ℕ → E → E →L[𝕜] F)
    (t : ℕ → ℝ≥0) (x : E) :
    Filter.Tendsto (adaptiveCayleyLoss A B t x) Filter.atTop (nhds 0) :=
  (adaptiveCayleyLoss_summable A B t x).tendsto_atTop_zero

end
end GaloisForLFunctions.HTGeometry.SchafferExl

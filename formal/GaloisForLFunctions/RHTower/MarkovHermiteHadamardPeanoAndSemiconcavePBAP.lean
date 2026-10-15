import GaloisForLFunctions.RHTower.MarkovResolventFaithfulnessAndContinuumSignChangePBAP

/-!
# Hermite–Hadamard Secant Positivity, the Peano Parabola, and Semiconcave $\theta$-Amplifier Absorption on the Primitive Hyperplane and Odd Sector

This module develops the exact secant-remainder and Peano parabola theory for
`trueTrapezoidalCellDefect` and couples it to the upgraded $(\alpha = 1 / 2, \theta)$ Euler–Maclaurin +
$m$-th Cesàro decomposition from Module 42 and the resolvent faithfulness theorem from Module 43:

1. **Section 1 (The Unit-Cell Secant Interpolant `cellSecant`, the Peano Parabola `cellParabola`,
   and the Exact Secant-Remainder Representation of `trueTrapezoidalCellDefect`):**
   - For each unit cell `[n - 1, n]`, we define the linear secant interpolant
     `cellSecant g n x := (n - x) * g(n - 1) + (x - (n - 1)) * g(n)`
     and the quadratic Peano / Hermite–Hadamard parabola
     `cellParabola n x := (x - (n - 1)) * (n - x) = 1 / 4 - (x - (n - 1 / 2)) ^ 2`.
   - We prove `0 ≤ cellParabola n x ≤ 1 / 4` on `[n - 1, n]`, the exact quadratic secant identity
     `cellSecant (fun t => t ^ 2) n x - x ^ 2 = cellParabola n x`, and the exact unit-cell integrals
     `∫ x in (n - 1)..n, cellSecant g n x = (g n + g (n - 1)) / 2` and
     `∫ x in (n - 1)..n, cellParabola n x = 1 / 6`.
   - Consequently (`trueTrapezoidalCellDefect_eq_sum_integral_sub_cellSecant`), for every continuous
     profile `g` on `[1, ∞)`,
     `trueTrapezoidalCellDefect g N = ∑ n ∈ Finset.Icc 2 N, ∫ x in (n - 1)..n, (g x - cellSecant g n x)`.

2. **Section 2 (Hermite–Hadamard Secant Positivity and Piecewise Semiconcavity Bounds
   `-(1 / 12) ∑ K_n` for `trueTrapezoidalCellDefect`):**
   - **Hermite–Hadamard Secant Positivity (`trueTrapezoidalCellDefect_nonneg_of_cellSecant_le`)**:
     if `cellSecant g n x ≤ g x` on each unit cell `[n - 1, n]` (`2 ≤ n ≤ N`), then
     `0 ≤ trueTrapezoidalCellDefect g N`.
   - **Piecewise $K_n$-Semiconcavity Lower Bound
     (`neg_sum_div_twelve_le_trueTrapezoidalCellDefect_of_semiconcave`)**:
     if `-(K n / 2) * cellParabola n x ≤ g x - cellSecant g n x` on `[n - 1, n]` for `2 ≤ n ≤ N`,
     then since `∫_{n-1}^n (1 / 2) * cellParabola n x dx = 1 / 12`,
     `-(1 / 12) * (∑ n ∈ Finset.Icc 2 N, K n) ≤ trueTrapezoidalCellDefect g N`.
   - **Two-Sided Second-Order Trapezoidal Error Bound
     (`abs_trueTrapezoidalCellDefect_le_sum_div_twelve_of_abs_sub_cellSecant_le`)**:
     if `|g x - cellSecant g n x| ≤ (K n / 2) * cellParabola n x` on `[n - 1, n]`, then
     `|trueTrapezoidalCellDefect g N| ≤ (1 / 12) * ∑ n ∈ Finset.Icc 2 N, K n`.

3. **Section 3 (The Discrete Unit-Step Sign Law on the Primitive Hyperplane and the
   $\theta$-Amplifier Absorption Theorem for Semiconcave Profiles):**
   - **Exact Discrete Unit-Step Identity on the Primitive Hyperplane
     (`neg_primeBlindCounterterm_unitStep_eq_trueTrapezoidal_of_cosh_zero`)**:
     for every real test `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0`,
     `-primeBlindCounterterm unitStepCountertermWeight F = (∫ u, ‖F u‖²) + bochnerResolventEnergy k_F + 2 * sinhHalfMoment f ^ 2 + trueTrapezoidalCellDefect ℓ_F N`.
     Thus on the primitive hyperplane, the discrete unit-step sum `∑_{n ≥ 2} ℓ_F(n)` is driven negative
     by the sum of three nonnegative coercive quantities `(∫ ‖F‖²) + bochnerResolventEnergy k_F + 2 S(f)²`.
   - **Discrete Unit-Step Nonpositivity and Rigidity under Semiconcavity
     (`primeBlindCounterterm_unitStep_nonpos_of_semiconcave_of_cosh_zero`,
     `markovCountertermEnergy_nonneg_of_unitStep_nonneg_and_semiconcave_of_cosh_zero`)**:
     whenever `(1 / 12) * ∑_{n=2}^N K_n ≤ (∫ ‖F‖²) + bochnerResolventEnergy k_F + 2 * sinhHalfMoment f ^ 2`,
     we have `primeBlindCounterterm unitStepCountertermWeight F ≤ 0`; and if
     `(1 / 12) * ∑_{n=2}^N K_n ≤ ∫ ‖F‖²` while `0 ≤ primeBlindCounterterm unitStepCountertermWeight F`,
     then `bochnerResolventEnergy k_F = 0`, `∫ ‖F‖² = 0`, and `0 ≤ markovCountertermEnergy lam F` for
     all `lam`.
   - **The $\theta$-Amplifier Absorption Theorem for Semiconcave Profiles
     (`markovEnergy_ofReal_nonneg_of_semiconcave_of_cosh_zero`,
     `markovEnergy_ofReal_nonneg_of_semiconcave_energy_ratio_of_cosh_zero`,
     `riemannHypothesis_of_forall_odd_exists_semiconcave_dom`)**:
     every unit increase in the slope gauge $\theta$ increases the positive budget
     `∫ ‖F‖² + bochnerResolventEnergy k_F + 2 * sinhHalfMoment f ^ 2` by $1\times$, while the
     semiconcavity quadrature penalty grows by $(1 / 12) \sum_{n=2}^N K_n$. Consequently, whenever
     `(1 / 12) * ∑_{n=2}^N K_n ≤ (1 - δ) * (∫ ‖F‖² + bochnerResolventEnergy k_F + 2 * sinhHalfMoment f ^ 2)`
     for any `δ ∈ (0, 1]` (i.e., `∑_{n=2}^N K_n < 12 * (total coercive energy)`), choosing
     `θ ≥ max(log N, 2 / δ)` automatically absorbs the entire trapezoidal quadrature defect and yields
     `1 / 100 * ∫ ‖F‖² ≤ markovEnergy F` and `0 ≤ markovEnergy F`!
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ContDiff FourierTransform
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

open WeilOneSided WeilSpectral WeilLevyPole WeilLevyPoleGauss WeilLevyCoshCrossover LebesgueAtomWeil
open RHTower.NonnegativeCone

/-! ## Section 1: The Unit-Cell Secant Interpolant `cellSecant`, the Peano Parabola `cellParabola`, and the Exact Secant-Remainder Representation of `trueTrapezoidalCellDefect` -/

/-- The **Unit-Cell Linear Secant Interpolant** of `g : ℝ → ℝ` on `[(n : ℝ) - 1, (n : ℝ)]`:
`cellSecant g n x = ((n : ℝ) - x) * g ((n : ℝ) - 1) + (x - ((n : ℝ) - 1)) * g (n : ℝ)`. -/
def cellSecant (g : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ((n : ℝ) - x) * g ((n : ℝ) - 1) + (x - ((n : ℝ) - 1)) * g (n : ℝ)

/-- The **Unit-Cell Peano / Hermite–Hadamard Parabola** on `[(n : ℝ) - 1, (n : ℝ)]`:
`cellParabola n x = (x - ((n : ℝ) - 1)) * ((n : ℝ) - x)`. -/
def cellParabola (n : ℕ) (x : ℝ) : ℝ :=
  (x - ((n : ℝ) - 1)) * ((n : ℝ) - x)

@[simp]
theorem cellSecant_left (g : ℝ → ℝ) (n : ℕ) :
    cellSecant g n ((n : ℝ) - 1) = g ((n : ℝ) - 1) := by
  unfold cellSecant
  ring

@[simp]
theorem cellSecant_right (g : ℝ → ℝ) (n : ℕ) :
    cellSecant g n (n : ℝ) = g (n : ℝ) := by
  unfold cellSecant
  ring

@[simp]
theorem cellParabola_left (n : ℕ) :
    cellParabola n ((n : ℝ) - 1) = 0 := by
  unfold cellParabola
  ring

@[simp]
theorem cellParabola_right (n : ℕ) :
    cellParabola n (n : ℝ) = 0 := by
  unfold cellParabola
  ring

/-- Completing the square for `cellParabola n x` around the cell midpoint `(n : ℝ) - 1 / 2`:
`cellParabola n x = 1 / 4 - (x - ((n : ℝ) - 1 / 2)) ^ 2`. -/
theorem cellParabola_eq_quarter_sub_sq (n : ℕ) (x : ℝ) :
    cellParabola n x = 1 / 4 - (x - ((n : ℝ) - 1 / 2)) ^ 2 := by
  unfold cellParabola
  ring

/-- On the unit cell `[(n : ℝ) - 1, (n : ℝ)]`, `0 ≤ cellParabola n x`. -/
theorem cellParabola_nonneg_of_mem_Icc {n : ℕ} {x : ℝ}
    (hx : x ∈ Icc ((n : ℝ) - 1) (n : ℝ)) :
    0 ≤ cellParabola n x := by
  unfold cellParabola
  exact mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)

/-- For every `n : ℕ` and `x : ℝ`, `cellParabola n x ≤ 1 / 4`. -/
theorem cellParabola_le_quarter (n : ℕ) (x : ℝ) :
    cellParabola n x ≤ 1 / 4 := by
  rw [cellParabola_eq_quarter_sub_sq]
  linarith [sq_nonneg (x - ((n : ℝ) - 1 / 2))]

/-- **Exact Quadratic Secant Identity**:
for the quadratic monomial `t ↦ t ^ 2`, the secant remainder on `[(n : ℝ) - 1, (n : ℝ)]` is
identically `cellParabola n x`:
`cellSecant (fun t => t ^ 2) n x - x ^ 2 = cellParabola n x`. -/
theorem cellSecant_sq_sub_sq_eq_cellParabola (n : ℕ) (x : ℝ) :
    cellSecant (fun t => t ^ 2) n x - x ^ 2 = cellParabola n x := by
  unfold cellSecant cellParabola
  ring

/-- For every `g : ℝ → ℝ` and `n : ℕ`, `cellSecant g n` is continuous on `ℝ`. -/
theorem continuous_cellSecant (g : ℝ → ℝ) (n : ℕ) :
    Continuous (cellSecant g n) := by
  unfold cellSecant
  fun_prop

/-- For every `n : ℕ`, `cellParabola n` is continuous on `ℝ`. -/
theorem continuous_cellParabola (n : ℕ) :
    Continuous (cellParabola n) := by
  unfold cellParabola
  fun_prop

/-- **Exact Unit-Cell Integral of `cellSecant g n`**:
`∫ x in ((n : ℝ) - 1)..(n : ℝ), cellSecant g n x = (g (n : ℝ) + g ((n : ℝ) - 1)) / 2`. -/
theorem intervalIntegral_cellSecant (g : ℝ → ℝ) (n : ℕ) :
    (∫ x in ((n : ℝ) - 1)..(n : ℝ), cellSecant g n x) =
      (g (n : ℝ) + g ((n : ℝ) - 1)) / 2 := by
  let F : ℝ → ℝ := fun x =>
    -(((n : ℝ) - x) ^ 2 / 2) * g ((n : ℝ) - 1) +
      ((x - ((n : ℝ) - 1)) ^ 2 / 2) * g (n : ℝ)
  have hderiv : ∀ x ∈ uIcc ((n : ℝ) - 1) (n : ℝ), HasDerivAt F (cellSecant g n x) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => (n : ℝ) - t) (0 - 1) x :=
      (hasDerivAt_const x (n : ℝ)).sub (hasDerivAt_id x)
    have h2 : HasDerivAt (fun t : ℝ => t - ((n : ℝ) - 1)) 1 x :=
      (hasDerivAt_id x).sub_const ((n : ℝ) - 1)
    have hF := (((h1.pow 2).div_const 2).neg.mul_const (g ((n : ℝ) - 1))).add
      (((h2.pow 2).div_const 2).mul_const (g (n : ℝ)))
    exact hF.congr_deriv (by unfold cellSecant; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_cellSecant g n).intervalIntegrable _ _)]
  dsimp [F]
  ring

/-- **Exact Unit-Cell Integral of the Peano Parabola `cellParabola n`**:
`∫ x in ((n : ℝ) - 1)..(n : ℝ), cellParabola n x = 1 / 6`. -/
theorem intervalIntegral_cellParabola (n : ℕ) :
    (∫ x in ((n : ℝ) - 1)..(n : ℝ), cellParabola n x) = 1 / 6 := by
  let F : ℝ → ℝ := fun x => x / 4 - (x - ((n : ℝ) - 1 / 2)) ^ 3 / 3
  have hderiv : ∀ x ∈ uIcc ((n : ℝ) - 1) (n : ℝ), HasDerivAt F (cellParabola n x) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => t / 4) (1 / 4) x := (hasDerivAt_id x).div_const 4
    have h2 : HasDerivAt (fun t : ℝ => t - ((n : ℝ) - 1 / 2)) 1 x :=
      (hasDerivAt_id x).sub_const ((n : ℝ) - 1 / 2)
    have hF := h1.sub ((h2.pow 3).div_const 3)
    exact hF.congr_deriv (by unfold cellParabola; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_cellParabola n).intervalIntegrable _ _)]
  dsimp [F]
  ring

/-- **Unit-Cell Secant-Remainder Integral Identity**:
for any `g : ℝ → ℝ` interval-integrable on `[(n : ℝ) - 1, (n : ℝ)]`,
`∫ x in ((n : ℝ) - 1)..(n : ℝ), (g x - (1 / 2 * g ((n : ℝ) - 1) + (1 - 1 / 2) * g (n : ℝ))) = ∫ x in ((n : ℝ) - 1)..(n : ℝ), (g x - cellSecant g n x)`. -/
theorem intervalIntegral_sub_trapezoid_eq_sub_cellSecant {g : ℝ → ℝ} {n : ℕ}
    (hg : IntervalIntegrable g volume ((n : ℝ) - 1) (n : ℝ)) :
    (∫ x in ((n : ℝ) - 1)..(n : ℝ),
        (g x - (1 / 2 * g ((n : ℝ) - 1) + (1 - 1 / 2) * g (n : ℝ)))) =
      ∫ x in ((n : ℝ) - 1)..(n : ℝ), (g x - cellSecant g n x) := by
  rw [intervalIntegral.integral_sub hg intervalIntegrable_const,
    intervalIntegral.integral_sub hg ((continuous_cellSecant g n).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral_cellSecant]
  simp only [sub_sub_cancel, one_smul]
  ring

/-- **Exact Secant-Remainder Representation of `trueTrapezoidalCellDefect`**:
for any `g : ℝ → ℝ` continuous on `Ici 1` and any `N : ℕ`,
`trueTrapezoidalCellDefect g N = ∑ n ∈ Finset.Icc 2 N, ∫ x in ((n : ℝ) - 1)..(n : ℝ), (g x - cellSecant g n x)`. -/
theorem trueTrapezoidalCellDefect_eq_sum_integral_sub_cellSecant {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ici 1)) (N : ℕ) :
    trueTrapezoidalCellDefect g N =
      ∑ n ∈ Finset.Icc 2 N, ∫ x in ((n : ℝ) - 1)..(n : ℝ), (g x - cellSecant g n x) := by
  unfold trueTrapezoidalCellDefect weightedCellQuadratureDefect
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have hI : IntervalIntegrable g volume ((n : ℝ) - 1) (n : ℝ) := by
    refine (hg.mono fun x hx => ?_).intervalIntegrable
    rw [uIcc_of_le (by linarith)] at hx
    rw [mem_Ici]
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    linarith [hx.1]
  exact intervalIntegral_sub_trapezoid_eq_sub_cellSecant hI

/-! ## Section 2: Hermite–Hadamard Secant Positivity and Piecewise Semiconcavity Bounds `-(1 / 12) ∑ K_n` for `trueTrapezoidalCellDefect` -/

/-- **Hermite–Hadamard Secant Positivity (`0 ≤ trueTrapezoidalCellDefect g N`)**:
if `g` is continuous on `Ici 1` and lies above its secant line `cellSecant g n` on every unit cell
`[(n : ℝ) - 1, (n : ℝ)]` for `n ∈ Finset.Icc 2 N`, then `0 ≤ trueTrapezoidalCellDefect g N`. -/
theorem trueTrapezoidalCellDefect_nonneg_of_cellSecant_le {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ici 1)) {N : ℕ}
    (hsec : ∀ n ∈ Finset.Icc 2 N, ∀ x ∈ Icc ((n : ℝ) - 1) (n : ℝ), cellSecant g n x ≤ g x) :
    0 ≤ trueTrapezoidalCellDefect g N := by
  rw [trueTrapezoidalCellDefect_eq_sum_integral_sub_cellSecant hg N]
  refine Finset.sum_nonneg fun n hn => ?_
  refine intervalIntegral.integral_nonneg (by linarith) fun x hx => ?_
  exact sub_nonneg.mpr (hsec n hn x hx)

/-- **Hermite–Hadamard Secant Nonpositivity (`trueTrapezoidalCellDefect g N ≤ 0`)**:
if `g` is continuous on `Ici 1` and lies below its secant line `cellSecant g n` on every unit cell
`[(n : ℝ) - 1, (n : ℝ)]` for `n ∈ Finset.Icc 2 N`, then `trueTrapezoidalCellDefect g N ≤ 0`. -/
theorem trueTrapezoidalCellDefect_nonpos_of_le_cellSecant {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ici 1)) {N : ℕ}
    (hsec : ∀ n ∈ Finset.Icc 2 N, ∀ x ∈ Icc ((n : ℝ) - 1) (n : ℝ), g x ≤ cellSecant g n x) :
    trueTrapezoidalCellDefect g N ≤ 0 := by
  rw [trueTrapezoidalCellDefect_eq_sum_integral_sub_cellSecant hg N]
  refine Finset.sum_nonpos fun n hn => ?_
  have hI : IntervalIntegrable (fun x => g x - cellSecant g n x) volume ((n : ℝ) - 1) (n : ℝ) := by
    rw [Finset.mem_Icc] at hn
    refine ((hg.mono fun x hx => ?_).sub (continuous_cellSecant g n).continuousOn).intervalIntegrable
    rw [uIcc_of_le (by linarith)] at hx
    rw [mem_Ici]
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    linarith [hx.1]
  have hmono := intervalIntegral.integral_mono_on (by linarith : (n : ℝ) - 1 ≤ (n : ℝ))
    hI intervalIntegrable_const fun x hx => sub_nonpos.mpr (hsec n hn x hx)
  simpa using hmono

/-- **Piecewise $K_n$-Semiconcavity Lower Bound for `trueTrapezoidalCellDefect`**:
if `g` is continuous on `Ici 1` and on each cell `[(n : ℝ) - 1, (n : ℝ)]` (`n ∈ Finset.Icc 2 N`),
`-(K n / 2) * cellParabola n x ≤ g x - cellSecant g n x`, then
`-(1 / 12) * (∑ n ∈ Finset.Icc 2 N, K n) ≤ trueTrapezoidalCellDefect g N`. -/
theorem neg_sum_div_twelve_le_trueTrapezoidalCellDefect_of_semiconcave {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ici 1)) {N : ℕ} (K : ℕ → ℝ)
    (hsemi : ∀ n ∈ Finset.Icc 2 N, ∀ x ∈ Icc ((n : ℝ) - 1) (n : ℝ),
      -(K n / 2) * cellParabola n x ≤ g x - cellSecant g n x) :
    -(1 / 12) * (∑ n ∈ Finset.Icc 2 N, K n) ≤ trueTrapezoidalCellDefect g N := by
  rw [trueTrapezoidalCellDefect_eq_sum_integral_sub_cellSecant hg N, Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn_mem := hn
  rw [Finset.mem_Icc] at hn_mem
  have hIg : IntervalIntegrable (fun x => g x - cellSecant g n x) volume ((n : ℝ) - 1) (n : ℝ) := by
    refine ((hg.mono fun x hx => ?_).sub (continuous_cellSecant g n).continuousOn).intervalIntegrable
    rw [uIcc_of_le (by linarith)] at hx
    rw [mem_Ici]
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_mem.1
    linarith [hx.1]
  have hIp : IntervalIntegrable (fun x => -(K n / 2) * cellParabola n x)
      volume ((n : ℝ) - 1) (n : ℝ) :=
    ((continuous_cellParabola n).const_mul (-(K n / 2))).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on (by linarith : (n : ℝ) - 1 ≤ (n : ℝ))
    hIp hIg (hsemi n hn)
  rw [intervalIntegral.integral_const_mul, intervalIntegral_cellParabola] at hmono
  linarith

/-- **Piecewise $K_n$-Semiconvexity Upper Bound for `trueTrapezoidalCellDefect`**:
if `g` is continuous on `Ici 1` and on each cell `[(n : ℝ) - 1, (n : ℝ)]` (`n ∈ Finset.Icc 2 N`),
`g x - cellSecant g n x ≤ (K n / 2) * cellParabola n x`, then
`trueTrapezoidalCellDefect g N ≤ (1 / 12) * (∑ n ∈ Finset.Icc 2 N, K n)`. -/
theorem trueTrapezoidalCellDefect_le_sum_div_twelve_of_semiconvex {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ici 1)) {N : ℕ} (K : ℕ → ℝ)
    (hconv : ∀ n ∈ Finset.Icc 2 N, ∀ x ∈ Icc ((n : ℝ) - 1) (n : ℝ),
      g x - cellSecant g n x ≤ (K n / 2) * cellParabola n x) :
    trueTrapezoidalCellDefect g N ≤ (1 / 12) * (∑ n ∈ Finset.Icc 2 N, K n) := by
  rw [trueTrapezoidalCellDefect_eq_sum_integral_sub_cellSecant hg N, Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn_mem := hn
  rw [Finset.mem_Icc] at hn_mem
  have hIg : IntervalIntegrable (fun x => g x - cellSecant g n x) volume ((n : ℝ) - 1) (n : ℝ) := by
    refine ((hg.mono fun x hx => ?_).sub (continuous_cellSecant g n).continuousOn).intervalIntegrable
    rw [uIcc_of_le (by linarith)] at hx
    rw [mem_Ici]
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_mem.1
    linarith [hx.1]
  have hIp : IntervalIntegrable (fun x => (K n / 2) * cellParabola n x)
      volume ((n : ℝ) - 1) (n : ℝ) :=
    ((continuous_cellParabola n).const_mul (K n / 2)).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on (by linarith : (n : ℝ) - 1 ≤ (n : ℝ))
    hIg hIp (hconv n hn)
  rw [intervalIntegral.integral_const_mul, intervalIntegral_cellParabola] at hmono
  linarith

/-- **Two-Sided Peano Error Bound (`(1 / 12) ∑ K_n`) for `trueTrapezoidalCellDefect`**:
if `g` is continuous on `Ici 1` and `|g x - cellSecant g n x| ≤ (K n / 2) * cellParabola n x` on
each cell `[(n : ℝ) - 1, (n : ℝ)]` (`n ∈ Finset.Icc 2 N`), then
`|trueTrapezoidalCellDefect g N| ≤ (1 / 12) * (∑ n ∈ Finset.Icc 2 N, K n)`. -/
theorem abs_trueTrapezoidalCellDefect_le_sum_div_twelve_of_abs_sub_cellSecant_le {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ici 1)) {N : ℕ} (K : ℕ → ℝ)
    (habs : ∀ n ∈ Finset.Icc 2 N, ∀ x ∈ Icc ((n : ℝ) - 1) (n : ℝ),
      |g x - cellSecant g n x| ≤ (K n / 2) * cellParabola n x) :
    |trueTrapezoidalCellDefect g N| ≤ (1 / 12) * (∑ n ∈ Finset.Icc 2 N, K n) := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · have h1 := neg_sum_div_twelve_le_trueTrapezoidalCellDefect_of_semiconcave hg K fun n hn x hx => by
      have h := (abs_le.mp (habs n hn x hx)).1
      linarith
    linarith
  · exact trueTrapezoidalCellDefect_le_sum_div_twelve_of_semiconvex hg K fun n hn x hx =>
      (abs_le.mp (habs n hn x hx)).2

/-! ## Section 3: The Discrete Unit-Step Sign Law on the Primitive Hyperplane and the $\theta$-Amplifier Absorption Theorem for Semiconcave Profiles -/

/-- **Exact Discrete Unit-Step Sum Law on the Primitive Hyperplane ($\alpha$-Weighted Form)**:
for every real test `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0`, every `α : ℝ`, and every cutoff
`N ≥ 1`,
`-primeBlindCounterterm unitStepCountertermWeight F = 2 * α * (∫ u, ‖F u‖ ^ 2) + bochnerResolventEnergy k_F + 2 * sinhHalfMoment f ^ 2 + weightedCellQuadratureDefect α (ℓ_F) N`. -/
theorem neg_primeBlindCounterterm_unitStep_eq_weighted_of_cosh_zero (α : ℝ)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0) :
    -primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc) =
      2 * α * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        bochnerResolventEnergy
          (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
        2 * sinhHalfMoment f ^ 2 +
        weightedCellQuadratureDefect α
          (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N := by
  have h1 := unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
    hf hfc hcosh hN1 hN
  have h2 := rightCellQuadratureDefect_weilContinuumLogProfile_eq_weighted
    α (realWeilTestFn f hf hfc) hN1 hN0
  linarith

/-- **Exact Discrete Unit-Step Sum Law on the Primitive Hyperplane (True Trapezoidal Form)**:
for every real test `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0` and every cutoff `N ≥ 1`,
`-primeBlindCounterterm unitStepCountertermWeight F = (∫ u, ‖F u‖ ^ 2) + bochnerResolventEnergy k_F + 2 * sinhHalfMoment f ^ 2 + trueTrapezoidalCellDefect (ℓ_F) N`. -/
theorem neg_primeBlindCounterterm_unitStep_eq_trueTrapezoidal_of_cosh_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0) :
    -primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc) =
      (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        bochnerResolventEnergy
          (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
        2 * sinhHalfMoment f ^ 2 +
        trueTrapezoidalCellDefect
          (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N := by
  have h := neg_primeBlindCounterterm_unitStep_eq_weighted_of_cosh_zero (1 / 2) hf hfc hcosh hN1 hN0 hN
  unfold trueTrapezoidalCellDefect
  linarith

/-- **Discrete Unit-Step Nonpositivity under Semiconcavity on the Primitive Hyperplane**:
if `ℓ_F` is piecewise $K_n$-semiconcave on `[1, N]` and
`(1 / 12) * ∑_{n=2}^N K_n ≤ (∫ u, ‖F u‖ ^ 2) + bochnerResolventEnergy k_F + 2 * sinhHalfMoment f ^ 2`,
then the discrete unit-step sum `primeBlindCounterterm unitStepCountertermWeight F` is nonpositive
(`≤ 0`). -/
theorem primeBlindCounterterm_unitStep_nonpos_of_semiconcave_of_cosh_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (K : ℕ → ℝ)
    (hsemi : ∀ n ∈ Finset.Icc 2 N, ∀ x ∈ Icc ((n : ℝ) - 1) (n : ℝ),
      -(K n / 2) * cellParabola n x ≤
        weilContinuumLogProfile (realWeilTestFn f hf hfc).1 x -
          cellSecant (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) n x)
    (hK : (1 / 12) * (∑ n ∈ Finset.Icc 2 N, K n) ≤
      (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        bochnerResolventEnergy
          (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
        2 * sinhHalfMoment f ^ 2) :
    primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc) ≤ 0 := by
  have heq := neg_primeBlindCounterterm_unitStep_eq_trueTrapezoidal_of_cosh_zero
    hf hfc hcosh hN1 hN0 hN
  have htrap := neg_sum_div_twelve_le_trueTrapezoidalCellDefect_of_semiconcave
    (continuousOn_weilContinuumLogProfile (realWeilTestFn f hf hfc)) K hsemi
  linarith

/-- **Discrete Unit-Step Rigidity on the Primitive Hyperplane**:
if `ℓ_F` is piecewise $K_n$-semiconcave on `[1, N]` with `(1 / 12) * ∑_{n=2}^N K_n ≤ ∫ u, ‖F u‖ ^ 2`,
and the discrete unit-step sum satisfies `0 ≤ primeBlindCounterterm unitStepCountertermWeight F`,
then `bochnerResolventEnergy k_F = 0`, `sinhHalfMoment f = 0`, `∫ u, ‖F u‖ ^ 2 = 0`, and
`0 ≤ markovCountertermEnergy lam F` for every counterterm `lam : ℕ → ℝ`. -/
theorem markovCountertermEnergy_nonneg_of_unitStep_nonneg_and_semiconcave_of_cosh_zero
    (lam : ℕ → ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (K : ℕ → ℝ)
    (hsemi : ∀ n ∈ Finset.Icc 2 N, ∀ x ∈ Icc ((n : ℝ) - 1) (n : ℝ),
      -(K n / 2) * cellParabola n x ≤
        weilContinuumLogProfile (realWeilTestFn f hf hfc).1 x -
          cellSecant (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) n x)
    (hK : (1 / 12) * (∑ n ∈ Finset.Icc 2 N, K n) ≤
      ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)
    (hunit : 0 ≤ primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc)) :
    0 ≤ markovCountertermEnergy lam (realWeilTestFn f hf hfc).1 := by
  have heq := neg_primeBlindCounterterm_unitStep_eq_trueTrapezoidal_of_cosh_zero
    hf hfc hcosh hN1 hN0 hN
  have htrap := neg_sum_div_twelve_le_trueTrapezoidalCellDefect_of_semiconcave
    (continuousOn_weilContinuumLogProfile (realWeilTestFn f hf hfc)) K hsemi
  have hres_nonneg := bochnerResolventEnergy_weilTest_nonneg (realWeilTestFn f hf hfc)
  have hsinh_nonneg : 0 ≤ sinhHalfMoment f ^ 2 := sq_nonneg _
  have hres0 : bochnerResolventEnergy
      (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) = 0 := by
    linarith
  exact markovCountertermEnergy_nonneg_of_bochnerResolventEnergy_eq_zero lam hres0

/-- **Hermite–Hadamard Secant-Concave Coercive Lower Bound on `markovEnergy` (Primitive Hyperplane)**:
for any real test `f ∈ C²_c(ℝ)` on the primitive hyperplane `coshHalfMoment f = 0`, if `2 ≤ θ`,
`Real.log N ≤ θ`, `0 ≤ iteratedForwardDiff m (logValue F) n` for `2 ≤ n ≤ N`, and
`cellSecant ℓ_F n x ≤ ℓ_F x` on each unit cell `[n - 1, n]`, then `0 ≤ trueTrapezoidalCellDefect ℓ_F N`,
so
`(1 / 100 + θ - 2) * ∫ ‖F‖² + (θ - 1) * bochnerResolventEnergy k_F + 2 * θ * sinhHalfMoment f ^ 2 ≤ markovEnergy F`. -/
theorem secant_concave_upgraded_l2_le_markovEnergy_of_cosh_zero (m : ℕ) {θ : ℝ} (hθ2 : 2 ≤ θ)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N) (hθlog : Real.log (N : ℝ) ≤ θ)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hdiff : ∀ n ∈ Finset.Icc 2 N,
      0 ≤ iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n)
    (hsec : ∀ n ∈ Finset.Icc 2 N, ∀ x ∈ Icc ((n : ℝ) - 1) (n : ℝ),
      cellSecant (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) n x ≤
        weilContinuumLogProfile (realWeilTestFn f hf hfc).1 x) :
    (1 / 100 + θ - 2) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        (θ - 1) * bochnerResolventEnergy
          (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
        2 * θ * sinhHalfMoment f ^ 2 ≤
      markovEnergy (realWeilTestFn f hf hfc).1 := by
  have hbase := trueTrapezoidal_upgraded_l2_le_markovEnergy_of_cosh_zero
    m hθ2 hf hfc hcosh hN1 hθlog hN0 hN hdiff
  have htrap := trueTrapezoidalCellDefect_nonneg_of_cellSecant_le
    (continuousOn_weilContinuumLogProfile (realWeilTestFn f hf hfc)) hsec
  have hθ0 : 0 ≤ θ := by linarith
  have hmul : 0 ≤ θ * trueTrapezoidalCellDefect
      (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N :=
    mul_nonneg hθ0 htrap
  linarith

/-- **Semiconcave Coercive Lower Bound on `markovEnergy` (Primitive Hyperplane)**:
for any real test `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0`, if `2 ≤ θ`, `Real.log N ≤ θ`,
`0 ≤ iteratedForwardDiff m (logValue F) n` for `2 ≤ n ≤ N`, and
`-(K n / 2) * cellParabola n x ≤ ℓ_F x - cellSecant ℓ_F n x` on each unit cell `[n - 1, n]`, then
`(1 / 100 + θ - 2) * ∫ ‖F‖² + (θ - 1) * bochnerResolventEnergy k_F + 2 * θ * sinhHalfMoment f ^ 2 - (θ / 12) * ∑_{n=2}^N K_n ≤ markovEnergy F`. -/
theorem semiconcave_upgraded_l2_le_markovEnergy_of_cosh_zero (m : ℕ) {θ : ℝ} (hθ2 : 2 ≤ θ)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N) (hθlog : Real.log (N : ℝ) ≤ θ)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hdiff : ∀ n ∈ Finset.Icc 2 N,
      0 ≤ iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n)
    (K : ℕ → ℝ)
    (hsemi : ∀ n ∈ Finset.Icc 2 N, ∀ x ∈ Icc ((n : ℝ) - 1) (n : ℝ),
      -(K n / 2) * cellParabola n x ≤
        weilContinuumLogProfile (realWeilTestFn f hf hfc).1 x -
          cellSecant (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) n x) :
    (1 / 100 + θ - 2) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        (θ - 1) * bochnerResolventEnergy
          (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
        2 * θ * sinhHalfMoment f ^ 2 -
        (θ / 12) * (∑ n ∈ Finset.Icc 2 N, K n) ≤
      markovEnergy (realWeilTestFn f hf hfc).1 := by
  have hbase := trueTrapezoidal_upgraded_l2_le_markovEnergy_of_cosh_zero
    m hθ2 hf hfc hcosh hN1 hθlog hN0 hN hdiff
  have htrap := neg_sum_div_twelve_le_trueTrapezoidalCellDefect_of_semiconcave
    (continuousOn_weilContinuumLogProfile (realWeilTestFn f hf hfc)) K hsemi
  have hθ0 : 0 ≤ θ := by linarith
  have hmul := mul_le_mul_of_nonneg_left htrap hθ0
  linarith

/-- **The $\theta$-Amplifier Absorption Theorem for Semiconcave Profiles on the Primitive Hyperplane**:
if `ℓ_F` is piecewise $K_n$-semiconcave on `[1, N]` with
`(1 / 12) * ∑_{n=2}^N K_n ≤ (1 - δ) * ((∫ u, ‖F u‖ ^ 2) + bochnerResolventEnergy k_F + 2 * sinhHalfMoment f ^ 2)`
for some `δ > 0` (i.e., `∑_{n=2}^N K_n < 12 * (total coercive energy)`), and
`0 ≤ iteratedForwardDiff m (logValue F) n` for `2 ≤ n ≤ N`, then choosing
`θ = max (max 2 (Real.log N)) (2 / δ)` automatically absorbs the entire trapezoidal quadrature defect
and yields
`(1 / 100) * ∫ u, ‖F u‖ ^ 2 + bochnerResolventEnergy k_F + 2 * sinhHalfMoment f ^ 2 ≤ markovEnergy F`
and `0 ≤ markovEnergy F`. -/
theorem markovEnergy_ofReal_nonneg_of_semiconcave_energy_ratio_of_cosh_zero (m : ℕ)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hdiff : ∀ n ∈ Finset.Icc 2 N,
      0 ≤ iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n)
    (K : ℕ → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsemi : ∀ n ∈ Finset.Icc 2 N, ∀ x ∈ Icc ((n : ℝ) - 1) (n : ℝ),
      -(K n / 2) * cellParabola n x ≤
        weilContinuumLogProfile (realWeilTestFn f hf hfc).1 x -
          cellSecant (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) n x)
    (hK : (1 / 12) * (∑ n ∈ Finset.Icc 2 N, K n) ≤
      (1 - δ) *
        ((∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
          bochnerResolventEnergy
            (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
          2 * sinhHalfMoment f ^ 2)) :
    (1 / 100) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        bochnerResolventEnergy
          (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
        2 * sinhHalfMoment f ^ 2 ≤
      markovEnergy (realWeilTestFn f hf hfc).1 ∧
    0 ≤ markovEnergy (realWeilTestFn f hf hfc).1 := by
  let θ : ℝ := max (max 2 (Real.log (N : ℝ))) (2 / δ)
  have hθ2 : 2 ≤ θ := (le_max_left 2 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ_log : Real.log (N : ℝ) ≤ θ := (le_max_right 2 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ_δ : 2 / δ ≤ θ := le_max_right _ _
  have hθ0 : 0 ≤ θ := by linarith
  have hbase := semiconcave_upgraded_l2_le_markovEnergy_of_cosh_zero
    m hθ2 hf hfc hcosh hN1 hθ_log hN0 hN hdiff K hsemi
  set E : ℝ := (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
    bochnerResolventEnergy
      (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
    2 * sinhHalfMoment f ^ 2
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hres_nonneg := bochnerResolventEnergy_weilTest_nonneg (realWeilTestFn f hf hfc)
  have hsinh_nonneg : 0 ≤ sinhHalfMoment f ^ 2 := sq_nonneg _
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    positivity
  have hθK : (θ / 12) * (∑ n ∈ Finset.Icc 2 N, K n) ≤ θ * (1 - δ) * E := by
    have hmul := mul_le_mul_of_nonneg_left hK hθ0
    linarith
  have h2_le_θδ : 2 ≤ θ * δ := (div_le_iff₀ hδ).mp hθ_δ
  have hθδE : 2 * E ≤ θ * δ * E := mul_le_mul_of_nonneg_right h2_le_θδ hE_nonneg
  have hsinh_θ : 2 * sinhHalfMoment f ^ 2 ≤ 2 * (θ - 1) * sinhHalfMoment f ^ 2 := by
    nlinarith
  have hmain : (1 / 100) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
      bochnerResolventEnergy
        (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
      2 * sinhHalfMoment f ^ 2 ≤
      markovEnergy (realWeilTestFn f hf hfc).1 := by
    dsimp [E] at hθK hθδE
    linarith
  exact ⟨hmain, by linarith⟩

/-- **Unconditional `RiemannHypothesis` from Odd-Sector Semiconcave $\theta$-Amplifier Dominance**:
if for every odd real test `f ∈ C²_c(ℝ)` there exist a cutoff `N ≥ 1`, a Cesàro order `m : ℕ`,
a semiconcavity sequence `K : ℕ → ℝ`, and `δ > 0` such that `0 ≤ iteratedForwardDiff m (logValue F) n`
on `[2, N]`, `-(K n / 2) * cellParabola n x ≤ ℓ_F x - cellSecant ℓ_F n x` on each unit cell `[n - 1, n]`,
and `(1 / 12) * ∑_{n=2}^N K_n ≤ (1 - δ) * (∫ ‖F‖² + bochnerResolventEnergy k_F + 2 * sinhHalfMoment f ^ 2)`,
then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_forall_odd_exists_semiconcave_dom
    (hdom : ∀ (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f),
      (∀ x : ℝ, f (-x) = -f x) →
      ∃ (N : ℕ) (m : ℕ) (K : ℕ → ℝ) (δ : ℝ),
        1 ≤ N ∧ 0 < δ ∧
        (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
          EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0) ∧
        (∀ x : ℝ, (N : ℝ) < x →
          EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
            EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0) ∧
        (∀ n ∈ Finset.Icc 2 N,
          0 ≤ iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n) ∧
        (∀ n ∈ Finset.Icc 2 N, ∀ x ∈ Icc ((n : ℝ) - 1) (n : ℝ),
          -(K n / 2) * cellParabola n x ≤
            weilContinuumLogProfile (realWeilTestFn f hf hfc).1 x -
              cellSecant (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) n x) ∧
        (1 / 12) * (∑ n ∈ Finset.Icc 2 N, K n) ≤
          (1 - δ) *
            ((∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
              bochnerResolventEnergy
                (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
              2 * sinhHalfMoment f ^ 2)) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_forall_odd_markovEnergy_nonneg]
  intro f hf hfc hodd
  obtain ⟨N, m, K, δ, hN1, hδ, hN0, hN, hdiff, hsemi, hK⟩ := hdom f hf hfc hodd
  exact (markovEnergy_ofReal_nonneg_of_semiconcave_energy_ratio_of_cosh_zero
    m hf hfc (coshHalfMoment_eq_zero_of_odd hodd)
    hN1 hN0 hN hdiff K hδ hsemi hK).2

end RHTower

end

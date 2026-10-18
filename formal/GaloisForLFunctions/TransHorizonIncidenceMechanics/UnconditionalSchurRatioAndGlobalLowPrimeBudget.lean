import GaloisForLFunctions.TransHorizonIncidenceMechanics.OddProfileCollarToContinuumArchimedeanBridge
import GaloisForLFunctions.RHTower.RiemannKernelSharpLogDerivative

/-!
# Unconditional Horizon-Uniform Schur Ratio Bound and Global Low-Prime Budget (`UnconditionalSchurRatioAndGlobalLowPrimeBudget`)

This module completes the unconditional analytical discharge of the Schur-complement ratio
hypothesis `hκ` in `OddProfileCollarToContinuumArchimedeanBridge.lean` (**Obstacle B** of
`docs/reports/TransHorizonIncidenceMechanics/CHMD-programme.md`) and embeds the per-prime 2D
continuum slices into the single global 2D absorbed archimedean integral on $(0, a) \times (\delta, a)$
and into the half-line archimedean direct-minus-collar energy.

## Mathematical Overview

1. **Pointwise Linear Drop Bounds on `riemannKernelReal` Across Shifted Intervals (§1):**
   - Using the tail logarithmic derivative upper bound $\Theta'(u) \le -\pi e^{2u}\Theta(u)$ on
     $u \ge \frac{1}{2}\log 2$ (`cuspSeries_cuspDeriv_riemannCuspPoly_le`), we prove the linear
     drop lower bound (`riemannKernelReal_sub_ge_linear_of_log_two_half_le`):
     $$\pi e^{2u_1}\,\Theta(u_2)\,(u_2 - u_1) \le \Theta(u_1) - \Theta(u_2)
       \qquad (\tfrac{1}{2}\log 2 \le u_1 \le u_2).$$
   - Using the global logarithmic derivative lower bound $\Theta'(u) \ge -2\pi(e^{2u} + 2)\Theta(u)$
     on $u \ge 0$ (`cuspSeries_cuspDeriv_riemannCuspPoly_ge_sharp`), we prove the linear drop upper
     bound (`riemannKernelReal_sub_le_linear_of_nonneg`):
     $$\Theta(v_1) - \Theta(v_2) \le 2\pi(e^{2v_2} + 2)\,\Theta(v_1)\,(v_2 - v_1)
       \qquad (0 \le v_1 \le v_2).$$
   - For $0 \le t$, $\frac{3}{2}t + \frac{1}{2}\log 2 \le a$, and $x \in [0, t/2]$, the intervals
     $[a - t - x, a - t + x]$ and $[a - x, a + x]$ both have width $2x$ and are separated by the
     gap $(a - x) - (a - t + x) = t - 2x \ge 0$. Since $\Theta$ is antitone on $[0, \infty)$ and
     satisfies the super-exponential tail decay `riemannKernelReal_le_mul_exp`, the factor
     $2\pi x\,\Theta(a - t + x)$ cancels between the upper and lower bounds, while the $a$-dependence
     $e^{2a + t} / e^{2a - 3t} = e^{4t}$ cancels **identically**, yielding both the
     super-exponentially damped drop comparison (`riemannKernelReal_center_drop_le_damped_shifted_drop`)
     and the horizon-uniform drop comparison (`riemannKernelReal_center_drop_le_four_exp_four_shifted_drop`):
     $$\Theta(a - x) - \Theta(a + x) \le 4 e^{4t}\,\bigl(\Theta(a - t - x) - \Theta(a - t + x)\bigr).$$

2. **Unconditional Horizon-Uniform Schur Ratio Bound for `oddProfile a` (§2):**
   - For every $a, t, x \in \mathbb{R}$, parity of $\Theta$ gives the exact decomposition
     (`two_mul_sinh_mul_oddProfile_sub_eq`):
     $$2\sinh(a/2)\bigl(m_a(t + x) - m_a(t - x)\bigr)
       = \bigl(\Theta(a - t - x) - \Theta(a - t + x)\bigr)
         + \bigl(\Theta(a + t - x) - \Theta(a + t + x)\bigr).$$
   - Since $0 \le a + t - x \le a + t + x$, $\Theta(a + t - x) - \Theta(a + t + x) \ge 0$, so
     dividing by $2\sinh(a/2) > 0$ yields the **unconditional, horizon-independent Schur ratio
     theorem** (`oddProfile_le_four_exp_four_mul_sub`):
     $$\forall x \in [0, t/2],\qquad
       m_a(x) \le 4 e^{4t}\,\bigl(m_a(t + x) - m_a(t - x)\bigr),$$
     together with its super-exponentially damped refinement (`oddProfile_le_damped_four_exp_four_mul_sub`).

3. **Unconditional 1-for-1 Collar-Minus-Direct Excess & Full-Line Prime Positivity (§3):**
   - Discharging `hκ` with $\kappa = 4 e^{4t}$ in `OddProfileCollarToContinuumArchimedeanBridge`
     gives the **premise-free** 1-for-1 collar-minus-direct excess bound
     (`integral_oddProfileCollarDiffSq_sub_two_direct_le_sixteen_exp_four_absorbedArchSlice`) and
     the **premise-free** full-line prime shift-jump + 2D continuum positivity law
     (`unconditional_two_mul_integral_Ioi_half_le_fullLine_add_absorbedArchSlice`,
     `unconditional_fullLine_add_absorbedArchSlice_nonneg`).

4. **Global 2D Rectangle Monotonicity & Summed Low-Prime Budget (§4):**
   - We prove monotonicity of `absorbedArchSlice a w δ M y` in the upper cutoff $M$
     (`absorbedArchSlice_mono_right`), bound every per-prime slice integral over
     $(t/2, 3t/2) \times (\delta, t + \delta + L)$ by the single global 2D rectangle integral
     $\int_{y \in (0, a)} \operatorname{absorbedArchSlice}(a, w, \delta, a, y)\,dy$
     (`integral_absorbedArchSlice_Ioo_le_global_Ioo`), bound `absorbedArchSlice` by the half-line
     archimedean direct-minus-collar difference (`absorbedArchSlice_le_arch_direct_sub_collar`),
     and establish the unconditional summed low-prime budget
     (`sum_vonMangoldt_fullLine_add_global_absorbedArchSlice_ge_tail`).
-/

open MeasureTheory Set Filter Topology Real
open scoped BigOperators
noncomputable section

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

open _root_.RHTower _root_.RHTower.CHMDPolar _root_.RHTower.CHMDDoobGraph
open _root_.RHTower.ThetaSourceWard _root_.RHTower.PhiDivisorEnergy

/-! ## Section 1: Pointwise Linear Drop Bounds on `riemannKernelReal` Across Shifted Intervals -/

private theorem hasDerivAt_riemannKernelReal_pos {u : ℝ} (hu : 0 < u) :
    HasDerivAt riemannKernelReal (cuspSeries (cuspDeriv riemannCuspPoly) u) u := by
  have h := hasDerivAt_cuspSeries riemannCuspPoly u
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hu] with x hx
  exact riemannKernelReal_of_nonneg hx.le

/-- **Linear Lower Bound on the Tail Drop of `riemannKernelReal` (`[u₁, u₂] ⊂ [½ log 2, ∞)`):**
For $\frac{1}{2}\log 2 \le u_1 \le u_2$, since $\Theta'(u) \le -\pi e^{2u}\Theta(u) \le -\pi e^{2u_1}\Theta(u_2)$
on $[u_1, u_2]$, the drop $\Theta(u_1) - \Theta(u_2)$ is bounded below by
$\pi e^{2u_1}\Theta(u_2)(u_2 - u_1)$. -/
theorem riemannKernelReal_sub_ge_linear_of_log_two_half_le {u₁ u₂ : ℝ}
    (hu₁ : Real.log 2 / 2 ≤ u₁) (hu : u₁ ≤ u₂) :
    π * Real.exp (2 * u₁) * riemannKernelReal u₂ * (u₂ - u₁) ≤
      riemannKernelReal u₁ - riemannKernelReal u₂ := by
  have hu₁_pos : 0 < u₁ := lt_of_lt_of_le (by positivity) hu₁
  set c : ℝ := π * Real.exp (2 * u₁) * riemannKernelReal u₂
  set h : ℝ → ℝ := fun u => riemannKernelReal u + c * u
  have hderiv : ∀ u, 0 < u → HasDerivAt h
      (cuspSeries (cuspDeriv riemannCuspPoly) u + c) u := by
    intro u hu0
    exact (hasDerivAt_riemannKernelReal_pos hu0).add
      (((hasDerivAt_id u).const_mul c).congr_deriv (by ring))
  have hanti : AntitoneOn h (Icc u₁ u₂) := by
    have hcont : ContinuousOn h (Icc u₁ u₂) :=
      (continuous_riemannKernelReal.add (continuous_const.mul continuous_id)).continuousOn
    apply antitoneOn_of_deriv_nonpos (convex_Icc u₁ u₂) hcont
    · intro u hu_mem
      rw [interior_Icc] at hu_mem
      exact (hderiv u (hu₁_pos.trans hu_mem.1)).differentiableAt.differentiableWithinAt
    · intro u hu_mem
      rw [interior_Icc] at hu_mem
      have hu0 : 0 < u := hu₁_pos.trans hu_mem.1
      rw [(hderiv u hu0).deriv]
      have hD := cuspSeries_cuspDeriv_riemannCuspPoly_le (hu₁.trans hu_mem.1.le)
      rw [← riemannKernelReal_of_nonneg hu0.le] at hD
      have hexp : Real.exp (2 * u₁) ≤ Real.exp (2 * u) :=
        Real.exp_le_exp.mpr (by linarith [hu_mem.1])
      have hθ : riemannKernelReal u₂ ≤ riemannKernelReal u :=
        (strictAntiOn_riemannKernelReal_Ici (mem_Ici.mpr hu0.le)
          (mem_Ici.mpr (hu0.trans hu_mem.2).le) hu_mem.2).le
      have hc_le : c ≤ π * Real.exp (2 * u) * riemannKernelReal u := by
        dsimp [c]
        have h1 : π * Real.exp (2 * u₁) ≤ π * Real.exp (2 * u) :=
          mul_le_mul_of_nonneg_left hexp Real.pi_pos.le
        exact mul_le_mul h1 hθ (riemannKernelReal_pos u₂).le (by positivity)
      linarith
  have hle := hanti (left_mem_Icc.mpr hu) (right_mem_Icc.mpr hu) hu
  dsimp [h] at hle
  linarith

/-- **Linear Upper Bound on the Drop of `riemannKernelReal` (`0 ≤ v₁ ≤ v₂`):**
For $0 \le v_1 \le v_2$, since $\Theta'(u) \ge -2\pi(e^{2u} + 2)\Theta(u) \ge -2\pi(e^{2v_2} + 2)\Theta(v_1)$
on $[v_1, v_2]$, the drop $\Theta(v_1) - \Theta(v_2)$ is bounded above by
$2\pi(e^{2v_2} + 2)\Theta(v_1)(v_2 - v_1)$. -/
theorem riemannKernelReal_sub_le_linear_of_nonneg {v₁ v₂ : ℝ}
    (hv₁ : 0 ≤ v₁) (hv : v₁ ≤ v₂) :
    riemannKernelReal v₁ - riemannKernelReal v₂ ≤
      2 * π * (Real.exp (2 * v₂) + 2) * riemannKernelReal v₁ * (v₂ - v₁) := by
  set C : ℝ := 2 * π * (Real.exp (2 * v₂) + 2) * riemannKernelReal v₁
  set g : ℝ → ℝ := fun u => riemannKernelReal u + C * u
  have hderiv : ∀ u, 0 < u → HasDerivAt g
      (cuspSeries (cuspDeriv riemannCuspPoly) u + C) u := by
    intro u hu0
    exact (hasDerivAt_riemannKernelReal_pos hu0).add
      (((hasDerivAt_id u).const_mul C).congr_deriv (by ring))
  have hmono : MonotoneOn g (Icc v₁ v₂) := by
    have hcont : ContinuousOn g (Icc v₁ v₂) :=
      (continuous_riemannKernelReal.add (continuous_const.mul continuous_id)).continuousOn
    apply monotoneOn_of_deriv_nonneg (convex_Icc v₁ v₂) hcont
    · intro u hu_mem
      rw [interior_Icc] at hu_mem
      exact (hderiv u (lt_of_le_of_lt hv₁ hu_mem.1)).differentiableAt.differentiableWithinAt
    · intro u hu_mem
      rw [interior_Icc] at hu_mem
      have hu0 : 0 < u := lt_of_le_of_lt hv₁ hu_mem.1
      rw [(hderiv u hu0).deriv]
      have hD := cuspSeries_cuspDeriv_riemannCuspPoly_ge_sharp hu0.le
      rw [← riemannKernelReal_of_nonneg hu0.le] at hD
      have hexp : Real.exp (2 * u) + 2 ≤ Real.exp (2 * v₂) + 2 := by
        linarith [Real.exp_le_exp.mpr (show 2 * u ≤ 2 * v₂ by linarith [hu_mem.2])]
      have hθ : riemannKernelReal u ≤ riemannKernelReal v₁ :=
        (strictAntiOn_riemannKernelReal_Ici (mem_Ici.mpr hv₁)
          (mem_Ici.mpr hu0.le) hu_mem.1).le
      have hC_ge : 2 * π * (Real.exp (2 * u) + 2) * riemannKernelReal u ≤ C := by
        dsimp [C]
        have h1 : 2 * π * (Real.exp (2 * u) + 2) ≤ 2 * π * (Real.exp (2 * v₂) + 2) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
        exact mul_le_mul h1 hθ (riemannKernelReal_pos u).le (by positivity)
      linarith
  have hle := hmono (left_mem_Icc.mpr hv) (right_mem_Icc.mpr hv) hv
  dsimp [g] at hle
  linarith

/-- **Super-Exponentially Damped Drop Comparison Across `[a - t - x, a - t + x]` vs. `[a - x, a + x]`:**
For $0 \le t$, $\frac{3}{2}t + \frac{1}{2}\log 2 \le a$, and $x \in [0, t/2]$, the drop of $\Theta$
across $[a - x, a + x]$ is bounded by $4 e^{4t} \exp(-\pi e^{2(a - t + x)}(t - 2x))$ times the drop
of $\Theta$ across $[a - t - x, a - t + x]$. -/
theorem riemannKernelReal_center_drop_le_damped_shifted_drop {a t x : ℝ}
    (ht : 0 ≤ t) (ha : 3 * t / 2 + Real.log 2 / 2 ≤ a) (hx : x ∈ Icc (0 : ℝ) (t / 2)) :
    riemannKernelReal (a - x) - riemannKernelReal (a + x) ≤
      4 * Real.exp (4 * t) *
        Real.exp (-(π * Real.exp (2 * (a - t + x)) * (t - 2 * x))) *
        (riemannKernelReal (a - t - x) - riemannKernelReal (a - t + x)) := by
  have hx0 : 0 ≤ x := hx.1
  have hxt : x ≤ t / 2 := hx.2
  have hu₁_ge : Real.log 2 / 2 ≤ a - t - x := by linarith
  have hu_le : a - t - x ≤ a - t + x := by linarith
  have hv₁_ge : 0 ≤ a - x := by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hv_le : a - x ≤ a + x := by linarith
  have hlow := riemannKernelReal_sub_ge_linear_of_log_two_half_le hu₁_ge hu_le
  rw [show (a - t + x) - (a - t - x) = 2 * x by ring] at hlow
  have hhigh := riemannKernelReal_sub_le_linear_of_nonneg hv₁_ge hv_le
  rw [show (a + x) - (a - x) = 2 * x by ring] at hhigh
  have h2_le_exp : 2 ≤ Real.exp (2 * a + t) := by
    have hlog2 : Real.log 2 ≤ 2 * a + t := by linarith
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (2 * a + t) := Real.exp_le_exp.mpr hlog2
  have hexp_v₂ : Real.exp (2 * (a + x)) + 2 ≤ 2 * Real.exp (2 * a + t) := by
    have h1 : Real.exp (2 * (a + x)) ≤ Real.exp (2 * a + t) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  have hhigh' : riemannKernelReal (a - x) - riemannKernelReal (a + x) ≤
      4 * π * Real.exp (2 * a + t) * riemannKernelReal (a - x) * (2 * x) := by
    have hmul : 2 * π * (Real.exp (2 * (a + x)) + 2) * riemannKernelReal (a - x) * (2 * x) ≤
        2 * π * (2 * Real.exp (2 * a + t)) * riemannKernelReal (a - x) * (2 * x) := by
      have hθ0 : 0 ≤ riemannKernelReal (a - x) * (2 * x) :=
        mul_nonneg (riemannKernelReal_pos _).le (by linarith)
      have hπ0 : 0 ≤ 2 * π := by positivity
      calc 2 * π * (Real.exp (2 * (a + x)) + 2) * riemannKernelReal (a - x) * (2 * x)
          = (2 * π) * (Real.exp (2 * (a + x)) + 2) * (riemannKernelReal (a - x) * (2 * x)) := by ring
        _ ≤ (2 * π) * (2 * Real.exp (2 * a + t)) * (riemannKernelReal (a - x) * (2 * x)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp_v₂ hπ0) hθ0
        _ = _ := by ring
    linarith
  have hexp_u₁ : Real.exp (2 * a - 3 * t) ≤ Real.exp (2 * (a - t - x)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hlow' : π * Real.exp (2 * a - 3 * t) * riemannKernelReal (a - t + x) * (2 * x) ≤
      riemannKernelReal (a - t - x) - riemannKernelReal (a - t + x) := by
    have hθ0 : 0 ≤ riemannKernelReal (a - t + x) * (2 * x) :=
      mul_nonneg (riemannKernelReal_pos _).le (by linarith)
    have hmul : π * Real.exp (2 * a - 3 * t) * (riemannKernelReal (a - t + x) * (2 * x)) ≤
        π * Real.exp (2 * (a - t - x)) * (riemannKernelReal (a - t + x) * (2 * x)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp_u₁ Real.pi_pos.le) hθ0
    linarith
  have hdamp := riemannKernelReal_le_mul_exp (hu₁_ge.trans hu_le) (show a - t + x ≤ a - x by linarith)
  rw [show (a - x) - (a - t + x) = t - 2 * x by ring] at hdamp
  set E := Real.exp (-(π * Real.exp (2 * (a - t + x)) * (t - 2 * x)))
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hexp_id : 4 * Real.exp (2 * a + t) = 4 * Real.exp (4 * t) * Real.exp (2 * a - 3 * t) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  calc riemannKernelReal (a - x) - riemannKernelReal (a + x)
      ≤ 4 * π * Real.exp (2 * a + t) * riemannKernelReal (a - x) * (2 * x) := hhigh'
    _ ≤ 4 * π * Real.exp (2 * a + t) * (riemannKernelReal (a - t + x) * E) * (2 * x) := by
        have hpos : 0 ≤ 4 * π * Real.exp (2 * a + t) * (2 * x) := by positivity
        calc 4 * π * Real.exp (2 * a + t) * riemannKernelReal (a - x) * (2 * x)
            = (4 * π * Real.exp (2 * a + t) * (2 * x)) * riemannKernelReal (a - x) := by ring
          _ ≤ (4 * π * Real.exp (2 * a + t) * (2 * x)) * (riemannKernelReal (a - t + x) * E) :=
              mul_le_mul_of_nonneg_left hdamp hpos
          _ = _ := by ring
    _ = (4 * Real.exp (4 * t) * E) *
          (π * Real.exp (2 * a - 3 * t) * riemannKernelReal (a - t + x) * (2 * x)) := by
        calc 4 * π * Real.exp (2 * a + t) * (riemannKernelReal (a - t + x) * E) * (2 * x)
            = (4 * Real.exp (2 * a + t)) * E * π * riemannKernelReal (a - t + x) * (2 * x) := by ring
          _ = (4 * Real.exp (4 * t) * Real.exp (2 * a - 3 * t)) * E * π *
                riemannKernelReal (a - t + x) * (2 * x) := by rw [hexp_id]
          _ = _ := by ring
    _ ≤ (4 * Real.exp (4 * t) * E) *
          (riemannKernelReal (a - t - x) - riemannKernelReal (a - t + x)) :=
        mul_le_mul_of_nonneg_left hlow' (by positivity)

/-- **Horizon-Uniform Drop Comparison (`[a - x, a + x]` vs. `[a - t - x, a - t + x]`):**
For $0 \le t$, $\frac{3}{2}t + \frac{1}{2}\log 2 \le a$, and $x \in [0, t/2]$,
$$\Theta(a - x) - \Theta(a + x) \le 4 e^{4t}\,\bigl(\Theta(a - t - x) - \Theta(a - t + x)\bigr).$$ -/
theorem riemannKernelReal_center_drop_le_four_exp_four_shifted_drop {a t x : ℝ}
    (ht : 0 ≤ t) (ha : 3 * t / 2 + Real.log 2 / 2 ≤ a) (hx : x ∈ Icc (0 : ℝ) (t / 2)) :
    riemannKernelReal (a - x) - riemannKernelReal (a + x) ≤
      4 * Real.exp (4 * t) *
        (riemannKernelReal (a - t - x) - riemannKernelReal (a - t + x)) := by
  have hdamp := riemannKernelReal_center_drop_le_damped_shifted_drop ht ha hx
  have hexp_le_one : Real.exp (-(π * Real.exp (2 * (a - t + x)) * (t - 2 * x))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have h1 : 0 ≤ t - 2 * x := by linarith [hx.2]
    have h2 : 0 ≤ π * Real.exp (2 * (a - t + x)) * (t - 2 * x) := by positivity
    linarith
  have hdiff_nonneg : 0 ≤ riemannKernelReal (a - t - x) - riemannKernelReal (a - t + x) := by
    have hu₁ : 0 ≤ a - t - x := by linarith [hx.1, hx.2, Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    have hu_le : a - t - x ≤ a - t + x := by linarith [hx.1]
    exact sub_nonneg.mpr (strictAntiOn_riemannKernelReal_Ici.antitoneOn
      (mem_Ici.mpr hu₁) (mem_Ici.mpr (hu₁.trans hu_le)) hu_le)
  calc riemannKernelReal (a - x) - riemannKernelReal (a + x)
      ≤ 4 * Real.exp (4 * t) *
          Real.exp (-(π * Real.exp (2 * (a - t + x)) * (t - 2 * x))) *
          (riemannKernelReal (a - t - x) - riemannKernelReal (a - t + x)) := hdamp
    _ ≤ 4 * Real.exp (4 * t) * 1 *
          (riemannKernelReal (a - t - x) - riemannKernelReal (a - t + x)) := by
        refine mul_le_mul_of_nonneg_right ?_ hdiff_nonneg
        exact mul_le_mul_of_nonneg_left hexp_le_one (by positivity)
    _ = 4 * Real.exp (4 * t) *
          (riemannKernelReal (a - t - x) - riemannKernelReal (a - t + x)) := by ring

/-! ## Section 2: Unconditional Horizon-Uniform Schur Ratio Bound for `oddProfile a` -/

/-- **Two-Channel Decomposition of `2 sinh(a/2) (oddProfile a (t + x) - oddProfile a (t - x))`:**
For all $a \ne 0$ and $t, x \in \mathbb{R}$,
$$2\sinh(a/2)\bigl(m_a(t + x) - m_a(t - x)\bigr)
  = \bigl(\Theta(a - t - x) - \Theta(a - t + x)\bigr)
    + \bigl(\Theta(a + t - x) - \Theta(a + t + x)\bigr).$$ -/
theorem two_mul_sinh_mul_oddProfile_sub_eq {a : ℝ} (ha : a ≠ 0) (t x : ℝ) :
    2 * Real.sinh (a / 2) * (oddProfile a (t + x) - oddProfile a (t - x)) =
      (riemannKernelReal (a - t - x) - riemannKernelReal (a - t + x)) +
        (riemannKernelReal (a + t - x) - riemannKernelReal (a + t + x)) := by
  have hsh : 2 * Real.sinh (a / 2) ≠ 0 :=
    mul_ne_zero (by norm_num) (Real.sinh_ne_zero.mpr (div_ne_zero ha (by norm_num)))
  unfold oddProfile
  rw [mul_sub, mul_div_cancel₀ _ hsh, mul_div_cancel₀ _ hsh,
    show t + x - a = -(a - t - x) by ring,
    show t - x - a = -(a - t + x) by ring,
    WeilExcess.riemannKernelReal_neg, WeilExcess.riemannKernelReal_neg,
    show t + x + a = a + t + x by ring,
    show t - x + a = a + t - x by ring]
  ring

theorem two_mul_sinh_mul_oddProfile_eq {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    2 * Real.sinh (a / 2) * oddProfile a x =
      riemannKernelReal (a - x) - riemannKernelReal (a + x) := by
  have hsh : 2 * Real.sinh (a / 2) ≠ 0 :=
    mul_ne_zero (by norm_num) (Real.sinh_ne_zero.mpr (div_ne_zero ha (by norm_num)))
  unfold oddProfile
  rw [mul_div_cancel₀ _ hsh, show x - a = -(a - x) by ring,
    WeilExcess.riemannKernelReal_neg, show x + a = a + x by ring]

/-- **Lower Bound on `2 sinh(a/2) (oddProfile a (t + x) - oddProfile a (t - x))`:**
For $0 \le t$, $\frac{3}{2}t \le a$ ($a > 0$), and $x \in [0, t/2]$, since
$0 \le a + t - x \le a + t + x$, the far drop $\Theta(a + t - x) - \Theta(a + t + x)$ is
non-negative, so
$$\Theta(a - t - x) - \Theta(a - t + x) \le 2\sinh(a/2)\bigl(m_a(t + x) - m_a(t - x)\bigr).$$ -/
theorem riemannKernelReal_shifted_drop_le_two_mul_sinh_oddProfile_sub {a t x : ℝ}
    (ha : 0 < a) (ht : 0 ≤ t) (hx : x ∈ Icc (0 : ℝ) (t / 2)) :
    riemannKernelReal (a - t - x) - riemannKernelReal (a - t + x) ≤
      2 * Real.sinh (a / 2) * (oddProfile a (t + x) - oddProfile a (t - x)) := by
  rw [two_mul_sinh_mul_oddProfile_sub_eq ha.ne' t x]
  have hfar : 0 ≤ riemannKernelReal (a + t - x) - riemannKernelReal (a + t + x) := by
    have h1 : 0 ≤ a + t - x := by linarith [hx.2]
    have h2 : a + t - x ≤ a + t + x := by linarith [hx.1]
    exact sub_nonneg.mpr (strictAntiOn_riemannKernelReal_Ici.antitoneOn
      (mem_Ici.mpr h1) (mem_Ici.mpr (h1.trans h2)) h2)
  linarith

/-- **Super-Exponentially Damped Unconditional Schur Ratio Bound for `oddProfile a`:**
For $0 \le t$, $\frac{3}{2}t + \frac{1}{2}\log 2 \le a$, and $x \in [0, t/2]$,
$$m_a(x) \le 4 e^{4t}\,\exp\bigl(-\pi e^{2(a - t + x)}(t - 2x)\bigr)\,\bigl(m_a(t + x) - m_a(t - x)\bigr).$$ -/
theorem oddProfile_le_damped_four_exp_four_mul_sub {a t x : ℝ}
    (ht : 0 ≤ t) (ha : 3 * t / 2 + Real.log 2 / 2 ≤ a) (hx : x ∈ Icc (0 : ℝ) (t / 2)) :
    oddProfile a x ≤
      4 * Real.exp (4 * t) *
        Real.exp (-(π * Real.exp (2 * (a - t + x)) * (t - 2 * x))) *
        (oddProfile a (t + x) - oddProfile a (t - x)) := by
  have ha_pos : 0 < a := by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hsh : 0 < 2 * Real.sinh (a / 2) :=
    mul_pos (by norm_num) (Real.sinh_pos_iff.mpr (half_pos ha_pos))
  have h1 := two_mul_sinh_mul_oddProfile_eq ha_pos.ne' x
  have h2 := riemannKernelReal_center_drop_le_damped_shifted_drop ht ha hx
  have h3 := riemannKernelReal_shifted_drop_le_two_mul_sinh_oddProfile_sub ha_pos ht hx
  set K := 4 * Real.exp (4 * t) * Real.exp (-(π * Real.exp (2 * (a - t + x)) * (t - 2 * x)))
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hmul : 2 * Real.sinh (a / 2) * oddProfile a x ≤
      2 * Real.sinh (a / 2) * (K * (oddProfile a (t + x) - oddProfile a (t - x))) := by
    calc 2 * Real.sinh (a / 2) * oddProfile a x
        = riemannKernelReal (a - x) - riemannKernelReal (a + x) := h1
      _ ≤ K * (riemannKernelReal (a - t - x) - riemannKernelReal (a - t + x)) := h2
      _ ≤ K * (2 * Real.sinh (a / 2) * (oddProfile a (t + x) - oddProfile a (t - x))) :=
          mul_le_mul_of_nonneg_left h3 hK0
      _ = 2 * Real.sinh (a / 2) * (K * (oddProfile a (t + x) - oddProfile a (t - x))) := by ring
  exact le_of_mul_le_mul_left hmul hsh

/-- **Unconditional Horizon-Uniform Schur Ratio Theorem (`κ(t) = 4 e^{4t}`):**
For every $t \ge 0$, every $a \ge \frac{3}{2}t + \frac{1}{2}\log 2$, and every $x \in [0, t/2]$,
$$m_a(x) \le 4 e^{4t}\,\bigl(m_a(t + x) - m_a(t - x)\bigr),$$
with constant $4 e^{4t}$ completely independent of the support horizon $a$. -/
theorem oddProfile_le_four_exp_four_mul_sub {a t x : ℝ}
    (ht : 0 ≤ t) (ha : 3 * t / 2 + Real.log 2 / 2 ≤ a) (hx : x ∈ Icc (0 : ℝ) (t / 2)) :
    oddProfile a x ≤
      4 * Real.exp (4 * t) * (oddProfile a (t + x) - oddProfile a (t - x)) := by
  have ha_pos : 0 < a := by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hsh : 0 < 2 * Real.sinh (a / 2) :=
    mul_pos (by norm_num) (Real.sinh_pos_iff.mpr (half_pos ha_pos))
  have h1 := two_mul_sinh_mul_oddProfile_eq ha_pos.ne' x
  have h2 := riemannKernelReal_center_drop_le_four_exp_four_shifted_drop ht ha hx
  have h3 := riemannKernelReal_shifted_drop_le_two_mul_sinh_oddProfile_sub ha_pos ht hx
  have hK0 : 0 ≤ 4 * Real.exp (4 * t) := by positivity
  have hmul : 2 * Real.sinh (a / 2) * oddProfile a x ≤
      2 * Real.sinh (a / 2) * (4 * Real.exp (4 * t) * (oddProfile a (t + x) - oddProfile a (t - x))) := by
    calc 2 * Real.sinh (a / 2) * oddProfile a x
        = riemannKernelReal (a - x) - riemannKernelReal (a + x) := h1
      _ ≤ 4 * Real.exp (4 * t) *
            (riemannKernelReal (a - t - x) - riemannKernelReal (a - t + x)) := h2
      _ ≤ 4 * Real.exp (4 * t) *
            (2 * Real.sinh (a / 2) * (oddProfile a (t + x) - oddProfile a (t - x))) :=
          mul_le_mul_of_nonneg_left h3 hK0
      _ = 2 * Real.sinh (a / 2) *
            (4 * Real.exp (4 * t) * (oddProfile a (t + x) - oddProfile a (t - x))) := by ring
  exact le_of_mul_le_mul_left hmul hsh

/-- **Pointwise Unconditional 1-for-1 Schur Collar-Minus-Direct Bound (`κ = 4 e^{4t}`):**
For every $t \ge 0$, $a \ge \frac{3}{2}t + \frac{1}{2}\log 2$, $x \in (0, t/2)$, and
$w : \mathbb{R} \to \mathbb{R}$,
$$\operatorname{oddProfileCollarDiffSq}(a, w, t, x)
  - \operatorname{oddProfileShiftJump}(a, w, t, x)
  \le 4 e^{4t}\,\operatorname{oddProfileAcrossJump}(a, w, t, x).$$ -/
theorem oddProfileCollarDiffSq_sub_direct_le_four_exp_four_mul_across {a t x : ℝ}
    (ht : 0 ≤ t) (ha : 3 * t / 2 + Real.log 2 / 2 ≤ a)
    (hx : x ∈ Ioo (0 : ℝ) (t / 2)) (w : ℝ → ℝ) :
    oddProfileCollarDiffSq a w t x - oddProfileShiftJump a w t x ≤
      4 * Real.exp (4 * t) * oddProfileAcrossJump a w t x := by
  have ha_pos : 0 < a := by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have h3t : 3 * t / 2 ≤ a := by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  exact oddProfileCollarDiffSq_sub_direct_le_of_ratio_bound ha_pos h3t hx
    (oddProfile_le_four_exp_four_mul_sub ht ha (Ioo_subset_Icc_self hx)) w

/-! ## Section 3: Unconditional 1-for-1 Collar-Minus-Direct Excess and Full-Line Prime Positivity -/

/-- **Unconditional 1-for-1 Collar-Minus-Direct Excess Bound via the 2D Absorbed Archimedean Integral:**
Discharging `hκ` unconditionally with $\kappa = 4 e^{4t}$ in
`integral_oddProfileCollarDiffSq_sub_two_direct_le_absorbedArchSlice` proves that for any
$t \ge 0$, $\delta > 0$, $L > 0$ with $\frac{1}{2}\log 2 \le \delta + L$ and
$\frac{3}{2}t + \delta + L \le a$, subtracting twice the half-collar direct jump from the full
collar integral is bounded **purely** by $16 e^{4t}$ times the 2D continuum absorbed archimedean
slice integral over $(t/2, 3t/2) \times (\delta, t + \delta + L)$. -/
theorem integral_oddProfileCollarDiffSq_sub_two_direct_le_sixteen_exp_four_absorbedArchSlice
    {a t δ L : ℝ} (ht : 0 ≤ t) (hδ : 0 < δ) (hL : 0 < L)
    (hδL : Real.log 2 / 2 ≤ δ + L) (ha_le : 3 * t / 2 + δ + L ≤ a)
    {w : ℝ → ℝ} (hw : Continuous w) :
    L * ((1 - Real.exp (-(t / 2))) * archLevyDensity (t + δ + L)) *
        ((∫ x in Ioo (0 : ℝ) t, oddProfileCollarDiffSq a w t x) -
          2 * (∫ x in Ioo (0 : ℝ) (t / 2), oddProfileShiftJump a w t x)) ≤
      16 * Real.exp (4 * t) *
        ∫ y in Ioo (t / 2) (3 * t / 2), absorbedArchSlice a w δ (t + δ + L) y := by
  have ha_pos : 0 < a := by linarith
  have ha_log2 : 3 * t / 2 + Real.log 2 / 2 ≤ a := by linarith
  have h := integral_oddProfileCollarDiffSq_sub_two_direct_le_absorbedArchSlice
    ha_pos ht hδ hL (by positivity : 0 ≤ 4 * Real.exp (4 * t)) ha_le
    (fun x hx => oddProfile_le_four_exp_four_mul_sub ht ha_log2 (Ioo_subset_Icc_self hx)) hw
  linarith

/-- **Unconditional Full-Line Prime Shift Jump + 2D Continuum Absorbed Archimedean Positivity Law:**
For any even continuous compactly supported $w : \mathbb{R} \to \mathbb{R}$ and any $t \ge 0$,
$\delta > 0$, $L > 0$ with $\frac{1}{2}\log 2 \le \delta + L$ and $\frac{3}{2}t + \delta + L \le a$,
the full-line prime shift jump $\int_{\mathbb{R}} \operatorname{oddProfileShiftJump}(a, w, t, x)\,dx$
plus $16 e^{4t}$ times the 2D continuum absorbed archimedean slice integral dominates twice the
non-negative tail prime jump $2 \int_{t/2}^\infty \operatorname{oddProfileShiftJump}(a, w, t, x)\,dx \ge 0$
**without any external ratio hypothesis**. -/
theorem unconditional_two_mul_integral_Ioi_half_le_fullLine_add_absorbedArchSlice
    {a t δ L : ℝ} (ht : 0 ≤ t) (hδ : 0 < δ) (hL : 0 < L)
    (hδL : Real.log 2 / 2 ≤ δ + L) (ha_le : 3 * t / 2 + δ + L ≤ a)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x) :
    2 * L * ((1 - Real.exp (-(t / 2))) * archLevyDensity (t + δ + L)) *
        (∫ x in Ioi (t / 2), oddProfileShiftJump a w t x) ≤
      L * ((1 - Real.exp (-(t / 2))) * archLevyDensity (t + δ + L)) *
        (∫ x : ℝ, oddProfileShiftJump a w t x) +
        16 * Real.exp (4 * t) *
          ∫ y in Ioo (t / 2) (3 * t / 2), absorbedArchSlice a w δ (t + δ + L) y := by
  have ha_pos : 0 < a := by linarith
  have ha_log2 : 3 * t / 2 + Real.log 2 / 2 ≤ a := by linarith
  have h := two_mul_integral_Ioi_half_le_fullLine_add_absorbedArchSlice
    ha_pos ht hδ hL (by positivity : 0 ≤ 4 * Real.exp (4 * t)) ha_le
    (fun x hx => oddProfile_le_four_exp_four_mul_sub ht ha_log2 (Ioo_subset_Icc_self hx))
    hw hwc heven
  linarith

/-- **Unconditional Non-Negativity of Full-Line Prime Shift Jump + 2D Continuum Absorbed Archimedean Slice:** -/
theorem unconditional_fullLine_add_absorbedArchSlice_nonneg
    {a t δ L : ℝ} (ht : 0 ≤ t) (hδ : 0 < δ) (hL : 0 < L)
    (hδL : Real.log 2 / 2 ≤ δ + L) (ha_le : 3 * t / 2 + δ + L ≤ a)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x) :
    0 ≤ L * ((1 - Real.exp (-(t / 2))) * archLevyDensity (t + δ + L)) *
        (∫ x : ℝ, oddProfileShiftJump a w t x) +
        16 * Real.exp (4 * t) *
          ∫ y in Ioo (t / 2) (3 * t / 2), absorbedArchSlice a w δ (t + δ + L) y := by
  have ha_pos : 0 < a := by linarith
  have htail_nonneg : 0 ≤ ∫ x in Ioi (t / 2), oddProfileShiftJump a w t x := by
    refine setIntegral_nonneg measurableSet_Ioi fun x hx => ?_
    have hx_pos : 0 < x := by linarith [mem_Ioi.mp hx]
    exact oddProfileShiftJump_nonneg_of_pos ha_pos hx_pos ht w
  have hC_nonneg : 0 ≤ 2 * L * ((1 - Real.exp (-(t / 2))) * archLevyDensity (t + δ + L)) := by
    refine mul_nonneg (by linarith) (mul_nonneg ?_ (archLevyDensity_pos (by linarith)).le)
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  exact (mul_nonneg hC_nonneg htail_nonneg).trans
    (unconditional_two_mul_integral_Ioi_half_le_fullLine_add_absorbedArchSlice
      ht hδ hL hδL ha_le hw hwc heven)

/-! ## Section 4: Global 2D Rectangle Monotonicity and Summed Low-Prime Budget -/

/-- **Monotonicity of `absorbedArchSlice` in the Upper Shift Cutoff `M`:**
For $a > 0$, $\delta > 0$, $M_1 \le M_2$, $y > 0$, and continuous $w : \mathbb{R} \to \mathbb{R}$,
$$\operatorname{absorbedArchSlice}(a, w, \delta, M_1, y)
  \le \operatorname{absorbedArchSlice}(a, w, \delta, M_2, y).$$ -/
theorem absorbedArchSlice_mono_right {a δ M₁ M₂ y : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hM : M₁ ≤ M₂) (hy : 0 < y)
    {w : ℝ → ℝ} (hw : Continuous w) :
    absorbedArchSlice a w δ M₁ y ≤ absorbedArchSlice a w δ M₂ y := by
  unfold absorbedArchSlice
  refine setIntegral_mono_set (integrableOn_absorbedArchIntegrand_Ioo hδ hy.le hw) ?_
    (Eventually.of_forall fun s hs => ⟨hs.1, hs.2.trans_le hM⟩)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact absorbedArchIntegrand_nonneg ha (hδ.trans hs.1) hy w

/-- **Embedding Each Per-Prime 2D Slice into the Single Global 2D Rectangle `(0, a) × (δ, a)`:**
For any $t \ge 0$, $\delta > 0$, $L > 0$ with $\frac{3}{2}t + \delta + L \le a$ and any continuous
$w : \mathbb{R} \to \mathbb{R}$, since $t + \delta + L \le a$ and $(t/2, 3t/2) \subset (0, a)$,
the per-prime 2D slice integral is bounded above by the single global 2D integral over
$(y, s) \in (0, a) \times (\delta, a)$. -/
theorem integral_absorbedArchSlice_Ioo_le_global_Ioo {a t δ L : ℝ}
    (ht : 0 ≤ t) (hδ : 0 < δ) (hL : 0 < L) (ha_le : 3 * t / 2 + δ + L ≤ a)
    {w : ℝ → ℝ} (hw : Continuous w) :
    (∫ y in Ioo (t / 2) (3 * t / 2), absorbedArchSlice a w δ (t + δ + L) y) ≤
      ∫ y in Ioo (0 : ℝ) a, absorbedArchSlice a w δ a y := by
  have ha_pos : 0 < a := by linarith
  have hδa : δ ≤ a := by linarith
  have hMa : t + δ + L ≤ a := by linarith
  have hF_global : ContinuousOn (absorbedArchSlice a w δ a) (Ici (0 : ℝ)) :=
    continuousOn_absorbedArchSlice_Ici a hδ hδa hw
  have hint_global : IntegrableOn (absorbedArchSlice a w δ a) (Ioo (0 : ℝ) a) :=
    (hF_global.mono fun y hy => mem_Ici.mpr hy.1).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hF_local : ContinuousOn (absorbedArchSlice a w δ (t + δ + L)) (Ici (0 : ℝ)) :=
    continuousOn_absorbedArchSlice_Ici a hδ (by linarith) hw
  have hint_local : IntegrableOn (absorbedArchSlice a w δ (t + δ + L)) (Ioo (t / 2) (3 * t / 2)) :=
    (hF_local.mono fun y hy => mem_Ici.mpr (by linarith [hy.1])).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hint_sub : IntegrableOn (absorbedArchSlice a w δ a) (Ioo (t / 2) (3 * t / 2)) :=
    hint_global.mono_set fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hstep1 : (∫ y in Ioo (t / 2) (3 * t / 2), absorbedArchSlice a w δ (t + δ + L) y) ≤
      ∫ y in Ioo (t / 2) (3 * t / 2), absorbedArchSlice a w δ a y := by
    refine setIntegral_mono_on hint_local hint_sub measurableSet_Ioo fun y hy => ?_
    exact absorbedArchSlice_mono_right ha_pos hδ hMa (by linarith [hy.1]) hw
  have hstep2 : (∫ y in Ioo (t / 2) (3 * t / 2), absorbedArchSlice a w δ a y) ≤
      ∫ y in Ioo (0 : ℝ) a, absorbedArchSlice a w δ a y := by
    refine setIntegral_mono_set hint_global ?_
      (Eventually.of_forall fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact absorbedArchSlice_nonneg ha_pos hδ hy.1 w
  exact hstep1.trans hstep2

/-- **Direct-Minus-Collar Archimedean Upper Bound on `absorbedArchSlice`:**
At every $y > 0$, whenever `s ↦ ω(s) oddProfileShiftJump a w s y` is integrable on `(0, ∞)`,
the compact-strip slice `absorbedArchSlice a w δ M y` is bounded above by the exact half-line
archimedean direct-minus-collar difference from `integral_arch_direct_sub_collar_eq_absorbed`. -/
theorem absorbedArchSlice_le_arch_direct_sub_collar {a δ M y : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hy : 0 < y) {w : ℝ → ℝ} (hw : Continuous w)
    (hdir : IntegrableOn (fun s : ℝ => archLevyDensity s * oddProfileShiftJump a w s y) (Ioi 0)) :
    absorbedArchSlice a w δ M y ≤
      (∫ s in Ioi (0 : ℝ), archLevyDensity s * oddProfileShiftJump a w s y) -
        (∫ t in Ioi (2 * y), archLevyDensity t * oddProfileCollarDiffSq a w t y) := by
  have hcol := integrableOn_arch_collar_shift_of_direct ha hy hw hdir
  have hint_abs : IntegrableOn (fun s : ℝ => absorbedArchIntegrand a w s y) (Ioi 0) := by
    refine (hdir.sub hcol).congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, absorbedArchIntegrand]
    ring
  rw [integral_arch_direct_sub_collar_eq_absorbed ha hy hw hdir]
  exact absorbedArchSlice_le_integral_Ioi ha hδ hy hint_abs

/-- **Unconditional Summed Low-Prime Budget Against the Global 2D Absorbed Archimedean Integral:**
For any finite set $S$ of prime powers in the low-prime window $\frac{3}{2}\log d + \delta + L \le a$
with $\frac{1}{2}\log 2 \le \delta + L$ and any even continuous compactly supported $w$, the
von Mangoldt-weighted sum of full-line prime shift jumps plus the single global 2D absorbed
archimedean integral on $(0, a) \times (\delta, a)$ dominates twice the sum of non-negative tail
prime jumps. -/
theorem sum_vonMangoldt_fullLine_add_global_absorbedArchSlice_ge_tail
    {a δ L : ℝ} (hδ : 0 < δ) (hL : 0 < L) (hδL : Real.log 2 / 2 ≤ δ + L)
    (S : Finset ℕ) (hS : ∀ d ∈ S, 3 * Real.log d / 2 + δ + L ≤ a)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x) :
    2 * (∑ d ∈ S, vonMangoldtAtom d *
        (L * ((1 - Real.exp (-(Real.log d / 2))) * archLevyDensity (Real.log d + δ + L)) *
          (∫ x in Ioi (Real.log d / 2), oddProfileShiftJump a w (Real.log d) x))) ≤
      (∑ d ∈ S, vonMangoldtAtom d *
        (L * ((1 - Real.exp (-(Real.log d / 2))) * archLevyDensity (Real.log d + δ + L)) *
          (∫ x : ℝ, oddProfileShiftJump a w (Real.log d) x))) +
        (∑ d ∈ S, 16 * vonMangoldtAtom d * Real.exp (4 * Real.log d)) *
          ∫ y in Ioo (0 : ℝ) a, absorbedArchSlice a w δ a y := by
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun d hd => ?_
  have ht : 0 ≤ Real.log (d : ℝ) := Real.log_natCast_nonneg d
  have hd_le : 3 * Real.log d / 2 + δ + L ≤ a := hS d hd
  have h1 := unconditional_two_mul_integral_Ioi_half_le_fullLine_add_absorbedArchSlice
    ht hδ hL hδL hd_le hw hwc heven
  have h2 := integral_absorbedArchSlice_Ioo_le_global_Ioo ht hδ hL hd_le hw
  have hvm : 0 ≤ vonMangoldtAtom d := vonMangoldtAtom_nonneg d
  have h16 : 0 ≤ 16 * Real.exp (4 * Real.log (d : ℝ)) := by positivity
  have hstep : 2 * L * ((1 - Real.exp (-(Real.log d / 2))) * archLevyDensity (Real.log d + δ + L)) *
        (∫ x in Ioi (Real.log d / 2), oddProfileShiftJump a w (Real.log d) x) ≤
      L * ((1 - Real.exp (-(Real.log d / 2))) * archLevyDensity (Real.log d + δ + L)) *
        (∫ x : ℝ, oddProfileShiftJump a w (Real.log d) x) +
        16 * Real.exp (4 * Real.log d) *
          ∫ y in Ioo (0 : ℝ) a, absorbedArchSlice a w δ a y :=
    h1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left h2 h16))
  have hmul := mul_le_mul_of_nonneg_left hstep hvm
  linarith

/-! ## Section 5: Unweighted Low-Prime Collar-to-Continuum Comparison and Full-Line Shift-Jump Positivity (Obstacle B) -/

/-- Explicit unweighted collar-to-continuum ratio constant for a prime power $d$:
$$\operatorname{primeCollarArchRatio}(\delta, L, d)
  = \frac{16 e^{4\log d}}{L\,(1 - e^{-\log d / 2})\,\omega(\log d + \delta + L)}.$$ -/
def primeCollarArchRatio (δ L : ℝ) (d : ℕ) : ℝ :=
  (16 * Real.exp (4 * Real.log d)) /
    (L * ((1 - Real.exp (-(Real.log d / 2))) * archLevyDensity (Real.log d + δ + L)))

theorem primeCollarArchRatio_nonneg {δ L : ℝ} (hδ : 0 < δ) (hL : 0 < L) (d : ℕ) :
    0 ≤ primeCollarArchRatio δ L d := by
  unfold primeCollarArchRatio
  have ht : 0 ≤ Real.log (d : ℝ) := Real.log_natCast_nonneg d
  have h1 : 0 ≤ 1 - Real.exp (-(Real.log (d : ℝ) / 2)) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have h2 : 0 < archLevyDensity (Real.log d + δ + L) := archLevyDensity_pos (by linarith)
  exact div_nonneg (by positivity) (mul_nonneg hL.le (mul_nonneg h1 h2.le))

/-- **Unweighted Per-Prime 1-for-1 Collar-Minus-Direct Bound via Global 2D Absorbed Archimedean Integral:**
Dividing by $L\,(1 - e^{-\log d / 2})\,\omega(\log d + \delta + L) > 0$ for $d \ge 2$ (and using
$\operatorname{vonMangoldtAtom} d = 0$ for $d < 2$) yields the unweighted CHMD collar excess bound. -/
theorem vonMangoldt_oddProfileCollarDiffSq_sub_two_direct_le_global_absorbedArchSlice
    {a δ L : ℝ} (hδ : 0 < δ) (hL : 0 < L) (hδL : Real.log 2 / 2 ≤ δ + L)
    {d : ℕ} (hd_le : 3 * Real.log d / 2 + δ + L ≤ a)
    {w : ℝ → ℝ} (hw : Continuous w) :
    vonMangoldtAtom d *
        ((∫ x in Ioo (0 : ℝ) (Real.log d), oddProfileCollarDiffSq a w (Real.log d) x) -
          2 * (∫ x in Ioo (0 : ℝ) (Real.log d / 2), oddProfileShiftJump a w (Real.log d) x)) ≤
      (vonMangoldtAtom d * primeCollarArchRatio δ L d) *
        ∫ y in Ioo (0 : ℝ) a, absorbedArchSlice a w δ a y := by
  by_cases hd2 : 2 ≤ d
  · have hd_gt1 : (1 : ℝ) < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hd2)
    have ht_pos : 0 < Real.log (d : ℝ) := Real.log_pos hd_gt1
    have h1_pos : 0 < 1 - Real.exp (-(Real.log (d : ℝ) / 2)) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
    have hω_pos : 0 < archLevyDensity (Real.log d + δ + L) := archLevyDensity_pos (by linarith)
    set γ : ℝ := L * ((1 - Real.exp (-(Real.log d / 2))) * archLevyDensity (Real.log d + δ + L))
    have hγ_pos : 0 < γ := mul_pos hL (mul_pos h1_pos hω_pos)
    have h1 := integral_oddProfileCollarDiffSq_sub_two_direct_le_sixteen_exp_four_absorbedArchSlice
      ht_pos.le hδ hL hδL hd_le hw
    have h2 := integral_absorbedArchSlice_Ioo_le_global_Ioo ht_pos.le hδ hL hd_le hw
    have h16 : 0 ≤ 16 * Real.exp (4 * Real.log (d : ℝ)) := by positivity
    have hstep : γ * ((∫ x in Ioo (0 : ℝ) (Real.log d), oddProfileCollarDiffSq a w (Real.log d) x) -
          2 * (∫ x in Ioo (0 : ℝ) (Real.log d / 2), oddProfileShiftJump a w (Real.log d) x)) ≤
        16 * Real.exp (4 * Real.log d) *
          ∫ y in Ioo (0 : ℝ) a, absorbedArchSlice a w δ a y :=
      h1.trans (mul_le_mul_of_nonneg_left h2 h16)
    have hdiv := (le_div_iff₀' hγ_pos).mpr hstep
    have hmul := mul_le_mul_of_nonneg_left hdiv (vonMangoldtAtom_nonneg d)
    unfold primeCollarArchRatio
    change vonMangoldtAtom d * _ ≤
      (vonMangoldtAtom d * ((16 * Real.exp (4 * Real.log d)) / γ)) * _
    linarith [
      show vonMangoldtAtom d *
          ((16 * Real.exp (4 * Real.log d) * ∫ y in Ioo (0 : ℝ) a, absorbedArchSlice a w δ a y) / γ) =
        (vonMangoldtAtom d * ((16 * Real.exp (4 * Real.log d)) / γ)) *
          ∫ y in Ioo (0 : ℝ) a, absorbedArchSlice a w δ a y by ring]
  · have hvm0 : vonMangoldtAtom d = 0 := by
      unfold vonMangoldtAtom
      exact if_neg hd2
    rw [hvm0]
    simp

/-- **Unweighted Per-Prime Collar Domination by Half-Line Prime Jump + Global 2D Absorbed Archimedean Integral:** -/
theorem vonMangoldt_oddProfileCollarDiffSq_le_two_Ioi_add_global_absorbedArchSlice
    {a δ L : ℝ} (hδ : 0 < δ) (hL : 0 < L) (hδL : Real.log 2 / 2 ≤ δ + L)
    {d : ℕ} (hd_le : 3 * Real.log d / 2 + δ + L ≤ a)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w) :
    vonMangoldtAtom d *
        (∫ x in Ioo (0 : ℝ) (Real.log d), oddProfileCollarDiffSq a w (Real.log d) x) ≤
      2 * vonMangoldtAtom d *
        (∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w (Real.log d) x) +
      (vonMangoldtAtom d * primeCollarArchRatio δ L d) *
        ∫ y in Ioo (0 : ℝ) a, absorbedArchSlice a w δ a y := by
  have ht : 0 ≤ Real.log (d : ℝ) := Real.log_natCast_nonneg d
  have ha_pos : 0 < a := by linarith
  have h1 := vonMangoldt_oddProfileCollarDiffSq_sub_two_direct_le_global_absorbedArchSlice
    hδ hL hδL hd_le hw
  have hint : IntegrableOn (oddProfileShiftJump a w (Real.log d)) (Ioi (0 : ℝ)) := by
    have hsub : HasCompactSupport (fun x : ℝ => w x - w (x + Real.log d)) :=
      hwc.sub (hwc.comp_homeomorph (Homeomorph.addRight (Real.log d)))
    have hsub2 : HasCompactSupport (fun x : ℝ => (w x - w (x + Real.log d)) ^ 2) := by
      rw [hasCompactSupport_iff_eventuallyEq] at hsub ⊢
      filter_upwards [hsub] with x hx; simp [hx]
    have hc : Continuous (oddProfileShiftJump a w (Real.log d)) := by
      unfold oddProfileShiftJump
      exact (((continuous_oddProfile a).mul
        ((continuous_oddProfile a).comp (continuous_id.add continuous_const))).mul
        ((hw.sub (hw.comp (continuous_id.add continuous_const))).pow 2))
    exact (hc.integrable_of_hasCompactSupport hsub2.mul_left).integrableOn
  have hdir_mono : (∫ x in Ioo (0 : ℝ) (Real.log d / 2), oddProfileShiftJump a w (Real.log d) x) ≤
      ∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w (Real.log d) x := by
    refine setIntegral_mono_set hint ?_ (Eventually.of_forall fun x hx => hx.1)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact oddProfileShiftJump_nonneg_of_pos ha_pos (mem_Ioi.mp hx) ht w
  have hdir_mul := mul_le_mul_of_nonneg_left hdir_mono
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (vonMangoldtAtom_nonneg d))
  linarith

/-- **Obstacle B Closure — Unweighted Summed Low-Prime Collar Comparison Against Half-Line Prime Jumps and the Global 2D Absorbed Archimedean Integral:**
For any finite set $S$ of low prime powers ($\frac{3}{2}\log d + \delta + L \le a$), the unweighted
von Mangoldt sum of discrete prime-collar line integrals is bounded above by twice the unweighted
sum of half-line prime shift jumps plus the single global 2D absorbed archimedean integral. -/
theorem sum_vonMangoldt_oddProfileCollarDiffSq_le_two_Ioi_add_global_absorbedArchSlice
    {a δ L : ℝ} (hδ : 0 < δ) (hL : 0 < L) (hδL : Real.log 2 / 2 ≤ δ + L)
    (S : Finset ℕ) (hS : ∀ d ∈ S, 3 * Real.log d / 2 + δ + L ≤ a)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w) :
    (∑ d ∈ S, vonMangoldtAtom d *
        (∫ x in Ioo (0 : ℝ) (Real.log d), oddProfileCollarDiffSq a w (Real.log d) x)) ≤
      2 * (∑ d ∈ S, vonMangoldtAtom d *
        (∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w (Real.log d) x)) +
      (∑ d ∈ S, vonMangoldtAtom d * primeCollarArchRatio δ L d) *
        ∫ y in Ioo (0 : ℝ) a, absorbedArchSlice a w δ a y := by
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun d hd => ?_
  have h := vonMangoldt_oddProfileCollarDiffSq_le_two_Ioi_add_global_absorbedArchSlice
    hδ hL hδL (hS d hd) hw hwc
  linarith

/-- **Unweighted Summed Full-Line Prime Shift Jump + Global 2D Absorbed Archimedean Positivity Law:**
For any finite set $S$ of low prime powers ($\frac{3}{2}\log d + \delta + L \le a$) and any even
continuous compactly supported $w$, the unweighted CHMD prime shift-jump sum plus the global 2D
absorbed archimedean integral dominates twice the unweighted sum of non-negative tail prime jumps. -/
theorem sum_vonMangoldt_fullLine_add_global_absorbedArchSlice_ge_two_tail_unweighted
    {a δ L : ℝ} (hδ : 0 < δ) (hL : 0 < L) (hδL : Real.log 2 / 2 ≤ δ + L)
    (S : Finset ℕ) (hS : ∀ d ∈ S, 3 * Real.log d / 2 + δ + L ≤ a)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x) :
    2 * (∑ d ∈ S, vonMangoldtAtom d *
        (∫ x in Ioi (Real.log d / 2), oddProfileShiftJump a w (Real.log d) x)) ≤
      (∑ d ∈ S, vonMangoldtAtom d *
        (∫ x : ℝ, oddProfileShiftJump a w (Real.log d) x)) +
      (∑ d ∈ S, vonMangoldtAtom d * primeCollarArchRatio δ L d) *
        ∫ y in Ioo (0 : ℝ) a, absorbedArchSlice a w δ a y := by
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun d hd => ?_
  by_cases hd2 : 2 ≤ d
  · have hd_gt1 : (1 : ℝ) < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hd2)
    have ht_pos : 0 < Real.log (d : ℝ) := Real.log_pos hd_gt1
    have h1_pos : 0 < 1 - Real.exp (-(Real.log (d : ℝ) / 2)) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
    have hω_pos : 0 < archLevyDensity (Real.log d + δ + L) := archLevyDensity_pos (by linarith)
    set γ : ℝ := L * ((1 - Real.exp (-(Real.log d / 2))) * archLevyDensity (Real.log d + δ + L))
    have hγ_pos : 0 < γ := mul_pos hL (mul_pos h1_pos hω_pos)
    have h1 := unconditional_two_mul_integral_Ioi_half_le_fullLine_add_absorbedArchSlice
      ht_pos.le hδ hL hδL (hS d hd) hw hwc heven
    have h2 := integral_absorbedArchSlice_Ioo_le_global_Ioo ht_pos.le hδ hL (hS d hd) hw
    have h16 : 0 ≤ 16 * Real.exp (4 * Real.log (d : ℝ)) := by positivity
    have hstep : γ * (2 * ∫ x in Ioi (Real.log d / 2), oddProfileShiftJump a w (Real.log d) x) ≤
        γ * (∫ x : ℝ, oddProfileShiftJump a w (Real.log d) x) +
          16 * Real.exp (4 * Real.log d) *
            ∫ y in Ioo (0 : ℝ) a, absorbedArchSlice a w δ a y := by
      have := h1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left h2 h16))
      linarith
    have hdiv := (le_div_iff₀' hγ_pos).mpr hstep
    have hmul := mul_le_mul_of_nonneg_left hdiv (vonMangoldtAtom_nonneg d)
    unfold primeCollarArchRatio
    change 2 * (vonMangoldtAtom d * _) ≤
      vonMangoldtAtom d * _ +
        (vonMangoldtAtom d * ((16 * Real.exp (4 * Real.log d)) / γ)) * _
    have hγ_ne : γ ≠ 0 := hγ_pos.ne'
    have hident :
        vonMangoldtAtom d *
          ((γ * (∫ x : ℝ, oddProfileShiftJump a w (Real.log d) x) +
            16 * Real.exp (4 * Real.log d) *
              ∫ y in Ioo (0 : ℝ) a, absorbedArchSlice a w δ a y) / γ) =
        vonMangoldtAtom d * (∫ x : ℝ, oddProfileShiftJump a w (Real.log d) x) +
          (vonMangoldtAtom d * ((16 * Real.exp (4 * Real.log d)) / γ)) *
            ∫ y in Ioo (0 : ℝ) a, absorbedArchSlice a w δ a y := by
      rw [add_div, mul_div_cancel_left₀ _ hγ_ne]
      ring
    linarith
  · have hvm0 : vonMangoldtAtom d = 0 := by
      unfold vonMangoldtAtom
      exact if_neg hd2
    rw [hvm0]
    simp

end GaloisForLFunctions.TransHorizonIncidenceMechanics

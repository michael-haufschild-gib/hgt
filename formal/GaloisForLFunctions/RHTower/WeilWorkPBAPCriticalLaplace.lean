import GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalWindow

/-!
# Laplace transform of the actual signed coefficient window

The series interchange uses the absolute convergence derived from actual
modified positivity. The coefficients themselves can have either sign.
-/

open Complex MeasureTheory Filter Topology Set Zeta23
open scoped Real ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- The actual real Dirichlet series, with the unused indices zeroed. -/
def criticalDirichletReal (lam : ℕ → ℝ) (σ : ℝ) : ℝ :=
  ∑' n : ℕ, (if 2 ≤ n then lam n else 0) * (n : ℝ) ^ (-σ)

theorem summable_critical_abs_terms {a b C : ℝ} (ha : 0 ≤ a) {lam : ℕ → ℝ}
    (h : ∀ f : SmoothTest, testAtoms lam f.1 ≤ criticalDatum a b C f.1.1)
    {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => |if 2 ≤ n then lam n else 0| * (n : ℝ) ^ (-σ) := by
  refine (summable_abs_div_rpow_critical ha h hσ).of_norm_bounded fun n => ?_
  by_cases hn : 2 ≤ n
  · simpa only [if_pos hn, Real.norm_eq_abs, abs_mul, abs_abs,
      Real.rpow_neg (Nat.cast_nonneg n), abs_inv,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ), div_eq_mul_inv] using
      (le_refl (|lam n| / (n : ℝ) ^ σ))
  · simp only [if_neg hn, abs_zero, zero_mul, norm_zero]
    positivity

theorem measurable_criticalWindow (lam : ℕ → ℝ) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) : Measurable (criticalWindow lam g) :=
  Measurable.tsum fun n => measurable_const.mul (continuous_windowValue hg hgc n).measurable

/-- Exact Laplace identity for signed coefficients of any actual modified completion. -/
theorem integral_criticalWindow_mul_exp {a b C : ℝ} (ha : 0 ≤ a) {lam : ℕ → ℝ}
    (h : ∀ f : SmoothTest, testAtoms lam f.1 ≤ criticalDatum a b C f.1.1)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (hg0 : ∀ u, 0 ≤ g u)
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∫ y in Ioi (0 : ℝ), criticalWindow lam g y * Real.exp (-σ * y) =
      autoLaplaceReal g σ * criticalDirichletReal lam (1 / 2 + σ) := by
  let c : ℕ → ℝ := fun n => if 2 ≤ n then lam n else 0
  let F : ℕ → ℝ → ℝ := fun n y => c n * windowValue g y n * Real.exp (-σ * y)
  have hFc : ∀ n, HasCompactSupport (F n) := fun n =>
    (hasCompactSupport_windowValue hsupp n).mono (Function.support_subset_iff'.mpr fun y hy => by
      simp only [Function.mem_support, not_not] at hy
      simp only [F, hy, mul_zero, zero_mul])
  have hFint : ∀ n, Integrable (F n) (volume.restrict (Ioi 0)) := fun n =>
    (Continuous.integrable_of_hasCompactSupport
      ((continuous_const.mul (continuous_windowValue hg hgc n)).mul (by fun_prop))
      (hFc n)).integrableOn
  have hFval : ∀ n, ∫ y in Ioi (0 : ℝ), F n y =
      c n * (n : ℝ) ^ (-(1 / 2 + σ)) * autoLaplaceReal g σ := by
    intro n
    simp only [F, mul_assoc]
    rw [integral_const_mul]
    by_cases hn : 2 ≤ n
    · rw [integral_windowValue_mul_exp hsupp hn]
    · simp [c, hn]
  have hFnorm : ∀ n, ∫ y in Ioi (0 : ℝ), ‖F n y‖ =
      |c n| * (n : ℝ) ^ (-(1 / 2 + σ)) * autoLaplaceReal g σ := by
    intro n
    have heq : (fun y => ‖F n y‖) =
        fun y => |c n| * (windowValue g y n * Real.exp (-σ * y)) := by
      funext y
      simp only [F, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (windowValue_nonneg hg0 y n), abs_of_pos (Real.exp_pos _), mul_assoc]
    rw [heq, integral_const_mul]
    by_cases hn : 2 ≤ n
    · rw [integral_windowValue_mul_exp hsupp hn]
      ring
    · simp [c, hn]
  have hsum : Summable fun n => ∫ y in Ioi (0 : ℝ), ‖F n y‖ := by
    simp_rw [hFnorm]
    exact (summable_critical_abs_terms ha h (by linarith : 1 < 1 / 2 + σ)).mul_right _
  have hswap := integral_tsum_of_summable_integral_norm hFint hsum
  have hpt : ∀ y, criticalWindow lam g y * Real.exp (-σ * y) = ∑' n, F n y := fun y => by
    rw [criticalWindow, ← tsum_mul_right]
  simp_rw [hpt]
  rw [← hswap]
  simp_rw [hFval]
  rw [tsum_mul_right]
  exact mul_comm _ _

/-- Uniform control of the holomorphic remainder on the positive real axis. -/
theorem critical_laplace_remainder_bound {a b C : ℝ} (ha : 0 ≤ a) {lam : ℕ → ℝ}
    (h : ∀ f : SmoothTest, testAtoms lam f.1 ≤ criticalDatum a b C f.1.1)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (hg0 : ∀ u, 0 ≤ g u) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ : ℝ, 1 / 2 < σ →
      |autoLaplaceReal g σ * criticalDirichletReal lam (1 / 2 + σ) -
        b * poleConst g / (σ - 1 / 2) - b * poleConst g / (σ + 1 / 2)| ≤ M / σ := by
  obtain ⟨M, hM⟩ := exists_abs_criticalWindow_sub_poles_le h hg hgc
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine ⟨M, hM0, fun σ hσ => ?_⟩
  have hσ0 : 0 < σ := by linarith
  let E : ℝ → ℝ := fun y => criticalWindow lam g y - b * shiftMajorant g 0 y
  have hE : ∀ y, |E y| ≤ M := by
    intro y
    simpa only [E, shiftMajorant, add_zero, mul_assoc] using hM y
  have hmE : Measurable E :=
    (measurable_criticalWindow lam (contDiff_infty.mp hg 2) hgc).sub (by
      unfold shiftMajorant
      fun_prop)
  have hiM := (exp_neg_integrableOn_Ioi 0 hσ0).const_mul M
  have hpoint : ∀ y : ℝ, ‖E y * Real.exp (-σ * y)‖ ≤ M * Real.exp (-σ * y) := by
    intro y
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
      mul_le_mul_of_nonneg_right (hE y) (Real.exp_pos _).le
  have hiE : IntegrableOn (fun y => E y * Real.exp (-σ * y)) (Ioi 0) :=
    hiM.mono' (hmE.mul (by fun_prop)).aestronglyMeasurable (ae_of_all _ hpoint)
  obtain ⟨hiP, hP⟩ := integral_shiftMajorant_mul_exp (g := g) 0 hσ
  have hdecomp : (fun y => criticalWindow lam g y * Real.exp (-σ * y)) =
      fun y => b * (shiftMajorant g 0 y * Real.exp (-σ * y)) +
        E y * Real.exp (-σ * y) := by
    funext y
    dsimp [E]
    ring
  have hval := integral_criticalWindow_mul_exp ha h (contDiff_infty.mp hg 2) hgc hsupp hg0 hσ
  rw [hdecomp, integral_add (hiP.const_mul b) hiE, integral_const_mul, hP] at hval
  have hbound := norm_integral_le_of_norm_le hiM (ae_of_all _ hpoint)
  rw [integral_const_mul, integral_exp_neg_mul_Ioi_real hσ0,
    Real.norm_eq_abs] at hbound
  have heq : autoLaplaceReal g σ * criticalDirichletReal lam (1 / 2 + σ) -
      b * poleConst g / (σ - 1 / 2) - b * poleConst g / (σ + 1 / 2) =
      ∫ y in Ioi (0 : ℝ), E y * Real.exp (-σ * y) := by
    rw [← hval]
    ring
  rw [heq]
  simpa only [div_eq_mul_inv, one_mul] using hbound

end RHTower.WeilWorkPBAP

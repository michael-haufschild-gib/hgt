import GaloisForLFunctions.RHTower.ZetaVerticalLineGrowth
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# A holomorphic function of polynomial growth restricts to a temperate-growth function on a line

Infrastructure for App I (25) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  `|L(1/2 + it)| = O(|t|^N)`,  *"in particular, since `L(1/2+it)` is an analytic function of `t`
  we see that it is a multiplier of the algebra `𝒮(ℝ)`"*.

The step Connes compresses into that sentence is that a *pointwise* polynomial bound on an
analytic function upgrades to polynomial bounds on **all** derivatives — which is what
`Function.HasTemperateGrowth`, and hence mathlib's multiplier `SchwartzMap.smulLeftCLM`, requires.
Cauchy's estimate on a disc of fixed radius does exactly that, provided the bound is available on
a whole *tube* around the line rather than just on the line itself.

This module proves the general statement; `ConnesZetaLineTemperate` instantiates it for `ζ`.
-/

open Complex Filter Topology
open scoped ContDiff

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Every iterated derivative of an analytic function is analytic. -/
theorem connes_analyticOnNhd_iteratedDeriv {U : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) : ∀ n : ℕ, AnalyticOnNhd ℂ (iteratedDeriv n f) U := by
  intro n
  induction n with
  | zero => simpa [iteratedDeriv_zero] using hf
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv

/-- The real-linear map `s ↦ s i`. -/
private def connesLineMap : ℝ →L[ℝ] ℂ := (ContinuousLinearMap.id ℝ ℝ).smulRight I

theorem connesLineMap_apply (s : ℝ) : connesLineMap s = (s : ℂ) * I := by
  rw [connesLineMap]
  simp [Complex.real_smul]

theorem connesLineMap_coe : (fun s : ℝ => (connesLineMap s : ℂ)) = fun s : ℝ => (s : ℂ) * I :=
  funext connesLineMap_apply

/-- The line `s ↦ c + s i` has derivative `i`. -/
theorem connes_hasDerivAt_line (c : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => c + (s : ℂ) * I) I t := by
  have h1 : HasDerivAt (fun s : ℝ => (connesLineMap s : ℂ)) (connesLineMap 1) t :=
    connesLineMap.hasDerivAt
  rw [connesLineMap_coe, connesLineMap_apply] at h1
  simp only [Complex.ofReal_one, one_mul] at h1
  exact h1.const_add c

/-- **The iterated derivative of a line restriction.**  Restricting an analytic function to a
vertical line multiplies its `n`-th derivative by `i^n`. -/
theorem connes_iteratedDeriv_lineRestrict {U : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (c : ℂ) (hline : ∀ s : ℝ, c + (s : ℂ) * I ∈ U) :
    ∀ (n : ℕ) (t : ℝ), iteratedDeriv n (fun s : ℝ => f (c + (s : ℂ) * I)) t
      = I ^ n * iteratedDeriv n f (c + (t : ℂ) * I) := by
  intro n
  induction n with
  | zero =>
    intro t
    simp [iteratedDeriv_zero]
  | succ n ih =>
    intro t
    have hfun : iteratedDeriv n (fun s : ℝ => f (c + (s : ℂ) * I))
        = fun s : ℝ => I ^ n * iteratedDeriv n f (c + (s : ℂ) * I) := funext ih
    have hanal := connes_analyticOnNhd_iteratedDeriv hf n
    have hdiff : DifferentiableAt ℂ (iteratedDeriv n f) (c + (t : ℂ) * I) :=
      (hanal _ (hline t)).differentiableAt
    have hchain : HasDerivAt (fun s : ℝ => iteratedDeriv n f (c + (s : ℂ) * I))
        (I * deriv (iteratedDeriv n f) (c + (t : ℂ) * I)) t := by
      have h1 := hdiff.hasDerivAt
      have h2 := connes_hasDerivAt_line c t
      simpa [Function.comp_def, smul_eq_mul] using h1.scomp t h2
    have hmul : HasDerivAt (fun s : ℝ => I ^ n * iteratedDeriv n f (c + (s : ℂ) * I))
        (I ^ n * (I * deriv (iteratedDeriv n f) (c + (t : ℂ) * I))) t := hchain.const_mul _
    rw [iteratedDeriv_succ, hfun, hmul.deriv, iteratedDeriv_succ]
    ring

/-- **The line restriction is smooth.** -/
theorem connes_contDiff_lineRestrict {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (c : ℂ) (hline : ∀ s : ℝ, c + (s : ℂ) * I ∈ U) :
    ContDiff ℝ ∞ (fun s : ℝ => f (c + (s : ℂ) * I)) := by
  have hcd : ContDiffOn ℂ ∞ f U := hf.contDiffOn hU.uniqueDiffOn
  have hcdR : ContDiffOn ℝ ∞ f U := hcd.restrict_scalars ℝ
  have hlinecd : ContDiff ℝ ∞ (fun s : ℝ => c + (s : ℂ) * I) := by
    have hL : ContDiff ℝ ∞ (fun s : ℝ => (connesLineMap s : ℂ)) := connesLineMap.contDiff
    rw [connesLineMap_coe] at hL
    exact contDiff_const.add hL
  exact hcdR.comp_contDiff hlinecd hline

/-- **App I (25), the general form.**  An analytic function bounded by `C(1+|s|)^N` on a tube of
fixed radius around a vertical line restricts to a function of temperate growth on that line. -/
theorem connes_hasTemperateGrowth_lineRestrict {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (c : ℂ) {r : ℝ} (hr : 0 < r)
    (hline : ∀ s : ℝ, c + (s : ℂ) * I ∈ U)
    (htube : ∀ (s : ℝ) (z : ℂ), z ∈ Metric.closedBall (c + (s : ℂ) * I) r → z ∈ U)
    {C : ℝ} {N : ℕ}
    (hbound : ∀ (s : ℝ) (z : ℂ), z ∈ Metric.closedBall (c + (s : ℂ) * I) r →
      ‖f z‖ ≤ C * (1 + |s|) ^ N) :
    Function.HasTemperateGrowth (fun s : ℝ => f (c + (s : ℂ) * I)) := by
  refine ⟨connes_contDiff_lineRestrict hU hf c hline, fun n => ?_⟩
  refine ⟨N, (n.factorial : ℝ) * C / r ^ n, fun s => ?_⟩
  have hnorm : ‖iteratedFDeriv ℝ n (fun s : ℝ => f (c + (s : ℂ) * I)) s‖
      = ‖iteratedDeriv n (fun s : ℝ => f (c + (s : ℂ) * I)) s‖ :=
    norm_iteratedFDeriv_eq_norm_iteratedDeriv
  have hval := connes_iteratedDeriv_lineRestrict hf c hline n s
  have hIn : ‖(I : ℂ) ^ n‖ = 1 := by
    rw [norm_pow, Complex.norm_I, one_pow]
  have hstep : ‖iteratedFDeriv ℝ n (fun s : ℝ => f (c + (s : ℂ) * I)) s‖
      = ‖iteratedDeriv n f (c + (s : ℂ) * I)‖ := by
    rw [hnorm, hval, norm_mul, hIn, one_mul]
  have hball : Metric.ball (c + (s : ℂ) * I) r ⊆ U := fun z hz =>
    htube s z (Metric.ball_subset_closedBall hz)
  have hclosed : Metric.closedBall (c + (s : ℂ) * I) r ⊆ U := fun z hz => htube s z hz
  have hdcc : DiffContOnCl ℂ f (Metric.ball (c + (s : ℂ) * I) r) := by
    refine ⟨hf.differentiableOn.mono hball, ?_⟩
    have hcl : closure (Metric.ball (c + (s : ℂ) * I) r)
        = Metric.closedBall (c + (s : ℂ) * I) r := closure_ball _ (ne_of_gt hr)
    rw [hcl]
    exact hf.continuousOn.mono hclosed
  have hsphere : ∀ z ∈ Metric.sphere (c + (s : ℂ) * I) r, ‖f z‖ ≤ C * (1 + |s|) ^ N := by
    intro z hz
    refine hbound s z ?_
    rw [Metric.mem_closedBall]
    exact le_of_eq (Metric.mem_sphere.mp hz)
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hdcc hsphere
  rw [hstep, Real.norm_eq_abs]
  calc ‖iteratedDeriv n f (c + (s : ℂ) * I)‖
      ≤ (n.factorial : ℝ) * (C * (1 + |s|) ^ N) / r ^ n := hcauchy
    _ = ((n.factorial : ℝ) * C / r ^ n) * (1 + |s|) ^ N := by ring

end

end GaloisForLFunctions.RHTower

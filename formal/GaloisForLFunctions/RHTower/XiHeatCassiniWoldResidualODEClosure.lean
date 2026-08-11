import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualUpperAbscissa
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldRequiredResidualContinuation
import Mathlib.Analysis.Complex.HasPrimitives

/-!
# Route-T residual first-order ODE closure

The upper-abscissa theorem turns summable residual variation into a holomorphic source.  The
structural next step is not direct pole cancellation: on the safe Euler half-plane, the residual
identity solves the valuation-one prime current for `-ζ'/ζ`.  After clearing the denominator this
becomes a first-order holomorphic ODE for zeta.  A solution of such an ODE cannot acquire an isolated
zero: a local integrating factor makes it constant, and analytic continuation propagates the zero.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- **Holomorphic first-order zero propagation.**  On an open preconnected complex domain, a
solution of `F' = -G F` is either nowhere zero or identically zero.  This local-primitive proof does
not assume a global primitive for `G`. -/
theorem false_of_analytic_firstOrderODE_zero_and_nonzero
    {U : Set ℂ} (hUopen : IsOpen U) (hUpre : IsPreconnected U)
    {F G : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U)
    (hODE : ∀ z ∈ U, deriv F z = -G z * F z)
    {z₀ z₁ : ℂ} (hz₀ : z₀ ∈ U) (hz₁ : z₁ ∈ U)
    (hzero : F z₀ = 0) (hnonzero : F z₁ ≠ 0) : False := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hUopen z₀ hz₀
  have hGball : DifferentiableOn ℂ G (Metric.ball z₀ r) :=
    hG.differentiableOn.mono hball
  obtain ⟨P, hP⟩ := hGball.isExactOn_ball
  have hPdiff : DifferentiableOn ℂ P (Metric.ball z₀ r) := fun z hz =>
    (hP z hz).differentiableAt.differentiableWithinAt
  have hPan : AnalyticOnNhd ℂ P (Metric.ball z₀ r) :=
    hPdiff.analyticOnNhd Metric.isOpen_ball
  let J : ℂ → ℂ := fun z => F z * Complex.exp (P z)
  have hJan : AnalyticOnNhd ℂ J (Metric.ball z₀ r) := by
    dsimp only [J]
    exact (hF.mono hball).mul hPan.cexp
  have hJderiv : ∀ z ∈ Metric.ball z₀ r, deriv J z = 0 := by
    intro z hz
    have hFz : HasDerivAt F (deriv F z) z :=
      (hF z (hball hz)).differentiableAt.hasDerivAt
    have hPz := hP z hz
    have hprod : HasDerivAt J
        (deriv F z * Complex.exp (P z) +
          F z * (Complex.exp (P z) * G z)) z := by
      dsimp only [J]
      exact hFz.mul hPz.cexp
    rw [hprod.deriv, hODE z (hball hz)]
    ring
  have hJconst : ∀ z ∈ Metric.ball z₀ r, J z = J z₀ := fun z hz =>
    Metric.isOpen_ball.is_const_of_deriv_eq_zero
      (convex_ball z₀ r).isPreconnected hJan.differentiableOn hJderiv
      hz (Metric.mem_ball_self hr)
  have hJzero : J z₀ = 0 := by dsimp only [J]; rw [hzero, zero_mul]
  have hlocalZero : ∀ z ∈ Metric.ball z₀ r, F z = 0 := by
    intro z hz
    have h := hJconst z hz
    rw [hJzero] at h
    dsimp only [J] at h
    exact (mul_eq_zero.mp h).resolve_right (Complex.exp_ne_zero _)
  have hevent : F =ᶠ[𝓝 z₀] (0 : ℂ → ℂ) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)] with z hz
    exact hlocalZero z hz
  have hglobal : Set.EqOn F (0 : ℂ → ℂ) U :=
    hF.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      hUpre hz₀ hevent
  exact hnonzero (hglobal hz₁)

/-- Convex sector used to bypass the artificial mesh-resolvent value at `s = 0`.  Choosing
`eta = Im rho` puts both `rho - 1` and a safe Euler point in this same sector. -/
def xiHeatCassiniWoldResidualODESector (eta : ℝ) : Set ℂ :=
  {s : ℂ | -(1 / 2 : ℝ) < s.re ∧ 0 < eta * s.im}

theorem isOpen_xiHeatCassiniWoldResidualODESector (eta : ℝ) :
    IsOpen (xiHeatCassiniWoldResidualODESector eta) := by
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const
      ((continuous_const : Continuous fun _ : ℂ => eta).mul Complex.continuous_im))

theorem convex_xiHeatCassiniWoldResidualODESector (eta : ℝ) :
    Convex ℝ (xiHeatCassiniWoldResidualODESector eta) := by
  intro x hx y hy a b ha hb hab
  change -(1 / 2 : ℝ) < x.re ∧ 0 < eta * x.im at hx
  change -(1 / 2 : ℝ) < y.re ∧ 0 < eta * y.im at hy
  change -(1 / 2 : ℝ) < (a • x + b • y).re ∧
    0 < eta * (a • x + b • y).im
  simp only [Complex.add_re, Complex.smul_re, Complex.add_im, Complex.smul_im,
    smul_eq_mul]
  by_cases ha0 : a = 0
  · subst a
    have hb1 : b = 1 := by linarith
    subst b
    simpa using hy
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    constructor
    · have hxmul := mul_lt_mul_of_pos_left hx.1 hapos
      have hymul := mul_le_mul_of_nonneg_left hy.1.le hb
      nlinarith
    · have hxmul : 0 < a * (eta * x.im) := mul_pos hapos hx.2
      have hymul : 0 ≤ b * (eta * y.im) := mul_nonneg hb hy.2.le
      rw [show eta * (a * x.im + b * y.im) =
          a * (eta * x.im) + b * (eta * y.im) by ring]
      linarith

theorem isPreconnected_xiHeatCassiniWoldResidualODESector (eta : ℝ) :
    IsPreconnected (xiHeatCassiniWoldResidualODESector eta) :=
  (convex_xiHeatCassiniWoldResidualODESector eta).isPreconnected

/-- Holomorphic coefficient predicted by the residual identity after solving for the first shifted
valuation-one prime current. -/
def xiHeatCassiniWoldResidualODECoefficient (s : ℂ) : ℂ :=
  xiHeatCassiniWoldResidualLowerHardyKernel (-Complex.I * s) +
    xiHeatCassiniLogMeshLaplaceContinuation s +
    xiHeatCassiniWoldLaplaceHolonomyCounterterm s +
    3 * xiPrimeLogDirichletContinuation (s + 2) -
    3 * xiPrimeLogDirichletContinuation (s + 3) +
    xiPrimeLogDirichletContinuation (s + 4) +
    xiPrimeLogHigherValuation (s + 1)

/-- On the safe Euler half-plane, the exact residual decomposition is the cleared first-order ODE
`-ζ'(s+1) = G(s) ζ(s+1)`. -/
theorem neg_deriv_riemannZeta_shift_eq_residualODECoefficient_mul
    {s : ℂ} (hs : 0 < s.re)
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    -deriv riemannZeta (s + 1) =
      xiHeatCassiniWoldResidualODECoefficient s * riemannZeta (s + 1) := by
  have hres :=
    xiHeatCassiniWoldResidualLaplaceContinuation_eq_lowerHardy hs hcritical
  have hQ : xiPrimeLogDirichletContinuation (s + 1) =
      xiHeatCassiniWoldResidualLowerHardyKernel (-Complex.I * s) +
        xiHeatCassiniLogMeshLaplaceContinuation s +
        xiHeatCassiniWoldLaplaceHolonomyCounterterm s +
        3 * xiPrimeLogDirichletContinuation (s + 2) -
        3 * xiPrimeLogDirichletContinuation (s + 3) +
        xiPrimeLogDirichletContinuation (s + 4) := by
    rw [xiHeatCassiniWoldResidualLaplaceContinuation,
      xiHeatCassiniWoldLaplaceContinuation] at hres
    linear_combination hres
  have hflux : infinitePrimeFlux (s + 1) =
      xiHeatCassiniWoldResidualODECoefficient s := by
    rw [xiPrimeLogDirichletContinuation] at hQ
    rw [xiHeatCassiniWoldResidualODECoefficient]
    linear_combination hQ
  have hzeta : riemannZeta (s + 1) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  rw [infinitePrimeFlux, logDeriv_apply] at hflux
  calc
    -deriv riemannZeta (s + 1) =
        (-(deriv riemannZeta (s + 1) / riemannZeta (s + 1))) *
          riemannZeta (s + 1) := by field_simp
    _ = xiHeatCassiniWoldResidualODECoefficient s * riemannZeta (s + 1) := by
      rw [hflux]

/-- The original ordered log-mesh current is holomorphic throughout its safe half-plane. -/
theorem differentiableAt_xiHeatCassiniLogMeshLaplaceCurrent
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ xiHeatCassiniLogMeshLaplaceCurrent s := by
  let sigma : ℝ := s.re / 2
  let U : Set ℂ := {w : ℂ | sigma < w.re}
  have hsigma : 0 < sigma := by dsimp only [sigma]; linarith
  have hUopen : IsOpen U :=
    isOpen_lt continuous_const Complex.continuous_re
  have hsU : s ∈ U := by
    change sigma < s.re
    dsimp only [sigma]
    linarith
  have hmajor : Summable (fun N : ℕ =>
      ‖xiHeatCassiniLogMeshLaplaceAtom (sigma : ℂ) N‖) :=
    summable_norm_iff.mpr (summable_xiHeatCassiniLogMeshLaplaceAtom
      (s := (sigma : ℂ)) (by simpa using hsigma))
  have hterm : ∀ N : ℕ,
      DifferentiableOn ℂ (xiHeatCassiniLogMeshLaplaceAtom · N) U := by
    intro N w hw
    unfold xiHeatCassiniLogMeshLaplaceAtom
    unfold xiHeatCassiniOrderedPrimeLaplacePhase
    unfold xiHeatCassiniOrderedPrimeComplexNegativePhase
    fun_prop
  have hbound : ∀ N : ℕ, ∀ w ∈ U,
      ‖xiHeatCassiniLogMeshLaplaceAtom w N‖ ≤
        ‖xiHeatCassiniLogMeshLaplaceAtom (sigma : ℂ) N‖ := by
    intro N w hw
    have hsigw : sigma ≤ w.re := by exact hw.le
    have hy : 0 < xiMassNthPrimeLogHeight (N + 1) :=
      xiMassNthPrimeLogHeight_pos (N + 1)
    rw [xiHeatCassiniLogMeshLaplaceAtom, xiHeatCassiniLogMeshLaplaceAtom,
      norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (xiHeatCassiniOrderedPrimeLogGap_nonneg N),
      norm_xiHeatCassiniOrderedPrimeLaplacePhase,
      norm_xiHeatCassiniOrderedPrimeLaplacePhase]
    apply mul_le_mul_of_nonneg_left _
      (xiHeatCassiniOrderedPrimeLogGap_nonneg N)
    apply Real.exp_le_exp.mpr
    simp only [Complex.ofReal_re]
    nlinarith
  have hdiff := Complex.differentiableOn_tsum_of_summable_norm
    hmajor hterm hUopen hbound
  change DifferentiableAt ℂ
    (fun w : ℂ => ∑' N : ℕ, xiHeatCassiniLogMeshLaplaceAtom w N) s
  exact hdiff.differentiableAt (hUopen.mem_nhds hsU)

theorem analyticOnNhd_xiHeatCassiniLogMeshLaplaceCurrent_safe :
    AnalyticOnNhd ℂ xiHeatCassiniLogMeshLaplaceCurrent {s : ℂ | 0 < s.re} := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticOnNhd _ hopen
  intro s hs
  exact (differentiableAt_xiHeatCassiniLogMeshLaplaceCurrent hs).differentiableWithinAt

theorem analyticOnNhd_xiHeatCassiniLogMeshLaplaceContinuation_safe
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    AnalyticOnNhd ℂ xiHeatCassiniLogMeshLaplaceContinuation {s : ℂ | 0 < s.re} := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  apply AnalyticOnNhd.congr hopen analyticOnNhd_xiHeatCassiniLogMeshLaplaceCurrent_safe
  intro s hs
  exact (xiHeatCassiniLogMeshLaplaceContinuation_eq_current hs hcritical).symm

/-- Critical mesh energy makes the canonical mesh continuation holomorphic at every nonzero point
of `Re s > -1/2`, joining the safe current to the critical half-strip. -/
theorem analyticAt_xiHeatCassiniLogMeshLaplaceContinuation_of_criticalEnergy_full
    {s : ℂ} (hsleft : -(1 / 2 : ℝ) < s.re) (hs0 : s ≠ 0)
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    AnalyticAt ℂ xiHeatCassiniLogMeshLaplaceContinuation s := by
  by_cases hsright : s.re ≤ 0
  · exact analyticAt_xiHeatCassiniLogMeshLaplaceContinuation_of_criticalEnergy
      hsleft hsright hs0 hcritical
  · have hspos : 0 < s.re := lt_of_not_ge hsright
    exact analyticOnNhd_xiHeatCassiniLogMeshLaplaceContinuation_safe hcritical s hspos

theorem analyticOnNhd_xiPrimeLogDirichletContinuation_one_lt :
    AnalyticOnNhd ℂ xiPrimeLogDirichletContinuation {s : ℂ | 1 < s.re} := by
  have hopen : IsOpen {s : ℂ | 1 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticOnNhd _ hopen
  intro s hs
  exact (differentiableAt_xiPrimeLogDirichletContinuation_of_one_lt_re hs).differentiableWithinAt

theorem analyticOnNhd_xiPrimeLogHigherValuation_half :
    AnalyticOnNhd ℂ xiPrimeLogHigherValuation {s : ℂ | 1 / 2 < s.re} := by
  have hopen : IsOpen {s : ℂ | 1 / 2 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  exact differentiableOn_xiPrimeLogHigherValuation_halfPlane.analyticOnNhd hopen

/-- A holomorphic residual source on the critical source strip makes the ODE coefficient
holomorphic on every nonreal sector of the translated critical Laplace half-plane. -/
theorem analyticOnNhd_xiHeatCassiniWoldResidualODECoefficient
    {eta : ℝ}
    (hsource : AnalyticOnNhd ℂ xiHeatCassiniWoldResidualLowerHardyKernel
      {z : ℂ | z.im < 1 / 2})
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    AnalyticOnNhd ℂ xiHeatCassiniWoldResidualODECoefficient
      (xiHeatCassiniWoldResidualODESector eta) := by
  intro s hs
  change -(1 / 2 : ℝ) < s.re ∧ 0 < eta * s.im at hs
  have harg : (-Complex.I * s).im < 1 / 2 := by
    simp only [Complex.mul_im, Complex.neg_re, Complex.I_re, neg_zero, zero_mul,
      Complex.neg_im, Complex.I_im, neg_mul, one_mul, zero_add]
    linarith
  have hH : AnalyticAt ℂ
      (fun w : ℂ => xiHeatCassiniWoldResidualLowerHardyKernel (-Complex.I * w)) s :=
    by
      change AnalyticAt ℂ
        (xiHeatCassiniWoldResidualLowerHardyKernel ∘ fun w : ℂ => -Complex.I * w) s
      exact (hsource (-Complex.I * s) harg).comp
        (show AnalyticAt ℂ (fun w : ℂ => -Complex.I * w) s by fun_prop)
  have hs0 : s ≠ 0 := by
    intro hs0
    subst s
    simp at hs
  have hmesh : AnalyticAt ℂ xiHeatCassiniLogMeshLaplaceContinuation s :=
    analyticAt_xiHeatCassiniLogMeshLaplaceContinuation_of_criticalEnergy_full
      hs.1 hs0 hcritical
  have hhol : AnalyticAt ℂ xiHeatCassiniWoldLaplaceHolonomyCounterterm s :=
    analyticAt_xiHeatCassiniWoldLaplaceHolonomyCounterterm s
  have hs2 : 1 < (s + 2).re := by simp; linarith
  have hs3 : 1 < (s + 3).re := by simp; linarith
  have hs4 : 1 < (s + 4).re := by simp; linarith
  have hs1half : 1 / 2 < (s + 1).re := by simp; linarith
  have hQ2 : AnalyticAt ℂ
      (fun w : ℂ => xiPrimeLogDirichletContinuation (w + 2)) s :=
    by
      change AnalyticAt ℂ
        (xiPrimeLogDirichletContinuation ∘ fun w : ℂ => w + 2) s
      exact AnalyticAt.comp (f := fun w : ℂ => w + 2) (x := s)
        (analyticOnNhd_xiPrimeLogDirichletContinuation_one_lt (s + 2) hs2)
        (show AnalyticAt ℂ (fun w : ℂ => w + 2) s by fun_prop)
  have hQ3 : AnalyticAt ℂ
      (fun w : ℂ => xiPrimeLogDirichletContinuation (w + 3)) s :=
    by
      change AnalyticAt ℂ
        (xiPrimeLogDirichletContinuation ∘ fun w : ℂ => w + 3) s
      exact AnalyticAt.comp (f := fun w : ℂ => w + 3) (x := s)
        (analyticOnNhd_xiPrimeLogDirichletContinuation_one_lt (s + 3) hs3)
        (show AnalyticAt ℂ (fun w : ℂ => w + 3) s by fun_prop)
  have hQ4 : AnalyticAt ℂ
      (fun w : ℂ => xiPrimeLogDirichletContinuation (w + 4)) s :=
    by
      change AnalyticAt ℂ
        (xiPrimeLogDirichletContinuation ∘ fun w : ℂ => w + 4) s
      exact AnalyticAt.comp (f := fun w : ℂ => w + 4) (x := s)
        (analyticOnNhd_xiPrimeLogDirichletContinuation_one_lt (s + 4) hs4)
        (show AnalyticAt ℂ (fun w : ℂ => w + 4) s by fun_prop)
  have hHigher : AnalyticAt ℂ
      (fun w : ℂ => xiPrimeLogHigherValuation (w + 1)) s :=
    by
      change AnalyticAt ℂ
        (xiPrimeLogHigherValuation ∘ fun w : ℂ => w + 1) s
      exact AnalyticAt.comp (f := fun w : ℂ => w + 1) (x := s)
        (analyticOnNhd_xiPrimeLogHigherValuation_half (s + 1) hs1half)
        (show AnalyticAt ℂ (fun w : ℂ => w + 1) s by fun_prop)
  unfold xiHeatCassiniWoldResidualODECoefficient
  exact (((((hH.add hmesh).add hhol).add (analyticAt_const.mul hQ2)).sub
    (analyticAt_const.mul hQ3)).add hQ4).add hHigher

end

end RHTower

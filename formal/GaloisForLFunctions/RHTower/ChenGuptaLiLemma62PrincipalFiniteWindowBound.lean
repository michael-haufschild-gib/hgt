import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalCriticalIntegrability

/-!
# Chen--Gupta--Li Lemma 6.2, principal branch: the finite critical-line window bound

On any symmetric window `|u| ≤ R` of the critical line, the integral of the principal finite
reflected integrand is bounded by a closed Mellin constant times `N^{1/2}` times the integral of the
trivial-character Dirichlet head at the reflected point.  The regularized functional multiplier and
the finite Euler correction contribute exactly modulus one there.  The statement is free of any
source regime: the regimes only choose the radius and the cutoff.
-/

open Complex MeasureTheory Filter Set
open scoped LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- The exact norm of the principal finite integrand on the critical line. -/
theorem norm_cglLemma62PrincipalRegularizedFiniteContourIntegrand_critical_eq
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) (t : ℝ) (M : ℕ)
    (u : ℝ) :
    ‖cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M ((1 / 2 : ℂ) + (u : ℂ) * I)‖
      = ‖cglLemma62MellinTransform w ((1 / 2 : ℂ) + (u : ℂ) * I)‖ *
          (N.value : ℝ) ^ (1 / 2 : ℝ) *
          ‖cglLemma62DirichletHead (1 : DirichletCharacter ℂ Q.value) M
            (1 - ((1 / 2 : ℂ) + (u : ℂ) * I) + (t : ℂ) * I)‖ := by
  unfold cglLemma62PrincipalRegularizedFiniteContourIntegrand
  have hre1 : ((1 / 2 : ℂ) + (u : ℂ) * I - (t : ℂ) * I).re = 1 / 2 := by simp
  have hN : ‖(N.value : ℂ) ^ ((1 / 2 : ℂ) + (u : ℂ) * I)‖ = (N.value : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_natCast_cpow_of_pos N.positive]; simp
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hN,
    norm_cglLemma62PrincipalRegularizedFunctionalFactor_critical hre1,
    norm_cglLemma62PrincipalEulerCorrectionAt_critical Q hre1]
  ring

/-- **Principal finite critical-line window bound.**  For every radius `R ≥ 0` and cutoff `M`,
`‖∫_{−R}^{R} F(1/2 + iu) du‖ ≤ C · N^{1/2} · ∫_{−R}^{R} ‖D_M(1/2 − i(u − t))‖ du` with
`C = cglLemma62MellinLineDecayBudget w (1/2) 0`. -/
theorem cglLemma62_principal_finiteCritical_window_bound
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) (t : ℝ) (M : ℕ)
    {R : ℝ} (hR : 0 ≤ R) :
    ‖∫ u : ℝ in -R..R,
        cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M ((1 / 2 : ℂ) + (u : ℂ) * I)‖
      ≤ cglLemma62MellinLineDecayBudget w (1 / 2) 0 * (N.value : ℝ) ^ (1 / 2 : ℝ) *
          ∫ u : ℝ in -R..R,
            ‖cglLemma62DirichletHead (1 : DirichletCharacter ℂ Q.value) M
              (1 - ((1 / 2 : ℂ) + (u : ℂ) * I) + (t : ℂ) * I)‖ := by
  set C : ℝ := cglLemma62MellinLineDecayBudget w (1 / 2) 0 with hCdef
  have hab : -R ≤ R := by linarith
  have hcont := cglLemma62PrincipalRegularizedFinite_critical_continuous w N Q t M
  have harg : Continuous (fun u : ℝ => 1 - ((1 / 2 : ℂ) + (u : ℂ) * I) + (t : ℂ) * I) := by
    fun_prop
  have hhead : Continuous (fun u : ℝ =>
      cglLemma62DirichletHead (1 : DirichletCharacter ℂ Q.value) M
        (1 - ((1 / 2 : ℂ) + (u : ℂ) * I) + (t : ℂ) * I)) :=
    (cglLemma62DirichletHead_differentiable (1 : DirichletCharacter ℂ Q.value) M).continuous.comp harg
  have hfiniteInt : IntervalIntegrable (fun u : ℝ =>
      ‖cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M ((1 / 2 : ℂ) + (u : ℂ) * I)‖)
      volume (-R) R := hcont.norm.intervalIntegrable _ _
  have hmajorInt : IntervalIntegrable (fun u : ℝ =>
      C * (N.value : ℝ) ^ (1 / 2 : ℝ) *
        ‖cglLemma62DirichletHead (1 : DirichletCharacter ℂ Q.value) M
          (1 - ((1 / 2 : ℂ) + (u : ℂ) * I) + (t : ℂ) * I)‖) volume (-R) R :=
    ((continuous_const.mul continuous_const).mul hhead.norm).intervalIntegrable _ _
  have hpoint : ∀ u ∈ Set.Icc (-R) R,
      ‖cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M ((1 / 2 : ℂ) + (u : ℂ) * I)‖
        ≤ C * (N.value : ℝ) ^ (1 / 2 : ℝ) *
          ‖cglLemma62DirichletHead (1 : DirichletCharacter ℂ Q.value) M
            (1 - ((1 / 2 : ℂ) + (u : ℂ) * I) + (t : ℂ) * I)‖ := by
    intro u _
    have hMellin : ‖cglLemma62MellinTransform w ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤ C := by
      have := cglLemma62_mellinTransform_vertical_rapidDecay w (1 / 2) 0 u
      rw [← hCdef] at this
      simpa using this
    rw [norm_cglLemma62PrincipalRegularizedFiniteContourIntegrand_critical_eq]
    gcongr
  calc ‖∫ u : ℝ in -R..R,
        cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M ((1 / 2 : ℂ) + (u : ℂ) * I)‖
      ≤ ∫ u : ℝ in -R..R,
          ‖cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M
            ((1 / 2 : ℂ) + (u : ℂ) * I)‖ := intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ u : ℝ in -R..R, C * (N.value : ℝ) ^ (1 / 2 : ℝ) *
          ‖cglLemma62DirichletHead (1 : DirichletCharacter ℂ Q.value) M
            (1 - ((1 / 2 : ℂ) + (u : ℂ) * I) + (t : ℂ) * I)‖ :=
        intervalIntegral.integral_mono_on hab hfiniteInt hmajorInt hpoint
    _ = C * (N.value : ℝ) ^ (1 / 2 : ℝ) *
          ∫ u : ℝ in -R..R,
            ‖cglLemma62DirichletHead (1 : DirichletCharacter ℂ Q.value) M
              (1 - ((1 / 2 : ℂ) + (u : ℂ) * I) + (t : ℂ) * I)‖ := by
        rw [intervalIntegral.integral_const_mul]

end

end RHTower

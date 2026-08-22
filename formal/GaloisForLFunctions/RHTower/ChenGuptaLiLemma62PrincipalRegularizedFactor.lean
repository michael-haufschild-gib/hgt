import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalReflectedSplit

/-!
# Chen--Gupta--Li Lemma 6.2: regular principal functional multiplier

The `Gammaℝ` quotient used for the initial principal reflection is exact on
the left line, but its totalized denominator cannot provide strip holomorphy
through the crossing `z = 0`.  The classical zeta functional equation gives
an equivalent Gamma--cosine multiplier there.  Its Gamma argument stays in
the positive half-plane throughout CGL's displacement strip.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- The regular Gamma--cosine form of the zeta functional multiplier
`ζ(z) = χ_reg(z) ζ(1-z)`. -/
def cglLemma62PrincipalRegularizedFunctionalFactor (z : ℂ) : ℂ :=
  2 * ((2 * Real.pi : ℝ) : ℂ) ^ (-(1 - z)) * Complex.Gamma (1 - z) *
    Complex.cos (Real.pi * (1 - z) / 2)

/-- The regular principal functional multiplier is holomorphic throughout
CGL's full left-to-critical displacement strip. -/
theorem cglLemma62PrincipalRegularizedFunctionalFactor_analyticAt
    {z : ℂ} (hz : z.re ≤ 1 / 2) :
    AnalyticAt ℂ cglLemma62PrincipalRegularizedFunctionalFactor z := by
  have hbase : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos))
  have hpow : AnalyticAt ℂ
      (fun u : ℂ => ((2 * Real.pi : ℝ) : ℂ) ^ (-(1 - u))) z := by
    have hpowdiff : Differentiable ℂ
        (fun u : ℂ => ((2 * Real.pi : ℝ) : ℂ) ^ (-(1 - u))) := by
      intro u
      exact (((differentiableAt_const (c := (1 : ℂ)) (x := u)).sub
        (differentiableAt_id (x := u))).neg).const_cpow (Or.inl hbase)
    exact (hpowdiff.differentiableOn.analyticOnNhd isOpen_univ) z (mem_univ z)
  have harg : 0 < (1 - z).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hgamma : AnalyticAt ℂ (fun u : ℂ => Complex.Gamma (1 - u)) z := by
    have hinner : AnalyticAt ℂ (fun u : ℂ => 1 - u) z :=
      analyticAt_const.sub analyticAt_id
    simpa only [Function.comp_def] using
      (HTGeometry.analyticAt_Gamma_of_re_pos harg).comp hinner
  have hcos : AnalyticAt ℂ
      (fun u : ℂ => Complex.cos (Real.pi * (1 - u) / 2)) z := by
    fun_prop
  unfold cglLemma62PrincipalRegularizedFunctionalFactor
  exact ((analyticAt_const.mul hpow).mul hgamma).mul hcos

private theorem cglLemma62PrincipalRightPoint_ne_neg_nat (t v : ℝ) (n : ℕ) :
    cglLemma62PrincipalRightPoint t v ≠ -(n : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simp [cglLemma62PrincipalRightPoint] at hre
  linarith

private theorem cglLemma62PrincipalRightPoint_ne_one (t v : ℝ) :
    cglLemma62PrincipalRightPoint t v ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  simp [cglLemma62PrincipalRightPoint] at hre

/-- On CGL's literal left principal line, the regular multiplier is exactly
the zeta functional equation. -/
theorem cglLemma62_principal_zeta_left_eq_regularized_reflection (t v : ℝ) :
    riemannZeta (cglLemma62PrincipalLeftPoint t v) =
      cglLemma62PrincipalRegularizedFunctionalFactor
        (cglLemma62PrincipalLeftPoint t v) *
          riemannZeta (cglLemma62PrincipalRightPoint t v) := by
  have hforward : (1 : ℂ) - cglLemma62PrincipalLeftPoint t v =
      cglLemma62PrincipalRightPoint t v := by
    unfold cglLemma62PrincipalLeftPoint cglLemma62PrincipalRightPoint
    push_cast
    ring
  have hback : (1 : ℂ) - cglLemma62PrincipalRightPoint t v =
      cglLemma62PrincipalLeftPoint t v := by
    unfold cglLemma62PrincipalLeftPoint cglLemma62PrincipalRightPoint
    push_cast
    ring
  have hfe := riemannZeta_one_sub
    (s := cglLemma62PrincipalRightPoint t v)
    (cglLemma62PrincipalRightPoint_ne_neg_nat t v)
    (cglLemma62PrincipalRightPoint_ne_one t v)
  rw [hback] at hfe
  simpa [cglLemma62PrincipalRegularizedFunctionalFactor, ← hforward] using hfe

end

end RHTower

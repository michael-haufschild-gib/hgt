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

/-- The regular Gamma--cosine multiplier and the existing `Gammaℝ` quotient
agree on CGL's literal left line.  This is obtained by cancellation against
the nonvanishing right-half-plane zeta value, not postulated. -/
theorem cglLemma62_principal_regularizedFactor_eq_zetaChi (t v : ℝ) :
    cglLemma62PrincipalRegularizedFunctionalFactor
      (cglLemma62PrincipalLeftPoint t v) =
        zetaChi (cglLemma62PrincipalLeftPoint t v) := by
  have hforward : (1 : ℂ) - cglLemma62PrincipalLeftPoint t v =
      cglLemma62PrincipalRightPoint t v := by
    unfold cglLemma62PrincipalLeftPoint cglLemma62PrincipalRightPoint
    push_cast
    ring
  have hleft0 : cglLemma62PrincipalLeftPoint t v ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [cglLemma62PrincipalLeftPoint] at hre
  have hleft1 : cglLemma62PrincipalLeftPoint t v ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [cglLemma62PrincipalLeftPoint] at hre
    norm_num at hre
  have hgamma : Gammaℝ (1 - cglLemma62PrincipalLeftPoint t v) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    rw [hforward]
    simp [cglLemma62PrincipalRightPoint]
  have hchi : riemannZeta (cglLemma62PrincipalLeftPoint t v) =
      zetaChi (cglLemma62PrincipalLeftPoint t v) *
        riemannZeta (cglLemma62PrincipalRightPoint t v) := by
    rw [← hforward]
    exact zeta_eq_zetaChi_mul hleft0 hleft1 hgamma
  have hregular := cglLemma62_principal_zeta_left_eq_regularized_reflection t v
  have hright : riemannZeta (cglLemma62PrincipalRightPoint t v) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    simp [cglLemma62PrincipalRightPoint]
  apply mul_right_cancel₀ hright
  calc
    cglLemma62PrincipalRegularizedFunctionalFactor
        (cglLemma62PrincipalLeftPoint t v) *
        riemannZeta (cglLemma62PrincipalRightPoint t v) =
      riemannZeta (cglLemma62PrincipalLeftPoint t v) := hregular.symm
    _ = zetaChi (cglLemma62PrincipalLeftPoint t v) *
        riemannZeta (cglLemma62PrincipalRightPoint t v) := hchi

/-- Entire regularization of `sin z / z`, represented by its divided
difference at zero. -/
def cglLemma62PrincipalSineOverZ (z : ℂ) : ℂ :=
  dslope Complex.sin 0 z

/-- The sine quotient is entire, including its value at zero. -/
theorem cglLemma62PrincipalSineOverZ_analyticAt (z : ℂ) :
    AnalyticAt ℂ cglLemma62PrincipalSineOverZ z := by
  unfold cglLemma62PrincipalSineOverZ
  exact analyticAt_dslope_of_analyticAt Complex.analyticAt_sin Complex.analyticAt_sin

/-- The zeta functional multiplier after its simple zero at the reflected
trivial-character pole has been divided out. -/
def cglLemma62PrincipalPoleClearedFunctionalFactor (z : ℂ) : ℂ :=
  -(Real.pi : ℂ) * ((2 * Real.pi : ℝ) : ℂ) ^ (-(1 - z)) *
    Complex.Gamma (1 - z) *
      cglLemma62PrincipalSineOverZ ((Real.pi : ℂ) * z / 2)

/-- The pole-cleared principal multiplier is analytic across the full
displacement strip, including the crossing `z=0`. -/
theorem cglLemma62PrincipalPoleClearedFunctionalFactor_analyticAt
    {z : ℂ} (hz : z.re ≤ 1 / 2) :
    AnalyticAt ℂ cglLemma62PrincipalPoleClearedFunctionalFactor z := by
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
  have hsine : AnalyticAt ℂ
      (fun u : ℂ => cglLemma62PrincipalSineOverZ ((Real.pi : ℂ) * u / 2)) z := by
    have hinner : AnalyticAt ℂ (fun u : ℂ => (Real.pi : ℂ) * u / 2) z := by
      fun_prop
    have hcomp := AnalyticAt.comp
      (g := cglLemma62PrincipalSineOverZ)
      (f := fun u : ℂ => (Real.pi : ℂ) * u / 2)
      (cglLemma62PrincipalSineOverZ_analyticAt ((Real.pi : ℂ) * z / 2)) hinner
    simpa only [Function.comp_def] using hcomp
  unfold cglLemma62PrincipalPoleClearedFunctionalFactor
  exact (((analyticAt_const.mul hpow).mul hgamma).mul hsine)

/-- The regular multiplier carries exactly one zero at the reflected trivial
`L`-pole; this factorization exposes its analytic quotient. -/
theorem cglLemma62PrincipalRegularizedFunctionalFactor_eq_neg_mul_poleCleared
    (z : ℂ) :
    cglLemma62PrincipalRegularizedFunctionalFactor z =
      (-z) * cglLemma62PrincipalPoleClearedFunctionalFactor z := by
  have htrig : Complex.cos (Real.pi * (1 - z) / 2) =
      Complex.sin ((Real.pi : ℂ) * z / 2) := by
    have harg : Real.pi * (1 - z) / 2 =
        (Real.pi : ℂ) / 2 - (Real.pi : ℂ) * z / 2 := by
      ring
    rw [harg, Complex.cos_sub, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
    ring
  have hsine : ((Real.pi : ℂ) * z / 2) *
      cglLemma62PrincipalSineOverZ ((Real.pi : ℂ) * z / 2) =
        Complex.sin ((Real.pi : ℂ) * z / 2) := by
    simpa [cglLemma62PrincipalSineOverZ, smul_eq_mul] using
      (sub_smul_dslope_of_zero Complex.sin_zero ((Real.pi : ℂ) * z / 2))
  unfold cglLemma62PrincipalRegularizedFunctionalFactor
    cglLemma62PrincipalPoleClearedFunctionalFactor
  rw [htrig, ← hsine]
  ring

end

end RHTower

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalReflectedEuler
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62FiniteContour

/-!
# Chen--Gupta--Li Lemma 6.2: regularized principal reflected contours

This gives analytic finite and complementary-tail continuations for CGL's
principal reflected branch.  The tail uses the pole-cleared trivial
`L`-function, so the zero of the regular functional multiplier cancels its
sole pole exactly at the contour crossing.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- The principal finite Dirichlet-polynomial carrier continued from CGL's
reflected left line across the critical displacement strip. -/
def cglLemma62PrincipalRegularizedFiniteContourIntegrand
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : ℕ) (s : ℂ) : ℂ :=
  cglLemma62MellinTransform w s * (N.value : ℂ) ^ s *
    cglLemma62PrincipalRegularizedFunctionalFactor (s - (t : ℂ) * I) *
      cglLemma62PrincipalEulerCorrectionAt Q (s - (t : ℂ) * I) *
        cglLemma62DirichletHead (1 : DirichletCharacter ℂ Q.value) M
          (1 - s + (t : ℂ) * I)

/-- The principal complementary-tail carrier with the trivial `L`-pole
cleared before the contour crosses it. -/
def cglLemma62PrincipalRegularizedTailContourIntegrand
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : ℕ) (s : ℂ) : ℂ :=
  cglLemma62MellinTransform w s * (N.value : ℂ) ^ s *
    cglLemma62PrincipalEulerCorrectionAt Q (s - (t : ℂ) * I) *
      (cglLemma62PrincipalPoleClearedFunctionalFactor (s - (t : ℂ) * I) *
        DirichletCharacter.LFunctionTrivChar₁ Q.value (1 - s + (t : ℂ) * I) -
        cglLemma62PrincipalRegularizedFunctionalFactor (s - (t : ℂ) * I) *
          cglLemma62DirichletHead (1 : DirichletCharacter ℂ Q.value) M
            (1 - s + (t : ℂ) * I))

private theorem cglLemma62Principal_line_shift_eq_left (t v : ℝ) :
    ((-1 : ℂ) + (v : ℂ) * I) - (t : ℂ) * I =
      cglLemma62PrincipalLeftPoint t v := by
  unfold cglLemma62PrincipalLeftPoint
  push_cast
  ring

private theorem cglLemma62Principal_line_right_eq (t v : ℝ) :
    1 - ((-1 : ℂ) + (v : ℂ) * I) + (t : ℂ) * I =
      cglLemma62PrincipalRightPoint t v := by
  unfold cglLemma62PrincipalRightPoint
  push_cast
  ring

/-- The regularized finite carrier agrees exactly with CGL's original finite
reflected integrand on the literal left line. -/
theorem cglLemma62PrincipalRegularizedFiniteContourIntegrand_eq_line
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t v : ℝ) (M : ℕ) :
    cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M
      ((-1 : ℂ) + (v : ℂ) * I) =
      cglLemma62PrincipalReflectedFiniteIntegrand w N Q t M v := by
  unfold cglLemma62PrincipalRegularizedFiniteContourIntegrand
    cglLemma62PrincipalReflectedFiniteIntegrand
  rw [cglLemma62Principal_line_shift_eq_left, cglLemma62Principal_line_right_eq,
    cglLemma62_principal_regularizedFactor_eq_zetaChi,
    cglLemma62PrincipalEulerCorrectionAt_eq_line]

private theorem cglLemma62Principal_regularizedPoleCleared_mul_L1_eq_regular_mul_L
    (Q : CGLPositiveModulus) (t v : ℝ) :
    cglLemma62PrincipalPoleClearedFunctionalFactor (cglLemma62PrincipalLeftPoint t v) *
      DirichletCharacter.LFunctionTrivChar₁ Q.value
        (cglLemma62PrincipalRightPoint t v) =
      cglLemma62PrincipalRegularizedFunctionalFactor (cglLemma62PrincipalLeftPoint t v) *
        DirichletCharacter.LFunctionTrivChar Q.value
          (cglLemma62PrincipalRightPoint t v) := by
  letI : NeZero Q.value := ⟨Nat.ne_of_gt Q.positive⟩
  have hrightne : cglLemma62PrincipalRightPoint t v ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [cglLemma62PrincipalRightPoint] at hre
  have hfactor :=
    cglLemma62PrincipalRegularizedFunctionalFactor_eq_neg_mul_poleCleared
      (cglLemma62PrincipalLeftPoint t v)
  have hscalar : cglLemma62PrincipalRightPoint t v - 1 =
      -cglLemma62PrincipalLeftPoint t v := by
    unfold cglLemma62PrincipalRightPoint cglLemma62PrincipalLeftPoint
    push_cast
    ring
  rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hrightne, hscalar,
    hfactor]
  ring

/-- The pole-cleared tail continuation restricts exactly to CGL's literal
complementary principal Dirichlet tail on the initial left line. -/
theorem cglLemma62PrincipalRegularizedTailContourIntegrand_eq_line
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t v : ℝ) (M : ℕ) :
    cglLemma62PrincipalRegularizedTailContourIntegrand w N Q t M
      ((-1 : ℂ) + (v : ℂ) * I) =
      cglLemma62PrincipalReflectedTailIntegrand w N Q t M v := by
  unfold cglLemma62PrincipalRegularizedTailContourIntegrand
    cglLemma62PrincipalReflectedTailIntegrand
  rw [cglLemma62Principal_line_shift_eq_left, cglLemma62Principal_line_right_eq,
    cglLemma62PrincipalEulerCorrectionAt_eq_line,
    cglLemma62Principal_regularizedPoleCleared_mul_L1_eq_regular_mul_L,
    cglLemma62_principal_regularizedFactor_eq_zetaChi]
  have hsplit := cglLemma62_principal_right_lfunction_eq_head_add_tail Q t v M
  rw [hsplit]
  ring

private theorem cglLemma62PrincipalRegularizedContour_shift_mapsTo (t : ℝ) :
    Set.MapsTo (fun z : ℂ => z - (t : ℂ) * I)
      (GaloisForLFunctions.HTGeometry.verticalStrip (-1) (1 / 2))
      (GaloisForLFunctions.HTGeometry.verticalStrip (-1) (1 / 2)) := by
  intro z hz
  change (-1 : ℝ) ≤ (z - (t : ℂ) * I).re ∧
    (z - (t : ℂ) * I).re ≤ (1 / 2 : ℝ)
  simpa [GaloisForLFunctions.HTGeometry.verticalStrip] using hz

/-- The principal finite reflected carrier is holomorphic throughout CGL's
left-to-critical displacement strip. -/
theorem cglLemma62PrincipalRegularizedFiniteContourIntegrand_differentiableOn
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : ℕ) :
    DifferentiableOn ℂ (cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M)
      (GaloisForLFunctions.HTGeometry.verticalStrip (-1) (1 / 2)) := by
  intro s hs
  let S := GaloisForLFunctions.HTGeometry.verticalStrip (-1) (1 / 2)
  have hshift := cglLemma62PrincipalRegularizedContour_shift_mapsTo t
  have hdshift : DifferentiableWithinAt ℂ (fun z : ℂ => z - (t : ℂ) * I) S s :=
    (differentiableAt_id.sub (differentiableAt_const _)).differentiableWithinAt
  have hH : DifferentiableWithinAt ℂ (cglLemma62MellinTransform w) S s := by
    exact (cglLemma62_mellinTransform_analyticOnNhd w s (mem_univ s)).differentiableAt.differentiableWithinAt
  have hNne : (N.value : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt N.positive)
  have hN : DifferentiableWithinAt ℂ (fun z : ℂ => (N.value : ℂ) ^ z) S s :=
    (differentiableAt_id.const_cpow (Or.inl hNne)).differentiableWithinAt
  have hF : DifferentiableWithinAt ℂ
      (fun z : ℂ => cglLemma62PrincipalRegularizedFunctionalFactor (z - (t : ℂ) * I)) S s := by
    simpa only [Function.comp_def] using
      DifferentiableAt.comp_differentiableWithinAt s
        (cglLemma62PrincipalRegularizedFunctionalFactor_analyticAt (hshift hs).2).differentiableAt
        hdshift
  have hE : DifferentiableWithinAt ℂ
      (fun z : ℂ => cglLemma62PrincipalEulerCorrectionAt Q (z - (t : ℂ) * I)) S s := by
    simpa only [Function.comp_def] using
      ((cglLemma62PrincipalEulerCorrectionAt_differentiableOn Q
        (s - (t : ℂ) * I) (hshift hs)).comp s hdshift hshift)
  have hinner : DifferentiableAt ℂ (fun z : ℂ => 1 - z + (t : ℂ) * I) s :=
    ((differentiableAt_const _).sub differentiableAt_id).add (differentiableAt_const _)
  have hD : DifferentiableWithinAt ℂ
      (fun z : ℂ => cglLemma62DirichletHead (1 : DirichletCharacter ℂ Q.value) M
        (1 - z + (t : ℂ) * I)) S s := by
    simpa only [Function.comp_def] using
      ((cglLemma62DirichletHead_differentiable (1 : DirichletCharacter ℂ Q.value) M
        (1 - s + (t : ℂ) * I)).comp s hinner).differentiableWithinAt
  unfold cglLemma62PrincipalRegularizedFiniteContourIntegrand
  exact (((hH.mul hN).mul hF).mul hE).mul hD

/-- The pole-cleared principal complementary-tail carrier is holomorphic on
the same whole strip, including the former trivial-character pole crossing. -/
theorem cglLemma62PrincipalRegularizedTailContourIntegrand_differentiableOn
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : ℕ) :
    DifferentiableOn ℂ (cglLemma62PrincipalRegularizedTailContourIntegrand w N Q t M)
      (GaloisForLFunctions.HTGeometry.verticalStrip (-1) (1 / 2)) := by
  intro s hs
  let S := GaloisForLFunctions.HTGeometry.verticalStrip (-1) (1 / 2)
  have hshift := cglLemma62PrincipalRegularizedContour_shift_mapsTo t
  have hdshift : DifferentiableWithinAt ℂ (fun z : ℂ => z - (t : ℂ) * I) S s :=
    (differentiableAt_id.sub (differentiableAt_const _)).differentiableWithinAt
  have hH : DifferentiableWithinAt ℂ (cglLemma62MellinTransform w) S s := by
    exact (cglLemma62_mellinTransform_analyticOnNhd w s (mem_univ s)).differentiableAt.differentiableWithinAt
  have hNne : (N.value : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt N.positive)
  have hN : DifferentiableWithinAt ℂ (fun z : ℂ => (N.value : ℂ) ^ z) S s :=
    (differentiableAt_id.const_cpow (Or.inl hNne)).differentiableWithinAt
  have hE : DifferentiableWithinAt ℂ
      (fun z : ℂ => cglLemma62PrincipalEulerCorrectionAt Q (z - (t : ℂ) * I)) S s := by
    simpa only [Function.comp_def] using
      ((cglLemma62PrincipalEulerCorrectionAt_differentiableOn Q
        (s - (t : ℂ) * I) (hshift hs)).comp s hdshift hshift)
  have hP : DifferentiableWithinAt ℂ
      (fun z : ℂ => cglLemma62PrincipalPoleClearedFunctionalFactor (z - (t : ℂ) * I)) S s := by
    simpa only [Function.comp_def] using
      DifferentiableAt.comp_differentiableWithinAt s
        (cglLemma62PrincipalPoleClearedFunctionalFactor_analyticAt (hshift hs).2).differentiableAt
        hdshift
  have hF : DifferentiableWithinAt ℂ
      (fun z : ℂ => cglLemma62PrincipalRegularizedFunctionalFactor (z - (t : ℂ) * I)) S s := by
    simpa only [Function.comp_def] using
      DifferentiableAt.comp_differentiableWithinAt s
        (cglLemma62PrincipalRegularizedFunctionalFactor_analyticAt (hshift hs).2).differentiableAt
        hdshift
  have hinner : DifferentiableAt ℂ (fun z : ℂ => 1 - z + (t : ℂ) * I) s :=
    ((differentiableAt_const _).sub differentiableAt_id).add (differentiableAt_const _)
  have hL : DifferentiableWithinAt ℂ
      (fun z : ℂ => DirichletCharacter.LFunctionTrivChar₁ Q.value
        (1 - z + (t : ℂ) * I)) S s := by
    simpa only [Function.comp_def] using
      ((DirichletCharacter.differentiable_LFunctionTrivChar₁ Q.value
        (1 - s + (t : ℂ) * I)).comp s hinner).differentiableWithinAt
  have hD : DifferentiableWithinAt ℂ
      (fun z : ℂ => cglLemma62DirichletHead (1 : DirichletCharacter ℂ Q.value) M
        (1 - z + (t : ℂ) * I)) S s := by
    simpa only [Function.comp_def] using
      ((cglLemma62DirichletHead_differentiable (1 : DirichletCharacter ℂ Q.value) M
        (1 - s + (t : ℂ) * I)).comp s hinner).differentiableWithinAt
  unfold cglLemma62PrincipalRegularizedTailContourIntegrand
  exact ((hH.mul hN).mul hE).mul ((hP.mul hL).sub (hF.mul hD))

end

end RHTower

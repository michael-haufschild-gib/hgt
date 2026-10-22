import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalRegularizedContour
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailStripDirichlet
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailMellinBounds

/-!
# Chen--Gupta--Li Lemma 6.2: principal complementary tail on the deep strip

The principal reflected `m > M` tail is continued from `Re s = -1` into the
deep strip `-2k ≤ Re s ≤ -1` as the trivial-character `L`-function minus its
finite prefix.  There the dual argument has real part at least two, so the
continuation is literally the absolutely convergent complementary Dirichlet
series, and every factor is holomorphic.
-/

open Complex MeasureTheory Filter Set
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- The principal complementary tail carrier continued off the reflected line. -/
def cglLemma62PrincipalTailContourIntegrand
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : ℕ) (s : ℂ) : ℂ :=
  cglLemma62MellinTransform w s * (N.value : ℂ) ^ s *
    cglLemma62PrincipalRegularizedFunctionalFactor (s - (t : ℂ) * I) *
      cglLemma62PrincipalEulerCorrectionAt Q (s - (t : ℂ) * I) *
        (DirichletCharacter.LFunctionTrivChar Q.value (1 - s + (t : ℂ) * I) -
          cglLemma62DirichletHead (1 : DirichletCharacter ℂ Q.value) M
            (1 - s + (t : ℂ) * I))

/-- In the absolute-convergence half-plane the trivial-character `L`-function
minus its finite prefix is the complementary Dirichlet series. -/
theorem cglLemma62_principal_lfunction_sub_head_eq_tail
    (Q : CGLPositiveModulus) (M : ℕ) (s : CGLAbsoluteConvergencePoint) :
    DirichletCharacter.LFunctionTrivChar Q.value s.1 -
        cglLemma62DirichletHead (1 : DirichletCharacter ℂ Q.value) M s.1 =
      cglLemma62DirichletTail (1 : DirichletCharacter ℂ Q.value) M s := by
  letI : NeZero Q.value := ⟨Nat.ne_of_gt Q.positive⟩
  have h := cglLemma62_lseries_eq_head_add_tail (1 : DirichletCharacter ℂ Q.value) M s
  change DirichletCharacter.LFunction (1 : DirichletCharacter ℂ Q.value) s.1 - _ = _
  rw [DirichletCharacter.LFunction_eq_LSeries (1 : DirichletCharacter ℂ Q.value) s.2]
  calc
    L ↗(1 : DirichletCharacter ℂ Q.value) s.1 -
        cglLemma62DirichletHead (1 : DirichletCharacter ℂ Q.value) M s.1 =
      (cglLemma62DirichletHead (1 : DirichletCharacter ℂ Q.value) M s.1 +
        cglLemma62DirichletTail (1 : DirichletCharacter ℂ Q.value) M s) -
          cglLemma62DirichletHead (1 : DirichletCharacter ℂ Q.value) M s.1 := by rw [h]
    _ = cglLemma62DirichletTail (1 : DirichletCharacter ℂ Q.value) M s := by ring

/-- On the reflected line the continued tail carrier is the literal principal
reflected tail integrand. -/
theorem cglLemma62PrincipalTailContourIntegrand_eq_line
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t v : ℝ) (M : ℕ) :
    cglLemma62PrincipalTailContourIntegrand w N Q t M ((-1 : ℂ) + (v : ℂ) * I) =
      cglLemma62PrincipalReflectedTailIntegrand w N Q t M v := by
  have hleft : ((-1 : ℂ) + (v : ℂ) * I) - (t : ℂ) * I = cglLemma62PrincipalLeftPoint t v := by
    unfold cglLemma62PrincipalLeftPoint
    push_cast
    ring
  have hright : 1 - ((-1 : ℂ) + (v : ℂ) * I) + (t : ℂ) * I =
      (cglLemma62PrincipalRightPointAC t v).1 := by
    change _ = cglLemma62PrincipalRightPoint t v
    unfold cglLemma62PrincipalRightPoint
    push_cast
    ring
  have htail := cglLemma62_principal_lfunction_sub_head_eq_tail Q M
    (cglLemma62PrincipalRightPointAC t v)
  unfold cglLemma62PrincipalTailContourIntegrand cglLemma62PrincipalReflectedTailIntegrand
  rw [hleft, hright, htail, cglLemma62_principal_regularizedFactor_eq_zetaChi,
    cglLemma62PrincipalEulerCorrectionAt_eq_line]

/-- The principal far-left complementary tail: the absolutely convergent
complementary series on the deep line `Re s = -2k`. -/
def cglLemma62PrincipalFarTailIntegrand
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : ℕ) (d : CGLLemma62TailContourDepth)
    (v : ℝ) : ℂ :=
  cglLemma62MellinTransform w (cglLemma62FarLeftPoint d v) *
    (N.value : ℂ) ^ (cglLemma62FarLeftPoint d v) *
      cglLemma62PrincipalRegularizedFunctionalFactor
        (cglLemma62FarLeftPoint d v - (t : ℂ) * I) *
        cglLemma62PrincipalEulerCorrectionAt Q
          (cglLemma62FarLeftPoint d v - (t : ℂ) * I) *
          cglLemma62DirichletTail (1 : DirichletCharacter ℂ Q.value) M
            (cglLemma62FarRightPointAC t d v)

/-- On the deep line the continued principal tail carrier is its literal
complementary Dirichlet series. -/
theorem cglLemma62PrincipalTailContourIntegrand_eq_farTail
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : ℕ) (d : CGLLemma62TailContourDepth) (v : ℝ) :
    cglLemma62PrincipalTailContourIntegrand w N Q t M (cglLemma62FarLeftPoint d v) =
      cglLemma62PrincipalFarTailIntegrand w N Q t M d v := by
  have hright : 1 - cglLemma62FarLeftPoint d v + (t : ℂ) * I =
      (cglLemma62FarRightPointAC t d v).1 := rfl
  have htail := cglLemma62_principal_lfunction_sub_head_eq_tail Q M
    (cglLemma62FarRightPointAC t d v)
  unfold cglLemma62PrincipalTailContourIntegrand cglLemma62PrincipalFarTailIntegrand
  rw [hright, htail]

private theorem cglLemma62_principalTail_leftFactor_differentiable
    (Q : CGLPositiveModulus) :
    Differentiable ℂ (cglLemma62PrincipalEulerLeftFactorAt Q) :=
  cglLemma62PrincipalEulerLeftFactorAt_differentiable Q

private theorem cglLemma62_principalTail_rightFactor_differentiable
    (Q : CGLPositiveModulus) :
    Differentiable ℂ (cglLemma62PrincipalEulerRightFactorAt Q) :=
  cglLemma62PrincipalEulerRightFactorAt_differentiable Q

private theorem cglLemma62_principalTail_rightFactor_ne_zero
    (Q : CGLPositiveModulus) {z : ℂ} (hz : z.re ≤ 1 / 2) :
    cglLemma62PrincipalEulerRightFactorAt Q z ≠ 0 := by
  unfold cglLemma62PrincipalEulerRightFactorAt
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hlt : ‖(p : ℂ) ^ (-(1 - z))‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hpprime.pos]
    have hre : (-(1 - z)).re < 0 := by
      simp only [neg_re, sub_re, one_re]
      linarith
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpprime.one_lt) hre
  intro hzero
  have hone : (p : ℂ) ^ (-(1 - z)) = 1 := (sub_eq_zero.mp hzero).symm
  rw [hone, norm_one] at hlt
  exact lt_irrefl _ hlt

/-- The principal finite Euler correction is holomorphic at every point with
real part at most one half. -/
theorem cglLemma62PrincipalEulerCorrectionAt_differentiableAt
    (Q : CGLPositiveModulus) {z : ℂ} (hz : z.re ≤ 1 / 2) :
    DifferentiableAt ℂ (cglLemma62PrincipalEulerCorrectionAt Q) z := by
  unfold cglLemma62PrincipalEulerCorrectionAt
  exact (cglLemma62_principalTail_leftFactor_differentiable Q z).div
    (cglLemma62_principalTail_rightFactor_differentiable Q z)
    (cglLemma62_principalTail_rightFactor_ne_zero Q hz)

/-- The continued principal tail carrier is holomorphic on the deep strip. -/
theorem cglLemma62PrincipalTailContourIntegrand_differentiableOn
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M k : ℕ) :
    DifferentiableOn ℂ (cglLemma62PrincipalTailContourIntegrand w N Q t M)
      (GaloisForLFunctions.HTGeometry.verticalStrip (-2 * (k : ℝ)) (-1)) := by
  letI : NeZero Q.value := ⟨Nat.ne_of_gt Q.positive⟩
  intro s hs
  have hsre : s.re ≤ -1 := by
    change (-2 * (k : ℝ)) ≤ s.re ∧ s.re ≤ -1 at hs
    exact hs.2
  have hH : DifferentiableAt ℂ (cglLemma62MellinTransform w) s :=
    (cglLemma62_mellinTransform_analyticOnNhd w s (mem_univ s)).differentiableAt
  have hNne : (N.value : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt N.positive)
  have hN : DifferentiableAt ℂ (fun z : ℂ => (N.value : ℂ) ^ z) s :=
    differentiableAt_id.const_cpow (Or.inl hNne)
  have hdshift : DifferentiableAt ℂ (fun z : ℂ => z - (t : ℂ) * I) s :=
    differentiableAt_id.sub (differentiableAt_const _)
  have hshiftre : (s - (t : ℂ) * I).re ≤ 1 / 2 := by
    simp
    linarith
  have hF : DifferentiableAt ℂ
      (fun z : ℂ => cglLemma62PrincipalRegularizedFunctionalFactor (z - (t : ℂ) * I)) s := by
    simpa only [Function.comp_def] using
      ((cglLemma62PrincipalRegularizedFunctionalFactor_analyticAt hshiftre).differentiableAt.comp
        s hdshift)
  have hE : DifferentiableAt ℂ
      (fun z : ℂ => cglLemma62PrincipalEulerCorrectionAt Q (z - (t : ℂ) * I)) s := by
    simpa only [Function.comp_def] using
      ((cglLemma62PrincipalEulerCorrectionAt_differentiableAt Q hshiftre).comp s hdshift)
  have hinner : DifferentiableAt ℂ (fun z : ℂ => 1 - z + (t : ℂ) * I) s :=
    ((differentiableAt_const _).sub differentiableAt_id).add (differentiableAt_const _)
  have hne : 1 - s + (t : ℂ) * I ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hL : DifferentiableAt ℂ
      (fun z : ℂ => DirichletCharacter.LFunctionTrivChar Q.value (1 - z + (t : ℂ) * I)) s := by
    have := (DirichletCharacter.differentiableAt_LFunction (1 : DirichletCharacter ℂ Q.value)
      (1 - s + (t : ℂ) * I) (Or.inl hne)).comp s hinner
    simpa only [Function.comp_def] using this
  have hD : DifferentiableAt ℂ
      (fun z : ℂ => cglLemma62DirichletHead (1 : DirichletCharacter ℂ Q.value) M
        (1 - z + (t : ℂ) * I)) s := by
    simpa only [Function.comp_def] using
      ((cglLemma62DirichletHead_differentiable (1 : DirichletCharacter ℂ Q.value) M
        (1 - s + (t : ℂ) * I)).comp s hinner)
  unfold cglLemma62PrincipalTailContourIntegrand
  exact ((((hH.mul hN).mul hF).mul hE).mul (hL.sub hD)).differentiableWithinAt

end

end RHTower

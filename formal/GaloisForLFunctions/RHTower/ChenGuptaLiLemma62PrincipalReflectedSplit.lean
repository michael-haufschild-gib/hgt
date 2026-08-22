import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalReflection
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62ReflectedSplit

/-!
# Chen--Gupta--Li Lemma 6.2: principal reflected Dirichlet split

After the principal ζ-reflection, CGL's finite Euler factor is transferred to
the reflected principal `L`-function.  The same source finite-prefix and
complementary-tail split used in the nonprincipal branch then applies
verbatim, now with the principal character at the ambient modulus.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- The finite Euler factor on the right line of the principal reflection. -/
def cglLemma62PrincipalEulerRightFactor (Q : CGLPositiveModulus) (t v : ℝ) : ℂ :=
  ∏ p ∈ Q.value.primeFactors,
    (1 - (p : ℂ) ^ (-cglLemma62PrincipalRightPoint t v))

/-- The Euler correction moving CGL's principal left factor onto the
reflected principal `L`-function. -/
def cglLemma62PrincipalEulerCorrection (Q : CGLPositiveModulus) (t v : ℝ) : ℂ :=
  cglLemma62PrincipalEulerLeftFactor Q (cglLemma62PrincipalLeftPoint t v) /
    cglLemma62PrincipalEulerRightFactor Q t v

private theorem cglLemma62_principalEulerRightFactor_factor_ne_zero
    (Q : CGLPositiveModulus) (t v : ℝ) (p : ↑Q.value.primeFactors) :
    1 - (p.1 : ℂ) ^ (-cglLemma62PrincipalRightPoint t v) ≠ 0 := by
  have hpprime : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hppos : 0 < (p.1 : ℝ) := by exact_mod_cast hpprime.pos
  let z : ℂ := (p.1 : ℂ) ^ (-cglLemma62PrincipalRightPoint t v)
  have hpow : ‖z‖ < 1 := by
    dsimp [z]
    change ‖((p.1 : ℝ) : ℂ) ^ (-cglLemma62PrincipalRightPoint t v)‖ < 1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hppos]
    have hre : (-cglLemma62PrincipalRightPoint t v).re = (-2 : ℝ) := by
      simp [cglLemma62PrincipalRightPoint]
    rw [hre]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpprime.one_lt) (by norm_num)
  intro hzero
  have hone : z = 1 := by
    exact (sub_eq_zero.mp (by simpa only [z] using hzero)).symm
  have hnorm := congrArg norm hone
  rw [norm_one] at hnorm
  linarith

/-- The right principal Euler factor is nonzero on CGL's reflected line. -/
theorem cglLemma62_principalEulerRightFactor_ne_zero (Q : CGLPositiveModulus) (t v : ℝ) :
    cglLemma62PrincipalEulerRightFactor Q t v ≠ 0 := by
  unfold cglLemma62PrincipalEulerRightFactor
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  exact cglLemma62_principalEulerRightFactor_factor_ne_zero Q t v ⟨p, hp⟩

/-- The correction recovers the principal left Euler factor exactly. -/
theorem cglLemma62_principalEulerCorrection_mul_rightFactor
    (Q : CGLPositiveModulus) (t v : ℝ) :
    cglLemma62PrincipalEulerCorrection Q t v *
      cglLemma62PrincipalEulerRightFactor Q t v =
        cglLemma62PrincipalEulerLeftFactor Q (cglLemma62PrincipalLeftPoint t v) := by
  unfold cglLemma62PrincipalEulerCorrection
  field_simp [cglLemma62_principalEulerRightFactor_ne_zero Q t v]

/-- The reflected principal integrand after transferring its finite Euler
factor to the principal character on the right line. -/
def cglLemma62PrincipalReflectedLFunctionIntegrand
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t v : ℝ) : ℂ :=
  cglLemma62MellinTransform w ((-1 : ℂ) + (v : ℂ) * I) *
    (N.value : ℂ) ^ ((-1 : ℂ) + (v : ℂ) * I) *
      zetaChi (cglLemma62PrincipalLeftPoint t v) *
        cglLemma62PrincipalEulerCorrection Q t v *
          DirichletCharacter.LFunctionTrivChar Q.value
            (cglLemma62PrincipalRightPoint t v)

/-- The ζ-reflected principal line equals its Euler-corrected principal
`L`-function representation. -/
theorem cglLemma62_principal_reflected_line_eq_lfunction
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t v : ℝ) :
    cglLemma62PrincipalReflectedLineIntegrand w N Q t v =
      cglLemma62PrincipalReflectedLFunctionIntegrand w N Q t v := by
  letI : NeZero Q.value := ⟨Nat.ne_of_gt Q.positive⟩
  have hrightne : cglLemma62PrincipalRightPoint t v ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [cglLemma62PrincipalRightPoint] at hre
  have hL : DirichletCharacter.LFunctionTrivChar Q.value
      (cglLemma62PrincipalRightPoint t v) =
      cglLemma62PrincipalEulerRightFactor Q t v *
        riemannZeta (cglLemma62PrincipalRightPoint t v) := by
    rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hrightne]
    rfl
  unfold cglLemma62PrincipalReflectedLineIntegrand
    cglLemma62PrincipalReflectedLFunctionIntegrand
  rw [hL]
  change
    cglLemma62MellinTransform w ((-1 : ℂ) + (v : ℂ) * I) *
        (N.value : ℂ) ^ ((-1 : ℂ) + (v : ℂ) * I) *
          cglLemma62PrincipalEulerLeftFactor Q (cglLemma62PrincipalLeftPoint t v) *
            zetaChi (cglLemma62PrincipalLeftPoint t v) *
              riemannZeta (cglLemma62PrincipalRightPoint t v) =
      cglLemma62MellinTransform w ((-1 : ℂ) + (v : ℂ) * I) *
        (N.value : ℂ) ^ ((-1 : ℂ) + (v : ℂ) * I) *
          zetaChi (cglLemma62PrincipalLeftPoint t v) *
            cglLemma62PrincipalEulerCorrection Q t v *
              (cglLemma62PrincipalEulerRightFactor Q t v *
                riemannZeta (cglLemma62PrincipalRightPoint t v))
  calc
    cglLemma62MellinTransform w ((-1 : ℂ) + (v : ℂ) * I) *
        (N.value : ℂ) ^ ((-1 : ℂ) + (v : ℂ) * I) *
          cglLemma62PrincipalEulerLeftFactor Q (cglLemma62PrincipalLeftPoint t v) *
            zetaChi (cglLemma62PrincipalLeftPoint t v) *
              riemannZeta (cglLemma62PrincipalRightPoint t v) =
      cglLemma62MellinTransform w ((-1 : ℂ) + (v : ℂ) * I) *
        (N.value : ℂ) ^ ((-1 : ℂ) + (v : ℂ) * I) *
          zetaChi (cglLemma62PrincipalLeftPoint t v) *
            cglLemma62PrincipalEulerLeftFactor Q (cglLemma62PrincipalLeftPoint t v) *
              riemannZeta (cglLemma62PrincipalRightPoint t v) := by ring
    _ = cglLemma62MellinTransform w ((-1 : ℂ) + (v : ℂ) * I) *
        (N.value : ℂ) ^ ((-1 : ℂ) + (v : ℂ) * I) *
          zetaChi (cglLemma62PrincipalLeftPoint t v) *
            (cglLemma62PrincipalEulerCorrection Q t v *
              cglLemma62PrincipalEulerRightFactor Q t v) *
                riemannZeta (cglLemma62PrincipalRightPoint t v) := by
      rw [cglLemma62_principalEulerCorrection_mul_rightFactor Q t v]
    _ = _ := by ring

/-- The principal reflected right point with its absolute-convergence
certificate. -/
def cglLemma62PrincipalRightPointAC (t v : ℝ) : CGLAbsoluteConvergencePoint :=
  ⟨cglLemma62PrincipalRightPoint t v, by
    unfold cglLemma62PrincipalRightPoint
    norm_num⟩

/-- The principal reflected integrand with CGL's finite dual polynomial. -/
def cglLemma62PrincipalReflectedFiniteIntegrand
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : ℕ) (v : ℝ) : ℂ :=
  cglLemma62MellinTransform w ((-1 : ℂ) + (v : ℂ) * I) *
    (N.value : ℂ) ^ ((-1 : ℂ) + (v : ℂ) * I) *
      zetaChi (cglLemma62PrincipalLeftPoint t v) *
        cglLemma62PrincipalEulerCorrection Q t v *
          cglLemma62DirichletHead (1 : DirichletCharacter ℂ Q.value) M
            (cglLemma62PrincipalRightPoint t v)

/-- The principal reflected integrand with the exact complementary
Dirichlet-series tail. -/
def cglLemma62PrincipalReflectedTailIntegrand
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : ℕ) (v : ℝ) : ℂ :=
  cglLemma62MellinTransform w ((-1 : ℂ) + (v : ℂ) * I) *
    (N.value : ℂ) ^ ((-1 : ℂ) + (v : ℂ) * I) *
      zetaChi (cglLemma62PrincipalLeftPoint t v) *
        cglLemma62PrincipalEulerCorrection Q t v *
          cglLemma62DirichletTail (1 : DirichletCharacter ℂ Q.value) M
            (cglLemma62PrincipalRightPointAC t v)

/-- The principal `L`-function on the reflected line is CGL's exact finite
dual polynomial plus complementary tail. -/
theorem cglLemma62_principal_right_lfunction_eq_head_add_tail
    (Q : CGLPositiveModulus) (t v : ℝ) (M : ℕ) :
    DirichletCharacter.LFunctionTrivChar Q.value (cglLemma62PrincipalRightPoint t v) =
      cglLemma62DirichletHead (1 : DirichletCharacter ℂ Q.value) M
        (cglLemma62PrincipalRightPoint t v) +
      cglLemma62DirichletTail (1 : DirichletCharacter ℂ Q.value) M
        (cglLemma62PrincipalRightPointAC t v) := by
  letI : NeZero Q.value := ⟨Nat.ne_of_gt Q.positive⟩
  change DirichletCharacter.LFunction (1 : DirichletCharacter ℂ Q.value)
      (cglLemma62PrincipalRightPoint t v) = _
  rw [DirichletCharacter.LFunction_eq_LSeries]
  · exact cglLemma62_lseries_eq_head_add_tail (1 : DirichletCharacter ℂ Q.value) M
      (cglLemma62PrincipalRightPointAC t v)
  · exact (cglLemma62PrincipalRightPointAC t v).2

/-- **CGL (6.4), principal algebraic split.** The principal reflected
integrand is its source finite dual polynomial plus complementary tail. -/
theorem cglLemma62_principal_reflected_eq_finite_add_tail
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : ℕ) (v : ℝ) :
    cglLemma62PrincipalReflectedLineIntegrand w N Q t v =
      cglLemma62PrincipalReflectedFiniteIntegrand w N Q t M v +
        cglLemma62PrincipalReflectedTailIntegrand w N Q t M v := by
  rw [cglLemma62_principal_reflected_line_eq_lfunction]
  unfold cglLemma62PrincipalReflectedLFunctionIntegrand
    cglLemma62PrincipalReflectedFiniteIntegrand
    cglLemma62PrincipalReflectedTailIntegrand
  rw [cglLemma62_principal_right_lfunction_eq_head_add_tail]
  ring

end

end RHTower

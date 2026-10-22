import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalRegularizedFactor

/-!
# Chen--Gupta--Li Lemma 6.2: off-line principal Euler correction

The finite Euler correction in CGL's principal reflected branch is extended
from the literal left line across the contour-displacement strip.  Its right
Euler product stays nonzero because every local nonconstant term has norm
strictly below one.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- Principal left Euler product at an arbitrary reflected contour point. -/
def cglLemma62PrincipalEulerLeftFactorAt (Q : CGLPositiveModulus) (z : ℂ) : ℂ :=
  ∏ p ∈ Q.value.primeFactors, (1 - (p : ℂ) ^ (-z))

/-- Principal right Euler product at an arbitrary reflected contour point. -/
def cglLemma62PrincipalEulerRightFactorAt (Q : CGLPositiveModulus) (z : ℂ) : ℂ :=
  ∏ p ∈ Q.value.primeFactors, (1 - (p : ℂ) ^ (-(1 - z)))

/-- Principal finite Euler correction, analytically continued off the source
left line. -/
def cglLemma62PrincipalEulerCorrectionAt (Q : CGLPositiveModulus) (z : ℂ) : ℂ :=
  cglLemma62PrincipalEulerLeftFactorAt Q z /
    cglLemma62PrincipalEulerRightFactorAt Q z

/-- The off-line principal correction agrees with CGL's literal correction on
the original reflected line. -/
theorem cglLemma62PrincipalEulerCorrectionAt_eq_line
    (Q : CGLPositiveModulus) (t v : ℝ) :
    cglLemma62PrincipalEulerCorrectionAt Q (cglLemma62PrincipalLeftPoint t v) =
      cglLemma62PrincipalEulerCorrection Q t v := by
  have hright : (1 : ℂ) - cglLemma62PrincipalLeftPoint t v =
      cglLemma62PrincipalRightPoint t v := by
    unfold cglLemma62PrincipalLeftPoint cglLemma62PrincipalRightPoint
    push_cast
    ring
  unfold cglLemma62PrincipalEulerCorrectionAt cglLemma62PrincipalEulerLeftFactorAt
    cglLemma62PrincipalEulerRightFactorAt cglLemma62PrincipalEulerCorrection
    cglLemma62PrincipalEulerLeftFactor cglLemma62PrincipalEulerRightFactor
  rw [hright]

private theorem cglLemma62PrincipalEulerRightFactorAt_factor_ne_zero
    (Q : CGLPositiveModulus) (z : ℂ) (hz : z.re ≤ (1 / 2 : ℝ))
    (p : ↑Q.value.primeFactors) :
    1 - (p.1 : ℂ) ^ (-(1 - z)) ≠ 0 := by
  have hpprime : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hppos : 0 < (p.1 : ℝ) := by exact_mod_cast hpprime.pos
  let w : ℂ := (p.1 : ℂ) ^ (-(1 - z))
  have hpow : ‖w‖ < 1 := by
    dsimp [w]
    change ‖((p.1 : ℝ) : ℂ) ^ (-(1 - z))‖ < 1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hppos]
    have hre : (-(1 - z)).re < (0 : ℝ) := by
      simp only [neg_re, sub_re, one_re]
      linarith
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpprime.one_lt) hre
  intro hzero
  have hone : w = 1 := by
    exact (sub_eq_zero.mp (by simpa only [w] using hzero)).symm
  have hnorm := congrArg norm hone
  rw [norm_one] at hnorm
  linarith

theorem cglLemma62PrincipalEulerLeftFactorAt_differentiable
    (Q : CGLPositiveModulus) :
    Differentiable ℂ (cglLemma62PrincipalEulerLeftFactorAt Q) := by
  intro z
  unfold cglLemma62PrincipalEulerLeftFactorAt
  have hprod : DifferentiableAt ℂ (Finset.prod Q.value.primeFactors
      (fun p => fun z : ℂ => 1 - (p : ℂ) ^ (-z))) z := by
    apply DifferentiableAt.finsetProd
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hppos : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
    have hpow : DifferentiableAt ℂ (fun z : ℂ => (p : ℂ) ^ (-z)) z := by
      exact DifferentiableAt.cpow (differentiableAt_const _) differentiableAt_id.neg
        (Complex.ofReal_mem_slitPlane.mpr hppos)
    exact (differentiableAt_const _).sub hpow
  refine hprod.congr_of_eventuallyEq ?_
  filter_upwards with y
  simp only [Finset.prod_apply]

theorem cglLemma62PrincipalEulerRightFactorAt_differentiable
    (Q : CGLPositiveModulus) :
    Differentiable ℂ (cglLemma62PrincipalEulerRightFactorAt Q) := by
  intro z
  unfold cglLemma62PrincipalEulerRightFactorAt
  have hprod : DifferentiableAt ℂ (Finset.prod Q.value.primeFactors
      (fun p => fun z : ℂ => 1 - (p : ℂ) ^ (-(1 - z)))) z := by
    apply DifferentiableAt.finsetProd
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hppos : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
    have hexp : DifferentiableAt ℂ (fun z : ℂ => -(1 - z)) z :=
      ((differentiableAt_const _).sub differentiableAt_id).neg
    have hpow : DifferentiableAt ℂ (fun z : ℂ => (p : ℂ) ^ (-(1 - z))) z := by
      exact DifferentiableAt.cpow (differentiableAt_const _) hexp
        (Complex.ofReal_mem_slitPlane.mpr hppos)
    exact (differentiableAt_const _).sub hpow
  refine hprod.congr_of_eventuallyEq ?_
  filter_upwards with y
  simp only [Finset.prod_apply]

private theorem cglLemma62PrincipalEulerRightFactorAt_ne_zero_on
    (Q : CGLPositiveModulus) (z : ℂ) (hz : z.re ≤ (1 / 2 : ℝ)) :
    cglLemma62PrincipalEulerRightFactorAt Q z ≠ 0 := by
  unfold cglLemma62PrincipalEulerRightFactorAt
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  exact cglLemma62PrincipalEulerRightFactorAt_factor_ne_zero Q z hz ⟨p, hp⟩

/-- The principal finite Euler correction is holomorphic across CGL's full
left-to-critical displacement strip. -/
theorem cglLemma62PrincipalEulerCorrectionAt_differentiableOn
    (Q : CGLPositiveModulus) :
    DifferentiableOn ℂ (cglLemma62PrincipalEulerCorrectionAt Q)
      (GaloisForLFunctions.HTGeometry.verticalStrip (-1) (1 / 2)) := by
  intro z hz
  unfold cglLemma62PrincipalEulerCorrectionAt
  exact ((cglLemma62PrincipalEulerLeftFactorAt_differentiable Q z).div
    (cglLemma62PrincipalEulerRightFactorAt_differentiable Q z)
    (cglLemma62PrincipalEulerRightFactorAt_ne_zero_on Q z hz.2)).differentiableWithinAt

end

end RHTower

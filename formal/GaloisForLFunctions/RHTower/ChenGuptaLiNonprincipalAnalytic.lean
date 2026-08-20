/-
# Chen--Gupta--Li non-principal detector regularity

The non-principal branch of the zero-detection contour has no Dirichlet
`L`-function pole.  This module makes that dichotomy explicit: its zero
certificates carry non-principality as checked data, and the corresponding
shifted detector factor is analytic everywhere.  Gamma remains meromorphic,
with its local cancellation at the certified zero supplied by
`ChenGuptaLiZeroResidue`.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiZeroResidue
import GaloisForLFunctions.RHTower.AnalyticDividedDifference
import GaloisForLFunctions.HTGeometry.GammaAnalyticOffPoles
import GaloisForLFunctions.HTGeometry.RectangleResidue

open Complex LSeries DirichletCharacter Filter MeasureTheory Set intervalIntegral
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- A certified critical-strip zero of a non-principal Dirichlet character. -/
structure CGLNonprincipalCriticalStripLZero (q : ℕ) extends CGLCriticalStripLZero q where
  character_ne_one : character ≠ 1

/-- The translated finite detector factor in the non-principal branch. -/
def cglNonprincipalDetectorFactor (X q : ℕ)
    (z : CGLNonprincipalCriticalStripLZero q) (w : ℂ) : ℂ :=
  zeroDetectionMobiusPolynomial X (q + 1) z.character (z.point + w) *
    DirichletCharacter.LFunction z.character (z.point + w)

/-- In the non-principal branch, the shifted finite detector factor is
complex differentiable everywhere. -/
theorem cglNonprincipalDetectorFactor_differentiable (X q : ℕ)
    (z : CGLNonprincipalCriticalStripLZero q) :
    Differentiable ℂ (cglNonprincipalDetectorFactor X q z) := by
  intro w
  unfold cglNonprincipalDetectorFactor
  apply DifferentiableAt.mul
  · exact (differentiableAt_zeroDetectionMobiusPolynomial X (q + 1) z.character
      (z.point + w)).comp w
      ((differentiable_const z.point).differentiableAt.add differentiableAt_id)
  · exact (DirichletCharacter.differentiable_LFunction z.character_ne_one).differentiableAt.comp w
      ((differentiable_const z.point).differentiableAt.add differentiableAt_id)

/-- Hence the non-principal shifted detector factor is analytic at every
complex point. -/
theorem cglNonprincipalDetectorFactor_analyticAt (X q : ℕ)
    (z : CGLNonprincipalCriticalStripLZero q) (w : ℂ) :
    AnalyticAt ℂ (cglNonprincipalDetectorFactor X q z) w :=
  (cglNonprincipalDetectorFactor_differentiable X q z).analyticAt w

/-- Apart from Gamma's known poles, the non-principal detector Mellin
integrand is meromorphic everywhere. -/
theorem cglNonprincipalDetectorMellinIntegrand_meromorphicAt (X q : ℕ)
    (z : CGLNonprincipalCriticalStripLZero q) (w : ℂ) :
    MeromorphicAt (cglDetectorMellinIntegrand X q z.toCGLCriticalStripLZero) w := by
  unfold cglDetectorMellinIntegrand
  exact (Meromorphic.Gamma w).mul
    (cglNonprincipalDetectorFactor_analyticAt X q z w).meromorphicAt

/-- The translated non-principal detector factor vanishes at its certified
zero. -/
theorem cglNonprincipalDetectorFactor_zero (X q : ℕ)
    (z : CGLNonprincipalCriticalStripLZero q) :
    cglNonprincipalDetectorFactor X q z 0 = 0 := by
  simpa [cglNonprincipalDetectorFactor] using
    cglDetectorMellinIntegrand_residueCoefficient_at_criticalZero X q z.toCGLCriticalStripLZero

/-- Removable divided difference of the zero-vanishing non-principal detector
factor. -/
def cglNonprincipalDetectorZeroQuotient (X q : ℕ)
    (z : CGLNonprincipalCriticalStripLZero q) : ℂ → ℂ :=
  dslope (cglNonprincipalDetectorFactor X q z) 0

/-- The vanishing non-principal detector factor has the exact global linear
factor `w`, with a removable divided-difference quotient. -/
theorem cglNonprincipalDetectorFactor_eq_mul_zeroQuotient (X q : ℕ)
    (z : CGLNonprincipalCriticalStripLZero q) (w : ℂ) :
    cglNonprincipalDetectorFactor X q z w =
      w * cglNonprincipalDetectorZeroQuotient X q z w := by
  simpa [cglNonprincipalDetectorZeroQuotient, smul_eq_mul] using
    (sub_smul_dslope_of_zero (cglNonprincipalDetectorFactor_zero X q z) w).symm

/-- The divided-difference quotient is analytic at every point. -/
theorem cglNonprincipalDetectorZeroQuotient_analyticAt (X q : ℕ)
    (z : CGLNonprincipalCriticalStripLZero q) (w : ℂ) :
    AnalyticAt ℂ (cglNonprincipalDetectorZeroQuotient X q z) w := by
  unfold cglNonprincipalDetectorZeroQuotient
  exact analyticAt_dslope_of_analyticAt
    (cglNonprincipalDetectorFactor_analyticAt X q z 0)
    (cglNonprincipalDetectorFactor_analyticAt X q z w)

/-- The analytic replacement of the non-principal Mellin integrand after its
zero-cancelled Gamma pole is removed. -/
def cglNonprincipalRegularizedMellinIntegrand (X q : ℕ)
    (z : CGLNonprincipalCriticalStripLZero q) (w : ℂ) : ℂ :=
  Complex.Gamma (w + 1) * cglNonprincipalDetectorZeroQuotient X q z w

/-- Away from `w = 0`, the original non-principal detector Mellin integrand
is exactly its regularized analytic replacement. -/
theorem cglNonprincipalMellinIntegrand_eq_regularized_off_zero (X q : ℕ)
    (z : CGLNonprincipalCriticalStripLZero q) (w : ℂ) (hw : w ≠ 0) :
    cglDetectorMellinIntegrand X q z.toCGLCriticalStripLZero w =
      cglNonprincipalRegularizedMellinIntegrand X q z w := by
  rw [show cglDetectorMellinIntegrand X q z.toCGLCriticalStripLZero w =
    Complex.Gamma w * cglNonprincipalDetectorFactor X q z w by rfl,
    cglNonprincipalDetectorFactor_eq_mul_zeroQuotient,
    cglNonprincipalRegularizedMellinIntegrand]
  rw [Complex.Gamma_add_one w hw]
  ring

/-- The regularized non-principal Mellin integrand is analytic at the former
Gamma pole `w = 0`. -/
theorem cglNonprincipalRegularizedMellinIntegrand_analyticAt_zero (X q : ℕ)
    (z : CGLNonprincipalCriticalStripLZero q) :
    AnalyticAt ℂ (cglNonprincipalRegularizedMellinIntegrand X q z) 0 := by
  unfold cglNonprincipalRegularizedMellinIntegrand
  apply AnalyticAt.mul
  · exact (HTGeometry.analyticAt_Gamma_of_re_pos (by norm_num)).comp
      (analyticAt_id.add analyticAt_const)
  · exact cglNonprincipalDetectorZeroQuotient_analyticAt X q z 0

/-- The half-plane in which the regularized Gamma factor `Γ(w+1)` is
analytic. -/
def cglGammaSafeHalfPlane : Set ℂ := {w | (-1 : ℝ) < w.re}

/-- A certified finite rectangle for the non-principal detector shift.  It
contains the cancelled Gamma pole at zero while remaining in the half-plane
where its regularization is analytic. -/
structure CGLNonprincipalDetectorRectangle where
  lower : ℂ
  upper : ℂ
  lower_re_gt_neg_one : (-1 : ℝ) < lower.re
  lower_re_lt_zero : lower.re < 0
  zero_re_lt_upper : 0 < upper.re
  lower_im_lt_zero : lower.im < 0
  zero_im_lt_upper : 0 < upper.im

/-- The regularized non-principal integrand is analytic on the entire safe
Gamma half-plane. -/
theorem cglNonprincipalRegularizedMellinIntegrand_analyticOnGammaSafe (X q : ℕ)
    (z : CGLNonprincipalCriticalStripLZero q) :
    AnalyticOnNhd ℂ (cglNonprincipalRegularizedMellinIntegrand X q z)
      cglGammaSafeHalfPlane := by
  intro w hw
  unfold cglGammaSafeHalfPlane at hw
  unfold cglNonprincipalRegularizedMellinIntegrand
  apply AnalyticAt.mul
  · change AnalyticAt ℂ (fun u : ℂ => Complex.Gamma (u + 1)) w
    have hpos : 0 < (w + 1).re := by
      change (-1 : ℝ) < w.re at hw
      rw [Complex.add_re]
      norm_num
      linarith
    have hshift : AnalyticAt ℂ (fun u : ℂ => u + 1) w := by
      exact (analyticAt_id.add analyticAt_const : AnalyticAt ℂ (fun u : ℂ => u + 1) w)
    have hcomp := AnalyticAt.comp (g := Complex.Gamma) (f := fun u : ℂ => u + 1)
      (HTGeometry.analyticAt_Gamma_of_re_pos hpos) hshift
    simpa only [Function.comp_def] using hcomp
  · exact cglNonprincipalDetectorZeroQuotient_analyticAt X q z w

/-- The closed rectangle supplied by a non-principal rectangle certificate
lies in the safe Gamma half-plane. -/
theorem cglNonprincipalDetectorRectangle_subset_gammaSafe
    (r : CGLNonprincipalDetectorRectangle) :
    (uIcc r.lower.re r.upper.re ×ℂ uIcc r.lower.im r.upper.im) ⊆
      cglGammaSafeHalfPlane := by
  intro w hw
  rw [Complex.mem_reProdIm] at hw
  unfold cglGammaSafeHalfPlane
  have hre : r.lower.re ≤ r.upper.re := by
    linarith [r.lower_re_lt_zero, r.zero_re_lt_upper]
  rw [uIcc_of_le hre] at hw
  rw [mem_Icc] at hw
  exact r.lower_re_gt_neg_one.trans_le hw.1.1

/-- The lower horizontal edge of a certified non-principal rectangle avoids
the cancelled pole at zero. -/
theorem cglNonprincipalDetectorRectangle_bottom_ne_zero
    (r : CGLNonprincipalDetectorRectangle) (x : ℝ)
    (_hx : x ∈ uIcc r.lower.re r.upper.re) :
    (x : ℂ) + r.lower.im * I ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_add, mul_one, zero_im] at him
  linarith [r.lower_im_lt_zero]

/-- The upper horizontal edge of a certified non-principal rectangle avoids
the cancelled pole at zero. -/
theorem cglNonprincipalDetectorRectangle_top_ne_zero
    (r : CGLNonprincipalDetectorRectangle) (x : ℝ)
    (_hx : x ∈ uIcc r.lower.re r.upper.re) :
    (x : ℂ) + r.upper.im * I ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_add, mul_one, zero_im] at him
  linarith [r.zero_im_lt_upper]

/-- The right vertical edge of a certified non-principal rectangle avoids
the cancelled pole at zero. -/
theorem cglNonprincipalDetectorRectangle_right_ne_zero
    (r : CGLNonprincipalDetectorRectangle) (y : ℝ)
    (_hy : y ∈ uIcc r.lower.im r.upper.im) :
    (r.upper.re : ℂ) + y * I ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_re] at hre
  linarith [r.zero_re_lt_upper]

/-- The left vertical edge of a certified non-principal rectangle avoids the
cancelled pole at zero. -/
theorem cglNonprincipalDetectorRectangle_left_ne_zero
    (r : CGLNonprincipalDetectorRectangle) (y : ℝ)
    (_hy : y ∈ uIcc r.lower.im r.upper.im) :
    (r.lower.re : ℂ) + y * I ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_re] at hre
  linarith [r.lower_re_lt_zero]

/-- **Finite non-principal contour shift.**  On every certified safe rectangle
enclosing zero, the original detector integrand has vanishing boundary
integral: its sole apparent enclosed Gamma pole is removable at the certified
Dirichlet L-zero. -/
theorem rectIntegral_cglNonprincipalDetectorMellinIntegrand_eq_zero (X q : ℕ)
    (z : CGLNonprincipalCriticalStripLZero q) (r : CGLNonprincipalDetectorRectangle) :
    rectIntegral (cglDetectorMellinIntegrand X q z.toCGLCriticalStripLZero) r.lower r.upper = 0 := by
  calc
    rectIntegral (cglDetectorMellinIntegrand X q z.toCGLCriticalStripLZero) r.lower r.upper =
        rectIntegral (cglNonprincipalRegularizedMellinIntegrand X q z) r.lower r.upper := by
      apply rectIntegral_congr (S := ({0}ᶜ : Set ℂ))
      · intro w hw
        exact cglNonprincipalMellinIntegrand_eq_regularized_off_zero X q z w hw
      · exact cglNonprincipalDetectorRectangle_bottom_ne_zero r
      · exact cglNonprincipalDetectorRectangle_top_ne_zero r
      · exact cglNonprincipalDetectorRectangle_right_ne_zero r
      · exact cglNonprincipalDetectorRectangle_left_ne_zero r
    _ = 0 := rectIntegral_eq_zero_of_analyticOnNhd
      (cglNonprincipalDetectorRectangle_subset_gammaSafe r)
      (cglNonprincipalRegularizedMellinIntegrand_analyticOnGammaSafe X q z)

end RHTower

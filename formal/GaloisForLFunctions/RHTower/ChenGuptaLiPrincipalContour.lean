/-
# Chen--Gupta--Li principal-character detector contour

Formal finite-rectangle Cauchy formula for the pole-cleared principal-character branch.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiPrincipalResidue
import GaloisForLFunctions.RHTower.ChenGuptaLiNonprincipalAnalytic
import GaloisForLFunctions.RHTower.RectangleLocalCauchyFormula

open scoped BigOperators ComplexConjugate ENNReal NNReal Real

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- The principal `L`-factor after multiplication by its only possible pole. -/
def cglPrincipalPoleClearedFactor (X q : ℕ)
    (z : CGLPrincipalCriticalStripLZero q) (w : ℂ) : ℂ :=
  zeroDetectionMobiusPolynomial X (q + 1) z.character (z.point + w) *
    DirichletCharacter.LFunctionTrivChar₁ (q + 1) (z.point + w)

/-- The entire pole-cleared principal factor still vanishes at `w = 0`. -/
theorem cglPrincipalPoleClearedFactor_zero (X q : ℕ)
    (z : CGLPrincipalCriticalStripLZero q) :
    cglPrincipalPoleClearedFactor X q z 0 = 0 := by
  unfold cglPrincipalPoleClearedFactor
  simp only [add_zero]
  rw [DirichletCharacter.LFunctionTrivChar₁]
  rw [Function.update_of_ne z.point_ne_one]
  have hzero : DirichletCharacter.LFunctionTrivChar (q + 1) z.point = 0 := by
    simpa only [z.character_eq_one] using z.toCGLDirichletLZero.vanishes
  simp only [mul_eq_zero]
  exact Or.inr (Or.inr hzero)

/-- The pole-cleared principal factor is entire. -/
theorem cglPrincipalPoleClearedFactor_differentiable (X q : ℕ)
    (z : CGLPrincipalCriticalStripLZero q) :
    Differentiable ℂ (cglPrincipalPoleClearedFactor X q z) := by
  intro w
  unfold cglPrincipalPoleClearedFactor
  apply DifferentiableAt.mul
  · exact (differentiableAt_zeroDetectionMobiusPolynomial X (q + 1) z.character
      (z.point + w)).comp w
      ((differentiable_const z.point).differentiableAt.add differentiableAt_id)
  · exact (DirichletCharacter.differentiable_LFunctionTrivChar₁ (q + 1)).differentiableAt.comp w
      ((differentiable_const z.point).differentiableAt.add differentiableAt_id)

/-- Divided difference that globally removes the zero at the Mellin origin. -/
def cglPrincipalDetectorZeroQuotient (X q : ℕ)
    (z : CGLPrincipalCriticalStripLZero q) : ℂ → ℂ :=
  dslope (cglPrincipalPoleClearedFactor X q z) 0

/-- Exact global linear factorization at the cancelled Mellin origin. -/
theorem cglPrincipalPoleClearedFactor_eq_mul_zeroQuotient (X q : ℕ)
    (z : CGLPrincipalCriticalStripLZero q) (w : ℂ) :
    cglPrincipalPoleClearedFactor X q z w =
      w * cglPrincipalDetectorZeroQuotient X q z w := by
  simpa [cglPrincipalDetectorZeroQuotient, smul_eq_mul] using
    (sub_smul_dslope_of_zero (cglPrincipalPoleClearedFactor_zero X q z) w).symm

/-- The divided-difference quotient is entire. -/
theorem cglPrincipalDetectorZeroQuotient_analyticAt (X q : ℕ)
    (z : CGLPrincipalCriticalStripLZero q) (w : ℂ) :
    AnalyticAt ℂ (cglPrincipalDetectorZeroQuotient X q z) w := by
  unfold cglPrincipalDetectorZeroQuotient
  exact analyticAt_dslope_of_analyticAt
    ((cglPrincipalPoleClearedFactor_differentiable X q z).analyticAt 0)
    ((cglPrincipalPoleClearedFactor_differentiable X q z).analyticAt w)

/-- Analytic numerator of the sole remaining principal Mellin Cauchy kernel. -/
def cglPrincipalRegularizedMellinFactor (X q : ℕ)
    (z : CGLPrincipalCriticalStripLZero q) (w : ℂ) : ℂ :=
  Complex.Gamma (w + 1) * cglPrincipalDetectorZeroQuotient X q z w

/-- Off the origin and the principal L-pole, original detector integrand is
exactly the regularized Cauchy kernel. -/
theorem cglPrincipalDetectorMellinIntegrand_eq_regularized_off_poles (X q : ℕ)
    (z : CGLPrincipalCriticalStripLZero q) (w : ℂ)
    (hw0 : w ≠ 0) (hwp : w ≠ cglPrincipalPole z) :
    cglDetectorMellinIntegrand X q z.toCGLCriticalStripLZero w =
      cglPrincipalRegularizedMellinFactor X q z w * (w - cglPrincipalPole z)⁻¹ := by
  have hshift : z.point + w ≠ 1 := by
    intro h
    apply hwp
    unfold cglPrincipalPole
    calc
      w = (z.point + w) - z.point := by ring
      _ = 1 - z.point := by rw [h]
  have hfactor :
      zeroDetectionMobiusPolynomial X (q + 1) z.character (z.point + w) *
        DirichletCharacter.LFunction z.character (z.point + w) =
      cglPrincipalPoleClearedFactor X q z w * (w - cglPrincipalPole z)⁻¹ := by
    rw [z.character_eq_one]
    unfold cglPrincipalPoleClearedFactor
    rw [z.character_eq_one]
    rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hshift]
    have hscalar : z.point + w - 1 = w - cglPrincipalPole z := by
      unfold cglPrincipalPole
      ring
    rw [hscalar]
    field_simp [sub_ne_zero.mpr hwp]
  calc
    cglDetectorMellinIntegrand X q z.toCGLCriticalStripLZero w =
        Complex.Gamma w *
          (zeroDetectionMobiusPolynomial X (q + 1) z.character (z.point + w) *
            DirichletCharacter.LFunction z.character (z.point + w)) := rfl
    _ = Complex.Gamma w *
          (cglPrincipalPoleClearedFactor X q z w * (w - cglPrincipalPole z)⁻¹) := by
        rw [hfactor]
    _ = cglPrincipalRegularizedMellinFactor X q z w * (w - cglPrincipalPole z)⁻¹ := by
        rw [cglPrincipalPoleClearedFactor_eq_mul_zeroQuotient,
          cglPrincipalRegularizedMellinFactor, Complex.Gamma_add_one w hw0]
        ring

/-- Regularized principal factor is analytic through the safe Gamma half-plane. -/
theorem cglPrincipalRegularizedMellinFactor_analyticOnGammaSafe (X q : ℕ)
    (z : CGLPrincipalCriticalStripLZero q) :
    AnalyticOnNhd ℂ (cglPrincipalRegularizedMellinFactor X q z)
      cglGammaSafeHalfPlane := by
  intro w hw
  unfold cglGammaSafeHalfPlane at hw
  unfold cglPrincipalRegularizedMellinFactor
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
  · exact cglPrincipalDetectorZeroQuotient_analyticAt X q z w

/-- Finite safe rectangle enclosing cancelled Mellin origin and principal pole. -/
structure CGLPrincipalDetectorRectangle (z : CGLPrincipalCriticalStripLZero q)
    extends CGLNonprincipalDetectorRectangle where
  principal_re_lt_upper : (cglPrincipalPole z).re < upper.re
  lower_im_lt_principal : lower.im < (cglPrincipalPole z).im
  principal_im_lt_upper : (cglPrincipalPole z).im < upper.im

/-- A certified principal rectangle lies in regularized Gamma half-plane. -/
theorem cglPrincipalDetectorRectangle_subset_gammaSafe
    (r : CGLPrincipalDetectorRectangle z) :
    (uIcc r.lower.re r.upper.re ×ℂ uIcc r.lower.im r.upper.im) ⊆
      cglGammaSafeHalfPlane :=
  cglNonprincipalDetectorRectangle_subset_gammaSafe r.toCGLNonprincipalDetectorRectangle

/-- Lower horizontal edge avoids principal L-pole. -/
theorem cglPrincipalDetectorRectangle_bottom_ne_principal
    (r : CGLPrincipalDetectorRectangle z) (x : ℝ)
    (_hx : x ∈ uIcc r.lower.re r.upper.re) :
    (x : ℂ) + r.lower.im * I ≠ cglPrincipalPole z := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_add, mul_one] at him
  linarith [r.lower_im_lt_principal]

/-- Upper horizontal edge avoids principal L-pole. -/
theorem cglPrincipalDetectorRectangle_top_ne_principal
    (r : CGLPrincipalDetectorRectangle z) (x : ℝ)
    (_hx : x ∈ uIcc r.lower.re r.upper.re) :
    (x : ℂ) + r.upper.im * I ≠ cglPrincipalPole z := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_add, mul_one] at him
  linarith [r.principal_im_lt_upper]

/-- Right vertical edge avoids principal L-pole. -/
theorem cglPrincipalDetectorRectangle_right_ne_principal
    (r : CGLPrincipalDetectorRectangle z) (y : ℝ)
    (_hy : y ∈ uIcc r.lower.im r.upper.im) :
    (r.upper.re : ℂ) + y * I ≠ cglPrincipalPole z := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero] at hre
  linarith [r.principal_re_lt_upper]

/-- Left vertical edge avoids principal L-pole. -/
theorem cglPrincipalDetectorRectangle_left_ne_principal
    (r : CGLPrincipalDetectorRectangle z) (y : ℝ)
    (_hy : y ∈ uIcc r.lower.im r.upper.im) :
    (r.lower.re : ℂ) + y * I ≠ cglPrincipalPole z := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero] at hre
  linarith [r.toCGLNonprincipalDetectorRectangle.lower_re_lt_zero,
    cglPrincipalPole_re_pos z]

/-- **Finite principal contour shift.** Original detector integral on a
certified rectangle equals `2πi` times regularized factor at principal pole. -/
theorem rectIntegral_cglPrincipalDetectorMellinIntegrand (X q : ℕ)
    (z : CGLPrincipalCriticalStripLZero q) (r : CGLPrincipalDetectorRectangle z) :
    rectIntegral (cglDetectorMellinIntegrand X q z.toCGLCriticalStripLZero) r.lower r.upper =
      2 * Real.pi * I * cglPrincipalRegularizedMellinFactor X q z (cglPrincipalPole z) := by
  calc
    rectIntegral (cglDetectorMellinIntegrand X q z.toCGLCriticalStripLZero) r.lower r.upper =
        rectIntegral (fun w => cglPrincipalRegularizedMellinFactor X q z w *
          (w - cglPrincipalPole z)⁻¹) r.lower r.upper := by
      apply rectIntegral_congr (S := ({0, cglPrincipalPole z}ᶜ : Set ℂ))
      · intro w hw
        rw [mem_compl_iff] at hw
        have hw0 : w ≠ 0 := by
          intro h0
          apply hw
          simp [h0]
        have hwp : w ≠ cglPrincipalPole z := by
          intro hp
          apply hw
          simp [hp]
        exact cglPrincipalDetectorMellinIntegrand_eq_regularized_off_poles X q z w hw0 hwp
      · intro x hx
        rw [mem_compl_iff]
        intro hmem
        have hor : (x : ℂ) + r.lower.im * I = 0 ∨
            (x : ℂ) + r.lower.im * I = cglPrincipalPole z := by
          simpa only [mem_insert_iff, mem_singleton_iff] using hmem
        exact hor.elim
          (cglNonprincipalDetectorRectangle_bottom_ne_zero
            r.toCGLNonprincipalDetectorRectangle x hx)
          (cglPrincipalDetectorRectangle_bottom_ne_principal r x hx)
      · intro x hx
        rw [mem_compl_iff]
        intro hmem
        have hor : (x : ℂ) + r.upper.im * I = 0 ∨
            (x : ℂ) + r.upper.im * I = cglPrincipalPole z := by
          simpa only [mem_insert_iff, mem_singleton_iff] using hmem
        exact hor.elim
          (cglNonprincipalDetectorRectangle_top_ne_zero
            r.toCGLNonprincipalDetectorRectangle x hx)
          (cglPrincipalDetectorRectangle_top_ne_principal r x hx)
      · intro y hy
        rw [mem_compl_iff]
        intro hmem
        have hor : (r.upper.re : ℂ) + y * I = 0 ∨
            (r.upper.re : ℂ) + y * I = cglPrincipalPole z := by
          simpa only [mem_insert_iff, mem_singleton_iff] using hmem
        exact hor.elim
          (cglNonprincipalDetectorRectangle_right_ne_zero
            r.toCGLNonprincipalDetectorRectangle y hy)
          (cglPrincipalDetectorRectangle_right_ne_principal r y hy)
      · intro y hy
        rw [mem_compl_iff]
        intro hmem
        have hor : (r.lower.re : ℂ) + y * I = 0 ∨
            (r.lower.re : ℂ) + y * I = cglPrincipalPole z := by
          simpa only [mem_insert_iff, mem_singleton_iff] using hmem
        exact hor.elim
          (cglNonprincipalDetectorRectangle_left_ne_zero
            r.toCGLNonprincipalDetectorRectangle y hy)
          (cglPrincipalDetectorRectangle_left_ne_principal r y hy)
    _ = 2 * Real.pi * I * cglPrincipalRegularizedMellinFactor X q z (cglPrincipalPole z) :=
      rectIntegral_cauchyFormula_of_analyticOnNhd
        (cglPrincipalRegularizedMellinFactor_analyticOnGammaSafe X q z)
        (cglPrincipalDetectorRectangle_subset_gammaSafe r)
        (r.toCGLNonprincipalDetectorRectangle.lower_re_lt_zero.trans
          (cglPrincipalPole_re_pos z))
        r.principal_re_lt_upper r.lower_im_lt_principal r.principal_im_lt_upper

end

end RHTower

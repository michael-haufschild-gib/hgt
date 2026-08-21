/-
# Primitive class-I zero contours for the Chen--Gupta--Li detector

Chen--Gupta--Li's class-I branch starts with primitive nonprincipal zeros
strictly right of the critical line.  This module packages exactly those
actual centered-window zeros, supplies their canonical detector rectangles,
and puts every horizontal detector point in the right half-plane while
retaining the proved polynomial Dirichlet-L strip bound.

No RH, GRH, zero-density estimate, detector alternative, or large-value
bound is used.
-/

import GaloisForLFunctions.RHTower.DirichletLZeroDensityDetectorBridge
import GaloisForLFunctions.RHTower.DirichletLPhragmenInputs
import GaloisForLFunctions.RHTower.ChenGuptaLiMollifierBound

open Complex

noncomputable section

namespace RHTower

/-- A nonprincipal Dirichlet character with a certified primitive conductor. -/
abbrev PrimitiveNonprincipalDirichletCharacter (n : ℕ) :=
  {χ : NonprincipalDirichletCharacter n // DirichletCharacter.IsPrimitive χ.1}

/-- A nonprincipal critical-strip CGL zero whose character is primitive. -/
structure CGLPrimitiveNonprincipalCriticalStripLZero (n : ℕ)
    extends CGLNonprincipalCriticalStripLZero n where
  primitive : DirichletCharacter.IsPrimitive character

/-- An actual centered-window primitive zero strictly right of the critical
line, namely a CGL class-I zero carrier. -/
def CGLPrimitiveClassIWindowZero
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) :=
  {z : CGLZeroDensityVerticalWindowZero n χ.1 (1 / 2) τ H // (1 / 2 : ℝ) < z.1.re}

/-- Upgrade an actual primitive class-I window zero to the exact CGL zero
data required by the nonprincipal detector contour. -/
def cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    CGLPrimitiveNonprincipalCriticalStripLZero n :=
  CGLPrimitiveNonprincipalCriticalStripLZero.mk
    (cglNonprincipalCriticalStripLZeroOfWindowPoint n χ.1 τ H z.1) χ.2

/-- A canonical finite CGL detector rectangle for a primitive class-I zero.
Its lower edge shifts the zero exactly to the critical line and its upper edge
is the safe Mellin line of real part `2`. -/
def cglPrimitiveClassICanonicalRectangle
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) (K : ℕ) :
    CGLNonprincipalDetectorRectangle where
  lower := ((1 / 2 : ℝ) - z.1.1.re : ℂ) + (-((K + 1 : ℕ) : ℝ) : ℂ) * I
  upper := (2 : ℂ) + ((K + 1 : ℕ) : ℂ) * I
  lower_re_gt_neg_one := by
    simp
    have hlt := (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).lt_one
    change z.1.1.re < 1 at hlt
    linarith
  lower_re_lt_zero := by
    simp
    linarith [z.2]
  zero_re_lt_upper := by norm_num
  lower_im_lt_zero := by
    norm_num [Complex.add_im, Complex.mul_im]
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    linarith
  zero_im_lt_upper := by
    norm_num [Complex.add_im, Complex.mul_im]
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    linarith

/-- A point on a canonical class-I horizontal detector edge, shifted from its
actual zero.  Its real part is certified to lie in the Mollifier's right
half-plane. -/
def cglPrimitiveClassIHorizontalShiftPoint
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H)
    (u : Set.Icc ((1 / 2 : ℝ) - z.1.1.re) 2) (K : ℕ) : CGLRightHalfPlanePoint :=
  ⟨z.1.1 + (u.1 : ℂ) + ((K + 1 : ℕ) : ℂ) * I, by
    simp
    linarith [u.2.1]⟩

/-- The finite Möbius detector is uniformly bounded by its literal cutoff at
every canonical primitive class-I horizontal point. -/
theorem norm_cglPrimitiveClassIHorizontalShift_mollifier_le
    (X n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H)
    (u : Set.Icc ((1 / 2 : ℝ) - z.1.1.re) 2) (K : ℕ) :
    ‖zeroDetectionMobiusPolynomial X (n + 1) χ.1.1
      (cglPrimitiveClassIHorizontalShiftPoint n χ τ H z u K).1‖ ≤ (X + 1 : ℕ) :=
  norm_zeroDetectionMobiusPolynomial_le_cutoff X (n + 1) χ.1.1
    (cglPrimitiveClassIHorizontalShiftPoint n χ τ H z u K)

/-- The proved primitive Dirichlet-L Phragmén--Lindelöf estimate applies on
all canonical class-I horizontal detector edges. -/
theorem exists_cglPrimitiveClassIHorizontalShift_LFunction_bound
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Set.Icc ((1 / 2 : ℝ) - z.1.1.re) 2) (K : ℕ),
      ‖DirichletCharacter.LFunction χ.1.1
        (cglPrimitiveClassIHorizontalShiftPoint n χ τ H z u K).1‖ ≤
        C * ‖(cglPrimitiveClassIHorizontalShiftPoint n χ τ H z u K).1 - 4‖ ^ 3 := by
  obtain ⟨C, hC, hbound⟩ := bound_LFunction_strip χ.1.2 χ.2
  refine ⟨C, hC, fun u K => hbound _ ?_ ?_⟩
  · have hlow : -2 ≤ z.1.1.re + u.1 := by linarith [u.2.1]
    simpa [cglPrimitiveClassIHorizontalShiftPoint] using hlow
  · have hhigh : z.1.1.re + u.1 ≤ 3 := by
      have hlt := (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).lt_one
      change z.1.1.re < 1 at hlt
      linarith [u.2.2, hlt]
    simpa [cglPrimitiveClassIHorizontalShiftPoint] using hhigh

end RHTower

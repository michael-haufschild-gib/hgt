import GaloisForLFunctions.RHTower.GaussianEulerContinuumRelativeFormation
import GaloisForLFunctions.RHTower.XiGuinandWeilSpectralRectangle

/-!
# Formation-anchored completed contour charge

Scalar contour side of FACHD.  The completed endpoint is the literal continued prime--Gamma
source current; the positive Gaussian endpoint is the zero-free Euler--continuum formation.
Their relative rectangle charge is therefore the exact multiplicity-copy count of the enclosed
Xi divisor, while every pair of positive Gaussian anchors has zero mutual charge.
-/

noncomputable section

open Complex Set
open scoped BigOperators

namespace RHTower

/-- Completed prime--Gamma rectangle winding, normalized by `2πi`. -/
def formationCompletedRectangleWinding (z₁ z₂ : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    rectIntegral continuedPrimeArchSourceRelativeTrace z₁ z₂

/-- Relative completed-to-Gaussian formation charge at positive anchor `x`. -/
def formationAnchoredRectangleCharge (x : ℝ) (z₁ z₂ : ℂ) : ℂ :=
  formationCompletedRectangleWinding z₁ z₂ -
    gaussianFormationRectangleWinding x z₁ z₂

/-- The completed source contour is exactly the enclosed Xi multiplicity-copy cardinality. -/
theorem formationCompletedRectangleWinding_eq_xiMultiplicityCopies
    {z₁ z₂ : ℂ} (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * Complex.I))
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * Complex.I))
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * Complex.I))
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * Complex.I)) :
    formationCompletedRectangleWinding z₁ z₂ =
      ((xiZeroCopyClosedRectangle z₁ z₂).card : ℂ) := by
  have h :=
    rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_xiZeroCopyClosedRectangleSum
      (g := fun _ : ℂ => 1) analyticOnNhd_const hre him hbot htop hright hleft
  simp only [one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [formationCompletedRectangleWinding, h]
  have hnorm : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  field_simp

/-- Every positive Gaussian anchor contributes zero rectangle winding. -/
theorem formationAnchoredRectangleCharge_eq_completed
    {x : ℝ} (hx : 0 < x) {z₁ z₂ : ℂ}
    (hz₁ : 0 < z₁.re) (hz₂ : 0 < z₂.re) :
    formationAnchoredRectangleCharge x z₁ z₂ =
      formationCompletedRectangleWinding z₁ z₂ := by
  rw [formationAnchoredRectangleCharge,
    gaussianFormationRectangleWinding_eq_zero hx hz₁ hz₂, sub_zero]

/-- Literal FACHD contour law: completed-to-Gaussian charge equals enclosed Xi multiplicity. -/
theorem formationAnchoredRectangleCharge_eq_xiMultiplicityCopies
    {x : ℝ} (hx : 0 < x) {z₁ z₂ : ℂ}
    (hz₁ : 0 < z₁.re) (hz₂ : 0 < z₂.re)
    (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ r ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((r : ℂ) + z₁.im * Complex.I))
    (htop : ∀ r ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((r : ℂ) + z₂.im * Complex.I))
    (hright : ∀ t ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + t * Complex.I))
    (hleft : ∀ t ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + t * Complex.I)) :
    formationAnchoredRectangleCharge x z₁ z₂ =
      ((xiZeroCopyClosedRectangle z₁ z₂).card : ℂ) := by
  rw [formationAnchoredRectangleCharge_eq_completed hx hz₁ hz₂]
  exact formationCompletedRectangleWinding_eq_xiMultiplicityCopies
    hre him hbot htop hright hleft

/-- Any two positive Gaussian anchors have zero mutual rectangle charge. -/
theorem gaussianFormationMutualRectangleCharge_eq_zero
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) {z₁ z₂ : ℂ}
    (hz₁ : 0 < z₁.re) (hz₂ : 0 < z₂.re) :
    gaussianFormationRectangleWinding x z₁ z₂ -
      gaussianFormationRectangleWinding y z₁ z₂ = 0 := by
  rw [gaussianFormationRectangleWinding_eq_zero hx hz₁ hz₂,
    gaussianFormationRectangleWinding_eq_zero hy hz₁ hz₂, sub_zero]

/-- Closed certificate for FACHD's source-owned scalar endpoint law and anchor independence. -/
theorem formationAnchoredCubicContourCharge_closed :
    (∀ (x y : ℝ), 0 < x → 0 < y → ∀ (z₁ z₂ : ℂ),
      0 < z₁.re → 0 < z₂.re →
      gaussianFormationRectangleWinding x z₁ z₂ -
        gaussianFormationRectangleWinding y z₁ z₂ = 0) ∧
    (∀ (x : ℝ), 0 < x → ∀ (z₁ z₂ : ℂ),
      0 < z₁.re → 0 < z₂.re → z₁.re < z₂.re → z₁.im < z₂.im →
      (∀ r ∈ uIcc z₁.re z₂.re,
        XiExplicitAdmissible ((r : ℂ) + z₁.im * Complex.I)) →
      (∀ r ∈ uIcc z₁.re z₂.re,
        XiExplicitAdmissible ((r : ℂ) + z₂.im * Complex.I)) →
      (∀ t ∈ uIcc z₁.im z₂.im,
        XiExplicitAdmissible ((z₂.re : ℂ) + t * Complex.I)) →
      (∀ t ∈ uIcc z₁.im z₂.im,
        XiExplicitAdmissible ((z₁.re : ℂ) + t * Complex.I)) →
      formationAnchoredRectangleCharge x z₁ z₂ =
        ((xiZeroCopyClosedRectangle z₁ z₂).card : ℂ)) := by
  constructor
  · intro x y hx hy z₁ z₂ hz₁ hz₂
    exact gaussianFormationMutualRectangleCharge_eq_zero hx hy hz₁ hz₂
  · intro x hx z₁ z₂ hz₁ hz₂ hre him hbot htop hright hleft
    exact formationAnchoredRectangleCharge_eq_xiMultiplicityCopies
      hx hz₁ hz₂ hre him hbot htop hright hleft

end RHTower

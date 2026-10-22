import GaloisForLFunctions.RHTower.XiEntireReal
import GaloisForLFunctions.HTGeometry.ParabolicCayleyAutomorphism

/-!
# The rank-one dilation obstruction for the Hedenmalm source system

The most direct one-channel Hilbert dilation of the folded Hedenmalm Dirac system couples the
source to a single scalar level.  Eliminating that level at a spectral parameter leaves the
characteristic equation `a - z - C[mu](z) = 0`, where `C[mu]` is the Cauchy transform of the
positive source spectral measure.  That function is passive: above the real axis its imaginary part
is strictly negative, so it has no zeros there.

Consequently a rank-one dilation whose characteristic function reproduces `XiC` above the real axis
exists only if `XiC` has no zero there.  The ansatz is therefore a re-encoding of the missing
statement, not a route to it, and a single off-axis Xi zero obstructs every such identification.
-/

open Complex MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- The characteristic function of the one-channel rank-one self-adjoint dilation with source
spectral measure `mu` and scalar level `a`. -/
def rankOneDilationCharacteristic (a : ℝ) (μ : Measure ℝ) (z : ℂ) : ℂ :=
  (a : ℂ) - z - cauchyTransform μ z

/-- **Passivity of the rank-one dilation.**  Its characteristic function has strictly negative
imaginary part above the real axis: the Cauchy transform of a positive source measure is Herglotz,
so it can only add to the drift of `-z`. -/
theorem im_rankOneDilationCharacteristic_neg (a : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    {z : ℂ} (hz : 0 < z.im) : (rankOneDilationCharacteristic a μ z).im < 0 := by
  have him : 0 ≤ (cauchyTransform μ z).im := by
    rcases eq_or_ne μ 0 with rfl | hμ
    · simp [cauchyTransform]
    · exact (im_cauchyTransform_pos_of_ne_zero μ hμ hz).le
  simp only [rankOneDilationCharacteristic, Complex.sub_im, Complex.ofReal_im]
  linarith

/-- Hence every eigenvalue of the rank-one dilation is real. -/
theorem rankOneDilationCharacteristic_ne_zero (a : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    {z : ℂ} (hz : 0 < z.im) : rankOneDilationCharacteristic a μ z ≠ 0 := by
  intro h
  have hlt := im_rankOneDilationCharacteristic_neg a μ hz
  rw [h] at hlt
  simp at hlt

/-- **The rank-one dilation ansatz is exactly the zero-free upper half plane.**  If a rank-one
characteristic function agrees with `XiC` above the real axis then `XiC` has no zero there, so the
ansatz is a re-encoding of the missing statement rather than a route to it. -/
theorem XiC_ne_zero_of_rankOneDilationCharacteristic_eq (a : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (heq : ∀ z : ℂ, 0 < z.im → rankOneDilationCharacteristic a μ z = XiC z)
    {z : ℂ} (hz : 0 < z.im) : XiC z ≠ 0 := by
  rw [← heq z hz]
  exact rankOneDilationCharacteristic_ne_zero a μ hz

/-- **No finite rank-one Friedrichs dilation is the missing Hedenmalm realization.**  A single zero
of `XiC` off the real axis obstructs every such identification, for every scalar level and every
finite positive source measure. -/
theorem not_forall_rankOneDilationCharacteristic_eq_XiC
    {α : ℂ} (hα : XiC α = 0) (hαim : α.im ≠ 0) (a : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ¬ ∀ z : ℂ, 0 < z.im → rankOneDilationCharacteristic a μ z = XiC z := by
  intro heq
  rcases lt_or_gt_of_ne hαim with hneg | hpos
  · have h1 : XiC (-α) = 0 := by rw [XiC_even]; exact hα
    have h2 : 0 < (-α).im := by
      rw [Complex.neg_im]
      linarith
    exact XiC_ne_zero_of_rankOneDilationCharacteristic_eq a μ heq h2 h1
  · exact XiC_ne_zero_of_rankOneDilationCharacteristic_eq a μ heq hpos hα

end RHTower

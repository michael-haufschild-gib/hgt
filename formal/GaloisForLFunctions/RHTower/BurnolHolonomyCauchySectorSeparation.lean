import GaloisForLFunctions.RHTower.BurnolCoPoissonQuotientOrder
import GaloisForLFunctions.RHTower.BurnolDividedShiftPhysicalDissipativity

/-!
# Sector separation between Burnol holonomy and the Cauchy divided shift

Finite bilateral aperture holonomies are Fourier-odd. The one-sided Mellin divided shift is
strictly accretive on every nonzero vector in the open right half-plane. These operator sectors
cannot meet: Fourier oddness reverses a quadratic form along the cosine orbit, whereas strict
accretivity makes both orbit values positive.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- Strict accretivity of the physical Mellin divided shift on every nonzero vector. -/
theorem re_inner_burnolMellinDividedShift_pos
    {rho : ℂ} (h : 1 / 2 < rho.re) {f : evenSubspace} (hf : f ≠ 0) :
    0 < (inner ℂ f (burnolMellinDividedShift h f)).re := by
  rw [re_inner_burnolMellinDividedShift_eq h]
  have hshift : burnolMellinDividedShift h f ≠ 0 := by
    intro hz
    have hinner := burnolMellinDividedShift_inner_ne_zero h hf
    apply hinner
    rw [hz, inner_zero_right]
  exact mul_pos (by linarith) (sq_pos_of_pos (norm_pos_iff.mpr hshift))

/-- No one-sided Mellin divided shift is an uncompressed finite bilateral aperture holonomy. -/
theorem burnolMellinDividedShift_ne_bilateralApertureHolonomy
    {rho : ℂ} (h : 1 / 2 < rho.re)
    (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r) :
    burnolMellinDividedShift h ≠
      burnolExtendedBilateralApertureHolonomy a ha r hr := by
  intro heq
  let f : evenSubspace := burnolFixedSubWindowSourceAtom
  have hf : f ≠ 0 := burnolFixedSubWindowSourceAtom_ne_zero
  have hJf : soninCosineUnitary f ≠ 0 := by
    intro hz
    have hz' := congrArg soninCosineUnitary hz
    rw [soninCosineUnitary_involutive, map_zero] at hz'
    exact hf hz'
  have hodd := burnolExtendedBilateralApertureHolonomy_cosine_odd a ha r hr f
  rw [← heq] at hodd
  have hform :
      inner ℂ (soninCosineUnitary f)
          (burnolMellinDividedShift h (soninCosineUnitary f)) =
        -inner ℂ f (burnolMellinDividedShift h f) := by
    rw [hodd, inner_neg_right, soninCosineUnitary.inner_map_map]
  have hpos := re_inner_burnolMellinDividedShift_pos h hf
  have hJpos := re_inner_burnolMellinDividedShift_pos h hJf
  rw [hform] at hJpos
  simp only [Complex.neg_re] at hJpos
  linarith

/-- No one-sided Mellin divided shift is a quotient-compressed finite bilateral aperture
holonomy. -/
theorem burnolMellinDividedShift_ne_compressedHolonomy
    {rho : ℂ} (h : 1 / 2 < rho.re)
    (b : ℝ) (hb : 0 < b) (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r) :
    burnolMellinDividedShift h ≠
      burnolCoPoissonCompressedHolonomy b hb a ha r hr := by
  intro heq
  let f : evenSubspace := burnolFixedSubWindowSourceAtom
  have hf : f ≠ 0 := burnolFixedSubWindowSourceAtom_ne_zero
  have hJf : soninCosineUnitary f ≠ 0 := by
    intro hz
    have hz' := congrArg soninCosineUnitary hz
    rw [soninCosineUnitary_involutive, map_zero] at hz'
    exact hf hz'
  let H := burnolCoPoissonCompressedHolonomy b hb a ha r hr
  have hoddOp : evenFourierTransform * H * evenFourierTransform = -H := by
    simpa only [H] using
      burnolCoPoissonCompressedHolonomy_fourier_odd b hb a ha r hr
  have hoddPoint : H (soninCosineUnitary f) = -soninCosineUnitary (H f) := by
    have hx := congrArg
      (fun T : evenSubspace →L[ℂ] evenSubspace => T (evenFourierTransform f)) hoddOp
    simp only [mul_apply_eq_comp, neg_apply, evenFourierTransform_involutive] at hx
    change soninCosineUnitary (H f) = -H (soninCosineUnitary f) at hx
    have hx' := congrArg Neg.neg hx
    simpa only [neg_neg] using hx'.symm
  have heq' : burnolMellinDividedShift h = H := by
    simpa only [H] using heq
  have hform :
      inner ℂ (soninCosineUnitary f)
          (burnolMellinDividedShift h (soninCosineUnitary f)) =
        -inner ℂ f (burnolMellinDividedShift h f) := by
    rw [heq', hoddPoint, inner_neg_right,
      soninCosineUnitary.inner_map_map, ← heq']
  have hpos := re_inner_burnolMellinDividedShift_pos h hf
  have hJpos := re_inner_burnolMellinDividedShift_pos h hJf
  rw [hform] at hJpos
  simp only [Complex.neg_re] at hJpos
  linarith

end RHTower

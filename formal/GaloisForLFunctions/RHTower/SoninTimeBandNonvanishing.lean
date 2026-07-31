import GaloisForLFunctions.RHTower.SoninTimeBandHilbertSchmidt

/-!
# A nondegenerate time band is a nonzero operator

The finite time-band Fourier operator has squared Hilbert--Schmidt norm exactly the area of its
rectangle.  For a nondegenerate rectangle that area is positive, so the operator cannot vanish.

This is the nonvanishing input the aperture coupling question needs: the coupling is congruent to a
sum of four such blocks, and any argument that they fail to cancel has to start from each being
nonzero.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- **Nondegenerate time bands are nonzero.**  The rectangle-area formula for the squared
Hilbert--Schmidt norm forces it. -/
theorem fullTimeBandFourier_ne_zero
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hablt : a < b) (hcdlt : c < d) :
    fullTimeBandFourier a b c d hab ≠ 0 := by
  intro hzero
  have hHS := isHilbertSchmidt_fullTimeBandFourier a b c d hab
  have h0 : ContinuousLinearMap.hsNormSq (fullTimeBandFourier a b c d hab) = 0 :=
    (ContinuousLinearMap.hsNormSq_eq_zero_iff hHS).mpr hzero
  rw [hsNormSq_fullTimeBandFourier_eq_rectangleArea a b c d hab hcd] at h0
  have hpos : (0 : ℝ) < (b - a) * (d - c) :=
    mul_pos (sub_pos.mpr hablt) (sub_pos.mpr hcdlt)
  exact absurd h0 (ne_of_gt hpos)

/-- Positive rectangle energy, stated directly. -/
theorem hsNormSq_fullTimeBandFourier_pos
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hablt : a < b) (hcdlt : c < d) :
    0 < ContinuousLinearMap.hsNormSq (fullTimeBandFourier a b c d hab) := by
  rw [hsNormSq_fullTimeBandFourier_eq_rectangleArea a b c d hab hcd]
  exact mul_pos (sub_pos.mpr hablt) (sub_pos.mpr hcdlt)

/-- The energy is strictly monotone in the rectangle: enlarging either side strictly increases it,
so distinct nondegenerate bands are distinguished by their Hilbert--Schmidt energy alone. -/
theorem hsNormSq_fullTimeBandFourier_lt_of_lt
    {a b b' c d : ℝ} (hab : a ≤ b) (hab' : a ≤ b') (hcd : c ≤ d)
    (hbb' : b < b') (hcdlt : c < d) :
    ContinuousLinearMap.hsNormSq (fullTimeBandFourier a b c d hab) <
      ContinuousLinearMap.hsNormSq (fullTimeBandFourier a b' c d hab') := by
  rw [hsNormSq_fullTimeBandFourier_eq_rectangleArea a b c d hab hcd,
    hsNormSq_fullTimeBandFourier_eq_rectangleArea a b' c d hab' hcd]
  have hd : (0 : ℝ) < d - c := sub_pos.mpr hcdlt
  nlinarith [hbb', hd]

end RHTower

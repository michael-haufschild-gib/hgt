import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowPassiveNoGo

/-!
# Real Möbius postcomposition cannot repair sharp-window passivity

The raw dyadic sharp-window impedance takes both imaginary signs above every height.  This file
closes the full boundary-preserving scalar Möbius escape hatch.  A real fractional-linear map
multiplies imaginary part by its real determinant and divides by a strictly positive norm square.
Consequently every nondegenerate real Möbius postcomposition still takes both signs arbitrarily
high and is neither Herglotz nor anti-Herglotz on any upper tail.

No continuation, zero, or RH hypothesis occurs.
-/

open Complex

namespace RHTower

noncomputable section

/-- Real boundary-preserving Möbius postcomposition. -/
def realMobiusResponse (a b c d : ℝ) (w : ℂ) : ℂ :=
  ((a : ℂ) * w + b) / ((c : ℂ) * w + d)

/-- Exact imaginary-part transport by a real Möbius map. -/
theorem realMobiusResponse_im (a b c d : ℝ) (w : ℂ) :
    (realMobiusResponse a b c d w).im =
      (a * d - b * c) * w.im /
        Complex.normSq ((c : ℂ) * w + d) := by
  rw [realMobiusResponse, Complex.div_im]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  ring

/-- At a nonreal value, a nondegenerate real Möbius denominator cannot vanish. -/
theorem realMobiusResponse_denom_ne_of_im_ne_zero
    {a b c d : ℝ} {w : ℂ} (hdet : a * d - b * c ≠ 0) (hw : w.im ≠ 0) :
    (c : ℂ) * w + d ≠ 0 := by
  intro hzero
  have him := congrArg Complex.im hzero
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.zero_im] at him
  have hc : c = 0 := (mul_eq_zero.mp him).resolve_right hw
  have hre := congrArg Complex.re hzero
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.zero_re, hc] at hre
  have hd : d = 0 := by simpa using hre
  apply hdet
  rw [hc, hd]
  ring

/-- Every nondegenerate real Möbius transform has negative-imaginary values above every height. -/
theorem exists_high_realMobius_dyadicSharpPrimeImpedance_im_neg
    {a b c d : ℝ} (hdet : a * d - b * c ≠ 0) (Y : ℝ) :
    ∃ z : ℂ, Y < z.im ∧
      (realMobiusResponse a b c d (dyadicSharpPrimeImpedance z)).im < 0 := by
  rcases lt_or_gt_of_ne hdet with hdetneg | hdetpos
  · obtain ⟨z, hz, hpos⟩ := exists_high_dyadicSharpPrimeImpedance_im_pos Y
    refine ⟨z, hz, ?_⟩
    have hden := realMobiusResponse_denom_ne_of_im_ne_zero hdet hpos.ne'
    rw [realMobiusResponse_im a b c d]
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hdetneg hpos)
      (Complex.normSq_pos.mpr hden)
  · obtain ⟨z, hz, hneg⟩ := exists_high_dyadicSharpPrimeImpedance_im_neg Y
    refine ⟨z, hz, ?_⟩
    have hden := realMobiusResponse_denom_ne_of_im_ne_zero hdet hneg.ne
    rw [realMobiusResponse_im a b c d]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hdetpos hneg)
      (Complex.normSq_pos.mpr hden)

/-- Every nondegenerate real Möbius transform has positive-imaginary values above every height. -/
theorem exists_high_realMobius_dyadicSharpPrimeImpedance_im_pos
    {a b c d : ℝ} (hdet : a * d - b * c ≠ 0) (Y : ℝ) :
    ∃ z : ℂ, Y < z.im ∧
      0 < (realMobiusResponse a b c d (dyadicSharpPrimeImpedance z)).im := by
  rcases lt_or_gt_of_ne hdet with hdetneg | hdetpos
  · obtain ⟨z, hz, hneg⟩ := exists_high_dyadicSharpPrimeImpedance_im_neg Y
    refine ⟨z, hz, ?_⟩
    have hden := realMobiusResponse_denom_ne_of_im_ne_zero hdet hneg.ne
    rw [realMobiusResponse_im a b c d]
    exact div_pos (mul_pos_of_neg_of_neg hdetneg hneg) (Complex.normSq_pos.mpr hden)
  · obtain ⟨z, hz, hpos⟩ := exists_high_dyadicSharpPrimeImpedance_im_pos Y
    refine ⟨z, hz, ?_⟩
    have hden := realMobiusResponse_denom_ne_of_im_ne_zero hdet hpos.ne'
    rw [realMobiusResponse_im a b c d]
    exact div_pos (mul_pos hdetpos hpos) (Complex.normSq_pos.mpr hden)

/-- No nondegenerate real Möbius postcomposition is upper-half-plane valued on an upper tail. -/
theorem realMobius_dyadicSharpPrimeImpedance_not_upperHalfPlaneValued_above
    {a b c d : ℝ} (hdet : a * d - b * c ≠ 0) (Y : ℝ) :
    ¬ (∀ z : ℂ, Y < z.im →
      0 ≤ (realMobiusResponse a b c d (dyadicSharpPrimeImpedance z)).im) := by
  intro h
  obtain ⟨z, hz, hneg⟩ :=
    exists_high_realMobius_dyadicSharpPrimeImpedance_im_neg hdet Y
  exact hneg.not_ge (h z hz)

/-- No nondegenerate real Möbius postcomposition is lower-half-plane valued on an upper tail. -/
theorem realMobius_dyadicSharpPrimeImpedance_not_lowerHalfPlaneValued_above
    {a b c d : ℝ} (hdet : a * d - b * c ≠ 0) (Y : ℝ) :
    ¬ (∀ z : ℂ, Y < z.im →
      (realMobiusResponse a b c d (dyadicSharpPrimeImpedance z)).im ≤ 0) := by
  intro h
  obtain ⟨z, hz, hpos⟩ :=
    exists_high_realMobius_dyadicSharpPrimeImpedance_im_pos hdet Y
  exact hpos.not_ge (h z hz)

end

end RHTower

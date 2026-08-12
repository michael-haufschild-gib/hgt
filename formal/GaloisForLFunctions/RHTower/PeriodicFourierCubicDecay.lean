import GaloisForLFunctions.RHTower.PeriodicFourierDecay

/-!
# Cubic decay of periodic Fourier coefficients

The Laurent-core proof needs coefficient decay strong enough to absorb the logarithmic norm growth
of zero-extended aperture modes.  Three integrations by parts give the convenient unconditional
majorant `O(|n|⁻³)`.  This is the finite-order instance of the rapid decay used in
Connes--Consani's proof.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory intervalIntegral Set Filter Topology

/-- **Three integrations by parts give `O(|n|⁻³)` decay.** -/
theorem norm_fourierCoeffOn_le_of_periodic_three
    {a b : ℝ} (hab : a < b) {f f' f'' f''' : ℝ → ℂ} {C : ℝ}
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ uIcc a b, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ x ∈ uIcc a b, HasDerivAt f'' (f''' x) x)
    (hf'i : IntervalIntegrable f' volume a b)
    (hf''i : IntervalIntegrable f'' volume a b)
    (hf'''i : IntervalIntegrable f''' volume a b)
    (hf'''b : ∀ x, ‖f''' x‖ ≤ C)
    (hper : f b = f a) (hper' : f' b = f' a) (hper'' : f'' b = f'' a)
    {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeffOn hab f n‖ ≤
      ((b - a) / (2 * Real.pi)) ^ 3 * C * (1 / |(n : ℝ)| ^ 3) := by
  have hba : (0 : ℝ) < b - a := by linarith
  have hnabs : (0 : ℝ) < |(n : ℝ)| := by
    exact abs_pos.mpr (Int.cast_ne_zero.mpr hn)
  have hstep1 := norm_fourierCoeffOn_of_periodic hab hn hf hf'i hper
  have hstep2 := norm_fourierCoeffOn_of_periodic hab hn hf' hf''i hper'
  have hstep3 := norm_fourierCoeffOn_of_periodic hab hn hf'' hf'''i hper''
  have hbnd := norm_fourierCoeffOn_le hab hf'''b n
  have hC : (0 : ℝ) ≤ C :=
    le_trans (norm_nonneg (f''' a)) (hf'''b a)
  have hchain :
      ‖fourierCoeffOn hab f n‖ =
        ((b - a) / (2 * Real.pi * |(n : ℝ)|)) ^ 3 *
          ‖fourierCoeffOn hab f''' n‖ := by
    rw [hstep1, hstep2, hstep3]
    ring
  have hfactor :
      ((b - a) / (2 * Real.pi * |(n : ℝ)|)) ^ 3 =
        ((b - a) / (2 * Real.pi)) ^ 3 * (1 / |(n : ℝ)| ^ 3) := by
    field_simp [Real.pi_ne_zero, ne_of_gt hnabs]
  rw [hchain, hfactor]
  have hnonneg :
      0 ≤ ((b - a) / (2 * Real.pi)) ^ 3 * (1 / |(n : ℝ)| ^ 3) := by
    positivity
  calc
    ((b - a) / (2 * Real.pi)) ^ 3 * (1 / |(n : ℝ)| ^ 3) *
        ‖fourierCoeffOn hab f''' n‖
        ≤ ((b - a) / (2 * Real.pi)) ^ 3 * (1 / |(n : ℝ)| ^ 3) * C :=
      mul_le_mul_of_nonneg_left hbnd hnonneg
    _ = ((b - a) / (2 * Real.pi)) ^ 3 * C * (1 / |(n : ℝ)| ^ 3) := by
      ring

end GaloisForLFunctions.RHTower

end

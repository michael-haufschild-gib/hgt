import GaloisForLFunctions.HTGeometry.SegmentPolarForm
import GaloisForLFunctions.HTGeometry.ArgumentVariationSignChanges

/-!
# Backlund's bound for the argument variation along a segment

Combining the continuous logarithm along a segment with Backlund's sign-change step: the argument
variation of a differentiable nowhere-zero complex function of a real variable, written as the
integral of the imaginary part of its logarithmic derivative, is at most `π` times one more than
the number of zeros of its real part.
-/

open Set MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- **Backlund's bound in integral form.** -/
theorem abs_integral_im_logDeriv_le_of_finite_re_zeros {a b : ℝ} (hab : a ≤ b)
    {f f' : ℝ → ℂ} (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hcont : ContinuousOn (fun t => f' t / f t) (Icc a b))
    (hne : ∀ t ∈ Icc a b, f t ≠ 0)
    (Z : Finset ℝ) (hZ : ∀ t ∈ Ioo a b, (f t).re = 0 → t ∈ Z) :
    |∫ t in a..b, (f' t / f t).im|
      ≤ (((Z.filter (fun z => z ∈ Ioo a b)).card : ℝ) + 1) * Real.pi := by
  obtain ⟨L, hLcont, hLderiv, hLeq⟩ := exists_continuousOn_log_of_hasDerivAt hab hf hcont hne
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hint : IntervalIntegrable (fun t => (f' t / f t).im) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]
    exact Complex.continuous_im.comp_continuousOn hcont
  have hd : ∀ t ∈ uIcc a b, HasDerivAt (fun u => (L u).im) ((f' t / f t).im) t := by
    rw [huIcc]
    intro t ht
    exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hLderiv t ht)
  have hftc : (∫ t in a..b, (f' t / f t).im) = (L b).im - (L a).im :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [hftc]
  exact abs_im_sub_le_of_finite_re_zeros hab hLcont
    (fun t ht => (hLeq t ht).symm) Z hZ

end RHTower

end

import GaloisForLFunctions.HilbertMetric.Spectral.ClippedRankOne
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Recovering first moments from three referenced clipped energies

For a positive cutoff the scalar clipped quadratic is invertible on nonnegative
mass. Apply its inverse to the covariances of `u`, `u+1`, and `u+i`.
Polarization then recovers the complete complex first moment of `u`.
-/

open scoped NNReal
namespace GaloisForLFunctions.HilbertMetric.Clipped
noncomputable section

/-- Inverse of the clipped quadratic on nonnegative masses at positive cutoff. -/
def recoverMass (c y : ℝ) : ℝ :=
  if y ≤ c ^ 2 then Real.sqrt y else (y + c ^ 2) / (2 * c)

theorem recoverMass_quadratic {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    recoverMass c (quadratic c x) = x := by
  by_cases hxc : x ≤ c
  · rw [quadratic_of_le hxc, recoverMass, if_pos (by nlinarith only [hx, hc, hxc])]
    exact Real.sqrt_sq hx
  · have hcx : c < x := lt_of_not_ge hxc
    rw [quadratic_of_ge hcx.le, recoverMass,
      if_neg (by nlinarith only [mul_pos hc (sub_pos.mpr hcx)])]
    field_simp [ne_of_gt hc]
    ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The mass recovered after adding a known constant phase reference. -/
def referenceMass (c : ℝ≥0) (u : ι → ℂ) (z : ℂ) : ℝ :=
  recoverMass c (energy c (columnCovariance (fun i => u i + z)))

theorem referenceMass_eq (c : ℝ≥0) (hc : 0 < c) (u : ι → ℂ) (z : ℂ) :
    referenceMass c u z = ∑ i, Complex.normSq (u i + z) := by
  rw [referenceMass, energy_columnCovariance]
  exact recoverMass_quadratic hc (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

omit [DecidableEq ι] in
private theorem mass_add_one (u : ι → ℂ) :
    (∑ i, Complex.normSq (u i + 1)) =
      (∑ i, Complex.normSq (u i)) + Fintype.card ι + 2 * (∑ i, u i).re := by
  have he (i : ι) : Complex.normSq (u i + 1) = Complex.normSq (u i) + 1 + 2 * (u i).re := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re,
      Complex.one_im]
    ring
  simp only [he, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, Finset.mul_sum, Complex.re_sum]

omit [DecidableEq ι] in
private theorem mass_add_I (u : ι → ℂ) :
    (∑ i, Complex.normSq (u i + Complex.I)) =
      (∑ i, Complex.normSq (u i)) + Fintype.card ι + 2 * (∑ i, u i).im := by
  have he (i : ι) : Complex.normSq (u i + Complex.I) =
      Complex.normSq (u i) + 1 + 2 * (u i).im := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
    ring
  simp only [he, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, Finset.mul_sum, Complex.im_sum]

/-- Three fixed references recover both real and imaginary parts, not just the modulus. -/
theorem firstMoment_from_referenceMass (c : ℝ≥0) (hc : 0 < c) (u : ι → ℂ) :
    (∑ i, u i) =
      (((referenceMass c u 1 - referenceMass c u 0 - Fintype.card ι) / 2 : ℝ) : ℂ) +
      Complex.I * (((referenceMass c u Complex.I - referenceMass c u 0 -
        Fintype.card ι) / 2 : ℝ) : ℂ) := by
  rw [referenceMass_eq c hc u 1, referenceMass_eq c hc u 0,
    referenceMass_eq c hc u Complex.I, mass_add_one, mass_add_I]
  simp only [add_zero]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]
    ring
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]
    ring

/-- Equality of the three referenced energies forces equality of the complex first moments. -/
theorem firstMoment_eq_of_reference_energies (c : ℝ≥0) (hc : 0 < c) (u v : ι → ℂ)
    (h : ∀ z ∈ ({0, 1, Complex.I} : Finset ℂ),
      energy c (columnCovariance (fun i => u i + z)) =
        energy c (columnCovariance (fun i => v i + z))) :
    (∑ i, u i) = ∑ i, v i := by
  have hm (z : ℂ) (hz : z ∈ ({0, 1, Complex.I} : Finset ℂ)) :
      referenceMass c u z = referenceMass c v z := congrArg (recoverMass c) (h z hz)
  rw [firstMoment_from_referenceMass c hc u, firstMoment_from_referenceMass c hc v,
    hm 0 (by simp), hm 1 (by simp), hm Complex.I (by simp)]

#print axioms recoverMass_quadratic
#print axioms firstMoment_from_referenceMass
#print axioms firstMoment_eq_of_reference_energies

end
end GaloisForLFunctions.HilbertMetric.Clipped

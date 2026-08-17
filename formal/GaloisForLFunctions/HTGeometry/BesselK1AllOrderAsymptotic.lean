import GaloisForLFunctions.HTGeometry.HalfShiftedBinomialRemainder

/-!
# The all-orders Schläfli asymptotic of the modified Bessel function of order one

The order-one Schläfli integral is an exact Gaussian integral against the profile `(1+v²)/√(2+v²)`.
That profile has a Taylor expansion in `v²` valid on the whole half line with a uniform remainder, so
Watson's lemma turns it into a Poincaré expansion of `K_1` to every order, with an explicit
fixed-order remainder.

The remainder depends on the argument only through its real part, so it is uniform along every ray
in the open right half plane.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section AllOrders

variable {w : ℂ}

theorem besselK1C_eq_gauss (hw : 0 < w.re) :
    _root_.HTGeometry.besselK1C w
      = 2 * Complex.exp (-w) * ∫ v in Ioi (0 : ℝ),
          ((_root_.HTGeometry.besselLaplaceProfile v : ℝ) : ℂ)
            * Complex.exp (-w * (v : ℂ) ^ 2) := by
  rw [_root_.HTGeometry.besselK1C_eq_integral_laplaceKernel hw]
  have hpt : ∀ v : ℝ, _root_.HTGeometry.besselLaplaceKernel w v
      = (2 * Complex.exp (-w))
        * (((_root_.HTGeometry.besselLaplaceProfile v : ℝ) : ℂ)
          * Complex.exp (-w * (v : ℂ) ^ 2)) := by
    intro v
    rw [_root_.HTGeometry.besselLaplaceKernel]
    have hexp : Complex.exp (-w * (1 + (v : ℂ) ^ 2))
        = Complex.exp (-w) * Complex.exp (-w * (v : ℂ) ^ 2) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [hexp]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun v _ => hpt v),
    MeasureTheory.integral_const_mul]

/-- **The all-orders Schläfli asymptotic.**  Subtracting the first `m+1` Poincaré terms of `K_1`
leaves an error controlled by the `(m+1)`-st real Gaussian moment, uniformly along every ray. -/
theorem norm_besselK1C_sub_watson_le (hw : 0 < w.re) (m : ℕ) :
    ‖_root_.HTGeometry.besselK1C w - 2 * Complex.exp (-w)
        * ∑ k ∈ Finset.range (m + 1), ((schlafliCoeff k : ℝ) : ℂ) * gaussianHalfMoment w k‖
      ≤ 2 * Real.exp (-w.re) * ((3 * (Real.sqrt 2)⁻¹ / 2 ^ (m + 1))
        * realGaussianHalfMoment w.re (m + 1)) := by
  have hsplit : _root_.HTGeometry.besselK1C w - 2 * Complex.exp (-w)
      * ∑ k ∈ Finset.range (m + 1), ((schlafliCoeff k : ℝ) : ℂ) * gaussianHalfMoment w k
      = (2 * Complex.exp (-w))
        * ((∫ v in Ioi (0 : ℝ), ((_root_.HTGeometry.besselLaplaceProfile v : ℝ) : ℂ)
              * Complex.exp (-w * (v : ℂ) ^ 2))
          - ∑ k ∈ Finset.range (m + 1), ((schlafliCoeff k : ℝ) : ℂ) * gaussianHalfMoment w k) := by
    rw [besselK1C_eq_gauss hw]
    ring
  have hwatson := norm_integral_sub_watson_le hw
    (f := _root_.HTGeometry.besselLaplaceProfile)
    (_root_.HTGeometry.continuous_besselLaplaceProfile).aestronglyMeasurable
    schlafliCoeff (m + 1)
    (fun v _ => abs_besselLaplaceProfile_sub_watsonPoly_le m v)
  have hfac : ‖(2 : ℂ) * Complex.exp (-w)‖ = 2 * Real.exp (-w.re) := by
    rw [norm_mul, Complex.norm_exp]
    simp
  rw [hsplit, norm_mul, hfac]
  refine mul_le_mul_of_nonneg_left hwatson (by positivity)

end AllOrders

end

end GaloisForLFunctions.HTGeometry

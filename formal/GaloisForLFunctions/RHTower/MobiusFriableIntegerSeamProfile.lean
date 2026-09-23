import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The Möbius friable profile at the first integer seam

Elementary differential and normalization identities for the `z = -1` profile in
de la Bretèche--Tenenbaum's friable-sum theorem.  Their analytic theorem is not asserted here.
-/

noncomputable section

namespace RHTower

/-- On `1 < u < 2`, the delay solution for the Möbius parameter is `1 + log u`. -/
def mobiusFriableDelayBelowTwo (u : ℝ) : ℝ :=
  1 + Real.log u

/-- The actual leading profile is the second derivative of the delay solution. -/
def mobiusFriableLeadingProfileBelowTwo (u : ℝ) : ℝ :=
  -(u ^ (2 : ℕ))⁻¹

/-- On `2 < u < 3`, the first derivative of the delay solution has this formula. -/
def mobiusFriableDelayDerivativeAboveTwo (u : ℝ) : ℝ :=
  (1 + Real.log (u - 1)) / u

/-- Differential identity for the explicit delay branch below the first integer seam. -/
theorem mobiusFriableDelayBelowTwo_formula_hasDerivAt
    (u : ℝ) (hu : u ≠ 0) :
    HasDerivAt (fun v : ℝ => (1 : ℝ) + Real.log v) u⁻¹ u :=
  (Real.hasDerivAt_log hu).const_add (1 : ℝ)

/-- Differentiating once more gives the negative Möbius friable profile below `u = 2`. -/
theorem mobiusFriableDelayFirstDerivative_hasDerivAt
    (u : ℝ) (hu : u ≠ 0) :
    HasDerivAt (fun v : ℝ => v⁻¹)
      (mobiusFriableLeadingProfileBelowTwo u) u := by
  simpa only [mobiusFriableLeadingProfileBelowTwo] using hasDerivAt_inv hu

/-- After conversion from `log Y = log X / u`, the below-seam profile loses all
dependence on the aperture parameter `u`. -/
theorem mobiusFriableLeadingProfile_apertureIndependent
    (X L u : ℝ) (hL : L ≠ 0) (hu : u ≠ 0) :
    X / (L / u) ^ (2 : ℕ) * mobiusFriableLeadingProfileBelowTwo u =
      -(X / L ^ (2 : ℕ)) := by
  rw [mobiusFriableLeadingProfileBelowTwo]
  field_simp [hL, hu]

/-- The normalized left-seam charge is exactly `-1` at every nonzero aperture below `2`. -/
theorem mobiusFriableLeadingProfile_scaled
    (u : ℝ) (hu : u ≠ 0) :
    u ^ (2 : ℕ) * mobiusFriableLeadingProfileBelowTwo u = -1 := by
  rw [mobiusFriableLeadingProfileBelowTwo]
  field_simp [hu]

/-- Right-hand derivative of the delay solution's first derivative at the seam. -/
theorem mobiusFriableDelayDerivativeAboveTwo_hasDerivAt_two :
    HasDerivAt
      (fun u : ℝ => (1 + Real.log (u - 1)) / u)
      (1 / 4) 2 := by
  have hinner :
      HasDerivAt (fun u : ℝ => u - 1) 1 2 :=
    (hasDerivAt_id (2 : ℝ)).sub_const 1
  have hlog :
      HasDerivAt (fun u : ℝ => Real.log (u - 1)) 1 2 := by
    have hcomp :=
      (Real.hasDerivAt_log (by norm_num : (2 : ℝ) - 1 ≠ 0)).comp
        (2 : ℝ) hinner
    have hcomp' :
        HasDerivAt (fun u : ℝ => Real.log (u - 1))
          (((2 : ℝ) - 1)⁻¹ * 1) 2 :=
      hcomp.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun _ => rfl))
    norm_num at hcomp'
    exact hcomp'
  have hdiv :=
    (hlog.const_add (1 : ℝ)).div
      (hasDerivAt_id (2 : ℝ)) (by norm_num : (2 : ℝ) ≠ 0)
  have hdiv' :
      HasDerivAt (fun u : ℝ => (1 + Real.log (u - 1)) / u)
        ((1 * 2 - (1 + Real.log (2 - 1)) * 1) / (2 : ℝ) ^ (2 : ℕ)) 2 :=
    hdiv.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun _ => rfl))
  norm_num [Real.log_one] at hdiv'
  exact hdiv'

/-- The leading profile has left limit `-1/4` and right limit `1/4`; its jump is `1/2`. -/
theorem mobiusFriableLeadingProfile_jumpAtTwo :
    (1 / 4 : ℝ) - mobiusFriableLeadingProfileBelowTwo 2 = 1 / 2 := by
  norm_num [mobiusFriableLeadingProfileBelowTwo]

/-- Multiplying by `u²`, as forced by `log Y = log X / u`, quantizes the jump to `2`. -/
theorem mobiusFriableScaledProfile_jumpAtTwo :
    (2 : ℝ) ^ (2 : ℕ) * (1 / 4) -
        (2 : ℝ) ^ (2 : ℕ) * mobiusFriableLeadingProfileBelowTwo 2 = 2 := by
  norm_num [mobiusFriableLeadingProfileBelowTwo]

end RHTower

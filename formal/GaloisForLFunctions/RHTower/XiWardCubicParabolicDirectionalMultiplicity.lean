import GaloisForLFunctions.RHTower.XiWardCubicParabolicSourceLanding
import GaloisForLFunctions.RHTower.XiWardCubicPositiveShiftDampedDiagonalSeparator

/-!
# Directional multiplicity from the actual cubic source

The damped cubic radial mask is homogenized before averaging the continued source. Its
critical-line cancellation holds at every positive shift. At a fixed strictly rightward
point its homogenization extends continuously to shift zero with value one. Parabolic
source landing therefore extracts exactly the strict-right multiplicity at every point.

This is a real source operation: no entire scalar mask, chosen zero, or post-divisor
residue weight enters the definition. The arithmetic identity on the Euler chamber is
inherited from the actual continued covariance average.
-/

open Complex Filter Topology MeasureTheory Set

namespace RHTower
noncomputable section

/-- Homogeneous form of the damped cubic radial mask, regular at zero shift for `a > 0`. -/
def xiWardCubicHomogeneousDiagonalMask (a eps : ℝ) : ℝ :=
  1 - (108 / 115) * eps ^ 3 *
    (2 / (2 * a + 2 * eps) ^ 3 - 4 / (3 * a + 3 * eps / 2) ^ 3 +
      2 / (4 * a + eps) ^ 3)

/-- The source weight uses only real position and shift, before any divisor is extracted. -/
def xiWardCubicDirectionalSourceWeight (p : ℂ × ℝ) : ℂ :=
  (xiWardCubicHomogeneousDiagonalMask (max 0 (p.1.re - 1 / 2)) p.2 : ℂ)

/-- The literal continued source average with the damped cubic radial mask inserted. -/
def xiWardCubicParabolicDirectionalSource (z : ℂ) (h : ℝ) : ℂ :=
  xiWardParabolicSourceAverage xiWardCubicDirectionalSourceWeight z h

/-- The homogenized mask is exactly the radial cubic complement at every positive shift. -/
theorem xiWardCubicHomogeneousDiagonalMask_eq_radial
    {a eps : ℝ} (ha : 0 ≤ a) (heps : 0 < eps) :
    xiWardCubicHomogeneousDiagonalMask a eps =
      1 - (108 / 115) * eps ^ 3 *
        (∫ r : ℝ in Ioi 0, xiWardCubicPositiveShiftDampedRadialDensity a eps r) := by
  rw [integral_xiWardCubicPositiveShiftDampedRadialDensity ha heps]
  rfl

/-- Away from zero shift this is the existing cubic diagonal mask, with its natural scale. -/
theorem xiWardCubicHomogeneousDiagonalMask_eq_diagonalMask
    {a eps : ℝ} (ha : 0 ≤ a) (heps : 0 < eps) :
    xiWardCubicHomogeneousDiagonalMask a eps =
      xiWardCubicPositiveShiftDiagonalMask (a / eps) := by
  rw [xiWardCubicHomogeneousDiagonalMask_eq_radial ha heps]
  rw [mul_assoc, eps_cube_mul_integral_xiWardCubicPositiveShiftDampedRadialDensity ha heps]
  unfold xiWardCubicPositiveShiftDiagonalMask xiWardCubicPositiveShiftDiagonalSeparatorProfile
  ring

theorem xiWardCubicHomogeneousDiagonalMask_zero_left {eps : ℝ} (heps : 0 < eps) :
    xiWardCubicHomogeneousDiagonalMask 0 eps = 0 := by
  rw [xiWardCubicHomogeneousDiagonalMask_eq_diagonalMask (le_refl 0) heps, zero_div,
    xiWardCubicPositiveShiftDiagonalMask_zero]

theorem xiWardCubicHomogeneousDiagonalMask_zero_shift (a : ℝ) :
    xiWardCubicHomogeneousDiagonalMask a 0 = 1 := by
  simp [xiWardCubicHomogeneousDiagonalMask]

theorem measurable_xiWardCubicDirectionalSourceWeight :
    Measurable xiWardCubicDirectionalSourceWeight := by
  unfold xiWardCubicDirectionalSourceWeight xiWardCubicHomogeneousDiagonalMask
  fun_prop

theorem continuousAt_xiWardCubicDirectionalSourceWeight
    {z : ℂ} (hz : 1 / 2 < z.re) :
    ContinuousAt xiWardCubicDirectionalSourceWeight (z, 0) := by
  have ha : 0 < max 0 (z.re - 1 / 2) := lt_of_lt_of_le (sub_pos.mpr hz) (le_max_right _ _)
  unfold xiWardCubicDirectionalSourceWeight xiWardCubicHomogeneousDiagonalMask
  fun_prop (disch := simp only [mul_zero, add_zero]; positivity)

/-- Left and critical-line points cancel at the level of the actual averaged source. -/
theorem xiWardCubicParabolicDirectionalSource_eq_zero
    {z : ℂ} (hz : z.re ≤ 1 / 2) {h : ℝ} (hh : 0 < h) :
    xiWardCubicParabolicDirectionalSource z h = 0 := by
  unfold xiWardCubicParabolicDirectionalSource
  rw [xiWardParabolicSourceAverage_eq_incrementIntegral _ _ hh]
  apply intervalIntegral.integral_zero_ae
  apply Filter.Eventually.of_forall
  intro u hu
  have hu' : u ∈ Ioc (0 : ℝ) 1 := by simpa using hu
  have hre : (xiWardParabolicPoint z h).re = z.re := by
    simp [xiWardParabolicPoint, ← ofReal_pow]
  have ha : max 0 ((xiWardParabolicPoint z h).re - 1 / 2) = 0 := by
    rw [hre, max_eq_left (sub_nonpos.mpr hz)]
  simp only [xiWardCubicDirectionalSourceWeight, ha,
    xiWardCubicHomogeneousDiagonalMask_zero_left (mul_pos hh hu'.1), ofReal_zero, mul_zero]

/-- Unconditional directional unit-multiplicity landing of the actual source. -/
theorem tendsto_xiWardCubicParabolicDirectionalSource (z : ℂ) :
    Tendsto (xiWardCubicParabolicDirectionalSource z) (𝓝[>] 0)
      (𝓝 (if 1 / 2 < z.re then (((analyticOrderAt xi z).toNat : ℕ) : ℂ) else 0)) := by
  change Tendsto (xiWardParabolicSourceAverage xiWardCubicDirectionalSourceWeight z) _ _
  by_cases hz : 1 / 2 < z.re
  · simpa only [xiWardCubicDirectionalSourceWeight,
      xiWardCubicHomogeneousDiagonalMask_zero_shift, ofReal_one, mul_one, if_pos hz]
      using tendsto_xiWardParabolicSourceAverage_of_continuousAt
        xiWardCubicDirectionalSourceWeight measurable_xiWardCubicDirectionalSourceWeight z
        (continuousAt_xiWardCubicDirectionalSourceWeight hz)
  · rw [if_neg hz]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (xiWardCubicParabolicDirectionalSource_eq_zero (le_of_not_gt hz) hh).symm

/-- A single source scale works for every point of an arbitrary finite packet, including
collisions and critical-line points. No divisor-dependent shift is selected. -/
theorem tendsto_finset_xiWardCubicParabolicDirectionalSource (S : Finset ℂ) :
    Tendsto (fun h : ℝ => ∑ z ∈ S, xiWardCubicParabolicDirectionalSource z h) (𝓝[>] 0)
      (𝓝 (∑ z ∈ S,
        if 1 / 2 < z.re then (((analyticOrderAt xi z).toNat : ℕ) : ℂ) else 0)) :=
  tendsto_finsetSum S fun z _ => tendsto_xiWardCubicParabolicDirectionalSource z

/-- The directional current is the same pre-divisor pole--Gamma--prime source on its
absolute-Euler chamber; its definition does not depend on a divisor expansion. -/
theorem xiWardCubicParabolicDirectionalSource_eq_arithmetic
    {z : ℂ} {h : ℝ} (hh : 0 < h) (hz : 1 + h < z.re) :
    xiWardCubicParabolicDirectionalSource z h =
      I * (h : ℂ) ^ 2 *
        xiWardCubicShiftEndpointWeightedArithmeticAverage (xiWardParabolicPoint z h) 0 h
          (fun eps => xiWardCubicDirectionalSourceWeight (xiWardParabolicPoint z h, eps)) :=
  xiWardParabolicSourceAverage_eq_arithmetic _ hh hz

end
end RHTower

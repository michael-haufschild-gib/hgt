import GaloisForLFunctions.RHTower.SelbergMaassPairPhaseEnergy
import GaloisForLFunctions.RHTower.SelbergMaassWeakCurvature

/-!
# Exact source-current and regulator decomposition of Maass curvature

The original regularized curvature splits into two nonnegative terms: actual pair
and phase current squares, and the regulator times the actual gradient energy,
both divided by the cubed radius. At every original common zero the current-square
numerator is zero but curvature is gradient energy divided by the regulator.
These are exact original-source identities. No regulator-limit interchange,
vanishing of the nodal contribution, or spectral quarter comparison is asserted.
-/


open Complex Set Filter Topology UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassCurrentCurvature
open SelbergMaassCongruenceTrace SelbergMaassTraceEnergy SelbergMaassTraceRadial
  SelbergMaassPairPhaseEnergy SelbergMaassTraceRegularized SelbergMaassWeakCurvature
noncomputable section

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- The full two-direction sum of actual pair-current and total phase-current squares. -/
def currentEnergy (z : ℂ) : ℝ :=
  pairEnergy N f 1 z + pairEnergy N f Complex.I z +
    phaseCurrent N f 1 z ^ (2 : ℕ) + phaseCurrent N f Complex.I z ^ (2 : ℕ)

/-- The current-square numerator is nonnegative at every actual chart point. -/
theorem currentEnergy_nonneg (z : ℂ) : 0 ≤ currentEnergy N f z :=
  add_nonneg (add_nonneg (add_nonneg (pairEnergy_nonneg N f 1 z)
    (pairEnergy_nonneg N f Complex.I z)) (sq_nonneg _)) (sq_nonneg _)

/-- The current-square numerator is exactly the density-weighted actual angular energy, including nodes. -/
theorem currentEnergy_eq (z : ℍ) :
    currentEnergy N f (z : ℂ) = density N f z * angularEnergy N f z :=
  (density_mul_angularEnergy N f z).symm

/-- The full regulated remainder contains both the conserved-current numerator and the regulator gradient term. -/
theorem radius_sq_mul_remainder (e : Ioi (0 : ℝ)) (z : ℍ) :
    radius N f e (z : ℂ) ^ (2 : ℕ) * remainder N f e z =
      currentEnergy N f (z : ℂ) + (e : ℝ) ^ (2 : ℕ) * gradientDensity N f (z : ℂ) := by
  have hg : gradientDensity N f (z : ℂ) =
      directionalEnergy N f 1 z + directionalEnergy N f Complex.I z := Finset.sum_add_distrib
  rw [radius_sq, ofComplex_apply, remainder, mul_add, regularized_pair_phase_identity,
    regularized_pair_phase_identity, hg, currentEnergy]
  ring

/-- The original regularized curvature has the exact cubic-denominator current and regulator decomposition. -/
theorem radius_cube_mul_curvatureWeight (e : Ioi (0 : ℝ)) (z : ℍ) :
    radius N f e (z : ℂ) ^ (3 : ℕ) * curvatureWeight N f e (z : ℂ) =
      currentEnergy N f (z : ℂ) + (e : ℝ) ^ (2 : ℕ) * gradientDensity N f (z : ℂ) := by
  have hr := (radius_pos N f e (z : ℂ)).ne'
  calc
    _ = radius N f e (z : ℂ) ^ (2 : ℕ) * remainder N f e z := by
      rw [curvatureWeight, ofComplex_apply]
      field_simp
    _ = _ := radius_sq_mul_remainder N f e z

/-- The actual current-square contribution at a positive regulator. -/
def currentWeight (e : Ioi (0 : ℝ)) (z : ℂ) : ℝ :=
  currentEnergy N f z / radius N f e z ^ (3 : ℕ)

/-- The actual regulator-gradient contribution, retained before any nodal limit. -/
def regulatorGradientWeight (e : Ioi (0 : ℝ)) (z : ℂ) : ℝ :=
  (e : ℝ) ^ (2 : ℕ) * gradientDensity N f z / radius N f e z ^ (3 : ℕ)

/-- Exact positive splitting of the original curvature; no limit interchange is used. -/
theorem curvatureWeight_split (e : Ioi (0 : ℝ)) (z : ℍ) :
    curvatureWeight N f e (z : ℂ) =
      currentWeight N f e (z : ℂ) + regulatorGradientWeight N f e (z : ℂ) := by
  have hr := pow_ne_zero 3 (radius_pos N f e (z : ℂ)).ne'
  apply (mul_left_cancel₀ hr)
  rw [radius_cube_mul_curvatureWeight, currentWeight, regulatorGradientWeight]
  field_simp [(radius_pos N f e (z : ℂ)).ne']

/-- The actual current contribution is nonnegative. -/
theorem currentWeight_nonneg (e : Ioi (0 : ℝ)) (z : ℂ) : 0 ≤ currentWeight N f e z :=
  div_nonneg (currentEnergy_nonneg N f z) (pow_nonneg (radius_pos N f e z).le 3)

/-- The retained regulator-gradient contribution is nonnegative. -/
theorem regulatorGradientWeight_nonneg (e : Ioi (0 : ℝ)) (z : ℂ) :
    0 ≤ regulatorGradientWeight N f e z :=
  div_nonneg (mul_nonneg (sq_nonneg _) (gradientDensity_nonneg N f z))
    (pow_nonneg (radius_pos N f e z).le 3)

/-- At an original common zero the current-square numerator vanishes without controlling the source gradients. -/
theorem currentEnergy_zero_at_node (z : ℍ) (hz : density N f z = 0) :
    currentEnergy N f (z : ℂ) = 0 := by rw [currentEnergy_eq, hz, zero_mul]

/-- At an original common zero the full actual curvature is gradient energy divided by the regulator. -/
theorem curvatureWeight_at_node (e : Ioi (0 : ℝ)) (z : ℍ) (hz : density N f z = 0) :
    curvatureWeight N f e (z : ℂ) = gradientDensity N f (z : ℂ) / (e : ℝ) := by
  have hs := radius_sq N f e (z : ℂ)
  simp only [ofComplex_apply, hz, zero_add] at hs
  have hr : radius N f e (z : ℂ) = (e : ℝ) := by
    have hp : radius N f e (z : ℂ) + (e : ℝ) ≠ 0 :=
      (add_pos (radius_pos N f e (z : ℂ)) e.property).ne'
    have hm : (radius N f e (z : ℂ) - (e : ℝ)) *
        (radius N f e (z : ℂ) + (e : ℝ)) = 0 := by nlinarith only [hs]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hp)
  have h := radius_cube_mul_curvatureWeight N f e z
  rw [hr, currentEnergy_zero_at_node N f z hz, zero_add] at h
  have he : (e : ℝ) ≠ 0 := e.property.ne'
  apply (mul_left_cancel₀ (pow_ne_zero 3 he))
  rw [h]
  field_simp

end
end GaloisForLFunctions.RHTower.SelbergMaassCurrentCurvature

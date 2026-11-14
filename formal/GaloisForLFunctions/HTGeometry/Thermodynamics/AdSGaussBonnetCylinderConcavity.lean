import GaloisForLFunctions.HTGeometry.Thermodynamics.AdSGaussBonnetCylinder
import GaloisForLFunctions.HTGeometry.CPVThermalRadiation
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Strict cylinder concavity and endpoint selection

The exact second derivative in arXiv:2611.16364, equation (4.2), is negative
throughout the coupling interval `[0,9/100]`. At every positive radius an
interior coupling has strictly larger potential than at least one endpoint.
Consequently allowing the radius to vary cannot create an interior global
minimizer. Temperature, source and charge remain arbitrary.
-/

noncomputable section
open Filter Topology Set
namespace GaloisForLFunctions.HTGeometry.AdSGaussBonnet

/-- The curvature formula refers to the literal iterated derivative. -/
theorem cylinderPotential_second_derivative (t z q x s : ℝ) :
    deriv (deriv (cylinderPotential t z q x)) (subcriticalCoupling s) =
      betaCurvature (subcriticalCoupling s) * energy (subcriticalCoupling s) q x -
        3 / (16 * eta (subcriticalCoupling s) * beta (subcriticalCoupling s)) := by
  have heq : deriv (cylinderPotential t z q x) =ᶠ[nhds (subcriticalCoupling s)]
      cylinderPotentialSlope t z q x := by
    filter_upwards [Iio_mem_nhds (subcriticalCoupling_lt s)] with l hl
    change l < 1 / 4 at hl
    have hp : 0 < 1 - 4 * l := by linarith only [hl]
    have hr : subcriticalCoupling (Real.log (1 - 4 * l)) = l := by
      unfold subcriticalCoupling
      rw [Real.exp_log hp]
      ring
    have hd := cylinderPotential_hasDerivAt t z q x (Real.log (1 - 4 * l))
    rw [hr] at hd
    exact hd.deriv
  rw [heq.deriv_eq]
  exact (cylinderPotentialSlope_hasDerivAt t z q x s).deriv

/-- Constant-source comparison is strictly concave across the whole physical coupling window. -/
theorem cylinderPotential_strictConcaveOn (t z q u : ℝ) :
    StrictConcaveOn ℝ (Icc 0 (9 / 100)) (cylinderPotential t z q (Real.exp u)) := by
  have hparam : ∀ l ∈ Icc (0 : ℝ) (9 / 100),
      subcriticalCoupling (Real.log (1 - 4 * l)) = l := by
    intro l hl
    have hp : 0 < 1 - 4 * l := by linarith only [hl.2]
    unfold subcriticalCoupling
    rw [Real.exp_log hp]
    ring
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _)
  · intro l hl
    have hd := cylinderPotential_hasDerivAt t z q (Real.exp u) (Real.log (1 - 4 * l))
    rw [hparam l hl] at hd
    exact hd.continuousAt.continuousWithinAt
  · intro l hl
    have hi : l ∈ Icc (0 : ℝ) (9 / 100) := interior_subset hl
    change deriv (deriv (cylinderPotential t z q (Real.exp u))) l < 0
    have hd := cylinderPotential_second_derivative t z q (Real.exp u) (Real.log (1 - 4 * l))
    rw [hparam l hi] at hd
    rw [hd]
    have hcurv := betaCurvature_neg (Real.log (1 - 4 * l))
    have heta := eta_pos (Real.log (1 - 4 * l))
    have hbeta := beta_pos (Real.log (1 - 4 * l))
    rw [hparam l hi] at hcurv heta hbeta
    have henergy : 0 < energy l q (Real.exp u) := by
      unfold energy
      have hlower := hi.1
      positivity
    have hfirst := mul_neg_of_neg_of_pos hcurv henergy
    have hlast : 0 < 3 / (16 * eta l * beta l) := by positivity
    linarith only [hfirst, hlast]

/-- Every interior coupling lies strictly above an endpoint at the same radius. -/
theorem cylinderPotential_interior_gap (t z q u τ : ℝ) :
    min (cylinderPotential t z q (Real.exp u) 0)
        (cylinderPotential t z q (Real.exp u) (9 / 100)) <
      cylinderPotential t z q (Real.exp u) ((9 / 100) * CPV.thermalRatio τ) := by
  have hα : 0 < 1 - CPV.thermalRatio τ := sub_pos.mpr (CPV.thermalRatio_lt_one τ)
  have hβ := CPV.thermalRatio_pos τ
  have hj := (cylinderPotential_strictConcaveOn t z q u).2
    (show (0 : ℝ) ∈ Icc 0 (9 / 100) by norm_num)
    (show (9 / 100 : ℝ) ∈ Icc 0 (9 / 100) by norm_num)
    (by norm_num : (0 : ℝ) ≠ 9 / 100) hα hβ (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add] at hj
  rw [mul_comm (CPV.thermalRatio τ) (9 / 100)] at hj
  have hm : min (cylinderPotential t z q (Real.exp u) 0)
      (cylinderPotential t z q (Real.exp u) (9 / 100)) ≤
        (1 - CPV.thermalRatio τ) * cylinderPotential t z q (Real.exp u) 0 +
          CPV.thermalRatio τ * cylinderPotential t z q (Real.exp u) (9 / 100) := by
    calc
      _ = (1 - CPV.thermalRatio τ) * min (cylinderPotential t z q (Real.exp u) 0)
            (cylinderPotential t z q (Real.exp u) (9 / 100)) +
          CPV.thermalRatio τ * min (cylinderPotential t z q (Real.exp u) 0)
            (cylinderPotential t z q (Real.exp u) (9 / 100)) := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _) hα.le)
        (mul_le_mul_of_nonneg_left (min_le_right _ _) hβ.le)
  exact hm.trans_lt hj

theorem cylinderPotential_interior_has_better_endpoint (t z q u τ : ℝ) :
    cylinderPotential t z q (Real.exp u) 0 <
        cylinderPotential t z q (Real.exp u) ((9 / 100) * CPV.thermalRatio τ) ∨
      cylinderPotential t z q (Real.exp u) (9 / 100) <
        cylinderPotential t z q (Real.exp u) ((9 / 100) * CPV.thermalRatio τ) := by
  have h := cylinderPotential_interior_gap t z q u τ
  by_cases hc : cylinderPotential t z q (Real.exp u) 0 ≤
      cylinderPotential t z q (Real.exp u) (9 / 100)
  · exact Or.inl (by simpa only [min_eq_left hc] using h)
  · exact Or.inr (by simpa only [min_eq_right (le_of_not_ge hc)] using h)

#print axioms cylinderPotential_strictConcaveOn
#print axioms cylinderPotential_interior_has_better_endpoint

end GaloisForLFunctions.HTGeometry.AdSGaussBonnet

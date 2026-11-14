import GaloisForLFunctions.MetaplecticMobiusDescent.EisensteinCoordinates

/-!
# Unit separation in the integral triangular lattice

The squared complex norm is a positive integer away from zero. Hence
distinct embedded Eisenstein integers are at distance at least one.
-/

noncomputable section
namespace GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein

/-- Integrality of the positive norm gives the exact unit lower bound. -/
theorem one_le_norm_ringComplex {a : O} (ha : a ≠ 0) : 1 ≤ ‖ringComplex a‖ := by
  have hp := Coordinates.coordinate_norm_pos (Coordinates.coords a).1
    (Coordinates.coords a).2 (by simpa only [Coordinates.eval_coords] using ha)
  have hi : (1 : ℤ) ≤ (Coordinates.coords a).1 ^ 2 -
      (Coordinates.coords a).1 * (Coordinates.coords a).2 + (Coordinates.coords a).2 ^ 2 := hp
  have hr : (1 : ℝ) ≤ ((Coordinates.coords a).1 : ℝ) ^ 2 -
      ((Coordinates.coords a).1 : ℝ) * (Coordinates.coords a).2 +
      ((Coordinates.coords a).2 : ℝ) ^ 2 := by exact_mod_cast hi
  rw [← Coordinates.complex_norm_eval_sq, Coordinates.eval_coords] at hr
  nlinarith only [hr, norm_nonneg (ringComplex a)]

/-- Distinct lattice points are separated by at least one. -/
theorem one_le_dist_ringComplex {a b : O} (hab : a ≠ b) :
    1 ≤ dist (ringComplex a) (ringComplex b) := by
  rw [dist_eq_norm, ← map_sub]
  exact one_le_norm_ringComplex (sub_ne_zero.mpr hab)

end GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.one_le_dist_ringComplex

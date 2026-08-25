import GaloisForLFunctions.RHTower.BoundaryModulus
import Mathlib.Tactic

/-!
# Purity, normalization, and reciprocal functional-equation symmetry

For a pointwise pure sheaf, the Frobenius weight-circle condition is part of the definition of
purity.  Dividing an eigenvalue by the positive weight radius therefore gives a unit-modulus scalar;
this is the exact normalization theorem already underlying the proposed G5 recovery.

Reciprocal functional-equation symmetry alone is weaker.  At squared weight radius `4`, the pair
`{4, 1}` is exchanged by `alpha ↦ 4 / conj(alpha)` although both members lie off the radius-`2`
circle.  Thus Poincaré-duality symmetry cannot replace the missing purity input.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open GaloisForLFunctions

/-- Reciprocal-conjugate partner for a functional equation whose squared weight radius is `Q`. -/
def weightReciprocalPartner (Q : ℝ) (alpha : ℂ) : ℂ :=
  (Q : ℂ) / star alpha

/-- Closed scalar specialization of the exact weight-normalization equivalence. -/
theorem functionFieldWeightNormalize_four_one_one_iff (alpha : ℂ) :
    ‖functionFieldWeightNormalize 4 1 1 alpha‖ = 1 ↔
      ‖alpha‖ = functionFieldWeightRadius 4 1 1 :=
  functionFieldWeightNormalize_norm_eq_one_iff (by norm_num) 1 1 alpha

/-- Reciprocal FE symmetry can exchange two eigenvalues while both remain off the weight circle. -/
theorem reciprocalFE_pair_four_one_off_radius_two :
    weightReciprocalPartner 4 4 = 1 ∧
      weightReciprocalPartner 4 1 = 4 ∧
      ‖(4 : ℂ)‖ ≠ 2 ∧ ‖(1 : ℂ)‖ ≠ 2 := by
  norm_num [weightReciprocalPartner, Complex.norm_real]

/-- Functional-equation reciprocity does not, by itself, force the Frobenius weight modulus. -/
theorem reciprocalFE_symmetry_does_not_force_weightCircle :
    ¬ ∀ alpha : ℂ,
      weightReciprocalPartner 4 alpha = 1 → ‖alpha‖ = 2 := by
  intro h
  exact reciprocalFE_pair_four_one_off_radius_two.2.2.1
    (h 4 reciprocalFE_pair_four_one_off_radius_two.1)

end

end GaloisForLFunctions.HTGeometry

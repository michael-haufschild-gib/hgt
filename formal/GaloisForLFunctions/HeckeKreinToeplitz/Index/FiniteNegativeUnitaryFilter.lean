import GaloisForLFunctions.HeckeKreinToeplitz.Index.FiniteNegativeCoefficients
import GaloisForLFunctions.HTGeometry.PhaseResonanceProjection

/-!
# Unitary filtering lowers the negative index

The image of `T-a` is orthogonal to an eigenvector of a form-isometry `T`
with unit-modulus eigenvalue `a`. For a commuting group representation,
this orthogonality holds on the entire filtered orbit. A nonpositive
eigenvector therefore removes one possible negative square.
-/

noncomputable section
set_option autoImplicit false
open Complex Module
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative

variable {G H E : Type*} [CommGroup G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem pairing_sub_right (u v w : H × E) : pairing u (v - w) = pairing u v - pairing u w :=
  map_sub (pairingLinear u) v w

theorem pairing_sub_left (u v w : H × E) : pairing (u - v) w = pairing u w - pairing v w := by
  rw [← pairing_conj_symm (u - v) w, pairing_sub_right, map_sub,
    pairing_conj_symm, pairing_conj_symm]

variable (ρ : G →* End ℂ (H × E))
    (hρ : ∀ g v w, pairing (ρ g v) (ρ g w) = pairing v w)

private theorem action_commute (g t : G) (v : H × E) : ρ g (ρ t v) = ρ t (ρ g v) := by
  rw [← Module.End.mul_apply, ← map_mul, mul_comm g t, map_mul, Module.End.mul_apply]

include hρ in
/-- The unitary difference is orthogonal to its corresponding eigenvector. -/
theorem pairing_unitary_difference_eq_zero (t : G) {w : H × E} {a : ℂ}
    (ha : ‖a‖ = 1) (heig : ρ t w = a • w) (v : H × E) :
    pairing w (ρ t v - a • v) = 0 := by
  have h := hρ t w v
  rw [heig, pairing_smul_left] at h
  have ha' : a * conj a = 1 := by rw [mul_comm, conj_mul_self_of_norm_eq_one ha]
  have he := congrArg (fun z : ℂ => a * z) h
  rw [← mul_assoc, ha', one_mul] at he
  rw [pairing_sub_right, pairing_smul_right, he, sub_self]

include hρ in
/-- A nonpositive unitary eigenvector lowers the index of every filtered coefficient. -/
theorem negIndex_unitary_filter_le [FiniteDimensional ℂ E]
    {r : ℕ} (hE : finrank ℂ E ≤ r + 1) (t : G) (v : H × E) {w : H × E} {a : ℂ}
    (hw : w ≠ 0) (hwq : (pairing w w).re ≤ 0) (ha : ‖a‖ = 1)
    (heig : ρ t w = a • w) :
    negIndex (fun g => pairing (ρ t v - a • v) (ρ g (ρ t v - a • v))) ≤ r := by
  apply negIndex_coefficient_le_of_orthogonal_nonpositive ρ hρ hE _ hw hwq
  intro g
  rw [map_sub, map_smul, action_commute]
  exact pairing_unitary_difference_eq_zero ρ hρ t ha heig (ρ g v)

include hρ in
/-- Filtering a coefficient is a unitary twisted second difference of the original kernel. -/
theorem coefficient_unitary_filter (t g : G) (v : H × E) {a : ℂ} (ha : ‖a‖ = 1) :
    pairing (ρ t v - a • v) (ρ g (ρ t v - a • v)) =
      2 * pairing v (ρ g v) - a * pairing v (ρ (t⁻¹ * g) v) -
        conj a * pairing v (ρ (g * t) v) := by
  rw [map_sub, map_smul, pairing_sub_left, pairing_sub_right, pairing_sub_right,
    pairing_smul_left, pairing_smul_left, pairing_smul_right, pairing_smul_right]
  have hfirst : pairing (ρ t v) (ρ g (ρ t v)) = pairing v (ρ g v) := by
    rw [action_commute, hρ]
  have hlast : pairing v (ρ g (ρ t v)) = pairing v (ρ (g * t) v) := by
    rw [map_mul, Module.End.mul_apply]
  rw [hfirst, hlast, coefficient_orbit_pairing ρ hρ]
  have hc := conj_mul_self_of_norm_eq_one ha
  calc
    _ = 2 * pairing v (ρ g v) - a * pairing v (ρ (t⁻¹ * g) v) -
        conj a * pairing v (ρ (g * t) v) +
        (conj a * a - 1) * pairing v (ρ g v) := by ring
    _ = _ := by rw [hc, sub_self, zero_mul, add_zero]

#print axioms negIndex_unitary_filter_le
#print axioms coefficient_unitary_filter

end GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative

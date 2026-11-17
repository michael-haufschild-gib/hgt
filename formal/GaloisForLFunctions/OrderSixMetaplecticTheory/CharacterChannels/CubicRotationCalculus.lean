import GaloisForLFunctions.OrderSixMetaplecticTheory.CharacterChannels.WeilPolynomialFilters

/-!
# The three channels of actual cubic unit rotation

Rotation by the Eisenstein cubic unit has cube equal to the identity on residues modulo four.
Its three character projectors decompose every class function and reduce any
polynomial in rotation to its values at the three cube roots of unity. The
signed Weil pairing selects the inverse eigenvalue to its own phase. This
gives exact filtering identities for finite arithmetic row sums.
-/

noncomputable section
namespace GaloisForLFunctions.OrderSixMetaplecticTheory.RamifiedCharacterChannel
open _root_.Polynomial
open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.CubicJacobi MetaplecticMobiusDescent.CubicEisenstein
open scoped BigOperators

def unitRotation : Module.End ℂ (ResidueFour → ℂ) where
  toFun f c := f (rotate c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem unitRotation_cube : unitRotation ^ 3 = 1 := by
  apply LinearMap.ext
  intro f
  funext c
  change f (rotate (rotate (rotate c))) = f c
  rw [rotate_three]

/-- The character component inverse to a cube root of unity `a`. -/
def rotationChannel (a : ℂ) (f : ResidueFour → ℂ) (c : ResidueFour) : ℂ :=
  (f c + a * f (rotate c) + a ^ 2 * f (rotate (rotate c))) / 3

theorem rotationChannel_cubic (f : ResidueFour → ℂ) :
    rotationChannel (cubicTwoChar omega) f = cubicProjection f := rfl

theorem rotationChannel_eigen (a : ℂ) (ha : a ^ 3 = 1) (f : ResidueFour → ℂ) :
    unitRotation (rotationChannel a f) = a ^ 2 • rotationChannel a f := by
  funext c
  have he : a * rotationChannel a f (rotate c) = rotationChannel a f c := by
    dsimp only [rotationChannel]
    rw [rotate_three]
    linear_combination (f c / 3) * ha
  change rotationChannel a f (rotate c) = a ^ 2 * rotationChannel a f c
  calc
    _ = a ^ 2 * (a * rotationChannel a f (rotate c)) := by
      rw [← mul_assoc, ← pow_succ, ha, one_mul]
    _ = _ := by rw [he]

theorem rotationChannel_idempotent (a : ℂ) (ha : a ^ 3 = 1) (f : ResidueFour → ℂ) :
    rotationChannel a (rotationChannel a f) = rotationChannel a f := by
  have he (c : ResidueFour) : a * rotationChannel a f (rotate c) = rotationChannel a f c := by
    dsimp only [rotationChannel]
    rw [rotate_three]
    linear_combination (f c / 3) * ha
  funext c
  have he₂ : a ^ 2 * rotationChannel a f (rotate (rotate c)) = rotationChannel a f c := by
    calc
      _ = a * (a * rotationChannel a f (rotate (rotate c))) := by ring
      _ = a * rotationChannel a f (rotate c) := by rw [he]
      _ = _ := he c
  rw [rotationChannel, he, he₂]
  ring

theorem cubic_phase_cube : cubicTwoChar omega ^ 3 = 1 := by
  rw [cubicTwoChar_omega, ← pow_mul, Nat.mul_comm 2 3, pow_mul,
    ← map_pow, omega_primitive.pow_eq_one, map_one, one_pow]

theorem cubic_phase_sum : 1 + cubicTwoChar omega + cubicTwoChar omega ^ 2 = 0 := by
  have h : (cubicTwoChar omega - 1) * (1 + cubicTwoChar omega + cubicTwoChar omega ^ 2) = 0 := by
    linear_combination cubic_phase_cube
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr cubicTwoChar_omega_ne_one)

private theorem cubic_phase_four : (cubicTwoChar omega ^ 2) ^ 2 = cubicTwoChar omega := by
  calc
    _ = cubicTwoChar omega ^ 3 * cubicTwoChar omega := by ring
    _ = _ := by rw [cubic_phase_cube, one_mul]

/-- Every residue-class function splits into all three character components. -/
theorem rotationChannel_sum (f : ResidueFour → ℂ) :
    rotationChannel 1 f + rotationChannel (cubicTwoChar omega) f +
      rotationChannel (cubicTwoChar omega ^ 2) f = f := by
  funext c
  simp only [Pi.add_apply, rotationChannel, one_pow, one_mul, cubic_phase_four]
  linear_combination ((f (rotate c) + f (rotate (rotate c))) / 3) * cubic_phase_sum

private theorem rotation_pow_channel (a : ℂ) (ha : a ^ 3 = 1) (f : ResidueFour → ℂ) (n : ℕ) :
    (unitRotation ^ n) (rotationChannel a f) = (a ^ 2) ^ n • rotationChannel a f := by
  induction n with
  | zero => simp only [pow_zero, Module.End.one_apply, one_smul]
  | succ n ih =>
    rw [pow_succ']
    change unitRotation ((unitRotation ^ n) (rotationChannel a f)) = _
    rw [ih, map_smul, rotationChannel_eigen a ha,
      smul_smul, ← pow_succ]

/-- Polynomial rotation acts diagonally on each character channel. -/
theorem rotation_polynomial_channel (a : ℂ) (ha : a ^ 3 = 1) (p : ℂ[X])
    (f : ResidueFour → ℂ) :
    aeval unitRotation p (rotationChannel a f) = p.eval (a ^ 2) • rotationChannel a f := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, hp, hq, Polynomial.eval_add, add_smul]
  | monomial n r =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial]
    change r • ((unitRotation ^ n) (rotationChannel a f)) =
      (r * (a ^ 2) ^ n) • rotationChannel a f
    rw [rotation_pow_channel a ha, smul_smul]

/-- Complete polynomial calculus of cubic unit rotation on the actual residue classes. -/
theorem unitRotation_polynomial (p : ℂ[X]) (f : ResidueFour → ℂ) :
    aeval unitRotation p f =
      p.eval 1 • rotationChannel 1 f +
      p.eval (cubicTwoChar omega ^ 2) • cubicProjection f +
      p.eval (cubicTwoChar omega) • rotationChannel (cubicTwoChar omega ^ 2) f := by
  have hz₂ : (cubicTwoChar omega ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, Nat.mul_comm 2 3, pow_mul, cubic_phase_cube, one_pow]
  conv_lhs => rw [← rotationChannel_sum f]
  rw [map_add, map_add, rotation_polynomial_channel 1 (by norm_num),
    rotation_polynomial_channel _ cubic_phase_cube, rotation_polynomial_channel _ hz₂]
  simp only [one_pow, cubic_phase_four, rotationChannel_cubic]

theorem weightedSum_unitRotation (f : ResidueFour → ℂ) :
    weightedSum (unitRotation f) = cubicTwoChar omega ^ 2 * weightedSum f := by
  calc
    _ = cubicTwoChar omega ^ 2 * (cubicTwoChar omega * weightedSum (unitRotation f)) := by
      rw [← mul_assoc, ← pow_succ, cubic_phase_cube, one_mul]
    _ = _ := by
      change cubicTwoChar omega ^ 2 *
        (cubicTwoChar omega * weightedSum (fun c => f (rotate c))) = _
      rw [← weightedSum_rotation f]

private theorem weightedSum_rotation_pow (n : ℕ) (f : ResidueFour → ℂ) :
    weightedSum ((unitRotation ^ n) f) = (cubicTwoChar omega ^ 2) ^ n * weightedSum f := by
  induction n with
  | zero => simp only [pow_zero, Module.End.one_apply, one_mul]
  | succ n ih =>
    rw [pow_succ']
    change weightedSum (unitRotation ((unitRotation ^ n) f)) = _
    rw [weightedSum_unitRotation, ih, pow_succ']
    ring

/-- The Weil pairing sees exactly the value of a rotation filter at the inverse cubic eigenvalue. -/
theorem weightedSum_rotation_polynomial (p : ℂ[X]) (f : ResidueFour → ℂ) :
    weightedSum (aeval unitRotation p f) = p.eval (cubicTwoChar omega ^ 2) * weightedSum f := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, LinearMap.add_apply, weightedSum_add, hp, hq, Polynomial.eval_add, add_mul]
  | monomial n r =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial]
    change weightedSum (r • ((unitRotation ^ n) f)) = _
    rw [weightedSum_smul, weightedSum_rotation_pow]
    ring

/-- The same exact spectral multiplier acts on every finite order-six arithmetic row sum. -/
theorem finite_row_sum_rotation_polynomial (p : ℂ[X]) (S : Finset O) (w : O → ℂ) :
    weightedSum (aeval unitRotation p (gaussSquareClassMass S w)) =
      p.eval (cubicTwoChar omega ^ 2) *
        ∑ c ∈ S, fixedDualAverage c * cubicTwoChar c * normalizedCubicUnitGauss c ^ 2 * w c := by
  rw [weightedSum_rotation_polynomial, finite_row_sum_eq_projected, weightedSum_eq_projected]

/-- A rotation filter cancels a signed pairing exactly at its selected eigenvalue or an existing zero. -/
theorem weightedSum_rotation_polynomial_eq_zero_iff (p : ℂ[X]) (f : ResidueFour → ℂ) :
    weightedSum (aeval unitRotation p f) = 0 ↔
      p.eval (cubicTwoChar omega ^ 2) = 0 ∨ weightedSum f = 0 := by
  rw [weightedSum_rotation_polynomial, mul_eq_zero]

#print axioms rotationChannel_idempotent
#print axioms unitRotation_polynomial
#print axioms finite_row_sum_rotation_polynomial
#print axioms weightedSum_rotation_polynomial_eq_zero_iff

end GaloisForLFunctions.OrderSixMetaplecticTheory.RamifiedCharacterChannel

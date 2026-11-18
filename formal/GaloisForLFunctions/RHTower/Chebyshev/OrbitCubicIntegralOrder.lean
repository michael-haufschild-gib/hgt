import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicTraceGeometry
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Integral units in the Chebyshev orbit cubic

Oller, arXiv:2611.17965, §§3–4, uses small binary values to produce
codifferent elements and adjusts their signs by units. At the integral
parameters of the orbit cubic both the root and its translate by one are
units already in the monogenic order. This also rules out rational roots.
The order-three anharmonic substitution acts integrally on the order.
-/

noncomputable section
open Polynomial
namespace RHTower.OrbitCubic

/-- Integral member having distinguished mean parameter m. -/
def integralModel (m : ℤ) : Cubic ℤ := ⟨1,-(m+1),m-2,1⟩

private def secular {R : Type*} [CommRing R] (m x : R) : R :=
  (x-m)*x*(x-1) - (x-1) - x

private theorem eval_model {R : Type*} [CommRing R] (m : ℤ) (x : R) :
    (integralModel m).toPoly.eval₂ (Int.castRingHom R) x = secular (m : R) x := by
  simp [integralModel,Cubic.toPoly,secular]
  ring

/-- The real orbit parameter is shifted by exactly one half. -/
theorem integral_real_specialization (m : ℤ) (x : ℝ) :
    (integralModel m).toPoly.eval₂ (Int.castRingHom ℝ) x = binary ((m : ℝ)-1/2) x 1 := by
  rw [eval_model,arrowhead_secular]
  unfold secular
  ring

private theorem root_units {R : Type*} [CommRing R] {x m : R} (h : secular m x = 0) :
    x * (2-(x-m)*(x-1)) = 1 ∧ (x-1)*((x-m)*x-2) = 1 := by
  unfold secular at h
  constructor
  · linear_combination -h
  · linear_combination h

private theorem no_integer_root (m x : ℤ) : secular m x ≠ 0 := by
  intro h
  obtain ⟨hx,hy⟩ := root_units h
  have hx' := Int.eq_one_or_neg_one_of_mul_eq_one hx
  have hy' := Int.eq_one_or_neg_one_of_mul_eq_one hy
  omega

/-- Neither consecutive integral units nor rational linear factors can occur
at a rational root of this monic family. -/
theorem integralModel_no_rational_root (m : ℤ) (r : ℚ) :
    (integralModel m).toPoly.eval₂ (Int.castRingHom ℚ) r ≠ 0 := by
  intro h
  have hi : IsIntegral ℤ r :=
    ⟨_, Cubic.monic_of_a_eq_one (P := integralModel m) rfl, h⟩
  obtain ⟨z,hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  have hz' : (z : ℚ) = r := by simpa using hz
  rw [← hz', eval_model] at h
  apply no_integer_root m z
  unfold secular at h ⊢
  exact_mod_cast h

/-- Every integral parameter gives an irreducible rational cubic. -/
theorem integralModel_irreducible (m : ℤ) :
    Irreducible ((integralModel m).toPoly.map (Int.castRingHom ℚ)) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [Polynomial.natDegree_map, Cubic.natDegree_of_a_ne_zero (P := integralModel m) (by
      change (1 : ℤ) ≠ 0
      exact one_ne_zero)]
    simp
  · intro r
    simpa only [Polynomial.IsRoot,Polynomial.eval_map] using integralModel_no_rational_root m r

abbrev Order (m : ℤ) := AdjoinRoot (integralModel m).toPoly
abbrev generator (m : ℤ) : Order m := AdjoinRoot.root _

private theorem root_eqn (m : ℤ) : secular (m : Order m) (generator m) = 0 := by
  rw [← eval_model]
  exact AdjoinRoot.eval₂_root _

/-- The correcting quadratic numerator is a unit of the integral order. -/
theorem integralModel_units (m : ℤ) :
    IsUnit (generator m) ∧ IsUnit (generator m-1) ∧ IsUnit (generator m*(generator m-1)) := by
  obtain ⟨h,k⟩ := root_units (root_eqn m)
  have h₁ := IsUnit.of_mul_eq_one _ h
  have h₂ := IsUnit.of_mul_eq_one _ k
  exact ⟨h₁,h₂,h₁.mul h₂⟩

/-- The anharmonic substitution (x−1)/x written integrally on the cubic. -/
private def nextRoot {R : Type*} [CommRing R] (m x : R) : R :=
  (x-1)*(2-(x-m)*(x-1))

private theorem next_spec {R : Type*} [CommRing R] {m x : R} (hx : secular m x = 0) :
    x * nextRoot m x = x-1 := by
  unfold nextRoot
  rw [mul_left_comm, (root_units hx).1, mul_one]

private theorem next_root {R : Type*} [CommRing R] {m x : R} (hx : secular m x = 0) :
    secular m (nextRoot m x) = 0 := by
  let y := nextRoot m x
  have hxy : x*y = x-1 := next_spec hx
  have hxU := (IsUnit.of_mul_eq_one _ (root_units hx).1).pow 3
  apply hxU.mul_left_cancel
  rw [mul_zero]
  change x^3*secular m y = 0
  calc
    x^3*secular m y = (x*y-m*x)*(x*y)*(x*y-x) - (x*y-x)*x^2 - (x*y)*x^2 := by
      unfold secular
      ring
    _ = 0 := by rw [hxy]; unfold secular at hx; linear_combination -hx

private theorem next_three {R : Type*} [CommRing R] {m x : R} (hx : secular m x = 0) :
    nextRoot m (nextRoot m (nextRoot m x)) = x := by
  let y := nextRoot m x
  let z := nextRoot m y
  have hy : secular m y = 0 := next_root hx
  have hz : secular m z = 0 := next_root hy
  have hxy : x*y = x-1 := next_spec hx
  have hyz : y*z = y-1 := next_spec hy
  have hzw : z*nextRoot m z = z-1 := next_spec hz
  apply (IsUnit.of_mul_eq_one _ (root_units hz).1).mul_left_cancel
  change z*nextRoot m z = z*x
  rw [hzw]
  linear_combination (z-1)*hxy - x*hyz

/-- Cubing the integral polynomial substitution recovers the generator,
without division or localization. -/
theorem integral_generator_cycle (m : ℤ) :
    let f := fun x : Order m => (x-1)*(2-(x-m)*(x-1))
    f (f (f (generator m))) = generator m := next_three (root_eqn m)

#print axioms integral_real_specialization
#print axioms integralModel_no_rational_root
#print axioms integralModel_irreducible
#print axioms integralModel_units
#print axioms integral_generator_cycle
end RHTower.OrbitCubic

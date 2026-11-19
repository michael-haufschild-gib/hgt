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
  have h : eval₂ (Int.castRingHom R) x (m : ℤ[X]) = (m:R) :=
    map_intCast (Polynomial.eval₂RingHom (Int.castRingHom R) x) m
  simp [integralModel,Cubic.toPoly,secular,h]
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

/-- The two integral reciprocal polynomials give a multiplication table
over any coefficient ring. No localization at a root is necessary. -/
theorem reciprocal_polynomial_table {R : Type*} [CommRing R] (m x : R) :
    let U := 2-(x-m)*(x-1)
    let V := (x-m)*x-2
    (x-m)*x*(x-1)-(x-1)-x = 0 →
      x*U = 1 ∧ (x-1)*V = 1 ∧ x = m+U+V ∧ U*V = V-U ∧
      U^2 = 1+(1-m)*U-V ∧ V^2 = 1+U-m*V := by
  intro U V hx
  obtain ⟨hu,hv⟩ := root_units (show secular m x = 0 from hx)
  change x*U = 1 at hu
  change (x-1)*V = 1 at hv
  have he : x = m+U+V := by dsimp only [U,V]; ring
  have huv : U*V = V-U := by linear_combination V*hu - U*hv
  refine ⟨hu,hv,he,huv,?_,?_⟩
  · linear_combination hu - U*he - huv
  · linear_combination hv - V*he - huv

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
  · rw [(Cubic.monic_of_a_eq_one (P := integralModel m) rfl).natDegree_map,
      Cubic.natDegree_of_a_ne_zero (P := integralModel m) (by
      change (1 : ℤ) ≠ 0
      exact one_ne_zero)]
    simp
  · intro r
    simpa only [Polynomial.IsRoot,Polynomial.eval_map] using integralModel_no_rational_root m r

abbrev Order (m : ℤ) := AdjoinRoot (integralModel m).toPoly
abbrev generator (m : ℤ) : Order m := AdjoinRoot.root _

private theorem root_eqn (m : ℤ) : secular (m : Order m) (generator m) = 0 := by
  rw [← eval_model]
  rw [show Int.castRingHom (Order m) = AdjoinRoot.of (integralModel m).toPoly from Subsingleton.elim _ _]
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

private def factorIf {R : Type*} [One R] (b : Bool) (x : R) := if b then 1 else x

private theorem factor_unit {R : Type*} [Monoid R] (b : Bool) {x : R} (hx : IsUnit x) :
    IsUnit (factorIf b x) := by cases b <;> simp [factorIf,hx]

private theorem factor_pos {R : Type*} [Ring R] (f : R →+* ℝ) (b : Bool) {x : R} (hx : 0 < f x) :
    0 < f (factorIf b x) := by cases b <;> simp [factorIf,hx]

private theorem factor_flip {R : Type*} [Ring R] (f : R →+* ℝ) (b : Bool) {x : R} (hx : f x < 0) :
    0 < f (factorIf b x) ↔ b = true := by cases b <;> simp [factorIf,hx.not_gt]

/-- All eight unit signatures already occur in the monogenic integral order.
The three individual sign changes are realized by x, x(x−1), and 1−x. -/
theorem integral_order_unit_signatures (m : ℤ) :
    ∃ A B C : Order m →+* ℝ,
      A (generator m) < 0 ∧ 0 < B (generator m) ∧ B (generator m) < 1 ∧ 1 < C (generator m) ∧
      ∀ l t r : Bool, ∃ u : Order m, IsUnit u ∧
        (0 < A u ↔ l = true) ∧ (0 < B u ↔ t = true) ∧ (0 < C u ↔ r = true) := by
  obtain ⟨a,b,c,ha,hb,hb',hc,ea,eb,ec⟩ := roots_straddle_poles ((m:ℝ)-1/2)
  let hom (x : ℝ) (hx : binary ((m:ℝ)-1/2) x 1 = 0) : Order m →+* ℝ :=
    AdjoinRoot.lift (Int.castRingHom ℝ) x ((integral_real_specialization m x).trans hx)
  have homeval (x : ℝ) (hx : binary ((m:ℝ)-1/2) x 1 = 0) :
      hom x hx (generator m) = x := by simp only [hom,generator,AdjoinRoot.lift_root]
  refine ⟨hom a ea,hom b eb,hom c ec,by simpa only [homeval] using ha,
    by simpa only [homeval] using hb,by simpa only [homeval] using hb',
    by simpa only [homeval] using hc,?_⟩
  intro l t r
  let x := generator m
  let y := x*(x-1)
  let z := -(x-1)
  obtain ⟨hu,hv,hw⟩ := integralModel_units m
  refine ⟨factorIf l x * factorIf t y * factorIf r z,
    ((factor_unit l hu).mul (factor_unit t hw)).mul (factor_unit r hv.neg),?_,?_,?_⟩
  · have hy : 0 < hom a ea y := by
      simp only [y,x,map_mul,map_sub,map_one,homeval]
      exact mul_pos_of_neg_of_neg ha (by linarith)
    have hz : 0 < hom a ea z := by simp only [z,x,map_neg,map_sub,map_one,homeval]; linarith
    rw [map_mul,map_mul,mul_pos_iff_of_pos_right (factor_pos _ r hz),
      mul_pos_iff_of_pos_right (factor_pos _ t hy)]
    exact factor_flip _ l (by simpa only [x,homeval] using ha)
  · have hy : hom b eb y < 0 := by
      simp only [y,x,map_mul,map_sub,map_one,homeval]
      exact mul_neg_of_pos_of_neg hb (sub_neg.mpr hb')
    have hz : 0 < hom b eb z := by simp only [z,x,map_neg,map_sub,map_one,homeval]; linarith
    have hx : 0 < hom b eb x := by simpa only [x,homeval] using hb
    rw [map_mul,map_mul,mul_pos_iff_of_pos_right (factor_pos _ r hz),
      mul_pos_iff_of_pos_left (factor_pos _ l hx)]
    exact factor_flip _ t hy
  · have hx : 0 < hom c ec x := by rw [show hom c ec x = c from homeval c ec]; linarith
    have hy : 0 < hom c ec y := by
      simp only [y,x,map_mul,map_sub,map_one,homeval]
      exact mul_pos (by linarith) (sub_pos.mpr hc)
    have hz : hom c ec z < 0 := by simp only [z,x,map_neg,map_sub,map_one,homeval]; linarith
    rw [map_mul,map_mul,mul_pos_iff_of_pos_left (mul_pos (factor_pos _ l hx) (factor_pos _ t hy))]
    exact factor_flip _ r hz

#print axioms integral_order_unit_signatures
#print axioms integral_real_specialization
#print axioms integralModel_no_rational_root
#print axioms integralModel_irreducible
#print axioms integralModel_units
#print axioms integral_generator_cycle
#print axioms reciprocal_polynomial_table
end RHTower.OrbitCubic

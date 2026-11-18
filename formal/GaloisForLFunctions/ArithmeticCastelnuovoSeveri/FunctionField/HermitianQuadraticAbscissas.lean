import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianFrobeniusFiberDegrees
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysNormalizedIrreducible

/-!
# The quadratic abscissa obstruction on the Hermitian curve

Around a two-cycle of abscissas the sum of the two tangent increments
is minus the (Q+1)-st power of their difference. Consequently the
quadratic extension of the square constant field adds no curve points,
whereas a genuinely quadratic abscissa acquires its lifts in degree 2p.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Function Polynomial
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianAffinePoint p s E
local notation "F" => hermitianFrobeniusPoint p s E
local notation "dₓ" => hermitianAbscissaDegree p s

/-- The two-edge orbit sum is a single norm power, in every characteristic. -/
theorem hermitianFrobenius_two_cycle_norm (P : H)
    (h : (F^[2] P).val.1 = P.val.1) :
    (F^[2] P).val.2 - P.val.2 = -((F P).val.1 - P.val.1)^(Q+1) := by
  have hs := hermitianFrobenius_ordinate_sum p s P 2
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hs
  simp only [iterate_zero_apply, Nat.zero_add, iterate_one, Nat.reduceAdd] at hs
  rw [h] at hs
  have hp : ((F P).val.1 - P.val.1)^Q = (F P).val.1^Q - P.val.1^Q :=
    map_sub (iterateFrobenius E p (s+1)) _ _
  rw [hs, pow_succ ((F P).val.1 - P.val.1) Q, hp]
  ring

/-- The square of Frobenius has no additional fixed points over the geometric constants. -/
theorem hermitianFrobenius_two_fixed_iff (P : H) : F^[2] P = P ↔ F P = P := by
  refine ⟨?_, fun h => by rw [show F^[2] P = F (F P) from rfl, h, h]⟩
  intro h
  have hn := hermitianFrobenius_two_cycle_norm p s P (congrArg (fun U : H => U.val.1) h)
  rw [h, sub_self] at hn
  have hz := (neg_eq_zero.mp hn.symm)
  apply (hermitianFrobeniusPoint_eq_self_iff p s E P).2
  change (F P).val.1 = P.val.1
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz)

/-- Over a genuinely quadratic abscissa the displacement is always nonzero. -/
theorem hermitianQuadraticAbscissa_displacement (P : H) (hd : dₓ P = 2) :
    hermitianFiberDisplacement p s P = -((F P).val.1 - P.val.1)^(Q+1) ∧
      hermitianFiberDisplacement p s P ≠ 0 := by
  have hx : (F^[2] P).val.1 = P.val.1 := by
    rw [hermitianFrobenius_iterate_coordinates, squareFrobenius_coordinate_fixed_iff]
    change dₓ P ∣ 2
    rw [hd]
  have h := hermitianFrobenius_two_cycle_norm p s P hx
  have he : hermitianFiberDisplacement p s P = -((F P).val.1 - P.val.1)^(Q+1) := by
    unfold hermitianFiberDisplacement
    rw [hd]
    exact h
  refine ⟨he, ?_⟩
  rw [he, neg_ne_zero]
  apply pow_ne_zero
  intro hz
  have hx1 : (F^[1] P).val.1 = P.val.1 := sub_eq_zero.mp hz
  rw [hermitianFrobenius_iterate_coordinates, squareFrobenius_coordinate_fixed_iff] at hx1
  change dₓ P ∣ 1 at hx1
  rw [hd] at hx1
  omega

/-- Every geometric lift over a degree-two abscissa has exact degree 2p over the square field. -/
theorem hermitianQuadraticAbscissa_lift_degree (P : H) (hd : dₓ P = 2) :
    hermitianOrbitDegree p s P = 2*p := by
  rw [hermitianOrbitDegree_fiber_formula, if_neg (hermitianQuadraticAbscissa_displacement p s P hd).2, hd]

/-- The quadratic extension has exactly the same set of geometric curve points as the square field. -/
theorem hermitianFrobenius_fixed_sets_two :
    Function.fixedPoints (F^[2]) = Function.fixedPoints F := by
  ext P
  exact hermitianFrobenius_two_fixed_iff p s P

/-- The affine curve has no closed point of degree two over the square field. -/
theorem hermitianOrbitDegree_ne_two (P : H) : hermitianOrbitDegree p s P ≠ 2 := by
  intro h
  have hf : F^[2] P = P := (hermitianFrobenius_return_iff p s P 2).2 (h ▸ dvd_rfl)
  have hd := (hermitianFrobenius_return_iff p s P 1).1
    (show F^[1] P = P from (hermitianFrobenius_two_fixed_iff p s P).1 hf)
  rw [h] at hd
  omega

/-- Projection of the geometric affine curve onto the abscissa is surjective. -/
theorem hermitianGeometricAbscissa_surjective : Function.Surjective (fun P : H => P.val.1) := by
  intro x
  let f : E[X] := X^Q + (X - C (x^(Q+1)))
  have hQ : 1 < Q := Nat.one_lt_pow (Nat.succ_ne_zero _) (Fact.out : p.Prime).one_lt
  have hd : f.degree ≠ 0 := by
    dsimp only [f]
    rw [degree_add_eq_left_of_degree_lt, degree_X_pow]
    · exact_mod_cast (zero_lt_one.trans hQ).ne'
    · rw [degree_X_sub_C, degree_X_pow]
      exact_mod_cast hQ
  obtain ⟨y,hy⟩ := IsAlgClosed.exists_root f hd
  change eval y (X^Q + (X - C (x^(Q+1)))) = 0 at hy
  simp only [eval_add, eval_pow, eval_X, eval_sub, eval_C] at hy
  exact ⟨⟨(x,y), by change y^Q + y = x^(Q+1); linear_combination hy⟩,rfl⟩

/-- Every positive degree occurs as the degree of a geometric Hermitian abscissa. -/
theorem hermitianGeometricAbscissa_degrees (n : ℕ) (hn : 0 < n) :
    ∃ P : H, dₓ P = n := by
  letI : NeZero n := ⟨hn.ne'⟩
  let K := SquareConstantField p s
  let L := FiniteField.Extension K p n
  obtain ⟨z,hz⟩ := Field.exists_primitive_element_of_finite_top K L
  have hint : IsIntegral K z := Algebra.IsIntegral.isIntegral _
  have hd : (minpoly K z).natDegree = n := by
    rw [← IntermediateField.adjoin.finrank hint, hz, IntermediateField.finrank_top',
      FiniteField.finrank_extension]
  obtain ⟨x,hx⟩ : ∃ x : E, minpoly K x = minpoly K z :=
    _root_.RHTower.deningerExists_minpoly_eq (minpoly.monic hint) (minpoly.irreducible hint)
  obtain ⟨P,hP⟩ := hermitianGeometricAbscissa_surjective p s x
  change P.val.1 = x at hP
  refine ⟨P, ?_⟩
  change (minpoly K P.val.1).natDegree = n
  exact (congrArg (fun t : E => (minpoly K t).natDegree) hP).trans
    ((congrArg Polynomial.natDegree hx).trans hd)

/-- The obstructed degree 2p genuinely occurs on the curve in every characteristic. -/
theorem hermitianGeometric_exists_degree_two_mul_char :
    ∃ P : H, dₓ P = 2 ∧ hermitianOrbitDegree p s P = 2*p := by
  obtain ⟨P,h⟩ := hermitianGeometricAbscissa_degrees p s 2 zero_lt_two
  exact ⟨P,h,hermitianQuadraticAbscissa_lift_degree p s P h⟩

#print axioms hermitianGeometricAbscissa_surjective
#print axioms hermitianGeometricAbscissa_degrees
#print axioms hermitianGeometric_exists_degree_two_mul_char
#print axioms hermitianFrobenius_two_cycle_norm
#print axioms hermitianFrobenius_two_fixed_iff
#print axioms hermitianQuadraticAbscissa_displacement
#print axioms hermitianQuadraticAbscissa_lift_degree
#print axioms hermitianFrobenius_fixed_sets_two
#print axioms hermitianOrbitDegree_ne_two

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

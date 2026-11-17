import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianFrobeniusReturnTimes

/-!
# Splitting of Frobenius orbits over a Hermitian abscissa

Over an abscissa of degree d, the d-th square Frobenius is translation by
a single trace-zero constant on the entire vertical fiber. Its orbits
therefore have length d or pd. The translation is the sum of the tangent
increments around the abscissa orbit.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Function Polynomial
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "k₀" => SquareConstantField p s
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianAffinePoint p s E
local notation "F" => hermitianFrobeniusPoint p s E
local notation "Q" => p ^ (s + 1)
local notation "degX" => fun P : H => (minpoly k₀ P.val.1).natDegree

/-- Vertical displacement during one full cycle of the abscissa. -/
def hermitianFiberDisplacement (P : H) : E := (F^[degX P] P).val.2 - P.val.2

private theorem abscissa_return (P : H) (n : ℕ) :
    (F^[n] P).val.1 = P.val.1 ↔ degX P ∣ n := by
  rw [hermitianFrobenius_iterate_coordinates]
  exact squareFrobenius_coordinate_fixed_iff p s _ _

private theorem same_abscissa (P U : H) (h : P.val.1 = U.val.1) (n : ℕ) :
    (F^[n] P).val.1 = (F^[n] U).val.1 := by
  simp only [hermitianFrobenius_iterate_coordinates, h]

private theorem tangent_increment (P : H) :
    (F P).val.2 - P.val.2 = P.val.1 ^ Q * ((F P).val.1 - P.val.1) := by
  have h := hermitianTangent_eval_frobenius p s E P
  simp only [hermitianTangentPolynomial, eval_add, eval_C, eval_mul, eval_sub, eval_X] at h
  change P.val.2 ^ (Q * Q) - P.val.2 = _
  rw [← h]
  ring

/-- Differences of ordinates in the same fiber are invariant under all Frobenius iterates. -/
theorem hermitianFrobenius_vertical_difference (P U : H) (h : P.val.1 = U.val.1) (n : ℕ) :
    (F^[n] P).val.2 - (F^[n] U).val.2 = P.val.2 - U.val.2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hP := tangent_increment p s (F^[n] P)
    have hU := tangent_increment p s (F^[n] U)
    have hx : (F (F^[n] P)).val.1 = (F (F^[n] U)).val.1 := by
      simpa only [iterate_succ_apply'] using same_abscissa p s P U h (n+1)
    rw [same_abscissa p s P U h n, hx] at hP
    rw [iterate_succ_apply', iterate_succ_apply']
    linear_combination hP - hU + ih

/-- All lifts of the same abscissa have exactly the same Frobenius displacement. -/
theorem hermitianFiberDisplacement_eq (P U : H) (h : P.val.1 = U.val.1) :
    hermitianFiberDisplacement p s P = hermitianFiberDisplacement p s U := by
  unfold hermitianFiberDisplacement
  rw [h]
  linear_combination hermitianFrobenius_vertical_difference p s P U h (degX U)

/-- The displacement is in the kernel of the relative trace on the square field. -/
theorem hermitianFiberDisplacement_trace (P : H) :
    (hermitianFiberDisplacement p s P) ^ Q = -hermitianFiberDisplacement p s P := by
  let U := F^[degX P] P
  have hx : U.val.1 = P.val.1 := (abscissa_return p s P _).2 dvd_rfl
  have hU := U.property
  rw [hx] at hU
  have hmap : (U.val.2 - P.val.2) ^ Q = U.val.2 ^ Q - P.val.2 ^ Q :=
    map_sub (iterateFrobenius E p (s + 1)) _ _
  change (U.val.2 - P.val.2) ^ Q = -(U.val.2 - P.val.2)
  rw [hmap]
  linear_combination hU - P.property

/-- The displacement is the cyclic sum of the tangent increments on the abscissa orbit. -/
theorem hermitianFrobenius_ordinate_sum (P : H) (n : ℕ) :
    (F^[n] P).val.2 - P.val.2 =
      ∑ i ∈ Finset.range n, (F^[i] P).val.1 ^ Q *
        ((F^[i+1] P).val.1 - (F^[i] P).val.1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, iterate_succ_apply']
    have h := tangent_increment p s (F^[n] P)
    rw [iterate_succ_apply' F n P]
    linear_combination h

/-- Each completed base orbit adds another copy of the same vertical displacement. -/
theorem hermitianFrobenius_fiber_translation (P : H) (k : ℕ) :
    (F^[degX P * k] P).val.2 = P.val.2 + k • hermitianFiberDisplacement p s P := by
  induction k with
  | zero => simp
  | succ k ih =>
    let U := F^[degX P] P
    have hx : U.val.1 = P.val.1 := (abscissa_return p s P _).2 dvd_rfl
    have h := hermitianFrobenius_vertical_difference p s U P hx (degX P * k)
    rw [Nat.mul_succ, iterate_add_apply, succ_nsmul]
    change (F^[degX P * k] U).val.2 = _
    change _ = U.val.2 - P.val.2 at h
    change _ = P.val.2 + (k • hermitianFiberDisplacement p s P + (U.val.2 - P.val.2))
    linear_combination h + ih

/-- A nonzero displacement forces exactly p base circuits before the lift returns. -/
theorem hermitianFrobenius_fiber_return_iff (P : H) (k : ℕ) :
    IsPeriodicPt F (degX P * k) P ↔
      p ∣ k ∨ hermitianFiberDisplacement p s P = 0 := by
  change F^[_] P = P ↔ _
  have hval : F^[degX P * k] P = P ↔ (F^[degX P * k] P).val = P.val :=
    ⟨congrArg Subtype.val, Subtype.ext⟩
  rw [hval, Prod.ext_iff, hermitianFrobenius_fiber_translation,
    (abscissa_return p s P _).2 (dvd_mul_right _ _), true_and,
    add_eq_left, nsmul_eq_mul, mul_eq_zero, CharP.cast_eq_zero_iff E p]

/-- Exact degree of every lift, decided by the vertical displacement alone. -/
theorem hermitianOrbitDegree_fiber_formula (P : H) :
    hermitianOrbitDegree p s P =
      if hermitianFiberDisplacement p s P = 0 then degX P else degX P * p := by
  classical
  let d := degX P
  let r := hermitianOrbitDegree p s P
  have hd : d ∣ r := Nat.dvd_lcm_left _ _
  have hr : IsPeriodicPt F r P := (hermitianFrobenius_return_iff p s P r).2 dvd_rfl
  by_cases h : hermitianFiberDisplacement p s P = 0
  · rw [if_pos h]
    apply Nat.dvd_antisymm _ hd
    apply (hermitianFrobenius_return_iff p s P d).1
    have ht := (hermitianFrobenius_fiber_return_iff p s P 1).2 (Or.inr h)
    simpa only [Nat.mul_one] using ht
  · rw [if_neg h]
    apply Nat.dvd_antisymm
    · exact (hermitianFrobenius_return_iff p s P _).1
        ((hermitianFrobenius_fiber_return_iff p s P p).2 (Or.inl dvd_rfl))
    · obtain ⟨k, hk⟩ := hd
      rw [hk] at hr
      have hpk := ((hermitianFrobenius_fiber_return_iff p s P k).1 hr).resolve_right h
      change d * p ∣ r
      rw [hk]
      exact Nat.mul_dvd_mul_left d hpk

#print axioms hermitianFrobenius_vertical_difference
#print axioms hermitianFiberDisplacement_eq
#print axioms hermitianFiberDisplacement_trace
#print axioms hermitianFrobenius_ordinate_sum
#print axioms hermitianFrobenius_fiber_translation
#print axioms hermitianFrobenius_fiber_return_iff
#print axioms hermitianOrbitDegree_fiber_formula

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

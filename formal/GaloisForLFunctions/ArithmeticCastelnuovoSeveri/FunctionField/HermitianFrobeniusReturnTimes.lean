import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricFrobeniusDivisors
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Return times on the geometric Hermitian curve

The periodic-component argument in Yang, Proposition 2.1.1 (arXiv:2302.00948),
gives explicit progressions here. Their modulus is the least common multiple
of the coordinate degrees. A tangent meets the orbit in two consecutive residue
classes, with coincident contacts precisely at degree one.
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

/-- The field of definition of both affine coordinates has degree their least common multiple. -/
def hermitianOrbitDegree (P : H) : ℕ :=
  Nat.lcm (minpoly k₀ P.val.1).natDegree (minpoly k₀ P.val.2).natDegree

private theorem card_square : Nat.card k₀ = Q * Q := by
  rw [squareConstantField_card, two_mul, pow_add]

/-- Coordinates of the n-th orbit point are the square-field cardinal powers. -/
theorem hermitianFrobenius_iterate_coordinates (P : H) (n : ℕ) :
    (F^[n] P).val =
      (P.val.1 ^ (Nat.card k₀ ^ n), P.val.2 ^ (Nat.card k₀ ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply']
    change (((F^[n] P).val.1 ^ (Q * Q)), ((F^[n] P).val.2 ^ (Q * Q))) = _
    simp only [ih, ← card_square p s, pow_succ (Nat.card k₀), pow_mul]

/-- Over the square constant field the minimal-polynomial degree detects every Frobenius return. -/
theorem squareFrobenius_coordinate_fixed_iff (x : E) (n : ℕ) :
    x ^ (Nat.card k₀ ^ n) = x ↔ (minpoly k₀ x).natDegree ∣ n := by
  have hx : IsIntegral k₀ x := Algebra.IsIntegral.isIntegral _
  constructor
  · intro h
    apply (minpoly.irreducible hx).natDegree_dvd_of_dvd_X_pow_card_pow_sub_X
    apply minpoly.dvd k₀ x
    simpa only [map_sub, map_pow, aeval_X, sub_eq_zero] using h
  · rintro ⟨k, rfl⟩
    let L := IntermediateField.adjoin k₀ {x}
    letI : FiniteDimensional k₀ L := IntermediateField.adjoin.finiteDimensional hx
    letI : Finite L := Module.finite_of_finite k₀
    letI := Fintype.ofFinite L
    have hcard : Fintype.card L = Nat.card k₀ ^ (minpoly k₀ x).natDegree := by
      rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := k₀),
        IntermediateField.adjoin.finrank hx]
    have hfix := congrArg (fun t : L => (t : E))
      (FiniteField.pow_card (IntermediateField.AdjoinSimple.gen k₀ x))
    change x ^ Fintype.card L = x at hfix
    rw [hcard] at hfix
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ (minpoly k₀ x).natDegree k, pow_add (Nat.card k₀), pow_mul x, ih, hfix]

/-- The affine orbit returns exactly at multiples of the joint coordinate degree. -/
theorem hermitianFrobenius_return_iff (P : H) (n : ℕ) :
    IsPeriodicPt F n P ↔ hermitianOrbitDegree p s P ∣ n := by
  change F^[n] P = P ↔ _
  have hval : F^[n] P = P ↔ (F^[n] P).val = P.val := ⟨congrArg Subtype.val, Subtype.ext⟩
  rw [hval, hermitianFrobenius_iterate_coordinates, Prod.ext_iff, hermitianOrbitDegree, Nat.lcm_dvd_iff]
  exact and_congr (squareFrobenius_coordinate_fixed_iff p s _ n)
    (squareFrobenius_coordinate_fixed_iff p s _ n)

/-- The orbit length is determined without choosing a common field of definition. -/
theorem hermitianFrobenius_minimalPeriod (P : H) :
    minimalPeriod F P = hermitianOrbitDegree p s P := by
  apply Nat.dvd_antisymm
  · exact ((hermitianFrobenius_return_iff p s P _).2 dvd_rfl).minimalPeriod_dvd
  · exact (hermitianFrobenius_return_iff p s P _).1 (isPeriodicPt_minimalPeriod _ _)

theorem hermitianOrbitDegree_pos (P : H) : 0 < hermitianOrbitDegree p s P :=
  Nat.lcm_pos (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral _))
    (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral _))

/-- Two iterates coincide exactly when their indices are congruent modulo the orbit degree. -/
theorem hermitianFrobenius_iterate_eq_iff (P : H) (m n : ℕ) :
    F^[m] P = F^[n] P ↔ m ≡ n [MOD hermitianOrbitDegree p s P] := by
  let d := minimalPeriod F P
  have hd : 0 < d := by simpa only [d, hermitianFrobenius_minimalPeriod] using hermitianOrbitDegree_pos p s P
  rw [← hermitianFrobenius_minimalPeriod]
  change _ ↔ m % d = n % d
  rw [← iterate_eq_iterate_iff_of_lt_minimalPeriod (f := F) (x := P)
    (Nat.mod_lt m hd) (Nat.mod_lt n hd)]
  exact Iff.of_eq (congrArg₂ Eq iterate_mod_minimalPeriod_eq.symm iterate_mod_minimalPeriod_eq.symm)

/-- The tangent at any orbit point is visited on precisely the two stated progressions. -/
theorem hermitianFrobenius_tangent_return_iff (P : H) (k n : ℕ) :
    (hermitianTangentPolynomial p s E (F^[k] P)).eval (F^[n] P).val.1 = (F^[n] P).val.2 ↔
      n ≡ k [MOD hermitianOrbitDegree p s P] ∨ n ≡ k + 1 [MOD hermitianOrbitDegree p s P] := by
  rw [hermitianTangent_incidence_iff, ← iterate_succ_apply' F k P, hermitianFrobenius_iterate_eq_iff,
    hermitianFrobenius_iterate_eq_iff]

/-- Every subset of geometric points has a finite union of full arithmetic progressions as its hit set. -/
theorem hermitianFrobenius_hit_progressions (P : H) (V : Set H) :
    ∃ R : Finset ℕ, (∀ r ∈ R, r < hermitianOrbitDegree p s P) ∧
      ∀ n, F^[n] P ∈ V ↔ ∃ r ∈ R, n ≡ r [MOD hermitianOrbitDegree p s P] := by
  classical
  let d := hermitianOrbitDegree p s P
  refine ⟨(Finset.range d).filter fun r => F^[r] P ∈ V,
    fun r hr => Finset.mem_range.mp (Finset.mem_filter.mp hr).1, ?_⟩
  intro n
  constructor
  · intro hn
    have hr : n ≡ n % d [MOD d] := (Nat.mod_modEq _ _).symm
    refine ⟨n % d, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (Nat.mod_lt n (hermitianOrbitDegree_pos p s P)), ?_⟩, hr⟩
    rwa [← (hermitianFrobenius_iterate_eq_iff p s P _ _).2 hr]
  · rintro ⟨r, hr, he⟩
    rw [(hermitianFrobenius_iterate_eq_iff p s P _ _).2 he]
    exact (Finset.mem_filter.mp hr).2

#print axioms squareFrobenius_coordinate_fixed_iff
#print axioms hermitianFrobenius_iterate_coordinates
#print axioms hermitianFrobenius_return_iff
#print axioms hermitianFrobenius_minimalPeriod
#print axioms hermitianFrobenius_iterate_eq_iff
#print axioms hermitianFrobenius_tangent_return_iff
#print axioms hermitianFrobenius_hit_progressions
#print axioms hermitianOrbitDegree_pos

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

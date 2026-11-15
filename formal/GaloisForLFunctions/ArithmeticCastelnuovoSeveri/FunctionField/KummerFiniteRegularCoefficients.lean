import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerReducedDifferentials
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerDifferentialCharacterComponents

/-!
# Polynomial coefficients of regular Kummer differentials

A pole of a rational coefficient acquires at least the ramification
index upstairs. An inverse reduced radical differential has order below
that index, so it cannot conceal such a pole. Character projection then
forces every coefficient of a globally regular differential to be a polynomial.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
open GaloisForLFunctions.HTGeometry
variable (p : ℕ) [Fact p.Prime] (s d : ℕ) (c : (SquareConstantField p s)ˣ) (R : ℕ)

/-- A coefficient multiplying an inverse reduced differential cannot have a finite pole. -/
theorem squareKummer_finite_regular_coefficient_polynomial
    (a : FractionRing (SquareConstantField p s)[X]) (i : Fin (p ^ (s + 1) + 1))
    (ha : ∀ w : HeightOneSpectrum (SquareKummerNormalization p s c (p ^ (d + 1) - 2) R),
      w.valuation (SquareKummerField p s c (p ^ (d + 1) - 2) R)
        (algebraMap (FractionRing (SquareConstantField p s)[X])
          (SquareKummerField p s c (p ^ (d + 1) - 2) R) a *
          (squareKummerUniformizerDerivation p s c (p ^ (d + 1) - 2) R
            (placeUniformizer _ w)
            (algebraMap (SquareConstantField p s)[X]
              (SquareKummerField p s c (p ^ (d + 1) - 2) R) X) /
            kummerIntegralMonomial c (p ^ (d + 1) - 2) R (p ^ (s + 1)) i.val)) ≤ 1) :
    a ∈ (algebraMap (SquareConstantField p s)[X]
      (FractionRing (SquareConstantField p s)[X])).range := by
  let K := SquareConstantField p s
  let F := FractionRing K[X]
  let b := p ^ (d + 1) - 2
  let L := SquareKummerField p s c b R
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one F a
  intro v
  obtain ⟨f, hf, rfl⟩ := polynomial_heightOne_exists_irreducible v
  let v := polyPlace hf
  let w := squareKummerPrimeAbove p s c b R v
  let e := (Ideal.span {f}).ramificationIdx' w.asIdeal
  letI : w.asIdeal.LiesOver (Ideal.span {f}) := by
    change w.asIdeal.LiesOver v.asIdeal
    infer_instance
  obtain ⟨k, hk, hform⟩ := squareKummer_finite_inverseMonomial_differential_order p s d c R f hf w i
  have hb : v.valuation F ((algebraMap K[X] F f) ^ k) = WithZero.exp (-(k : ℤ)) := by
    rw [map_pow, polynomial_irreduciblePlace_parameter hf,
      ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg_one]
  apply valuation_le_one_of_power_mul_le_one (v.valuation F) a
    ((algebraMap K[X] F f) ^ k) e k hk hb
  have h := ha w
  rw [map_mul, hform, ← HeightOneSpectrum.valuation_liesOver L v w a] at h
  rw [map_mul, map_pow, hb]
  exact h

/-- Every inverse radical basis coordinate of a globally regular differential is polynomial. -/
theorem squareKummer_regular_basis_coordinate_polynomial
    (f : SquareKummerField p s c (p ^ (d + 1) - 2) R)
    (hf : f • KaehlerDifferential.D (SquareConstantField p s)
      (SquareKummerField p s c (p ^ (d + 1) - 2) R)
      (algebraMap (SquareConstantField p s)[X]
        (SquareKummerField p s c (p ^ (d + 1) - 2) R) X) ∈
        globalRegularDifferentials (SquareConstantField p s)
          (SquareKummerField p s c (p ^ (d + 1) - 2) R))
    (i : Fin (p ^ (s + 1) + 1)) :
    (squareKummerInverseMonomialBasis p s c (p ^ (d + 1) - 2) R).repr f i ∈
      (algebraMap (SquareConstantField p s)[X]
        (FractionRing (SquareConstantField p s)[X])).range := by
  let K := SquareConstantField p s
  let F := FractionRing K[X]
  let b := p ^ (d + 1) - 2
  let L := SquareKummerField p s c b R
  let B := squareKummerInverseMonomialBasis p s c b R
  let a := B.repr f i
  have hcomp := squareKummer_regular_character_component p s c b R f hf i
  apply squareKummer_finite_regular_coefficient_polynomial p s d c R a i
  intro w
  let W : ConstantFieldPlaces K L :=
    ⟨(w.valuation L).valuationSubring, heightOne_valuationSubring_ne_top w, heightOne_constants_mem w⟩
  have hlocal := (mem_globalRegularDifferentials_iff _).mp hcomp W
  have h := (squareKummer_coordinateForm_local_regular_iff p s c b R (w.valuation L)
    (heightOne_constants_mem w) (placeUniformizer L w) (placeUniformizer_valuation L w)
    (a • B i)).mp hlocal
  have heq : (a • B i) * squareKummerUniformizerDerivation p s c b R
      (placeUniformizer L w) (algebraMap K[X] L X) =
      algebraMap F L a * (squareKummerUniformizerDerivation p s c b R
        (placeUniformizer L w) (algebraMap K[X] L X) /
          kummerIntegralMonomial c b R (p ^ (s + 1)) i.val) := by
    rw [squareKummerInverseMonomialBasis_apply, Algebra.smul_def, div_eq_mul_inv]
    ring
  rw [heq] at h
  exact h

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

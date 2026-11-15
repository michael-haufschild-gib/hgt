import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RationalPlaceValuations
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.SmallDivisorIntegrality


/-!
# Reduced two-point divisors cannot conceal denominators

At any finite place, a product of two distinct linear factors has order
zero or one of its two prescribed multiplicities. When both multiplicities
are below `N`, integrality of `x^N` times this product forces `x` to be a polynomial.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable {K : Type*} [Field K]

/-- A linear polynomial has value one away from its own prime and normalized value at that prime. -/
theorem polynomial_linearFactor_valuation (w : HeightOneSpectrum K[X]) (a : K) :
    (w.asIdeal = Ideal.span {X - C a} →
      w.valuation (FractionRing K[X]) (algebraMap K[X] (FractionRing K[X]) (X - C a)) =
        WithZero.exp (-1 : ℤ)) ∧
    (w.asIdeal ≠ Ideal.span {X - C a} →
      w.valuation (FractionRing K[X]) (algebraMap K[X] (FractionRing K[X]) (X - C a)) = 1) := by
  classical
  constructor
  · intro ha
    have he : w = GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C a) :=
      HeightOneSpectrum.ext ha
    rw [he, polynomial_linearPlace_valuation a _ (X_sub_C_ne_zero a),
      rootMultiplicity_X_sub_C, if_pos rfl, Nat.cast_one]
  · intro ha
    apply (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr
    intro hm
    let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C a)
    have hmax : (Ideal.span {X - C a}).IsMaximal := v.isPrime.isMaximal v.ne_bot
    apply ha
    exact (hmax.eq_of_le w.isPrime.ne_top
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm))).symm

/-- A reduced two-point power divisor has every finite multiplicity below the covering degree. -/
theorem polynomial_twoPointPower_valuation (c : Kˣ) (a b : K) (hab : a ≠ b)
    (N i j : ℕ) (hi : i < N) (hj : j < N) (w : HeightOneSpectrum K[X]) :
    ∃ m : ℕ, m < N ∧
      w.valuation (FractionRing K[X]) (algebraMap K[X] (FractionRing K[X])
        (C (c : K) * (X - C a) ^ i * (X - C b) ^ j)) = WithZero.exp (-(m : ℤ)) := by
  classical
  have hc : w.valuation (FractionRing K[X]) (algebraMap K[X] (FractionRing K[X]) (C (c : K))) = 1 := by
    change w.valuation (FractionRing K[X])
      (algebraMap K[X] (FractionRing K[X]) (algebraMap K K[X] (c : K))) = 1
    rw [← IsScalarTower.algebraMap_apply K K[X] (FractionRing K[X])]
    exact heightOne_valuation_constant w (c : K) c.ne_zero
  have hv := polynomial_linearFactor_valuation w a
  have hw := polynomial_linearFactor_valuation w b
  by_cases ha : w.asIdeal = Ideal.span {X - C a}
  · have he : w = GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C a) :=
      HeightOneSpectrum.ext ha
    have hb : w.valuation (FractionRing K[X]) (algebraMap K[X] (FractionRing K[X]) (X - C b)) = 1 := by
      rw [he, polynomial_linearPlace_valuation a _ (X_sub_C_ne_zero b)]
      simp only [rootMultiplicity_X_sub_C, if_neg hab, Nat.cast_zero, neg_zero, WithZero.exp_zero]
    have hv := hv.1 ha
    refine ⟨i, hi, ?_⟩
    simp only [map_mul, map_pow, hc, hv, hb, one_mul, one_pow, mul_one]
    rw [← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg, mul_one]
  · have hv := hv.2 ha
    by_cases hb : w.asIdeal = Ideal.span {X - C b}
    · have hw := hw.1 hb
      refine ⟨j, hj, ?_⟩
      simp only [map_mul, map_pow, hc, hv, hw, one_mul, one_pow]
      rw [← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg, mul_one]
    · have hw := hw.2 hb
      refine ⟨0, lt_of_le_of_lt (Nat.zero_le i) hi, ?_⟩
      simp only [map_mul, map_pow, hc, hv, hw, one_pow, one_mul,
        Nat.cast_zero, neg_zero, WithZero.exp_zero]

/-- No rational-function denominator can survive an integral power product with a reduced two-point divisor. -/
theorem polynomial_twoPointPower_no_denominator
    (c : Kˣ) (a b : K) (hab : a ≠ b) (N i j : ℕ) (hi : i < N) (hj : j < N)
    (x : FractionRing K[X])
    (hx : x ^ N * algebraMap K[X] (FractionRing K[X])
      (C (c : K) * (X - C a) ^ i * (X - C b) ^ j) ∈ (algebraMap K[X] (FractionRing K[X])).range) :
    x ∈ (algebraMap K[X] (FractionRing K[X])).range :=
  mem_fractionRing_base_of_power_mul_mem x _ N
    (polynomial_twoPointPower_valuation c a b hab N i j hi hj) hx

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

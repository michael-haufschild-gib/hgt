import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerLocalDifferentials
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerLocalDifferentialOrders

/-!
# Valuation tests for intrinsic regular differentials

The local Kähler-image condition becomes a valuation inequality after
expressing a differential in a uniformizer coordinate. The intrinsic
classification of places reduces global regularity to all finite
normalization valuations and the unique infinity valuation.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain ArithmeticHarmonicAnalysis
open GaloisForLFunctions.HTGeometry

/-- A differential is locally regular precisely when its uniformizer coefficient is integral. -/
theorem squareKummer_localDifferential_valuation_iff
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)
    (v : Valuation (SquareKummerField p s c b R) (WithZero (Multiplicative ℤ)))
    (hK : ∀ a : SquareConstantField p s,
      algebraMap (SquareConstantField p s) (SquareKummerField p s c b R) a ∈ v.valuationSubring)
    (π : SquareKummerField p s c b R) (hπ : v π = WithZero.exp (-1 : ℤ))
    (ω : KaehlerDifferential (SquareConstantField p s) (SquareKummerField p s c b R)) :
    ω ∈ valuationLocalDifferentials v.valuationSubring hK ↔
      v ((squareKummerCoordinateDerivation p s c b R π)⁻¹ *
        squareKummerDifferentialEquiv p s c b R ω) ≤ 1 := by
  rw [squareKummer_mem_localDifferentials_iff p s c b R v hK π hπ]
  have hne := squareKummerCoordinateDerivation_uniformizer_ne_zero p s c b R v π hπ
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [map_smul, smul_eq_mul]
    change v ((squareKummerCoordinateDerivation p s c b R π)⁻¹ *
      (a * squareKummerCoordinateDerivation p s c b R π)) ≤ 1
    rw [mul_left_comm, inv_mul_cancel₀ hne, mul_one]
    exact ha
  · intro h
    refine ⟨_, h, ?_⟩
    apply (squareKummerDifferentialEquiv p s c b R).injective
    rw [map_smul, smul_eq_mul]
    change squareKummerDifferentialEquiv p s c b R ω =
      ((squareKummerCoordinateDerivation p s c b R π)⁻¹ *
        squareKummerDifferentialEquiv p s c b R ω) * squareKummerCoordinateDerivation p s c b R π
    rw [mul_right_comm, inv_mul_cancel₀ hne, one_mul]

/-- For a form `f dy`, local regularity is the integrality of `f` times the local derivative of `y`. -/
theorem squareKummer_coordinateForm_local_regular_iff
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)
    (v : Valuation (SquareKummerField p s c b R) (WithZero (Multiplicative ℤ)))
    (hK : ∀ a : SquareConstantField p s,
      algebraMap (SquareConstantField p s) (SquareKummerField p s c b R) a ∈ v.valuationSubring)
    (π : SquareKummerField p s c b R) (hπ : v π = WithZero.exp (-1 : ℤ))
    (f : SquareKummerField p s c b R) :
    f • KaehlerDifferential.D (SquareConstantField p s) (SquareKummerField p s c b R)
      (algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) X) ∈
        valuationLocalDifferentials v.valuationSubring hK ↔
      v (f * squareKummerUniformizerDerivation p s c b R π
        (algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) X)) ≤ 1 := by
  rw [squareKummer_localDifferential_valuation_iff p s c b R v hK π hπ,
    map_smul, smul_eq_mul, squareKummerDifferentialEquiv_D_polynomial, derivative_X, map_one, mul_one,
    squareKummerUniformizerDerivation_apply, squareKummerCoordinateDerivation_polynomial,
    derivative_X, map_one, mul_one, mul_comm]

/-- The finite normalization valuations and the unique infinity valuation test global regularity exactly. -/
theorem squareKummer_coordinateForm_global_regular_iff
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)
    (f : SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) :
    f • KaehlerDifferential.D (SquareConstantField p s)
      (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r))
      (algebraMap (SquareConstantField p s)[X]
        (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) X) ∈
      globalRegularDifferentials (SquareConstantField p s)
        (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) ↔
    (∀ w : HeightOneSpectrum (SquareKummerNormalization p s c (p ^ (d + 1) - 2)
        (kummerExponent (p ^ (d + 1)) r)),
      w.valuation _ (f * squareKummerUniformizerDerivation p s c (p ^ (d + 1) - 2)
        (kummerExponent (p ^ (d + 1)) r) (placeUniformizer _ w)
        (algebraMap (SquareConstantField p s)[X]
          (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) X)) ≤ 1) ∧
    squareKummerInfinityValuation p s c d r
      (f * squareKummerUniformizerDerivation p s c (p ^ (d + 1) - 2)
        (kummerExponent (p ^ (d + 1)) r) (squareKummerInfinityUniformizer p s c d r)
        (algebraMap (SquareConstantField p s)[X]
          (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) X)) ≤ 1 := by
  let b := p ^ (d + 1) - 2
  let R := kummerExponent (p ^ (d + 1)) r
  let L := SquareKummerField p s c b R
  constructor
  · intro h
    have hloc := (mem_globalRegularDifferentials_iff _).mp h
    constructor
    · intro w
      exact (squareKummer_coordinateForm_local_regular_iff p s c b R (w.valuation L)
        (heightOne_constants_mem w) (placeUniformizer L w) (placeUniformizer_valuation L w) f).mp
          (hloc (squareKummerFiniteConstantPlace p s c d r w))
    · exact (squareKummer_coordinateForm_local_regular_iff p s c b R
        (squareKummerInfinityValuation p s c d r)
        (squareKummerInfinityConstantPlace p s c d r).property.2
        (squareKummerInfinityUniformizer p s c d r) (squareKummerInfinityUniformizer_value p s c d r) f).mp
          (hloc (squareKummerInfinityConstantPlace p s c d r))
  · rintro ⟨hfin, hinf⟩
    rw [mem_globalRegularDifferentials_iff]
    intro W
    rcases squareKummer_constantPlace_cases p s c d r W with ⟨w, hw⟩ | hw
    · rw [← hw]
      exact (squareKummer_coordinateForm_local_regular_iff p s c b R (w.valuation L)
        (heightOne_constants_mem w) (placeUniformizer L w) (placeUniformizer_valuation L w) f).mpr (hfin w)
    · rw [← hw]
      exact (squareKummer_coordinateForm_local_regular_iff p s c b R
        (squareKummerInfinityValuation p s c d r)
        (squareKummerInfinityConstantPlace p s c d r).property.2
        (squareKummerInfinityUniformizer p s c d r) (squareKummerInfinityUniformizer_value p s c d r) f).mpr hinf

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

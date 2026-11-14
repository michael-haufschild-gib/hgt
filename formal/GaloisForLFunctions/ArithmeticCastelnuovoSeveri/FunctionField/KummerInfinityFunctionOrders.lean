import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityPlace

/-!
# Pole orders of the Kummer coordinates

The normalized infinity valuation is transported to the original radical
field. Total ramification gives pole order `Q+1` for the base coordinate;
the radical equation then gives pole order `q^r` for the radical. These
orders are computed on the actual field, without a genus assumption.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
open GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)

/-- The infinity valuation on the original Kummer field, transported from its normalized chart. -/
def squareKummerInfinityValuation : Valuation
    (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r))
    (WithZero (Multiplicative ℤ)) :=
  ((squareKummerInfinityPlace p s c d r).valuation
    (KummerInfinityField c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r) (p ^ (s + 1)))).comap
      (kummerInfinityFieldEquiv c (p ^ (d + 1) - 2)
        (kummerExponent (p ^ (d + 1)) r) (p ^ (s + 1))).toRingHom

private theorem infinity_newCoordinate :
    (squareKummerInfinityPlace p s c d r).valuation
      (KummerInfinityField c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r) (p ^ (s + 1)))
      (algebraMap (SquareConstantField p s)[X]
        (KummerInfinityField c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r) (p ^ (s + 1))) X) =
        WithZero.exp (-((p ^ (s + 1) + 1 : ℕ) : ℤ)) := by
  let v := kummerInfinityBasePlace (K := SquareConstantField p s)
  let w := squareKummerInfinityPlace p s c d r
  letI : w.asIdeal.LiesOver v.asIdeal := by
    change (squareKummerInfinityPlace p s c d r).asIdeal.LiesOver
      (Ideal.span {(X : (SquareConstantField p s)[X])})
    infer_instance
  have h := HeightOneSpectrum.valuation_liesOver
    (KummerInfinityField c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r) (p ^ (s + 1))) v w
    (algebraMap (SquareConstantField p s)[X] (FractionRing (SquareConstantField p s)[X]) X)
  rw [kummerInfinityBasePlace_coordinate, ← IsScalarTower.algebraMap_apply] at h
  change WithZero.exp (-1 : ℤ) ^
      (Ideal.span {(X : (SquareConstantField p s)[X])}).ramificationIdx'
        (squareKummerInfinityPlace p s c d r).asIdeal = _ at h
  rw [squareKummerInfinityPlace_ramification, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg_one] at h
  exact h.symm

/-- The original base coordinate has pole order `Q+1`. -/
theorem squareKummerInfinityValuation_coordinate :
    squareKummerInfinityValuation p s c d r
      (algebraMap (SquareConstantField p s)[X]
        (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) X) =
      WithZero.exp ((p ^ (s + 1) + 1 : ℕ) : ℤ) := by
  change (squareKummerInfinityPlace p s c d r).valuation _
    (kummerInfinityFieldEquiv c (p ^ (d + 1) - 2)
      (kummerExponent (p ^ (d + 1)) r) (p ^ (s + 1))
      (algebraMap (SquareConstantField p s)[X] _ X)) = _
  rw [kummerInfinityFieldEquiv_coordinate, map_inv₀, infinity_newCoordinate,
    ← WithZero.exp_neg, neg_neg]

/-- The original radical has pole order `q^r`. -/
theorem squareKummerInfinityValuation_root :
    squareKummerInfinityValuation p s c d r
      (AdjoinRoot.root (kummerBranchFieldPolynomial c (p ^ (d + 1) - 2)
        (kummerExponent (p ^ (d + 1)) r) (p ^ (s + 1)))) =
      WithZero.exp (((p ^ (d + 1)) ^ r : ℕ) : ℤ) := by
  let v := kummerInfinityBasePlace (K := SquareConstantField p s)
  let w := squareKummerInfinityPlace p s c d r
  let L := KummerInfinityField c (p ^ (d + 1) - 2)
    (kummerExponent (p ^ (d + 1)) r) (p ^ (s + 1))
  let z : L := AdjoinRoot.root (kummerInfinityPolynomial c (p ^ (d + 1) - 2)
    (kummerExponent (p ^ (d + 1)) r) (p ^ (s + 1)))
  letI : w.asIdeal.LiesOver v.asIdeal := by
    change (squareKummerInfinityPlace p s c d r).asIdeal.LiesOver
      (Ideal.span {(X : (SquareConstantField p s)[X])})
    infer_instance
  have h := congrArg (w.valuation L)
    (kummerInfinityField_root_pow c (p ^ (d + 1) - 2)
      (kummerExponent (p ^ (d + 1)) r) (p ^ (s + 1)))
  rw [map_pow, ← HeightOneSpectrum.valuation_liesOver L v w,
    kummerInfinityBasePlace_branch, kummerInfinity_primePower_poleDegree] at h
  change w.valuation L z ^ (p ^ (s + 1) + 1) =
    WithZero.exp (((p ^ (d + 1)) ^ r : ℕ) : ℤ) ^
      (Ideal.span {(X : (SquareConstantField p s)[X])}).ramificationIdx'
        (squareKummerInfinityPlace p s c d r).asIdeal at h
  rw [squareKummerInfinityPlace_ramification] at h
  have hz0 : w.valuation L z ≠ 0 := by
    intro hz
    rw [hz, zero_pow (Nat.succ_ne_zero _)] at h
    exact (pow_ne_zero _ WithZero.exp_ne_zero) h.symm
  have hl := congrArg WithZero.log h
  simp only [WithZero.log_pow, WithZero.log_exp, nsmul_eq_mul] at hl
  have hlog := mul_left_cancel₀ (show ((p ^ (s + 1) + 1 : ℕ) : ℤ) ≠ 0 by
    exact_mod_cast Nat.succ_ne_zero (p ^ (s + 1))) hl
  change w.valuation L (kummerInfinityFieldEquiv c (p ^ (d + 1) - 2)
    (kummerExponent (p ^ (d + 1)) r) (p ^ (s + 1))
    (AdjoinRoot.root (kummerBranchFieldPolynomial c (p ^ (d + 1) - 2)
      (kummerExponent (p ^ (d + 1)) r) (p ^ (s + 1))))) = _
  rw [kummerInfinityFieldEquiv_root]
  change w.valuation L z = _
  rw [← WithZero.exp_log hz0, hlog]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerOriginRamification
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRamificationOrders
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RationalPlaceValuations

/-!
# Zero orders at the normalized Kummer origin

The original coordinate has order `Q+1` at the unique origin place.
The branch polynomial has a simple base zero, so the radical equation
makes the radical a uniformizer of the actual normalization valuation.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)

/-- The unique origin prime, viewed as a height-one place of the normalization. -/
def squareKummerOriginPlace : HeightOneSpectrum (SquareKummerNormalization p s c b R) :=
  ⟨squareKummerOriginIdeal p s c b R, inferInstance, squareKummerOriginIdeal_ne_bot p s c b R⟩

/-- The normalized adic valuation at the actual origin place. -/
def squareKummerOriginValuation :
    Valuation (SquareKummerField p s c b R) (WithZero (Multiplicative ℤ)) :=
  (squareKummerOriginPlace p s c b R).valuation (SquareKummerField p s c b R)

/-- The coordinate has zero order equal to the covering degree at the origin. -/
theorem squareKummerOriginValuation_coordinate :
    squareKummerOriginValuation p s c b R
      (algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) X) =
        WithZero.exp (-((p ^ (s + 1) + 1 : ℕ) : ℤ)) := by
  classical
  let K := SquareConstantField p s
  let F := FractionRing K[X]
  let L := SquareKummerField p s c b R
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C (0 : K))
  let w := squareKummerOriginPlace p s c b R
  letI : w.asIdeal.LiesOver v.asIdeal := by
    change (squareKummerOriginIdeal p s c b R).LiesOver (Ideal.span {X - C (0 : K)})
    simpa only [map_zero, sub_zero] using squareKummerOriginIdeal_liesOver p s c b R
  have hm : rootMultiplicity (0 : K) (X : K[X]) = 1 := by
    simpa only [map_zero, sub_zero, if_true] using
      (rootMultiplicity_X_sub_C (x := (0 : K)) (y := (0 : K)))
  have hv : v.valuation F (algebraMap K[X] F X) = WithZero.exp (-1 : ℤ) := by
    rw [polynomial_linearPlace_valuation (0 : K) _ X_ne_zero, hm, Nat.cast_one]
  have h := HeightOneSpectrum.valuation_liesOver L v w (algebraMap K[X] F X)
  rw [hv, ← IsScalarTower.algebraMap_apply] at h
  change WithZero.exp (-1 : ℤ) ^ (Ideal.span {X - C (0 : K)}).ramificationIdx'
    (squareKummerOriginIdeal p s c b R) = squareKummerOriginValuation p s c b R _ at h
  rw [map_zero, sub_zero, squareKummerOriginIdeal_ramification,
    ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg_one] at h
  exact h.symm

/-- The radical has a simple zero and is therefore a uniformizer at the origin. -/
theorem squareKummerOriginValuation_root :
    squareKummerOriginValuation p s c b R
      (AdjoinRoot.root (kummerBranchFieldPolynomial c b R (p ^ (s + 1)))) =
        WithZero.exp (-1 : ℤ) := by
  let K := SquareConstantField p s
  let F := FractionRing K[X]
  let L := SquareKummerField p s c b R
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C (0 : K))
  let w := squareKummerOriginPlace p s c b R
  let z : L := AdjoinRoot.root (kummerBranchFieldPolynomial c b R (p ^ (s + 1)))
  letI : w.asIdeal.LiesOver v.asIdeal := by
    change (squareKummerOriginIdeal p s c b R).LiesOver (Ideal.span {X - C (0 : K)})
    simpa only [map_zero, sub_zero] using squareKummerOriginIdeal_liesOver p s c b R
  have hf : kummerBranch c b R ≠ 0 := by
    intro h
    have hc := congrArg (fun f : K[X] => f.coeff 1) h
    rw [kummerBranch_coeff_one, coeff_zero] at hc
    exact c.ne_zero hc
  have hv : v.valuation F (algebraMap K[X] F (kummerBranch c b R)) = WithZero.exp (-1 : ℤ) := by
    rw [polynomial_linearPlace_valuation (0 : K) _ hf, kummerBranch_rootMultiplicity_origin, Nat.cast_one]
  have h := congrArg (w.valuation L) (kummerBranchField_root_pow c b R (p ^ (s + 1)))
  rw [map_pow, ← HeightOneSpectrum.valuation_liesOver L v w, hv] at h
  change w.valuation L z ^ (p ^ (s + 1) + 1) = WithZero.exp (-1 : ℤ) ^
    (Ideal.span {X - C (0 : K)}).ramificationIdx' (squareKummerOriginIdeal p s c b R) at h
  rw [map_zero, sub_zero, squareKummerOriginIdeal_ramification] at h
  have hz0 : w.valuation L z ≠ 0 := by
    intro hz
    rw [hz, zero_pow (Nat.succ_ne_zero _)] at h
    exact (pow_ne_zero _ WithZero.exp_ne_zero) h.symm
  have hl := congrArg WithZero.log h
  simp only [WithZero.log_pow, WithZero.log_exp, nsmul_eq_mul] at hl
  have hlog := mul_left_cancel₀ (show ((p ^ (s + 1) + 1 : ℕ) : ℤ) ≠ 0 by
    exact_mod_cast Nat.succ_ne_zero (p ^ (s + 1))) hl
  change w.valuation L z = _
  rw [← WithZero.exp_log hz0, hlog]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

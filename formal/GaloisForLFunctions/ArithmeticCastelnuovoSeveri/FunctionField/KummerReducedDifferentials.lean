import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerFiniteDifferentialOrders
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerLocalRegularityCriterion
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerIntegralMonomials
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerPowerFreeDivisors
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.ValuationPowerOrders

/-!
# Finite regularity of inverse radical differentials

The reduced radical monomials have orders strictly below the local
ramification index. The coordinate differential has order one less than
that index, so dividing it by any reduced monomial remains regular at
every finite normalization place, regardless of residue degree.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
open GaloisForLFunctions.HTGeometry
variable (p : ℕ) [Fact p.Prime] (s d : ℕ) (c : (SquareConstantField p s)ˣ) (R : ℕ)

/-- An inverse reduced radical differential has nonnegative order strictly below ramification. -/
theorem squareKummer_finite_inverseMonomial_differential_order
    (f : (SquareConstantField p s)[X]) (hf : Irreducible f)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c (p ^ (d + 1) - 2) R))
    [w.asIdeal.LiesOver (Ideal.span {f})] (i : Fin (p ^ (s + 1) + 1)) :
    ∃ k : ℕ, k < (Ideal.span {f}).ramificationIdx' w.asIdeal ∧
      w.valuation (SquareKummerField p s c (p ^ (d + 1) - 2) R)
        (squareKummerUniformizerDerivation p s c (p ^ (d + 1) - 2) R
          (placeUniformizer _ w)
          (algebraMap (SquareConstantField p s)[X]
            (SquareKummerField p s c (p ^ (d + 1) - 2) R) X) /
          kummerIntegralMonomial c (p ^ (d + 1) - 2) R (p ^ (s + 1)) i.val) =
        WithZero.exp (-(k : ℤ)) := by
  let K := SquareConstantField p s
  let F := FractionRing K[X]
  let b := p ^ (d + 1) - 2
  let L := SquareKummerField p s c b R
  let N := p ^ (s + 1) + 1
  let v₀ := polyPlace hf
  let e := (Ideal.span {f}).ramificationIdx' w.asIdeal
  let g : K[X] := C ((c : K) ^ i.val) * X ^ i.val *
    (1 - X ^ (b + 1)) ^ (i.val * R % N)
  let β := kummerIntegralMonomial c b R (p ^ (s + 1)) i.val
  letI : w.asIdeal.LiesOver v₀.asIdeal := by
    change w.asIdeal.LiesOver (Ideal.span {f})
    infer_instance
  obtain ⟨m, hm, hbase⟩ := polynomial_reducedBranchPower_valuation (c ^ i.val) b
    (squareConstantField_branchExponent_ne_zero p s d) N i.val (i.val * R % N)
    i.isLt (Nat.mod_lt _ (Nat.succ_pos _)) v₀
  change v₀.valuation F (algebraMap K[X] F g) = WithZero.exp (-(m : ℤ)) at hbase
  have hpower : w.valuation L (β ^ N) = WithZero.exp (-((e * m : ℕ) : ℤ)) := by
    have h := HeightOneSpectrum.valuation_liesOver L v₀ w (algebraMap K[X] F g)
    rw [hbase, ← IsScalarTower.algebraMap_apply,
      ← WithZero.exp_nsmul, nsmul_eq_mul] at h
    rw [kummerIntegralMonomial_pow]
    change w.valuation L (algebraMap K[X] L g) = _
    rw [← h]
    congr 1
    change (e : ℤ) * (-(m : ℤ)) = -((e * m : ℕ) : ℤ)
    push_cast
    ring
  exact valuation_div_reduced_power_order (w.valuation L) _ β N e m
    (squareKummer_ramification_pos p s c b R v₀ w) hm hpower
    (squareKummer_finite_derivative_coordinate p s c b R f hf w)

/-- Every inverse reduced radical differential belongs to each actual finite local Kähler image. -/
theorem squareKummer_inverseMonomial_differential_finite_regular
    (w : HeightOneSpectrum (SquareKummerNormalization p s c (p ^ (d + 1) - 2) R))
    (i : Fin (p ^ (s + 1) + 1)) :
    (kummerIntegralMonomial c (p ^ (d + 1) - 2) R (p ^ (s + 1)) i.val)⁻¹ •
      KaehlerDifferential.D (SquareConstantField p s)
        (SquareKummerField p s c (p ^ (d + 1) - 2) R)
        (algebraMap (SquareConstantField p s)[X]
          (SquareKummerField p s c (p ^ (d + 1) - 2) R) X) ∈
      valuationLocalDifferentials (w.valuation _).valuationSubring (heightOne_constants_mem w) := by
  let L := SquareKummerField p s c (p ^ (d + 1) - 2) R
  obtain ⟨f, hf, hw⟩ := squareKummer_finitePlace_liesOver_irreducible p s c _ R w
  letI := hw
  obtain ⟨k, _, hk⟩ := squareKummer_finite_inverseMonomial_differential_order p s d c R f hf w i
  rw [squareKummer_coordinateForm_local_regular_iff p s c _ R (w.valuation L)
    (heightOne_constants_mem w) (placeUniformizer L w) (placeUniformizer_valuation L w)]
  rw [mul_comm (kummerIntegralMonomial c (p ^ (d + 1) - 2) R (p ^ (s + 1)) i.val)⁻¹,
    ← div_eq_mul_inv, hk, ← WithZero.exp_zero, WithZero.exp_le_exp]
  exact neg_nonpos.mpr (Nat.cast_nonneg _)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

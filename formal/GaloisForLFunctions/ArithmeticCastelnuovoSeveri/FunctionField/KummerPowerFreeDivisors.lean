import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.TwoPointPowerDivisors
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerBranchUnit
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerTraceConstants
import Mathlib.Algebra.Squarefree.Basic
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.PolynomialPrimeParameters

/-!
# Reduced Kummer divisors have no hidden denominators

The nonlinear branch factor is squarefree when its exponent is nonzero
in the constant field. Its support excludes the origin. Consequently
every multiplicity of `c X^i (1-X^m)^j` is below `N` when `i,j<N`.
The valuation criterion then excludes denominators in an integral power product.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable {K : Type*} [Field K]

/-- A squarefree polynomial has normalized order zero or one at every finite place. -/
theorem polynomial_squarefree_valuation (f : K[X]) (hf : Squarefree f)
    (w : HeightOneSpectrum K[X]) :
    ∃ m : ℕ, m ≤ 1 ∧ w.valuation (FractionRing K[X])
      (algebraMap K[X] (FractionRing K[X]) f) = WithZero.exp (-(m : ℤ)) := by
  obtain ⟨π, hπ, rfl⟩ := polynomial_heightOne_exists_irreducible w
  have hμ : (multiplicity π f : ℕ∞) ≤ 1 := multiplicity_le_emultiplicity.trans
    (((squarefree_iff_emultiplicity_le_one f).mp hf π).resolve_right hπ.not_isUnit)
  exact ⟨multiplicity π f, by exact_mod_cast hμ,
    polynomial_irreduciblePlace_valuation hπ f hf.ne_zero⟩

/-- A branch factor with exponent prime to the characteristic is squarefree. -/
theorem kummerBranchFactor_squarefree (b : ℕ) (hb : (b + 1 : K) ≠ 0) :
    Squarefree (1 - X ^ (b + 1) : K[X]) := by
  have hs : Squarefree (X ^ (b + 1) - 1 : K[X]) :=
    ((X_pow_sub_one_separable_iff).mpr (by exact_mod_cast hb)).squarefree
  intro a ha
  apply hs a
  simpa only [neg_sub] using dvd_neg.mpr ha

/-- The reduced branch divisor has all finite multiplicities below the covering degree. -/
theorem polynomial_reducedBranchPower_valuation (c : Kˣ) (b : ℕ)
    (hb : (b + 1 : K) ≠ 0) (N i j : ℕ) (hi : i < N) (hj : j < N)
    (w : HeightOneSpectrum K[X]) :
    ∃ m : ℕ, m < N ∧ w.valuation (FractionRing K[X])
      (algebraMap K[X] (FractionRing K[X])
        (C (c : K) * X ^ i * (1 - X ^ (b + 1)) ^ j)) = WithZero.exp (-(m : ℤ)) := by
  classical
  have hc : w.valuation (FractionRing K[X]) (algebraMap K[X] (FractionRing K[X]) (C (c : K))) = 1 := by
    change w.valuation (FractionRing K[X])
      (algebraMap K[X] (FractionRing K[X]) (algebraMap K K[X] (c : K))) = 1
    rw [← IsScalarTower.algebraMap_apply K K[X] (FractionRing K[X])]
    exact heightOne_valuation_constant w (c : K) c.ne_zero
  by_cases hw : w.asIdeal = Ideal.span {(X : K[X])}
  · have he : w = GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C (0 : K)) := by
      apply HeightOneSpectrum.ext
      change w.asIdeal = Ideal.span {X - C (0 : K)}
      simpa only [map_zero, sub_zero] using hw
    have hX : w.valuation (FractionRing K[X]) (algebraMap K[X] (FractionRing K[X]) X) = WithZero.exp (-1 : ℤ) := by
      simpa only [map_zero, sub_zero] using
        (polynomial_linearFactor_valuation w (0 : K)).1 (by simpa only [map_zero, sub_zero] using hw)
    have hh : w.valuation (FractionRing K[X]) (algebraMap K[X] (FractionRing K[X]) (1 - X ^ (b + 1))) = 1 := by
      rw [he, polynomial_linearPlace_valuation (0 : K) _ (kummerBranchFactor_ne_zero b),
        rootMultiplicity_eq_zero (by simp only [IsRoot, eval_sub, eval_one, eval_pow, eval_X,
          zero_pow (Nat.succ_ne_zero b), sub_zero]; exact one_ne_zero),
        Nat.cast_zero, neg_zero, WithZero.exp_zero]
    refine ⟨i, hi, ?_⟩
    simp only [map_mul, map_pow, hc, hX, hh, one_mul, one_pow, mul_one]
    rw [← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg_one]
  · have hX : w.valuation (FractionRing K[X]) (algebraMap K[X] (FractionRing K[X]) X) = 1 := by
      simpa only [map_zero, sub_zero] using
        (polynomial_linearFactor_valuation w (0 : K)).2 (by simpa only [map_zero, sub_zero] using hw)
    obtain ⟨m, hm, hh⟩ := polynomial_squarefree_valuation (1 - X ^ (b + 1))
      (kummerBranchFactor_squarefree b hb) w
    refine ⟨j * m, (Nat.mul_le_mul_left j hm).trans_lt (by simpa only [mul_one] using hj), ?_⟩
    simp only [map_mul, map_pow, hc, hX, hh, one_mul, one_pow]
    rw [← WithZero.exp_nsmul]
    congr 1
    simp only [nsmul_eq_mul, Nat.cast_mul, mul_neg]

/-- A reduced Kummer divisor cannot cancel a denominator raised to the covering degree. -/
theorem polynomial_reducedBranchPower_no_denominator (c : Kˣ) (b : ℕ)
    (hb : (b + 1 : K) ≠ 0) (N i j : ℕ) (hi : i < N) (hj : j < N)
    (x : FractionRing K[X])
    (hx : x ^ N * algebraMap K[X] (FractionRing K[X])
      (C (c : K) * X ^ i * (1 - X ^ (b + 1)) ^ j) ∈ (algebraMap K[X] (FractionRing K[X])).range) :
    x ∈ (algebraMap K[X] (FractionRing K[X])).range :=
  mem_fractionRing_base_of_power_mul_mem x _ N
    (polynomial_reducedBranchPower_valuation c b hb N i j hi hj) hx

/-- The prime-power branch exponent is always nonzero in the actual constant field. -/
theorem squareConstantField_branchExponent_ne_zero (p : ℕ) [Fact p.Prime] (s d : ℕ) :
    ((p ^ (d + 1) - 2 : ℕ) : SquareConstantField p s) + 1 ≠ 0 := by
  have hq : 2 ≤ p ^ (d + 1) :=
    Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  have h := congrArg (fun n : ℕ => (n : SquareConstantField p s))
    (show p ^ (d + 1) - 2 + 1 + 1 = p ^ (d + 1) by omega)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow] at h
  rw [CharP.cast_eq_zero (SquareConstantField p s) p, zero_pow (Nat.succ_ne_zero d)] at h
  intro hz
  rw [hz, zero_add] at h
  exact one_ne_zero h

/-- The no-denominator criterion applies to every reduced divisor in the prime-power family. -/
theorem squareKummer_reducedBranchPower_no_denominator
    (p : ℕ) [Fact p.Prime] (s d : ℕ) (c : (SquareConstantField p s)ˣ)
    (N i j : ℕ) (hi : i < N) (hj : j < N)
    (x : FractionRing (SquareConstantField p s)[X])
    (hx : x ^ N * algebraMap (SquareConstantField p s)[X] (FractionRing (SquareConstantField p s)[X])
      (C (c : SquareConstantField p s) * X ^ i * (1 - X ^ (p ^ (d + 1) - 2 + 1)) ^ j) ∈
        (algebraMap (SquareConstantField p s)[X] (FractionRing (SquareConstantField p s)[X])).range) :
    x ∈ (algebraMap (SquareConstantField p s)[X] (FractionRing (SquareConstantField p s)[X])).range :=
  polynomial_reducedBranchPower_no_denominator c _
    (squareConstantField_branchExponent_ne_zero p s d) N i j hi hj x hx

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

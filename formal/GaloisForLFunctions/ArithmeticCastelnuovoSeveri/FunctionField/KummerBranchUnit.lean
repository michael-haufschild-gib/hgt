import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerNormalization
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.InertiaUnitCharacters
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RationalPlaceValuations

/-!
# A quotient radical with linear gcd-th power

For `z^N=c y(1-y^(b+1))^R`, put `δ=gcd(N,R)`. Dividing matched
powers gives `u=z^(N/δ)/(1-y^(b+1))^(R/δ)` with `u^δ=c y`.
Consequently `u` has valuation one above every nonzero rational base
point. Its residue equation controls branch splitting and also
exhibits a rational intermediate field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable {K : Type*} [Field K] (c : Kˣ) (b R n : ℕ)

/-- The nonlinear branch factor is a nonzero polynomial. -/
theorem kummerBranchFactor_ne_zero : (1 - X ^ (b + 1) : K[X]) ≠ 0 := by
  intro h
  have h' : (X ^ (b + 1) - C (1 : K)) = 0 := by
    rw [map_one]
    exact sub_eq_zero.mpr (sub_eq_zero.mp h).symm
  exact (monic_X_pow_sub_C 1 (Nat.succ_ne_zero b)).ne_zero h'

/-- A quotient of radical powers whose gcd-th power is the linear factor `c y`. -/
def kummerBranchUnitRoot : KummerBranchField c b R n :=
  AdjoinRoot.root (kummerBranchFieldPolynomial c b R n) ^ ((n + 1) / Nat.gcd (n + 1) R) /
    (algebraMap K[X] (KummerBranchField c b R n) (1 - X ^ (b + 1))) ^
      (R / Nat.gcd (n + 1) R)

/-- The nonlinear branch factor cancels exactly in the gcd-th power. -/
theorem kummerBranchUnitRoot_pow :
    kummerBranchUnitRoot c b R n ^ Nat.gcd (n + 1) R =
      algebraMap K (KummerBranchField c b R n) c *
        algebraMap K[X] (KummerBranchField c b R n) X := by
  let L := KummerBranchField c b R n
  have hinj : Function.Injective (algebraMap K[X] L) := by
    rw [IsScalarTower.algebraMap_eq K[X] (FractionRing K[X]) L]
    exact (algebraMap (FractionRing K[X]) L).injective.comp (IsFractionRing.injective K[X] _)
  have ht : algebraMap K[X] L (1 - X ^ (b + 1)) ≠ 0 :=
    fun h => kummerBranchFactor_ne_zero (K := K) b (hinj (h.trans (map_zero _).symm))
  rw [kummerBranchUnitRoot, div_pow, ← pow_mul, ← pow_mul,
    Nat.div_mul_cancel (Nat.gcd_dvd_left (n + 1) R),
    Nat.div_mul_cancel (Nat.gcd_dvd_right (n + 1) R), kummerBranchField_root_pow,
    ← IsScalarTower.algebraMap_apply, kummerBranch, map_mul, map_mul, map_pow]
  rw [mul_div_cancel_right₀ _ (pow_ne_zero R ht)]
  congr 1

/-- A polynomial nonzero at a rational base point has value one above that point. -/
theorem squareKummer_valuation_of_eval_ne_zero
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)
    (a : SquareConstantField p s) (f : (SquareConstantField p s)[X]) (hf : f.eval a ≠ 0)
    (w : IsDedekindDomain.HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    w.valuation (SquareKummerField p s c b R)
      (algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) f) = 1 := by
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C a)
  letI : w.asIdeal.LiesOver v.asIdeal := by
    change w.asIdeal.LiesOver (Ideal.span {X - C a})
    infer_instance
  have hf0 : f ≠ 0 := by
    intro h
    exact hf (by rw [h, eval_zero])
  rw [IsScalarTower.algebraMap_apply (SquareConstantField p s)[X]
    (FractionRing (SquareConstantField p s)[X]) (SquareKummerField p s c b R),
    ← IsDedekindDomain.HeightOneSpectrum.valuation_liesOver _ v w,
    polynomial_linearPlace_valuation a f hf0, rootMultiplicity_eq_zero hf,
    Nat.cast_zero, neg_zero, WithZero.exp_zero, one_pow]

/-- The quotient radical is a valuation unit above every nonzero rational base point. -/
theorem squareKummerBranchUnitRoot_valuation_one
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)
    (a : SquareConstantField p s) (ha : a ≠ 0)
    (w : IsDedekindDomain.HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    w.valuation (SquareKummerField p s c b R)
      (kummerBranchUnitRoot c b R (p ^ (s + 1))) = 1 := by
  let L := SquareKummerField p s c b R
  let δ := Nat.gcd (p ^ (s + 1) + 1) R
  have hδ : 0 < δ := Nat.gcd_pos_of_pos_left R (Nat.succ_pos _)
  have hp := congrArg (w.valuation L) (kummerBranchUnitRoot_pow c b R (p ^ (s + 1)))
  rw [map_pow, map_mul, heightOne_valuation_constant w _ (Units.ne_zero c),
    squareKummer_valuation_of_eval_ne_zero p s c b R a X (by simpa only [eval_X] using ha) w,
    one_mul] at hp
  have h := valuation_balanced_radical (w.valuation L) (z := kummerBranchUnitRoot c b R (p ^ (s + 1)))
    (t := 1) (N := δ) (m := 0) hδ (dvd_refl δ) (dvd_zero δ)
    (by rw [map_one]; exact one_ne_zero) (by simpa only [pow_zero] using hp)
  simpa only [Nat.div_self hδ, Nat.zero_div, pow_one, pow_zero, div_one] using h

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.SquareKummerExtensionRamification

/-!
# Normalized coordinate orders over enlarged constants

The linear base parameter has order equal to the ramification index.
At a simple branch root, the radical equation and total ramification
make the canonical radical an actual normalized uniformizer.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
    (E : Type*) [Field E] [Algebra (SquareConstantField p s) E]
    (c : Eˣ) (b R : ℕ)
local notation "N" => p ^ (s + 1) + 1
local notation "L" => SquareKummerExtensionField p s E c b R
local notation "B" => SquareKummerExtensionNormalization p s E c b R
local notation "F" => FractionRing E[X]

/-- The linear base parameter has normalized order equal to its actual ramification index. -/
theorem squareKummerExtension_valuation_linear (x : E) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver (Ideal.span {X - C x})] :
    w.valuation L (algebraMap E[X] L (X - C x)) =
      WithZero.exp (-((Ideal.span {X - C x}).ramificationIdx' w.asIdeal : ℤ)) := by
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C x)
  letI : w.asIdeal.LiesOver v.asIdeal := by
    change w.asIdeal.LiesOver (Ideal.span {X - C x})
    infer_instance
  have hv : v.valuation F (algebraMap E[X] F (X - C x)) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_singleton v (monic_X_sub_C x).ne_zero rfl
  have h := HeightOneSpectrum.valuation_liesOver L v w (algebraMap E[X] F (X - C x))
  rw [hv, ← IsScalarTower.algebraMap_apply, ← WithZero.exp_nsmul,
    nsmul_eq_mul, mul_neg_one] at h
  exact h.symm

variable [PerfectField E]

/-- Above every simple branch root, the canonical radical is a normalized uniformizer. -/
theorem squareKummerExtension_valuation_root_simple
    (x : E) (hx : (kummerBranch c b R).rootMultiplicity x = 1)
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver (Ideal.span {X - C x})] :
    w.valuation L (AdjoinRoot.root (kummerBranchFieldPolynomial c b R (p ^ (s + 1)))) =
      WithZero.exp (-1 : ℤ) := by
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C x)
  let z : L := AdjoinRoot.root (kummerBranchFieldPolynomial c b R (p ^ (s + 1)))
  letI : w.asIdeal.LiesOver v.asIdeal := by
    change w.asIdeal.LiesOver (Ideal.span {X - C x})
    infer_instance
  have hf : kummerBranch c b R ≠ 0 := by
    intro h
    have hc := congrArg (fun f : E[X] => f.coeff 1) h
    rw [kummerBranch_coeff_one, coeff_zero] at hc
    exact c.ne_zero hc
  have hv : v.valuation F (algebraMap E[X] F (kummerBranch c b R)) = WithZero.exp (-1 : ℤ) := by
    rw [polynomial_linearPlace_valuation x _ hf, hx, Nat.cast_one]
  have he : (Ideal.span {X - C x}).ramificationIdx' w.asIdeal = N := by
    rw [squareKummerExtension_rationalPlace_ramification, hx, Nat.gcd_one_right, Nat.div_one]
  have h := congrArg (w.valuation L) (kummerBranchField_root_pow c b R (p ^ (s + 1)))
  rw [map_pow, ← HeightOneSpectrum.valuation_liesOver L v w, hv] at h
  change w.valuation L z ^ N = WithZero.exp (-1 : ℤ) ^
    (Ideal.span {X - C x}).ramificationIdx' w.asIdeal at h
  rw [he] at h
  have hz0 : w.valuation L z ≠ 0 := by
    intro hz
    rw [hz, zero_pow (Nat.succ_ne_zero _)] at h
    exact (pow_ne_zero _ WithZero.exp_ne_zero) h.symm
  have hl := congrArg WithZero.log h
  simp only [WithZero.log_pow, WithZero.log_exp, nsmul_eq_mul] at hl
  have hlog := mul_left_cancel₀ (show (N : ℤ) ≠ 0 by
    exact_mod_cast Nat.succ_ne_zero (p ^ (s + 1))) hl
  change w.valuation L z = _
  rw [← WithZero.exp_log hz0, hlog]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointExtensionInfinityPlace

/-!
# Actual pole orders after extension of constants

Transporting the normalized infinity valuation to the original
three-point field gives pole order `M` for the coordinate and `q^r`
for the radical. The calculation uses total ramification and the
literal radical equation, without a genus or point-count assumption.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
    (E : Type*) [Field E]
    [Algebra (SquareConstantField p (kummerSquareIndex d n)) E] (η : Eˣ)
local notation "q" => p ^ (d + 1)
local notation "a" => (q - 1) * kummerExponent q r
local notation "c" => (η⁻¹) ^ a
local notation "M" => primePowerKummerCyclicDegree p d n
local notation "L" => PrimePowerThreePointExtensionField p d n E c a
local notation "L∞" => PrimePowerThreePointExtensionInfinityField p d n E c a
local notation "B∞" => PrimePowerThreePointExtensionInfinityNormalization p d n E c a

local instance infinityOrderPolynomialTorsionFree : Module.IsTorsionFree E[X] L∞ :=
  kummerInfinityField_torsionFree c 0 a (M - 1)

local instance infinityOrderNormalizationTorsionFree : Module.IsTorsionFree E[X] B∞ :=
  inferInstanceAs (Module.IsTorsionFree E[X] (integralClosure E[X] L∞))

local instance infinityOrderNormalizationAlgebra : Algebra B∞ L∞ :=
  inferInstanceAs (Algebra (integralClosure E[X] L∞) L∞)

local instance infinityOrderNormalizationFractionRing : IsFractionRing B∞ L∞ :=
  primePowerThreePointExtensionInfinityNormalization_fractionRing p d n E c a

/-- The actual infinity valuation transported to the fixed-degree three-point field. -/
def primePowerKummerExtensionInfinityValuation : Valuation L (WithZero (Multiplicative ℤ)) :=
  ((primePowerKummerExtensionInfinityPlace p d n r E η).valuation L∞).comap
    (kummerInfinityFieldEquiv c 0 a (M - 1)).toRingHom

private theorem reciprocal_coordinate_valuation :
    (primePowerKummerExtensionInfinityPlace p d n r E η).valuation L∞
      (algebraMap E[X] L∞ X) = WithZero.exp (-(M : ℤ)) := by
  let v := kummerInfinityBasePlace (K := E)
  let w := primePowerKummerExtensionInfinityPlace p d n r E η
  letI : w.asIdeal.LiesOver v.asIdeal := by
    change w.asIdeal.LiesOver (Ideal.span {(X : E[X])})
    infer_instance
  have h := HeightOneSpectrum.valuation_liesOver L∞ v w
    (algebraMap E[X] (FractionRing E[X]) X)
  rw [kummerInfinityBasePlace_coordinate, ← IsScalarTower.algebraMap_apply] at h
  change WithZero.exp (-1 : ℤ) ^ (Ideal.span {(X : E[X])}).ramificationIdx' w.asIdeal = _ at h
  rw [primePowerKummerExtensionInfinityPlace_ramification,
    ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg_one] at h
  exact h.symm

/-- The three-point coordinate has pole order equal to the unchanged covering degree. -/
theorem primePowerKummerExtensionInfinityValuation_coordinate :
    primePowerKummerExtensionInfinityValuation p d n r E η (algebraMap E[X] L X) =
      WithZero.exp (M : ℤ) := by
  change (primePowerKummerExtensionInfinityPlace p d n r E η).valuation L∞
    (kummerInfinityFieldEquiv c 0 a (M - 1) (algebraMap E[X] L X)) = _
  rw [kummerInfinityFieldEquiv_coordinate, map_inv₀, reciprocal_coordinate_valuation,
    ← WithZero.exp_neg, neg_neg]

/-- The three-point radical has prime-power pole order over every extension of constants. -/
theorem primePowerKummerExtensionInfinityValuation_root :
    primePowerKummerExtensionInfinityValuation p d n r E η
      (AdjoinRoot.root (kummerBranchFieldPolynomial c 0 a (M - 1))) =
        WithZero.exp ((q ^ r : ℕ) : ℤ) := by
  let v := kummerInfinityBasePlace (K := E)
  let w := primePowerKummerExtensionInfinityPlace p d n r E η
  let z : L∞ := AdjoinRoot.root (kummerInfinityPolynomial c 0 a (M - 1))
  letI : w.asIdeal.LiesOver v.asIdeal := by
    change w.asIdeal.LiesOver (Ideal.span {(X : E[X])})
    infer_instance
  have h := congrArg (w.valuation L∞) (kummerInfinityField_root_pow c 0 a (M - 1))
  rw [map_pow, ← HeightOneSpectrum.valuation_liesOver L∞ v w,
    kummerInfinityBasePlace_branch, Nat.zero_add, Nat.one_mul] at h
  change w.valuation L∞ z ^ (M - 1 + 1) = WithZero.exp ((1 + a : ℕ) : ℤ) ^
    (Ideal.span {(X : E[X])}).ramificationIdx' w.asIdeal at h
  have h' : w.valuation L∞ z ^ M = WithZero.exp ((q ^ r : ℕ) : ℤ) ^ M := by
    calc
      w.valuation L∞ z ^ M = w.valuation L∞ z ^ (M - 1 + 1) :=
        congrArg (fun k : ℕ => w.valuation L∞ z ^ k)
          (primePowerThreePointExtension_index p d n).symm
      _ = WithZero.exp ((1 + a : ℕ) : ℤ) ^
          (Ideal.span {(X : E[X])}).ramificationIdx' w.asIdeal := h
      _ = WithZero.exp ((q ^ r : ℕ) : ℤ) ^ M := by
        rw [primePowerKummerExtensionInfinityPlace_ramification]
        exact congrArg (fun k : ℕ => WithZero.exp (k : ℤ) ^ M)
          (primePowerThreePointExponent_poleDegree p d r)
  have hM : 0 < M := primePowerKummerCyclicDegree_pos p d n
  have hz0 : w.valuation L∞ z ≠ 0 := by
    intro hz
    rw [hz, zero_pow (Nat.ne_of_gt hM)] at h'
    exact (pow_ne_zero _ WithZero.exp_ne_zero) h'.symm
  have hl := congrArg WithZero.log h'
  simp only [WithZero.log_pow, WithZero.log_exp, nsmul_eq_mul] at hl
  have hlog := mul_left_cancel₀ (show (M : ℤ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hM) hl
  change w.valuation L∞ (kummerInfinityFieldEquiv c 0 a (M - 1)
    (AdjoinRoot.root (kummerBranchFieldPolynomial c 0 a (M - 1)))) = _
  rw [kummerInfinityFieldEquiv_root]
  change w.valuation L∞ z = _
  rw [← WithZero.exp_log hz0, hlog]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

import GaloisForLFunctions.HTGeometry.PrimeDirichletDifferentialField
import Mathlib.RingTheory.Derivation.Lie

/-!
# Differential stability of the finite-prime coefficient field

The rotated logarithmic derivation does not create new active prime directions.  The mechanism is
the exact Euler commutator

`[partial_p, D] = i log(p) partial_p`.

We prove this first on arithmetic functions and then on their fraction field.  It follows that the
intrinsic finite-prime coefficient field is stable under the ambient derivation and therefore is
itself a differential field.  This supplies the missing differential-field structure used by the
prime-radial fusion correspondence.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction
open scoped Differential

noncomputable section

local instance importedArithmeticFunctionIntAlgebra :
    Algebra ℤ (ArithmeticFunction ℂ) :=
  GaloisForLFunctions.HTGeometry.arithmeticFunctionIntAlgebra

local instance importedArithmeticFunctionFractionIntAlgebra :
    Algebra ℤ arithmeticFunctionFractionField :=
  GaloisForLFunctions.HTGeometry.arithmeticFunctionFractionIntAlgebra

/-! ## The Euler commutator -/

/-- Coefficient form of the Euler commutator on the Dirichlet-convolution algebra. -/
theorem primeDeriv_rotatedLogArithmetic_commutator
    (p : Nat.Primes) (f : ArithmeticFunction ℂ) :
    primeDeriv p.1 (Complex.I • logWeight f) -
        Complex.I • logWeight (primeDeriv p.1 f) =
      (Complex.I * (Real.log p.1 : ℂ)) • primeDeriv p.1 f := by
  ext n
  simp only [sub_eq_add_neg, ArithmeticFunction.add_apply,
    ArithmeticFunction.neg_apply, primeDeriv_apply,
    ArithmeticFunction.smul_map, logWeight_apply, smul_eq_mul]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hpR : (p.1 : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
    have hlog : Real.log ((n * p.1 : Nat) : ℝ) =
        Real.log n + Real.log p.1 := by
      calc
        Real.log ((n * p.1 : Nat) : ℝ) =
            Real.log ((n : ℝ) * (p.1 : ℝ)) := by rw [Nat.cast_mul]
        _ = Real.log n + Real.log p.1 := Real.log_mul hnR hpR
    rw [hlog]
    push_cast
    ring

/-- The prime derivation and the rotated logarithmic derivation satisfy an exact Euler
commutator on arithmetic functions. -/
theorem primeArithmetic_rotatedLog_commutator
    (p : Nat.Primes) :
    ⁅primeArithmeticDerivation p.1 p.2,
        rotatedLogArithmeticDerivationComplex⁆ =
      algebraMap ℂ (ArithmeticFunction ℂ)
          (Complex.I * (Real.log p.1 : ℂ)) •
        primeArithmeticDerivation p.1 p.2 := by
  apply Derivation.ext
  intro f
  rw [Derivation.commutator_apply]
  change primeDeriv p.1 (Complex.I • logWeight f) -
      Complex.I • logWeight (primeDeriv p.1 f) = _
  simpa only [Derivation.smul_apply, Algebra.smul_def] using!
    primeDeriv_rotatedLogArithmetic_commutator p f

/-- Complex-linear quotient-rule extension of the rotated logarithmic derivation.  Its
restriction to the integer base is the ambient differential derivation. -/
def rotatedLogFractionDerivationComplex :
    Derivation ℂ arithmeticFunctionFractionField arithmeticFunctionFractionField :=
  fractionRingDerivation
    ((Algebra.linearMap (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField).compDer
        rotatedLogArithmeticDerivationComplex)

@[simp]
theorem rotatedLogFractionDerivationComplex_algebraMap
    (f : ArithmeticFunction ℂ) :
    rotatedLogFractionDerivationComplex
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f) =
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (Complex.I • logWeight f) := by
  exact fractionRingDerivation_algebraMap
    ((Algebra.linearMap (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField).compDer
        rotatedLogArithmeticDerivationComplex) f

theorem rotatedLogFractionDerivationComplex_restrictScalars :
    rotatedLogFractionDerivationComplex.restrictScalars ℤ =
      rotatedLogFractionDerivation := by
  apply GaloisForLFunctions.fractionRing_derivation_ext
    (A := ArithmeticFunction ℂ)
  intro f
  rw [Derivation.restrictScalars_apply,
    rotatedLogFractionDerivationComplex_algebraMap,
    rotatedLogFractionDerivation_algebraMap]

theorem rotatedLogFractionDerivationComplex_apply
    (x : arithmeticFunctionFractionField) :
    rotatedLogFractionDerivationComplex x = rotatedLogFractionDerivation x := by
  exact DFunLike.congr_fun rotatedLogFractionDerivationComplex_restrictScalars x

/-- **Fraction-field Euler commutator.**  Prime-coordinate differentiation and the ambient
rotated logarithmic derivation obey the same weight relation after quotient-rule extension. -/
theorem primeFraction_rotatedLog_commutator
    (p : Nat.Primes) :
    ⁅primeFractionDerivation p, rotatedLogFractionDerivationComplex⁆ =
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (algebraMap ℂ (ArithmeticFunction ℂ)
            (Complex.I * (Real.log p.1 : ℂ))) •
        primeFractionDerivation p := by
  apply GaloisForLFunctions.fractionRing_derivation_ext
    (A := ArithmeticFunction ℂ)
  intro f
  rw [Derivation.commutator_apply]
  simp only [Derivation.smul_apply,
    rotatedLogFractionDerivationComplex_algebraMap,
    primeFractionDerivation_algebraMap, Algebra.smul_def]
  simpa [Algebra.smul_def] using congrArg
    (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField)
    (primeDeriv_rotatedLogArithmetic_commutator p f)

/-- A prime direction annihilating a fraction also annihilates its rotated logarithmic
derivative. -/
theorem primeFractionDerivation_rotatedLog_eq_zero_of_eq_zero
    (p : Nat.Primes) (x : arithmeticFunctionFractionField)
    (hx : primeFractionDerivation p x = 0) :
    primeFractionDerivation p (rotatedLogFractionDerivation x) = 0 := by
  rw [← rotatedLogFractionDerivationComplex_apply]
  have hcomm := Derivation.congr_fun
    (primeFraction_rotatedLog_commutator p) x
  rw [Derivation.commutator_apply] at hcomm
  simp only [Derivation.smul_apply, Algebra.smul_def] at hcomm
  rw [hx, map_zero rotatedLogFractionDerivationComplex, mul_zero, sub_zero] at hcomm
  exact hcomm

/-- The rotated logarithmic derivation can only remove active primes; it cannot create one. -/
theorem finitePrimeActivity_rotatedLogFractionDerivation_subset
    (x : arithmeticFunctionFractionField) :
    finitePrimeActivity (rotatedLogFractionDerivation x) ⊆ finitePrimeActivity x := by
  intro p hp
  change primeFractionDerivation p (rotatedLogFractionDerivation x) ≠ 0 at hp
  change primeFractionDerivation p x ≠ 0
  intro hx
  exact hp (primeFractionDerivation_rotatedLog_eq_zero_of_eq_zero p x hx)

/-- The intrinsic finite-prime coefficient field is stable under the ambient rotated logarithmic
derivation. -/
theorem rotatedLogFractionDerivation_mem_finitePrimeCoefficientField
    {x : arithmeticFunctionFractionField}
    (hx : x ∈ finitePrimeCoefficientField) :
    rotatedLogFractionDerivation x ∈ finitePrimeCoefficientField := by
  rw [mem_finitePrimeCoefficientField_iff] at hx ⊢
  exact hx.subset (finitePrimeActivity_rotatedLogFractionDerivation_subset x)

/-! ## Differential-field structure -/

/-- The ambient rotated logarithmic derivation restricted to the intrinsic finite-prime field. -/
noncomputable instance finitePrimeCoefficientFieldDifferential :
    Differential finitePrimeCoefficientField where
  deriv :=
    { toLinearMap :=
        { toFun := fun x =>
            ⟨rotatedLogFractionDerivation x.1,
              rotatedLogFractionDerivation_mem_finitePrimeCoefficientField x.2⟩
          map_add' := fun x y => Subtype.ext (map_add rotatedLogFractionDerivation x.1 y.1)
          map_smul' := fun n x =>
            Subtype.ext (rotatedLogFractionDerivation.map_smul n x.1) }
      map_one_eq_zero' := Subtype.ext rotatedLogFractionDerivation.map_one_eq_zero
      leibniz' := fun x y =>
        Subtype.ext (rotatedLogFractionDerivation.leibniz x.1 y.1) }

@[simp]
theorem finitePrimeCoefficientField_deriv_coe
    (x : finitePrimeCoefficientField) :
    ((x′ : finitePrimeCoefficientField) : arithmeticFunctionFractionField) =
      rotatedLogFractionDerivation x.1 :=
  rfl

/-- Inclusion of the finite-prime coefficient field into the arithmetic fraction field commutes
with the derivation. -/
instance finitePrimeCoefficientFieldDifferentialAlgebra :
    DifferentialAlgebra finitePrimeCoefficientField arithmeticFunctionFractionField where
  deriv_algebraMap x := by
    rfl

end

end GaloisForLFunctions.HTGeometry

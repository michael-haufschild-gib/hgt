import GaloisForLFunctions.HTGeometry.GammaPoleUnitRelativeFreeness

/-!
# Joint relative freeness of the Gamma pole scale and actual unit derivatives

Moving-pole descent requires coefficients in the rational pole-position field `ℂ(n)`.  This is
strictly stronger than the existing complex-base theorem: the pole label itself may participate in
every candidate relation.

The proof first transports the scale--harmonic relative freeness law through a weighted affine
value relation to the exact logarithmic derivatives.  A head-preserving lift of the scalar-extended
Bell automorphism then transports it to the actual regular-unit Taylor coefficients.  Passing from
finite prefixes to the countable family and applying a nonzero factorial diagonal yields joint
algebraic independence of the reciprocal factorial scale and every actual positive analytic
derivative of the Gamma regular units over `ℂ(n)`.

All substitutions are proved injective.  The analytic endpoint is an exact Taylor-coefficient value
reflection and uses no asymptotic or numerical input.
-/

open MvPolynomial Polynomial

namespace GaloisForLFunctions

noncomputable section

local instance jointRelativeNatGermAlgebra :
    Algebra GammaPoleRationalBase NatGerm := ratNatEval.toAlgebra

local instance jointRelativeComplexNatGermAlgebra :
    Algebra ℂ NatGerm := complexNatGerm.toAlgebra

def gammaPoleScaleAndLogDerivativeRationalFamily
    (m : ℕ) : Option (Fin m) → NatGerm
  | none => reciprocalSignedFactorialGerm
  | some j => gammaPoleLogDerivativeGerm (j : ℕ)

def gammaPoleScaleAndLogDerivativeRationalEval (m : ℕ) :
    MvPolynomial (Option (Fin m)) GammaPoleRationalBase →+* NatGerm :=
  MvPolynomial.eval₂Hom ratNatEval
    (gammaPoleScaleAndLogDerivativeRationalFamily m)

theorem gammaPoleScaleAndLogDerivativeRationalEval_eq_comp (m : ℕ) :
    gammaPoleScaleAndLogDerivativeRationalEval m =
      (gammaPoleScaleAndHarmonicEval m).comp
        (weightedScaleAffineMap m
          (fun j => gammaPoleLogDerivativeRationalSlope (j : ℕ))
          (fun j => gammaPoleLogDerivativeRationalConstant (j : ℕ))).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [gammaPoleScaleAndLogDerivativeRationalEval,
      gammaPoleScaleAndHarmonicEval]
  · intro o
    rcases o with (_ | j)
    · simp [gammaPoleScaleAndLogDerivativeRationalEval,
        gammaPoleScaleAndLogDerivativeRationalFamily,
        gammaPoleScaleAndHarmonicEval,
        gammaPoleScaleAndHarmonicFamily,
        weightedScaleAffineMap_none]
    · have hbase (c : ℂ) :
          algebraMap ℂ NatGerm c = ratNatEval (RatFunc.C c) := rfl
      rw [RingHom.comp_apply]
      change gammaPoleScaleAndLogDerivativeRationalEval m
          (MvPolynomial.X (some j)) =
        gammaPoleScaleAndHarmonicEval m
          (weightedScaleAffineMap m
            (fun j => gammaPoleLogDerivativeRationalSlope (j : ℕ))
            (fun j => gammaPoleLogDerivativeRationalConstant (j : ℕ))
            (MvPolynomial.X (some j)))
      rw [weightedScaleAffineMap_some]
      simp [gammaPoleScaleAndLogDerivativeRationalEval,
        gammaPoleScaleAndLogDerivativeRationalFamily,
        gammaPoleScaleAndHarmonicEval,
        gammaPoleScaleAndHarmonicFamily,
        gammaPoleLogDerivativeGerm,
        gammaPoleLogDerivativeRationalSlope,
        gammaPoleLogDerivativeRationalConstant, hbase]

theorem gammaPoleScaleAndLogDerivativeRationalEval_injective (m : ℕ) :
    Function.Injective (gammaPoleScaleAndLogDerivativeRationalEval m) := by
  rw [gammaPoleScaleAndLogDerivativeRationalEval_eq_comp]
  exact (gammaPoleScaleAndHarmonicEval_injective m).comp
    (weightedScaleAffineMap_injective m fun _j => by
      simp [gammaPoleLogDerivativeRationalSlope])

theorem gammaPoleScaleAndLogDerivativeRationalEval_rename_some
    (m : ℕ) (P : MvPolynomial (Fin m) GammaPoleRationalBase) :
    gammaPoleScaleAndLogDerivativeRationalEval m
        (MvPolynomial.rename some P) =
      gammaPoleLogDerivativeRationalEval m P := by
  simp [gammaPoleScaleAndLogDerivativeRationalEval,
    gammaPoleScaleAndLogDerivativeRationalFamily,
    gammaPoleLogDerivativeRationalEval,
    MvPolynomial.eval₂_rename, Function.comp_def]

def gammaPoleScaleAndUnitPositiveCoefficientRationalFamilyFin (n : ℕ) :
    Option (Fin (n + 1)) → NatGerm
  | none => reciprocalSignedFactorialGerm
  | some j => gammaPoleUnitPositiveCoefficientGerm (j : ℕ)

def gammaPoleScaleAndUnitPositiveCoefficientRationalEvalFin (n : ℕ) :
    MvPolynomial (Option (Fin (n + 1))) GammaPoleRationalBase →+* NatGerm :=
  MvPolynomial.eval₂Hom ratNatEval
    (gammaPoleScaleAndUnitPositiveCoefficientRationalFamilyFin n)

theorem gammaPoleScaleAndUnitPositiveCoefficientRationalEvalFin_eq_comp (n : ℕ) :
    gammaPoleScaleAndUnitPositiveCoefficientRationalEvalFin n =
      (gammaPoleScaleAndLogDerivativeRationalEval (n + 1)).comp
        (optionHeadLiftAlgHom
          (gammaPoleUnitPositiveBellRationalMap n)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [gammaPoleScaleAndUnitPositiveCoefficientRationalEvalFin,
      gammaPoleScaleAndLogDerivativeRationalEval]
  · intro o
    rcases o with (_ | j)
    · simp [gammaPoleScaleAndUnitPositiveCoefficientRationalEvalFin,
        gammaPoleScaleAndUnitPositiveCoefficientRationalFamilyFin,
        gammaPoleScaleAndLogDerivativeRationalEval,
        gammaPoleScaleAndLogDerivativeRationalFamily,
        optionHeadLiftAlgHom_none]
    · rw [RingHom.comp_apply]
      change gammaPoleScaleAndUnitPositiveCoefficientRationalEvalFin n
          (MvPolynomial.X (some j)) =
        gammaPoleScaleAndLogDerivativeRationalEval (n + 1)
          (optionHeadLiftAlgHom (gammaPoleUnitPositiveBellRationalMap n)
            (MvPolynomial.X (some j)))
      rw [optionHeadLiftAlgHom_some,
        gammaPoleScaleAndLogDerivativeRationalEval_rename_some]
      have h := RingHom.congr_fun
        (gammaPoleUnitPositiveCoefficientRationalEvalFin_eq_comp n)
        (MvPolynomial.X j)
      simpa [gammaPoleScaleAndUnitPositiveCoefficientRationalEvalFin,
        gammaPoleScaleAndUnitPositiveCoefficientRationalFamilyFin,
        gammaPoleUnitPositiveCoefficientRationalEvalFin] using h

theorem gammaPoleScaleAndUnitPositiveCoefficientRationalEvalFin_injective (n : ℕ) :
    Function.Injective
      (gammaPoleScaleAndUnitPositiveCoefficientRationalEvalFin n) := by
  rw [gammaPoleScaleAndUnitPositiveCoefficientRationalEvalFin_eq_comp]
  exact (gammaPoleScaleAndLogDerivativeRationalEval_injective (n + 1)).comp
    (optionHeadLiftAlgHom_injective
      (gammaPoleUnitPositiveBellRationalMap_injective n))

theorem algebraicIndependent_gammaPoleScaleAndUnitPositiveCoefficient_over_ratFunc_fin
    (n : ℕ) :
    AlgebraicIndependent GammaPoleRationalBase
      (gammaPoleScaleAndUnitPositiveCoefficientRationalFamilyFin n) := by
  rw [algebraicIndependent_iff_injective_aeval]
  simpa [gammaPoleScaleAndUnitPositiveCoefficientRationalEvalFin,
    MvPolynomial.aeval_def] using!
      gammaPoleScaleAndUnitPositiveCoefficientRationalEvalFin_injective n

theorem algebraicIndependent_gammaPoleScaleAndUnitPositiveCoefficient_over_ratFunc :
    AlgebraicIndependent GammaPoleRationalBase
      gammaPoleScaleAndUnitPositiveCoefficientFamily := by
  apply algebraicIndependent_optionNat_of_prefix
  intro n
  have h :=
    algebraicIndependent_gammaPoleScaleAndUnitPositiveCoefficient_over_ratFunc_fin n
  have hfamily :
      gammaPoleScaleAndUnitPositiveCoefficientFamily ∘ optionFinInclude n =
        gammaPoleScaleAndUnitPositiveCoefficientRationalFamilyFin n := by
    funext o
    rcases o with (_ | j) <;> rfl
  rwa [hfamily]

def gammaPoleScaleAndUnitPositiveCoefficientRationalEval :
    MvPolynomial (Option ℕ) GammaPoleRationalBase →+* NatGerm :=
  MvPolynomial.eval₂Hom ratNatEval
    gammaPoleScaleAndUnitPositiveCoefficientFamily

theorem gammaPoleScaleAndUnitPositiveCoefficientRationalEval_injective :
    Function.Injective gammaPoleScaleAndUnitPositiveCoefficientRationalEval := by
  have h := algebraicIndependent_iff_injective_aeval.mp
    algebraicIndependent_gammaPoleScaleAndUnitPositiveCoefficient_over_ratFunc
  simpa [gammaPoleScaleAndUnitPositiveCoefficientRationalEval,
    MvPolynomial.aeval_def] using! h

def gammaPoleUnitDerivativeRationalScale : Option ℕ → GammaPoleRationalBase
  | none => 1
  | some k => RatFunc.C (((k + 1).factorial : ℂ))

theorem gammaPoleUnitDerivativeRationalScale_ne_zero (o : Option ℕ) :
    gammaPoleUnitDerivativeRationalScale o ≠ 0 := by
  rcases o with (_ | k)
  · exact one_ne_zero
  · have hf : (((k + 1).factorial : ℂ)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k + 1))
    simpa [gammaPoleUnitDerivativeRationalScale] using
      RatFunc.C_injective.ne hf

def gammaPoleScaleAndUnitDerivativeRationalFamily : Option ℕ → NatGerm
  | none => reciprocalSignedFactorialGerm
  | some k => algebraMap ℂ NatGerm (((k + 1).factorial : ℂ)) *
      gammaPoleUnitPositiveCoefficientGerm k

def gammaPoleUnitPositiveDerivativeRationalGerm (k : ℕ) : NatGerm :=
  fun N : ℕ => iteratedDeriv (k + 1) (gammaPoleRegularUnit (N - 1)) 0

theorem gammaPoleScaleAndUnitDerivativeRationalFamily_some_eq_actual (k : ℕ) :
    gammaPoleScaleAndUnitDerivativeRationalFamily (some k) =
      gammaPoleUnitPositiveDerivativeRationalGerm k := by
  rw [gammaPoleScaleAndUnitDerivativeRationalFamily,
    gammaPoleUnitPositiveCoefficientGerm_eq_actualTaylorCoefficient]
  change complexNatGerm (((k + 1).factorial : ℂ)) *
      (↑(fun N : ℕ => (((k + 1).factorial : ℂ)⁻¹) *
        iteratedDeriv (k + 1) (gammaPoleRegularUnit (N - 1)) 0) : NatGerm) =
      (↑(fun N : ℕ =>
        iteratedDeriv (k + 1) (gammaPoleRegularUnit (N - 1)) 0) : NatGerm)
  rw [complexNatGerm_eq_constGerm, ← Filter.Germ.coe_mul, Filter.Germ.coe_eq]
  exact Filter.Eventually.of_forall fun N => by
    dsimp [gammaPoleUnitPositiveDerivativeRationalGerm]
    have hf : (((k + 1).factorial : ℂ)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k + 1))
    rw [← mul_assoc, mul_inv_cancel₀ hf, one_mul]

def gammaPoleScaleAndUnitDerivativeRationalEval :
    MvPolynomial (Option ℕ) GammaPoleRationalBase →+* NatGerm :=
  MvPolynomial.eval₂Hom ratNatEval
    gammaPoleScaleAndUnitDerivativeRationalFamily

theorem gammaPoleScaleAndUnitDerivativeRationalEval_eq_comp :
    gammaPoleScaleAndUnitDerivativeRationalEval =
      gammaPoleScaleAndUnitPositiveCoefficientRationalEval.comp
        (mvPolynomialDiagonalScaleRing
          gammaPoleUnitDerivativeRationalScale).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [gammaPoleScaleAndUnitDerivativeRationalEval,
      gammaPoleScaleAndUnitPositiveCoefficientRationalEval]
  · intro o
    rcases o with (_ | k)
    · simp [gammaPoleScaleAndUnitDerivativeRationalEval,
        gammaPoleScaleAndUnitDerivativeRationalFamily,
        gammaPoleScaleAndUnitPositiveCoefficientRationalEval,
        gammaPoleScaleAndUnitPositiveCoefficientFamily,
        gammaPoleUnitDerivativeRationalScale,
        mvPolynomialDiagonalScaleRing]
    · simp [gammaPoleScaleAndUnitDerivativeRationalEval,
        gammaPoleScaleAndUnitDerivativeRationalFamily,
        gammaPoleScaleAndUnitPositiveCoefficientRationalEval,
        gammaPoleScaleAndUnitPositiveCoefficientFamily,
        gammaPoleUnitDerivativeRationalScale,
        mvPolynomialDiagonalScaleRing]

theorem gammaPoleScaleAndUnitDerivativeRationalEval_injective :
    Function.Injective gammaPoleScaleAndUnitDerivativeRationalEval := by
  rw [gammaPoleScaleAndUnitDerivativeRationalEval_eq_comp]
  exact gammaPoleScaleAndUnitPositiveCoefficientRationalEval_injective.comp
    (mvPolynomialDiagonalScaleRing_injective
      gammaPoleUnitDerivativeRationalScale
      gammaPoleUnitDerivativeRationalScale_ne_zero)

theorem algebraicIndependent_gammaPoleScaleAndUnitDerivative_over_ratFunc :
    AlgebraicIndependent GammaPoleRationalBase
      gammaPoleScaleAndUnitDerivativeRationalFamily := by
  rw [algebraicIndependent_iff_injective_aeval]
  simpa [gammaPoleScaleAndUnitDerivativeRationalEval,
    MvPolynomial.aeval_def] using!
      gammaPoleScaleAndUnitDerivativeRationalEval_injective

def gammaPoleScaleAndActualUnitDerivativeFamily : Option ℕ → NatGerm
  | none => reciprocalSignedFactorialGerm
  | some k => gammaPoleUnitPositiveDerivativeRationalGerm k

theorem gammaPoleScaleAndActualUnitDerivativeFamily_eq :
    gammaPoleScaleAndActualUnitDerivativeFamily =
      gammaPoleScaleAndUnitDerivativeRationalFamily := by
  funext o
  rcases o with (_ | k)
  · rfl
  · exact (gammaPoleScaleAndUnitDerivativeRationalFamily_some_eq_actual k).symm

theorem algebraicIndependent_gammaPoleScaleAndActualUnitDerivative_over_ratFunc :
    AlgebraicIndependent GammaPoleRationalBase
      gammaPoleScaleAndActualUnitDerivativeFamily := by
  rw [gammaPoleScaleAndActualUnitDerivativeFamily_eq]
  exact algebraicIndependent_gammaPoleScaleAndUnitDerivative_over_ratFunc

end

end GaloisForLFunctions

import GaloisForLFunctions.HTGeometry.GammaPoleReciprocalBellGrading
import GaloisForLFunctions.HTGeometry.GammaPoleScaleUnitRelativeFreeness

/-!
# Covariant Gamma pole freeness over the moving-center field

The reciprocal-factorial scale and the Gamma regular-unit derivatives were
already known to be jointly free over the rational pole-position field
`GammaPoleRationalBase = ℂ(N)`.  This file transports that law through formal
unit inversion and the nonzero factorial diagonal.  Thus the scale and every
covariant simple-zero residue remain jointly algebraically independent even
when candidate relations have rational functions of the pole center as
coefficients.

The final Laurent evaluation theorem is the corresponding value reflection:
no finite relation between signed scale powers and covariant residues can be
created by moving-center coefficients.  This is the coefficient-field
interface required by moving-pole principal-part descent.
-/

open MvPolynomial Polynomial LaurentPolynomial

namespace GaloisForLFunctions

noncomputable section

local instance relativeReciprocalNatGermAlgebra :
    Algebra GammaPoleRationalBase NatGerm := ratNatEval.toAlgebra

/-- Formal unit inversion after extending coefficients from `ℂ` to the
rational pole-position field. -/
def universalUnitInverseCoefficientRationalMap :
    MvPolynomial ℕ GammaPoleRationalBase →ₐ[GammaPoleRationalBase]
      MvPolynomial ℕ GammaPoleRationalBase :=
  mvPolynomialAlgHomBaseChange
    (K := GammaPoleRationalBase) universalUnitInverseCoefficientMap

theorem universalUnitInverseCoefficientRationalMap_involutive :
    universalUnitInverseCoefficientRationalMap.comp
        universalUnitInverseCoefficientRationalMap =
      AlgHom.id GammaPoleRationalBase _ := by
  rw [universalUnitInverseCoefficientRationalMap,
    ← mvPolynomialAlgHomBaseChange_comp,
    universalUnitInverseCoefficientMap_involutive,
    mvPolynomialAlgHomBaseChange_id]

theorem universalUnitInverseCoefficientRationalMap_injective :
    Function.Injective universalUnitInverseCoefficientRationalMap := by
  apply Function.LeftInverse.injective
    (g := universalUnitInverseCoefficientRationalMap)
  intro P
  simpa using
    AlgHom.congr_fun universalUnitInverseCoefficientRationalMap_involutive P

@[simp] theorem universalUnitInverseCoefficientRationalMap_X (j : ℕ) :
    universalUnitInverseCoefficientRationalMap (MvPolynomial.X j) =
      MvPolynomial.map (algebraMap ℂ GammaPoleRationalBase)
        (universalUnitInverseCoefficient j) := by
  rw [universalUnitInverseCoefficientRationalMap,
    mvPolynomialAlgHomBaseChange_X]
  simp [universalUnitInverseCoefficientMap]

/-- Rational-base evaluation of the scale and reciprocal regular-unit
coefficients. -/
def gammaPoleScaleAndReciprocalUnitCoefficientRationalEval :
    MvPolynomial (Option ℕ) GammaPoleRationalBase →+* NatGerm :=
  MvPolynomial.eval₂Hom ratNatEval
    gammaPoleScaleAndReciprocalUnitCoefficientFamily

theorem gammaPoleScaleAndReciprocalUnitCoefficientRationalEval_eq_comp :
    gammaPoleScaleAndReciprocalUnitCoefficientRationalEval =
      gammaPoleScaleAndUnitPositiveCoefficientRationalEval.comp
        (optionHeadLiftAlgHom
          universalUnitInverseCoefficientRationalMap).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [gammaPoleScaleAndReciprocalUnitCoefficientRationalEval,
      gammaPoleScaleAndUnitPositiveCoefficientRationalEval]
  · intro o
    rcases o with (_ | j)
    · simp [gammaPoleScaleAndReciprocalUnitCoefficientRationalEval,
        gammaPoleScaleAndReciprocalUnitCoefficientFamily,
        gammaPoleScaleAndUnitPositiveCoefficientRationalEval,
        gammaPoleScaleAndUnitPositiveCoefficientFamily,
        optionHeadLiftAlgHom_none]
    · rw [RingHom.comp_apply]
      simp only [gammaPoleScaleAndReciprocalUnitCoefficientRationalEval,
        MvPolynomial.eval₂Hom_X',
        gammaPoleScaleAndReciprocalUnitCoefficientFamily]
      change gammaPoleReciprocalUnitCoefficientGerm j =
        gammaPoleScaleAndUnitPositiveCoefficientRationalEval
          (optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
            (MvPolynomial.X (some j)))
      rw [optionHeadLiftAlgHom_some,
        universalUnitInverseCoefficientRationalMap_X]
      simp [gammaPoleScaleAndUnitPositiveCoefficientRationalEval,
        gammaPoleScaleAndUnitPositiveCoefficientFamily,
        gammaPoleReciprocalUnitCoefficientGerm,
        unitInverseCoefficientOfCoefficients_eq_aeval,
        MvPolynomial.aeval_def, MvPolynomial.eval₂_rename,
        Function.comp_def]
      have hbase : ratNatEval.comp RatFunc.C = complexNatGerm := rfl
      rw [hbase]
      rfl

theorem gammaPoleScaleAndReciprocalUnitCoefficientRationalEval_injective :
    Function.Injective
      gammaPoleScaleAndReciprocalUnitCoefficientRationalEval := by
  rw [gammaPoleScaleAndReciprocalUnitCoefficientRationalEval_eq_comp]
  exact gammaPoleScaleAndUnitPositiveCoefficientRationalEval_injective.comp
    (optionHeadLiftAlgHom_injective
      universalUnitInverseCoefficientRationalMap_injective)

/-- Formal unit inversion preserves joint relative freeness with the
factorial scale. -/
theorem algebraicIndependent_gammaPoleScaleAndReciprocalUnitCoefficient_over_ratFunc :
    AlgebraicIndependent GammaPoleRationalBase
      gammaPoleScaleAndReciprocalUnitCoefficientFamily := by
  rw [algebraicIndependent_iff_injective_aeval]
  simpa [gammaPoleScaleAndReciprocalUnitCoefficientRationalEval,
    MvPolynomial.aeval_def] using!
      gammaPoleScaleAndReciprocalUnitCoefficientRationalEval_injective

def gammaPoleCovariantResidueRationalScale :
    Option ℕ → GammaPoleRationalBase
  | none => 1
  | some j => RatFunc.C (((j + 2).factorial : ℂ))

theorem gammaPoleCovariantResidueRationalScale_ne_zero (o : Option ℕ) :
    gammaPoleCovariantResidueRationalScale o ≠ 0 := by
  rcases o with (_ | j)
  · exact one_ne_zero
  · have hfactor : (((j + 2).factorial : ℂ)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (j + 2))
    simpa [gammaPoleCovariantResidueRationalScale] using
      RatFunc.C_injective.ne hfactor

/-- Rational-base evaluation of the scale and covariant residues. -/
def gammaPoleScaleAndCovariantResidueRationalEval :
    MvPolynomial (Option ℕ) GammaPoleRationalBase →+* NatGerm :=
  MvPolynomial.eval₂Hom ratNatEval gammaPoleScaleAndCovariantResidueFamily

theorem gammaPoleScaleAndCovariantResidueRationalEval_eq_comp :
    gammaPoleScaleAndCovariantResidueRationalEval =
      gammaPoleScaleAndReciprocalUnitCoefficientRationalEval.comp
        (mvPolynomialDiagonalScaleRing
          gammaPoleCovariantResidueRationalScale).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [gammaPoleScaleAndCovariantResidueRationalEval,
      gammaPoleScaleAndReciprocalUnitCoefficientRationalEval]
  · intro o
    rcases o with (_ | j)
    · simp [gammaPoleScaleAndCovariantResidueRationalEval,
        gammaPoleScaleAndCovariantResidueFamily,
        gammaPoleScaleAndReciprocalUnitCoefficientRationalEval,
        gammaPoleScaleAndReciprocalUnitCoefficientFamily,
        gammaPoleCovariantResidueRationalScale,
        mvPolynomialDiagonalScaleRing]
    · simp [gammaPoleScaleAndCovariantResidueRationalEval,
        gammaPoleScaleAndCovariantResidueFamily,
        gammaPoleScaleAndReciprocalUnitCoefficientRationalEval,
        gammaPoleScaleAndReciprocalUnitCoefficientFamily,
        gammaPoleCovariantResidueRationalScale,
        mvPolynomialDiagonalScaleRing,
        gammaSimpleZeroCovariantResidueGerm_eq]

theorem gammaPoleScaleAndCovariantResidueRationalEval_injective :
    Function.Injective gammaPoleScaleAndCovariantResidueRationalEval := by
  rw [gammaPoleScaleAndCovariantResidueRationalEval_eq_comp]
  exact gammaPoleScaleAndReciprocalUnitCoefficientRationalEval_injective.comp
    (mvPolynomialDiagonalScaleRing_injective
      gammaPoleCovariantResidueRationalScale
      gammaPoleCovariantResidueRationalScale_ne_zero)

/-- The scale and all covariant residues are jointly algebraically
independent over the rational moving-center field. -/
theorem algebraicIndependent_gammaPoleScaleAndCovariantResidue_over_ratFunc :
    AlgebraicIndependent GammaPoleRationalBase
      gammaPoleScaleAndCovariantResidueFamily := by
  rw [algebraicIndependent_iff_injective_aeval]
  simpa [gammaPoleScaleAndCovariantResidueRationalEval,
    MvPolynomial.aeval_def] using!
      gammaPoleScaleAndCovariantResidueRationalEval_injective

def gammaPoleCovariantResidueRationalEval :
    MvPolynomial ℕ GammaPoleRationalBase →+* NatGerm :=
  MvPolynomial.eval₂Hom ratNatEval gammaSimpleZeroCovariantResidueGerm

def gammaPoleScaleAndCovariantResidueRationalPolynomialEval :
    Polynomial (MvPolynomial ℕ GammaPoleRationalBase) →+* NatGerm :=
  Polynomial.eval₂RingHom gammaPoleCovariantResidueRationalEval
    reciprocalSignedFactorialGerm

theorem gammaPoleScaleAndCovariantResidueRationalPolynomialEval_eq_comp :
    gammaPoleScaleAndCovariantResidueRationalPolynomialEval =
      gammaPoleScaleAndCovariantResidueRationalEval.comp
        (MvPolynomial.optionEquivLeft GammaPoleRationalBase ℕ).symm.toRingHom := by
  apply Polynomial.ringHom_ext
  · intro p
    let lhs : MvPolynomial ℕ GammaPoleRationalBase →+*
        MvPolynomial (Option ℕ) GammaPoleRationalBase :=
      (MvPolynomial.optionEquivLeft GammaPoleRationalBase ℕ).symm.toRingHom.comp
        Polynomial.C
    have hlhs : lhs = (MvPolynomial.rename some).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [lhs]
      · intro k
        simp [lhs, MvPolynomial.optionEquivLeft_symm_C_X]
    calc
      gammaPoleScaleAndCovariantResidueRationalPolynomialEval
          (Polynomial.C p) = gammaPoleCovariantResidueRationalEval p := by
        simp [gammaPoleScaleAndCovariantResidueRationalPolynomialEval]
      _ = gammaPoleScaleAndCovariantResidueRationalEval
          (MvPolynomial.rename some p) := by
        simp [gammaPoleCovariantResidueRationalEval,
          gammaPoleScaleAndCovariantResidueRationalEval,
          gammaPoleScaleAndCovariantResidueFamily,
          MvPolynomial.eval₂_rename, Function.comp_def]
      _ = gammaPoleScaleAndCovariantResidueRationalEval
          ((MvPolynomial.optionEquivLeft
            GammaPoleRationalBase ℕ).symm (Polynomial.C p)) := by
        have hp := RingHom.congr_fun hlhs p
        change (MvPolynomial.optionEquivLeft
            GammaPoleRationalBase ℕ).symm (Polynomial.C p) =
          MvPolynomial.rename some p at hp
        exact congrArg gammaPoleScaleAndCovariantResidueRationalEval hp.symm
  · simp [gammaPoleScaleAndCovariantResidueRationalPolynomialEval,
      gammaPoleCovariantResidueRationalEval,
      gammaPoleScaleAndCovariantResidueRationalEval,
      gammaPoleScaleAndCovariantResidueFamily]

theorem gammaPoleScaleAndCovariantResidueRationalPolynomialEval_injective :
    Function.Injective
      gammaPoleScaleAndCovariantResidueRationalPolynomialEval := by
  rw [gammaPoleScaleAndCovariantResidueRationalPolynomialEval_eq_comp]
  exact gammaPoleScaleAndCovariantResidueRationalEval_injective.comp
    (MvPolynomial.optionEquivLeft
      GammaPoleRationalBase ℕ).symm.injective

/-- Laurent evaluation in the factorial scale with rational-center
covariant-residue coefficients. -/
def gammaPoleScaleAndCovariantResidueRationalLaurentEval :
    LaurentPolynomial (MvPolynomial ℕ GammaPoleRationalBase) →+* NatGerm :=
  LaurentPolynomial.eval₂ gammaPoleCovariantResidueRationalEval
    reciprocalSignedFactorialGermUnit

/-- **Moving-center Laurent value reflection.**  No nonzero finite Laurent
relation between the factorial scale and covariant residues can vanish on the
Gamma pole tower, even with coefficients in `ℂ(N)`. -/
theorem gammaPoleScaleAndCovariantResidueRationalLaurentEval_injective :
    Function.Injective
      gammaPoleScaleAndCovariantResidueRationalLaurentEval := by
  apply laurentPolynomial_eval₂_injective_of_polynomial_eval₂_injective
  simpa [gammaPoleScaleAndCovariantResidueRationalPolynomialEval,
    reciprocalSignedFactorialGermUnit_val] using
      gammaPoleScaleAndCovariantResidueRationalPolynomialEval_injective

end

end GaloisForLFunctions

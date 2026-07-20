import GaloisForLFunctions.HTGeometry.GammaPoleScaleUnitRelativeFreeness
import Mathlib.Algebra.Polynomial.Laurent

/-!
# Laurent freeness of the Gamma pole scale and unit derivatives

The moving-pole diagonal descent uses both positive and negative powers of the
factorial scale.  Polynomial algebraic independence alone does not expose that
interface.  This file separates the scale coordinate from the positive
regular-unit derivatives and extends their joint `ℂ(n)`-evaluation faithfully
to the Laurent localization at the scale.

Thus a Laurent relation in the scale whose coefficients are polynomials in the
actual positive unit derivatives vanishes as a pole-index germ only when the
symbolic Laurent polynomial itself vanishes.  This is the exact value-reflection
law needed to distinguish the signed scale exponents in the Gamma
maximal-weight descent.
-/

open Polynomial LaurentPolynomial MvPolynomial

namespace GaloisForLFunctions

noncomputable section

local instance : Algebra GammaPoleRationalBase NatGerm := ratNatEval.toAlgebra

/-- Relative evaluation on the positive derivatives after separating the scale
coordinate. -/
def gammaPoleUnitDerivativeRationalEval :
    MvPolynomial ℕ GammaPoleRationalBase →+* NatGerm :=
  MvPolynomial.eval₂Hom ratNatEval
    gammaPoleUnitPositiveDerivativeRationalGerm

theorem gammaPoleUnitDerivativeRationalEval_eq_comp :
    gammaPoleUnitDerivativeRationalEval =
      gammaPoleScaleAndUnitDerivativeRationalEval.comp
        (MvPolynomial.rename some).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [gammaPoleUnitDerivativeRationalEval,
      gammaPoleScaleAndUnitDerivativeRationalEval]
  · intro k
    simp only [gammaPoleUnitDerivativeRationalEval,
      MvPolynomial.eval₂Hom_X', RingHom.comp_apply]
    simpa [gammaPoleScaleAndUnitDerivativeRationalEval] using
      (gammaPoleScaleAndUnitDerivativeRationalFamily_some_eq_actual k).symm

/-- Polynomial evaluation after separating the factorial scale from the unit
derivatives. -/
def gammaPoleScaleAndUnitDerivativePolynomialEval :
    Polynomial (MvPolynomial ℕ GammaPoleRationalBase) →+* NatGerm :=
  Polynomial.eval₂RingHom gammaPoleUnitDerivativeRationalEval
    reciprocalSignedFactorialGerm

theorem gammaPoleScaleAndUnitDerivativePolynomialEval_eq_comp :
    gammaPoleScaleAndUnitDerivativePolynomialEval =
      gammaPoleScaleAndUnitDerivativeRationalEval.comp
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
      gammaPoleScaleAndUnitDerivativePolynomialEval (Polynomial.C p) =
          gammaPoleUnitDerivativeRationalEval p := by
        simp [gammaPoleScaleAndUnitDerivativePolynomialEval]
      _ = gammaPoleScaleAndUnitDerivativeRationalEval
          (MvPolynomial.rename some p) := by
        rw [gammaPoleUnitDerivativeRationalEval_eq_comp]
        rfl
      _ = gammaPoleScaleAndUnitDerivativeRationalEval
          ((MvPolynomial.optionEquivLeft GammaPoleRationalBase ℕ).symm
            (Polynomial.C p)) := by
        have hp := RingHom.congr_fun hlhs p
        change (MvPolynomial.optionEquivLeft GammaPoleRationalBase ℕ).symm
          (Polynomial.C p) = MvPolynomial.rename some p at hp
        exact congrArg gammaPoleScaleAndUnitDerivativeRationalEval hp.symm
  · simp [gammaPoleScaleAndUnitDerivativePolynomialEval,
      gammaPoleScaleAndUnitDerivativeRationalEval,
      gammaPoleScaleAndUnitDerivativeRationalFamily]

theorem gammaPoleScaleAndUnitDerivativePolynomialEval_injective :
    Function.Injective gammaPoleScaleAndUnitDerivativePolynomialEval := by
  rw [gammaPoleScaleAndUnitDerivativePolynomialEval_eq_comp]
  exact gammaPoleScaleAndUnitDerivativeRationalEval_injective.comp
    (MvPolynomial.optionEquivLeft GammaPoleRationalBase ℕ).symm.injective

/-- The factorial scale packaged as a unit, for Laurent evaluation. -/
def reciprocalSignedFactorialGermUnit : NatGermˣ :=
  reciprocalSignedFactorialGerm_isUnit.unit

@[simp] theorem reciprocalSignedFactorialGermUnit_val :
    (reciprocalSignedFactorialGermUnit : NatGerm) =
      reciprocalSignedFactorialGerm :=
  reciprocalSignedFactorialGerm_isUnit.unit_spec

/-- Laurent evaluation on the factorial scale with unit-derivative polynomial
coefficients. -/
def gammaPoleScaleAndUnitDerivativeLaurentEval :
    LaurentPolynomial (MvPolynomial ℕ GammaPoleRationalBase) →+* NatGerm :=
  LaurentPolynomial.eval₂ gammaPoleUnitDerivativeRationalEval
    reciprocalSignedFactorialGermUnit

theorem gammaPoleScaleAndUnitDerivativeLaurentEval_toLaurent
    (p : Polynomial (MvPolynomial ℕ GammaPoleRationalBase)) :
    gammaPoleScaleAndUnitDerivativeLaurentEval
        (Polynomial.toLaurent p) =
      gammaPoleScaleAndUnitDerivativePolynomialEval p := by
  simp [gammaPoleScaleAndUnitDerivativeLaurentEval,
    gammaPoleScaleAndUnitDerivativePolynomialEval]

/-- **Laurent value reflection.** Joint relative freeness survives localization
at the nonzero Gamma factorial scale. -/
theorem gammaPoleScaleAndUnitDerivativeLaurentEval_injective :
    Function.Injective gammaPoleScaleAndUnitDerivativeLaurentEval := by
  intro f g hfg
  apply sub_eq_zero.mp
  let q := f - g
  have hqeval : gammaPoleScaleAndUnitDerivativeLaurentEval q = 0 := by
    simp [q, hfg]
  obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow q
  have hpeval : gammaPoleScaleAndUnitDerivativePolynomialEval p = 0 := by
    rw [← gammaPoleScaleAndUnitDerivativeLaurentEval_toLaurent, hp,
      map_mul, hqeval, zero_mul]
  have hp0 : p = 0 :=
    gammaPoleScaleAndUnitDerivativePolynomialEval_injective
      (hpeval.trans (map_zero _).symm)
  have hqT : q * LaurentPolynomial.T (n : ℤ) = 0 := by
    rw [← hp, hp0, map_zero]
  exact (mul_eq_zero.mp hqT).resolve_right
    (LaurentPolynomial.isUnit_T
      (R := MvPolynomial ℕ GammaPoleRationalBase) n).ne_zero

end

end GaloisForLFunctions

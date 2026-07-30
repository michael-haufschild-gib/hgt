import GaloisForLFunctions.HTGeometry.BellCoefficientScalarExtension
import GaloisForLFunctions.HTGeometry.GammaInversePoleBranchScaleFreeness

/-!
# Gamma regular-unit coefficients are free over the rational pole-position field

The complete-Bell coordinate equivalence identifies logarithmic Gamma jets with the Taylor
coefficients of the regular pole unit.  Absolute freeness over `ℂ` does not suffice for moving-pole
descent, because every rational function of the pole label is then available as a coefficient.

This module scalar-extends the nonlinear Bell equivalence to `ℂ(n)`, composes it with the exact
factorial Taylor normalization, and proves that every finite prefix—and hence the complete family—of
actual positive Gamma regular-unit coefficients remains algebraically independent over `ℂ(n)`.
The proof is an exact value relation through the already faithful logarithmic-jet evaluation; it
uses no asymptotic or numerical input.
-/

open MvPolynomial Polynomial

namespace GaloisForLFunctions

noncomputable section

local instance relativeUnitNatGermAlgebra :
    Algebra GammaPoleRationalBase NatGerm := ratNatEval.toAlgebra

local instance relativeUnitComplexNatGermAlgebra :
    Algebra ℂ NatGerm := complexNatGerm.toAlgebra

/-- Factor converting a complete Bell derivative to the matching Taylor coefficient. -/
def gammaPoleUnitBellRationalScale (j : ℕ) : GammaPoleRationalBase :=
  RatFunc.C (((j + 1).factorial : ℂ)⁻¹)

/-- The scalar-extended Bell coordinate equivalence followed by the nonzero Taylor
normalization. -/
def gammaPoleUnitPositiveBellRationalMap (n : ℕ) :
    MvPolynomial (Fin (n + 1)) GammaPoleRationalBase →ₐ[GammaPoleRationalBase]
      MvPolynomial (Fin (n + 1)) GammaPoleRationalBase :=
  (HTGeometry.bellCoefficientMapBaseChange
      (K := GammaPoleRationalBase) n).comp
    (mvPolynomialDiagonalScaleRing
      (fun j : Fin (n + 1) => gammaPoleUnitBellRationalScale (j : ℕ)))

theorem gammaPoleUnitBellRationalScale_ne_zero (j : ℕ) :
    gammaPoleUnitBellRationalScale j ≠ 0 := by
  have hf : (((j + 1).factorial : ℂ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (j + 1))
  simpa [gammaPoleUnitBellRationalScale] using
    RatFunc.C_injective.ne (inv_ne_zero hf)

@[simp] theorem gammaPoleUnitPositiveBellRationalMap_C (n : ℕ)
    (c : GammaPoleRationalBase) :
    gammaPoleUnitPositiveBellRationalMap n (MvPolynomial.C c) =
      MvPolynomial.C c := by
  rw [gammaPoleUnitPositiveBellRationalMap, AlgHom.comp_apply]
  simp [mvPolynomialDiagonalScaleRing]

@[simp] theorem gammaPoleUnitPositiveBellRationalMap_X (n : ℕ)
    (j : Fin (n + 1)) :
    gammaPoleUnitPositiveBellRationalMap n (MvPolynomial.X j) =
      MvPolynomial.C (gammaPoleUnitBellRationalScale (j : ℕ)) *
        MvPolynomial.map (algebraMap ℂ GammaPoleRationalBase)
          (bellAt n ((j : ℕ) + 1) j.isLt) := by
  rw [gammaPoleUnitPositiveBellRationalMap, AlgHom.comp_apply]
  simp [mvPolynomialDiagonalScaleRing]

theorem gammaPoleUnitPositiveBellRationalMap_injective (n : ℕ) :
    Function.Injective (gammaPoleUnitPositiveBellRationalMap n) := by
  exact (HTGeometry.bellCoefficientMapBaseChange_injective
    (K := GammaPoleRationalBase) n).comp
      (mvPolynomialDiagonalScaleRing_injective _ fun j =>
        gammaPoleUnitBellRationalScale_ne_zero (j : ℕ))

/-- Rational-pole-position evaluation on a finite prefix of actual positive Gamma unit
coefficients. -/
def gammaPoleUnitPositiveCoefficientRationalEvalFin (n : ℕ) :
    MvPolynomial (Fin (n + 1)) GammaPoleRationalBase →+* NatGerm :=
  MvPolynomial.eval₂Hom ratNatEval fun j =>
    gammaPoleUnitPositiveCoefficientGerm (j : ℕ)

/-- Exact value relation from regular-unit coefficients to logarithmic derivatives over
`ℂ(n)`. -/
theorem gammaPoleUnitPositiveCoefficientRationalEvalFin_eq_comp (n : ℕ) :
    gammaPoleUnitPositiveCoefficientRationalEvalFin n =
      (gammaPoleLogDerivativeRationalEval (n + 1)).comp
        (gammaPoleUnitPositiveBellRationalMap n).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [gammaPoleUnitPositiveCoefficientRationalEvalFin,
      gammaPoleLogDerivativeRationalEval]
  · intro j
    have hbase : (algebraMap ℂ NatGerm) = ratNatEval.comp RatFunc.C := rfl
    simp only [gammaPoleUnitPositiveCoefficientRationalEvalFin,
      MvPolynomial.eval₂Hom_X', RingHom.comp_apply]
    rw [gammaPoleUnitPositiveCoefficientGerm,
      actualGammaPoleRegularCoefficientGerm_eq,
      gammaPoleRegularCoefficientGerm]
    simp [gammaPoleUnitBellRationalScale,
      gammaPoleLogDerivativeRationalEval,
      bellAt, MvPolynomial.aeval_def, MvPolynomial.eval₂_rename,
      Function.comp_def]
    rw [hbase]
    simp only [RingHom.comp_apply, map_inv₀, map_natCast]

theorem gammaPoleUnitPositiveCoefficientRationalEvalFin_injective (n : ℕ) :
    Function.Injective (gammaPoleUnitPositiveCoefficientRationalEvalFin n) := by
  rw [gammaPoleUnitPositiveCoefficientRationalEvalFin_eq_comp]
  exact (gammaPoleLogDerivativeRationalEval_injective (n + 1)).comp
    (gammaPoleUnitPositiveBellRationalMap_injective n)

/-- Every finite prefix of the actual positive Gamma unit coefficients remains algebraically
independent over the full rational pole-position field. -/
theorem algebraicIndependent_gammaPoleUnitPositiveCoefficientGerm_over_ratFunc_fin
    (n : ℕ) :
    AlgebraicIndependent GammaPoleRationalBase
      (fun j : Fin (n + 1) => gammaPoleUnitPositiveCoefficientGerm (j : ℕ)) := by
  rw [algebraicIndependent_iff_injective_aeval]
  simpa [gammaPoleUnitPositiveCoefficientRationalEvalFin,
    MvPolynomial.aeval_def] using!
      gammaPoleUnitPositiveCoefficientRationalEvalFin_injective n

/-- The complete positive-unit coefficient family remains algebraically independent over
`ℂ(n)`. -/
theorem algebraicIndependent_gammaPoleUnitPositiveCoefficientGerm_over_ratFunc :
    AlgebraicIndependent GammaPoleRationalBase
      gammaPoleUnitPositiveCoefficientGerm := by
  apply algebraicIndependent_of_finite_type
  intro t ht
  rcases ht.bddAbove with ⟨k, hk⟩
  let f : t → Fin (k + 1) := fun i => ⟨i, Nat.lt_succ_of_le (hk i.2)⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact Fin.ext_iff.mp hij
  have hprefix :=
    algebraicIndependent_gammaPoleUnitPositiveCoefficientGerm_over_ratFunc_fin k
  have hsub := hprefix.comp f hf
  simpa [f, Function.comp_def] using hsub

/-- Evaluation of rational-pole-position polynomials on every positive Gamma unit coefficient. -/
def gammaPoleUnitPositiveCoefficientRationalEval :
    MvPolynomial ℕ GammaPoleRationalBase →+* NatGerm :=
  MvPolynomial.eval₂Hom ratNatEval gammaPoleUnitPositiveCoefficientGerm

theorem gammaPoleUnitPositiveCoefficientRationalEval_injective :
    Function.Injective gammaPoleUnitPositiveCoefficientRationalEval := by
  have h := algebraicIndependent_iff_injective_aeval.mp
    algebraicIndependent_gammaPoleUnitPositiveCoefficientGerm_over_ratFunc
  simpa [gammaPoleUnitPositiveCoefficientRationalEval,
    MvPolynomial.aeval_def] using! h

end

end GaloisForLFunctions

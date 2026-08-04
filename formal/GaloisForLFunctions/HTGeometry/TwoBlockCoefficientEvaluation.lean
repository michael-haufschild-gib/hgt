import GaloisForLFunctions.HTGeometry.TwoBlockCoefficientSupport

/-!
# Evaluating the coefficients of a cleared characteristic

Clearing denominators multiplies the characteristic by one scalar of the jet fraction field.  Read
coefficientwise and transported back along the jet parametrization, this says that evaluating the
left-block coefficients of the cleared two-block characteristic at the free element reproduces the
coefficients of the characteristic relation, all scaled by that one nonzero element.

Consequently a ratio of two such evaluations is the corresponding ratio of coefficients of the
characteristic relation, hence lies in the intermediate field: the numerator and denominator needed
by the single-generator criterion can be taken to be coefficients of the cleared characteristic.
-/

namespace GaloisForLFunctions

open scoped Differential

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]

/-- **The coefficients of the cleared characteristic evaluate to the coefficients of the
characteristic relation, up to one common nonzero scalar.** -/
theorem exists_scalar_twoBlockCoefficient_eval
    (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (P : DifferentialPolynomial Unit G)
    (Cc : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P) :
    ∃ c : E, c ≠ 0 ∧ ∀ ν : (Unit × ℕ) →₀ ℕ,
      differentialPolynomialEvalOver (K := F) (fun _ : Unit ↦ y)
          (differentialPolynomialTwoBlockCoefficient ν Cc.polynomial) =
        c * ((P.coeff ν : G) : E) := by
  classical
  have hG' : G ≤ differentialAdjoin F (Set.range fun _ : Unit ↦ y) := by
    simpa [Set.range_const] using hG
  refine ⟨(((differentialIndependentAdjoinParametrization (fun _ : Unit ↦ y) hy)
      (Cc.scalar : FractionRing (DifferentialPolynomial Unit F)) :
      differentialAdjoin F (Set.range fun _ : Unit ↦ y)) : E), ?_, ?_⟩
  · intro h0
    have hzero : (differentialIndependentAdjoinParametrization (fun _ : Unit ↦ y) hy)
        (Cc.scalar : FractionRing (DifferentialPolynomial Unit F)) = 0 := Subtype.ext h0
    have hscalar : (Cc.scalar : FractionRing (DifferentialPolynomial Unit F)) = 0 := by
      have hback := congrArg
        (differentialIndependentAdjoinParametrization (fun _ : Unit ↦ y) hy).symm hzero
      simp at hback
    exact Cc.scalar.ne_zero hscalar
  · intro ν
    have hco := congrArg (MvPolynomial.coeff ν) Cc.clearing
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map] at hco
    have hval := congrArg (fun z => (((differentialIndependentAdjoinParametrization
      (fun _ : Unit ↦ y) hy) z : differentialAdjoin F (Set.range fun _ : Unit ↦ y)) : E)) hco
    simp only [map_mul, MulMemClass.coe_mul] at hval
    have hleft : (((differentialIndependentAdjoinParametrization (fun _ : Unit ↦ y) hy)
        (algebraMap (DifferentialPolynomial Unit F)
          (FractionRing (DifferentialPolynomial Unit F))
          (differentialPolynomialTwoBlockCoefficient ν Cc.polynomial)) :
        differentialAdjoin F (Set.range fun _ : Unit ↦ y)) : E) =
        differentialPolynomialEvalOver (K := F) (fun _ : Unit ↦ y)
          (differentialPolynomialTwoBlockCoefficient ν Cc.polynomial) := by
      have hraw := differentialIndependentAdjoinParametrization_algebraMap_val hy
        (differentialPolynomialTwoBlockCoefficient ν Cc.polynomial)
      simpa [differentialPolynomialEvalOver, differentialPolynomialEval] using hraw
    have hright : (((differentialIndependentAdjoinParametrization (fun _ : Unit ↦ y) hy)
        ((differentialIntermediateToJetFraction G hG hy).toRingHom (P.coeff ν)) :
        differentialAdjoin F (Set.range fun _ : Unit ↦ y)) : E) =
        ((P.coeff ν : G) : E) := by
      rw [differentialIntermediateToJetFraction]
      simp
    rw [show MvPolynomial.coeff ν (differentialPolynomialTwoBlockEquiv F Cc.polynomial) =
        differentialPolynomialTwoBlockCoefficient ν Cc.polynomial from rfl] at hval
    rw [hleft] at hval
    rw [hval, hright]

/-- The evaluation of a coefficient of the cleared characteristic vanishes exactly when the
corresponding coefficient of the characteristic relation does. -/
theorem twoBlockCoefficient_eval_ne_zero_iff
    (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (P : DifferentialPolynomial Unit G)
    (Cc : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P)
    {c : E} (hc : c ≠ 0)
    (hcoeff : ∀ ν : (Unit × ℕ) →₀ ℕ,
      differentialPolynomialEvalOver (K := F) (fun _ : Unit ↦ y)
          (differentialPolynomialTwoBlockCoefficient ν Cc.polynomial) =
        c * ((P.coeff ν : G) : E))
    (ν : (Unit × ℕ) →₀ ℕ) :
    differentialPolynomialEvalOver (K := F) (fun _ : Unit ↦ y)
        (differentialPolynomialTwoBlockCoefficient ν Cc.polynomial) ≠ 0 ↔ P.coeff ν ≠ 0 := by
  rw [hcoeff ν]
  constructor
  · intro h hzero
    apply h
    rw [hzero]
    simp
  · intro h hzero
    rcases mul_eq_zero.mp hzero with hc0 | hP0
    · exact hc hc0
    · refine h ?_
      have hcast : ((P.coeff ν : G) : E) = ((0 : G) : E) := by simpa using hP0
      exact Subtype.ext hcast

/-- **The ratio of two evaluated coefficients is the corresponding coefficient ratio of the
characteristic relation.** -/
theorem twoBlockCoefficient_eval_div
    (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (P : DifferentialPolynomial Unit G)
    (Cc : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P)
    {c : E} (hc : c ≠ 0)
    (hcoeff : ∀ ν : (Unit × ℕ) →₀ ℕ,
      differentialPolynomialEvalOver (K := F) (fun _ : Unit ↦ y)
          (differentialPolynomialTwoBlockCoefficient ν Cc.polynomial) =
        c * ((P.coeff ν : G) : E))
    (ν μ : (Unit × ℕ) →₀ ℕ) :
    differentialPolynomialEvalOver (K := F) (fun _ : Unit ↦ y)
        (differentialPolynomialTwoBlockCoefficient ν Cc.polynomial) /
      differentialPolynomialEvalOver (K := F) (fun _ : Unit ↦ y)
        (differentialPolynomialTwoBlockCoefficient μ Cc.polynomial) =
      ((P.coeff ν / P.coeff μ : G) : E) := by
  rw [hcoeff ν, hcoeff μ]
  by_cases hμ : (P.coeff μ : G) = 0
  · rw [hμ]
    simp
  · field_simp
    push_cast
    ring

end

end GaloisForLFunctions

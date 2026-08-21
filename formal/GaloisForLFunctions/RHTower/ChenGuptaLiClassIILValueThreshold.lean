/-
# Chen--Gupta--Li Class-II critical-line threshold

This module converts the exact finite Class-II integral certificate into a
closed positive lower threshold for the selected critical-line L-value.
No RH, GRH, zero-density, large-value, moment, or analytic premise is
accepted from callers.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiClassIILeftIntegralEnvelope

open Complex

noncomputable section

namespace RHTower

/-- The closed L-value threshold forced by a certified primitive Class-II row. -/
def cglPrimitiveClassIWellSpacedClassIILValueThreshold
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIIRow X Y n χ τ H) : ℝ :=
  (Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4) /
    (‖(1 / (2 * Real.pi) : ℝ)‖ *
      cglPrimitiveClassILeftLineWeightEnvelope X n Y χ τ H
        (cglPrimitiveClassIWellSpacedZero n χ τ H r.1)
        (cglPrimitiveClassIWellSpacedClassIIMaximizerRadius X Y n χ τ H r) *
      |((cglPrimitiveClassIWellSpacedClassIIMaximizerRadius X Y n χ τ H r : NNReal) : ℝ) -
        (-((cglPrimitiveClassIWellSpacedClassIIMaximizerRadius X Y n χ τ H r : NNReal) : ℝ))|)

/-- The selected Class-II critical-line L-value is nonzero. -/
theorem cglPrimitiveClassIWellSpacedClassII_LValue_positive
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIIRow X Y n χ τ H) :
    0 < ‖DirichletCharacter.LFunction χ.1.1
      (cglCriticalLinePoint
        (cglPrimitiveClassIWellSpacedClassIIMaximizerRow X Y n χ τ H r).time).1‖ := by
  let a : ℝ := ‖(1 / (2 * Real.pi) : ℝ)‖
  let W : ℝ := cglPrimitiveClassILeftLineWeightEnvelope X n Y χ τ H
    (cglPrimitiveClassIWellSpacedZero n χ τ H r.1)
    (cglPrimitiveClassIWellSpacedClassIIMaximizerRadius X Y n χ τ H r)
  let L : ℝ := ‖DirichletCharacter.LFunction χ.1.1
    (cglCriticalLinePoint
      (cglPrimitiveClassIWellSpacedClassIIMaximizerRow X Y n χ τ H r).time).1‖
  let ell : ℝ := |((cglPrimitiveClassIWellSpacedClassIIMaximizerRadius X Y n χ τ H r : NNReal) : ℝ) -
    (-((cglPrimitiveClassIWellSpacedClassIIMaximizerRadius X Y n χ τ H r : NNReal) : ℝ))|
  have hcert := cglPrimitiveClassIWellSpacedClassII_LValue_certificate X Y n χ τ H r
  have hcert' : Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 ≤ a * W * L * ell := by
    simpa [a, W, L, ell] using hcert
  have hstart : 0 < Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 := by
    exact div_pos (Real.exp_pos _) (by norm_num)
  have hprod : 0 < a * W * L * ell := lt_of_lt_of_le hstart hcert'
  let D : ℝ := a * W * ell
  have hprod' : 0 < D * L := by
    calc
      0 < a * W * L * ell := hprod
      _ = D * L := by
        dsimp [D]
        ring
  rcases (mul_pos_iff.mp hprod') with hpos | hneg
  · simpa only [L] using hpos.2
  · exact False.elim ((not_lt_of_ge (norm_nonneg _)) hneg.2)

/-- The closed Class-II threshold is strictly positive for every certified row. -/
theorem cglPrimitiveClassIWellSpacedClassIILValueThreshold_positive
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIIRow X Y n χ τ H) :
    0 < cglPrimitiveClassIWellSpacedClassIILValueThreshold X Y n χ τ H r := by
  let a : ℝ := ‖(1 / (2 * Real.pi) : ℝ)‖
  let W : ℝ := cglPrimitiveClassILeftLineWeightEnvelope X n Y χ τ H
    (cglPrimitiveClassIWellSpacedZero n χ τ H r.1)
    (cglPrimitiveClassIWellSpacedClassIIMaximizerRadius X Y n χ τ H r)
  let L : ℝ := ‖DirichletCharacter.LFunction χ.1.1
    (cglCriticalLinePoint
      (cglPrimitiveClassIWellSpacedClassIIMaximizerRow X Y n χ τ H r).time).1‖
  let ell : ℝ := |((cglPrimitiveClassIWellSpacedClassIIMaximizerRadius X Y n χ τ H r : NNReal) : ℝ) -
    (-((cglPrimitiveClassIWellSpacedClassIIMaximizerRadius X Y n χ τ H r : NNReal) : ℝ))|
  have hcert := cglPrimitiveClassIWellSpacedClassII_LValue_certificate X Y n χ τ H r
  have hcert' : Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 ≤ a * W * L * ell := by
    simpa [a, W, L, ell] using hcert
  have hstart : 0 < Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 := by
    exact div_pos (Real.exp_pos _) (by norm_num)
  have hprod : 0 < a * W * L * ell := lt_of_lt_of_le hstart hcert'
  let D : ℝ := a * W * ell
  have hprod' : 0 < D * L := by
    calc
      0 < a * W * L * ell := hprod
      _ = D * L := by
        dsimp [D]
        ring
  have hD : 0 < D := by
    rcases (mul_pos_iff.mp hprod') with hpos | hneg
    · exact hpos.1
    · exact False.elim ((not_lt_of_ge (norm_nonneg _)) hneg.2)
  change (0 : ℝ) < (Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4) / D
  exact div_pos hstart hD

/-- The closed Class-II threshold is attained by the selected local maximum. -/
theorem cglPrimitiveClassIWellSpacedClassII_LValueThreshold_le
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIIRow X Y n χ τ H) :
    cglPrimitiveClassIWellSpacedClassIILValueThreshold X Y n χ τ H r ≤
      ‖DirichletCharacter.LFunction χ.1.1
        (cglCriticalLinePoint
          (cglPrimitiveClassIWellSpacedClassIIMaximizerRow X Y n χ τ H r).time).1‖ := by
  let a : ℝ := ‖(1 / (2 * Real.pi) : ℝ)‖
  let W : ℝ := cglPrimitiveClassILeftLineWeightEnvelope X n Y χ τ H
    (cglPrimitiveClassIWellSpacedZero n χ τ H r.1)
    (cglPrimitiveClassIWellSpacedClassIIMaximizerRadius X Y n χ τ H r)
  let L : ℝ := ‖DirichletCharacter.LFunction χ.1.1
    (cglCriticalLinePoint
      (cglPrimitiveClassIWellSpacedClassIIMaximizerRow X Y n χ τ H r).time).1‖
  let ell : ℝ := |((cglPrimitiveClassIWellSpacedClassIIMaximizerRadius X Y n χ τ H r : NNReal) : ℝ) -
    (-((cglPrimitiveClassIWellSpacedClassIIMaximizerRadius X Y n χ τ H r : NNReal) : ℝ))|
  have hcert := cglPrimitiveClassIWellSpacedClassII_LValue_certificate X Y n χ τ H r
  have hcert' : Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 ≤ a * W * L * ell := by
    simpa [a, W, L, ell] using hcert
  have hstart : 0 < Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 := by
    exact div_pos (Real.exp_pos _) (by norm_num)
  have hprod : 0 < a * W * L * ell := lt_of_lt_of_le hstart hcert'
  let D : ℝ := a * W * ell
  have hprod' : 0 < D * L := by
    calc
      0 < a * W * L * ell := hprod
      _ = D * L := by
        dsimp [D]
        ring
  have hD : 0 < D := by
    rcases (mul_pos_iff.mp hprod') with hpos | hneg
    · exact hpos.1
    · exact False.elim ((not_lt_of_ge (norm_nonneg _)) hneg.2)
  change (Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4) / D ≤ L
  apply (div_le_iff₀ hD).mpr
  calc
    Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 ≤ a * W * L * ell := hcert'
    _ = L * D := by
      dsimp [D]
      ring

end RHTower

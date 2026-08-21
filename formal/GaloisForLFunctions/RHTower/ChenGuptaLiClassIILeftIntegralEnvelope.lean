/-
# Chen--Gupta--Li Class-II finite integral envelope

This module integrates the compact left-line weight envelope and transfers
the closed finite left-contour witness to its canonical critical-line L-value
maximizer.  The certificate is exact and carries no caller-provided analytic
premise.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiClassIILeftEnvelope

open Complex

noncomputable section

namespace RHTower

/-- A finite Class-II left contour is bounded by its compact weight envelope,
the selected L-value maximum, and its literal interval length. -/
theorem norm_cglPrimitiveClassI_leftLineIntegral_le_envelope
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) (B : NNReal) :
    ‖∫ t in (-((B : ℝ)))..(B : ℝ),
      cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
        (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
        (cglPrimitiveClassILeftLinePoint n χ τ H z t)‖ ≤
      (cglPrimitiveClassILeftLineWeightEnvelope X n Y χ τ H z B *
        ‖DirichletCharacter.LFunction χ.1.1
          (cglCriticalLinePoint
            (cglClassIICriticalLineLocalMaximizerRow n χ.1.1 z.1.1.im B).time).1‖) *
          |(B : ℝ) - (-((B : ℝ)) : ℝ)| := by
  have hleft : (-((B : ℝ)) : ℝ) ≤ (B : ℝ) := by
    linarith [NNReal.coe_nonneg B]
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => by
    rw [Set.uIoc_of_le hleft] at ht
    let u : CGLClassIICriticalLineLocalOffset B := ⟨t, ⟨ht.1.le, ht.2⟩⟩
    calc
      ‖cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
          (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
          (cglPrimitiveClassILeftLinePoint n χ τ H z t)‖ ≤
          ‖cglPrimitiveClassILeftLineWeight X n Y χ τ H z u.1‖ *
            ‖DirichletCharacter.LFunction χ.1.1
              (cglCriticalLinePoint
                (cglClassIICriticalLineLocalMaximizerRow n χ.1.1 z.1.1.im B).time).1‖ := by
            simpa [u] using
              norm_cglPrimitiveClassI_leftLineIntegrand_le_localMax X n Y χ τ H z B u
      _ ≤ cglPrimitiveClassILeftLineWeightEnvelope X n Y χ τ H z B *
            ‖DirichletCharacter.LFunction χ.1.1
              (cglCriticalLinePoint
                (cglClassIICriticalLineLocalMaximizerRow n χ.1.1 z.1.1.im B).time).1‖ := by
            exact mul_le_mul_of_nonneg_right
              (norm_cglPrimitiveClassILeftLineWeight_le_envelope X n Y χ τ H z B u)
              (norm_nonneg _))

/-- Each certified primitive Class-II row yields an explicit lower certificate
for its selected critical-line L-value maximum. -/
theorem cglPrimitiveClassIWellSpacedClassII_LValue_certificate
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (r : CGLPrimitiveClassIWellSpacedClassIIRow X Y n χ τ H) :
    Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 ≤
      ‖(1 / (2 * Real.pi) : ℝ)‖ *
        cglPrimitiveClassILeftLineWeightEnvelope X n Y χ τ H
          (cglPrimitiveClassIWellSpacedZero n χ τ H r.1)
          (cglPrimitiveClassIWellSpacedClassIIMaximizerRadius X Y n χ τ H r) *
        ‖DirichletCharacter.LFunction χ.1.1
          (cglCriticalLinePoint
            (cglPrimitiveClassIWellSpacedClassIIMaximizerRow X Y n χ τ H r).time).1‖ *
        |((cglPrimitiveClassIWellSpacedClassIIMaximizerRadius X Y n χ τ H r : NNReal) : ℝ) -
          (-((cglPrimitiveClassIWellSpacedClassIIMaximizerRadius X Y n χ τ H r : NNReal) : ℝ))| := by
  let z : CGLPrimitiveClassIWindowZero n χ τ H :=
    cglPrimitiveClassIWellSpacedZero n χ τ H r.1
  let B : NNReal := cglPrimitiveClassIWellSpacedClassIIMaximizerRadius X Y n χ τ H r
  have hB : (B : ℝ) =
      ((cglPrimitiveClassIWellSpacedClassIILeftLineDepth X Y n χ τ H r + 1 : ℕ) : ℝ) := by
    dsimp only [B]
    unfold cglPrimitiveClassIWellSpacedClassIIMaximizerRadius
    rfl
  have hlarge := cglPrimitiveClassIWellSpacedClassIILeftLineDepth_large X Y n χ τ H r
  have hint := norm_cglPrimitiveClassI_leftLineIntegral_le_envelope X n Y χ τ H z B
  have hint' :
      ‖∫ t in (-((B : ℝ)))..(B : ℝ),
        cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
          (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
          (cglPrimitiveClassILeftLinePoint n χ τ H z t)‖ ≤
        (cglPrimitiveClassILeftLineWeightEnvelope X n Y χ τ H z B *
          ‖DirichletCharacter.LFunction χ.1.1
            (cglCriticalLinePoint
              (cglClassIICriticalLineLocalMaximizerRow n χ.1.1 z.1.1.im B).time).1‖) *
            |(B : ℝ) - (-((B : ℝ)) : ℝ)| := hint
  have hlarge' :
      Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 ≤
        ‖(1 / (2 * Real.pi) : ℝ)‖ *
          ‖∫ t in (-((B : ℝ)))..(B : ℝ),
            cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
              (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
              (cglPrimitiveClassILeftLinePoint n χ τ H z t)‖ := by
    rw [hB]
    simpa [z, cglPrimitiveClassILeftLinePoint] using hlarge
  calc
    Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 ≤
        ‖(1 / (2 * Real.pi) : ℝ)‖ *
          ‖∫ t in (-((B : ℝ)))..(B : ℝ),
            cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
              (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
              (cglPrimitiveClassILeftLinePoint n χ τ H z t)‖ := hlarge'
    _ ≤ ‖(1 / (2 * Real.pi) : ℝ)‖ *
          ((cglPrimitiveClassILeftLineWeightEnvelope X n Y χ τ H z B *
            ‖DirichletCharacter.LFunction χ.1.1
              (cglCriticalLinePoint
                (cglClassIICriticalLineLocalMaximizerRow n χ.1.1 z.1.1.im B).time).1‖) *
              |(B : ℝ) - (-((B : ℝ)) : ℝ)|) :=
        mul_le_mul_of_nonneg_left hint' (norm_nonneg _)
    _ = ‖(1 / (2 * Real.pi) : ℝ)‖ *
        cglPrimitiveClassILeftLineWeightEnvelope X n Y χ τ H
          (cglPrimitiveClassIWellSpacedZero n χ τ H r.1)
          (cglPrimitiveClassIWellSpacedClassIIMaximizerRadius X Y n χ τ H r) *
        ‖DirichletCharacter.LFunction χ.1.1
          (cglCriticalLinePoint
            (cglPrimitiveClassIWellSpacedClassIIMaximizerRow X Y n χ τ H r).time).1‖ *
        |((cglPrimitiveClassIWellSpacedClassIIMaximizerRadius X Y n χ τ H r : NNReal) : ℝ) -
          (-((cglPrimitiveClassIWellSpacedClassIIMaximizerRadius X Y n χ τ H r : NNReal) : ℝ))| := by
      simp only [z, B, cglPrimitiveClassIWellSpacedClassIIMaximizerRow]
      ring

end RHTower

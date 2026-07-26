import GaloisForLFunctions.RHTower.DeningerArithmeticPoincareDuality

/-!
# Source quotient evaluations in compact-support cohomology

Every Xi divisor point yields a character of the source-defined quotient
`Entire(ℂ)/(XiC)` by evaluation.  The construction is a theorem from the Xi ideal and does not
define ordinary cohomology by a zero list.  These characters are the zeroth local residue classes
inside compact-support cohomology.

The forced compact-support Frobenius acts on evaluation at `alpha` with complementary eigenvalue
`1/2 - I*alpha`.  This gives the local Poincare selection law directly from the source quotient:
ordinary and compact-support eigenvalues add to one.

Higher jet characters are required to recover multiple-zero fibers; this file isolates the
zeroth-jet layer.
-/

open Complex

namespace RHTower

noncomputable section

/-- Evaluation of an entire source at a complex point. -/
def deningerEntireEvaluation (z : ℂ) :
    DeningerEntire →ₐ[ℂ] ℂ where
  toFun F := F z
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem deningerEntireEvaluation_apply
    (z : ℂ) (F : DeningerEntire) :
    deningerEntireEvaluation z F = F z :=
  rfl

/-- The centered completed Xi source vanishes at every divisor support point. -/
theorem XiC_xiSpectralPointSupport_eq_zero_source
    (rho : XiDivisorSupport) :
    XiC (xiSpectralPointSupport rho) = 0 := by
  simpa only [xiThetaDividedChain_zero] using
    xiThetaDividedChain_vanish_before_multiplicity rho
      (xiSupportMultiplicity_pos rho)

/-- Evaluation at a Xi point descends to a character of source middle cohomology. -/
def deningerArithmeticEvaluation
    (rho : XiDivisorSupport) :
    DeningerArithmeticH1 →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ deningerEntireXiIdeal
    (deningerEntireEvaluation (xiSpectralPointSupport rho)) (by
      intro F hF
      rw [deningerEntireXiIdeal, Ideal.mem_span_singleton'] at hF
      obtain ⟨G, hG⟩ := hF
      have heval := congrArg
        (fun H : DeningerEntire =>
          H (xiSpectralPointSupport rho)) hG
      simpa only [deningerEntire_mul_apply, deningerEntireXi_apply,
        XiC_xiSpectralPointSupport_eq_zero_source rho, mul_zero] using
        heval.symm)

@[simp]
theorem deningerArithmeticEvaluation_class
    (rho : XiDivisorSupport) (F : DeningerEntire) :
    deningerArithmeticEvaluation rho (deningerEntireH1Class F) =
      F (xiSpectralPointSupport rho) := by
  change
    Ideal.Quotient.lift deningerEntireXiIdeal
        (deningerEntireEvaluation (xiSpectralPointSupport rho)).toRingHom _
        (Ideal.Quotient.mk deningerEntireXiIdeal F) =
      F (xiSpectralPointSupport rho)
  rw [Ideal.Quotient.lift_mk]
  rfl

@[simp]
theorem deningerArithmeticEvaluation_coordinateClass
    (rho : XiDivisorSupport) :
    deningerArithmeticEvaluation rho deningerEntireCoordinateClass =
      xiSpectralPointSupport rho := by
  rw [deningerEntireCoordinateClass,
    deningerArithmeticEvaluation_class]
  rfl

@[simp]
theorem deningerArithmeticEvaluation_thetaClass
    (rho : XiDivisorSupport) :
    deningerArithmeticEvaluation rho deningerEntireThetaClass =
      1 / 2 + Complex.I * xiSpectralPointSupport rho := by
  rw [← deningerEntireH1Class_thetaCoordinate,
    deningerArithmeticEvaluation_class,
    deningerEntireThetaCoordinate_apply]

/-- Zeroth local residue class as an element of compact-support middle cohomology. -/
def deningerArithmeticEvaluationCompact
    (rho : XiDivisorSupport) :
    DeningerArithmeticH1Compact :=
  (deningerArithmeticEvaluation rho).toLinearMap

@[simp]
theorem deningerArithmeticEvaluationCompact_apply
    (rho : XiDivisorSupport) (x : DeningerArithmeticH1) :
    deningerArithmeticEvaluationCompact rho x =
      deningerArithmeticEvaluation rho x :=
  rfl

/-- Every local evaluation class is nonzero. -/
theorem deningerArithmeticEvaluationCompact_ne_zero
    (rho : XiDivisorSupport) :
    deningerArithmeticEvaluationCompact rho ≠ 0 := by
  intro hzero
  have h := LinearMap.congr_fun hzero (1 : DeningerArithmeticH1)
  change deningerArithmeticEvaluation rho 1 = 0 at h
  rw [map_one] at h
  exact one_ne_zero h

/--
Local compact-support Frobenius eigenlaw.  Evaluation at `alpha` carries the complementary
weight `1/2 - I*alpha`.
-/
theorem deningerArithmeticThetaCompact_evaluation
    (rho : XiDivisorSupport) :
    deningerArithmeticThetaCompact
        (deningerArithmeticEvaluationCompact rho) =
      (1 / 2 - Complex.I * xiSpectralPointSupport rho) •
        deningerArithmeticEvaluationCompact rho := by
  apply LinearMap.ext
  intro x
  change
    deningerArithmeticEvaluation rho x -
        deningerArithmeticEvaluation rho (deningerEntireTheta x) =
      (1 / 2 - Complex.I * xiSpectralPointSupport rho) *
        deningerArithmeticEvaluation rho x
  rw [deningerEntireTheta_apply,
    map_mul, deningerArithmeticEvaluation_thetaClass]
  ring

/-- Ordinary and compact-support local Frobenius weights add to one. -/
theorem deningerArithmetic_local_weights_add_one
    (rho : XiDivisorSupport) :
    (1 / 2 + Complex.I * xiSpectralPointSupport rho) +
      (1 / 2 - Complex.I * xiSpectralPointSupport rho) = 1 := by
  ring

end

end RHTower

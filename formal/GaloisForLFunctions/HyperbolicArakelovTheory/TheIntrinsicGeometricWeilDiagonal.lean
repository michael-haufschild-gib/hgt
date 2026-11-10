import GaloisForLFunctions.HyperbolicArakelovTheory.TheWeilPacketsFromRenormalizedGeometricDiagonals
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerScatteringNormalization

/-!
# An intrinsic geometric definition of the Weil diagonal

The raw primitive-pair Poincare series supplies its own scattering
coefficient by zero-Fourier extraction. Its truncated pairing defines
the diagonal without inserting completed zeta values. Actual Fourier
uniqueness cancels the completed normalization and transfers the scalar
Robin limit to this intrinsic geometric construction.
-/

open Complex Filter Topology MeasureTheory Set ModularGroup
open scoped BigOperators FourierTransform
open RHTower Zeta23 RHTower.WeilLineAnyAbscissa
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScatteringNormalization

namespace GaloisForLFunctions.HyperbolicArakelovTheory.ScatteringTower.RawGeometry

set_option autoImplicit false
noncomputable section

/-- The actual, uncompleted primitive-pair Poincare series on the upper half-plane. -/
def model (P : D4BMEisensteinAbsoluteConvergenceParameter) (z : UpperHalfPlane) : ℂ :=
  d4BMRawEisensteinHorizontalFunction ⟨z.re, z.im, z.im_pos⟩ P z.re

/-- Cusp truncation using only the raw series and its extracted zero Fourier coefficient. -/
def truncated (P : D4BMEisensteinAbsoluteConvergenceParameter) (z : UpperHalfPlane) : ℂ :=
  model P z - if 1 < z.im then
    (z.im : ℂ) ^ P.s + actualScattering P * (z.im : ℂ) ^ (1 - P.s) else 0

/-- The bilinear pairing of the actual raw truncated field. -/
def pairing (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  ∫ z in fd, truncated P z ^ 2

/-- The normalization-free geometric diagonal, defined without zeta values. -/
def diagonal (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  ((actualScattering P)⁻¹ - actualScattering P) / (4 * (P.s - 1 / 2)) -
    pairing P / (2 * actualScattering P)

private theorem parameter_re (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    1 / 2 < (P.s - 1 / 2).re := by
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
  linarith [P.re_gt_one]

private theorem completion_eq (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    reflectedCompletedLambda (2 * P.s) = msA (P.s - 1 / 2) := by
  unfold msA
  congr 1
  ring

/-- Zero-Fourier extraction determines the raw scattering coefficient geometrically. -/
theorem completion_mul_scattering (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    msA (P.s - 1 / 2) * actualScattering P = msB (P.s - 1 / 2) := by
  have h : msA (P.s - 1 / 2) * (actualScattering P + 1) =
      msB (P.s - 1 / 2) + msA (P.s - 1 / 2) := by
    calc
      msA (P.s - 1 / 2) * (actualScattering P + 1) =
        ∫ x in Ioc (0 : ℝ) 1, fourier (0 : ℤ) (x : UnitAddCircle) *
          d4BMCompletedEisensteinHorizontalFunction basePoint P x := by
        rw [actualScattering, sub_add_cancel, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        dsimp only
        rw [d4BM_completedEisensteinHorizontalFunction_eq_lambda_mul_raw, completion_eq]
        ring
      _ = msB (P.s - 1 / 2) + msA (P.s - 1 / 2) := by
        rw [d4BM_actualCompletedPoincare_zeroFourierCoefficient_eq_canonicalConstantPart,
          cuspConstantPart_eq_msAB]
        simp only [basePoint, Complex.ofReal_one, Complex.one_cpow, mul_one]
  linear_combination h

private theorem scattering_ne_zero (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    actualScattering P ≠ 0 := by
  have hB : msB (P.s - 1 / 2) ≠ 0 := by
    unfold msB reflectedCompletedLambda
    apply mul_ne_zero
    · exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith [P.re_gt_one])
    · exact riemannZeta_ne_zero_of_one_lt_re (by simp; linarith [P.re_gt_one])
  intro hzero
  have h := completion_mul_scattering P
  rw [hzero, mul_zero] at h
  exact hB h.symm

theorem completion_mul_model (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (z : UpperHalfPlane) :
    msA (P.s - 1 / 2) * model P z = eisensteinLineModel (P.s - 1 / 2) z := by
  have h := d4BM_actualCompletedPoincare_eq_canonicalCuspLeg
    (⟨z.re, z.im, z.im_pos⟩ : D4BMUpperHalfPlaneCoordinate) P z.re
  rw [d4BM_completedEisensteinHorizontalFunction_eq_lambda_mul_raw, completion_eq] at h
  exact h

theorem completion_mul_truncated (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (z : UpperHalfPlane) :
    msA (P.s - 1 / 2) * truncated P z = truncatedLineModel (P.s - 1 / 2) 1 z := by
  unfold truncated truncatedLineModel
  rw [mul_sub, completion_mul_model, cuspConstantPart_eq_msAB]
  split_ifs
  · rw [mul_add, ← mul_assoc, completion_mul_scattering]
    rw [show (1 / 2 : ℂ) + (P.s - 1 / 2) = P.s by ring,
      show (1 / 2 : ℂ) - (P.s - 1 / 2) = 1 - P.s by ring]
    ring
  · simp

/-- Completion is a common scalar square in the actual pairing. -/
theorem completed_pairing_eq (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    truncatedPairing 1 (P.s - 1 / 2) (P.s - 1 / 2) =
      msA (P.s - 1 / 2) ^ 2 * pairing P := by
  unfold truncatedPairing pairing
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  dsimp only
  rw [← completion_mul_truncated P z]
  ring

/-- The completed normalization cancels entirely from the geometric diagonal. -/
theorem diagonal_eq (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    diagonal P = geometricDiagonal (P.s - 1 / 2) := by
  have hA := msA_ne_zero_of_re (parameter_re P)
  have hφ := scattering_ne_zero P
  have hu : P.s - 1 / 2 ≠ 0 := by
    intro h
    have hr := parameter_re P
    rw [h] at hr
    norm_num at hr
  rw [diagonal, geometricDiagonal, completed_pairing_eq, ← completion_mul_scattering]
  generalize hscalar : msA (P.s - 1 / 2) = a at hA ⊢
  field_simp [hA, hφ, hu]

/-- Absolute-chamber parameters of the primitive-pair tower on `Re s=3/2`. -/
def packetParameter (t : ℝ) (n : ℕ) : D4BMEisensteinAbsoluteConvergenceParameter where
  s := ((3 / 2 : ℂ) + t * I + n + 1) / 2
  re_gt_one := by
    norm_num
    linarith [Nat.cast_nonneg (α := ℝ) n]

/-- Finite Weil energy defined entirely from raw geometric fields and a scalar subtraction. -/
def energy (f : ℝ → ℂ) (N : ℕ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, lineF (EF.weilTest f f) (3 / 2) t *
    ((∑ n ∈ Finset.range N, diagonal (packetParameter t n)) +
      robinCounterterm ((3 / 2 : ℝ) + N) +
        1 / ((3 / 2 : ℂ) + t * I) + 1 / ((3 / 2 : ℂ) + t * I - 1))

theorem energy_eq (f : ℝ → ℂ) (N : ℕ) : energy f N = geometricWeilEnergy f N := by
  have hsum (t : ℝ) : (∑ n ∈ Finset.range N, diagonal (packetParameter t n)) =
      geometricTower ((3 / 2 : ℂ) + t * I) N := by
    unfold geometricTower
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [diagonal_eq]
    congr 1
    dsimp [packetParameter]
    ring
  unfold energy geometricWeilEnergy
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [hsum, renormalizedTower]
  norm_num

/-- The full Weil functional is the Robin limit of intrinsic primitive-pair geometric energies. -/
theorem tendsto_energy {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Tendsto (energy f) atTop
      (𝓝 (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f f))) :=
  (tendsto_geometricWeilEnergy hf hfc).congr fun N => (energy_eq f N).symm

#print axioms diagonal_eq
#print axioms tendsto_energy

end

end GaloisForLFunctions.HyperbolicArakelovTheory.ScatteringTower.RawGeometry

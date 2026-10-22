import GaloisForLFunctions.RHTower.SoninSemilocalCyclicWeylDescent
import GaloisForLFunctions.RHTower.Suzuki.SuzukiApertureL2Equivalence
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaMovableCompletedCovarianceCharacteristic

/-!
# Finite-aperture Weyl holonomy and the literal Suzuki source

The two-factor Weyl relation survives compression when position phase preserves an aperture.
The four-factor group holonomy does not: its exact defect is one escaped translation channel.
This file proves that identity on the physical logarithmic `L²` model and applies it to the
literal movable Suzuki completed covariance.  It makes no positivity or cofinality claim.
-/

namespace RHTower

open MeasureTheory Set Filter

noncomputable section

/-- Algebraic finite-cutoff holonomy: the only defect after compressing a global group
commutator is the channel which leaves the cutoff between translation and its inverse. -/
theorem compressed_weyl_holonomy
    {R : Type*} [Ring R] (P U V Ui Vi z : R)
    (hP : P * P = P)
    (hPU : P * U = U * P)
    (hPUi : P * Ui = Ui * P)
    (hfull : U * V * Ui * Vi = z) :
    P * U * P * V * P * Ui * P * Vi * P =
      P * z * P - P * U * V * (1 - P) * Ui * Vi * P := by
  calc
    P * U * P * V * P * Ui * P * Vi * P =
        P * U * V * P * Ui * Vi * P := by
          noncomm_ring [hP, hPU, hPUi]
    _ = P * (U * V * Ui * Vi) * P - P * U * V * (1 - P) * Ui * Vi * P := by
          noncomm_ring
    _ = P * z * P - P * U * V * (1 - P) * Ui * Vi * P := by rw [hfull]

/-- When phase is central and unitary, compressed holonomy is the central character times
identity minus exactly the escaped translation channel. -/
theorem compressed_weyl_holonomy_scalar_escape
    {R : Type*} [Ring R] (P U V Ui Vi z : R)
    (hP : P * P = P)
    (hPU : P * U = U * P)
    (hUU : U * Ui = 1)
    (hUiU : Ui * U = 1)
    (hPz : P * z = z * P)
    (hUV : U * V = z * (V * U))
    (hfull : U * V * Ui * Vi = z) :
    P * U * P * V * P * Ui * P * Vi * P =
      z * (P - P * V * (1 - P) * Vi * P) := by
  have hUPUi : U * P * Ui = P := by
    calc
      U * P * Ui = P * U * Ui := by rw [hPU]
      _ = P * (U * Ui) := by noncomm_ring
      _ = P := by rw [hUU, mul_one]
  have hUQUi : U * (1 - P) * Ui = 1 - P := by
    calc
      U * (1 - P) * Ui = U * Ui - U * P * Ui := by noncomm_ring
      _ = 1 - P := by rw [hUU, hUPUi]
  have hPUi : P * Ui = Ui * P := by
    calc
      P * Ui = (Ui * U) * P * Ui := by rw [hUiU, one_mul]
      _ = Ui * (U * P * Ui) := by noncomm_ring
      _ = Ui * P := by rw [hUPUi]
  have hcentral : P * z * P = z * P := by
    calc
      P * z * P = z * P * P := by rw [hPz]
      _ = z * (P * P) := by noncomm_ring
      _ = z * P := by rw [hP]
  have hescape : P * U * V * (1 - P) * Ui * Vi * P =
      z * (P * V * (1 - P) * Vi * P) := by
    calc
      P * U * V * (1 - P) * Ui * Vi * P =
          P * (U * V) * (1 - P) * Ui * Vi * P := by noncomm_ring
      _ = P * (z * (V * U)) * (1 - P) * Ui * Vi * P := by rw [hUV]
      _ = (P * z) * (V * U) * (1 - P) * Ui * Vi * P := by noncomm_ring
      _ = (z * P) * (V * U) * (1 - P) * Ui * Vi * P := by rw [hPz]
      _ = z * (P * V * (U * (1 - P) * Ui) * Vi * P) := by noncomm_ring
      _ = z * (P * V * (1 - P) * Vi * P) := by rw [hUQUi]
  rw [compressed_weyl_holonomy P U V Ui Vi z hP hPU hPUi hfull,
    hcentral, hescape, mul_sub]
  noncomm_ring

/-- Literal central-interval cutoff on the physical logarithmic line. -/
def soninCentralCutoff (a : SuzukiPositiveAperture) : SoninL2 →L[ℂ] SoninL2 :=
  indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)

/-- Four-factor Weyl holonomy after every physical factor is compressed to the Suzuki aperture. -/
def soninCompressedWeylHolonomy
    (a : SuzukiPositiveAperture) (h t : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  soninCentralCutoff a * soninLogPositionPhaseCLM t *
    soninCentralCutoff a * soninLogTranslationCLM h *
    soninCentralCutoff a * soninLogPositionPhaseInvCLM t *
    soninCentralCutoff a * soninLogTranslationInvCLM h *
    soninCentralCutoff a

/-- The sole finite-aperture holonomy defect: translation escapes the aperture and returns. -/
def soninCentralWeylEscape
    (a : SuzukiPositiveAperture) (h : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  soninCentralCutoff a * soninLogTranslationCLM h *
    (1 - soninCentralCutoff a) * soninLogTranslationInvCLM h *
    soninCentralCutoff a

/-- Position phase commutes with sharp physical aperture cutoff pointwise almost everywhere. -/
theorem soninLogPositionPhaseCLM_commutes_centralCutoff
    (a : SuzukiPositiveAperture) (t : ℝ) :
    soninCentralCutoff a * soninLogPositionPhaseCLM t =
      soninLogPositionPhaseCLM t * soninCentralCutoff a := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  let q : ℝ := t / (2 * Real.pi)
  filter_upwards [
    indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1)
      (soninLogPositionPhaseCLM t f),
    indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1) f,
    MellinL2.fourierPhaseMulAux_ae q f,
    MellinL2.fourierPhaseMulAux_ae q (soninCentralCutoff a f)
  ] with x hleft hcut hf hright
  change indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)
      (soninLogPositionPhaseCLM t f) x =
    soninLogPositionPhaseCLM t
      (indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1) f) x
  rw [hleft]
  change (centralInterval a.1).indicator
      (fun y => MellinL2.fourierPhaseMulAux q f y) x =
    MellinL2.fourierPhaseMulAux q (soninCentralCutoff a f) x
  rw [hright]
  by_cases hx : x ∈ centralInterval a.1
  · rw [Set.indicator_of_mem hx, hf]
    have hfix : (soninCentralCutoff a f : SoninL2) x = f x := by
      change indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1) f x = _
      rw [hcut, Set.indicator_of_mem hx]
    rw [hfix]
  · rw [Set.indicator_of_notMem hx]
    have hzero : (soninCentralCutoff a f : SoninL2) x = 0 := by
      change indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1) f x = _
      rw [hcut, Set.indicator_of_notMem hx]
    rw [hzero, mul_zero]

theorem soninLogPositionPhase_mul_inv (t : ℝ) :
    soninLogPositionPhaseCLM t * soninLogPositionPhaseInvCLM t = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  exact (soninLogPositionPhaseUnitary t).apply_symm_apply f

theorem soninLogPositionPhase_inv_mul (t : ℝ) :
    soninLogPositionPhaseInvCLM t * soninLogPositionPhaseCLM t = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  exact (soninLogPositionPhaseUnitary t).symm_apply_apply f

theorem soninCentralCutoff_mul_character
    (a : SuzukiPositiveAperture) (z : ℂ) :
    soninCentralCutoff a * (z • (1 : SoninL2 →L[ℂ] SoninL2)) =
      (z • (1 : SoninL2 →L[ℂ] SoninL2)) * soninCentralCutoff a := by
  ext f
  simp [soninCentralCutoff]

/-- Exact finite-aperture Weyl law: the compressed holonomy is its central phase times the
physical aperture identity minus one escaped translation channel. -/
theorem soninCompressedWeylHolonomy_eq_character_sub_escape
    (a : SuzukiPositiveAperture) (h t : ℝ) :
    soninCompressedWeylHolonomy a h t =
      (HTGeometry.scalarWeylCharacter h (t : ℂ) • (1 : SoninL2 →L[ℂ] SoninL2)) *
        (soninCentralCutoff a - soninCentralWeylEscape a h) := by
  apply compressed_weyl_holonomy_scalar_escape
  · exact indicatorCutoff_idempotent _ _
  · exact soninLogPositionPhaseCLM_commutes_centralCutoff a t
  · exact soninLogPositionPhase_mul_inv t
  · exact soninLogPositionPhase_inv_mul t
  · exact soninCentralCutoff_mul_character a _
  · simpa [smul_mul_assoc] using soninLogPositionPhaseCLM_mul_translation h t
  · simpa [soninLogWeylGroupCommutator] using
      soninLogWeylGroupCommutator_eq_character h t

/-- The literal movable completed covariance, regarded as an aperture vector before zero extension. -/
def suzukiTaMovableCompletedCovarianceHead
    (a : SuzukiPositiveAperture) (c : ℝ) : suzukiApertureHilbert a :=
  suzukiApertureZeroExtendLinearIsometry a
    (suzukiWeilIntervalCovariance a (suzukiTaExponentialL2 a c))

theorem coe_suzukiTaMovableCompletedCovarianceHead
    (a : SuzukiPositiveAperture) (c : ℝ) :
    (suzukiTaMovableCompletedCovarianceHead a c : SoninL2) =
      suzukiTaMovableCompletedCovarianceSource a c := rfl

/-- The actual movable completed covariance is fixed by the same literal cutoff. -/
theorem soninCentralCutoff_suzukiTaMovableCompletedCovarianceSource
    (a : SuzukiPositiveAperture) (c : ℝ) :
    soninCentralCutoff a (suzukiTaMovableCompletedCovarianceSource a c) =
      suzukiTaMovableCompletedCovarianceSource a c := by
  rw [← coe_suzukiTaMovableCompletedCovarianceHead]
  exact indicatorCutoff_suzukiApertureHilbert a
    (suzukiTaMovableCompletedCovarianceHead a c)

/-- Literal Suzuki covariance holonomy is its source vector minus the one escaped channel,
weighted by the exact Weyl character. -/
theorem suzukiTaMovableCompletedCovariance_holonomy
    (a : SuzukiPositiveAperture) (c h t : ℝ) :
    soninCompressedWeylHolonomy a h t
      (suzukiTaMovableCompletedCovarianceSource a c) =
      (HTGeometry.scalarWeylCharacter h (t : ℂ) • (1 : SoninL2 →L[ℂ] SoninL2))
        ((suzukiTaMovableCompletedCovarianceSource a c) -
          soninCentralWeylEscape a h
            (suzukiTaMovableCompletedCovarianceSource a c)) := by
  have hhol := congrArg (fun T : SoninL2 →L[ℂ] SoninL2 =>
    T (suzukiTaMovableCompletedCovarianceSource a c))
    (soninCompressedWeylHolonomy_eq_character_sub_escape a h t)
  change soninCompressedWeylHolonomy a h t
      (suzukiTaMovableCompletedCovarianceSource a c) =
    (HTGeometry.scalarWeylCharacter h (t : ℂ) • (1 : SoninL2 →L[ℂ] SoninL2))
      ((soninCentralCutoff a - soninCentralWeylEscape a h)
        (suzukiTaMovableCompletedCovarianceSource a c)) at hhol
  rw [show (soninCentralCutoff a - soninCentralWeylEscape a h)
      (suzukiTaMovableCompletedCovarianceSource a c) =
      soninCentralCutoff a (suzukiTaMovableCompletedCovarianceSource a c) -
        soninCentralWeylEscape a h
          (suzukiTaMovableCompletedCovarianceSource a c) by rfl,
    soninCentralCutoff_suzukiTaMovableCompletedCovarianceSource] at hhol
  exact hhol

end

end RHTower

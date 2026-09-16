import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMStreamMetricField

/-!
# Literal bilinear stream response for the cyclic Peierls construction

The physical stream reconstruction is quadratic in its amplitude on the diagonal.  This file
constructs its unique displayed complex-bilinear polarization: no target coefficient, abstract
carrier, or propagator is introduced.  It supplies the literal symmetric quadratic residual
candidate for the still-open action-to-causal-source realization.

The remaining Peierls edge is not hidden here: one must identify this metric residual with the
full time-domain retarded-minus-advanced source channel, including the lifted-wave boundary term.
-/

open GaloisForLFunctions.HTGeometry

namespace RHTower.D4BMLiteralPeierlsStream

open D4BMHorizon D4BMFundamentalScalarMetric D4BMModularCore

noncomputable section

private theorem streamRadialField_smul (w c a : ℂ) (square : Bool) (x : Fin 4 → ℝ) :
    streamRadialField w (c * a) square x = c * streamRadialField w a square x := by
  simp only [streamRadialField, envelope_eq_exp]
  split <;> ring

private theorem streamRadialField_add (w a d : ℂ) (square : Bool) (x : Fin 4 → ℝ) :
    streamRadialField w (a + d) square x =
      streamRadialField w a square x + streamRadialField w d square x := by
  simp only [streamRadialField, envelope_eq_exp]
  split <;> ring

private theorem streamRadialDerivative_smul (w c a : ℂ) (square : Bool) (x : Fin 4 → ℝ) :
    streamRadialDerivative w (c * a) square x = c * streamRadialDerivative w a square x := by
  simp only [streamRadialDerivative, envelope_eq_exp]
  split <;> ring

private theorem streamRadialDerivative_add (w a d : ℂ) (square : Bool) (x : Fin 4 → ℝ) :
    streamRadialDerivative w (a + d) square x =
      streamRadialDerivative w a square x + streamRadialDerivative w d square x := by
  simp only [streamRadialDerivative, envelope_eq_exp]
  split <;> ring

private theorem streamMetricField_smul (w c a : ℂ) (square : Bool) (V : Covector)
    (x : Fin 4 → ℝ) :
    streamMetricField w (c * a) square V x = c • streamMetricField w a square V x := by
  have hT : streamTimeBlock w (c * a) square x = c * streamTimeBlock w a square x := by
    unfold streamTimeBlock
    rw [streamRadialDerivative_smul]
    ring
  have hR : streamRadiusBlock w (c * a) square x = c * streamRadiusBlock w a square x := by
    unfold streamRadiusBlock
    rw [streamRadialField_smul]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;> simp [streamMetricField, hT, hR] <;> ring

private theorem streamMetricField_add (w a d : ℂ) (square : Bool) (V : Covector)
    (x : Fin 4 → ℝ) :
    streamMetricField w (a + d) square V x =
      streamMetricField w a square V x + streamMetricField w d square V x := by
  have hT : streamTimeBlock w (a + d) square x =
      streamTimeBlock w a square x + streamTimeBlock w d square x := by
    unfold streamTimeBlock
    rw [streamRadialDerivative_add]
    ring
  have hR : streamRadiusBlock w (a + d) square x =
      streamRadiusBlock w a square x + streamRadiusBlock w d square x := by
    unfold streamRadiusBlock
    rw [streamRadialField_add]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;> simp [streamMetricField, hT, hR] <;> ring

/-- Exact complex-bilinear polarization of one literal stream-metric response. -/
def streamMetricBilinear (w : ℂ) (square : Bool) (V : Covector) :
    ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ((Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ) :=
  LinearMap.mk₂ ℂ (fun a d x => streamMetricField w (a * d) square V x)
    (by
      intro a b d
      funext x
      rw [show (a + b) * d = a * d + b * d by ring, streamMetricField_add]
      rfl)
    (by
      intro c a d
      funext x
      change streamMetricField w ((c * a) * d) square V x =
        c • streamMetricField w (a * d) square V x
      rw [show (c * a) * d = c * (a * d) by ring, streamMetricField_smul])
    (by
      intro a d e
      funext x
      rw [show a * (d + e) = a * d + a * e by ring, streamMetricField_add]
      rfl)
    (by
      intro c a d
      funext x
      change streamMetricField w (a * (c * d)) square V x =
        c • streamMetricField w (a * d) square V x
      rw [show a * (c * d) = c * (a * d) by ring, streamMetricField_smul])

/-- The polarization's diagonal is precisely the original squared-amplitude stream response. -/
theorem streamMetricBilinear_diag (w a : ℂ) (square : Bool) (V : Covector)
    (x : Fin 4 → ℝ) :
    streamMetricBilinear w square V a a x = streamMetricField w (a ^ 2) square V x := by
  simp only [streamMetricBilinear, LinearMap.mk₂_apply, pow_two]

/-- The literal polarized stream residual is symmetric in its two physical input amplitudes. -/
theorem streamMetricBilinear_symm (w a d : ℂ) (square : Bool) (V : Covector)
    (x : Fin 4 → ℝ) :
    streamMetricBilinear w square V a d x = streamMetricBilinear w square V d a x := by
  simp only [streamMetricBilinear, LinearMap.mk₂_apply]
  rw [mul_comm]

/-- Literal two-stream quadratic residual used by the physical mixed Einstein response. -/
def forcedMetricBilinear (q : XiZeroCopy) (branch : Bool) :
    ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ((Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ) :=
  streamMetricBilinear (2 * physicalRate q branch) false (fullAngularCovector q branch) -
    (physicalRate q branch * (physicalRate q branch - 1) / 4) •
      streamMetricBilinear (2 * physicalRate q branch) true (fullSquareCovector q)

/-- The literal mixed response residual is symmetric before imposing any causal boundary condition. -/
theorem forcedMetricBilinear_symm (q : XiZeroCopy) (branch : Bool) (a d : ℂ)
    (x : Fin 4 → ℝ) :
    forcedMetricBilinear q branch a d x = forcedMetricBilinear q branch d a x := by
  change
    streamMetricBilinear (2 * physicalRate q branch) false (fullAngularCovector q branch) a d x -
        (physicalRate q branch * (physicalRate q branch - 1) / 4) •
          streamMetricBilinear (2 * physicalRate q branch) true (fullSquareCovector q) a d x =
      streamMetricBilinear (2 * physicalRate q branch) false (fullAngularCovector q branch) d a x -
        (physicalRate q branch * (physicalRate q branch - 1) / 4) •
          streamMetricBilinear (2 * physicalRate q branch) true (fullSquareCovector q) d a x
  have hA := streamMetricBilinear_symm (2 * physicalRate q branch) a d false
    (fullAngularCovector q branch) x
  have hB := streamMetricBilinear_symm (2 * physicalRate q branch) a d true
    (fullSquareCovector q) x
  rw [hA, hB]

/-- On the diagonal the literal bilinear residual recovers the two-stream quadratic field. -/
theorem forcedMetricBilinear_diag (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (x : Fin 4 → ℝ) :
    forcedMetricBilinear q branch a a x =
      streamMetricField (2 * physicalRate q branch) (a ^ 2) false
          (fullAngularCovector q branch) x -
        (physicalRate q branch * (physicalRate q branch - 1) / 4) •
          streamMetricField (2 * physicalRate q branch) (a ^ 2) true
            (fullSquareCovector q) x := by
  change
    streamMetricBilinear (2 * physicalRate q branch) false (fullAngularCovector q branch) a a x -
        (physicalRate q branch * (physicalRate q branch - 1) / 4) •
          streamMetricBilinear (2 * physicalRate q branch) true (fullSquareCovector q) a a x = _
  rw [streamMetricBilinear_diag, streamMetricBilinear_diag]

end

end RHTower.D4BMLiteralPeierlsStream

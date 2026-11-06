import GaloisForLFunctions.BlackHoleRingdown.TheSharpAnalyticBoundary
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Gaussian probes preserve the sharp resonance boundary

A Gaussian pulse has an entire, nowhere-vanishing frequency transform. Multiplication by this
transform preserves all meromorphic orders and local analyticity. Thus a fixed Gaussian probe
retains every arithmetic pole and the same RH-equivalent analytic half-plane as the causal symbol.
The pulse is bilateral; the result makes no claim of compact causal support.
-/

open Complex Filter Topology
noncomputable section
namespace GaloisForLFunctions.BlackHoleRingdown
open _root_.RHTower

/-- A Gaussian spectral multiplier, with no zero anywhere in the complex plane. -/
def gaussianSpectralProbe (σ : ℝ) (ω : ℂ) : ℂ := Complex.exp (-(σ : ℂ) * ω ^ 2)

/-- The normalized response observed through a Gaussian spectral probe. -/
def gaussianResponse (σ D : ℝ) (ω : ℂ) : ℂ :=
  gaussianSpectralProbe σ ω * causalSymbol D ω

theorem gaussianSpectralProbe_analyticAt (σ : ℝ) (ω : ℂ) :
    AnalyticAt ℂ (gaussianSpectralProbe σ) ω := by
  unfold gaussianSpectralProbe
  fun_prop

theorem gaussianSpectralProbe_ne_zero (σ : ℝ) (ω : ℂ) :
    gaussianSpectralProbe σ ω ≠ 0 := Complex.exp_ne_zero _

/-- The probe is the transform of a real Gaussian pulse, up to its nonzero mass factor. -/
theorem gaussianPulse_transform {σ : ℝ} (hσ : 0 < σ) (ω : ℂ) :
    (∫ t : ℝ, Complex.exp (I * ω * t) * Complex.exp (-(σ : ℂ) * (t : ℂ) ^ 2)) =
      ((Real.pi : ℂ) / σ) ^ (1 / 2 : ℂ) * gaussianSpectralProbe (1 / (4 * σ)) ω := by
  rw [fourierIntegral_gaussian (by exact hσ : 0 < (σ : ℂ).re), gaussianSpectralProbe]
  congr 1
  congr 1
  push_cast
  ring

/-- Along each horizontal line the probe has exact Gaussian decay in real frequency. -/
theorem norm_gaussianSpectralProbe (σ : ℝ) (ω : ℂ) :
    ‖gaussianSpectralProbe σ ω‖ = Real.exp (σ * (ω.im ^ 2 - ω.re ^ 2)) := by
  rw [gaussianSpectralProbe, Complex.norm_exp]
  congr 1
  simp [pow_two, Complex.mul_re]
  ring

/-- Spectral smoothing preserves every zero and pole order. -/
theorem gaussianResponse_meromorphicOrderAt (σ D : ℝ) (ω : ℂ) :
    meromorphicOrderAt (gaussianResponse σ D) ω = meromorphicOrderAt (causalSymbol D) ω := by
  exact meromorphicOrderAt_mul_of_ne_zero
    (gaussianSpectralProbe_analyticAt σ ω) (gaussianSpectralProbe_ne_zero σ ω)

theorem gaussianResponse_analyticAt_iff (σ D : ℝ) (ω : ℂ) :
    AnalyticAt ℂ (gaussianResponse σ D) ω ↔ AnalyticAt ℂ (causalSymbol D) ω := by
  constructor
  · intro h
    have hd := h.div (gaussianSpectralProbe_analyticAt σ ω) (gaussianSpectralProbe_ne_zero σ ω)
    convert hd using 1
    funext w
    simp [gaussianResponse, gaussianSpectralProbe_ne_zero, mul_div_cancel_left₀]
  · intro h
    exact (gaussianSpectralProbe_analyticAt σ ω).mul h

/-- No Gaussian probe can miss a nontrivial zeta resonance. -/
theorem gaussianResponse_isPole_iff (σ D : ℝ) (ω : ℂ) :
    meromorphicOrderAt (gaussianResponse σ D) ω < 0 ↔
      ∃ q : XiZeroCopy, ω = resonanceFrequency D (xiSpectralPoint q) := by
  rw [gaussianResponse_meromorphicOrderAt, causalSymbol_isPole_iff]

/-- One fixed Gaussian probe has exactly the same sharp analytic boundary as the full symbol. -/
theorem riemannHypothesis_iff_gaussianResponse_analytic (σ D : ℝ) :
    RiemannHypothesis ↔
      AnalyticOnNhd ℂ (gaussianResponse σ D) {ω : ℂ | -(D + 1 / 4) < ω.im} := by
  rw [riemannHypothesis_iff_causalSymbol_analytic D]
  exact forall_congr' fun ω => imp_congr_right fun _ =>
    (gaussianResponse_analyticAt_iff σ D ω).symm

#print axioms gaussianPulse_transform
#print axioms norm_gaussianSpectralProbe
#print axioms gaussianResponse_meromorphicOrderAt
#print axioms riemannHypothesis_iff_gaussianResponse_analytic

end GaloisForLFunctions.BlackHoleRingdown

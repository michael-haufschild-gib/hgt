import GaloisForLFunctions.HTGeometry.ComplexAnalysis.CompensatedSlices
import GaloisForLFunctions.HTGeometry.ComplexAnalysis.BallPowerMass
import GaloisForLFunctions.HTGeometry.ComplexAnalysis.HolomorphicL2Flatness
import GaloisForLFunctions.HTGeometry.EntireFunctionField
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.CuspAveragesAndBesselMellin

/-!
# Holomorphic compensation of cubic cusp Fourier modes

A trace character has constant antiholomorphic logarithmic derivative. Multiplication by any
holomorphic polynomial preserves that derivative. In particular, monomial multiples have
arbitrarily high finite vanishing order while the differential-inequality potential stays fixed.
This distinguishes finite-order zeros from the infinite-order hypothesis in strong unique
continuation. The same identity applies to every horizontal Bessel Fourier term.
-/

noncomputable section

open Complex HTGeometry MeasureTheory Filter Set Topology

namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

/-- The antiholomorphic coefficient of the trace-character exponent. -/
theorem wirtingerAntihol_horizontalPhaseCLM (freq : ℂ) :
    wirtingerAntihol (horizontalPhaseCLM freq) =
      2 * Real.pi * Complex.I * star freq := by
  rw [wirtingerAntihol, horizontalPhaseCLM_apply, horizontalPhaseCLM_apply]
  have h := horizontalPhaseMultiplier_wirtinger freq
  simpa only [horizontalPhaseMultiplier, div_eq_mul_inv, one_div, mul_comm] using h

/-- Every trace character solves a constant-coefficient `∂̄` equation. -/
theorem dzbar_tracePhase (freq z : ℂ) :
    dzbar (fun w => tracePhase (freq * w)) z =
      (2 * Real.pi * Complex.I * star freq) * tracePhase (freq * z) := by
  rw [dzbar_eq_of_hasFDerivAt (tracePhase_hasFDerivAt freq z),
    wirtingerAntihol_smul, wirtingerAntihol_horizontalPhaseCLM, mul_comm]

/-- A monomial-compensated trace mode. -/
def compensatedTraceMode (m : ℕ) (freq z : ℂ) : ℂ := z ^ m * tracePhase (freq * z)

/-- Monomial compensation leaves the trace mode's antiholomorphic potential unchanged. -/
theorem dzbar_compensatedTraceMode (m : ℕ) (freq z : ℂ) :
    dzbar (compensatedTraceMode m freq) z =
      (2 * Real.pi * Complex.I * star freq) * compensatedTraceMode m freq z := by
  unfold compensatedTraceMode
  rw [dzbar_pow_mul (tracePhase_hasFDerivAt freq z).differentiableAt, dzbar_tracePhase]
  ring

/-- The exact amplitude records the finite vanishing order. -/
theorem norm_compensatedTraceMode (m : ℕ) (freq z : ℂ) :
    ‖compensatedTraceMode m freq z‖ = ‖z‖ ^ m := by
  rw [compensatedTraceMode, norm_mul, norm_pow, tracePhase_norm, mul_one]

/-- Every compensated mode is nonzero at the unit point. -/
theorem compensatedTraceMode_one_ne_zero (m : ℕ) (freq : ℂ) :
    compensatedTraceMode m freq 1 ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_compensatedTraceMode, norm_one, one_pow]
  exact one_ne_zero

/-- All positive compensation degrees vanish at the origin. -/
theorem compensatedTraceMode_succ_zero (m : ℕ) (freq : ℂ) :
    compensatedTraceMode (m + 1) freq 0 = 0 := by
  simp only [compensatedTraceMode, zero_pow (Nat.succ_ne_zero m), zero_mul]

/-- The potential has no dependence on the vanishing order. -/
theorem norm_dzbar_compensatedTraceMode (m : ℕ) (freq z : ℂ) :
    ‖dzbar (compensatedTraceMode m freq) z‖ =
      (2 * Real.pi * ‖freq‖) * ‖compensatedTraceMode m freq z‖ := by
  rw [dzbar_compensatedTraceMode, norm_mul]
  congr 1
  simp only [norm_mul, norm_star, Complex.norm_I, mul_one, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- Polynomial envelopes preserve the same equation, including at their zeros. -/
theorem dzbar_polynomial_tracePhase (P : Polynomial ℂ) (freq z : ℂ) :
    dzbar (fun w => P.eval w * tracePhase (freq * w)) z =
      (2 * Real.pi * Complex.I * star freq) * (P.eval z * tracePhase (freq * z)) := by
  rw [dzbar_holomorphic_mul P.differentiableAt
    (tracePhase_hasFDerivAt freq z).differentiableAt, dzbar_tracePhase]
  ring

/-- The Bessel amplitude depends only on height, so every horizontal Fourier term has the
same constant antiholomorphic potential as its trace character. -/
theorem dzbar_cubicBesselTerm (c : Eisenstein.O → ℂ) (h : Eisenstein.O) (v : ℝ) (z : ℂ) :
    dzbar (fun w => cubicBesselTerm c h (v, w)) z =
      (2 * Real.pi * Complex.I * star (cuspFrequency h)) * cubicBesselTerm c h (v, z) := by
  change dzbar (fun w => cubicBesselAmplitude c v h * tracePhase (cuspFrequency h * w)) z = _
  rw [dzbar_holomorphic_mul (differentiableAt_const _)
    (tracePhase_hasFDerivAt (cuspFrequency h) z).differentiableAt, dzbar_tracePhase]
  unfold cubicBesselTerm
  ring

/-- Holomorphic polynomial compensation of a Bessel mode introduces no degree loss. -/
theorem dzbar_polynomial_cubicBesselTerm (P : Polynomial ℂ)
    (c : Eisenstein.O → ℂ) (h : Eisenstein.O) (v : ℝ) (z : ℂ) :
    dzbar (fun w => P.eval w * cubicBesselTerm c h (v, w)) z =
      (2 * Real.pi * Complex.I * star (cuspFrequency h)) *
        (P.eval z * cubicBesselTerm c h (v, z)) := by
  have hd : DifferentiableAt ℝ (fun w => cubicBesselTerm c h (v, w)) z :=
    (tracePhase_hasFDerivAt (cuspFrequency h) z).differentiableAt.const_mul _
  rw [dzbar_holomorphic_mul P.differentiableAt hd, dzbar_cubicBesselTerm]
  ring

/-- The local squared mass has exact order `2*m+2`, independently of the frequency. -/
theorem integral_ball_norm_compensatedTraceMode_sq (m : ℕ) (freq : ℂ) (R : NNReal) :
    (∫ z in Metric.ball (0 : ℂ) R, ‖compensatedTraceMode m freq z‖ ^ 2) =
      Real.pi * (R : ℝ) ^ (2 * m + 2) / (m + 1) := by
  simp only [norm_compensatedTraceMode, ← pow_mul, Nat.mul_comm m 2]
  exact GaloisForLFunctions.HTGeometry.integral_ball_norm_even_pow m R

/-- The critical rescaled mass stays positive instead of tending to zero. -/
theorem compensatedTraceMode_mass_not_flat (m : ℕ) (freq : ℂ) :
    ¬ Tendsto
      (fun r : ℝ => (∫ z in Metric.ball (0 : ℂ) r,
        ‖compensatedTraceMode m freq z‖ ^ 2) / r ^ (2 * m + 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have heq : (fun r : ℝ => (∫ z in Metric.ball (0 : ℂ) r,
      ‖compensatedTraceMode m freq z‖ ^ 2) / r ^ (2 * m + 2))
      =ᶠ[𝓝[>] (0 : ℝ)] fun _ => Real.pi / (m + 1) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : 0 < r := hr
    rw [integral_ball_norm_compensatedTraceMode_sq m freq ⟨r, hr0.le⟩]
    have hpow : r ^ (2 * m + 2) ≠ 0 := pow_ne_zero _ hr0.ne'
    field_simp
  intro h
  have hconst : Tendsto (fun _ : ℝ => Real.pi / (m + 1))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := h.congr' heq
  have he := tendsto_nhds_unique hconst tendsto_const_nhds
  have hpos : 0 < Real.pi / (m + 1 : ℝ) := by positivity
  exact (ne_of_gt hpos) he.symm

/-- A unit-modulus trace character preserves local L² flatness at every point. -/
theorem l2FlatAt_mul_tracePhase_iff (f : ℂ → ℂ) (freq a : ℂ) :
    GaloisForLFunctions.HTGeometry.L2FlatAt (fun z => f z * tracePhase (freq * z)) a ↔
      GaloisForLFunctions.HTGeometry.L2FlatAt f a := by
  simp only [GaloisForLFunctions.HTGeometry.L2FlatAt, norm_mul, tracePhase_norm, mul_one]

/-- An entire envelope times a trace character is flat precisely when the envelope vanishes. -/
theorem l2FlatAt_entire_tracePhase_iff
    (f : GaloisForLFunctions.HTGeometry.entireSubring ℂ) (freq a : ℂ) :
    GaloisForLFunctions.HTGeometry.L2FlatAt
      (fun z => f z * tracePhase (freq * z)) a ↔ f = 0 := by
  rw [l2FlatAt_mul_tracePhase_iff,
    GaloisForLFunctions.HTGeometry.l2FlatAt_iff_eq_zero_of_entire f.property]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

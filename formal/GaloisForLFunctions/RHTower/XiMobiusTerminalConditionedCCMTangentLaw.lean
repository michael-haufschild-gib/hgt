import GaloisForLFunctions.RHTower.XiMobiusContinuousApertureCCMTangent
import GaloisForLFunctions.RHTower.XiMobiusTerminalConditionedApertureMetric

/-!
# Terminal-conditioned Möbius aperture tangents retain the CCM channels

Terminal conditioning multiplies the all-prime aperture tangent by two prime-independent
pseudohyperbolic boundary factors.  The unconditioned tangent is exactly the CCM
prime--polar--critical-Mellin colligation.  Consequently conditioning suppresses every channel by
the same boundary filter and cannot alter their signed relative decomposition.
-/

open Filter

noncomputable section

namespace RHTower

/-- **Exact terminal-conditioned CCM tangent.**  The terminal-conditioned limiting kernel is the
old CCM colligation multiplied by the two aperture-boundary factors; no new prime channel is
created by the Schur complement. -/
theorem xiMobiusTerminalConditionedApertureSlopeShape_eq_ccm
    {A a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ((xiMobiusContinuousApertureSlopeConstant *
        xiMobiusTerminalConditionedApertureCauchyShape A a b : ℝ) : ℂ) =
      (((A - a) / (A + a) : ℝ) : ℂ) *
        (((A - b) / (A + b) : ℝ) : ℂ) *
        ((xiMobiusContinuousApertureSlopeConstant : ℂ) * ((a * b : ℝ) : ℂ) *
          (vonMangoldtPrimeLaplaceChannelComplex (((a + b : ℝ) : ℂ)) -
            1 / (((a + b : ℝ) : ℂ) + 1) +
            criticalMellinDefectLaplaceChannelComplex (((a + b : ℝ) : ℂ)))) := by
  have hbase := xiMobiusContinuousApertureSlopeKernel_eq_ccm ha hb
  calc
    ((xiMobiusContinuousApertureSlopeConstant *
        xiMobiusTerminalConditionedApertureCauchyShape A a b : ℝ) : ℂ) =
        ((xiMobiusContinuousApertureSlopeConstant * (a * b / (a + b)) : ℝ) : ℂ) *
          (((A - a) / (A + a) : ℝ) : ℂ) *
          (((A - b) / (A + b) : ℝ) : ℂ) := by
            simp only [xiMobiusTerminalConditionedApertureCauchyShape]
            push_cast
            ring
    _ = _ := by rw [hbase]; ring

/-- **Terminal-conditioned CCM channel limit.**  The true all-prime Schur-complement kernel,
after critical aperture rescaling, converges directly to the uniformly boundary-filtered CCM
prime--polar--critical-Mellin colligation. -/
theorem tendsto_xiMobiusTerminalConditionedApertureKernel_ccm_nhdsGT_zero
    {A a b : ℝ} (hA : 0 < A) (ha : 0 < a) (hb : 0 < b)
    (haA : a < A) (hbA : b < A) :
    Tendsto
      (fun t : ℝ =>
        ((xiMobiusTerminalConditionedApertureKernel (t * A) (t * a) (t * b) / t : ℝ) : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (
        (((A - a) / (A + a) : ℝ) : ℂ) *
          (((A - b) / (A + b) : ℝ) : ℂ) *
          ((xiMobiusContinuousApertureSlopeConstant : ℂ) * ((a * b : ℝ) : ℂ) *
            (vonMangoldtPrimeLaplaceChannelComplex (((a + b : ℝ) : ℂ)) -
              1 / (((a + b : ℝ) : ℂ) + 1) +
              criticalMellinDefectLaplaceChannelComplex (((a + b : ℝ) : ℂ)))))) := by
  have hreal := tendsto_xiMobiusTerminalConditionedApertureKernel_mul_div_nhdsGT_zero
    hA ha hb haA hbA
  have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  rw [xiMobiusTerminalConditionedApertureSlopeShape_eq_ccm ha hb] at hcomplex
  exact hcomplex

end RHTower

end

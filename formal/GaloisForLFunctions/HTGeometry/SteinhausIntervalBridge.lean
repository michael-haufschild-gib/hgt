import GaloisForLFunctions.HTGeometry.SteinhausCumulantLower

/-!
# The circle Laplace transform as an interval integral

`steinhausLaplace r = (1/2π)∫₀^{2π} e^{r cos t} dt`.  This identifies the abstract Haar integral
with the classical Bessel integral, which is what every sharp envelope for `log I₀` is proved from.
-/

open MeasureTheory Set

namespace HTGeometry

local instance phaseCirclePositiveBridge : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

noncomputable section

/-- The projection of a real point of the circle is the cosine. -/
theorem steinhausProjection_coe (t : ℝ) :
    steinhausProjection ((t : ℝ) : PhaseCircle) = Real.cos t := by
  rw [steinhausProjection, steinhausPhase, fourier_coe_apply]
  have harg : (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℤ) : ℂ) * (t : ℂ)) / ((2 * Real.pi : ℝ) : ℂ)
      = (t : ℂ) * Complex.I := by
    have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
      simp only [Complex.ofReal_ne_zero]
      positivity
    push_cast
    field_simp
  rw [harg, Complex.exp_ofReal_mul_I_re]

/-- **The Haar integral is the classical Bessel integral.** -/
theorem steinhausLaplace_eq_intervalIntegral (r : ℝ) :
    steinhausLaplace r
      = (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..(2 * Real.pi), Real.exp (r * Real.cos t) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hvol : (volume : Measure PhaseCircle)
      = ENNReal.ofReal (2 * Real.pi) • AddCircle.haarAddCircle :=
    AddCircle.volume_eq_smul_haarAddCircle
  have hpre := AddCircle.integral_preimage (2 * Real.pi) 0
    (fun x : PhaseCircle => Real.exp (r * steinhausProjection x))
  have hleft : (∫ a in Set.Ioc (0 : ℝ) (0 + 2 * Real.pi),
      Real.exp (r * steinhausProjection ((a : ℝ) : PhaseCircle)))
      = ∫ t in (0 : ℝ)..(2 * Real.pi), Real.exp (r * Real.cos t) := by
    rw [intervalIntegral.integral_of_le (by positivity)]
    simp only [zero_add]
    exact setIntegral_congr_fun measurableSet_Ioc fun a _ => by
      rw [steinhausProjection_coe]
  rw [hleft] at hpre
  have hright : (∫ b : PhaseCircle, Real.exp (r * steinhausProjection b))
      = (2 * Real.pi) * steinhausLaplace r := by
    rw [steinhausLaplace, hvol, integral_smul_measure,
      ENNReal.toReal_ofReal hpi.le, smul_eq_mul]
  rw [hright] at hpre
  rw [hpre]
  field_simp

end

end HTGeometry

import GaloisForLFunctions.HTGeometry.ConductorCausalSuperposition
import GaloisForLFunctions.HTGeometry.ConductorKernelFubini

/-!
# From the causal pair form to the Hankel form

On a core of anticausal sources and causal readers the convolution pairing against a one-sided
exponential is literally a Hankel form: the reflection `s = -v` turns the difference `t - s` into
the sum `t + v`, and the one-sided support makes the two half lines the whole domain.

Integrating the rank-one Hankel kernels over the rate then produces the conductor kernel, whose
form is bounded by the Carleman/Hilbert inequality.
-/

open Complex Real Set Filter Topology MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem causalFourierExponential_eval {a r : ℝ} (hr : 0 < r) :
    RHTower.causalFourierExponential a r
      = (Real.pi : ℂ) * Complex.exp (-(Real.pi * a : ℝ) * r) := by
  rw [RHTower.causalFourierExponential, Set.indicator_of_mem (Set.mem_Ioi.mpr hr)]

theorem causalFourierExponential_eval_nonpos {a r : ℝ} (hr : r ≤ 0) :
    RHTower.causalFourierExponential a r = 0 := by
  rw [RHTower.causalFourierExponential,
    Set.indicator_of_notMem (by simpa using not_lt.mpr hr)]

/-- Reflecting the half line. -/
theorem setIntegral_Iio_neg (f : ℝ → ℂ) :
    (∫ s in Iio (0:ℝ), f s) = ∫ v in Ioi (0:ℝ), f (-v) := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
    (Homeomorph.neg ℝ).measurableEmbedding f (Iio 0)
  simpa [show (fun v : ℝ => -v) ⁻¹' (Iio (0:ℝ)) = Ioi (0:ℝ) by ext v; simp] using h.symm

/-- **The reflection turns a difference kernel into a sum kernel.** -/
theorem hankel_substitution (a : ℝ) (φ ψ : ℝ → ℂ) :
    (∫ t in Ioi (0:ℝ), ∫ s in Iio (0:ℝ),
        RHTower.causalFourierExponential a (t - s) * φ s * (starRingEnd ℂ) (ψ t))
      = ∫ t in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
          RHTower.causalFourierExponential a (t + v) * φ (-v) * (starRingEnd ℂ) (ψ t) := by
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  rw [setIntegral_Iio_neg]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
  congr 3
  ring

/-- **The causal pair form is a Hankel form.**  On the core, the kernel value is the explicit
rank-one exponential in the sum variable. -/
theorem hankel_substitution_eval (a : ℝ) (φ ψ : ℝ → ℂ) :
    (∫ t in Ioi (0:ℝ), ∫ s in Iio (0:ℝ),
        RHTower.causalFourierExponential a (t - s) * φ s * (starRingEnd ℂ) (ψ t))
      = ∫ t in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
          (Real.pi : ℂ) * Complex.exp (-(Real.pi * a : ℝ) * (t + v))
            * φ (-v) * (starRingEnd ℂ) (ψ t) := by
  rw [hankel_substitution]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
  have ht0 : (0 : ℝ) < t := ht
  have hv0 : (0 : ℝ) < v := hv
  rw [causalFourierExponential_eval (by linarith : (0:ℝ) < t + v)]
  push_cast
  ring

end GaloisForLFunctions.HTGeometry

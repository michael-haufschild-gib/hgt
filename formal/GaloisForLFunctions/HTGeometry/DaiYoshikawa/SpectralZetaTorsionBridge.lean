import GaloisForLFunctions.HTGeometry.DaiYoshikawa.SpectralZetaDerivative
import GaloisForLFunctions.HTGeometry.DaiYoshikawa.RegularizedLogDeterminant

/-!
# `ζ'(0)` is the regularized log-determinant

The two halves of the construction meet here.  `RegularizedLogDeterminant` defines the regularized
logarithm of a determinant by formula (3.3) of Dai–Yoshikawa, *Degeneration of Riemann surfaces and
small eigenvalues of the Laplacian* (arXiv:2509.06151v2), as a pair of convergent real integrals;
`SpectralZetaDerivative` computes the derivative at the origin of the continued spectral zeta
function.  Evaluating the two Mellin pieces at `s = 0` turns the second into the first:

```text
ζ'(0) = ∫_0^(1 : ℕ) (Θ(t) − a₀/t − a₁) dt/t + ∫_1^∞ (Θ(t) − h) dt/t − a₀ + (a₁ − h) γ .
```

So the zeta-regularized log-determinant *is* the pair of integrals of (3.3), up to the explicit
constant `−a₀ + (a₁ − h)γ`.
-/

open MeasureTheory Set Filter Real Complex Topology

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

/-- The head Mellin integral at the origin. -/
theorem mellinHead_zero (g : ℝ → ℂ) :
    mellinHead g 0 = ∫ t in Ioc (0 : ℝ) 1, (t : ℂ)⁻¹ • g t := by
  rw [mellinHead_eq_setIntegral]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  rw [show ((0 : ℂ) - 1) = (-1 : ℂ) by ring, Complex.cpow_neg_one]

/-- The tail Mellin integral at the origin. -/
theorem mellinTail_zero (g : ℝ → ℂ) :
    mellinTail g 0 = ∫ t in Ioi (1 : ℝ), (t : ℂ)⁻¹ • g t := by
  rw [mellinTail_eq_setIntegral]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [show ((0 : ℂ) - 1) = (-1 : ℂ) by ring, Complex.cpow_neg_one]

/-- The head Mellin integral at the origin, for a real integrand, is the head of (3.3). -/
theorem mellinHead_zero_ofReal (Θ : ℝ → ℝ) (A₀ A₁ : ℝ) :
    mellinHead (fun t => ((Θ t - A₀ / t - A₁ : ℝ) : ℂ)) 0 = ((torsionHead Θ A₀ A₁ : ℝ) : ℂ) := by
  rw [mellinHead_zero, torsionHead]
  rw [← integral_complex_ofReal]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  rw [smul_eq_mul]
  push_cast
  ring

/-- The tail Mellin integral at the origin, for a real integrand, is the tail of (3.3). -/
theorem mellinTail_zero_ofReal (Θ : ℝ → ℝ) (H : ℝ) :
    mellinTail (fun t => ((Θ t - H : ℝ) : ℂ)) 0 = ((torsionTail Θ H : ℝ) : ℂ) := by
  rw [mellinTail_zero, torsionTail]
  rw [← integral_complex_ofReal]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [smul_eq_mul]
  push_cast
  ring

/-- **`ζ'(0)` in terms of the two integrals of (3.3).** -/
theorem deriv_zetaCont_zero_ofReal {Θ : ℝ → ℝ} {A₀ A₁ H : ℝ}
    (hhead : DifferentiableAt ℂ (mellinHead fun t => ((Θ t - A₀ / t - A₁ : ℝ) : ℂ)) 0)
    (htail : DifferentiableAt ℂ (mellinTail fun t => ((Θ t - H : ℝ) : ℂ)) 0) :
    deriv (zetaCont (fun t => ((Θ t - A₀ / t - A₁ : ℝ) : ℂ)) (fun t => ((Θ t - H : ℝ) : ℂ))
        (A₀ : ℂ) (A₁ : ℂ) (H : ℂ)) 0
      = ((torsionHead Θ A₀ A₁ + torsionTail Θ H - A₀
          + (A₁ - H) * Real.eulerMascheroniConstant : ℝ) : ℂ) := by
  rw [(hasDerivAt_zetaCont_zero hhead htail).deriv,
    mellinHead_zero_ofReal, mellinTail_zero_ofReal]
  push_cast
  ring

end GaloisForLFunctions.HTGeometry.DaiYoshikawa

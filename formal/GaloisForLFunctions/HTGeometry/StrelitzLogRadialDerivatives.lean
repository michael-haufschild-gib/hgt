import GaloisForLFunctions.HTGeometry.StrelitzLogJetReduction
import GaloisForLFunctions.RHTower.LogModulusHorizontal
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Log-radial derivatives for the Strelitz jet

The logarithmic radius through `z` based at `x` is

`t ↦ exp(t - x) z`.

Its velocity at `x` is exactly `z`.  Consequently the real derivative of
`log ‖f‖` along this path is the real part of the Euler logarithmic derivative
`u = z f'/f`, while the derivative of `Re u` is the real part of the second
Euler jet `v = z u'`.  These are the exact differential identities used when
the local Newton alternatives are integrated along radial components.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

/-- Logarithmic radial path through `z`, normalized to pass through `z` at `x`. -/
def logRadialPath (x : ℝ) (z : ℂ) : ℝ → ℂ :=
  fun t => Complex.exp ((t : ℂ) - (x : ℂ)) * z

@[simp]
theorem logRadialPath_self (x : ℝ) (z : ℂ) :
    logRadialPath x z x = z := by
  simp [logRadialPath]

/-- Velocity of the normalized logarithmic radial path at its base point. -/
theorem hasDerivAt_logRadialPath (x : ℝ) (z : ℂ) :
    HasDerivAt (logRadialPath x z) z x := by
  have hlin : HasDerivAt (fun s : ℂ => s - (x : ℂ)) 1 (x : ℂ) := by
    simpa using (hasDerivAt_id (x : ℂ)).sub_const (x : ℂ)
  have hcomplex : HasDerivAt
      (fun s : ℂ => Complex.exp (s - (x : ℂ)) * z) z (x : ℂ) := by
    simpa using hlin.cexp.mul_const z
  convert hcomplex.comp_ofReal using 1
  rfl

/-- Along logarithmic radius, `log ‖f‖` has derivative `Re(z f'/f)`. -/
theorem hasDerivAt_log_norm_logRadialPath
    {f : ℂ → ℂ} {x : ℝ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hfz : f z ≠ 0) :
    HasDerivAt (fun t => Real.log ‖f (logRadialPath x z t)‖)
      (eulerLogDeriv f z).re x := by
  have hf' : HasDerivAt f (deriv f z) (logRadialPath x z x) := by
    simpa using hf.hasDerivAt
  have hcomp : HasDerivAt (fun t => f (logRadialPath x z t)) (deriv f z * z) x := by
    exact hf'.comp x (hasDerivAt_logRadialPath x z)
  have hlog := RHTower.hasDerivAt_log_norm_comp hcomp (by simpa using hfz)
  simpa [eulerLogDeriv, mul_comm] using hlog

/-- Along logarithmic radius, the Euler logarithmic derivative has derivative
the second Euler jet. -/
theorem hasDerivAt_eulerLogDeriv_logRadialPath
    {f : ℂ → ℂ} {x : ℝ} {z : ℂ}
    (hu : DifferentiableAt ℂ (eulerLogDeriv f) z) :
    HasDerivAt (fun t => eulerLogDeriv f (logRadialPath x z t))
      (eulerLogDerivSecond f z) x := by
  have hu' : HasDerivAt (eulerLogDeriv f) (deriv (eulerLogDeriv f) z)
      (logRadialPath x z x) := by
    simpa using hu.hasDerivAt
  have hcomp := hu'.comp x (hasDerivAt_logRadialPath x z)
  simpa [Function.comp_def, eulerLogDerivSecond, mul_comm] using hcomp

/-- Real-part form of the second log-radial identity. -/
theorem hasDerivAt_re_eulerLogDeriv_logRadialPath
    {f : ℂ → ℂ} {x : ℝ} {z : ℂ}
    (hu : DifferentiableAt ℂ (eulerLogDeriv f) z) :
    HasDerivAt (fun t => (eulerLogDeriv f (logRadialPath x z t)).re)
      (eulerLogDerivSecond f z).re x := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
    (hasDerivAt_eulerLogDeriv_logRadialPath hu)

end

end GaloisForLFunctions.HTGeometry

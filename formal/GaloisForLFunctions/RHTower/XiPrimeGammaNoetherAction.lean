import GaloisForLFunctions.HTGeometry.ReciprocalScaleDrivenAction
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspPrimeArchSourceEquation

/-!
# The prime--Gamma equation as a canonical Noether system

On the zero-free Euler line `w = 1 + I t`, the complete theta transform
and its reciprocal form a canonical pair. Their coefficient is the literal
Gamma/pole symbol minus the full von Mangoldt Dirichlet series, multiplied
by `I` for differentiation along this line.

The actual arithmetic source equation gives both canonical equations.
Reciprocal scaling preserves the driven action and its conserved charge is
one. The action vanishes along these trajectories, while varying the
independent coefficient with the trajectory fixed has nonzero response.
-/

noncomputable section

namespace RHTower.ThetaSourceWard

open Complex
open GaloisForLFunctions.HTGeometry

/-- A fixed zero-free Euler line in centered Laplace coordinates. -/
def xiPrimeGammaNoetherCoordinate (t : ℝ) : ℂ := 1 + I * (t : ℂ)

/-- Literal prime, Gamma, and pole coefficient governing the canonical pair. -/
def xiPrimeGammaNoetherRate (t : ℝ) : ℂ :=
  I * (archSymbol (xiPrimeGammaNoetherCoordinate t) -
    primeSymbol (xiPrimeGammaNoetherCoordinate t))

/-- The completed arithmetic source and its reciprocal along the Euler line. -/
def xiPrimeGammaNoetherPath (t : ℝ) : ℂ × ℂ :=
  (bilateralLaplace thetaCuspTiltSource (xiPrimeGammaNoetherCoordinate t),
    (bilateralLaplace thetaCuspTiltSource (xiPrimeGammaNoetherCoordinate t))⁻¹)

theorem xiPrimeGammaNoetherCoordinate_re (t : ℝ) :
    (xiPrimeGammaNoetherCoordinate t).re = 1 := by
  simp [xiPrimeGammaNoetherCoordinate]

theorem xiPrimeGammaNoetherPath_fst_ne_zero (t : ℝ) :
    (xiPrimeGammaNoetherPath t).1 ≠ 0 := by
  change bilateralLaplace thetaCuspTiltSource (xiPrimeGammaNoetherCoordinate t) ≠ 0
  rw [bilateralLaplace_thetaCuspTiltSource_eq_xiCent]
  apply xi_ne_zero_of_one_le_re
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re,
    xiPrimeGammaNoetherCoordinate_re]
  norm_num

/-- The forward Hamilton equation is the actual arithmetic source equation. -/
theorem hasDerivAt_xiPrimeGammaNoetherPath_fst (t : ℝ) :
    HasDerivAt (fun u => (xiPrimeGammaNoetherPath u).1)
      (xiPrimeGammaNoetherRate t * (xiPrimeGammaNoetherPath t).1) t := by
  have hw : 1 / 2 < (xiPrimeGammaNoetherCoordinate t).re := by
    rw [xiPrimeGammaNoetherCoordinate_re]
    norm_num
  have ha : HasDerivAt (fun u : ℂ => 1 + I * u) I (t : ℂ) := by
    simpa using ((hasDerivAt_id (t : ℂ)).const_mul I).const_add 1
  have h := ((hasDerivAt_bilateralLaplace thetaCuspTiltSource
    (xiPrimeGammaNoetherCoordinate t)).comp (t : ℂ) ha).comp_ofReal
  convert! h using 1
  rw [source_symbol_identity hw]
  unfold xiPrimeGammaNoetherRate xiPrimeGammaNoetherPath
  ring

/-- The reciprocal solves the adjoint Hamilton equation with the same arithmetic coefficient. -/
theorem hasDerivAt_xiPrimeGammaNoetherPath_snd (t : ℝ) :
    HasDerivAt (fun u => (xiPrimeGammaNoetherPath u).2)
      (-xiPrimeGammaNoetherRate t * (xiPrimeGammaNoetherPath t).2) t := by
  have h := (hasDerivAt_xiPrimeGammaNoetherPath_fst t).inv
    (xiPrimeGammaNoetherPath_fst_ne_zero t)
  convert! h using 1
  change -xiPrimeGammaNoetherRate t * ((xiPrimeGammaNoetherPath t).1)⁻¹ = _
  field_simp

/-- Unit charge is conserved along the literal prime--Gamma canonical solution. -/
theorem xiPrimeGammaNoetherCharge (t : ℝ) :
    reciprocalScaleCharge (xiPrimeGammaNoetherPath t) = 1 :=
  mul_inv_cancel₀ (xiPrimeGammaNoetherPath_fst_ne_zero t)

theorem hasDerivAt_xiPrimeGammaNoetherCharge (t : ℝ) :
    HasDerivAt (fun u => reciprocalScaleCharge (xiPrimeGammaNoetherPath u)) 0 t := by
  simpa only [xiPrimeGammaNoetherCharge] using hasDerivAt_const t (1 : ℂ)

/-- The actual path derivatives solve both Euler--Lagrange equations. -/
theorem xiPrimeGammaNoetherPath_velocity (t : ℝ) :
    (deriv (fun u => (xiPrimeGammaNoetherPath u).1) t,
      deriv (fun u => (xiPrimeGammaNoetherPath u).2) t) =
        reciprocalScaleVelocity (xiPrimeGammaNoetherRate t) (xiPrimeGammaNoetherPath t) :=
  Prod.ext (hasDerivAt_xiPrimeGammaNoetherPath_fst t).deriv
    (hasDerivAt_xiPrimeGammaNoetherPath_snd t).deriv

/-- The prime--Gamma canonical action vanishes along its canonical trajectories. -/
theorem xiPrimeGammaNoetherAction_onShell (l r : ℝ) :
    reciprocalScaleDrivenAction xiPrimeGammaNoetherRate xiPrimeGammaNoetherPath l r = 0 := by
  simp only [reciprocalScaleDrivenAction, xiPrimeGammaNoetherPath_velocity,
    reciprocalScaleLagrangian_onShell, intervalIntegral.integral_zero]

/-- The literal arithmetic solution has the same continuous reciprocal action symmetry. -/
theorem xiPrimeGammaNoetherAction_symmetry (s l r : ℝ) :
    reciprocalScaleDrivenAction xiPrimeGammaNoetherRate
      (fun t => reciprocalScale s (xiPrimeGammaNoetherPath t)) l r =
        reciprocalScaleDrivenAction xiPrimeGammaNoetherRate xiPrimeGammaNoetherPath l r :=
  reciprocalScaleDrivenAction_symmetry _ s _ l r

/-- A frozen arithmetic trajectory has exact nonzero response to an independent rate shift.
Zero action on the canonical family therefore does not imply rate stationarity. -/
theorem xiPrimeGammaNoetherAction_rateShift (b : ℂ) (l r : ℝ) :
    reciprocalScaleDrivenAction (fun t => xiPrimeGammaNoetherRate t + b)
      xiPrimeGammaNoetherPath l r = (r - l) • (-b) := by
  have hd (t : ℝ) : reciprocalScaleLagrangian (xiPrimeGammaNoetherRate t + b)
      (xiPrimeGammaNoetherPath t)
      (reciprocalScaleVelocity (xiPrimeGammaNoetherRate t) (xiPrimeGammaNoetherPath t)) =
        -b := by
    have h := reciprocalScaleLagrangian_rateShift (xiPrimeGammaNoetherRate t) b
      (xiPrimeGammaNoetherPath t)
      (reciprocalScaleVelocity (xiPrimeGammaNoetherRate t) (xiPrimeGammaNoetherPath t))
    simpa only [reciprocalScaleLagrangian_onShell, sub_zero,
      xiPrimeGammaNoetherCharge, mul_one] using h
  simp only [reciprocalScaleDrivenAction, xiPrimeGammaNoetherPath_velocity, hd,
    intervalIntegral.integral_const]

end RHTower.ThetaSourceWard

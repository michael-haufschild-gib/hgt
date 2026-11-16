import GaloisForLFunctions.BlackHoleRingdown.Damping.OptimalScalarDecay
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Critical scalar modes and their energy

Critical damping has a repeated characteristic root. Its full two-parameter solution is
`exp (-|ω|t) (A + Bt)`, so the optimal characteristic rate does not imply a bound by a
constant times `exp (-|ω|t)` for arbitrary initial data. The polynomial factor is essential.
-/

noncomputable section
namespace GaloisForLFunctions.BlackHoleRingdown

/-- General scalar solution at the repeated characteristic root. -/
def criticalScalarMode (ω A B t : ℝ) : ℝ :=
  Real.exp (-|ω| * t) * (A + B * t)

/-- Velocity of a critically damped scalar mode. -/
def criticalScalarVelocity (ω A B t : ℝ) : ℝ :=
  Real.exp (-|ω| * t) * (B - |ω| * (A + B * t))

/-- Acceleration of a critically damped scalar mode. -/
def criticalScalarAcceleration (ω A B t : ℝ) : ℝ :=
  Real.exp (-|ω| * t) * (ω ^ 2 * (A + B * t) - 2 * |ω| * B)

theorem hasDerivAt_criticalScalarMode (ω A B t : ℝ) :
    HasDerivAt (criticalScalarMode ω A B) (criticalScalarVelocity ω A B t) t := by
  have he := ((hasDerivAt_id t).const_mul (-|ω|)).exp
  have hp := (hasDerivAt_const t A).add ((hasDerivAt_id t).const_mul B)
  convert he.mul hp using 1 <;> try rfl
  dsimp [criticalScalarVelocity]
  ring

theorem hasDerivAt_criticalScalarVelocity (ω A B t : ℝ) :
    HasDerivAt (criticalScalarVelocity ω A B) (criticalScalarAcceleration ω A B t) t := by
  have he := ((hasDerivAt_id t).const_mul (-|ω|)).exp
  have hp := (hasDerivAt_const t B).sub
    (((hasDerivAt_const t A).add ((hasDerivAt_id t).const_mul B)).const_mul |ω|)
  convert he.mul hp using 1 <;> try rfl
  dsimp [criticalScalarAcceleration]
  rw [← sq_abs ω]
  ring

/-- The complete critical family solves the scalar wave-mode equation. -/
theorem criticalScalarMode_ode (ω A B t : ℝ) :
    deriv (deriv (criticalScalarMode ω A B)) t +
      2 * |ω| * deriv (criticalScalarMode ω A B) t +
      ω ^ 2 * criticalScalarMode ω A B t = 0 := by
  have hd : deriv (criticalScalarMode ω A B) = criticalScalarVelocity ω A B :=
    funext fun s => (hasDerivAt_criticalScalarMode ω A B s).deriv
  rw [hd, (hasDerivAt_criticalScalarVelocity ω A B t).deriv]
  unfold criticalScalarAcceleration criticalScalarVelocity criticalScalarMode
  rw [← sq_abs ω]
  ring

/-- Prescribed displacement and velocity determine the two critical-mode parameters. -/
theorem criticalScalarMode_initial_data (ω a v : ℝ) :
    criticalScalarMode ω a (v + |ω| * a) 0 = a ∧
      deriv (criticalScalarMode ω a (v + |ω| * a)) 0 = v := by
  rw [(hasDerivAt_criticalScalarMode ω a (v + |ω| * a) 0).deriv]
  simp [criticalScalarMode, criticalScalarVelocity]

/-- Kinetic plus potential energy decreases by exactly the damping loss. -/
theorem criticalScalarMode_energy_derivative (ω A B t : ℝ) :
    HasDerivAt
      (fun s => criticalScalarVelocity ω A B s ^ 2 +
        ω ^ 2 * criticalScalarMode ω A B s ^ 2)
      (-4 * |ω| * criticalScalarVelocity ω A B t ^ 2) t := by
  have hv := hasDerivAt_criticalScalarVelocity ω A B t
  have ha := hasDerivAt_criticalScalarMode ω A B t
  convert (hv.pow 2).add ((ha.pow 2).const_mul (ω ^ 2)) using 1 <;> try rfl
  dsimp [criticalScalarAcceleration, criticalScalarVelocity, criticalScalarMode]
  rw [← sq_abs ω]
  ring

#print axioms criticalScalarMode_ode
#print axioms criticalScalarMode_initial_data
#print axioms criticalScalarMode_energy_derivative

end GaloisForLFunctions.BlackHoleRingdown

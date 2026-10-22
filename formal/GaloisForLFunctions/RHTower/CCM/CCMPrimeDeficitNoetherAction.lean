import GaloisForLFunctions.RHTower.CCM.CCMPoleLeadingCancellation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Position-translation Noether charge for the actual prime deficit

Let D(t) be the literal logarithmic Chebyshev deficit primitive. The
Lagrangian L(t,q,v)=v²/2-D(t)v has exact position-translation symmetry and
canonical momentum v-D(t). Every prescribed momentum has an explicit global
trajectory. Its Newton force is exp(t)-psi(exp(t)) almost everywhere, the
negative position derivative of the time-dependent potential -q*force(t).

The charge is conserved even at prime-entry times. PNT gives a velocity
defect o(exp(t)); no square-root-scale velocity bound is assumed.
-/

noncomputable section
open MeasureTheory Filter

namespace RHTower

theorem continuous_ccmLogChebyshevDeficitPrimitive : Continuous ccmLogChebyshevDeficitPrimitive := by
  apply intervalIntegral.continuous_primitive
  intro a b
  exact (Real.continuous_exp.intervalIntegrable a b).sub
    ((Chebyshev.psi_mono.comp Real.exp_monotone).intervalIntegrable)

def ccmPrimeDeficitLagrangian (t _q v : ℝ) : ℝ :=
  v ^ 2 / 2 - ccmLogChebyshevDeficitPrimitive t * v

def ccmPrimeDeficitAction (q : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ccmPrimeDeficitLagrangian t (q t) (deriv q t)

def ccmPrimeDeficitTrajectory (q₀ p t : ℝ) : ℝ :=
  q₀ + p * t + ∫ s in (0 : ℝ)..t, ccmLogChebyshevDeficitPrimitive s

def ccmPrimeDeficitPotential (t q : ℝ) : ℝ :=
  -q * (Real.exp t - Chebyshev.psi (Real.exp t))

theorem ccmPrimeDeficitAction_position_translation (q : ℝ → ℝ) (a b c : ℝ) :
    ccmPrimeDeficitAction (fun t => q t + c) a b = ccmPrimeDeficitAction q a b := by
  simp only [ccmPrimeDeficitAction, ccmPrimeDeficitLagrangian, deriv_add_const]

theorem hasDerivAt_ccmPrimeDeficitLagrangian_velocity (t q v : ℝ) :
    HasDerivAt (ccmPrimeDeficitLagrangian t q) (v - ccmLogChebyshevDeficitPrimitive t) v := by
  change HasDerivAt (fun x : ℝ => x ^ 2 / 2 - ccmLogChebyshevDeficitPrimitive t * x)
    (v - ccmLogChebyshevDeficitPrimitive t) v
  convert! (((hasDerivAt_id v).pow 2).div_const 2).sub
    ((hasDerivAt_id v).const_mul (ccmLogChebyshevDeficitPrimitive t)) using 1
  simp only [id_eq]
  ring

theorem hasDerivAt_ccmPrimeDeficitTrajectory (q₀ p t : ℝ) :
    HasDerivAt (ccmPrimeDeficitTrajectory q₀ p) (p + ccmLogChebyshevDeficitPrimitive t) t := by
  have hi := intervalIntegral.integral_hasDerivAt_right
    (continuous_ccmLogChebyshevDeficitPrimitive.intervalIntegrable 0 t)
    continuous_ccmLogChebyshevDeficitPrimitive.stronglyMeasurable.stronglyMeasurableAtFilter
    continuous_ccmLogChebyshevDeficitPrimitive.continuousAt
  convert! (((hasDerivAt_id t).const_mul p).const_add q₀).add hi using 1
  simp only [mul_one]

/-- Inverse Noether construction: every prescribed charge is realized by an actual trajectory. -/
theorem ccmPrimeDeficitTrajectory_noether_charge (q₀ p t : ℝ) :
    deriv (ccmPrimeDeficitLagrangian t (ccmPrimeDeficitTrajectory q₀ p t))
      (deriv (ccmPrimeDeficitTrajectory q₀ p) t) = p := by
  rw [(hasDerivAt_ccmPrimeDeficitLagrangian_velocity _ _ _).deriv,
    (hasDerivAt_ccmPrimeDeficitTrajectory q₀ p t).deriv]
  ring

theorem ccmPrimeDeficitTrajectory_initial (q₀ p : ℝ) :
    ccmPrimeDeficitTrajectory q₀ p 0 = q₀ ∧ deriv (ccmPrimeDeficitTrajectory q₀ p) 0 = p := by
  rw [(hasDerivAt_ccmPrimeDeficitTrajectory q₀ p 0).deriv]
  simp [ccmPrimeDeficitTrajectory, ccmLogChebyshevDeficitPrimitive]

theorem intervalIntegrable_ccmPrimeDeficitTrajectory_lagrangian (q₀ p a b : ℝ) :
    IntervalIntegrable (fun t => ccmPrimeDeficitLagrangian t (ccmPrimeDeficitTrajectory q₀ p t)
      (deriv (ccmPrimeDeficitTrajectory q₀ p) t)) volume a b := by
  simp_rw [(hasDerivAt_ccmPrimeDeficitTrajectory q₀ p _).deriv]
  apply Continuous.intervalIntegrable
  unfold ccmPrimeDeficitLagrangian
  have hv : Continuous (fun t : ℝ => p + ccmLogChebyshevDeficitPrimitive t) :=
    continuous_const.add continuous_ccmLogChebyshevDeficitPrimitive
  exact ((hv.pow 2).div_const 2).sub (continuous_ccmLogChebyshevDeficitPrimitive.mul hv)

/-- The momentum form of Euler--Lagrange holds globally, including prime entries. -/
theorem ccmPrimeDeficitTrajectory_euler_lagrange (q₀ p t : ℝ) :
    deriv (fun s => deriv (ccmPrimeDeficitLagrangian s (ccmPrimeDeficitTrajectory q₀ p s))
      (deriv (ccmPrimeDeficitTrajectory q₀ p) s)) t =
        deriv (fun q => ccmPrimeDeficitLagrangian t q
          (deriv (ccmPrimeDeficitTrajectory q₀ p) t)) (ccmPrimeDeficitTrajectory q₀ p t) := by
  simp only [ccmPrimeDeficitTrajectory_noether_charge, ccmPrimeDeficitLagrangian, deriv_const]

theorem ccmPrimeDeficitPotential_force (t q : ℝ) :
    -deriv (ccmPrimeDeficitPotential t) q = Real.exp t - Chebyshev.psi (Real.exp t) := by
  have hd := ((hasDerivAt_id q).neg).mul_const (Real.exp t - Chebyshev.psi (Real.exp t))
  change HasDerivAt (ccmPrimeDeficitPotential t) (-1 * (Real.exp t - Chebyshev.psi (Real.exp t))) q at hd
  rw [hd.deriv]
  ring

/-- The actual conservative spatial force gives Newton's equation almost everywhere in time. -/
theorem ccmPrimeDeficitTrajectory_newton_ae (q₀ p : ℝ) :
    ∀ᵐ t : ℝ ∂volume, deriv (deriv (ccmPrimeDeficitTrajectory q₀ p)) t =
      -deriv (ccmPrimeDeficitPotential t) (ccmPrimeDeficitTrajectory q₀ p t) := by
  have hf : LocallyIntegrable (fun t => Real.exp t - Chebyshev.psi (Real.exp t)) volume :=
    Real.continuous_exp.locallyIntegrable.sub
      ((Chebyshev.psi_mono.comp Real.exp_monotone).locallyIntegrable)
  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hf] with t ht
  have hd : HasDerivAt ccmLogChebyshevDeficitPrimitive (Real.exp t - Chebyshev.psi (Real.exp t)) t := ht 0
  have hvel : deriv (ccmPrimeDeficitTrajectory q₀ p) = fun s => p + ccmLogChebyshevDeficitPrimitive s :=
    funext fun s => (hasDerivAt_ccmPrimeDeficitTrajectory q₀ p s).deriv
  rw [hvel, (hd.const_add p).deriv, ccmPrimeDeficitPotential_force]

/-- PNT controls the actual velocity defect at exponential scale. -/
theorem tendsto_ccmPrimeDeficitTrajectory_scaled_velocity (q₀ p : ℝ) :
    Tendsto (fun t => Real.exp (-t) * (deriv (ccmPrimeDeficitTrajectory q₀ p) t - p))
      atTop (nhds 0) := by
  simpa only [(hasDerivAt_ccmPrimeDeficitTrajectory q₀ p _).deriv, add_sub_cancel_left] using
    tendsto_ccmLogChebyshevDeficitPrimitive_scaled_zero

end RHTower

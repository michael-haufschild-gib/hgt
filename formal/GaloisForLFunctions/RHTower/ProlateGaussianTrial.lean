import GaloisForLFunctions.RHTower.FuchsProlateScale
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# A Gaussian trial profile for the prolate separation quotient

The centred Gaussian `exp(-c x²/2)` is an exact test vector for the prolate Sturm--Liouville
action: its action is a quartic polynomial multiple of itself, so the Rayleigh numerator is an
elementary integral.  Because the Gaussian is concentrated on the scale `c^{-1/2}` while the
polynomial's negative part only bites near the aperture edge, the quotient is `O(c)` rather than
`O(c²)`.

This module records the exact action and the resulting shifted Rayleigh integrand.
-/

noncomputable section

open Real Set

namespace RHTower

/-- Centred Gaussian trial profile at bandwidth `c`. -/
def gaussianTrial (c x : ℝ) : ℝ := Real.exp (-(c * x ^ (2 : ℕ)) / 2)

theorem gaussianTrial_pos (c x : ℝ) : 0 < gaussianTrial c x := Real.exp_pos _

theorem hasDerivAt_gaussianTrial (c x : ℝ) :
    HasDerivAt (gaussianTrial c) (-(c * x) * gaussianTrial c x) x := by
  have hsq : HasDerivAt (fun y : ℝ => y ^ (2 : ℕ)) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hinner : HasDerivAt (fun y : ℝ => -(c * y ^ (2 : ℕ)) / 2) (-(c * x)) x := by
    have h1 : HasDerivAt (fun y : ℝ => (-c / 2) * y ^ (2 : ℕ)) ((-c / 2) * (2 * x)) x :=
      hsq.const_mul _
    have hfun : (fun y : ℝ => (-c / 2) * y ^ (2 : ℕ)) = fun y : ℝ => -(c * y ^ (2 : ℕ)) / 2 := by
      funext y
      ring
    rw [hfun] at h1
    convert h1 using 1
    ring
  have h4 := hinner.exp
  have heq : (fun y : ℝ => Real.exp (-(c * y ^ (2 : ℕ)) / 2)) = gaussianTrial c := rfl
  rw [heq] at h4
  have hcomm : Real.exp (-(c * x ^ (2 : ℕ)) / 2) * -(c * x) = -(c * x) * gaussianTrial c x :=
    mul_comm _ _
  rwa [hcomm] at h4

theorem deriv_gaussianTrial (c : ℝ) :
    deriv (gaussianTrial c) = fun x => -(c * x) * gaussianTrial c x :=
  funext fun x => (hasDerivAt_gaussianTrial c x).deriv

theorem hasDerivAt_deriv_gaussianTrial (c x : ℝ) :
    HasDerivAt (deriv (gaussianTrial c))
      ((-c + c ^ (2 : ℕ) * x ^ (2 : ℕ)) * gaussianTrial c x) x := by
  rw [deriv_gaussianTrial]
  have hlin : HasDerivAt (fun y : ℝ => -(c * y)) (-c) x := by
    have h1 : HasDerivAt (fun y : ℝ => (-c) * y) ((-c) * 1) x := (hasDerivAt_id x).const_mul _
    have hfun : (fun y : ℝ => (-c) * y) = fun y : ℝ => -(c * y) := by
      funext y
      ring
    rw [hfun] at h1
    convert h1 using 1
    ring
  have h := hlin.fun_mul (hasDerivAt_gaussianTrial c x)
  have hval : -c * gaussianTrial c x + -(c * x) * (-(c * x) * gaussianTrial c x)
      = (-c + c ^ (2 : ℕ) * x ^ (2 : ℕ)) * gaussianTrial c x := by ring
  rw [hval] at h
  exact h

theorem deriv2_gaussianTrial (c : ℝ) :
    deriv (deriv (gaussianTrial c)) = fun x => (-c + c ^ (2 : ℕ) * x ^ (2 : ℕ)) * gaussianTrial c x :=
  funext fun x => (hasDerivAt_deriv_gaussianTrial c x).deriv

theorem contDiff_gaussianTrial (c : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gaussianTrial c) := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x : ℝ => -(c * x ^ (2 : ℕ)) / 2 := by fun_prop
  exact Real.contDiff_exp.comp h

theorem continuous_gaussianTrial (c : ℝ) : Continuous (gaussianTrial c) :=
  (contDiff_gaussianTrial c).continuous

theorem even_gaussianTrial (c : ℝ) : Function.Even (gaussianTrial c) := by
  intro x
  simp [gaussianTrial]

/-- **Exact prolate action of the Gaussian trial profile.** -/
theorem prolateSLAction_gaussianTrial (c x : ℝ) :
    prolateSLAction c (gaussianTrial c) x =
      (-c + 3 * c * x ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (4 : ℕ)) * gaussianTrial c x := by
  rw [prolateSLAction, deriv2_gaussianTrial, deriv_gaussianTrial]
  ring

/-- The square of the Gaussian trial profile. -/
theorem gaussianTrial_sq (c x : ℝ) :
    gaussianTrial c x * gaussianTrial c x = Real.exp (-(c * x ^ (2 : ℕ))) := by
  rw [gaussianTrial, ← Real.exp_add]
  congr 1
  ring

/-- The shifted Rayleigh integrand of the Gaussian trial profile. -/
def gaussianTrialIntegrand (c x : ℝ) : ℝ :=
  (c ^ (2 : ℕ) / 2 - c + 3 * c * x ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (4 : ℕ)) * Real.exp (-(c * x ^ (2 : ℕ)))

theorem prolate_gaussian_rayleigh_integrand (c x : ℝ) :
    prolateSLAction c (gaussianTrial c) x * gaussianTrial c x
        + c ^ (2 : ℕ) / 2 * (gaussianTrial c x * gaussianTrial c x) =
      gaussianTrialIntegrand c x := by
  have h1 : gaussianTrial c x * gaussianTrial c x = Real.exp (-(c * x ^ (2 : ℕ))) :=
    gaussianTrial_sq c x
  have h2 : (-c + 3 * c * x ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (4 : ℕ)) * gaussianTrial c x * gaussianTrial c x
      = (-c + 3 * c * x ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (4 : ℕ)) * Real.exp (-(c * x ^ (2 : ℕ))) := by
    rw [mul_assoc, h1]
  rw [prolateSLAction_gaussianTrial, gaussianTrialIntegrand, h2, h1]
  ring

theorem continuous_gaussianTrialIntegrand (c : ℝ) : Continuous (gaussianTrialIntegrand c) := by
  unfold gaussianTrialIntegrand
  fun_prop

end RHTower

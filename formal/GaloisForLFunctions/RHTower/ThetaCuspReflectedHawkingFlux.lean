import GaloisForLFunctions.RHTower.ThetaCuspGlobalReflectedRiccati
import GaloisForLFunctions.HTGeometry.PeelingSchwarzianFlux

/-!
# Reflected theta action as a Hawking conformal flux

For a reflection center `u`, let `q_u(t)` be the completed theta source's normalized reflected
logarithmic action.  A conformal ray with derivative `p_u'(t) = exp (2 q_u(t))` has peeling field
`-2 q_u'(t)`.  The Schwarzian flux formula therefore becomes

`F_C,u(t) = 2 C (q_u'(t)^(2 : ℕ) - q_u''(t))`.

With `C = c/(24*pi)` and entropy `S_u = -(c/6) q_u`, this is exactly the Bianchi--Smerlak
entropy--flux identity.  Its derivative is twice `C` times the existing reflected Riccati margin.
The global theta Riccati theorem consequently makes this conformal flux nondecreasing at every
center on the nonnegative displacement ray.

This is an unconditional source theorem.  It supplies a precise Hawking/CFT interpretation of the
theta Riccati margin but does not assert the multi-mode horizon passivity condition equivalent to
the Riemann hypothesis.
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Peeling field induced by the formal conformal-ray derivative `exp (2 q_u)`. -/
def thetaCuspReflectedHawkingPeeling (u t : ℝ) : ℝ :=
  -2 * thetaCuspReflectedLogJetOne u t

/-- Named derivative of the reflected theta peeling field. -/
def thetaCuspReflectedHawkingPeelingDerivative (u t : ℝ) : ℝ :=
  -2 * thetaCuspReflectedLogJetTwo u t

/-- Schwarzian conformal flux of the reflected theta action, with
`C = cCFT/(24*pi)`. -/
def thetaCuspReflectedHawkingFlux (C u t : ℝ) : ℝ :=
  2 * C *
    (thetaCuspReflectedLogJetOne u t ^ (2 : ℕ) -
      thetaCuspReflectedLogJetTwo u t)

/-- Renormalized entropy attached to the reflected theta action. -/
def thetaCuspReflectedHawkingEntropy (c u t : ℝ) : ℝ :=
  -(c / 6) * thetaCuspReflectedLogAction u t

/-- First displacement jet of the renormalized entropy. -/
def thetaCuspReflectedHawkingEntropyJetOne (c u t : ℝ) : ℝ :=
  -(c / 6) * thetaCuspReflectedLogJetOne u t

/-- Second displacement jet of the renormalized entropy. -/
def thetaCuspReflectedHawkingEntropyJetTwo (c u t : ℝ) : ℝ :=
  -(c / 6) * thetaCuspReflectedLogJetTwo u t

theorem hasDerivAt_thetaCuspReflectedHawkingEntropy (c u t : ℝ) :
    HasDerivAt (thetaCuspReflectedHawkingEntropy c u)
      (thetaCuspReflectedHawkingEntropyJetOne c u t) t := by
  unfold thetaCuspReflectedHawkingEntropy thetaCuspReflectedHawkingEntropyJetOne
  simpa using (hasDerivAt_thetaCuspReflectedLogAction u t).const_mul (-(c / 6))

theorem hasDerivAt_thetaCuspReflectedHawkingEntropyJetOne (c u t : ℝ) :
    HasDerivAt (thetaCuspReflectedHawkingEntropyJetOne c u)
      (thetaCuspReflectedHawkingEntropyJetTwo c u t) t := by
  unfold thetaCuspReflectedHawkingEntropyJetOne
    thetaCuspReflectedHawkingEntropyJetTwo
  simpa using (hasDerivAt_thetaCuspReflectedLogJetOne u t).const_mul (-(c / 6))

/-- Exact Bianchi--Smerlak entropy--flux identity for the reflected theta action. -/
theorem thetaCuspReflectedHawkingFlux_eq_bianchiSmerlak
    {c : ℝ} (hc : c ≠ 0) (u t : ℝ) :
    thetaCuspReflectedHawkingFlux (c / (24 * Real.pi)) u t =
      (1 / (2 * Real.pi)) *
        ((6 / c) * thetaCuspReflectedHawkingEntropyJetOne c u t ^ (2 : ℕ) +
          thetaCuspReflectedHawkingEntropyJetTwo c u t) := by
  unfold thetaCuspReflectedHawkingFlux thetaCuspReflectedHawkingEntropyJetOne
    thetaCuspReflectedHawkingEntropyJetTwo
  field_simp [hc, Real.pi_ne_zero]
  ring

/-- The named peeling derivative is the actual derivative of the peeling field. -/
theorem hasDerivAt_thetaCuspReflectedHawkingPeeling (u t : ℝ) :
    HasDerivAt (thetaCuspReflectedHawkingPeeling u)
      (thetaCuspReflectedHawkingPeelingDerivative u t) t := by
  unfold thetaCuspReflectedHawkingPeeling
    thetaCuspReflectedHawkingPeelingDerivative
  simpa using (hasDerivAt_thetaCuspReflectedLogJetOne u t).const_mul (-2)

/-- The reflected theta flux has the standard peeling normal form
`C * (kappa' + kappa^(2 : ℕ)/2)`. -/
theorem thetaCuspReflectedHawkingFlux_eq_peeling_normal_form (C u t : ℝ) :
    thetaCuspReflectedHawkingFlux C u t =
      C * (thetaCuspReflectedHawkingPeelingDerivative u t +
        (1 / 2 : ℝ) * thetaCuspReflectedHawkingPeeling u t ^ (2 : ℕ)) := by
  unfold thetaCuspReflectedHawkingFlux thetaCuspReflectedHawkingPeeling
    thetaCuspReflectedHawkingPeelingDerivative
  ring

/-- The conformal-flux derivative is exactly the reflected theta Riccati margin. -/
theorem hasDerivAt_thetaCuspReflectedHawkingFlux (C u t : ℝ) :
    HasDerivAt (thetaCuspReflectedHawkingFlux C u)
      (2 * C * thetaCuspReflectedLogRiccatiMargin u t) t := by
  have h₁ := hasDerivAt_thetaCuspReflectedLogJetOne u t
  have h₂ := hasDerivAt_thetaCuspReflectedLogJetTwo u t
  have hraw : HasDerivAt
      (fun x => thetaCuspReflectedLogJetOne u x *
          thetaCuspReflectedLogJetOne u x - thetaCuspReflectedLogJetTwo u x)
      (thetaCuspReflectedLogJetTwo u t * thetaCuspReflectedLogJetOne u t +
          thetaCuspReflectedLogJetOne u t * thetaCuspReflectedLogJetTwo u t -
        thetaCuspReflectedLogJetThree u t) t :=
    (h₁.mul h₁).sub h₂
  have hscaled : HasDerivAt
      (fun x => 2 * C * (thetaCuspReflectedLogJetOne u x *
          thetaCuspReflectedLogJetOne u x - thetaCuspReflectedLogJetTwo u x))
      (2 * C * (thetaCuspReflectedLogJetTwo u t *
          thetaCuspReflectedLogJetOne u t +
          thetaCuspReflectedLogJetOne u t * thetaCuspReflectedLogJetTwo u t -
        thetaCuspReflectedLogJetThree u t)) t :=
    hraw.const_mul (2 * C)
  change HasDerivAt
    (fun x => 2 * C * (thetaCuspReflectedLogJetOne u x ^ (2 : ℕ) -
      thetaCuspReflectedLogJetTwo u x))
    (2 * C * (2 * thetaCuspReflectedLogJetOne u t *
      thetaCuspReflectedLogJetTwo u t - thetaCuspReflectedLogJetThree u t)) t
  simp only [pow_two]
  exact hscaled.congr_deriv (by ring)

theorem deriv_thetaCuspReflectedHawkingFlux (C u t : ℝ) :
    deriv (thetaCuspReflectedHawkingFlux C u) t =
      2 * C * thetaCuspReflectedLogRiccatiMargin u t :=
  (hasDerivAt_thetaCuspReflectedHawkingFlux C u t).deriv

/-- **Unconditional Hawking-flux law.**  At nonnegative displacement and nonnegative CFT
normalization, the reflected theta conformal flux has nonnegative derivative at every center. -/
theorem deriv_thetaCuspReflectedHawkingFlux_nonneg
    {C u t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t) :
    0 ≤ deriv (thetaCuspReflectedHawkingFlux C u) t := by
  rw [deriv_thetaCuspReflectedHawkingFlux]
  exact mul_nonneg (mul_nonneg (by norm_num) hC)
    (thetaCuspReflectedLogRiccatiMargin_nonneg ht)

end

end RHTower

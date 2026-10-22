import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTiltFluxHedenmalmWeld
import GaloisForLFunctions.RHTower.XiEulerSafeObservability

/-!
# Theta cusp tilt flux and Euler-safe observability are the same quadratic law

This module identifies the remaining multi-mode positivity problem in the literal theta-source
tilt-flux route with the Euler-safe observability deficit from the Cauchy-loss route.

Above any safe offset `a > 1 / 2`, rescaling packet coefficients by the nonvanishing factor
`xiCent (w j)` sends the theta-source Bezoutian quadratic form exactly to the Euler-safe deficit,
up to the positive scalar `π`.  Since this diagonal rescaling is invertible, universal positivity
of the two families is equivalent.  Thus tilt flux supplies a theta-correlation realization of
the observability deficit, while the unresolved content is precisely cross-node coherence.
-/

open Complex
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- The literal theta-source Bezoutian is the critical logarithmic-derivative kernel conjugated
by the nonvanishing diagonal multiplier `xiCent`. -/
theorem sourceBezoutian_thetaCuspTiltSource_eq_xiCent_mul_criticalKernel
    {w v : ℂ} (hw : 1 / 2 < w.re) (hv : 1 / 2 < v.re) :
    sourceBezoutian thetaCuspTiltSource w v =
      xiCent w * conj (xiCent v) * criticalLogDerivKernel w v := by
  have hden : w + conj v ≠ 0 := add_conj_ne_zero (by linarith) (by linarith)
  rw [sourceBezoutian_thetaCuspTiltSource_eq_xiCentBezoutian hden,
    xiCentBezoutian_eq_mul_criticalKernel hw hv]

/-- After coefficient rescaling by `xiCent`, the Euler-safe deficit is exactly `π` times the
literal theta-source flux quadratic form. -/
theorem eulerSafeDeficit_rescaledXi_eq_pi_mul_thetaCuspTiltSource_flux
    {a : ℝ} (ha : 1 / 2 < a) {n : ℕ} (c w : Fin n → ℂ)
    (hw : ∀ j, a < (w j).re) :
    eulerSafeDeficit a (fun j => c j * xiCent (w j)) w =
      (Real.pi : ℂ) *
        ∑ j, ∑ k, c j * conj (c k) *
          sourceBezoutian thetaCuspTiltSource (w j) (w k) := by
  rw [eulerSafeDeficit_eq ha _ w hw]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul,
    sourceBezoutian_thetaCuspTiltSource_eq_xiCent_mul_criticalKernel
      (lt_trans ha (hw j)) (lt_trans ha (hw k))]
  ring

/-- At the derivative level, the real Euler-safe deficit is exactly `π` times the neutral
tilt-correlation derivative for the literal theta source. -/
theorem eulerSafeDeficit_rescaledXi_re_eq_pi_mul_tiltCorrelation_deriv
    {a : ℝ} (ha : 1 / 2 < a) {n : ℕ} (c w : Fin n → ℂ)
    (hw : ∀ j, a < (w j).re) {D : ℝ}
    (hD : HasDerivAt (tiltCorrelation thetaCuspTiltSource c w) D 0) :
    (eulerSafeDeficit a (fun j => c j * xiCent (w j)) w).re =
      Real.pi * D := by
  have hcanonical := hasDerivAt_tiltCorrelation thetaCuspTiltSource c w
    (fun j => lt_trans (by linarith) (hw j))
  have hvalue := hD.unique hcanonical
  have hdeficit :=
    eulerSafeDeficit_rescaledXi_eq_pi_mul_thetaCuspTiltSource_flux
      ha c w hw
  have hre := congrArg Complex.re hdeficit
  rw [Complex.re_ofReal_mul, ← hvalue] at hre
  exact hre

/-- On every safe half-plane, universal positivity of the literal theta-source flux packets is
equivalent to universal positivity of the Euler-safe observability deficits.  The forward map is
coefficient multiplication by `xiCent`; its inverse exists because `xiCent` has no zeros there. -/
theorem thetaCuspTiltSource_flux_nonneg_iff_eulerSafeDeficit_nonneg
    {a : ℝ} (ha : 1 / 2 < a) :
    (∀ (n : ℕ) (c w : Fin n → ℂ), (∀ j, a < (w j).re) →
      0 ≤ (∑ j, ∑ k, c j * conj (c k) *
        sourceBezoutian thetaCuspTiltSource (w j) (w k)).re) ↔
    (∀ (n : ℕ) (d w : Fin n → ℂ), (∀ j, a < (w j).re) →
      0 ≤ (eulerSafeDeficit a d w).re) := by
  constructor
  · intro hflux n d w hw
    let c : Fin n → ℂ := fun j => d j / xiCent (w j)
    have hX : ∀ j, xiCent (w j) ≠ 0 := fun j =>
      xiCent_ne_zero_of_half_lt_re (lt_trans ha (hw j))
    have hc : (fun j => c j * xiCent (w j)) = d := by
      funext j
      dsimp only [c]
      exact div_mul_cancel₀ (d j) (hX j)
    have hdeficit :=
      eulerSafeDeficit_rescaledXi_eq_pi_mul_thetaCuspTiltSource_flux
        ha c w hw
    rw [hc] at hdeficit
    have hre := congrArg Complex.re hdeficit
    rw [Complex.re_ofReal_mul] at hre
    rw [hre]
    exact mul_nonneg Real.pi_pos.le (hflux n c w hw)
  · intro hdeficit n c w hw
    have hEq :=
      eulerSafeDeficit_rescaledXi_eq_pi_mul_thetaCuspTiltSource_flux
        ha c w hw
    have hre := congrArg Complex.re hEq
    rw [Complex.re_ofReal_mul] at hre
    have hnonneg := hdeficit n (fun j => c j * xiCent (w j)) w hw
    rw [hre] at hnonneg
    nlinarith [Real.pi_pos]

end

end RHTower

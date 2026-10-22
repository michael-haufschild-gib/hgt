import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaRoutePDyadicInformationMobiusRigidity
import GaloisForLFunctions.RHTower.SourceHorizontalWoldGaussHodgeVirialBridge

/-!
# Route P information--Wold--Gauss virial bridge

P-G55's information holonomy virial `V(u)=u cosh u-sinh u` is the radial primitive of the
existing Wold/Gauss Hodge virial: `V'(u)=u sinh u=u²G'(u)`, where `G` is inverse-Euler Green
profile.  At every prime-power clock, derivative of P-G55's summand is a strictly positive Euler
weight times that same mass response.  Information, co-Poisson holonomy, and Gauss Hodge mass are
successive differential presentations of one horizontal mode, not independent coercivities.
-/

open Real Set Filter Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Information holonomy virial differentiates to Wold/Gauss Hodge virial. -/
theorem hasDerivAt_sourceHorizontalHolonomyVirial (u : ℝ) :
    HasDerivAt sourceHorizontalHolonomyVirial (u * Real.sinh u) u := by
  have h := ((hasDerivAt_id u).mul (Real.hasDerivAt_cosh u)).sub
    (Real.hasDerivAt_sinh u)
  have hfun : id * Real.cosh - Real.sinh = sourceHorizontalHolonomyVirial := by
    funext y
    rfl
  rw [hfun] at h
  simpa only [id_eq, one_mul, add_sub_cancel_left] using h

theorem deriv_sourceHorizontalHolonomyVirial (u : ℝ) :
    deriv sourceHorizontalHolonomyVirial u = u * Real.sinh u :=
  (hasDerivAt_sourceHorizontalHolonomyVirial u).deriv

/-- Exact differential weld to inverse-Euler Green carrier. -/
theorem deriv_sourceHorizontalHolonomyVirial_eq_woldEulerGreenResponse (u : ℝ) :
    deriv sourceHorizontalHolonomyVirial u =
      u ^ (2 : ℕ) * deriv RHTower.sourceHorizontalWoldEulerGreenProfile u := by
  rw [deriv_sourceHorizontalHolonomyVirial,
    RHTower.sourceHorizontalWoldEulerGreenProfile_euler]

/-- Prime-power information virial differentiates to its Wold/Gauss mass response. -/
theorem hasDerivAt_sourceHorizontalPrimePowerScaleVirial
    (p : Nat.Primes) (n : ℕ) (t : ℝ) :
    HasDerivAt
      (fun y => 2 * sourceHorizontalHolonomyVirial
        (2 * (n + 1) * Real.log (p : ℝ) * y))
      (4 * (n + 1) * Real.log (p : ℝ) *
        ((2 * (n + 1) * Real.log (p : ℝ) * t) *
          Real.sinh (2 * (n + 1) * Real.log (p : ℝ) * t))) t := by
  have hlin : HasDerivAt
      (fun y : ℝ => 2 * (n + 1) * Real.log (p : ℝ) * y)
      (2 * (n + 1) * Real.log (p : ℝ)) t := by
    simpa using (hasDerivAt_id t).const_mul
      (2 * (n + 1) * Real.log (p : ℝ))
  have h := (hasDerivAt_sourceHorizontalHolonomyVirial _).comp t hlin |>.const_mul 2
  have hcoeff : 2 *
      ((2 * (n + 1) * Real.log (p : ℝ) * t) *
        Real.sinh (2 * (n + 1) * Real.log (p : ℝ) * t) *
          (2 * (n + 1) * Real.log (p : ℝ))) =
      4 * (n + 1) * Real.log (p : ℝ) *
        ((2 * (n + 1) * Real.log (p : ℝ) * t) *
          Real.sinh (2 * (n + 1) * Real.log (p : ℝ) * t)) := by ring
  rw [hcoeff] at h
  simpa only [Function.comp_apply] using h

/-- Derivative of `tH'-H` is a positive multiple of Wold/Gauss Hodge virial. -/
theorem deriv_sourceHorizontalPrimePowerScaleVirial
    (p : Nat.Primes) (n : ℕ) (t : ℝ) :
    deriv (fun y => y * deriv (sourceHorizontalPrimePowerHolonomy p n) y -
        sourceHorizontalPrimePowerHolonomy p n y) t =
      4 * (n + 1) * Real.log (p : ℝ) *
        ((2 * (n + 1) * Real.log (p : ℝ) * t) *
          Real.sinh (2 * (n + 1) * Real.log (p : ℝ) * t)) := by
  have hfun : (fun y => y * deriv (sourceHorizontalPrimePowerHolonomy p n) y -
        sourceHorizontalPrimePowerHolonomy p n y) =
      fun y => 2 * sourceHorizontalHolonomyVirial
        (2 * (n + 1) * Real.log (p : ℝ) * y) := by
    funext y
    exact sourceHorizontalPrimePowerHolonomy_scaleVirial p n y
  rw [hfun, (hasDerivAt_sourceHorizontalPrimePowerScaleVirial p n t).deriv]

/-- Off wall, information virial grows strictly with horizontal depth. -/
theorem deriv_sourceHorizontalPrimePowerScaleVirial_pos
    (p : Nat.Primes) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < deriv (fun y => y * deriv (sourceHorizontalPrimePowerHolonomy p n) y -
        sourceHorizontalPrimePowerHolonomy p n y) t := by
  rw [deriv_sourceHorizontalPrimePowerScaleVirial]
  have hp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have hu : 0 < 2 * (n + 1) * Real.log (p : ℝ) * t := by positivity
  positivity

/-- One physical prime-power summand in P-G55's geometric KL expansion. -/
def sourceHorizontalPrimeGeometricKLScaleTerm
    (p : Nat.Primes) (n : ℕ) (t : ℝ) : ℝ :=
  2 * Real.exp (-Real.log (p : ℝ) * (n + 1)) / (n + 1) *
    (t * deriv (sourceHorizontalPrimePowerHolonomy p n) t -
      sourceHorizontalPrimePowerHolonomy p n t)

/-- Termwise derivative is positively weighted Wold/Gauss Hodge virial. -/
theorem hasDerivAt_sourceHorizontalPrimeGeometricKLScaleTerm
    (p : Nat.Primes) (n : ℕ) (t : ℝ) :
    HasDerivAt (sourceHorizontalPrimeGeometricKLScaleTerm p n)
      (8 * Real.log (p : ℝ) * Real.exp (-Real.log (p : ℝ) * (n + 1)) *
        ((2 * (n + 1) * Real.log (p : ℝ) * t) *
          Real.sinh (2 * (n + 1) * Real.log (p : ℝ) * t))) t := by
  have h := (hasDerivAt_sourceHorizontalPrimePowerScaleVirial p n t).const_mul
    (2 * Real.exp (-Real.log (p : ℝ) * (n + 1)) / (n + 1))
  have hk : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hfun : sourceHorizontalPrimeGeometricKLScaleTerm p n = fun y =>
      2 * Real.exp (-Real.log (p : ℝ) * (n + 1)) / (n + 1) *
        (2 * sourceHorizontalHolonomyVirial
          (2 * (n + 1) * Real.log (p : ℝ) * y)) := by
    funext y
    rw [sourceHorizontalPrimeGeometricKLScaleTerm,
      sourceHorizontalPrimePowerHolonomy_scaleVirial]
  have hcoeff :
      8 * Real.log (p : ℝ) * Real.exp (-Real.log (p : ℝ) * (n + 1)) *
          ((2 * (n + 1) * Real.log (p : ℝ) * t) *
            Real.sinh (2 * (n + 1) * Real.log (p : ℝ) * t)) =
      2 * Real.exp (-Real.log (p : ℝ) * (n + 1)) / (n + 1) *
        (4 * (n + 1) * Real.log (p : ℝ) *
          ((2 * (n + 1) * Real.log (p : ℝ) * t) *
            Real.sinh (2 * (n + 1) * Real.log (p : ℝ) * t))) := by
    field_simp [hk.ne']
    ring
  rw [hfun, hcoeff]
  exact h

theorem deriv_sourceHorizontalPrimeGeometricKLScaleTerm_pos
    (p : Nat.Primes) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < deriv (sourceHorizontalPrimeGeometricKLScaleTerm p n) t := by
  rw [(hasDerivAt_sourceHorizontalPrimeGeometricKLScaleTerm p n t).deriv]
  have hp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have hu : 0 < 2 * (n + 1) * Real.log (p : ℝ) * t := by positivity
  positivity

end

end RHTower.HedenmalmThetaSource

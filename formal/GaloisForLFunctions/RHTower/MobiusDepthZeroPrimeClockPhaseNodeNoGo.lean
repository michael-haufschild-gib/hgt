import GaloisForLFunctions.RHTower.MobiusGammaCoPoissonDepthZeroReduction
import GaloisForLFunctions.RHTower.XiCTaylorSignedPrimePhaseNodeLocalEulerNoGo

/-!
# Route E depth-zero current is not a phase-node source

The hard Route E boundary is the depth-zero divided-log prime current.  Its coefficient on every
prime ray is the positive critical square-root radius.  The phase-node classification says that a
nonzero carrier frequency can activate at most one prime ray and is therefore zero modulo
finite-prime Euler data.

This file proves the missing cross-route separation: the canonical Route E depth-zero profile has
every prime ray active, represents a nonzero global prime-clock class, and cannot be a phase-node
multiplier at any nonzero frequency.  Thus the phase-node escape closed by the modular
superselection theorem cannot orient `OPEN-SOURCE-001`.

No cancellation estimate, zero hypothesis, or RH assumption occurs here.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry
open Set

noncomputable section

/-- Canonical prime-power coordinate profile of the hard Route E depth-zero divided-log current.
Positive valuation depths vanish because they belong to the already critical-size remainder. -/
def routeEDepthZeroPrimeClockProfile : PrimePowerClockIndex → ℂ
  | (p, e) =>
      if e = 0 then
        (routeEDividedLogHalfDensityAtom (criticalPrimeTowerRadius p) 0 : ℂ)
      else 0

@[simp]
theorem routeEDepthZeroPrimeClockProfile_zero (p : Nat.Primes) :
    routeEDepthZeroPrimeClockProfile (p, 0) =
      (criticalPrimeTowerRadius p : ℂ) := by
  simp [routeEDepthZeroPrimeClockProfile,
    routeEDividedLogHalfDensityAtom_zero]

@[simp]
theorem routeEDepthZeroPrimeClockProfile_succ
    (p : Nat.Primes) (e : ℕ) :
    routeEDepthZeroPrimeClockProfile (p, e + 1) = 0 := by
  simp [routeEDepthZeroPrimeClockProfile]

/-- Every rational-prime ray is active in the canonical Route E depth-zero profile. -/
theorem routeEDepthZeroPrimeClockProfile_rayActivity_eq_univ :
    rayActivity primePowerClockRay routeEDepthZeroPrimeClockProfile = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  refine ⟨(p, 0), rfl, ?_⟩
  rw [routeEDepthZeroPrimeClockProfile_zero]
  exact_mod_cast (criticalPrimeTowerRadius_pos p.property.pos).ne'

/-- The all-prime Route E depth-zero current is not finite-prime Euler data. -/
theorem routeEDepthZeroPrimeClockProfile_not_local :
    ¬ PrimePowerClockLocal routeEDepthZeroPrimeClockProfile := by
  intro hlocal
  unfold PrimePowerClockLocal RayLocal at hlocal
  rw [routeEDepthZeroPrimeClockProfile_rayActivity_eq_univ] at hlocal
  exact Set.infinite_univ hlocal

/-- Global prime-clock class of the canonical Route E depth-zero current. -/
def routeEDepthZeroPrimeClockClass : PrimeProfileClockQuotient :=
  (rayLocalSubmodule primePowerClockRay).mkQ
    routeEDepthZeroPrimeClockProfile

/-- Unlike every phase-node prime-power multiplier, the Route E depth-zero profile survives the
quotient by finite-prime Euler rays. -/
theorem routeEDepthZeroPrimeClockClass_ne_zero :
    routeEDepthZeroPrimeClockClass ≠ 0 := by
  intro hzero
  apply routeEDepthZeroPrimeClockProfile_not_local
  change routeEDepthZeroPrimeClockProfile ∈
    rayLocalSubmodule primePowerClockRay
  rw [← Submodule.Quotient.mk_eq_zero]
  exact hzero

/-- **Route E phase-node no-go.**  No nonzero carrier frequency can place the canonical all-prime
depth-zero Route E current on phase nodes.  The result assumes neither boundedness nor finite
valuation depth of a proposed multiplier. -/
theorem routeEDepthZeroPrimeClockProfile_not_phaseNode
    {u : ℝ} (hu : u ≠ 0) :
    ¬ RouteJPrimePowerComplexPhaseNodeMultiplier
      u routeEDepthZeroPrimeClockProfile := by
  intro hphase
  exact routeEDepthZeroPrimeClockProfile_not_local
    (routeJ_primePowerComplexPhaseNode_primePowerClockLocal hu hphase)

/-- Exact source-category separation exposed by the updated modular superselection theorem:
the Route E profile is globally nonzero, while a phase-node realization at nonzero frequency is
impossible. -/
theorem routeEDepthZero_globalSource_phaseNode_separation
    {u : ℝ} (hu : u ≠ 0) :
    routeEDepthZeroPrimeClockClass ≠ 0 ∧
      ¬ RouteJPrimePowerComplexPhaseNodeMultiplier
        u routeEDepthZeroPrimeClockProfile :=
  ⟨routeEDepthZeroPrimeClockClass_ne_zero,
    routeEDepthZeroPrimeClockProfile_not_phaseNode hu⟩

end

end RHTower

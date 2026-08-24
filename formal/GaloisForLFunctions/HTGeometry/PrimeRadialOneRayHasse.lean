import GaloisForLFunctions.HTGeometry.PrimeRadialFusionFieldCorrespondence

/-!
# One-ray Hasse reconstruction for prime-radial profiles

A zero-constant formal power series is reconstructed by its positive coefficients.  After radial
replication into an arithmetic function, those same coefficients occur on every prime-power ray.
Consequently the complete depth profile at any single prime determines the global replicated source,
and every nonzero source is detected at one finite depth on that chosen ray.

This is also a redundancy theorem: within the radial subspace, observing all primes supplies no more
separation than observing one prime.  A genuinely arithmetic route must leave radial replication if
it expects cross-prime variation to carry additional information.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Formal prime-radial profiles are equivalent to their realized positive-depth coefficients. -/
noncomputable def primeRadialCoefficientProfileHasseEquivRange :
    PrimeRadialProfile ≃ Set.range primeRadialCoefficientProfile :=
  Equiv.ofInjective primeRadialCoefficientProfile primeRadialCoefficientProfile_injective

@[simp]
theorem primeRadialCoefficientProfileHasseEquivRange_apply (u : PrimeRadialProfile) :
    (primeRadialCoefficientProfileHasseEquivRange u : ℕ → ℂ) =
      primeRadialCoefficientProfile u := rfl

/-- Positive valuation depths determine a complete zero-constant formal profile. -/
theorem primeRadialProfile_congr_coefficient_hasse_iff
    (u v : PrimeRadialProfile) :
    u = v ↔ ∀ e : ℕ,
      PowerSeries.coeff (e + 1) (u : PowerSeries ℂ) =
        PowerSeries.coeff (e + 1) (v : PowerSeries ℂ) := by
  constructor
  · rintro rfl
    exact fun _ ↦ rfl
  · intro h
    apply primeRadialCoefficientProfile_injective
    funext e
    change PowerSeries.coeff (e + 1) (u : PowerSeries ℂ) =
      PowerSeries.coeff (e + 1) (v : PowerSeries ℂ)
    exact h e

/-- One arbitrary prime ray already reconstructs a replicated global prime-radial source. -/
theorem primeRadialProfile_congr_oneRay_hasse_iff
    (p : Nat.Primes) (u v : PrimeRadialProfile) :
    u = v ↔ ∀ e : ℕ,
      primePowerCoordinateProfile (primeRadialSource u) (p, e) =
        primePowerCoordinateProfile (primeRadialSource v) (p, e) := by
  constructor
  · rintro rfl
    exact fun _ ↦ rfl
  · intro h
    apply primeRadialCoefficientProfile_injective
    funext e
    change PowerSeries.coeff (e + 1) (u : PowerSeries ℂ) =
      PowerSeries.coeff (e + 1) (v : PowerSeries ℂ)
    simpa using h e

/-- A replicated radial source is zero exactly when one prime ray vanishes at every depth. -/
theorem primeRadialProfile_eq_zero_oneRay_hasse_iff
    (p : Nat.Primes) (u : PrimeRadialProfile) :
    u = 0 ↔ ∀ e : ℕ,
      primePowerCoordinateProfile (primeRadialSource u) (p, e) = 0 := by
  constructor
  · rintro rfl
    intro e
    rw [primePowerCoordinateProfile_primeRadialSource]
    simp
  · intro h
    apply primeRadialCoefficientProfile_injective
    funext e
    change PowerSeries.coeff (e + 1) (u : PowerSeries ℂ) =
      PowerSeries.coeff (e + 1) ((0 : PrimeRadialProfile) : PowerSeries ℂ)
    have he := h e
    rw [primePowerCoordinateProfile_primeRadialSource] at he
    simpa using he

/-- Every nonzero radial profile is detected at a finite depth on any chosen prime ray. -/
theorem exists_oneRayCoordinate_ne_zero_of_primeRadialProfile_ne_zero
    (p : Nat.Primes) (u : PrimeRadialProfile) (hu : u ≠ 0) :
    ∃ e : ℕ, primePowerCoordinateProfile (primeRadialSource u) (p, e) ≠ 0 := by
  by_contra h
  push Not at h
  exact hu ((primeRadialProfile_eq_zero_oneRay_hasse_iff p u).2 h)

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.RHTower.HardyTitchmarshEulerConcrete
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFinitePrimeSource

/-!
# Bounded finite-prime theta resolvent

This module assembles the already formalized physical one-prime Euler factors over every prime up
to `N`.  Each factor is a norm-small perturbation of a unitary dilation and hence invertible.  Their
ordered finite product is therefore invertible, giving an actual bounded resolvent on the even
physical Hilbert carrier.

The scalar smooth-integer action on the theta seed is proved separately in
`ThetaCuspFinitePrimeSource`.  Identifying the operator inverse with that pointwise series after the
logarithmic unitary, and differentiating it in a general real parameter, remain later steps.
-/

noncomputable section

namespace RHTower

/-- One retained prime factor, with primality carried by the attached finite-prime subtype. -/
def finitePrimeEvenLocalFactorTerm (N : ℕ)
    (p : {p : ℕ // p ∈ Nat.primesLE N}) :
    evenSubspace →L[ℂ] evenSubspace :=
  evenPrimeLocalFactor (p : ℕ) (by
    exact_mod_cast (Nat.mem_primesLE.mp p.property).2.one_lt)

/-- Ordered product of all physical Euler local factors at primes `p ≤ N`. -/
def finitePrimeEvenLocalFactor (N : ℕ) : evenSubspace →L[ℂ] evenSubspace :=
  ((Nat.primesLE N).attach.toList.map (finitePrimeEvenLocalFactorTerm N)).prod

theorem finitePrimeEvenLocalFactorTerm_isUnit
    (N : ℕ) (p : {p : ℕ // p ∈ Nat.primesLE N}) :
    IsUnit (finitePrimeEvenLocalFactorTerm N p) := by
  unfold finitePrimeEvenLocalFactorTerm
  apply evenPrimeLocalFactor_isUnit

/-- The full finite-prime Euler factor is invertible. -/
theorem finitePrimeEvenLocalFactor_isUnit (N : ℕ) :
    IsUnit (finitePrimeEvenLocalFactor N) := by
  unfold finitePrimeEvenLocalFactor
  apply List.prod_isUnit
  intro T hT
  rw [List.mem_map] at hT
  obtain ⟨p, hp, rfl⟩ := hT
  exact finitePrimeEvenLocalFactorTerm_isUnit N p

/-- The bounded inverse of the finite-prime physical Euler factor. -/
noncomputable def finitePrimeEvenResolvent (N : ℕ) :
    evenSubspace →L[ℂ] evenSubspace :=
  ↑((finitePrimeEvenLocalFactor_isUnit N).unit⁻¹)

theorem finitePrimeEvenLocalFactor_mul_resolvent (N : ℕ) :
    finitePrimeEvenLocalFactor N * finitePrimeEvenResolvent N = 1 := by
  let u := (finitePrimeEvenLocalFactor_isUnit N).unit
  change (u : evenSubspace →L[ℂ] evenSubspace) *
      (↑(u⁻¹) : evenSubspace →L[ℂ] evenSubspace) = 1
  exact Units.mul_inv u

theorem finitePrimeEvenResolvent_mul_localFactor (N : ℕ) :
    finitePrimeEvenResolvent N * finitePrimeEvenLocalFactor N = 1 := by
  let u := (finitePrimeEvenLocalFactor_isUnit N).unit
  change (↑(u⁻¹) : evenSubspace →L[ℂ] evenSubspace) *
      (u : evenSubspace →L[ℂ] evenSubspace) = 1
  exact Units.inv_mul u

end RHTower

import GaloisForLFunctions.RHTower.PrimeGammaAllPrimeLaurentAnnihilatorNoGo
import GaloisForLFunctions.RHTower.PrimeLogFiniteOrderUniqueness

/-!
# Finite-order analytic non-erasure of the physical prime--Gamma log curve

At unit clock, the forward and reflected physical prime--Gamma determinants are `-p` and
`(-p)⁻¹`. Their logarithmic moduli therefore trace the physical curve

`p ↦ (log p, -log p)`.

This module proves that no nonzero finite-order entire restriction to that curve can vanish on all
ordinary primes, even after deleting an arbitrary fixed finite exceptional set. This strictly
extends the finite Laurent no-go: the local scalar response may be any finite-order entire function
of the curve parameter. Hence a surviving G-CE all-prime annihilator must be cross-prime,
infinite-order or singular on the physical log curve, or non-scalar before cofinal assembly.

The result is unconditional and contains no RH premise or divisor-selected input.
-/

open Complex

namespace RHTower

noncomputable section

/-- Logarithmic modulus of the forward physical prime--Gamma determinant at unit clock. -/
def primeGammaUnitForwardLogModulusProfile (p : Nat.Primes) : ℂ :=
  Real.log ‖primeGammaUnitForwardDeterminantProfile p‖

@[simp]
theorem primeGammaUnitForwardLogModulusProfile_eq (p : Nat.Primes) :
    primeGammaUnitForwardLogModulusProfile p = Real.log (p : ℕ) := by
  rw [primeGammaUnitForwardLogModulusProfile,
    primeGammaUnitForwardDeterminantProfile_eq, norm_neg]
  norm_cast

/-- Logarithmic modulus of the reflected physical prime--Gamma determinant at unit clock. -/
def primeGammaUnitReflectedLogModulusProfile (p : Nat.Primes) : ℂ :=
  Real.log ‖((primeGammaPhysicalRotationDeterminant (-1) p : ℝ) : ℂ)‖

@[simp]
theorem primeGammaUnitReflectedLogModulusProfile_eq (p : Nat.Primes) :
    primeGammaUnitReflectedLogModulusProfile p = -Real.log (p : ℕ) := by
  rw [primeGammaUnitReflectedLogModulusProfile,
    primeGammaUnitReflectedDeterminant_eq_inv_forward, norm_inv,
    Real.log_inv, primeGammaUnitForwardDeterminantProfile_eq, norm_neg]
  norm_cast

/-- Exact forward/reflected logarithmic physical curve. -/
def primeGammaUnitLogDeterminantCurve (p : Nat.Primes) : ℂ × ℂ :=
  (primeGammaUnitForwardLogModulusProfile p,
    primeGammaUnitReflectedLogModulusProfile p)

@[simp]
theorem primeGammaUnitLogDeterminantCurve_eq (p : Nat.Primes) :
    primeGammaUnitLogDeterminantCurve p =
      (((Real.log (p : ℕ) : ℝ) : ℂ), -((Real.log (p : ℕ) : ℝ) : ℂ)) := by
  ext <;> simp [primeGammaUnitLogDeterminantCurve]

/-- A finite-order entire response on the physical log curve that annihilates every prime outside
a fixed finite exceptional set, while remaining nonzero as a curve response. -/
def GCEPrimeLocalCofiniteFiniteOrderLogCurveAnnihilatorExists
    (E : Finset ℕ) : Prop :=
  ∃ F : EntireFiniteOrder,
    (fun z : ℂ ↦ F z) ≠ 0 ∧
      ∀ p : Nat.Primes, (p : ℕ) ∉ E →
        F (primeGammaUnitForwardLogModulusProfile p) = 0

/-- Cofinite prime annihilation forces every finite-order entire physical-curve response to erase
identically. -/
theorem primeGammaUnitFiniteOrderLogCurve_eq_zero_of_cofinite
    (F : EntireFiniteOrder) (E : Finset ℕ)
    (hzero : ∀ p : Nat.Primes, (p : ℕ) ∉ E →
      F (primeGammaUnitForwardLogModulusProfile p) = 0) :
    (fun z : ℂ ↦ F z) = 0 := by
  apply F.eq_zero_of_cofinite_primeLog_zeros E
  intro p hp hpE
  simpa using hzero ⟨p, hp⟩ hpE

/-- **G-CE route-class kill.** No non-erasing finite-order entire local response on the physical
forward/reflected log-determinant curve can annihilate the all-prime G-CE source, even modulo an
arbitrary fixed finite set of exceptional primes. -/
theorem not_GCEPrimeLocalCofiniteFiniteOrderLogCurveAnnihilatorExists
    (E : Finset ℕ) :
    ¬ GCEPrimeLocalCofiniteFiniteOrderLogCurveAnnihilatorExists E := by
  rintro ⟨F, hF, hzero⟩
  exact hF (primeGammaUnitFiniteOrderLogCurve_eq_zero_of_cofinite F E hzero)

/-- The all-prime specialization of the finite-order analytic G-CE no-go. -/
def GCEPrimeLocalFiniteOrderLogCurveAnnihilatorExists : Prop :=
  GCEPrimeLocalCofiniteFiniteOrderLogCurveAnnihilatorExists ∅

theorem not_GCEPrimeLocalFiniteOrderLogCurveAnnihilatorExists :
    ¬ GCEPrimeLocalFiniteOrderLogCurveAnnihilatorExists :=
  not_GCEPrimeLocalCofiniteFiniteOrderLogCurveAnnihilatorExists ∅

end

end RHTower

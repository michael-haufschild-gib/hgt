import GaloisForLFunctions.HTGeometry.PaperPrimeTerminatingSupport
import GaloisForLFunctions.HTGeometry.PaperNativeInvariantLocalization
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The literal Möbius source has linear prime orbits

Squarefree support gives second-order termination for every prime separately.
Möbius and zeta remain inverse under the formal flow, but zeta has infinite
degree. Thus an ambient unit in every terminating core need not be a unit
of any of those cores. These are exact source identities without estimates.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Squarefree support kills the second native prime derivative of Möbius. -/
theorem paperMoebius_prime_iterate_two (p : Nat.Primes) :
    (primeArithmeticDerivation (p : ℕ) p.property :
        ArithmeticFunction ℂ → ArithmeticFunction ℂ)^[2]
      (ArithmeticFunction.moebius : ArithmeticFunction ℂ) = 0 := by
  apply (paperPrimeArithmetic_iterate_eq_zero_iff_support p _ 2).mpr
  intro n hn
  have hm : ArithmeticFunction.moebius n ≠ 0 := by
    intro h
    exact hn (by simp [ArithmeticFunction.intCoe_apply, h])
  have hs := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hm
  have hle := hs.natFactorization_le_one (p : ℕ)
  omega

/-- The literal Möbius source belongs to every prime's maximal terminating algebra. -/
theorem paperMoebius_mem_prime_terminatingCore (p : Nat.Primes) :
    (ArithmeticFunction.moebius : ArithmeticFunction ℂ) ∈
      paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property) :=
  (paperTerminatingCore_mem_iff _ _).mpr ⟨2, paperMoebius_prime_iterate_two p⟩

/-- Every prime direction has a nonzero derivative on the signed source. -/
theorem paperMoebius_prime_derivative_one (p : Nat.Primes) :
    primeArithmeticDerivation (p : ℕ) p.property
      (ArithmeticFunction.moebius : ArithmeticFunction ℂ) 1 = -1 := by
  have h := paperPrimeArithmetic_iterate_apply p
    (ArithmeticFunction.moebius : ArithmeticFunction ℂ) 1 1
  simpa [ArithmeticFunction.intCoe_apply, ArithmeticFunction.moebius_apply_prime p.property]
    using h

/-- Second-order termination is sharp in every prime direction. -/
theorem paperMoebius_prime_derivative_ne_zero (p : Nat.Primes) :
    primeArithmeticDerivation (p : ℕ) p.property
      (ArithmeticFunction.moebius : ArithmeticFunction ℂ) ≠ 0 := by
  intro h
  have he := congrArg (fun f : ArithmeticFunction ℂ => f 1) h
  rw [paperMoebius_prime_derivative_one, ArithmeticFunction.zero_apply] at he
  exact neg_ne_zero.mpr one_ne_zero he

/-- The complete formal prime orbit of Möbius is an exact linear polynomial. -/
theorem paperMoebius_formal_prime_orbit (p : Nat.Primes) :
    paperArithmeticPrimeFormalFlow p (ArithmeticFunction.moebius : ArithmeticFunction ℂ) =
      PowerSeries.C (ArithmeticFunction.moebius : ArithmeticFunction ℂ) +
        PowerSeries.C (primeArithmeticDerivation (p : ℕ) p.property
          (ArithmeticFunction.moebius : ArithmeticFunction ℂ)) * PowerSeries.X :=
  paperFormalExponential_linear_on _ _ (paperMoebius_prime_iterate_two p)

/-- None of these linear motions is a fixed orbit. -/
theorem paperMoebius_formal_prime_orbit_not_fixed (p : Nat.Primes) :
    paperArithmeticPrimeFormalFlow p (ArithmeticFunction.moebius : ArithmeticFunction ℂ) ≠
      PowerSeries.C (ArithmeticFunction.moebius : ArithmeticFunction ℂ) :=
  (paperFormalExponential_fixed_iff (primeArithmeticDerivation (p : ℕ) p.property)
    (ArithmeticFunction.moebius : ArithmeticFunction ℂ)).not.mpr
      (paperMoebius_prime_derivative_ne_zero p)

/-- The source flow preserves the exact Möbius–zeta convolution inverse identity. -/
theorem paperMoebius_zeta_formal_prime_inverse (p : Nat.Primes) :
    paperArithmeticPrimeFormalFlow p (ArithmeticFunction.moebius : ArithmeticFunction ℂ) *
      paperArithmeticPrimeFormalFlow p (ArithmeticFunction.zeta : ArithmeticFunction ℂ) = 1 := by
  rw [← map_mul, ArithmeticFunction.coe_moebius_mul_coe_zeta, map_one]

/-- Zeta lies outside every prime's terminating algebra despite its terminating inverse. -/
theorem paperZeta_not_mem_prime_terminatingCore (p : Nat.Primes) :
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ) ∉
      paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property) :=
  paperArithmeticPrimeFormalFlow_zeta_not_polynomial p

/-- The original Möbius function is a unit in the full native convolution algebra. -/
theorem paperMoebius_ambient_isUnit :
    IsUnit (ArithmeticFunction.moebius : ArithmeticFunction ℂ) := by
  apply ArithmeticFunction.isUnit_iff_isUnit_apply_one.mpr
  simp [ArithmeticFunction.intCoe_apply]

/-- The literal source as an element of the full prime core. -/
def paperMoebiusInPrimeCore (p : Nat.Primes) :
    paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property) :=
  ⟨(ArithmeticFunction.moebius : ArithmeticFunction ℂ),
    paperMoebius_mem_prime_terminatingCore p⟩

/-- The polynomial core cannot invert its active Möbius element. -/
theorem paperMoebius_not_isUnit_prime_core (p : Nat.Primes) :
    ¬ IsUnit (paperMoebiusInPrimeCore p) := by
  let D := primeArithmeticDerivation (p : ℕ) p.property
  letI : CharZero (paperTerminatingCore D) :=
    charZero_of_injective_algebraMap (algebraMap ℂ (paperTerminatingCore D)).injective
  rintro ⟨u, hu⟩
  have h := paperLocallyNilpotent_kills_unit (k := ℂ) (A := paperTerminatingCore D)
    (paperTerminatingClock D)
    (paperTerminatingClock_locallyNilpotent D) u
  rw [hu] at h
  exact paperMoebius_prime_derivative_ne_zero p (congrArg Subtype.val h)

/-- Finite-prime polynomial charts miss the literal Möbius source. -/
theorem paperMoebius_not_mem_finite_prime_chart (S : Finset Nat.Primes) :
    (ArithmeticFunction.moebius : ArithmeticFunction ℂ) ∉ paperPrimePolynomialAlgebra S := by
  obtain ⟨p, hp⟩ := Infinite.exists_notMem_finset S
  intro hmem
  exact paperMoebius_prime_derivative_ne_zero p
    (paperPrimePolynomialAlgebra_primeDeriv_outside S p
      ⟨(ArithmeticFunction.moebius : ArithmeticFunction ℂ), hmem⟩ hp)

end

end GaloisForLFunctions.HTGeometry

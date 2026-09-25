import GaloisForLFunctions.RHTower.PhotonicParabolicReturn
import GaloisForLFunctions.Core

/-!
# Euler dilation intertwines prime occupation with parabolic return time

The occupation corpus reconstructs a positive integer `primeProduct ν` from
each finite prime-exponent vector.  The PTR return uses the same integer as
the exponent of one fixed parabolic Jordan block.  A diagonal dilation is
multiplicative in that integer and intertwines the fixed block with its
arithmetic power.  Thus the coefficient assembly need not multiply local
parabolic shears or impose bounded-order cross-prime clusters.

This is an algebraic source-assembly bridge, not a physical Maxwell-port
realization, a trace-class construction, or an RH confinement theorem.
-/

namespace RHTower

/-- The multiplicative occupation number acts on the first Jordan coordinate. -/
def photonicEulerDilation (n : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(n : ℂ), 0; 0, 1]

/-- Arithmetic multiplication becomes composition of diagonal dilations. -/
theorem photonicEulerDilation_mul (m n : ℕ) :
    photonicEulerDilation (m * n) =
      photonicEulerDilation m * photonicEulerDilation n := by
  simp [photonicEulerDilation, Nat.cast_mul]

/-- **Euler-to-Jordan transduction.** One fixed unit shear becomes the
arithmetic `n`-fold shear after multiplicative diagonal transport. -/
theorem photonicEulerDilation_intertwines (n : ℕ) :
    photonicEulerDilation n * photonicParabolic =
      photonicParabolic ^ n * photonicEulerDilation n := by
  rw [photonicParabolic_pow]
  simp [photonicEulerDilation, photonicParabolic, photonicUpper]

/-- On a prime-exponent occupation, the exact PTR coefficient is obtained
from its Euler product number by the same fixed-block intertwiner. -/
theorem photonicPrimeOccupationDilation_intertwines
    (ν : Nat.Primes →₀ ℕ) :
    photonicEulerDilation (GaloisForLFunctions.primeProduct ν) * photonicParabolic =
      photonicParabolic ^ (GaloisForLFunctions.primeProduct ν) *
        photonicEulerDilation (GaloisForLFunctions.primeProduct ν) := by
  exact photonicEulerDilation_intertwines _

end RHTower

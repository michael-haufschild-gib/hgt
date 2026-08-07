import GaloisForLFunctions.RHTower.DeningerCalderonWittOrientedSource
import GaloisForLFunctions.RHTower.DeningerOneSidedFramedMateCurvatureTransgression

/-!
# Deninger two-prime oriented boundary wall

The all-prime oriented Calderón--Witt source identifies every normalized
prime orientation in its one-dimensional top cohomology.  In particular,
the difference between the prime-two and prime-three orientation cochains is
the boundary of its canonical top Green lift.

The prime-indexed Deninger physical reporter is defined before choosing a
divisor.  On that one explicit source boundary it reads the difference of
the two half-density mate gains.  Its value vanishes exactly when the
spectral parameter lies on the critical line.  Thus the full Route-L strict
descent problem already contains one finite, canonical two-prime boundary
wall; no infinite completion is needed to state the remaining obstruction.

This file does not assert that the physical reporter annihilates the source
boundary.  It proves unconditionally that such annihilation is equivalent
to the critical-line equation.
-/

open Complex

namespace RHTower

noncomputable section

/-- Normalized global top cochain carried by one ordinary prime. -/
def deningerCalderonWittGlobalPrimeOrientationCochain
    (p : Nat.Primes) :
    DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ :=
  (deningerCalderonWittGlobalPrimeCenterOrientationSection p 1, 0)

@[simp]
theorem deningerCalderonWittGlobalOrientedTrace_primeOrientationCochain
    (p : Nat.Primes) :
    deningerCalderonWittGlobalOrientedTrace
        (deningerCalderonWittGlobalPrimeOrientationCochain p) = 1 := by
  simp [deningerCalderonWittGlobalPrimeOrientationCochain,
    deningerCalderonWittGlobalOrientedTrace]

/-- Prime-indexed physical reporter on the global oriented top source.
The direct sum makes the displayed prime sum finite on every source
cochain.  The auxiliary Arakelov coordinate is deliberately ignored. -/
def deningerCalderonWittPrimeIndexedPhysicalOrientationReporter
    (s : ℂ) :
    (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) →ₗ[ℂ] ℂ :=
  (DirectSum.toModule ℂ Nat.Primes ℂ
      (fun p =>
        (((deningerHalfDensityMateGain (p : ℕ) s : ℂ) - 1) •
          deningerCalderonWittAlgebraicCenterTrace p))).comp
    (LinearMap.fst ℂ DeningerCalderonWittAlgebraicGlobalDegreeTwo ℂ)

@[simp]
theorem deningerCalderonWittPrimeIndexedPhysicalOrientationReporter_prime
    (s : ℂ) (p : Nat.Primes) :
    deningerCalderonWittPrimeIndexedPhysicalOrientationReporter s
        (deningerCalderonWittGlobalPrimeOrientationCochain p) =
      (deningerHalfDensityMateGain (p : ℕ) s : ℂ) - 1 := by
  simp [deningerCalderonWittPrimeIndexedPhysicalOrientationReporter,
    deningerCalderonWittGlobalPrimeOrientationCochain,
    deningerCalderonWittGlobalPrimeCenterOrientationSection]

/-- Canonical Green primitive of the difference between two normalized
prime-orientation cochains. -/
def deningerCalderonWittTwoPrimeOrientationGreenBoundaryWitness
    (p q : Nat.Primes) :
    ⋀[ℂ]^2 DeningerCalderonWittAlgebraicGlobalDegreeOne :=
  deningerCalderonWittGlobalOrientedTopGreenLift
    (deningerCalderonWittGlobalPrimeOrientationCochain p -
      deningerCalderonWittGlobalPrimeOrientationCochain q)

/-- The two normalized prime orientations are cohomologous through the
literal canonical top Green lift. -/
theorem deningerCalderonWittGlobalOrientedBoundary_twoPrimeWitness
    (p q : Nat.Primes) :
    deningerCalderonWittGlobalOrientedBoundary
        (deningerCalderonWittTwoPrimeOrientationGreenBoundaryWitness p q) =
      deningerCalderonWittGlobalPrimeOrientationCochain p -
        deningerCalderonWittGlobalPrimeOrientationCochain q := by
  have hdecomp :=
    deningerCalderonWittGlobalOrientedTopGreenDecomposition
      (deningerCalderonWittGlobalPrimeOrientationCochain p -
        deningerCalderonWittGlobalPrimeOrientationCochain q)
  have htrace :
      deningerCalderonWittGlobalOrientedTrace
          (deningerCalderonWittGlobalPrimeOrientationCochain p -
            deningerCalderonWittGlobalPrimeOrientationCochain q) = 0 := by
    rw [map_sub]
    simp
  simpa [deningerCalderonWittTwoPrimeOrientationGreenBoundaryWitness,
    htrace] using hdecomp

/-- Exact physical value of the canonical two-prime source boundary. -/
theorem deningerCalderonWittPrimeIndexedPhysicalReporter_twoPrimeWitness
    (s : ℂ) (p q : Nat.Primes) :
    deningerCalderonWittPrimeIndexedPhysicalOrientationReporter s
        (deningerCalderonWittGlobalOrientedBoundary
          (deningerCalderonWittTwoPrimeOrientationGreenBoundaryWitness p q)) =
      (deningerHalfDensityMateGain (p : ℕ) s : ℂ) -
        deningerHalfDensityMateGain (q : ℕ) s := by
  rw [deningerCalderonWittGlobalOrientedBoundary_twoPrimeWitness, map_sub]
  simp

/-- The two literal primes used by the minimal Route-L wall. -/
def deningerCalderonWittPrimeTwo : Nat.Primes := ⟨2, by norm_num⟩

/-- The second literal prime used by the minimal Route-L wall. -/
def deningerCalderonWittPrimeThree : Nat.Primes := ⟨3, by norm_num⟩

/-- Equality of the prime-two and prime-three mate gains is exactly the
critical-line equation. -/
theorem deningerHalfDensityMateGain_two_eq_three_iff (s : ℂ) :
    deningerHalfDensityMateGain 2 s =
        deningerHalfDensityMateGain 3 s ↔
      s.re = 1 / 2 := by
  constructor
  · intro hgain
    rw [deningerHalfDensityMateGain, deningerHalfDensityMateGain] at hgain
    have hexp :
        (2 * s.re - 1) * Real.log 2 =
          (2 * s.re - 1) * Real.log 3 :=
      Real.exp_injective hgain
    have hprod :
        (2 * s.re - 1) * (Real.log 2 - Real.log 3) = 0 := by
      calc
        (2 * s.re - 1) * (Real.log 2 - Real.log 3) =
            (2 * s.re - 1) * Real.log 2 -
              (2 * s.re - 1) * Real.log 3 := by ring
        _ = 0 := sub_eq_zero.mpr hexp
    have hlog : Real.log 2 < Real.log 3 :=
      Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
    have ht : 2 * s.re - 1 = 0 :=
      (mul_eq_zero.mp hprod).resolve_right
        (sub_ne_zero.mpr (ne_of_lt hlog))
    linarith
  · intro hs
    rw [deningerHalfDensityMateGain, deningerHalfDensityMateGain]
    have ht : 2 * s.re - 1 = 0 := by linarith
    simp [ht]

/-- **Minimal two-prime Route-L wall.**  The prime-indexed physical reporter
annihilates the one canonical prime-two/prime-three Green boundary exactly on
the critical line. -/
theorem
    deningerCalderonWittPrimeIndexedPhysicalReporter_twoPrimeBoundary_eq_zero_iff
    (s : ℂ) :
    deningerCalderonWittPrimeIndexedPhysicalOrientationReporter s
        (deningerCalderonWittGlobalOrientedBoundary
          (deningerCalderonWittTwoPrimeOrientationGreenBoundaryWitness
            deningerCalderonWittPrimeTwo
            deningerCalderonWittPrimeThree)) = 0 ↔
      s.re = 1 / 2 := by
  rw [deningerCalderonWittPrimeIndexedPhysicalReporter_twoPrimeWitness]
  change
    ((deningerHalfDensityMateGain 2 s : ℂ) -
        deningerHalfDensityMateGain 3 s = 0) ↔ _
  rw [sub_eq_zero, Complex.ofReal_inj]
  exact deningerHalfDensityMateGain_two_eq_three_iff s

/-- Multiplication by any nonzero leading Xi calibration preserves the
minimal two-prime boundary wall. -/
theorem
    deningerCalderonWittPrimeIndexedPhysicalReporter_twoPrimeBoundary_mul_eq_zero_iff
    (s c : ℂ) (hc : c ≠ 0) :
    c * deningerCalderonWittPrimeIndexedPhysicalOrientationReporter s
        (deningerCalderonWittGlobalOrientedBoundary
          (deningerCalderonWittTwoPrimeOrientationGreenBoundaryWitness
            deningerCalderonWittPrimeTwo
            deningerCalderonWittPrimeThree)) = 0 ↔
      s.re = 1 / 2 := by
  rw [mul_eq_zero]
  simp only [hc, false_or]
  exact
    deningerCalderonWittPrimeIndexedPhysicalReporter_twoPrimeBoundary_eq_zero_iff s

end

end RHTower

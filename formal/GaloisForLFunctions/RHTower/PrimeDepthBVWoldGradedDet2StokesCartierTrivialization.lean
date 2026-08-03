import GaloisForLFunctions.RHTower.PrimeDepthBVWoldGradedDet2ScalarDescentBoundary

/-!
# Source Stokes/Cartier trivialization of the graded det2 class

Reflection negates the centered Xi rate.  Hence the explicit graded-det2
anomaly and its reflected partner are reciprocal on every labelled
prime/depth triangle.  This file packages that identity as a determinant-one
reflection double and proves that its hyperbolic Stokes pairing is preserved.
This is an unconditional source Cartier trivialization retaining the divisor
reflection and all prime/depth labels.

The same construction exposes a sharp no-go.  Reflection-hyperbolic
triviality holds for every real rate, whereas preservation of the positive
same-fibre diagonal holds on the exact three-depth witness precisely at rate
zero.  On the actual Xi specialization that diagonal descent is equivalent
to the critical line, and global diagonal descent is equivalent to RH.
Thus determinant-one or indefinite Stokes conservation cannot supply the
missing pointwise annihilation; a source-created positive same-fibre
polarization is the exact remaining producer.
-/

namespace RHTower

noncomputable section

/-! ## Reflection double and hyperbolic Stokes form -/

/-- Reflection double of the scalar graded-det2 anomaly fibre. -/
abbrev PrimeDepthBVWoldGradedDet2ReflectionDouble := ℝ × ℝ

/-- Hyperbolic Stokes pairing between the original and reflected anomaly
channels. -/
def primeDepthBVWoldGradedDet2StokesPairing
    (x y : PrimeDepthBVWoldGradedDet2ReflectionDouble) : ℝ :=
  x.1 * y.2 + x.2 * y.1

/-- Positive same-fibre Cartier diagonal inside the reflection double. -/
def primeDepthBVWoldGradedDet2CartierDiagonal :
    PrimeDepthBVWoldGradedDet2ReflectionDouble :=
  (1, 1)

/-- Original/reflected diagonal anomaly transport.  The second channel is
constructed by source reflection `a ↦ -a`, not by choosing an inverse after
specialization. -/
def primeDepthBVWoldGradedDet2ReflectedTransport
    (a : ℝ) (i j k : PrimeDepthBVWoldCell)
    (x : PrimeDepthBVWoldGradedDet2ReflectionDouble) :
    PrimeDepthBVWoldGradedDet2ReflectionDouble :=
  (primeDepthBVWoldGradedDet2Anomaly a i j k * x.1,
    primeDepthBVWoldGradedDet2Anomaly (-a) i j k * x.2)

/-- **Reflection Cartier trivialization.**  Original and reflected anomaly
factors have product one on every fully labelled source triangle. -/
theorem primeDepthBVWoldGradedDet2Anomaly_mul_reflection
    (a : ℝ) (i j k : PrimeDepthBVWoldCell) :
    primeDepthBVWoldGradedDet2Anomaly a i j k *
        primeDepthBVWoldGradedDet2Anomaly (-a) i j k = 1 := by
  rw [primeDepthBVWoldGradedDet2Anomaly,
    primeDepthBVWoldGradedDet2Anomaly, ← Real.exp_add]
  convert Real.exp_zero using 1
  ring

/-- The reflection double preserves its hyperbolic Stokes pairing for every
rate.  This is stronger than determinant-one but remains indefinite. -/
theorem primeDepthBVWoldGradedDet2ReflectedTransport_preserves_stokesPairing
    (a : ℝ) (i j k : PrimeDepthBVWoldCell)
    (x y : PrimeDepthBVWoldGradedDet2ReflectionDouble) :
    primeDepthBVWoldGradedDet2StokesPairing
        (primeDepthBVWoldGradedDet2ReflectedTransport a i j k x)
        (primeDepthBVWoldGradedDet2ReflectedTransport a i j k y) =
      primeDepthBVWoldGradedDet2StokesPairing x y := by
  rw [primeDepthBVWoldGradedDet2StokesPairing,
    primeDepthBVWoldGradedDet2ReflectedTransport,
    primeDepthBVWoldGradedDet2ReflectedTransport]
  have h := primeDepthBVWoldGradedDet2Anomaly_mul_reflection a i j k
  calc
    _ = (primeDepthBVWoldGradedDet2Anomaly a i j k *
          primeDepthBVWoldGradedDet2Anomaly (-a) i j k) *
        (x.1 * y.2 + x.2 * y.1) := by ring
    _ = x.1 * y.2 + x.2 * y.1 := by rw [h, one_mul]

/-- The same-fibre Cartier diagonal is positive for the hyperbolic form. -/
theorem primeDepthBVWoldGradedDet2CartierDiagonal_stokesPositive :
    primeDepthBVWoldGradedDet2StokesPairing
        primeDepthBVWoldGradedDet2CartierDiagonal
        primeDepthBVWoldGradedDet2CartierDiagonal = 2 := by
  change (1 : ℝ) * 1 + 1 * 1 = 2
  ring

/-! ## Exact boundary between indefinite and positive trivialization -/

/-- The transported Cartier vector remains in the same-fibre diagonal
exactly when the anomaly exponent vanishes. -/
theorem primeDepthBVWoldGradedDet2ReflectedTransport_cartierDiagonal_iff
    (a : ℝ) (i j k : PrimeDepthBVWoldCell) :
    (primeDepthBVWoldGradedDet2ReflectedTransport a i j k
          primeDepthBVWoldGradedDet2CartierDiagonal).1 =
        (primeDepthBVWoldGradedDet2ReflectedTransport a i j k
          primeDepthBVWoldGradedDet2CartierDiagonal).2 ↔
      a * primeDepthBVWoldConsecutiveIncrementArea i j k = 0 := by
  simp only [primeDepthBVWoldGradedDet2ReflectedTransport,
    primeDepthBVWoldGradedDet2CartierDiagonal,
    primeDepthBVWoldGradedDet2Anomaly, mul_one]
  rw [Real.exp_injective.eq_iff]
  constructor
  · intro h
    linarith
  · intro h
    linear_combination -2 * h

/-- On the exact same-prime three-depth curvature witness, positive diagonal
descent is equivalent to zero centered rate. -/
theorem primeDepthBVWoldGradedDet2ReflectedTransport_cartierDiagonal_witness_iff
    (a : ℝ) :
    (primeDepthBVWoldGradedDet2ReflectedTransport a
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
          primeDepthBVWoldWitnessTwo
          primeDepthBVWoldGradedDet2CartierDiagonal).1 =
        (primeDepthBVWoldGradedDet2ReflectedTransport a
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
          primeDepthBVWoldWitnessTwo
          primeDepthBVWoldGradedDet2CartierDiagonal).2 ↔
      a = 0 := by
  rw [primeDepthBVWoldGradedDet2ReflectedTransport_cartierDiagonal_iff,
    primeDepthBVWoldConsecutiveIncrementArea_eq_curvature]
  exact mul_eq_zero_iff_right
    primeDepthBVWoldAdditiveCurvature_witness_ne_zero

/-- Concrete no-go witness: determinant-one and hyperbolic Stokes
trivializations hold at nonzero rate, but positive diagonal descent fails. -/
theorem primeDepthBVWoldGradedDet2StokesCartierTrivialization_strictNoGo :
    primeDepthBVWoldGradedDet2Anomaly 1
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
          primeDepthBVWoldWitnessTwo *
        primeDepthBVWoldGradedDet2Anomaly (-1)
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
          primeDepthBVWoldWitnessTwo = 1 ∧
      primeDepthBVWoldGradedDet2StokesPairing
          (primeDepthBVWoldGradedDet2ReflectedTransport 1
            primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
            primeDepthBVWoldWitnessTwo
            primeDepthBVWoldGradedDet2CartierDiagonal)
          (primeDepthBVWoldGradedDet2ReflectedTransport 1
            primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
            primeDepthBVWoldWitnessTwo
            primeDepthBVWoldGradedDet2CartierDiagonal) =
        primeDepthBVWoldGradedDet2StokesPairing
          primeDepthBVWoldGradedDet2CartierDiagonal
          primeDepthBVWoldGradedDet2CartierDiagonal ∧
      (primeDepthBVWoldGradedDet2ReflectedTransport 1
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
          primeDepthBVWoldWitnessTwo
          primeDepthBVWoldGradedDet2CartierDiagonal).1 ≠
        (primeDepthBVWoldGradedDet2ReflectedTransport 1
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
          primeDepthBVWoldWitnessTwo
          primeDepthBVWoldGradedDet2CartierDiagonal).2 := by
  refine ⟨primeDepthBVWoldGradedDet2Anomaly_mul_reflection 1 _ _ _,
    primeDepthBVWoldGradedDet2ReflectedTransport_preserves_stokesPairing
      1 _ _ _ _ _, ?_⟩
  intro hdiag
  have hzero :=
    (primeDepthBVWoldGradedDet2ReflectedTransport_cartierDiagonal_witness_iff
      1).mp hdiag
  exact one_ne_zero hzero

/-! ## Actual Xi reflection and the RH-bearing positive descent -/

/-- Divisor-resolved reflection balance.  Both Xi divisor labels remain
explicit; no quotient or sum erases their provenance. -/
theorem primeDepthBVWoldXiGradedDet2Anomaly_mul_reflection
    (rho : XiDivisorSupport) (i j k : PrimeDepthBVWoldCell) :
    primeDepthBVWoldGradedDet2Anomaly
          (primeDepthBVWoldXiCenteredRate rho) i j k *
        primeDepthBVWoldGradedDet2Anomaly
          (primeDepthBVWoldXiCenteredRate (xiZeroLineConjEquiv rho))
            i j k = 1 := by
  rw [primeDepthBVWoldXiCenteredRate_reflection]
  exact primeDepthBVWoldGradedDet2Anomaly_mul_reflection
    (primeDepthBVWoldXiCenteredRate rho) i j k

/-- At each actual Xi divisor point, positive same-fibre Cartier descent on
the witness is equivalent to the critical-line equation. -/
theorem primeDepthBVWoldXiGradedDet2CartierDiagonal_witness_iff
    (rho : XiDivisorSupport) :
    (primeDepthBVWoldGradedDet2ReflectedTransport
          (primeDepthBVWoldXiCenteredRate rho)
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
          primeDepthBVWoldWitnessTwo
          primeDepthBVWoldGradedDet2CartierDiagonal).1 =
        (primeDepthBVWoldGradedDet2ReflectedTransport
          (primeDepthBVWoldXiCenteredRate rho)
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
          primeDepthBVWoldWitnessTwo
          primeDepthBVWoldGradedDet2CartierDiagonal).2 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [primeDepthBVWoldGradedDet2ReflectedTransport_cartierDiagonal_witness_iff,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Global positive same-fibre descent proposition. -/
def PrimeDepthBVWoldXiGradedDet2CartierDiagonalDescends : Prop :=
  ∀ rho : XiDivisorSupport,
    (primeDepthBVWoldGradedDet2ReflectedTransport
          (primeDepthBVWoldXiCenteredRate rho)
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
          primeDepthBVWoldWitnessTwo
          primeDepthBVWoldGradedDet2CartierDiagonal).1 =
      (primeDepthBVWoldGradedDet2ReflectedTransport
          (primeDepthBVWoldXiCenteredRate rho)
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
          primeDepthBVWoldWitnessTwo
          primeDepthBVWoldGradedDet2CartierDiagonal).2

/-- Positive diagonal descent is exactly triviality of the explicit
graded-det2 scalar counterboundary on the actual leading Xi conormal. -/
theorem primeDepthBVWoldXiGradedDet2CartierDiagonalDescends_iff_boundaryTrivial :
    PrimeDepthBVWoldXiGradedDet2CartierDiagonalDescends ↔
      PrimeDepthBVWoldXiGradedDet2BoundaryTrivial := by
  constructor
  · intro h rho
    exact
      (primeDepthBVWoldXiGradedDet2Boundary_leadingConormal_eq_zero_iff rho).mpr
        ((primeDepthBVWoldXiGradedDet2CartierDiagonal_witness_iff rho).mp
          (h rho))
  · intro h rho
    exact
      (primeDepthBVWoldXiGradedDet2CartierDiagonal_witness_iff rho).mpr
        ((primeDepthBVWoldXiGradedDet2Boundary_leadingConormal_eq_zero_iff rho).mp
          (h rho))

/-- Exact frontier theorem: global positive same-fibre Cartier descent is
equivalent to the Riemann hypothesis.  The reflection-hyperbolic
trivialization above does not prove this proposition. -/
theorem primeDepthBVWoldXiGradedDet2CartierDiagonalDescends_iff_riemannHypothesis :
    PrimeDepthBVWoldXiGradedDet2CartierDiagonalDescends ↔
      RiemannHypothesis := by
  rw [primeDepthBVWoldXiGradedDet2CartierDiagonalDescends_iff_boundaryTrivial,
    primeDepthBVWoldXiGradedDet2BoundaryTrivial_iff_riemannHypothesis]

end

end RHTower

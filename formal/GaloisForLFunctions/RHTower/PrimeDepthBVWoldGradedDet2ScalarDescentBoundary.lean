import GaloisForLFunctions.RHTower.PrimeDepthBVWoldResolvedXiLandingAnnihilation
import GaloisForLFunctions.RHTower.PrimeEssentialEdgeOccupationDet2BVRelativeClass

/-!
# Graded det2 scalar-descent counterboundary

The scalar BV--Wold connection has nonzero triangle curvature, while its
two-coordinate source frame is flat.  This file constructs the missing
same-grade scalar counterterm independently from that curved square.

The actual essential-edge occupation operator has quadratic trace
`q = zeta(2)`.  Consecutive BV-mass and Wold-clock increments define two
crossed parity channels.  Their normalized supertrace contraction is exactly
the oriented triangle curvature.  Consequently their graded Hilbert--Carleman
anomaly is the inverse scalar holonomy.  Adding the resulting degree-two
counterboundary to `D1 D0` gives zero unconditionally, including on the actual
nonzero leading Xi conormal.

This corrected square is not RH: the counterboundary itself vanishes on the
three-depth witness exactly on the critical line, and global triviality is
equivalent to RH.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## Consecutive source increments and their oriented area -/

/-- Singular BV-mass increment on an oriented prime/depth edge. -/
def primeDepthBVWoldMassIncrement
    (i j : PrimeDepthBVWoldCell) : ℝ :=
  primeDepthBVFirstTraceDepthWeight j -
    primeDepthBVFirstTraceDepthWeight i

/-- Regular Wold--Gamma clock increment on an oriented prime/depth edge. -/
def primeDepthBVWoldClockIncrement
    (i j : PrimeDepthBVWoldCell) : ℝ :=
  xiGammaEulerPrimitivePrimeDepthLogClock j -
    xiGammaEulerPrimitivePrimeDepthLogClock i

/-- Symplectic area of two consecutive source increments. -/
def primeDepthBVWoldConsecutiveIncrementArea
    (i j k : PrimeDepthBVWoldCell) : ℝ :=
  primeDepthBVWoldMassIncrement i j *
      primeDepthBVWoldClockIncrement j k -
    primeDepthBVWoldClockIncrement i j *
      primeDepthBVWoldMassIncrement j k

/-- Consecutive-increment area is exactly the existing additive curvature.
This identity uses only the two source records. -/
theorem primeDepthBVWoldConsecutiveIncrementArea_eq_curvature
    (i j k : PrimeDepthBVWoldCell) :
    primeDepthBVWoldConsecutiveIncrementArea i j k =
      primeDepthBVWoldAdditiveCurvature i j k := by
  rw [primeDepthBVWoldConsecutiveIncrementArea,
    primeDepthBVWoldMassIncrement, primeDepthBVWoldMassIncrement,
    primeDepthBVWoldClockIncrement, primeDepthBVWoldClockIncrement,
    primeDepthBVWoldAdditiveCurvature,
    primeDepthBVWoldConnection, primeDepthBVWoldConnection,
    primeDepthBVWoldConnection]
  ring

/-! ## Actual occupation trace and crossed graded contraction -/

/-- Quadratic trace of the actual essential-edge occupation operator. -/
def primeDepthBVWoldOccupationQuadraticTrace : ℂ :=
  HilbertSchmidt.hsTraceDiag
    (HilbertSchmidt.hsPow
      primeFirstTraceEssentialEdgeOccupationKernel 1)

theorem primeDepthBVWoldOccupationQuadraticTrace_eq_riemannZeta_two :
    primeDepthBVWoldOccupationQuadraticTrace = riemannZeta 2 := by
  exact primeFirstTraceEssentialEdgeOccupationKernel_quadraticTrace

theorem primeDepthBVWoldOccupationQuadraticTrace_ne_zero :
    primeDepthBVWoldOccupationQuadraticTrace ≠ 0 := by
  rw [primeDepthBVWoldOccupationQuadraticTrace_eq_riemannZeta_two]
  exact riemannZeta_ne_zero_of_one_lt_re (by norm_num)

/-- Coefficients of a parity-preserving operator on the graded double of the
actual occupation space.  Both entries multiply the same occupation kernel;
the first is even and the second odd. -/
abbrev PrimeDepthBVWoldGradedOccupationCoefficient := ℂ × ℂ

/-- First polarized leg: modular rate times the consecutive BV/clock
increment, normalized by the actual occupation quadratic trace. -/
def primeDepthBVWoldGradedOccupationSourceLeg
    (a : ℝ) (i j : PrimeDepthBVWoldCell) :
    PrimeDepthBVWoldGradedOccupationCoefficient :=
  ((((a * primeDepthBVWoldMassIncrement i j : ℝ) : ℂ) /
      primeDepthBVWoldOccupationQuadraticTrace),
    (((a * primeDepthBVWoldClockIncrement i j : ℝ) : ℂ) /
      primeDepthBVWoldOccupationQuadraticTrace))

/-- Crossed second leg.  The parity swap converts ordinary symmetric trace
pairing into the oriented BV/clock area. -/
def primeDepthBVWoldGradedOccupationCrossLeg
    (j k : PrimeDepthBVWoldCell) :
    PrimeDepthBVWoldGradedOccupationCoefficient :=
  ((primeDepthBVWoldClockIncrement j k : ℂ),
    (primeDepthBVWoldMassIncrement j k : ℂ))

/-- Supertrace of the product of two parity-diagonal scalar multiples of the
actual occupation kernel. -/
def primeDepthBVWoldGradedOccupationSupertracePair
    (x y : PrimeDepthBVWoldGradedOccupationCoefficient) : ℂ :=
  (x.1 * y.1 - x.2 * y.2) *
    primeDepthBVWoldOccupationQuadraticTrace

/-- The normalized graded occupation contraction is the scalar curvature.
Neither connection nor curvature occurs in either operator leg. -/
theorem primeDepthBVWoldGradedOccupationSupertracePair_source_cross
    (a : ℝ) (i j k : PrimeDepthBVWoldCell) :
    primeDepthBVWoldGradedOccupationSupertracePair
        (primeDepthBVWoldGradedOccupationSourceLeg a i j)
        (primeDepthBVWoldGradedOccupationCrossLeg j k) =
      ((a * primeDepthBVWoldAdditiveCurvature i j k : ℝ) : ℂ) := by
  rw [primeDepthBVWoldGradedOccupationSupertracePair,
    primeDepthBVWoldGradedOccupationSourceLeg,
    primeDepthBVWoldGradedOccupationCrossLeg]
  field_simp [primeDepthBVWoldOccupationQuadraticTrace_ne_zero]
  push_cast
  rw [← primeDepthBVWoldConsecutiveIncrementArea_eq_curvature]
  rw [primeDepthBVWoldConsecutiveIncrementArea]
  ring

/-! ## Multiplicative anomaly and scalar counterboundary -/

/-- Global exponential anomaly defined directly from crossed source
increments.  The definition does not mention scalar curvature or holonomy. -/
def primeDepthBVWoldGradedDet2Anomaly
    (a : ℝ) (i j k : PrimeDepthBVWoldCell) : ℝ :=
  Real.exp
    (-a * primeDepthBVWoldConsecutiveIncrementArea i j k)

/-- Operator realization of the same anomaly as the exponential of the
negative graded Hilbert--Carleman contraction. -/
theorem primeDepthBVWoldGradedDet2Anomaly_eq_supertraceExp
    (a : ℝ) (i j k : PrimeDepthBVWoldCell) :
    (primeDepthBVWoldGradedDet2Anomaly a i j k : ℂ) =
      Complex.exp
        (-primeDepthBVWoldGradedOccupationSupertracePair
          (primeDepthBVWoldGradedOccupationSourceLeg a i j)
          (primeDepthBVWoldGradedOccupationCrossLeg j k)) := by
  rw [primeDepthBVWoldGradedOccupationSupertracePair_source_cross]
  simp only [primeDepthBVWoldGradedDet2Anomaly, Complex.ofReal_exp,
    Complex.ofReal_neg, Complex.ofReal_mul]

theorem primeDepthBVWoldGradedDet2Anomaly_pos
    (a : ℝ) (i j k : PrimeDepthBVWoldCell) :
    0 < primeDepthBVWoldGradedDet2Anomaly a i j k :=
  Real.exp_pos _

/-- **Inverse-holonomy law.**  The independently constructed graded anomaly
is the exact inverse of scalar Route-R triangle holonomy. -/
theorem primeDepthBVWoldTransport_mul_gradedDet2Anomaly
    (a : ℝ) (i j k : PrimeDepthBVWoldCell) :
    primeDepthBVWoldTransport a i j *
        primeDepthBVWoldTransport a j k *
          primeDepthBVWoldGradedDet2Anomaly a i j k =
      primeDepthBVWoldTransport a i k := by
  rw [primeDepthBVWoldTransport, primeDepthBVWoldTransport,
    primeDepthBVWoldTransport, primeDepthBVWoldGradedDet2Anomaly,
    primeDepthBVWoldConsecutiveIncrementArea_eq_curvature,
    primeDepthBVWoldAdditiveCurvature,
    primeDepthBVWoldConnection_swap k i,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- Equal-grade additive counterboundary induced by the multiplicative
graded anomaly. -/
def primeDepthBVWoldGradedDet2ScalarDescentBoundary (a : ℝ) :
    PrimeDepthBVWoldZeroCochain →ₗ[ℂ] PrimeDepthBVWoldTwoCochain where
  toFun f i j k :=
    ((primeDepthBVWoldTransport a i j *
        primeDepthBVWoldTransport a j k : ℝ) : ℂ) *
      ((primeDepthBVWoldGradedDet2Anomaly a i j k : ℂ) - 1) *
        f k
  map_add' f g := by
    funext i j k
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext i j k
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

/-- **Unconditional corrected square.**  The curved scalar square and the
independent same-grade graded-det2 boundary cancel on every scalar section. -/
theorem primeDepthBVWoldCovariantD1_comp_D0_add_gradedDet2Boundary
    (a : ℝ) (f : PrimeDepthBVWoldZeroCochain)
    (i j k : PrimeDepthBVWoldCell) :
    primeDepthBVWoldCovariantD1 a
          (primeDepthBVWoldCovariantD0 a f) i j k +
        primeDepthBVWoldGradedDet2ScalarDescentBoundary a f i j k = 0 := by
  rw [primeDepthBVWoldCovariantD1_comp_D0_apply,
    primeDepthBVWoldGradedDet2ScalarDescentBoundary]
  have h := primeDepthBVWoldTransport_mul_gradedDet2Anomaly a i j k
  push_cast at h ⊢
  linear_combination h * f k

/-! ## Divisor resolution and the actual Xi conormal -/

/-- Pointwise Xi-divisor version of the same source-defined boundary. -/
def primeDepthBVWoldXiGradedDet2ScalarDescentBoundary :
    PrimeDepthBVWoldXiZeroCochain →ₗ[ℂ]
      PrimeDepthBVWoldXiTwoCochain where
  toFun f rho :=
    primeDepthBVWoldGradedDet2ScalarDescentBoundary
      (primeDepthBVWoldXiCenteredRate rho) (f rho)
  map_add' f g := by
    funext rho i j k
    simp only [Pi.add_apply, map_add]
  map_smul' c f := by
    funext rho i j k
    simp only [Pi.smul_apply, RingHom.id_apply, map_smul]

/-- Source-derived corrected annihilation on the actual nonzero leading Xi
conormal. -/
theorem primeDepthBVWoldXiCovariantD1_comp_D0_add_gradedDet2Boundary_leadingConormal
    (rho : XiDivisorSupport) (i j k : PrimeDepthBVWoldCell) :
    primeDepthBVWoldXiCovariantD1
          (primeDepthBVWoldXiCovariantD0
            primeDepthBVWoldXiScalarLeadingConormal) rho i j k +
        primeDepthBVWoldXiGradedDet2ScalarDescentBoundary
          primeDepthBVWoldXiScalarLeadingConormal rho i j k = 0 := by
  exact primeDepthBVWoldCovariantD1_comp_D0_add_gradedDet2Boundary
    (primeDepthBVWoldXiCenteredRate rho)
    (primeDepthBVWoldXiScalarLeadingConormal rho) i j k

/-- Sharpness: on the same actual Xi conormal and exact three-depth witness,
the counterboundary itself vanishes exactly on the critical line. -/
theorem primeDepthBVWoldXiGradedDet2Boundary_leadingConormal_eq_zero_iff
    (rho : XiDivisorSupport) :
    primeDepthBVWoldXiGradedDet2ScalarDescentBoundary
        primeDepthBVWoldXiScalarLeadingConormal rho
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
            primeDepthBVWoldWitnessTwo = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  let square :=
    primeDepthBVWoldXiCovariantD1
        (primeDepthBVWoldXiCovariantD0
          primeDepthBVWoldXiScalarLeadingConormal)
          rho primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
            primeDepthBVWoldWitnessTwo
  let boundary :=
    primeDepthBVWoldXiGradedDet2ScalarDescentBoundary
        primeDepthBVWoldXiScalarLeadingConormal rho
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
            primeDepthBVWoldWitnessTwo
  have hsum : square + boundary = 0 :=
    primeDepthBVWoldXiCovariantD1_comp_D0_add_gradedDet2Boundary_leadingConormal
      rho primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
        primeDepthBVWoldWitnessTwo
  have hsquare : square = 0 ↔ (rho : ℂ).re = 1 / 2 :=
    primeDepthBVWoldXiCovariant_square_scalarLeadingConormal_eq_zero_iff rho
  constructor
  · intro hb
    apply hsquare.mp
    rw [hb, add_zero] at hsum
    exact hsum
  · intro hline
    have hs : square = 0 := hsquare.mpr hline
    rw [hs, zero_add] at hsum
    exact hsum

/-- Global triviality of the explicit counterboundary on the actual leading
Xi conormal. -/
def PrimeDepthBVWoldXiGradedDet2BoundaryTrivial : Prop :=
  ∀ rho : XiDivisorSupport,
    primeDepthBVWoldXiGradedDet2ScalarDescentBoundary
        primeDepthBVWoldXiScalarLeadingConormal rho
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
            primeDepthBVWoldWitnessTwo = 0

/-- The corrected square is unconditional, but triviality of its explicit
counterboundary remains exactly RH. -/
theorem primeDepthBVWoldXiGradedDet2BoundaryTrivial_iff_riemannHypothesis :
    PrimeDepthBVWoldXiGradedDet2BoundaryTrivial ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply rh_iff_xi_ne_zero_right.mpr
    intro z hz hzero
    let rho : XiDivisorSupport :=
      ⟨z, mem_xi_divisor_support_of_eq_zero hzero⟩
    have hline : z.re = 1 / 2 :=
      (primeDepthBVWoldXiGradedDet2Boundary_leadingConormal_eq_zero_iff
        rho).mp (h rho)
    have hzgt : 1 / 2 < z.re := mem_rightHalf.mp hz
    linarith
  · intro hRH rho
    exact
      (primeDepthBVWoldXiGradedDet2Boundary_leadingConormal_eq_zero_iff
        rho).mpr (xi_divisor_support_re_eq_half_of_rh hRH rho)

end

end RHTower

import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualEigenEquation

/-!
# Actual modular Green-current boundary cancellation

Corpus conjecture C-A.9s is the first route-killing boundary test after actual
modularity and the actual Poincaré eigen-equation.  This module proves:

* exact translation laws for horizontal and vertical first jets;
* exact anti-invariance of the radial first jet under inversion on the unit
  semicircle, derived seed by seed and lifted through the primitive-pair sum;
* the pointwise Green--Lagrange interior identity for two completed Poincaré
  eigenfunctions, with zero interior source at equal eigenvalue;
* exact cancellation of paired vertical and circular noncusp Green currents;
* the resulting paired modular boundary current is exactly its cusp current.

Thus noncusp boundary cancellation is proved for the actual infinite series,
not assumed through an abstract automorphic-field interface.

RH chain:

noncusp Green cancellation → cusp-only truncated Stokes current → balanced BM
`++−` source → conserved left-QNM projection → HC94 clock defect → RH.

All statements are unconditional; unit-circle and equal-eigenvalue constraints
are carried by closed structures.
-/

open Complex Real
open scoped BigOperators

namespace RHTower
noncomputable section

theorem d4BM_poincareSeedHorizontalFirstJet_translate
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    d4BMPoincareSeedHorizontalFirstJet (d4BMEisensteinTranslateCoordinate z) s p =
      d4BMPoincareSeedHorizontalFirstJet z s
        (d4BMEisensteinTranslatePrimitivePair p) := by
  unfold d4BMPoincareSeedHorizontalFirstJet d4BMPoincareHorizontalLinear
  rw [d4BM_poincareQuadratic_translate, d4BM_poincareSeed_translate]
  congr 1
  simp [d4BMEisensteinTranslateCoordinate, d4BMEisensteinTranslatePrimitivePair]
  ring

theorem d4BM_poincareSeedVerticalFirstJet_translate
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    d4BMPoincareSeedVerticalFirstJet (d4BMEisensteinTranslateCoordinate z) s p =
      d4BMPoincareSeedVerticalFirstJet z s
        (d4BMEisensteinTranslatePrimitivePair p) := by
  unfold d4BMPoincareSeedVerticalFirstJet
  rw [d4BM_poincareQuadratic_translate, d4BM_poincareSeed_translate]
  simp [d4BMEisensteinTranslateCoordinate, d4BMEisensteinTranslatePrimitivePair]

def d4BMPoincareSeedRadialFirstJet
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) : ℂ :=
  (z.x : ℂ) * d4BMPoincareSeedHorizontalFirstJet z s p +
    (z.y : ℂ) * d4BMPoincareSeedVerticalFirstJet z s p

structure D4BMUnitSemicircleCoordinate where
  point : D4BMUpperHalfPlaneCoordinate
  unit_circle : point.x ^ 2 + point.y ^ 2 = 1

theorem d4BM_poincareSeedRadialFirstJet_invert_unitCircle
    (z : D4BMUnitSemicircleCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    d4BMPoincareSeedRadialFirstJet
        (d4BMEisensteinInvertCoordinate z.point) s p =
      -d4BMPoincareSeedRadialFirstJet z.point s
        (d4BMEisensteinRotatePrimitivePair p) := by
  let c : ℂ := p.pair.1
  let d : ℂ := p.pair.2
  let Q : ℂ := d4BMPoincareQuadratic z.point
    (d4BMEisensteinRotatePrimitivePair p).pair
  have hQ : Q ≠ 0 := by
    dsimp only [Q]
    exact_mod_cast (d4BMPoincareQuadratic_pos z.point
      (d4BMEisensteinRotatePrimitivePair p).pair
      (d4BMEisensteinRotatePrimitivePair p).pair_ne_zero).ne'
  have hQformula : Q =
      (d * (z.point.y : ℂ)) ^ 2 +
        (d * (z.point.x : ℂ) - c) ^ 2 := by
    unfold Q d4BMPoincareQuadratic d4BMEisensteinRotatePrimitivePair c d
    push_cast
    ring
  have hQdenom :
      ((p.pair.2 : ℂ) * (z.point.y : ℂ)) ^ 2 +
        ((p.pair.2 : ℂ) * (z.point.x : ℂ) + -(p.pair.1 : ℂ)) ^ 2 = Q := by
    dsimp only [c, d] at hQformula
    simpa only [sub_eq_add_neg] using hQformula.symm
  have hR : z.point.x ^ 2 + z.point.y ^ 2 ≠ 0 := by
    rw [z.unit_circle]
    norm_num
  have hRC : (z.point.x : ℂ) ^ 2 + (z.point.y : ℂ) ^ 2 = 1 := by
    exact_mod_cast z.unit_circle
  have hy : (z.point.y : ℂ) ≠ 0 := by
    exact_mod_cast z.point.y_pos.ne'
  have hQinv :
      (d4BMPoincareQuadratic (d4BMEisensteinInvertCoordinate z.point) p.pair : ℂ) = Q := by
    have hseedQ := d4BM_poincareSeed_invert z.point (1 : ℂ) p
    unfold d4BMPoincareSeed at hseedQ
    have hquad :
        d4BMPoincareQuadratic (d4BMEisensteinInvertCoordinate z.point) p.pair =
          d4BMPoincareQuadratic z.point
            (d4BMEisensteinRotatePrimitivePair p).pair /
              (z.point.x ^ 2 + z.point.y ^ 2) := by
      unfold d4BMEisensteinInvertCoordinate d4BMPoincareQuadratic
        d4BMEisensteinRotatePrimitivePair
      field_simp [hR]
      push_cast
      ring
    rw [hquad, z.unit_circle]
    simp [Q]
  unfold d4BMPoincareSeedRadialFirstJet d4BMPoincareSeedHorizontalFirstJet
    d4BMPoincareSeedVerticalFirstJet d4BMPoincareHorizontalLinear
  rw [d4BM_poincareSeed_invert]
  rw [hQinv]
  unfold d4BMEisensteinInvertCoordinate d4BMEisensteinRotatePrimitivePair
  dsimp only [c, d, Q]
  push_cast
  rw [hRC]
  norm_num
  unfold d4BMPoincareQuadratic
  push_cast
  simp only [d4BMEisensteinRotatePrimitivePair, Int.cast_neg]
  rw [hQdenom]
  field_simp [hQ, hy]
  rw [← hQdenom]
  let q : D4BMPrimitiveIntegerPair := by
    refine ⟨(p.pair.2, -p.pair.1), ?_⟩
    rw [Int.gcd_neg, Int.gcd_comm]
    exact p.primitive
  linear_combination
    -(2 * s * d4BMPoincareSeed z.point s q * (p.pair.1 : ℂ) ^ 2) * hRC

theorem summable_d4BMPoincareSeedHorizontalFirstJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable fun p : D4BMPrimitiveIntegerPair =>
      d4BMPoincareSeedHorizontalFirstJet z P.s p := by
  let K : ℝ := 2 * ‖P.s‖ / z.y
  have hK : Summable fun p : D4BMPrimitiveIntegerPair =>
      K * ‖d4BMPoincareSeed z P.s p‖ :=
    (summable_d4BMPoincareSeed z P).norm.mul_left K
  refine Summable.of_norm_bounded hK ?_
  intro p
  exact norm_d4BMPoincareSeedHorizontalFirstJet_le z P.s p

theorem summable_d4BMPoincareSeedVerticalFirstJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable fun p : D4BMPrimitiveIntegerPair =>
      d4BMPoincareSeedVerticalFirstJet z P.s p := by
  let K : ℝ := 3 * ‖P.s‖ / z.y
  have hK : Summable fun p : D4BMPrimitiveIntegerPair =>
      K * ‖d4BMPoincareSeed z P.s p‖ :=
    (summable_d4BMPoincareSeed z P).norm.mul_left K
  refine Summable.of_norm_bounded hK ?_
  intro p
  exact norm_d4BMPoincareSeedVerticalFirstJet_le z P.s p

theorem summable_d4BMPoincareSeedRadialFirstJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable fun p : D4BMPrimitiveIntegerPair =>
      d4BMPoincareSeedRadialFirstJet z P.s p := by
  unfold d4BMPoincareSeedRadialFirstJet
  exact ((summable_d4BMPoincareSeedHorizontalFirstJet z P).mul_left (z.x : ℂ)).add
    ((summable_d4BMPoincareSeedVerticalFirstJet z P).mul_left (z.y : ℂ))

def d4BMRawPoincareRadialFirstJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  (1 / 2 : ℂ) * ∑' p : D4BMPrimitiveIntegerPair,
    d4BMPoincareSeedRadialFirstJet z P.s p

def d4BMCompletedPoincareRadialFirstJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  reflectedCompletedLambda (2 * P.s) * d4BMRawPoincareRadialFirstJet z P

theorem d4BM_rawPoincareRadialFirstJet_eq_gradientContraction
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMRawPoincareRadialFirstJet z P =
      (z.x : ℂ) * d4BMRawPoincareHorizontalFirstJet z P +
        (z.y : ℂ) * d4BMRawPoincareVerticalFirstJet z P := by
  have hH := summable_d4BMPoincareSeedHorizontalFirstJet z P
  have hV := summable_d4BMPoincareSeedVerticalFirstJet z P
  unfold d4BMRawPoincareRadialFirstJet d4BMPoincareSeedRadialFirstJet
    d4BMRawPoincareHorizontalFirstJet d4BMRawPoincareVerticalFirstJet
  rw [hH.mul_left (z.x : ℂ) |>.tsum_add (hV.mul_left (z.y : ℂ))]
  rw [tsum_mul_left, tsum_mul_left]
  ring

theorem d4BM_completedPoincareRadialFirstJet_eq_gradientContraction
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedPoincareRadialFirstJet z P =
      (z.x : ℂ) * d4BMCompletedPoincareHorizontalFirstJet z P +
        (z.y : ℂ) * d4BMCompletedPoincareVerticalFirstJet z P := by
  rw [d4BMCompletedPoincareRadialFirstJet,
    d4BM_rawPoincareRadialFirstJet_eq_gradientContraction]
  unfold d4BMCompletedPoincareHorizontalFirstJet
    d4BMCompletedPoincareVerticalFirstJet
  ring

theorem d4BM_completedPoincareHorizontalFirstJet_translate
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedPoincareHorizontalFirstJet
        (d4BMEisensteinTranslateCoordinate z) P =
      d4BMCompletedPoincareHorizontalFirstJet z P := by
  unfold d4BMCompletedPoincareHorizontalFirstJet d4BMRawPoincareHorizontalFirstJet
  rw [show (fun p : D4BMPrimitiveIntegerPair =>
      d4BMPoincareSeedHorizontalFirstJet (d4BMEisensteinTranslateCoordinate z) P.s p) =
      fun p => d4BMPoincareSeedHorizontalFirstJet z P.s
        (d4BMEisensteinTranslatePrimitivePairEquiv p) by
    funext p
    exact d4BM_poincareSeedHorizontalFirstJet_translate z P.s p]
  rw [d4BMEisensteinTranslatePrimitivePairEquiv.tsum_eq]

theorem d4BM_completedPoincareVerticalFirstJet_translate
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedPoincareVerticalFirstJet
        (d4BMEisensteinTranslateCoordinate z) P =
      d4BMCompletedPoincareVerticalFirstJet z P := by
  unfold d4BMCompletedPoincareVerticalFirstJet d4BMRawPoincareVerticalFirstJet
  rw [show (fun p : D4BMPrimitiveIntegerPair =>
      d4BMPoincareSeedVerticalFirstJet (d4BMEisensteinTranslateCoordinate z) P.s p) =
      fun p => d4BMPoincareSeedVerticalFirstJet z P.s
        (d4BMEisensteinTranslatePrimitivePairEquiv p) by
    funext p
    exact d4BM_poincareSeedVerticalFirstJet_translate z P.s p]
  rw [d4BMEisensteinTranslatePrimitivePairEquiv.tsum_eq]

theorem d4BM_completedPoincareRadialFirstJet_invert_unitCircle
    (z : D4BMUnitSemicircleCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedPoincareRadialFirstJet
        (d4BMEisensteinInvertCoordinate z.point) P =
      -d4BMCompletedPoincareRadialFirstJet z.point P := by
  unfold d4BMCompletedPoincareRadialFirstJet d4BMRawPoincareRadialFirstJet
  rw [show (fun p : D4BMPrimitiveIntegerPair =>
      d4BMPoincareSeedRadialFirstJet
        (d4BMEisensteinInvertCoordinate z.point) P.s p) =
      fun p => -d4BMPoincareSeedRadialFirstJet z.point P.s
        (d4BMEisensteinRotatePrimitivePairEquiv p) by
    funext p
    exact d4BM_poincareSeedRadialFirstJet_invert_unitCircle z P.s p]
  rw [show (fun p : D4BMPrimitiveIntegerPair =>
      -d4BMPoincareSeedRadialFirstJet z.point P.s
        (d4BMEisensteinRotatePrimitivePairEquiv p)) =
      fun p => (-1 : ℂ) * d4BMPoincareSeedRadialFirstJet z.point P.s
        (d4BMEisensteinRotatePrimitivePairEquiv p) by
    funext p
    ring]
  rw [tsum_mul_left, d4BMEisensteinRotatePrimitivePairEquiv.tsum_eq]
  ring

def d4BMCompletedPoincareHorizontalGreenCurrent
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  d4BMCompletedEisensteinPoincareSeries z P *
      d4BMCompletedPoincareHorizontalFirstJet z Q -
    d4BMCompletedEisensteinPoincareSeries z Q *
      d4BMCompletedPoincareHorizontalFirstJet z P

def d4BMCompletedPoincareVerticalGreenCurrent
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  d4BMCompletedEisensteinPoincareSeries z P *
      d4BMCompletedPoincareVerticalFirstJet z Q -
    d4BMCompletedEisensteinPoincareSeries z Q *
      d4BMCompletedPoincareVerticalFirstJet z P

def d4BMCompletedPoincareRadialGreenCurrent
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  d4BMCompletedEisensteinPoincareSeries z P *
      d4BMCompletedPoincareRadialFirstJet z Q -
    d4BMCompletedEisensteinPoincareSeries z Q *
      d4BMCompletedPoincareRadialFirstJet z P

theorem d4BM_completedPoincareHorizontalGreenCurrent_translate
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedPoincareHorizontalGreenCurrent
        (d4BMEisensteinTranslateCoordinate z) P Q =
      d4BMCompletedPoincareHorizontalGreenCurrent z P Q := by
  unfold d4BMCompletedPoincareHorizontalGreenCurrent
  rw [d4BM_completedEisensteinPoincareSeries_translate z P,
    d4BM_completedEisensteinPoincareSeries_translate z Q,
    d4BM_completedPoincareHorizontalFirstJet_translate z P,
    d4BM_completedPoincareHorizontalFirstJet_translate z Q]

theorem d4BM_completedPoincareVerticalGreenCurrent_translate
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedPoincareVerticalGreenCurrent
        (d4BMEisensteinTranslateCoordinate z) P Q =
      d4BMCompletedPoincareVerticalGreenCurrent z P Q := by
  unfold d4BMCompletedPoincareVerticalGreenCurrent
  rw [d4BM_completedEisensteinPoincareSeries_translate z P,
    d4BM_completedEisensteinPoincareSeries_translate z Q,
    d4BM_completedPoincareVerticalFirstJet_translate z P,
    d4BM_completedPoincareVerticalFirstJet_translate z Q]

theorem d4BM_completedPoincareRadialGreenCurrent_invert_unitCircle
    (z : D4BMUnitSemicircleCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedPoincareRadialGreenCurrent
        (d4BMEisensteinInvertCoordinate z.point) P Q =
      -d4BMCompletedPoincareRadialGreenCurrent z.point P Q := by
  unfold d4BMCompletedPoincareRadialGreenCurrent
  rw [d4BM_completedEisensteinPoincareSeries_invert z.point P,
    d4BM_completedEisensteinPoincareSeries_invert z.point Q,
    d4BM_completedPoincareRadialFirstJet_invert_unitCircle z P,
    d4BM_completedPoincareRadialFirstJet_invert_unitCircle z Q]
  ring

theorem d4BM_completedPoincare_GreenLagrange_interior_identity
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    (z.y : ℂ) ^ 2 *
        (d4BMCompletedEisensteinPoincareSeries z P *
            (d4BMCompletedPoincareHorizontalSecondJet z Q +
              d4BMCompletedPoincareVerticalSecondJet z Q) -
          d4BMCompletedEisensteinPoincareSeries z Q *
            (d4BMCompletedPoincareHorizontalSecondJet z P +
              d4BMCompletedPoincareVerticalSecondJet z P)) =
      (Q.s * (Q.s - 1) - P.s * (P.s - 1)) *
        d4BMCompletedEisensteinPoincareSeries z P *
          d4BMCompletedEisensteinPoincareSeries z Q := by
  have hP :=
    d4BM_completedEisensteinPoincareSeries_hyperbolicLaplacian_eq_eigenvalue z P
  have hQ :=
    d4BM_completedEisensteinPoincareSeries_hyperbolicLaplacian_eq_eigenvalue z Q
  linear_combination
    d4BMCompletedEisensteinPoincareSeries z P * hQ -
      d4BMCompletedEisensteinPoincareSeries z Q * hP

structure D4BMEqualEigenvaluePoincarePair where
  left : D4BMEisensteinAbsoluteConvergenceParameter
  right : D4BMEisensteinAbsoluteConvergenceParameter
  eigenvalue_eq : left.s * (left.s - 1) = right.s * (right.s - 1)

theorem d4BM_completedPoincare_equalEigenvalue_GreenLagrange_interior_zero
    (z : D4BMUpperHalfPlaneCoordinate)
    (E : D4BMEqualEigenvaluePoincarePair) :
    (z.y : ℂ) ^ 2 *
        (d4BMCompletedEisensteinPoincareSeries z E.left *
            (d4BMCompletedPoincareHorizontalSecondJet z E.right +
              d4BMCompletedPoincareVerticalSecondJet z E.right) -
          d4BMCompletedEisensteinPoincareSeries z E.right *
            (d4BMCompletedPoincareHorizontalSecondJet z E.left +
              d4BMCompletedPoincareVerticalSecondJet z E.left)) = 0 := by
  rw [d4BM_completedPoincare_GreenLagrange_interior_identity]
  rw [← E.eigenvalue_eq]
  ring

structure D4BMTruncatedModularBoundaryPair where
  verticalSide : D4BMUpperHalfPlaneCoordinate
  circularArc : D4BMUnitSemicircleCoordinate
  cuspTop : D4BMUpperHalfPlaneCoordinate

def d4BMCompletedPoincareNonCuspPairedGreenDefect
    (B : D4BMTruncatedModularBoundaryPair)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  (d4BMCompletedPoincareHorizontalGreenCurrent
      (d4BMEisensteinTranslateCoordinate B.verticalSide) P Q -
    d4BMCompletedPoincareHorizontalGreenCurrent B.verticalSide P Q) +
  (d4BMCompletedPoincareRadialGreenCurrent
      (d4BMEisensteinInvertCoordinate B.circularArc.point) P Q +
    d4BMCompletedPoincareRadialGreenCurrent B.circularArc.point P Q)

def d4BMCompletedPoincarePairedBoundaryGreenCurrent
    (B : D4BMTruncatedModularBoundaryPair)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  d4BMCompletedPoincareVerticalGreenCurrent B.cuspTop P Q +
    d4BMCompletedPoincareNonCuspPairedGreenDefect B P Q

theorem d4BM_completedPoincare_nonCuspPairedGreenDefect_eq_zero
    (B : D4BMTruncatedModularBoundaryPair)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedPoincareNonCuspPairedGreenDefect B P Q = 0 := by
  unfold d4BMCompletedPoincareNonCuspPairedGreenDefect
  rw [d4BM_completedPoincareHorizontalGreenCurrent_translate,
    d4BM_completedPoincareRadialGreenCurrent_invert_unitCircle]
  ring

theorem d4BM_completedPoincare_pairedBoundaryGreenCurrent_eq_cuspCurrent
    (B : D4BMTruncatedModularBoundaryPair)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedPoincarePairedBoundaryGreenCurrent B P Q =
      d4BMCompletedPoincareVerticalGreenCurrent B.cuspTop P Q := by
  rw [d4BMCompletedPoincarePairedBoundaryGreenCurrent,
    d4BM_completedPoincare_nonCuspPairedGreenDefect_eq_zero]
  simp

end
end RHTower

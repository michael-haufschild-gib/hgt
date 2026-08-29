import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualZeroFourierCoefficient

/-!
# Modular-generator invariance of the actual completed Eisenstein Poincare series

Corpus research identified the first honest quotient gate after actual Fourier coefficients:
vertical-side and circular-arc cancellation in a truncated modular Green identity require the
literal primitive-pair Poincare function to satisfy the modular generator laws, not an abstract
automorphy premise.

This module constructs exact primitive-pair equivalences for translation and inversion.  The
translation generator reindexes `(c,d)` by `(c,d+c)`; the inversion generator reindexes it by
`(d,-c)`.  Direct denominator algebra proves invariance of both raw and completed series.

Downstream RH chain:

`S/T invariance -> honest modular boundary pairing -> Green/Stokes defects -> polarized BM ++-
 source -> negative BM leg -> conserved left-QNM projection -> HC94 clock defect -> RH`.

All statements are unconditional in the existing absolute-convergence parameter.
-/

open Complex Real
open scoped BigOperators

namespace RHTower
noncomputable section

def d4BMEisensteinTranslateCoordinate
    (z : D4BMUpperHalfPlaneCoordinate) : D4BMUpperHalfPlaneCoordinate where
  x := z.x + 1
  y := z.y
  y_pos := z.y_pos

def d4BMEisensteinInvertCoordinate
    (z : D4BMUpperHalfPlaneCoordinate) : D4BMUpperHalfPlaneCoordinate where
  x := -z.x / (z.x ^ 2 + z.y ^ 2)
  y := z.y / (z.x ^ 2 + z.y ^ 2)
  y_pos := by
    apply div_pos z.y_pos
    nlinarith [sq_nonneg z.x, sq_pos_of_pos z.y_pos]

def d4BMEisensteinTranslatePrimitivePair
    (p : D4BMPrimitiveIntegerPair) : D4BMPrimitiveIntegerPair where
  pair := (p.pair.1, p.pair.2 + p.pair.1)
  primitive := by simpa using p.primitive

def d4BMEisensteinTranslatePrimitivePairInv
    (p : D4BMPrimitiveIntegerPair) : D4BMPrimitiveIntegerPair where
  pair := (p.pair.1, p.pair.2 - p.pair.1)
  primitive := by simpa using p.primitive

def d4BMEisensteinTranslatePrimitivePairEquiv :
    D4BMPrimitiveIntegerPair ≃ D4BMPrimitiveIntegerPair where
  toFun := d4BMEisensteinTranslatePrimitivePair
  invFun := d4BMEisensteinTranslatePrimitivePairInv
  left_inv p := by
    apply d4BMPrimitiveIntegerPair_ext
    simp [d4BMEisensteinTranslatePrimitivePair,
      d4BMEisensteinTranslatePrimitivePairInv]
  right_inv p := by
    apply d4BMPrimitiveIntegerPair_ext
    simp [d4BMEisensteinTranslatePrimitivePair,
      d4BMEisensteinTranslatePrimitivePairInv]

def d4BMEisensteinRotatePrimitivePair
    (p : D4BMPrimitiveIntegerPair) : D4BMPrimitiveIntegerPair where
  pair := (p.pair.2, -p.pair.1)
  primitive := by
    rw [Int.gcd_neg, Int.gcd_comm]
    exact p.primitive

def d4BMEisensteinRotatePrimitivePairInv
    (p : D4BMPrimitiveIntegerPair) : D4BMPrimitiveIntegerPair where
  pair := (-p.pair.2, p.pair.1)
  primitive := by
    rw [Int.gcd_comm, Int.gcd_neg]
    exact p.primitive

def d4BMEisensteinRotatePrimitivePairEquiv :
    D4BMPrimitiveIntegerPair ≃ D4BMPrimitiveIntegerPair where
  toFun := d4BMEisensteinRotatePrimitivePair
  invFun := d4BMEisensteinRotatePrimitivePairInv
  left_inv p := by
    apply d4BMPrimitiveIntegerPair_ext
    simp [d4BMEisensteinRotatePrimitivePair,
      d4BMEisensteinRotatePrimitivePairInv]
  right_inv p := by
    apply d4BMPrimitiveIntegerPair_ext
    simp [d4BMEisensteinRotatePrimitivePair,
      d4BMEisensteinRotatePrimitivePairInv]

theorem d4BM_poincareQuadratic_translate
    (z : D4BMUpperHalfPlaneCoordinate) (p : D4BMPrimitiveIntegerPair) :
    d4BMPoincareQuadratic (d4BMEisensteinTranslateCoordinate z) p.pair =
      d4BMPoincareQuadratic z
        (d4BMEisensteinTranslatePrimitivePair p).pair := by
  simp [d4BMPoincareQuadratic, d4BMEisensteinTranslateCoordinate,
    d4BMEisensteinTranslatePrimitivePair]
  ring

theorem d4BM_poincareSeed_translate
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    d4BMPoincareSeed (d4BMEisensteinTranslateCoordinate z) s p =
      d4BMPoincareSeed z s (d4BMEisensteinTranslatePrimitivePair p) := by
  unfold d4BMPoincareSeed
  rw [d4BM_poincareQuadratic_translate]
  rfl

theorem d4BM_poincareSeed_invert
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    d4BMPoincareSeed (d4BMEisensteinInvertCoordinate z) s p =
      d4BMPoincareSeed z s (d4BMEisensteinRotatePrimitivePair p) := by
  unfold d4BMPoincareSeed
  have hratio :
      (d4BMEisensteinInvertCoordinate z).y /
          d4BMPoincareQuadratic (d4BMEisensteinInvertCoordinate z) p.pair =
        z.y / d4BMPoincareQuadratic z
          (d4BMEisensteinRotatePrimitivePair p).pair := by
    have hR : z.x ^ 2 + z.y ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg z.x, sq_pos_of_pos z.y_pos]
    have hquad :
        d4BMPoincareQuadratic (d4BMEisensteinInvertCoordinate z) p.pair =
          d4BMPoincareQuadratic z
            (d4BMEisensteinRotatePrimitivePair p).pair /
              (z.x ^ 2 + z.y ^ 2) := by
      unfold d4BMEisensteinInvertCoordinate d4BMPoincareQuadratic
        d4BMEisensteinRotatePrimitivePair
      field_simp [hR]
      push_cast
      ring
    have hQ : d4BMPoincareQuadratic z
        (d4BMEisensteinRotatePrimitivePair p).pair ≠ 0 := by
      exact ne_of_gt (d4BMPoincareQuadratic_pos z
        (d4BMEisensteinRotatePrimitivePair p).pair
        (d4BMEisensteinRotatePrimitivePair p).pair_ne_zero)
    rw [hquad]
    dsimp [d4BMEisensteinInvertCoordinate]
    field_simp [hR, hQ]
  rw [hratio]

theorem d4BM_rawEisensteinPoincareSeries_translate
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMRawEisensteinPoincareSeries (d4BMEisensteinTranslateCoordinate z) P =
      d4BMRawEisensteinPoincareSeries z P := by
  unfold d4BMRawEisensteinPoincareSeries
  rw [show (fun p : D4BMPrimitiveIntegerPair =>
      d4BMPoincareSeed (d4BMEisensteinTranslateCoordinate z) P.s p) =
      fun p => d4BMPoincareSeed z P.s
        (d4BMEisensteinTranslatePrimitivePairEquiv p) by
    funext p
    exact d4BM_poincareSeed_translate z P.s p]
  rw [d4BMEisensteinTranslatePrimitivePairEquiv.tsum_eq]

theorem d4BM_rawEisensteinPoincareSeries_invert
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMRawEisensteinPoincareSeries (d4BMEisensteinInvertCoordinate z) P =
      d4BMRawEisensteinPoincareSeries z P := by
  unfold d4BMRawEisensteinPoincareSeries
  rw [show (fun p : D4BMPrimitiveIntegerPair =>
      d4BMPoincareSeed (d4BMEisensteinInvertCoordinate z) P.s p) =
      fun p => d4BMPoincareSeed z P.s
        (d4BMEisensteinRotatePrimitivePairEquiv p) by
    funext p
    exact d4BM_poincareSeed_invert z P.s p]
  rw [d4BMEisensteinRotatePrimitivePairEquiv.tsum_eq]

theorem d4BM_completedEisensteinPoincareSeries_translate
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedEisensteinPoincareSeries (d4BMEisensteinTranslateCoordinate z) P =
      d4BMCompletedEisensteinPoincareSeries z P := by
  unfold d4BMCompletedEisensteinPoincareSeries
  rw [d4BM_rawEisensteinPoincareSeries_translate]

theorem d4BM_completedEisensteinPoincareSeries_invert
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedEisensteinPoincareSeries (d4BMEisensteinInvertCoordinate z) P =
      d4BMCompletedEisensteinPoincareSeries z P := by
  unfold d4BMCompletedEisensteinPoincareSeries
  rw [d4BM_rawEisensteinPoincareSeries_invert]

end
end RHTower

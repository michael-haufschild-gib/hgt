import GaloisForLFunctions.RHTower.ThetaCuspReflectedEighthPolynomial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sparse singular envelope for rank-three D1

Pure algebraic core of the theta rank-three singular-envelope reduction.  It is intentionally
independent of the analytic theta jet stack so conjecture/proof iterations elaborate quickly.
-/

namespace RHTower

noncomputable section

/-- Strict rank-two invariant in native positive logarithmic coordinates. -/
def thetaCuspRankThreeLowerGap (A B : ℝ) : ℝ :=
  4 * A ^ 2 - B

/-- Rank-three order-six invariant in native positive logarithmic coordinates. -/
def thetaCuspRankThreeSixthMargin (A B C : ℝ) : ℝ :=
  A * C - B ^ 2 - 18 * A ^ 2 * B + 24 * A ^ 4

/-- Eighth-jet-free side of the singular rank-three envelope. -/
def thetaCuspRankThreeSingularEighthEnvelope (A L T : ℝ) : ℝ :=
  52 * A ^ 2 * L * T - 2 * T * L ^ 2 - T ^ 2 +
    2176 * A ^ 6 * L - 1188 * A ^ 4 * L ^ 2 +
      120 * A ^ 2 * L ^ 3 - L ^ 4

/-- Directional derivative of the native rank-three reflected polynomial. -/
def thetaCuspReflectedEighthPolynomialVariation
    (A B C D a b c d : ℝ) : ℝ :=
  a * (4608 * A ^ 5 - 5376 * A ^ 3 * B + 608 * A * B ^ 2 +
      384 * A ^ 2 * C - 8 * A * D) +
    b * (-1344 * A ^ 4 + 608 * A ^ 2 * B - 204 * B ^ 2 + D) +
    c * (128 * A ^ 3 - 2 * C) +
    d * (B - 4 * A ^ 2)

/-- Directional derivative of the strict rank-two invariant. -/
def thetaCuspRankThreeLowerGapVariation (A a b : ℝ) : ℝ :=
  8 * A * a - b

/-- Directional derivative of the order-six invariant. -/
def thetaCuspRankThreeSixthMarginVariation
    (A B C a b c : ℝ) : ℝ :=
  a * C + A * c - 2 * B * b - 36 * A * a * B -
    18 * A ^ 2 * b + 96 * A ^ 3 * a

/-- Division-free normal velocity of the singular envelope.  It is linear in the four adapted
velocity channels and contains no eighth-jet value. -/
def thetaCuspRankThreeSingularNormalVelocity
    (A L T a l t d : ℝ) : ℝ :=
  2 * a * L *
      (4352 * A ^ 6 * L - 1188 * A ^ 4 * L ^ 2 +
        2 * T * L ^ 2 + T ^ 2 + L ^ 4) +
    A * l *
      (T ^ 2 - 2 * T * L ^ 2 - 1188 * A ^ 4 * L ^ 2 +
        240 * A ^ 2 * L ^ 3 - 3 * L ^ 4) +
    2 * A * L * t * (26 * A ^ 2 * L - L ^ 2 - T) -
    A ^ 3 * L ^ 2 * d

private def thetaCuspRankThreeCompressedCore (X B K : ℝ) : ℝ :=
  768 * X ^ 4 - 1344 * X ^ 3 * B + 304 * X ^ 2 * B ^ 2 -
    68 * X * B ^ 3 + 128 * X ^ 2 * K - K ^ 2

private theorem thetaCuspRankThreeCompressedCore_substitution (X L T : ℝ) :
    thetaCuspRankThreeCompressedCore X (4 * X - L)
        (T + 64 * X ^ 2 - 26 * X * L + L ^ 2) =
      52 * X * L * T - 2 * T * L ^ 2 - T ^ 2 +
        2176 * X ^ 3 * L - 1188 * X ^ 2 * L ^ 2 +
          120 * X * L ^ 3 - L ^ 4 := by
  unfold thetaCuspRankThreeCompressedCore
  ring

/-- Sparse lower-invariant presentation of the native rank-three D1 polynomial. -/
theorem thetaCuspReflectedEighthPolynomial_sparse (A B C D : ℝ) :
    A ^ 2 * thetaCuspReflectedEighthPolynomial A B C D =
      -A ^ 2 * thetaCuspRankThreeLowerGap A B * D +
        thetaCuspRankThreeSingularEighthEnvelope A
          (thetaCuspRankThreeLowerGap A B)
          (thetaCuspRankThreeSixthMargin A B C) := by
  let X := A ^ 2
  let L := thetaCuspRankThreeLowerGap A B
  let T := thetaCuspRankThreeSixthMargin A B C
  have hscaled :
      A ^ 2 * thetaCuspReflectedEighthPolynomial A B C D =
        -A ^ 2 * L * D + thetaCuspRankThreeCompressedCore X B (A * C) := by
    dsimp only [X, L]
    unfold thetaCuspReflectedEighthPolynomial thetaCuspRankThreeLowerGap
      thetaCuspRankThreeCompressedCore
    ring
  have hB : B = 4 * X - L := by
    dsimp only [X, L, thetaCuspRankThreeLowerGap]
    ring
  have hK : A * C = T + 64 * X ^ 2 - 26 * X * L + L ^ 2 := by
    dsimp only [X, L, T, thetaCuspRankThreeLowerGap,
      thetaCuspRankThreeSixthMargin]
    ring
  calc
    A ^ 2 * thetaCuspReflectedEighthPolynomial A B C D =
        -A ^ 2 * L * D + thetaCuspRankThreeCompressedCore X B (A * C) := hscaled
    _ = -A ^ 2 * L * D +
        thetaCuspRankThreeCompressedCore X (4 * X - L)
          (T + 64 * X ^ 2 - 26 * X * L + L ^ 2) := by rw [hB, hK]
    _ = -A ^ 2 * L * D +
        (52 * X * L * T - 2 * T * L ^ 2 - T ^ 2 +
          2176 * X ^ 3 * L - 1188 * X ^ 2 * L ^ 2 +
            120 * X * L ^ 3 - L ^ 4) := by
      rw [thetaCuspRankThreeCompressedCore_substitution]
    _ = _ := by
      dsimp only [X, L, T]
      unfold thetaCuspRankThreeSingularEighthEnvelope
      ring

/-- Exact off-shell normal-flow identity.  The sole correction away from the singular sheet is
the lower-gap velocity times `D1`; consequently it vanishes at first contact. -/
theorem thetaCuspReflectedEighthPolynomial_normalVelocity
    (A B C D a b c d : ℝ) :
    let L := thetaCuspRankThreeLowerGap A B
    let T := thetaCuspRankThreeSixthMargin A B C
    let l := thetaCuspRankThreeLowerGapVariation A a b
    let t := thetaCuspRankThreeSixthMarginVariation A B C a b c
    A ^ 3 * L * thetaCuspReflectedEighthPolynomialVariation A B C D a b c d =
      thetaCuspRankThreeSingularNormalVelocity A L T a l t d +
        A ^ 3 * l * thetaCuspReflectedEighthPolynomial A B C D := by
  dsimp only
  unfold thetaCuspRankThreeLowerGap thetaCuspRankThreeSixthMargin
    thetaCuspRankThreeLowerGapVariation thetaCuspRankThreeSixthMarginVariation
    thetaCuspReflectedEighthPolynomialVariation
    thetaCuspRankThreeSingularNormalVelocity thetaCuspReflectedEighthPolynomial
  ring

/-- On a singular `D1` face, the four-channel normal velocity is exactly the scaled determinant
variation. -/
theorem thetaCuspReflectedEighthPolynomial_normalVelocity_of_zero
    {A B C D a b c d : ℝ}
    (hzero : thetaCuspReflectedEighthPolynomial A B C D = 0) :
    let L := thetaCuspRankThreeLowerGap A B
    let T := thetaCuspRankThreeSixthMargin A B C
    let l := thetaCuspRankThreeLowerGapVariation A a b
    let t := thetaCuspRankThreeSixthMarginVariation A B C a b c
    A ^ 3 * L * thetaCuspReflectedEighthPolynomialVariation A B C D a b c d =
      thetaCuspRankThreeSingularNormalVelocity A L T a l t d := by
  dsimp only
  rw [thetaCuspReflectedEighthPolynomial_normalVelocity]
  rw [hzero, mul_zero, add_zero]

/-- For nonzero curvature, D1 singularity is exactly the sparse eighth-envelope equality. -/
theorem thetaCuspReflectedEighthPolynomial_eq_zero_iff_singularEnvelope
    {A B C D : ℝ} (hA : A ≠ 0) :
    thetaCuspReflectedEighthPolynomial A B C D = 0 ↔
      A ^ 2 * thetaCuspRankThreeLowerGap A B * D =
        thetaCuspRankThreeSingularEighthEnvelope A
          (thetaCuspRankThreeLowerGap A B)
          (thetaCuspRankThreeSixthMargin A B C) := by
  have hsparse := thetaCuspReflectedEighthPolynomial_sparse A B C D
  constructor
  · intro h
    rw [h] at hsparse
    nlinarith
  · intro h
    have hz : A ^ 2 * thetaCuspReflectedEighthPolynomial A B C D = 0 := by
      rw [hsparse]
      nlinarith
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 hA)

end

end RHTower

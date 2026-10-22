import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspReflectedEighthPolynomial
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
  4 * A ^ (2 : ℕ) - B

/-- Rank-three order-six invariant in native positive logarithmic coordinates. -/
def thetaCuspRankThreeSixthMargin (A B C : ℝ) : ℝ :=
  A * C - B ^ (2 : ℕ) - 18 * A ^ (2 : ℕ) * B + 24 * A ^ (4 : ℕ)

/-- Eighth-jet-free side of the singular rank-three envelope. -/
def thetaCuspRankThreeSingularEighthEnvelope (A L T : ℝ) : ℝ :=
  52 * A ^ (2 : ℕ) * L * T - 2 * T * L ^ (2 : ℕ) - T ^ (2 : ℕ) +
    2176 * A ^ (6 : ℕ) * L - 1188 * A ^ (4 : ℕ) * L ^ (2 : ℕ) +
      120 * A ^ (2 : ℕ) * L ^ (3 : ℕ) - L ^ (4 : ℕ)

/-- Directional derivative of the native rank-three reflected polynomial. -/
def thetaCuspReflectedEighthPolynomialVariation
    (A B C D a b c d : ℝ) : ℝ :=
  a * (4608 * A ^ (5 : ℕ) - 5376 * A ^ (3 : ℕ) * B + 608 * A * B ^ (2 : ℕ) +
      384 * A ^ (2 : ℕ) * C - 8 * A * D) +
    b * (-1344 * A ^ (4 : ℕ) + 608 * A ^ (2 : ℕ) * B - 204 * B ^ (2 : ℕ) + D) +
    c * (128 * A ^ (3 : ℕ) - 2 * C) +
    d * (B - 4 * A ^ (2 : ℕ))

/-- Directional derivative of the strict rank-two invariant. -/
def thetaCuspRankThreeLowerGapVariation (A a b : ℝ) : ℝ :=
  8 * A * a - b

/-- Directional derivative of the order-six invariant. -/
def thetaCuspRankThreeSixthMarginVariation
    (A B C a b c : ℝ) : ℝ :=
  a * C + A * c - 2 * B * b - 36 * A * a * B -
    18 * A ^ (2 : ℕ) * b + 96 * A ^ (3 : ℕ) * a

/-- Division-free normal velocity of the singular envelope.  It is linear in the four adapted
velocity channels and contains no eighth-jet value. -/
def thetaCuspRankThreeSingularNormalVelocity
    (A L T a l t d : ℝ) : ℝ :=
  2 * a * L *
      (4352 * A ^ (6 : ℕ) * L - 1188 * A ^ (4 : ℕ) * L ^ (2 : ℕ) +
        2 * T * L ^ (2 : ℕ) + T ^ (2 : ℕ) + L ^ (4 : ℕ)) +
    A * l *
      (T ^ (2 : ℕ) - 2 * T * L ^ (2 : ℕ) - 1188 * A ^ (4 : ℕ) * L ^ (2 : ℕ) +
        240 * A ^ (2 : ℕ) * L ^ (3 : ℕ) - 3 * L ^ (4 : ℕ)) +
    2 * A * L * t * (26 * A ^ (2 : ℕ) * L - L ^ (2 : ℕ) - T) -
    A ^ (3 : ℕ) * L ^ (2 : ℕ) * d

private def thetaCuspRankThreeCompressedCore (X B K : ℝ) : ℝ :=
  768 * X ^ (4 : ℕ) - 1344 * X ^ (3 : ℕ) * B + 304 * X ^ (2 : ℕ) * B ^ (2 : ℕ) -
    68 * X * B ^ (3 : ℕ) + 128 * X ^ (2 : ℕ) * K - K ^ (2 : ℕ)

private theorem thetaCuspRankThreeCompressedCore_substitution (X L T : ℝ) :
    thetaCuspRankThreeCompressedCore X (4 * X - L)
        (T + 64 * X ^ (2 : ℕ) - 26 * X * L + L ^ (2 : ℕ)) =
      52 * X * L * T - 2 * T * L ^ (2 : ℕ) - T ^ (2 : ℕ) +
        2176 * X ^ (3 : ℕ) * L - 1188 * X ^ (2 : ℕ) * L ^ (2 : ℕ) +
          120 * X * L ^ (3 : ℕ) - L ^ (4 : ℕ) := by
  unfold thetaCuspRankThreeCompressedCore
  ring

/-- Sparse lower-invariant presentation of the native rank-three D1 polynomial. -/
theorem thetaCuspReflectedEighthPolynomial_sparse (A B C D : ℝ) :
    A ^ (2 : ℕ) * thetaCuspReflectedEighthPolynomial A B C D =
      -A ^ (2 : ℕ) * thetaCuspRankThreeLowerGap A B * D +
        thetaCuspRankThreeSingularEighthEnvelope A
          (thetaCuspRankThreeLowerGap A B)
          (thetaCuspRankThreeSixthMargin A B C) := by
  let X := A ^ (2 : ℕ)
  let L := thetaCuspRankThreeLowerGap A B
  let T := thetaCuspRankThreeSixthMargin A B C
  have hscaled :
      A ^ (2 : ℕ) * thetaCuspReflectedEighthPolynomial A B C D =
        -A ^ (2 : ℕ) * L * D + thetaCuspRankThreeCompressedCore X B (A * C) := by
    dsimp only [X, L]
    unfold thetaCuspReflectedEighthPolynomial thetaCuspRankThreeLowerGap
      thetaCuspRankThreeCompressedCore
    ring
  have hB : B = 4 * X - L := by
    dsimp only [X, L, thetaCuspRankThreeLowerGap]
    ring
  have hK : A * C = T + 64 * X ^ (2 : ℕ) - 26 * X * L + L ^ (2 : ℕ) := by
    dsimp only [X, L, T, thetaCuspRankThreeLowerGap,
      thetaCuspRankThreeSixthMargin]
    ring
  calc
    A ^ (2 : ℕ) * thetaCuspReflectedEighthPolynomial A B C D =
        -A ^ (2 : ℕ) * L * D + thetaCuspRankThreeCompressedCore X B (A * C) := hscaled
    _ = -A ^ (2 : ℕ) * L * D +
        thetaCuspRankThreeCompressedCore X (4 * X - L)
          (T + 64 * X ^ (2 : ℕ) - 26 * X * L + L ^ (2 : ℕ)) := by rw [hB, hK]
    _ = -A ^ (2 : ℕ) * L * D +
        (52 * X * L * T - 2 * T * L ^ (2 : ℕ) - T ^ (2 : ℕ) +
          2176 * X ^ (3 : ℕ) * L - 1188 * X ^ (2 : ℕ) * L ^ (2 : ℕ) +
            120 * X * L ^ (3 : ℕ) - L ^ (4 : ℕ)) := by
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
    A ^ (3 : ℕ) * L * thetaCuspReflectedEighthPolynomialVariation A B C D a b c d =
      thetaCuspRankThreeSingularNormalVelocity A L T a l t d +
        A ^ (3 : ℕ) * l * thetaCuspReflectedEighthPolynomial A B C D := by
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
    A ^ (3 : ℕ) * L * thetaCuspReflectedEighthPolynomialVariation A B C D a b c d =
      thetaCuspRankThreeSingularNormalVelocity A L T a l t d := by
  dsimp only
  rw [thetaCuspReflectedEighthPolynomial_normalVelocity]
  rw [hzero, mul_zero, add_zero]

/-- For nonzero curvature, D1 singularity is exactly the sparse eighth-envelope equality. -/
theorem thetaCuspReflectedEighthPolynomial_eq_zero_iff_singularEnvelope
    {A B C D : ℝ} (hA : A ≠ 0) :
    thetaCuspReflectedEighthPolynomial A B C D = 0 ↔
      A ^ (2 : ℕ) * thetaCuspRankThreeLowerGap A B * D =
        thetaCuspRankThreeSingularEighthEnvelope A
          (thetaCuspRankThreeLowerGap A B)
          (thetaCuspRankThreeSixthMargin A B C) := by
  have hsparse := thetaCuspReflectedEighthPolynomial_sparse A B C D
  constructor
  · intro h
    rw [h] at hsparse
    nlinarith
  · intro h
    have hz : A ^ (2 : ℕ) * thetaCuspReflectedEighthPolynomial A B C D = 0 := by
      rw [hsparse]
      nlinarith
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 hA)

end

end RHTower

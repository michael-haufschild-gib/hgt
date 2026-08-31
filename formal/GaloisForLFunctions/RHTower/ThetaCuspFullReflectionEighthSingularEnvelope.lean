import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthLowerJetBaseline

/-!
# Sparse singular envelope for theta rank-three D1

The native eighth reflected determinant admits a sparse presentation in the lower rank-two and
rank-three invariants.  On a singular face this eliminates the eighth logarithmic jet exactly.
The identity is staged through a six-term core, avoiding recursive expansion of source jets.

RH chain: singular-envelope elimination -> theta ninth-jet crossing orientation -> no first D1
zero -> global rank-three TCD gate -> all-order/cofinal Hankel landing -> Weil positivity -> RH.
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

/-- Complete theta reflected curvature is uniformly nonzero on the closed positive half-line. -/
theorem thetaCuspFullReflectedLogCurvature_pos_of_nonneg
    {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspFullReflectedLogCurvature x := by
  have hA0 := nineteen_le_thetaCuspBornWittenLogCurvature
    (n := 1) (by norm_num) hx
  have he2 := thetaCuspLikelihoodSourceLogPartitionJetTwo_le_thirteen_tenths hx
  unfold thetaCuspFullReflectedLogCurvature
  nlinarith

/-- At every physical singular face, the eighth logarithmic jet is eliminated exactly by the
lower rank-two and rank-three invariants. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_eq_zero_iff_singularEnvelope
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspFullReflectionEighthHankelCurvature x = 0 ↔
      let A := thetaCuspFullReflectedLogCurvature x
      let B := thetaCuspFullReflectedLogFourthJet x
      let C := thetaCuspFullReflectedLogSixthJet x
      let D := thetaCuspFullReflectedLogEighthJet x
      A ^ 2 * thetaCuspRankThreeLowerGap A B * D =
        thetaCuspRankThreeSingularEighthEnvelope A
          (thetaCuspRankThreeLowerGap A B)
          (thetaCuspRankThreeSixthMargin A B C) := by
  dsimp only
  unfold thetaCuspFullReflectionEighthHankelCurvature
  exact thetaCuspReflectedEighthPolynomial_eq_zero_iff_singularEnvelope
    (thetaCuspFullReflectedLogCurvature_pos_of_nonneg hx).ne'

end

end RHTower

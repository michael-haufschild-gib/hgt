import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthLowerJetBaseline

/-!
# Sharp nonlinear compact reserve for eighth reflected curvature

Independent linear comparison of the fourth, sixth, and eighth likelihood scores loses the
dominant atom in the compact first-atom chamber.  The exact reflected polynomial contains
additional favorable quadratic and cubic fourth-jet terms.  This module retains those terms
and proves that one explicit scalar reserve is an unconditional lower bound for native
rank-three reflected curvature.
-/

namespace RHTower

noncomputable section

/-- Worst-curvature linear coefficient of the fourth likelihood displacement. -/
def thetaCuspFullReflectionEighthCompactFourthCoefficient (q : ℝ) : ℝ :=
  let W := thetaCuspFirstAtomCurvatureProfile q - 13 / 10
  let B0 := thetaCuspFirstAtomFourthProfile q
  let D0 := thetaCuspFirstAtomEighthProfile q
  1344 * W ^ 4 - 608 * W ^ 2 * B0 + 204 * B0 ^ 2 - D0

/-- Born-curvature upper coefficient of the sixth likelihood loss. -/
def thetaCuspFullReflectionEighthCompactSixthCoefficient (q : ℝ) : ℝ :=
  let A0 := thetaCuspFirstAtomCurvatureProfile q
  let C0 := thetaCuspFirstAtomSixthProfile q
  128 * A0 ^ 3 - 2 * C0

/-- Worst-curvature coefficient of the eighth likelihood gain before the fourth displacement. -/
def thetaCuspFullReflectionEighthCompactEighthCoefficient (q : ℝ) : ℝ :=
  let W := thetaCuspFirstAtomCurvatureProfile q - 13 / 10
  let B0 := thetaCuspFirstAtomFourthProfile q
  4 * W ^ 2 - B0

/-- Explicit nonlinear reserve in the compact first-atom chamber. -/
def thetaCuspFullReflectionEighthCompactReserve (x : ℝ) : ℝ :=
  let q := thetaCuspBornWittenWeight 1 x
  let e4 := thetaCuspLikelihoodSourceLogPartitionJetFour x
  let e6 := thetaCuspLikelihoodSourceLogPartitionJetSix x
  let e8 := thetaCuspLikelihoodSourceLogPartitionJetEight x
  thetaCuspFirstAtomEighthNoSixthLossBaseline q +
    e4 * (68 * e4 ^ 2 +
      (304 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ 2 -
        204 * thetaCuspFirstAtomFourthProfile q) * e4 +
      thetaCuspFullReflectionEighthCompactFourthCoefficient q) +
    (thetaCuspFullReflectionEighthCompactEighthCoefficient q + e4) * e8 -
    e6 * (thetaCuspFullReflectionEighthCompactSixthCoefficient q + e6)

/-- Abstract sharp reserve inequality.  Curvature monotonicity is used only on the Born
baseline; all three likelihood displacements are then kept to their exact polynomial orders. -/
theorem thetaCuspReflectedEighthPolynomial_compactReserve_le
    {W A A0 B0 C0 D0 e4 e6 e8 : ℝ}
    (hWpos : 0 < W) (hWA : W ≤ A) (hAA0 : A ≤ A0)
    (hB0 : B0 < (7 / 5 : ℝ) * W ^ 2) (hC0 : 0 < C0)
    (hG : 0 < 576 * W ^ 4 - 672 * W ^ 2 * B0 + 76 * B0 ^ 2 +
      48 * W * C0 - D0)
    (he4 : 0 ≤ e4) (he6 : 0 ≤ e6) (he8 : 0 ≤ e8) :
    thetaCuspReflectedEighthPolynomial W B0 C0 D0 +
        e4 * (68 * e4 ^ 2 + (304 * W ^ 2 - 204 * B0) * e4 +
          (1344 * W ^ 4 - 608 * W ^ 2 * B0 + 204 * B0 ^ 2 - D0)) +
        (4 * W ^ 2 - B0 + e4) * e8 -
        e6 * ((128 * A0 ^ 3 - 2 * C0) + e6) ≤
      thetaCuspReflectedEighthPolynomial A (B0 - e4) (C0 - e6) (D0 - e8) := by
  have hbase : thetaCuspReflectedEighthPolynomial W B0 C0 D0 ≤
      thetaCuspReflectedEighthPolynomial A B0 C0 D0 :=
    thetaCuspReflectedEighthPolynomial_mono_curvature hWpos hWA hB0 hC0 hG
  have hAsq : W ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hWpos.le hWA 2
  have hAcube : A ^ 3 ≤ A0 ^ 3 := by
    have hApos : 0 < A := hWpos.trans_le hWA
    exact pow_le_pow_left₀ hApos.le hAA0 3
  have hfourCoeff :
      1344 * W ^ 4 - 608 * W ^ 2 * B0 + 204 * B0 ^ 2 - D0 ≤
        1344 * A ^ 4 - 608 * A ^ 2 * B0 + 204 * B0 ^ 2 - D0 := by
    have hcore : 0 < 1344 * (A ^ 2 + W ^ 2) - 608 * B0 := by
      nlinarith
    have hfactor : 0 ≤
        (A - W) * (A + W) * (1344 * (A ^ 2 + W ^ 2) - 608 * B0) := by
      exact mul_nonneg
        (mul_nonneg (sub_nonneg.mpr hWA)
          (add_nonneg (hWpos.le.trans hWA) hWpos.le)) hcore.le
    have hid :
        (1344 * A ^ 4 - 608 * A ^ 2 * B0 + 204 * B0 ^ 2 - D0) -
          (1344 * W ^ 4 - 608 * W ^ 2 * B0 + 204 * B0 ^ 2 - D0) =
        (A - W) * (A + W) * (1344 * (A ^ 2 + W ^ 2) - 608 * B0) := by
      ring
    nlinarith
  have hfourLinear : 304 * W ^ 2 - 204 * B0 ≤ 304 * A ^ 2 - 204 * B0 := by
    nlinarith
  have heightCoeff : 4 * W ^ 2 - B0 + e4 ≤ 4 * A ^ 2 - B0 + e4 := by
    nlinarith
  have hsixCoeff : 128 * A ^ 3 - 2 * C0 ≤ 128 * A0 ^ 3 - 2 * C0 := by
    nlinarith
  have hfourGain :
      e4 * (68 * e4 ^ 2 + (304 * W ^ 2 - 204 * B0) * e4 +
        (1344 * W ^ 4 - 608 * W ^ 2 * B0 + 204 * B0 ^ 2 - D0)) ≤
      e4 * (68 * e4 ^ 2 + (304 * A ^ 2 - 204 * B0) * e4 +
        (1344 * A ^ 4 - 608 * A ^ 2 * B0 + 204 * B0 ^ 2 - D0)) := by
    gcongr
  have heightGain : (4 * W ^ 2 - B0 + e4) * e8 ≤
      (4 * A ^ 2 - B0 + e4) * e8 := by
    gcongr
  have hsixLoss :
      -(e6 * ((128 * A0 ^ 3 - 2 * C0) + e6)) ≤
        -(e6 * ((128 * A ^ 3 - 2 * C0) + e6)) := by
    nlinarith [mul_nonneg he6 (sub_nonneg.mpr hsixCoeff)]
  have hexact :
      thetaCuspReflectedEighthPolynomial A (B0 - e4) (C0 - e6) (D0 - e8) =
        thetaCuspReflectedEighthPolynomial A B0 C0 D0 +
          e4 * (68 * e4 ^ 2 + (304 * A ^ 2 - 204 * B0) * e4 +
            (1344 * A ^ 4 - 608 * A ^ 2 * B0 + 204 * B0 ^ 2 - D0)) +
          (4 * A ^ 2 - B0 + e4) * e8 -
          e6 * ((128 * A ^ 3 - 2 * C0) + e6) := by
    unfold thetaCuspReflectedEighthPolynomial
    ring
  rw [hexact]
  linarith

/-- Actual native D1 dominates the explicit nonlinear compact reserve on the full source
half-line. -/
theorem thetaCuspFullReflectionEighthCompactReserve_le_hankelCurvature
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspFullReflectionEighthCompactReserve x ≤
      thetaCuspFullReflectionEighthHankelCurvature x := by
  let q := thetaCuspBornWittenWeight 1 x
  let A0 := thetaCuspBornWittenLogCurvature 1 x
  let B0 := thetaCuspBornWittenLogFourthDerivative 1 x
  let C0 := thetaCuspBornWittenLogSixthDerivative 1 x
  let D0 := thetaCuspBornWittenLogEighthDerivative 1 x
  let e2 := thetaCuspLikelihoodSourceLogPartitionJetTwo x
  let e4 := thetaCuspLikelihoodSourceLogPartitionJetFour x
  let e6 := thetaCuspLikelihoodSourceLogPartitionJetSix x
  let e8 := thetaCuspLikelihoodSourceLogPartitionJetEight x
  let A := A0 - e2
  let W := A0 - 13 / 10
  have hq : (41 / 25 : ℝ) ≤ q := by
    have hpi := Real.pi_gt_d2
    norm_num at hpi
    have he : 1 ≤ Real.exp x := Real.one_le_exp hx
    have he2 : 1 ≤ Real.exp x ^ 2 := by nlinarith [Real.exp_pos x]
    have hscale : Real.pi ≤ thetaCuspMorseScale 1 x := by
      rw [thetaCuspMorseScale]
      norm_num
      simpa using mul_le_mul_of_nonneg_left he2 Real.pi_pos.le
    dsimp only [q]
    rw [thetaCuspBornWittenWeight_eq]
    linarith
  have hqpos : 0 < q := by linarith
  have hA0profile : A0 = thetaCuspFirstAtomCurvatureProfile q := by
    dsimp only [A0, q]
    rw [thetaCuspBornWittenLogCurvature_eq_readoutProfile (by norm_num) hx]
    rfl
  have hB0profile : B0 = thetaCuspFirstAtomFourthProfile q := by
    dsimp only [B0, q]
    rfl
  have hC0profile : C0 = thetaCuspFirstAtomSixthProfile q := by
    change
      (2 * q + 3) * (32 + 48 / q ^ 2 + 2160 / q ^ 3 +
        16200 / q ^ 4 + 38880 / q ^ 5 + 29160 / q ^ 6) =
        thetaCuspFirstAtomSixthProfile q
    dsimp only [thetaCuspFirstAtomSixthProfile]
    field_simp [hqpos.ne']
    ring
  have hD0profile : D0 = thetaCuspFirstAtomEighthProfile q := by
    dsimp only [D0, q, thetaCuspBornWittenLogEighthDerivative,
      thetaCuspFirstAtomEighthProfile]
  have hA0 : (19 : ℝ) ≤ A0 := by
    simpa only [A0] using
      nineteen_le_thetaCuspBornWittenLogCurvature (n := 1) (by norm_num) hx
  have he2pos : 0 < e2 := by
    simpa only [e2] using thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hx
  have he2upper : e2 ≤ (13 / 10 : ℝ) := by
    simpa only [e2] using
      thetaCuspLikelihoodSourceLogPartitionJetTwo_le_thirteen_tenths hx
  have he4 : 0 ≤ e4 := by
    simpa only [e4] using (thetaCuspLikelihoodSourceLogPartitionJetFour_pos hx).le
  have he6 : 0 ≤ e6 := by
    simpa only [e6] using (thetaCuspLikelihoodSourceLogPartitionJetSix_pos hx).le
  have he8 : 0 ≤ e8 := by
    simpa only [e8] using (thetaCuspLikelihoodSourceLogPartitionJetEight_pos hx).le
  have hWpos : 0 < W := by
    dsimp only [W]
    linarith
  have hWA : W ≤ A := by
    dsimp only [W, A]
    linarith
  have hAA0 : A ≤ A0 := by
    dsimp only [A]
    linarith
  have hC0 : 0 < C0 := by
    simpa only [C0] using
      thetaCuspBornWittenLogSixthDerivative_pos (n := 1) (by norm_num) hx
  have hB0upper : B0 ≤ (6 / 5 : ℝ) * A0 ^ 2 := by
    simpa only [A0, B0] using
      thetaCuspBornWittenLogFourthDerivative_le_sixFifths_curvature_sq
        (n := 1) (by norm_num) hx
  have hWratio : (177 / 190 : ℝ) * A0 ≤ W := by
    dsimp only [W]
    nlinarith
  have hratioSq : (177 / 190 : ℝ) ^ 2 * A0 ^ 2 ≤ W ^ 2 := by
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (177 / 190) * A0)
      hWratio 2
    simpa only [mul_pow] using hpow
  have hB0 : B0 < (7 / 5 : ℝ) * W ^ 2 := by
    have hcoef : (6 / 5 : ℝ) < (7 / 5 : ℝ) * (177 / 190) ^ 2 := by
      norm_num
    have hA0sq : 0 < A0 ^ 2 := by positivity
    have hstrict : (6 / 5 : ℝ) * A0 ^ 2 <
        ((7 / 5 : ℝ) * (177 / 190) ^ 2) * A0 ^ 2 :=
      mul_lt_mul_of_pos_right hcoef hA0sq
    nlinarith
  have hG : 0 < 576 * W ^ 4 - 672 * W ^ 2 * B0 + 76 * B0 ^ 2 +
      48 * W * C0 - D0 := by
    dsimp only [W]
    rw [hA0profile, hB0profile, hC0profile, hD0profile]
    simpa only using thetaCuspFirstAtomEighthCurvatureDerivativeBracket_pos hq
  have h := thetaCuspReflectedEighthPolynomial_compactReserve_le
    hWpos hWA hAA0 hB0 hC0 hG he4 he6 he8
  dsimp only [thetaCuspFullReflectionEighthCompactReserve,
    thetaCuspFullReflectionEighthCompactFourthCoefficient,
    thetaCuspFullReflectionEighthCompactSixthCoefficient,
    thetaCuspFullReflectionEighthCompactEighthCoefficient,
    thetaCuspFirstAtomEighthNoSixthLossBaseline] at ⊢
  rw [← hA0profile, ← hB0profile, ← hC0profile, ← hD0profile]
  dsimp only [q, e4, e6, e8, A0, B0, C0, D0, A, W] at h ⊢
  unfold thetaCuspFullReflectionEighthHankelCurvature
    thetaCuspFullReflectedLogCurvature thetaCuspFullReflectedLogFourthJet
    thetaCuspFullReflectedLogSixthJet thetaCuspFullReflectedLogEighthJet
  exact h

/-- Positivity of the explicit compact reserve is sufficient for native D1 positivity. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_compactReserve_pos
    {x : ℝ} (hx : 0 ≤ x)
    (hreserve : 0 < thetaCuspFullReflectionEighthCompactReserve x) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x :=
  hreserve.trans_le (thetaCuspFullReflectionEighthCompactReserve_le_hankelCurvature hx)

end

end RHTower

import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthCompactReserve
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthEighthSpectralCoupling

/-!
# Sixth-spectral compact reserve for eighth reflected curvature

The fixed higher-theta spectrum couples the positive logarithmic eighth likelihood jet to the
sixth jet.  Since the eighth coefficient in the sharp compact reserve is itself positive, that
coupling converts the independent eighth gain into an explicit sixth-loss compensation.  The
resulting strict lower reserve depends only on the fourth and sixth likelihood jets.
-/

namespace RHTower

noncomputable section

/-- The eighth-jet coefficient in the compact reserve is strictly positive on the physical
source half-line. -/
theorem thetaCuspFullReflectionEighthCompactEighthCoefficient_pos
    {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspFullReflectionEighthCompactEighthCoefficient
      (thetaCuspBornWittenWeight 1 x) := by
  let q := thetaCuspBornWittenWeight 1 x
  let A0 := thetaCuspBornWittenLogCurvature 1 x
  let B0 := thetaCuspBornWittenLogFourthDerivative 1 x
  have hA0profile : A0 = thetaCuspFirstAtomCurvatureProfile q := by
    dsimp only [A0, q]
    rw [thetaCuspBornWittenLogCurvature_eq_readoutProfile (by norm_num) hx]
    rfl
  have hB0profile : B0 = thetaCuspFirstAtomFourthProfile q := by
    dsimp only [B0, q]
    rfl
  have hA0 : (19 : ℝ) ≤ A0 := by
    simpa only [A0] using
      nineteen_le_thetaCuspBornWittenLogCurvature (n := 1) (by norm_num) hx
  have hB0upper : B0 ≤ (6 / 5 : ℝ) * A0 ^ (2 : ℕ) := by
    simpa only [A0, B0] using
      thetaCuspBornWittenLogFourthDerivative_le_sixFifths_curvature_sq
        (n := 1) (by norm_num) hx
  have hWratio : (177 / 190 : ℝ) * A0 ≤ A0 - 13 / 10 := by
    nlinarith
  have hratioSq : (177 / 190 : ℝ) ^ (2 : ℕ) * A0 ^ (2 : ℕ) ≤ (A0 - 13 / 10) ^ (2 : ℕ) := by
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (177 / 190) * A0)
      hWratio 2
    simpa only [mul_pow] using hpow
  have hcoef : (6 / 5 : ℝ) < 4 * (177 / 190) ^ (2 : ℕ) := by norm_num
  have hA0sq : 0 < A0 ^ (2 : ℕ) := by positivity
  have hstrict : (6 / 5 : ℝ) * A0 ^ (2 : ℕ) <
      (4 * (177 / 190) ^ (2 : ℕ)) * A0 ^ (2 : ℕ) :=
    mul_lt_mul_of_pos_right hcoef hA0sq
  dsimp only [thetaCuspFullReflectionEighthCompactEighthCoefficient]
  rw [← hA0profile, ← hB0profile]
  nlinarith

/-- Compact reserve after replacing the eighth likelihood gain by the shared-spectrum lower
multiple of the sixth likelihood jet. -/
def thetaCuspFullReflectionEighthSixthSpectralReserve (x : ℝ) : ℝ :=
  let q := thetaCuspBornWittenWeight 1 x
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let e4 := thetaCuspLikelihoodSourceLogPartitionJetFour x
  let e6 := thetaCuspLikelihoodSourceLogPartitionJetSix x
  thetaCuspFirstAtomEighthNoSixthLossBaseline q +
    e4 * (68 * e4 ^ (2 : ℕ) +
      (304 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (2 : ℕ) -
        204 * thetaCuspFirstAtomFourthProfile q) * e4 +
      thetaCuspFullReflectionEighthCompactFourthCoefficient q) +
    e6 * ((thetaCuspFullReflectionEighthCompactEighthCoefficient q + e4) *
      (1 / 69) * A ^ (2 : ℕ) -
      (thetaCuspFullReflectionEighthCompactSixthCoefficient q + e6))

/-- The sixth-spectral reserve is a strict lower bound for the compact reserve. -/
theorem thetaCuspFullReflectionEighthSixthSpectralReserve_lt_compactReserve
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspFullReflectionEighthSixthSpectralReserve x <
      thetaCuspFullReflectionEighthCompactReserve x := by
  let q := thetaCuspBornWittenWeight 1 x
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let e4 := thetaCuspLikelihoodSourceLogPartitionJetFour x
  let e6 := thetaCuspLikelihoodSourceLogPartitionJetSix x
  let e8 := thetaCuspLikelihoodSourceLogPartitionJetEight x
  have hcoef0 : 0 < thetaCuspFullReflectionEighthCompactEighthCoefficient q := by
    simpa only [q] using thetaCuspFullReflectionEighthCompactEighthCoefficient_pos hx
  have he4 : 0 < e4 := by
    simpa only [e4] using thetaCuspLikelihoodSourceLogPartitionJetFour_pos hx
  have hcoef : 0 < thetaCuspFullReflectionEighthCompactEighthCoefficient q + e4 := by
    linarith
  have hcoupling : (1 / 69 : ℝ) * A ^ (2 : ℕ) * e6 < e8 := by
    simpa only [A, e6, e8] using
      oneSixtyNinth_mul_scale_sq_logJetSix_lt_logJetEight hx
  have hgain := mul_lt_mul_of_pos_left hcoupling hcoef
  dsimp only [thetaCuspFullReflectionEighthSixthSpectralReserve,
    thetaCuspFullReflectionEighthCompactReserve]
  dsimp only [q, A, e4, e6, e8] at hgain ⊢
  nlinarith

/-- Positivity of the sixth-spectral reserve is sufficient for native D1 positivity. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_sixthSpectralReserve_pos
    {x : ℝ} (hx : 0 ≤ x)
    (hreserve : 0 < thetaCuspFullReflectionEighthSixthSpectralReserve x) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  exact hreserve.trans
    ((thetaCuspFullReflectionEighthSixthSpectralReserve_lt_compactReserve hx).trans_le
      (thetaCuspFullReflectionEighthCompactReserve_le_hankelCurvature hx))

end

end RHTower

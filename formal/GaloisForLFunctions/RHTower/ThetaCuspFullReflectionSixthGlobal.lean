import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionSixthBellTransfer
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionSixthLogJets
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodFourthSixthSpectralDomination
import GaloisForLFunctions.RHTower.ThetaCuspAtomLikelihoodCrossDomination

/-!
# Global strict reflected sixth curvature of the complete theta source

The first Born--Witten atom is measured in its exact positive weight coordinate.  Shared
fourth--sixth likelihood spectral domination limits the higher-source losses to `2432` and
`63232`, while the second loss is at most `13/10`.  Clearing denominators at the exact support
edge `q = 41/25` yields a positive worst-loss polynomial.  Monotonicity then transfers that
certificate to the actual log jets.

The real Bell transfer converts the log-jet certificate into raw reflected-product curvature.
Evenness and the separately closed modular seam give a strict theorem on all real source
coordinates.
-/

open Real

namespace RHTower

noncomputable section
/-- Exact first-atom curvature profile in Born--Witten weight coordinates. -/
def thetaCuspFirstAtomCurvatureProfile (q : ℝ) : ℝ :=
  4 * q + 6 + 6 / q + 9 / q ^ (2 : ℕ)

/-- Exact first-atom fourth log-jet profile. -/
def thetaCuspFirstAtomFourthProfile (q : ℝ) : ℝ :=
  (2 * q + 3) * (8 + 12 / q ^ (2 : ℕ) + 108 / q ^ (3 : ℕ) + 162 / q ^ (4 : ℕ))

/-- Exact first-atom sixth log-jet profile. -/
def thetaCuspFirstAtomSixthProfile (q : ℝ) : ℝ :=
  let s := q + 3 / 2
  64 * s + 96 * s / q ^ (2 : ℕ) + 4320 * s / q ^ (3 : ℕ) +
    32400 * s / q ^ (4 : ℕ) + 77760 * s / q ^ (5 : ℕ) + 58320 * s / q ^ (6 : ℕ)

/-- Quartic Bell remainder in reflected second--sixth curvature. -/
def thetaCuspReflectedSixthBellRemainder (A B : ℝ) : ℝ :=
  -B ^ (2 : ℕ) - 18 * A ^ (2 : ℕ) * B + 24 * A ^ (4 : ℕ)

set_option maxHeartbeats 2000000 in
/-- The exact worst likelihood-loss profile remains strictly positive from the support edge. -/
theorem thetaCuspFirstAtomWorstLikelihoodLossProfile_pos
    {q : ℝ} (hq : (41 / 25 : ℝ) ≤ q) :
    let A := thetaCuspFirstAtomCurvatureProfile q - 13 / 10
    0 < A * (thetaCuspFirstAtomSixthProfile q - 63232) +
      thetaCuspReflectedSixthBellRemainder A (thetaCuspFirstAtomFourthProfile q) := by
  have hqpos : 0 < q := by linarith
  let y := q - 41 / 25
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hy2 : 0 ≤ y ^ (2 : ℕ) := by positivity
  have hy3 : 0 ≤ y ^ (3 : ℕ) := by positivity
  have hy4 : 0 ≤ y ^ (4 : ℕ) := by positivity
  have hy5 : 0 ≤ y ^ (5 : ℕ) := by positivity
  have hy6 : 0 ≤ y ^ (6 : ℕ) := by positivity
  have hy7 : 0 ≤ y ^ (7 : ℕ) := by positivity
  have hy8 : 0 ≤ y ^ (8 : ℕ) := by positivity
  have hy9 : 0 ≤ y ^ (9 : ℕ) := by positivity
  have hy10 : 0 ≤ y ^ (10 : ℕ) := by positivity
  have hy11 : 0 ≤ y ^ (11 : ℕ) := by positivity
  have hy12 : 0 ≤ y ^ (12 : ℕ) := by positivity
  let E :=
    (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) *
        (thetaCuspFirstAtomSixthProfile q - 63232) +
      thetaCuspReflectedSixthBellRemainder
        (thetaCuspFirstAtomCurvatureProfile q - 13 / 10)
        (thetaCuspFirstAtomFourthProfile q)
  have hmul : 0 < q ^ (8 : ℕ) * E := by
    dsimp [E, thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile, thetaCuspReflectedSixthBellRemainder]
    field_simp [hqpos.ne']
    rw [show q = 41 / 25 + y by dsimp [y]; ring]
    ring_nf
    nlinarith
  dsimp only [E] at hmul
  dsimp only
  by_contra hE
  have hnonpos : q ^ (8 : ℕ) *
      ((thetaCuspFirstAtomCurvatureProfile q - 13 / 10) *
          (thetaCuspFirstAtomSixthProfile q - 63232) +
        thetaCuspReflectedSixthBellRemainder
          (thetaCuspFirstAtomCurvatureProfile q - 13 / 10)
          (thetaCuspFirstAtomFourthProfile q)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_gt hE)
  exact (not_le_of_gt hmul) hnonpos

set_option maxHeartbeats 2000000 in
/-- Positive-coordinate logarithmic reflected sixth curvature of the complete source. -/
theorem thetaCuspFullReflectionSixthCurvature_pos_of_pos
    {x : ℝ} (hx : 0 < x) :
    0 < thetaCuspFullReflectionSixthCurvature x := by
  let q := thetaCuspBornWittenWeight 1 x
  let A0 := thetaCuspBornWittenLogCurvature 1 x
  let B0 := thetaCuspBornWittenLogFourthDerivative 1 x
  let C0 := thetaCuspBornWittenLogSixthDerivative 1 x
  let e2 := thetaCuspLikelihoodSourceLogPartitionJetTwo x
  let e4 := thetaCuspLikelihoodSourceLogPartitionJetFour x
  let e6 := thetaCuspLikelihoodSourceLogPartitionJetSix x
  let A := A0 - e2
  let B := B0 - e4
  let C := C0 - e6
  let Aw := A0 - 13 / 10
  have hq : (41 / 25 : ℝ) ≤ q := by
    have hpi := Real.pi_gt_d2
    norm_num at hpi
    have he : 1 ≤ Real.exp x := Real.one_le_exp hx.le
    have he2 : 1 ≤ Real.exp x ^ (2 : ℕ) := by nlinarith [Real.exp_pos x]
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
    rw [thetaCuspBornWittenLogCurvature_eq_readoutProfile (by norm_num) hx.le]
    rfl
  have hB0profile : B0 = thetaCuspFirstAtomFourthProfile q := by
    dsimp only [B0, q]
    rfl
  have hC0profile : C0 = thetaCuspFirstAtomSixthProfile q := by
    change
      (2 * q + 3) * (32 + 48 / q ^ (2 : ℕ) + 2160 / q ^ (3 : ℕ) +
        16200 / q ^ (4 : ℕ) + 38880 / q ^ (5 : ℕ) + 29160 / q ^ (6 : ℕ)) =
        thetaCuspFirstAtomSixthProfile q
    dsimp only [thetaCuspFirstAtomSixthProfile]
    field_simp [hqpos.ne']
    ring
  have hA0 : (19 : ℝ) ≤ A0 := by
    simpa only [A0] using
      nineteen_le_thetaCuspBornWittenLogCurvature (n := 1) (by norm_num) hx.le
  have hB0 : 0 < B0 := by
    simpa only [B0] using
      thetaCuspBornWittenLogFourthDerivative_pos (n := 1) (by norm_num) hx.le
  have hC0 : 0 < C0 := by
    simpa only [C0] using
      thetaCuspBornWittenLogSixthDerivative_pos (n := 1) (by norm_num) hx.le
  have hB0upper : B0 ≤ (6 / 5 : ℝ) * A0 ^ (2 : ℕ) := by
    simpa only [A0, B0] using
      thetaCuspBornWittenLogFourthDerivative_le_sixFifths_curvature_sq
        (n := 1) (by norm_num) hx.le
  have he2pos : 0 < e2 := by
    simpa only [e2] using thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hx.le
  have he2upper : e2 ≤ (13 / 10 : ℝ) := by
    simpa only [e2] using
      thetaCuspLikelihoodSourceLogPartitionJetTwo_le_thirteen_tenths hx.le
  have he4pos : 0 < e4 := by
    simpa only [e4] using thetaCuspLikelihoodSourceLogPartitionJetFour_pos hx.le
  have he4upper : e4 < 2432 := by
    simpa only [e4] using
      thetaCuspLikelihoodSourceLogPartitionJetFour_lt_twoThousandFourHundredThirtyTwo hx.le
  have he6pos : 0 < e6 := by
    simpa only [e6] using thetaCuspLikelihoodSourceLogPartitionJetSix_pos hx.le
  have he6upper : e6 < 63232 := by
    simpa only [e6] using
      thetaCuspLikelihoodSourceLogPartitionJetSix_lt_sixtyThreeThousandTwoHundredThirtyTwo hx.le
  have hAwpos : 0 < Aw := by dsimp only [Aw]; linarith
  have hAwA : Aw ≤ A := by dsimp only [Aw, A]; linarith
  have hAA0 : A ≤ A0 := by dsimp only [A]; linarith
  have hApos : 0 < A := hAwpos.trans_le hAwA
  have hAmin : (177 / 10 : ℝ) ≤ A := by
    dsimp only [A, Aw] at hAwA hAwpos ⊢
    linarith
  have hBlower : -8 * A ^ (2 : ℕ) < B := by
    have hAsq : (177 / 10 : ℝ) ^ (2 : ℕ) ≤ A ^ (2 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) hAmin 2
    dsimp only [B]
    nlinarith
  have hBB0 : B < B0 := by dsimp only [B]; linarith
  have hQmono :
      thetaCuspReflectedSixthBellRemainder A B0 ≤
        thetaCuspReflectedSixthBellRemainder A B := by
    have hfactor1 : 0 < B0 - B := by linarith
    have hfactor2 : 0 < B + B0 + 18 * A ^ (2 : ℕ) := by
      nlinarith [hB0]
    dsimp only [thetaCuspReflectedSixthBellRemainder]
    nlinarith [mul_pos hfactor1 hfactor2]
  have hC : C0 - 63232 < C := by dsimp only [C]; linarith
  have hAC : A * (C0 - 63232) < A * C :=
    mul_lt_mul_of_pos_left hC hApos
  have hAwRatio : (177 / 190 : ℝ) * A0 ≤ Aw := by
    dsimp only [Aw]
    nlinarith
  have hAwCube : (177 / 190 : ℝ) ^ (3 : ℕ) * A0 ^ (3 : ℕ) ≤ Aw ^ (3 : ℕ) := by
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (177 / 190) * A0)
      hAwRatio 3
    simpa only [mul_pow] using hpow
  have hA0Cube : (19 : ℝ) ^ (3 : ℕ) ≤ A0 ^ (3 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) hA0 3
  have hsumUpper : A + Aw ≤ 2 * A0 := by linarith
  have hnegBound : 18 * B0 * (A + Aw) ≤ (216 / 5 : ℝ) * A0 ^ (3 : ℕ) := by
    have hsumNonneg : 0 ≤ A + Aw := by positivity
    calc
      18 * B0 * (A + Aw) ≤ 18 * ((6 / 5 : ℝ) * A0 ^ (2 : ℕ)) * (A + Aw) := by
        gcongr
      _ ≤ 18 * ((6 / 5 : ℝ) * A0 ^ (2 : ℕ)) * (2 * A0) := by
        gcongr
      _ = (216 / 5 : ℝ) * A0 ^ (3 : ℕ) := by ring
  have hsumCubes : 4 * Aw ^ (3 : ℕ) ≤
      A ^ (3 : ℕ) + A ^ (2 : ℕ) * Aw + A * Aw ^ (2 : ℕ) + Aw ^ (3 : ℕ) := by
    have hAwA2 := mul_le_mul_of_nonneg_left hAwA hAwpos.le
    have hAw2A2 : Aw ^ (2 : ℕ) ≤ A ^ (2 : ℕ) := by nlinarith
    have hAw3A3 : Aw ^ (3 : ℕ) ≤ A ^ (3 : ℕ) := by
      exact pow_le_pow_left₀ hAwpos.le hAwA 3
    have hAw3A2Aw : Aw ^ (3 : ℕ) ≤ A ^ (2 : ℕ) * Aw := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hAw2A2) hAwpos.le]
    have hAw3AAw2 : Aw ^ (3 : ℕ) ≤ A * Aw ^ (2 : ℕ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hAwA) (sq_nonneg Aw)]
    linarith
  have hDpos :
      0 < (C0 - 63232) - 18 * B0 * (A + Aw) +
        24 * (A ^ (3 : ℕ) + A ^ (2 : ℕ) * Aw + A * Aw ^ (2 : ℕ) + Aw ^ (3 : ℕ)) := by
    have hposBound :
        96 * ((177 / 190 : ℝ) ^ (3 : ℕ) * A0 ^ (3 : ℕ)) ≤
          24 * (A ^ (3 : ℕ) + A ^ (2 : ℕ) * Aw + A * Aw ^ (2 : ℕ) + Aw ^ (3 : ℕ)) := by
      calc
        96 * ((177 / 190 : ℝ) ^ (3 : ℕ) * A0 ^ (3 : ℕ)) ≤ 96 * Aw ^ (3 : ℕ) := by gcongr
        _ ≤ 24 * (A ^ (3 : ℕ) + A ^ (2 : ℕ) * Aw + A * Aw ^ (2 : ℕ) + Aw ^ (3 : ℕ)) := by
          nlinarith
    have hnumeric :
        (63232 : ℝ) + (216 / 5 : ℝ) * A0 ^ (3 : ℕ) <
          96 * ((177 / 190 : ℝ) ^ (3 : ℕ) * A0 ^ (3 : ℕ)) := by
      have hcoef : (63232 : ℝ) + (216 / 5 : ℝ) * 19 ^ (3 : ℕ) <
          96 * ((177 / 190 : ℝ) ^ (3 : ℕ) * 19 ^ (3 : ℕ)) := by norm_num
      have hcoefpos : 0 <
          96 * (177 / 190 : ℝ) ^ (3 : ℕ) - 216 / 5 := by norm_num
      nlinarith
    linarith
  have hHmono :
      Aw * (C0 - 63232) + thetaCuspReflectedSixthBellRemainder Aw B0 ≤
        A * (C0 - 63232) + thetaCuspReflectedSixthBellRemainder A B0 := by
    have hdiff :
        (A * (C0 - 63232) + thetaCuspReflectedSixthBellRemainder A B0) -
            (Aw * (C0 - 63232) + thetaCuspReflectedSixthBellRemainder Aw B0) =
          (A - Aw) * ((C0 - 63232) - 18 * B0 * (A + Aw) +
            24 * (A ^ (3 : ℕ) + A ^ (2 : ℕ) * Aw + A * Aw ^ (2 : ℕ) + Aw ^ (3 : ℕ))) := by
      dsimp only [thetaCuspReflectedSixthBellRemainder]
      ring
    rw [← sub_nonneg]
    rw [hdiff]
    exact mul_nonneg (sub_nonneg.mpr hAwA) hDpos.le
  have hworst :
      0 < Aw * (C0 - 63232) + thetaCuspReflectedSixthBellRemainder Aw B0 := by
    dsimp only [Aw]
    rw [hA0profile, hB0profile, hC0profile]
    simpa only using thetaCuspFirstAtomWorstLikelihoodLossProfile_pos hq
  have hactual :
      0 < A * C + thetaCuspReflectedSixthBellRemainder A B := by
    calc
      0 < Aw * (C0 - 63232) + thetaCuspReflectedSixthBellRemainder Aw B0 := hworst
      _ ≤ A * (C0 - 63232) + thetaCuspReflectedSixthBellRemainder A B0 := hHmono
      _ ≤ A * (C0 - 63232) + thetaCuspReflectedSixthBellRemainder A B := by
        linarith
      _ < A * C + thetaCuspReflectedSixthBellRemainder A B := by linarith
  dsimp only [thetaCuspReflectedSixthBellRemainder] at hactual
  have hactual' : 0 < A * C - B ^ (2 : ℕ) - 18 * A ^ (2 : ℕ) * B + 24 * A ^ (4 : ℕ) := by
    linarith
  change 0 < A * C - B ^ (2 : ℕ) - 18 * A ^ (2 : ℕ) * B + 24 * A ^ (4 : ℕ)
  exact hactual'

/-- Strict raw reflected second--sixth curvature on the positive source half-line. -/
theorem thetaCuspFullSourceReflectionSecondSixthCurvature_pos_of_pos
    {x : ℝ} (hx : 0 < x) :
    0 < thetaCuspFullSourceReflectionSecondSixthCurvature x := by
  rw [thetaCuspFullSourceReflectionSecondSixthCurvature_eq_logJets,
    thetaCuspLogSource_secondSixthHankel_eq_fullReflectionSixthCurvature hx]
  exact mul_pos (mul_pos (by norm_num) (pow_pos (thetaCuspFullSource_pos_all x) 4))
    (thetaCuspFullReflectionSixthCurvature_pos_of_pos hx)

/-- Global unconditional strict reflected second--sixth curvature of the complete theta source. -/
theorem thetaCuspFullSourceReflectionSecondSixthCurvature_pos :
    ∀ x : ℝ, 0 < thetaCuspFullSourceReflectionSecondSixthCurvature x := by
  intro x
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hpos := thetaCuspFullSourceReflectionSecondSixthCurvature_pos_of_pos
      (x := -x) (neg_pos.mpr hx)
    rw [thetaCuspFullSourceReflectionSecondSixthCurvature_eq_logJets] at hpos ⊢
    rw [thetaCuspFullSource_neg x,
      iteratedDeriv_thetaCuspLogSource_neg 2 x,
      iteratedDeriv_thetaCuspLogSource_neg 4 x,
      iteratedDeriv_thetaCuspLogSource_neg 6 x] at hpos
    norm_num at hpos
    exact hpos
  · exact thetaCuspFullSourceReflectionSecondSixthCurvature_zero_pos
  · exact thetaCuspFullSourceReflectionSecondSixthCurvature_pos_of_pos hx

end

end RHTower

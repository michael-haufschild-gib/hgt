import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthLowerJetBaseline

/-!
# Strict eighth reflected curvature at large source weight

The uniform sixth likelihood bound becomes sufficient once the exact first-atom weight reaches
`q = 5`. Positive-coefficient profile certificates propagate the worst sixth loss through the
curvature, sixth-jet, and fourth-jet displacements. The elementary exponential lower bound then
places every `x ≥ 11/20` in this chamber.
-/

namespace RHTower

noncomputable section

/-- Exact first-atom rank-three baseline after the uniform worst sixth likelihood loss. -/
def thetaCuspFirstAtomEighthWorstSixthLossBaseline (q : ℝ) : ℝ :=
  thetaCuspReflectedEighthPolynomial
    (thetaCuspFirstAtomCurvatureProfile q - 13 / 10)
    (thetaCuspFirstAtomFourthProfile q)
    (thetaCuspFirstAtomSixthProfile q - 63232)
    (thetaCuspFirstAtomEighthProfile q)

/-- Above weight five, even the uniform worst sixth loss leaves a strict baseline. -/
theorem thetaCuspFirstAtomEighthWorstSixthLossBaseline_pos {q : ℝ} (hq : 5 ≤ q) :
    0 < thetaCuspFirstAtomEighthWorstSixthLossBaseline q := by
  have hqpos : 0 < q := by linarith
  let y := q - 5
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hmul : 0 < q ^ 16 * thetaCuspFirstAtomEighthWorstSixthLossBaseline q := by
    dsimp [thetaCuspFirstAtomEighthWorstSixthLossBaseline, thetaCuspReflectedEighthPolynomial,
      thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile, thetaCuspFirstAtomEighthProfile]
    field_simp [hqpos.ne']
    rw [show q = 5 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 16]

/-- The curvature derivative bracket survives the uniform worst sixth loss. -/
theorem thetaCuspFirstAtomEighthWorstSixthLossCurvatureBracket_pos {q : ℝ} (hq : 5 ≤ q) :
    let Aw := thetaCuspFirstAtomCurvatureProfile q - 13 / 10
    let B0 := thetaCuspFirstAtomFourthProfile q
    let Cw := thetaCuspFirstAtomSixthProfile q - 63232
    let D0 := thetaCuspFirstAtomEighthProfile q
    0 < 576 * Aw ^ 4 - 672 * Aw ^ 2 * B0 + 76 * B0 ^ 2 +
      48 * Aw * Cw - D0 := by
  have hqpos : 0 < q := by linarith
  let y := q - 5
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  dsimp only
  have hmul : 0 < q ^ 16 *
      (576 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ 4 -
        672 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ 2 *
          thetaCuspFirstAtomFourthProfile q +
        76 * thetaCuspFirstAtomFourthProfile q ^ 2 +
        48 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) *
          (thetaCuspFirstAtomSixthProfile q - 63232) -
        thetaCuspFirstAtomEighthProfile q) := by
    dsimp [thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile, thetaCuspFirstAtomEighthProfile]
    field_simp [hqpos.ne']
    rw [show q = 5 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 16]

/-- The derivative of the curvature bracket is positive at the worst curvature. -/
theorem thetaCuspFirstAtomEighthWorstSixthLossCurvatureBracketDerivative_pos {q : ℝ} (hq : 5 ≤ q) :
    let Aw := thetaCuspFirstAtomCurvatureProfile q - 13 / 10
    let B0 := thetaCuspFirstAtomFourthProfile q
    let Cw := thetaCuspFirstAtomSixthProfile q - 63232
    0 < 2 * Aw * (1152 * Aw ^ 2 - 672 * B0) + 48 * Cw := by
  have hqpos : 0 < q := by linarith
  let y := q - 5
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  dsimp only
  have hmul : 0 < q ^ 10 *
      (2 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) *
          (1152 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ 2 -
            672 * thetaCuspFirstAtomFourthProfile q) +
        48 * (thetaCuspFirstAtomSixthProfile q - 63232)) := by
    dsimp [thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile]
    field_simp [hqpos.ne']
    rw [show q = 5 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 10]

/-- Curvature monotonicity with a possibly negative lower sixth-jet comparator. -/
theorem thetaCuspReflectedEighthPolynomial_mono_curvature_of_lower_sixth
    {Aw A B Cw C D : ℝ} (hAwpos : 0 < Aw) (hAwA : Aw ≤ A)
    (hB : B < (7 / 5 : ℝ) * Aw ^ 2) (hCwC : Cw ≤ C)
    (hG : 0 < 576 * Aw ^ 4 - 672 * Aw ^ 2 * B + 76 * B ^ 2 +
      48 * Aw * Cw - D)
    (hJ : 0 < 2 * Aw * (1152 * Aw ^ 2 - 672 * B) + 48 * Cw) :
    thetaCuspReflectedEighthPolynomial Aw B C D ≤
      thetaCuspReflectedEighthPolynomial A B C D := by
  let G : ℝ → ℝ := fun t =>
    576 * t ^ 4 - 672 * t ^ 2 * B + 76 * B ^ 2 + 48 * t * C - D
  let Gw : ℝ → ℝ := fun t =>
    576 * t ^ 4 - 672 * t ^ 2 * B + 76 * B ^ 2 + 48 * t * Cw - D
  let L : ℝ → ℝ := fun t =>
    (t + Aw) * (576 * (t ^ 2 + Aw ^ 2) - 672 * B) + 48 * Cw
  let f : ℝ → ℝ := fun t => thetaCuspReflectedEighthPolynomial t B C D
  have hLpos : ∀ t, Aw ≤ t → 0 < L t := by
    intro t ht
    have hdiff : L t - L Aw =
        (t - Aw) * (576 * (t ^ 2 + 2 * t * Aw + 3 * Aw ^ 2) - 672 * B) := by
      dsimp only [L]
      ring
    have hcore : 0 < 576 * (t ^ 2 + 2 * t * Aw + 3 * Aw ^ 2) - 672 * B := by
      have htpos : 0 < t := hAwpos.trans_le ht
      have htsq : Aw ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hAwpos.le ht 2
      have hcross : Aw ^ 2 ≤ t * Aw := by nlinarith
      nlinarith
    have hLAw : 0 < L Aw := by
      dsimp only [L]
      nlinarith [hJ]
    rw [hdiff] at *
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) hcore.le]
  have hGwpos : ∀ t, Aw ≤ t → 0 < Gw t := by
    intro t ht
    have hdiff : Gw t - Gw Aw = (t - Aw) * L t := by
      dsimp only [Gw, L]
      ring
    have hGwAw : 0 < Gw Aw := by simpa only [Gw] using hG
    rw [hdiff] at *
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) (hLpos t ht).le]
  have hGpos : ∀ t, Aw ≤ t → 0 < G t := by
    intro t ht
    have htpos : 0 < t := hAwpos.trans_le ht
    have hdiff : G t - Gw t = 48 * t * (C - Cw) := by
      dsimp only [G, Gw]
      ring
    have hnonneg : 0 ≤ 48 * t * (C - Cw) := by positivity
    rw [hdiff] at *
    linarith [hGwpos t ht]
  have hf' : ∀ t : ℝ, HasDerivAt f (8 * t * G t) t := by
    intro t
    dsimp only [f, G, thetaCuspReflectedEighthPolynomial]
    convert (((((((((hasDerivAt_id t).pow 6).const_mul 768).sub
        (((hasDerivAt_id t).pow 4).mul_const B |>.const_mul 1344)).add
        (((hasDerivAt_id t).pow 2).mul_const (B ^ 2) |>.const_mul 304)).sub
        (hasDerivAt_const t (68 * B ^ 3))).add
        (((hasDerivAt_id t).pow 3).mul_const C |>.const_mul 128)).sub
        (((hasDerivAt_id t).pow 2).mul_const D |>.const_mul 4)).add
        (hasDerivAt_const t (B * D))).sub
        (hasDerivAt_const t (C ^ 2)) using 1
    all_goals try rfl
    · funext y
      simp only [Pi.pow_apply, Pi.add_apply, Pi.sub_apply, id_eq]
      ring
    · norm_num
      ring
  have hstrict : StrictMonoOn f (Set.Ici Aw) :=
    strictMonoOn_of_deriv_pos (convex_Ici Aw) (by
      dsimp only [f, thetaCuspReflectedEighthPolynomial]
      fun_prop) (by
      intro t ht
      rw [interior_Ici] at ht
      have hAwt : Aw < t := by simpa using ht
      rw [(hf' t).deriv]
      exact mul_pos (mul_pos (by norm_num) (hAwpos.trans hAwt))
        (hGpos t hAwt.le))
  exact hstrict.monotoneOn (by simp) (by simpa using hAwA) hAwA

/-- Full Born-top baseline is strict whenever the first-atom weight is at least five. -/
theorem thetaCuspFullReflectionEighthBornTopBaseline_pos_of_five_le_weight
    {x : ℝ} (hx : 0 ≤ x) (hq5 : (5 : ℝ) ≤ thetaCuspBornWittenWeight 1 x) :
    0 < thetaCuspFullReflectionEighthBornTopBaseline x := by
  let q := thetaCuspBornWittenWeight 1 x
  let A0 := thetaCuspBornWittenLogCurvature 1 x
  let B0 := thetaCuspBornWittenLogFourthDerivative 1 x
  let C0 := thetaCuspBornWittenLogSixthDerivative 1 x
  let D0 := thetaCuspBornWittenLogEighthDerivative 1 x
  let e2 := thetaCuspLikelihoodSourceLogPartitionJetTwo x
  let e4 := thetaCuspLikelihoodSourceLogPartitionJetFour x
  let e6 := thetaCuspLikelihoodSourceLogPartitionJetSix x
  let A := A0 - e2
  let B := B0 - e4
  let C := C0 - e6
  let Aw := A0 - 13 / 10
  let Cw := C0 - 63232
  have hq : (5 : ℝ) ≤ q := by simpa only [q] using hq5
  have hqSupport : (41 / 25 : ℝ) ≤ q := by linarith
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
  have hB0upper : B0 ≤ (6 / 5 : ℝ) * A0 ^ 2 := by
    simpa only [A0, B0] using
      thetaCuspBornWittenLogFourthDerivative_le_sixFifths_curvature_sq
        (n := 1) (by norm_num) hx
  have he2upper : e2 ≤ (13 / 10 : ℝ) := by
    simpa only [e2] using
      thetaCuspLikelihoodSourceLogPartitionJetTwo_le_thirteen_tenths hx
  have he4pos : 0 < e4 := by
    simpa only [e4] using thetaCuspLikelihoodSourceLogPartitionJetFour_pos hx
  have he6pos : 0 < e6 := by
    simpa only [e6] using thetaCuspLikelihoodSourceLogPartitionJetSix_pos hx
  have he6upper : e6 < 63232 := by
    simpa only [e6] using
      thetaCuspLikelihoodSourceLogPartitionJetSix_lt_sixtyThreeThousandTwoHundredThirtyTwo hx
  have hAwpos : 0 < Aw := by dsimp only [Aw]; linarith
  have hAwA : Aw ≤ A := by dsimp only [Aw, A]; linarith
  have hBB0 : B < B0 := by dsimp only [B]; linarith
  have hCwC : Cw < C := by dsimp only [Cw, C]; linarith
  have hAwRatio : (177 / 190 : ℝ) * A0 ≤ Aw := by
    dsimp only [Aw]
    nlinarith
  have hratioSq : (177 / 190 : ℝ) ^ 2 * A0 ^ 2 ≤ Aw ^ 2 := by
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (177 / 190) * A0)
      hAwRatio 2
    simpa only [mul_pow] using hpow
  have hB0Aw : B0 < (7 / 5 : ℝ) * Aw ^ 2 := by
    have hcoef : (6 / 5 : ℝ) < (7 / 5 : ℝ) * (177 / 190) ^ 2 := by norm_num
    have hA0sq : 0 < A0 ^ 2 := by positivity
    have hstrict : (6 / 5 : ℝ) * A0 ^ 2 <
        ((7 / 5 : ℝ) * (177 / 190) ^ 2) * A0 ^ 2 :=
      mul_lt_mul_of_pos_right hcoef hA0sq
    nlinarith
  have hbase : 0 < thetaCuspReflectedEighthPolynomial Aw B0 Cw D0 := by
    dsimp only [Aw, Cw]
    rw [hA0profile, hB0profile, hC0profile, hD0profile]
    simpa only [thetaCuspFirstAtomEighthWorstSixthLossBaseline] using thetaCuspFirstAtomEighthWorstSixthLossBaseline_pos hq
  have hCcoefWorst : 0 < 128 * Aw ^ 3 - 2 * C0 := by
    dsimp only [Aw]
    rw [hA0profile, hC0profile]
    exact thetaCuspFirstAtomEighthSixthLossCoefficient_pos hqSupport
  have hCcoef : 0 < 128 * Aw ^ 3 - C - Cw := by
    dsimp only [C, Cw]
    nlinarith
  have hCmono : thetaCuspReflectedEighthPolynomial Aw B0 Cw D0 <
      thetaCuspReflectedEighthPolynomial Aw B0 C D0 := by
    have hdiff :
        thetaCuspReflectedEighthPolynomial Aw B0 C D0 -
            thetaCuspReflectedEighthPolynomial Aw B0 Cw D0 =
          (C - Cw) * (128 * Aw ^ 3 - C - Cw) := by
      unfold thetaCuspReflectedEighthPolynomial
      ring
    rw [← sub_pos, hdiff]
    exact mul_pos (sub_pos.mpr hCwC) hCcoef
  have hG : 0 < 576 * Aw ^ 4 - 672 * Aw ^ 2 * B0 + 76 * B0 ^ 2 +
      48 * Aw * Cw - D0 := by
    dsimp only [Aw, Cw]
    rw [hA0profile, hB0profile, hC0profile, hD0profile]
    simpa only using thetaCuspFirstAtomEighthWorstSixthLossCurvatureBracket_pos hq
  have hJ : 0 < 2 * Aw * (1152 * Aw ^ 2 - 672 * B0) + 48 * Cw := by
    dsimp only [Aw, Cw]
    rw [hA0profile, hB0profile, hC0profile]
    simpa only using thetaCuspFirstAtomEighthWorstSixthLossCurvatureBracketDerivative_pos hq
  have hK : 0 < 1344 * Aw ^ 4 - 608 * Aw ^ 2 * B0 + 204 * B0 ^ 2 - D0 := by
    dsimp only [Aw]
    rw [hA0profile, hB0profile, hD0profile]
    simpa only using thetaCuspFirstAtomEighthFourthDisplacementConstant_pos hqSupport
  have hAmono : thetaCuspReflectedEighthPolynomial Aw B0 C D0 ≤
      thetaCuspReflectedEighthPolynomial A B0 C D0 :=
    thetaCuspReflectedEighthPolynomial_mono_curvature_of_lower_sixth
      hAwpos hAwA hB0Aw hCwC.le hG hJ
  have hBmono : thetaCuspReflectedEighthPolynomial A B0 C D0 <
      thetaCuspReflectedEighthPolynomial A B C D0 :=
    thetaCuspReflectedEighthPolynomial_strictAnti_fourth hAwpos hAwA hBB0 hB0Aw hK
  change 0 < thetaCuspReflectedEighthPolynomial A B C D0
  exact ((hbase.trans hCmono).trans_le hAmono).trans hBmono

/-- The favorable eighth likelihood channel makes native D1 strict above weight five. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_five_le_weight
    {x : ℝ} (hx : 0 ≤ x) (hq5 : (5 : ℝ) ≤ thetaCuspBornWittenWeight 1 x) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  have hbase := thetaCuspFullReflectionEighthBornTopBaseline_pos_of_five_le_weight hx hq5
  have hA : 0 < thetaCuspFullReflectedLogCurvature x := by
    have hfirst := nineteen_le_thetaCuspBornWittenLogCurvature
      (n := 1) (by norm_num) hx
    have he2 := thetaCuspLikelihoodSourceLogPartitionJetTwo_le_thirteen_tenths hx
    unfold thetaCuspFullReflectedLogCurvature
    linarith
  have hcoef : 0 < 4 * thetaCuspFullReflectedLogCurvature x ^ 2 -
      thetaCuspFullReflectedLogFourthJet x := by
    have hfourth := thetaCuspFullReflectedLogFourthJet_lt_two_mul_curvature_sq hx
    nlinarith [sq_pos_of_pos hA]
  have he8 := thetaCuspLikelihoodSourceLogPartitionJetEight_pos hx
  rw [thetaCuspFullReflectionEighthHankelCurvature_eq_baseline_add_likelihoodGain]
  exact add_pos hbase (mul_pos hcoef he8)

/-- Native D1 is strictly positive on the complete large-source half-line `x ≥ 11/20`. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_eleven_twentieths_le
    {x : ℝ} (hx : (11 / 20 : ℝ) ≤ x) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  have hx0 : 0 ≤ x := by linarith
  have hexp : (21 / 10 : ℝ) ≤ Real.exp (2 * x) := by
    nlinarith [Real.add_one_le_exp (2 * x)]
  have hpi : (157 / 50 : ℝ) ≤ Real.pi := by
    have hp := Real.pi_gt_d2
    norm_num at hp ⊢
    exact hp.le
  have hprod : (13 / 2 : ℝ) < Real.pi * Real.exp (2 * x) := by
    calc
      (13 / 2 : ℝ) < (157 / 50 : ℝ) * (21 / 10 : ℝ) := by norm_num
      _ ≤ Real.pi * Real.exp (2 * x) := by gcongr
  have hq5 : (5 : ℝ) ≤ thetaCuspBornWittenWeight 1 x := by
    rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
    norm_num
    rw [show Real.exp x ^ 2 = Real.exp (2 * x) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
    linarith
  exact thetaCuspFullReflectionEighthHankelCurvature_pos_of_five_le_weight hx0 hq5

end

end RHTower

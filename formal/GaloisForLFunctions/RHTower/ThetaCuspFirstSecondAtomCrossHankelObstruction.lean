import GaloisForLFunctions.RHTower.PrimeArchThetaBornWittenPopescuCorrection
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthFockSector

/-!
# First--second theta-atom cross-Hankel obstruction

The reflected product of the full source is a sum of symmetrized atom-pair channels.  A tempting
rank-three route would prove every pair channel positive semidefinite before summing.  The first
off-diagonal pair already forbids this: its normalized signed second entry is uniformly below
`-656` throughout a rational interval containing the modular seam.

The quantitative negative budget is the positive survivor.  Any atomwise rank-three proof must
absorb this explicit cross defect with diagonal atom margins; pairwise positivity cannot work.
-/

namespace RHTower

noncomputable section

/-- First logarithmic source score in the Born--Witten readout coordinate. -/
def thetaCuspBornWittenRawLogScoreProfile (q : ℝ) : ℝ :=
  3 / 2 + 3 / q - 2 * q

/-- Born--Witten log curvature in factored readout coordinates. -/
def thetaCuspBornWittenLogCurvatureFactoredProfile (q : ℝ) : ℝ :=
  (2 * q + 3) * (2 + 3 / q ^ 2)

/-- Normalized signed second entry of one symmetrized atom-pair reflected channel. -/
def thetaCuspBornWittenCrossSignedSecondProfile (q r : ℝ) : ℝ :=
  2 * (thetaCuspBornWittenLogCurvatureFactoredProfile q +
    thetaCuspBornWittenLogCurvatureFactoredProfile r -
    (thetaCuspBornWittenRawLogScoreProfile q -
      thetaCuspBornWittenRawLogScoreProfile r) ^ 2)

/-- Native Born--Witten form of the normalized atom-pair cross entry. -/
def thetaCuspBornWittenCrossSignedSecond (n m : ℕ) (x : ℝ) : ℝ :=
  2 * (thetaCuspBornWittenLogCurvature n x +
    thetaCuspBornWittenLogCurvature m x -
    ((-2 * thetaCuspBornWittenSuperpotential n x) -
      (-2 * thetaCuspBornWittenSuperpotential m x)) ^ 2)

/-- The profile is the literal normalized Born--Witten cross entry. -/
theorem thetaCuspBornWittenCrossSignedSecond_eq_profile
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspBornWittenCrossSignedSecond n m x =
      thetaCuspBornWittenCrossSignedSecondProfile
        (thetaCuspBornWittenWeight n x) (thetaCuspBornWittenWeight m x) := by
  let q := thetaCuspBornWittenWeight n x
  let r := thetaCuspBornWittenWeight m x
  have hq : 0 < q := by
    simpa only [q] using thetaCuspBornWittenWeight_pos hn hx
  have hr : 0 < r := by
    simpa only [r] using thetaCuspBornWittenWeight_pos hm hx
  have hscoreQ :
      -2 * thetaCuspBornWittenSuperpotential n x =
        thetaCuspBornWittenRawLogScoreProfile q := by
    have h := two_thetaCuspBornWittenSuperpotential_eq_readoutProfile hn hx
    dsimp only [q, thetaCuspBornWittenRawLogScoreProfile]
    linarith
  have hscoreR :
      -2 * thetaCuspBornWittenSuperpotential m x =
        thetaCuspBornWittenRawLogScoreProfile r := by
    have h := two_thetaCuspBornWittenSuperpotential_eq_readoutProfile hm hx
    dsimp only [r, thetaCuspBornWittenRawLogScoreProfile]
    linarith
  have hcurvQ :
      thetaCuspBornWittenLogCurvature n x =
        thetaCuspBornWittenLogCurvatureFactoredProfile q := by
    rw [thetaCuspBornWittenLogCurvature_eq_readoutProfile hn hx]
    change 4 * q + 6 + 6 / q + 9 / q ^ 2 =
      thetaCuspBornWittenLogCurvatureFactoredProfile q
    unfold thetaCuspBornWittenLogCurvatureFactoredProfile
    field_simp [hq.ne']
    ring
  have hcurvR :
      thetaCuspBornWittenLogCurvature m x =
        thetaCuspBornWittenLogCurvatureFactoredProfile r := by
    rw [thetaCuspBornWittenLogCurvature_eq_readoutProfile hm hx]
    change 4 * r + 6 + 6 / r + 9 / r ^ 2 =
      thetaCuspBornWittenLogCurvatureFactoredProfile r
    unfold thetaCuspBornWittenLogCurvatureFactoredProfile
    field_simp [hr.ne']
    ring
  unfold thetaCuspBornWittenCrossSignedSecond
    thetaCuspBornWittenCrossSignedSecondProfile
  rw [hscoreQ, hscoreR, hcurvQ, hcurvR]

/-- Uniform cross-defect classification on a rational seam neighborhood in readout space. -/
theorem thetaCuspBornWittenCrossSignedSecondProfile_lt_neg_sixHundredFiftySix
    {q : ℝ} (hqlo : 41 / 25 ≤ q) (hqhi : q ≤ 23 / 14) :
    thetaCuspBornWittenCrossSignedSecondProfile q (4 * q + 9 / 2) < -656 := by
  let r := 4 * q + 9 / 2
  have hq0 : 0 < q := by linarith
  have hrlo : 553 / 50 ≤ r := by dsimp only [r]; linarith
  have hrhi : r ≤ 155 / 14 := by dsimp only [r]; linarith
  have hr0 : 0 < r := by linarith
  have hqinterval : 0 ≤ (q - 41 / 25) * (23 / 14 - q) :=
    mul_nonneg (sub_nonneg.mpr hqlo) (sub_nonneg.mpr hqhi)
  have hscoreq : 0 ≤ thetaCuspBornWittenRawLogScoreProfile q := by
    rw [show thetaCuspBornWittenRawLogScoreProfile q =
        (3 / 2 * q + 3 - 2 * q ^ 2) / q by
      unfold thetaCuspBornWittenRawLogScoreProfile
      field_simp [hq0.ne']]
    exact div_nonneg (by nlinarith) hq0.le
  have hscorer : thetaCuspBornWittenRawLogScoreProfile r < -20 := by
    have hid : thetaCuspBornWittenRawLogScoreProfile r + 20 =
        (43 / 2 * r + 3 - 2 * r ^ 2) / r := by
      unfold thetaCuspBornWittenRawLogScoreProfile
      field_simp [hr0.ne']
      ring
    have htail : 0 ≤ (r - 553 / 50) * (4 * r - 43 / 2) := by
      exact mul_nonneg (sub_nonneg.mpr hrlo) (by nlinarith)
    have hnum : 43 / 2 * r + 3 - 2 * r ^ 2 < 0 := by nlinarith
    have hdiv : (43 / 2 * r + 3 - 2 * r ^ 2) / r < 0 :=
      div_neg_of_neg_of_pos hnum hr0
    nlinarith
  have hqSquare : (8 / 3 : ℝ) ≤ q ^ 2 := by
    nlinarith [sq_nonneg (q - 41 / 25)]
  have hqInv : 3 / q ^ 2 ≤ (9 / 8 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos hq0)).2
    nlinarith
  have hcurvq : thetaCuspBornWittenLogCurvatureFactoredProfile q < 20 := by
    have hleft : 0 ≤ 2 * q + 3 := by positivity
    have hright : 0 ≤ 2 + 3 / q ^ 2 := by positivity
    have hmul : (2 * q + 3) * (2 + 3 / q ^ 2) ≤
        (44 / 7) * (25 / 8) := by
      gcongr
      · linarith
      · linarith
    unfold thetaCuspBornWittenLogCurvatureFactoredProfile
    nlinarith
  have hrSquare : (120 : ℝ) ≤ r ^ 2 := by
    nlinarith [sq_nonneg (r - 553 / 50)]
  have hrInv : 3 / r ^ 2 ≤ (1 / 40 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos hr0)).2
    nlinarith
  have hcurvr : thetaCuspBornWittenLogCurvatureFactoredProfile r < 52 := by
    have hleft : 0 ≤ 2 * r + 3 := by positivity
    have hright : 0 ≤ 2 + 3 / r ^ 2 := by positivity
    have hmul : (2 * r + 3) * (2 + 3 / r ^ 2) ≤
        (176 / 7) * (81 / 40) := by
      gcongr
      · linarith
      · linarith
    unfold thetaCuspBornWittenLogCurvatureFactoredProfile
    nlinarith
  have hdiff : 20 < thetaCuspBornWittenRawLogScoreProfile q -
      thetaCuspBornWittenRawLogScoreProfile r := by linarith
  have hdiffSq : 400 < (thetaCuspBornWittenRawLogScoreProfile q -
      thetaCuspBornWittenRawLogScoreProfile r) ^ 2 := by
    nlinarith
  unfold thetaCuspBornWittenCrossSignedSecondProfile
  dsimp only [r] at hcurvr hscorer hdiff hdiffSq ⊢
  nlinarith

/-- Signed second entry after mixing the normalized first atom with weight `rho` times the
normalized second atom. -/
def thetaCuspBornWittenFirstSecondMixedSignedSecondProfile (q rho : ℝ) : ℝ :=
  2 * thetaCuspBornWittenLogCurvatureFactoredProfile q +
    rho * thetaCuspBornWittenCrossSignedSecondProfile q (4 * q + 9 / 2) +
    2 * rho ^ 2 *
      thetaCuspBornWittenLogCurvatureFactoredProfile (4 * q + 9 / 2)

/-- Matching lower budget: the cross defect has magnitude less than `1058` on the same rational
seam interval. -/
theorem neg_oneThousandFiftyEight_lt_thetaCuspBornWittenCrossSignedSecondProfile
    {q : ℝ} (hqlo : 41 / 25 ≤ q) (hqhi : q ≤ 23 / 14) :
    -1058 < thetaCuspBornWittenCrossSignedSecondProfile q (4 * q + 9 / 2) := by
  let r := 4 * q + 9 / 2
  have hq0 : 0 < q := by linarith
  have hrlo : 553 / 50 ≤ r := by dsimp only [r]; linarith
  have hrhi : r ≤ 155 / 14 := by dsimp only [r]; linarith
  have hr0 : 0 < r := by linarith
  have hscoreq : thetaCuspBornWittenRawLogScoreProfile q < 1 := by
    have htail : 0 ≤ (q - 41 / 25) * (4 * q - 1 / 2) := by
      exact mul_nonneg (sub_nonneg.mpr hqlo) (by nlinarith)
    have hnum : 1 / 2 * q + 3 - 2 * q ^ 2 < 0 := by nlinarith
    have hid : thetaCuspBornWittenRawLogScoreProfile q - 1 =
        (1 / 2 * q + 3 - 2 * q ^ 2) / q := by
      unfold thetaCuspBornWittenRawLogScoreProfile
      field_simp [hq0.ne']
      ring
    have hdiv : (1 / 2 * q + 3 - 2 * q ^ 2) / q < 0 :=
      div_neg_of_neg_of_pos hnum hq0
    nlinarith
  have hscorer : -22 < thetaCuspBornWittenRawLogScoreProfile r := by
    have htail : 0 ≤ (155 / 14 - r) *
        (2 * (155 / 14 + r) - 47 / 2) := by
      exact mul_nonneg (sub_nonneg.mpr hrhi) (by nlinarith)
    have hnum : 0 < 47 / 2 * r + 3 - 2 * r ^ 2 := by nlinarith
    have hid : thetaCuspBornWittenRawLogScoreProfile r + 22 =
        (47 / 2 * r + 3 - 2 * r ^ 2) / r := by
      unfold thetaCuspBornWittenRawLogScoreProfile
      field_simp [hr0.ne']
      ring
    have hdiv : 0 < (47 / 2 * r + 3 - 2 * r ^ 2) / r :=
      div_pos hnum hr0
    nlinarith
  have hscoreq0 : 0 ≤ thetaCuspBornWittenRawLogScoreProfile q := by
    rw [show thetaCuspBornWittenRawLogScoreProfile q =
        (3 / 2 * q + 3 - 2 * q ^ 2) / q by
      unfold thetaCuspBornWittenRawLogScoreProfile
      field_simp [hq0.ne']]
    have hinterval : 0 ≤ (q - 41 / 25) * (23 / 14 - q) :=
      mul_nonneg (sub_nonneg.mpr hqlo) (sub_nonneg.mpr hqhi)
    exact div_nonneg (by nlinarith) hq0.le
  have hscorer0 : thetaCuspBornWittenRawLogScoreProfile r < 0 := by
    have htail : 0 ≤ (r - 553 / 50) * (4 * r - 3 / 2) := by
      exact mul_nonneg (sub_nonneg.mpr hrlo) (by nlinarith)
    have hnum : 3 / 2 * r + 3 - 2 * r ^ 2 < 0 := by nlinarith
    have hid : thetaCuspBornWittenRawLogScoreProfile r =
        (3 / 2 * r + 3 - 2 * r ^ 2) / r := by
      unfold thetaCuspBornWittenRawLogScoreProfile
      field_simp [hr0.ne']
    rw [hid]
    exact div_neg_of_neg_of_pos hnum hr0
  have hdiff0 : 0 < thetaCuspBornWittenRawLogScoreProfile q -
      thetaCuspBornWittenRawLogScoreProfile r := by linarith
  have hdiff : thetaCuspBornWittenRawLogScoreProfile q -
      thetaCuspBornWittenRawLogScoreProfile r < 23 := by linarith
  have hdiffSq : (thetaCuspBornWittenRawLogScoreProfile q -
      thetaCuspBornWittenRawLogScoreProfile r) ^ 2 < 529 := by
    nlinarith
  have hcurvq : 0 ≤ thetaCuspBornWittenLogCurvatureFactoredProfile q := by
    unfold thetaCuspBornWittenLogCurvatureFactoredProfile
    positivity
  have hcurvr : 0 ≤ thetaCuspBornWittenLogCurvatureFactoredProfile r := by
    unfold thetaCuspBornWittenLogCurvatureFactoredProfile
    positivity
  unfold thetaCuspBornWittenCrossSignedSecondProfile
  dsimp only [r] at hcurvr hscorer hdiff0 hdiff hdiffSq ⊢
  nlinarith

/-- Quantitative positive survivor: despite the indefinite cross channel, the first diagonal
strictly absorbs every nonnegative second-atom mixing weight at most `1/100`. -/
theorem thetaCuspBornWittenFirstSecondMixedSignedSecondProfile_pos
    {q rho : ℝ} (hqlo : 41 / 25 ≤ q) (hqhi : q ≤ 23 / 14)
    (hrho : 0 ≤ rho) (hrhoSmall : 100 * rho ≤ 1) :
    0 < thetaCuspBornWittenFirstSecondMixedSignedSecondProfile q rho := by
  let r := 4 * q + 9 / 2
  have hq0 : 0 < q := by linarith
  have hcross :=
    neg_oneThousandFiftyEight_lt_thetaCuspBornWittenCrossSignedSecondProfile
      hqlo hqhi
  have hcrossBudget : 0 ≤ rho *
      (thetaCuspBornWittenCrossSignedSecondProfile q (4 * q + 9 / 2) + 1058) := by
    exact mul_nonneg hrho (by linarith)
  have hcurvq : 12 < thetaCuspBornWittenLogCurvatureFactoredProfile q := by
    have hleft : 0 < 2 * q + 3 := by positivity
    have hright : 2 < 2 + 3 / q ^ 2 := by
      have hdiv : 0 < 3 / q ^ 2 := div_pos (by norm_num) (sq_pos_of_pos hq0)
      linarith
    have hmul : (2 * q + 3) * 2 <
        (2 * q + 3) * (2 + 3 / q ^ 2) :=
      mul_lt_mul_of_pos_left hright hleft
    unfold thetaCuspBornWittenLogCurvatureFactoredProfile
    nlinarith
  have hcurvr : 0 ≤ thetaCuspBornWittenLogCurvatureFactoredProfile r := by
    unfold thetaCuspBornWittenLogCurvatureFactoredProfile
    positivity
  have hdiag : 0 ≤ 2 * rho ^ 2 *
      thetaCuspBornWittenLogCurvatureFactoredProfile r := by positivity
  unfold thetaCuspBornWittenFirstSecondMixedSignedSecondProfile
  dsimp only [r] at hcurvr hdiag ⊢
  nlinarith

/-- Actual second-to-first theta likelihood at the modular seam lies in the much larger
`1/100` cross-absorption chamber. -/
theorem oneHundred_mul_thetaCuspSecondAtomLikelihoodRatio_seam_le_one :
    100 * thetaCuspAtomLikelihoodRatio 2 0 ≤ 1 := by
  let B := thetaCuspLikelihoodCoordinate 0
  have hB : 0 < B := by
    simpa only [B] using thetaCuspLikelihoodCoordinate_pos le_rfl
  have hratio : thetaCuspAtomLikelihoodRatio 2 0 =
      thetaCuspAtomLikelihoodSpectralTerm 2 B := by
    simpa only [B] using
      thetaCuspAtomLikelihoodRatio_eq_spectralTerm_of_coordinate_pos
        (n := 2) (x := 0) hB
  have hsummable := summable_thetaCuspAtomLikelihoodSpectralTerm hB
  have hle : thetaCuspAtomLikelihoodSpectralTerm 2 B ≤
      thetaCuspHigherLikelihoodSpectralResponse B := by
    unfold thetaCuspHigherLikelihoodSpectralResponse
    apply hsummable.le_tsum 0
    intro j hj
    have hgap := thetaCuspLikelihoodGap_pos (n := j + 2) (by omega)
    unfold thetaCuspAtomLikelihoodSpectralTerm
    positivity
  have hsmall : 399 * thetaCuspHigherLikelihoodSpectralResponse B < 1 := by
    simpa only [B] using
      three_hundred_ninety_nine_mul_thetaCuspHigherLikelihoodSpectralResponse_lt_one
        (x := 0) le_rfl
  rw [hratio]
  nlinarith

/-- The physical second-atom seam mixing weight is nonnegative. -/
theorem thetaCuspSecondAtomLikelihoodRatio_seam_nonneg :
    0 ≤ thetaCuspAtomLikelihoodRatio 2 0 := by
  let B := thetaCuspLikelihoodCoordinate 0
  have hB : 0 < B := by
    simpa only [B] using thetaCuspLikelihoodCoordinate_pos le_rfl
  rw [thetaCuspAtomLikelihoodRatio_eq_spectralTerm_of_coordinate_pos
    (n := 2) (x := 0) hB]
  have hgap := thetaCuspLikelihoodGap_pos (n := 2) (by norm_num)
  unfold thetaCuspAtomLikelihoodSpectralTerm
  positivity

/-- Positive physical survivor: the actual first-plus-second atom mixture absorbs its large
indefinite cross entry at the modular seam. -/
theorem thetaCuspFirstSecondPhysicalMixedSignedSecond_seam_pos :
    0 < thetaCuspBornWittenFirstSecondMixedSignedSecondProfile
      (thetaCuspBornWittenWeight 1 0) (thetaCuspAtomLikelihoodRatio 2 0) := by
  have hq1 : thetaCuspBornWittenWeight 1 0 = Real.pi - 3 / 2 := by
    simp [thetaCuspBornWittenWeight, thetaCuspMorseSuperpotential,
      thetaCuspMorseScale]
    ring
  apply thetaCuspBornWittenFirstSecondMixedSignedSecondProfile_pos
  · rw [hq1]
    nlinarith [Real.pi_gt_d2]
  · rw [hq1]
    nlinarith [Real.pi_lt_d4]
  · exact thetaCuspSecondAtomLikelihoodRatio_seam_nonneg
  · exact oneHundred_mul_thetaCuspSecondAtomLikelihoodRatio_seam_le_one

/-- The physical first--second atom cross channel has a large negative signed second entry at the
modular seam. -/
theorem thetaCuspFirstSecondAtomCrossSignedSecond_seam_lt_neg_sixHundredFiftySix :
    thetaCuspBornWittenCrossSignedSecond 1 2 0 < -656 := by
  rw [thetaCuspBornWittenCrossSignedSecond_eq_profile
    (n := 1) (m := 2) (by norm_num) (by norm_num) le_rfl]
  have hq1 : thetaCuspBornWittenWeight 1 0 = Real.pi - 3 / 2 := by
    simp [thetaCuspBornWittenWeight, thetaCuspMorseSuperpotential,
      thetaCuspMorseScale]
    ring
  have hq2 : thetaCuspBornWittenWeight 2 0 =
      4 * (thetaCuspBornWittenWeight 1 0) + 9 / 2 := by
    rw [hq1]
    simp [thetaCuspBornWittenWeight, thetaCuspMorseSuperpotential,
      thetaCuspMorseScale]
    ring
  rw [hq2]
  apply thetaCuspBornWittenCrossSignedSecondProfile_lt_neg_sixHundredFiftySix
  · rw [hq1]
    nlinarith [Real.pi_gt_d2]
  · rw [hq1]
    nlinarith [Real.pi_lt_d4]

/-- Quantitative positive survivor: diagonal channels must absorb more than `656` units of
normalized first--second cross defect at the modular seam. -/
theorem sixHundredFiftySix_lt_neg_thetaCuspFirstSecondAtomCrossSignedSecond_seam :
    656 < -thetaCuspBornWittenCrossSignedSecond 1 2 0 := by
  linarith [thetaCuspFirstSecondAtomCrossSignedSecond_seam_lt_neg_sixHundredFiftySix]

/-- Pair-channel positive semidefiniteness already fails at the signed second entry. -/
theorem not_thetaCuspFirstSecondAtomCrossSignedSecond_seam_nonneg :
    ¬ 0 ≤ thetaCuspBornWittenCrossSignedSecond 1 2 0 := by
  linarith [thetaCuspFirstSecondAtomCrossSignedSecond_seam_lt_neg_sixHundredFiftySix]

end

end RHTower

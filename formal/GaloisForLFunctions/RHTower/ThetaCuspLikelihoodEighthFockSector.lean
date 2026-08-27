import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodEighthStablePairCompensation
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthFockSector

/-!
# Eighth-score higher Fock completion

The complete ordered grade-two sector is already absorbed.  This module sharpens the stable
Gaussian constants and closes every higher even grade.  The key scale-free series is
`sum_{q=4,6,...} q^7 r^(q-1)`: the logarithmic coefficient `1/q` cancels one power from the
eighth-order convex fusion cost `q^8`.  Actual theta activity satisfies `399r<1`, making this
tail smaller than `1/3000` of the one-particle eighth monomial mass.
-/

namespace RHTower

noncomputable section

/-- Sharpened exact exponential edge bound obtained from a degree-fourteen Taylor lower sum. -/
theorem exp_neg_two_pi_lt_one_div_fiveHundred :
    Real.exp (-2 * Real.pi) < (1 : ℝ) / 500 := by
  let z := 2 * Real.pi
  have hz : (157 / 25 : ℝ) < z := by
    dsimp only [z]
    nlinarith [Real.pi_gt_d2]
  have hz0 : 0 ≤ z := by linarith
  have he : (∑ k ∈ Finset.range 15, z ^ k / (k.factorial : ℝ)) ≤ Real.exp z :=
    Real.sum_le_exp_of_nonneg hz0 15
  have htaylor : (500 : ℝ) <
      ∑ k ∈ Finset.range 15, z ^ k / (k.factorial : ℝ) := by
    have hbase : (500 : ℝ) <
        ∑ k ∈ Finset.range 15, (157 / 25 : ℝ) ^ k / (k.factorial : ℝ) := by
      norm_num [Finset.sum_range_succ]
    have hsum :
        (∑ k ∈ Finset.range 15, (157 / 25 : ℝ) ^ k / (k.factorial : ℝ)) ≤
          ∑ k ∈ Finset.range 15, z ^ k / (k.factorial : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      gcongr
    exact hbase.trans_le hsum
  have hexp : 500 < Real.exp z := lt_of_lt_of_le htaylor he
  rw [show -2 * Real.pi = -z by dsimp only [z]; ring, Real.exp_neg]
  simpa only [one_div] using
    (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 500) hexp)

theorem exp_neg_seven_pi_lt_one_div_threeBillion :
    Real.exp (-7 * Real.pi) < (1 : ℝ) / 3000000000 := by
  rw [show -7 * Real.pi = -3 * Real.pi + (-2 * Real.pi) +
      (-2 * Real.pi) by ring, Real.exp_add, Real.exp_add]
  have h3 := thetaCusp_exp_neg_three_pi_lt
  have h2 := exp_neg_two_pi_lt_one_div_fiveHundred
  calc
    (Real.exp (-3 * Real.pi) * Real.exp (-2 * Real.pi)) *
          Real.exp (-2 * Real.pi) <
        ((1 / 12000 : ℝ) * (1 / 500 : ℝ)) * Real.exp (-2 * Real.pi) := by
      gcongr
    _ < ((1 / 12000 : ℝ) * (1 / 500 : ℝ)) * (1 / 500 : ℝ) := by gcongr
    _ = (1 : ℝ) / 3000000000 := by norm_num

theorem exp_neg_eight_pi_lt_one_div_seventyTwoBillion :
    Real.exp (-8 * Real.pi) < (1 : ℝ) / 72000000000 := by
  rw [show -8 * Real.pi = -3 * Real.pi + (-3 * Real.pi) +
      (-2 * Real.pi) by ring, Real.exp_add, Real.exp_add]
  have h3 := thetaCusp_exp_neg_three_pi_lt
  have h2 := exp_neg_two_pi_lt_one_div_fiveHundred
  calc
    (Real.exp (-3 * Real.pi) * Real.exp (-3 * Real.pi)) *
          Real.exp (-2 * Real.pi) <
        ((1 / 12000 : ℝ) * (1 / 12000 : ℝ)) * Real.exp (-2 * Real.pi) := by
      gcongr
    _ < ((1 / 12000 : ℝ) * (1 / 12000 : ℝ)) * (1 / 500 : ℝ) := by gcongr
    _ = (1 : ℝ) / 72000000000 := by norm_num

theorem exp_neg_five_pi_lt_one_div_sixMillion :
    Real.exp (-5 * Real.pi) < (1 : ℝ) / 6000000 := by
  rw [show -5 * Real.pi = -3 * Real.pi + (-2 * Real.pi) by ring,
    Real.exp_add]
  have h3 := thetaCusp_exp_neg_three_pi_lt
  have h2 := exp_neg_two_pi_lt_one_div_fiveHundred
  calc
    Real.exp (-3 * Real.pi) * Real.exp (-2 * Real.pi) <
        (1 / 12000 : ℝ) * (1 / 500 : ℝ) := by gcongr
    _ = (1 : ℝ) / 6000000 := by norm_num

/-- Sharpened stable eighth-weight envelope. -/
theorem thetaCuspReflectionJetTailWeight_eight_tail_le_sharp_geometric (k : ℕ) :
    thetaCuspReflectionJetTailWeight 8 (k + 1) ≤
      (1 / 20 : ℝ) * ((1 / 2000 : ℝ) ^ k) := by
  let n : ℕ := k + 3
  have hpow := thetaCusp_nat_add_three_pow_twenty_le k
  have hexp := thetaCusp_tail_exponent_seven_add_three_le_eighth k
  have hbase : Real.exp (-8 * Real.pi) ≤ (1 : ℝ) / 72000000000 :=
    exp_neg_eight_pi_lt_one_div_seventyTwoBillion.le
  have hratio : 1048576 * Real.exp (-7 * Real.pi) ≤ (1 / 2000 : ℝ) := by
    nlinarith [exp_neg_seven_pi_lt_one_div_threeBillion]
  have hn : (3 : ℝ) ≤ n := by
    exact_mod_cast (by dsimp only [n]; omega : 3 ≤ n)
  have hd : 0 ≤ (n : ℝ) ^ 2 - 1 := by nlinarith
  have hdle : ((n : ℝ) ^ 2 - 1) ^ 8 ≤ ((n : ℝ) ^ 2) ^ 8 :=
    pow_le_pow_left₀ hd (by linarith) 8
  unfold thetaCuspReflectionJetTailWeight
  dsimp only [n]
  calc
    (n : ℝ) ^ 4 * ((n : ℝ) ^ 2 - 1) ^ 8 *
          Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1)) ≤
        (n : ℝ) ^ 4 * ((n : ℝ) ^ 2) ^ 8 *
          Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1)) := by gcongr
    _ = (n : ℝ) ^ 20 * Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1)) := by
      rw [← pow_mul, ← pow_add]
    _ ≤ (3486784401 * (1048576 : ℝ) ^ k) *
        (Real.exp (-8 * Real.pi) * (Real.exp (-7 * Real.pi)) ^ k) := by gcongr
    _ = 3486784401 * Real.exp (-8 * Real.pi) *
        (1048576 * Real.exp (-7 * Real.pi)) ^ k := by ring
    _ ≤ 3486784401 * ((1 : ℝ) / 72000000000) *
        ((1 / 2000 : ℝ) ^ k) := by gcongr
    _ ≤ (1 / 20 : ℝ) * ((1 / 2000 : ℝ) ^ k) := by
      gcongr
      norm_num

/-- Sharp complete stable eighth moment. -/
theorem tsum_thetaCuspReflectionJetTailWeight_eight_tail_le_sharp :
    (∑' k : ℕ, thetaCuspReflectionJetTailWeight 8 (k + 1)) ≤
      (100 / 1999 : ℝ) := by
  have hs : Summable (fun k : ℕ => thetaCuspReflectionJetTailWeight 8 (k + 1)) :=
    (summable_nat_add_iff 1).2 (summable_thetaCuspReflectionJetTailWeight 8)
  have hgeo : Summable (fun k : ℕ =>
      (1 / 20 : ℝ) * ((1 / 2000 : ℝ) ^ k)) :=
    (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 2000 : ℝ)‖ < 1)).mul_left _
  calc
    (∑' k : ℕ, thetaCuspReflectionJetTailWeight 8 (k + 1)) ≤
        ∑' k : ℕ, (1 / 20 : ℝ) * ((1 / 2000 : ℝ) ^ k) :=
      Summable.tsum_le_tsum
        thetaCuspReflectionJetTailWeight_eight_tail_le_sharp_geometric hs hgeo
    _ = (1 / 20 : ℝ) * (1 - (1 / 2000 : ℝ))⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    _ = (100 / 1999 : ℝ) := by norm_num

/-- Sharpened gap-shifted stable activity envelope. -/
theorem thetaCuspLikelihoodStableShiftedActivityTerm_le_sharp_geometric (k : ℕ) :
    ((k + 3 : ℕ) : ℝ) ^ 4 *
        Real.exp (-Real.pi * (thetaCuspLikelihoodGap (k + 3) - 3)) ≤
      (1 / 50000 : ℝ) * ((1 / 1000000 : ℝ) ^ k) := by
  have hpow := thetaCusp_nat_add_three_pow_four_le k
  have hexp := thetaCusp_shifted_tail_exponent_seven_add_three_le k
  have hbase : Real.exp (-5 * Real.pi) ≤ (1 : ℝ) / 6000000 :=
    exp_neg_five_pi_lt_one_div_sixMillion.le
  have hratio : 16 * Real.exp (-7 * Real.pi) ≤ (1 / 1000000 : ℝ) := by
    nlinarith [exp_neg_seven_pi_lt_one_div_threeBillion]
  unfold thetaCuspLikelihoodGap
  calc
    ((k + 3 : ℕ) : ℝ) ^ 4 *
          Real.exp (-Real.pi * ((((k + 3 : ℕ) : ℝ) ^ 2 - 1) - 3)) ≤
        (81 * (16 : ℝ) ^ k) *
          (Real.exp (-5 * Real.pi) * (Real.exp (-7 * Real.pi)) ^ k) := by gcongr
    _ = 81 * Real.exp (-5 * Real.pi) *
        (16 * Real.exp (-7 * Real.pi)) ^ k := by ring
    _ ≤ 81 * ((1 : ℝ) / 6000000) * ((1 / 1000000 : ℝ) ^ k) := by gcongr
    _ ≤ (1 / 50000 : ℝ) * ((1 / 1000000 : ℝ) ^ k) := by
      gcongr
      norm_num

theorem tsum_thetaCuspLikelihoodStableShiftedActivity_pi_le_sharp :
    (∑' k : ℕ, ((k + 3 : ℕ) : ℝ) ^ 4 *
        Real.exp (-Real.pi * (thetaCuspLikelihoodGap (k + 3) - 3))) ≤
      (20 / 999999 : ℝ) := by
  have hgeo : Summable (fun k : ℕ =>
      (1 / 50000 : ℝ) * ((1 / 1000000 : ℝ) ^ k)) :=
    (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 1000000 : ℝ)‖ < 1)).mul_left _
  have hnonneg : ∀ k : ℕ, 0 ≤ ((k + 3 : ℕ) : ℝ) ^ 4 *
      Real.exp (-Real.pi * (thetaCuspLikelihoodGap (k + 3) - 3)) := by
    intro k
    positivity
  have hs := Summable.of_nonneg_of_le hnonneg
    thetaCuspLikelihoodStableShiftedActivityTerm_le_sharp_geometric hgeo
  calc
    (∑' k : ℕ, ((k + 3 : ℕ) : ℝ) ^ 4 *
        Real.exp (-Real.pi * (thetaCuspLikelihoodGap (k + 3) - 3))) ≤
        ∑' k : ℕ, (1 / 50000 : ℝ) * ((1 / 1000000 : ℝ) ^ k) :=
      Summable.tsum_le_tsum
        thetaCuspLikelihoodStableShiftedActivityTerm_le_sharp_geometric hs hgeo
    _ = (1 / 50000 : ℝ) * (1 - (1 / 1000000 : ℝ))⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    _ = (20 / 999999 : ℝ) := by norm_num

theorem thetaCuspLikelihoodStableEighthTail_le_sharp
    {A : ℝ} (hA : Real.pi ≤ A) :
    thetaCuspLikelihoodStableEighthTail A ≤ (100 / 1999 : ℝ) := by
  have hs := summable_thetaCuspLikelihoodStableEighthTail hA
  have hw : Summable (fun k : ℕ =>
      thetaCuspReflectionJetTailWeight 8 (k + 1)) :=
    (summable_nat_add_iff 1).2 (summable_thetaCuspReflectionJetTailWeight 8)
  unfold thetaCuspLikelihoodStableEighthTail
  exact (Summable.tsum_le_tsum
    (thetaCuspLikelihoodStableEighthTailTerm_le_pi hA) hs hw).trans
      tsum_thetaCuspReflectionJetTailWeight_eight_tail_le_sharp

theorem thetaCuspLikelihoodStableShiftedActivity_le_sharp
    {A : ℝ} (hA : Real.pi ≤ A) :
    thetaCuspLikelihoodStableShiftedActivity A ≤ (20 / 999999 : ℝ) := by
  have hs := summable_thetaCuspLikelihoodStableShiftedActivity hA
  have hgeo : Summable (fun k : ℕ =>
      (1 / 50000 : ℝ) * ((1 / 1000000 : ℝ) ^ k)) :=
    (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 1000000 : ℝ)‖ < 1)).mul_left _
  have hpiNonneg : ∀ k : ℕ, 0 ≤ ((k + 3 : ℕ) : ℝ) ^ 4 *
      Real.exp (-Real.pi * (thetaCuspLikelihoodGap (k + 3) - 3)) := by
    intro k
    positivity
  have hpi := Summable.of_nonneg_of_le hpiNonneg
    thetaCuspLikelihoodStableShiftedActivityTerm_le_sharp_geometric hgeo
  unfold thetaCuspLikelihoodStableShiftedActivity
  have hfirst := Summable.tsum_le_tsum
    (thetaCuspLikelihoodStableShiftedActivityTerm_le_pi hA) hs hpi
  exact hfirst.trans tsum_thetaCuspLikelihoodStableShiftedActivity_pi_le_sharp

/-- Sharpened ordered mixed-pair tail bound. -/
theorem thetaCuspLikelihoodDominantStablePairEighthTail_le_sharp
    {A B : ℝ} (hA : Real.pi ≤ A) (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodDominantStablePairEighthTail A B ≤
      (187200 / 1999 : ℝ) * A ^ 8 * Real.exp (-(3 * A)) := by
  have hs := summable_thetaCuspLikelihoodDominantStablePairEighthScoreMass hA hBA
  have hw := (summable_thetaCuspLikelihoodStableEighthTail hA).mul_left
    (1872 * A ^ 8 * Real.exp (-(3 * A)))
  have htail := thetaCuspLikelihoodStableEighthTail_le_sharp hA
  unfold thetaCuspLikelihoodDominantStablePairEighthTail
  calc
    (∑' k : ℕ, thetaCuspLikelihoodAtomPairEighthScoreMass 2 (k + 3) A B) ≤
        ∑' k : ℕ, 1872 * A ^ 8 * Real.exp (-(3 * A)) *
          (((k + 3 : ℕ) : ℝ) ^ 4 * thetaCuspLikelihoodGap (k + 3) ^ 8 *
            Real.exp (-(A * thetaCuspLikelihoodGap (k + 3)))) :=
      Summable.tsum_le_tsum
        (fun k => thetaCuspLikelihoodDominantStablePairEighthScoreMass_le k hA hBA) hs hw
    _ = (1872 * A ^ 8 * Real.exp (-(3 * A))) *
        thetaCuspLikelihoodStableEighthTail A := by
      unfold thetaCuspLikelihoodStableEighthTail
      rw [tsum_mul_left]
    _ ≤ (1872 * A ^ 8 * Real.exp (-(3 * A))) * (100 / 1999 : ℝ) := by
      gcongr
    _ = (187200 / 1999 : ℝ) * A ^ 8 * Real.exp (-(3 * A)) := by ring

/-- Sharpened complete non-dominant grade-two bound. -/
theorem thetaCuspLikelihoodNonDominantPairEighthTail_le_sharp
    {A B : ℝ} (hA : Real.pi ≤ A) (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodNonDominantPairEighthTail A B ≤
      (376399 / 1999 : ℝ) * A ^ 8 * Real.exp (-(3 * A)) := by
  have hmixed := thetaCuspLikelihoodDominantStablePairEighthTail_le_sharp hA hBA
  have hstable := thetaCuspLikelihoodStableStablePairEighthTail_le hA hBA
  unfold thetaCuspLikelihoodNonDominantPairEighthTail
  nlinarith

/-! ### Complete one-particle eighth-monomial budget -/

/-- Stable rays cost at most three copies of their point eighth monomial. -/
theorem thetaCuspLikelihoodEighthMonomialRayTransform_le_three_mul_pow_eight
    {r z : ℝ} (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hz : 24 ≤ z) :
    thetaCuspLikelihoodEighthMonomialRayTransform r z ≤ 3 * z ^ 8 := by
  have hz0 : 0 ≤ z := by linarith
  have hr1 : r ^ 1 ≤ (2 : ℝ) ^ 1 := pow_le_pow_left₀ hr0 hr2 1
  have hr2' : r ^ 2 ≤ (2 : ℝ) ^ 2 := pow_le_pow_left₀ hr0 hr2 2
  have hr3 : r ^ 3 ≤ (2 : ℝ) ^ 3 := pow_le_pow_left₀ hr0 hr2 3
  have hr4 : r ^ 4 ≤ (2 : ℝ) ^ 4 := pow_le_pow_left₀ hr0 hr2 4
  have hr5 : r ^ 5 ≤ (2 : ℝ) ^ 5 := pow_le_pow_left₀ hr0 hr2 5
  have hr6 : r ^ 6 ≤ (2 : ℝ) ^ 6 := pow_le_pow_left₀ hr0 hr2 6
  have hr7 : r ^ 7 ≤ (2 : ℝ) ^ 7 := pow_le_pow_left₀ hr0 hr2 7
  have hr8 : r ^ 8 ≤ (2 : ℝ) ^ 8 := pow_le_pow_left₀ hr0 hr2 8
  have hmono : thetaCuspLikelihoodEighthMonomialRayTransform r z ≤
      thetaCuspLikelihoodEighthMonomialRayTransform 2 z := by
    unfold thetaCuspLikelihoodEighthMonomialRayTransform
    gcongr
  let s := z - 24
  have hs : 0 ≤ s := by dsimp only [s]; linarith
  have hend : thetaCuspLikelihoodEighthMonomialRayTransform 2 z ≤ 3 * z ^ 8 := by
    unfold thetaCuspLikelihoodEighthMonomialRayTransform
    rw [show z = 24 + s by dsimp only [s]; ring]
    ring_nf
    nlinarith [sq_nonneg s, sq_nonneg (s ^ 2), sq_nonneg (s ^ 3), sq_nonneg (s ^ 4)]
  exact hmono.trans hend

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- Coupling `r=A/(A-3/2)` to the dominant support `z=3A` gives a factor-sixteen ray bound. -/
theorem thetaCuspLikelihoodDominantEighthMonomialRayTransform_le
    {A : ℝ} (hA : (157 / 50 : ℝ) ≤ A) :
    thetaCuspLikelihoodEighthMonomialRayTransform
        (A / (A - 3 / 2)) (3 * A) ≤ 16 * (3 * A) ^ 8 := by
  let B := A - 3 / 2
  have hB : 0 < B := by dsimp only [B]; linarith
  let s := A - 157 / 50
  have hs : 0 ≤ s := by dsimp only [s]; linarith
  have hmul : 0 ≤ B ^ 8 *
      (16 * (3 * A) ^ 8 -
        thetaCuspLikelihoodEighthMonomialRayTransform (A / B) (3 * A)) := by
    unfold thetaCuspLikelihoodEighthMonomialRayTransform
    field_simp [hB.ne']
    dsimp only [B]
    rw [show A = 157 / 50 + s by dsimp only [s]; ring]
    ring_nf
    positivity
  have hdiff : 0 ≤ 16 * (3 * A) ^ 8 -
      thetaCuspLikelihoodEighthMonomialRayTransform (A / B) (3 * A) :=
    nonneg_of_mul_nonneg_left (by simpa only [mul_comm] using hmul) (pow_pos hB 8)
  dsimp only [B] at hdiff
  linarith

/-- Dominant atom plus its continuous ray has an explicit eighth-monomial budget. -/
theorem thetaCuspLikelihoodDominantAtomEighthMonomialMass_le
    {A B : ℝ} (hA : (157 / 50 : ℝ) ≤ A) (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodAtomEighthMonomialMass 2 A B ≤
      1259712 * A ^ 8 * Real.exp (-(3 * A)) := by
  have hB : 0 < B := by rw [hBA]; linarith
  rw [thetaCuspLikelihoodAtomEighthMonomialMass_eq 2 (by norm_num) A hB]
  norm_num [thetaCuspLikelihoodGap, thetaCuspLikelihoodAtomWeight,
    thetaCuspLikelihoodRayWeight]
  have hray : thetaCuspLikelihoodEighthMonomialRayTransform
      (A / (A - 3 / 2)) (3 * A) ≤ 16 * (3 * A) ^ 8 :=
    thetaCuspLikelihoodDominantEighthMonomialRayTransform_le hA
  have hB0 : 0 < A - 3 / 2 := by linarith
  have hcoef : 18 / (A - 3 / 2) ≤ (11 : ℝ) := by
    apply (div_le_iff₀ hB0).2
    nlinarith
  have hray0 : 0 ≤ thetaCuspLikelihoodEighthMonomialRayTransform
      (A / (A - 3 / 2)) (3 * A) := by
    unfold thetaCuspLikelihoodEighthMonomialRayTransform
    positivity
  rw [hBA]
  have hexp : Real.exp (-(9 / 2 : ℝ)) * Real.exp (-((A - 3 / 2) * 3)) =
      Real.exp (-(3 * A)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp (-(9 / 2 : ℝ)) * 16 *
          ((A * 3) ^ 8 * Real.exp (-((A - 3 / 2) * 3))) +
        Real.exp (-(9 / 2 : ℝ)) * (3 / 2) * 4 * 3 *
          (Real.exp (-((A - 3 / 2) * 3)) / (A - 3 / 2) *
            thetaCuspLikelihoodEighthMonomialRayTransform
              (A / (A - 3 / 2)) (A * 3)) =
        Real.exp (-(3 * A)) *
          (16 * (3 * A) ^ 8 + (18 / (A - 3 / 2)) *
            thetaCuspLikelihoodEighthMonomialRayTransform
              (A / (A - 3 / 2)) (3 * A)) := by rw [← hexp]; ring
    _ ≤ Real.exp (-(3 * A)) *
        (16 * (3 * A) ^ 8 + 11 * (16 * (3 * A) ^ 8)) := by gcongr
    _ = 1259712 * A ^ 8 * Real.exp (-(3 * A)) := by ring

/-- Every stable atom-ray is bounded by four copies of its point Gaussian eighth weight. -/
theorem thetaCuspLikelihoodStableAtomEighthMonomialMass_le
    {n : ℕ} (hn : 3 ≤ n) {A B : ℝ} (hA : Real.pi ≤ A)
    (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodAtomEighthMonomialMass n A B ≤
      4 * A ^ 8 * (n : ℝ) ^ 4 * thetaCuspLikelihoodGap n ^ 8 *
        Real.exp (-(A * thetaCuspLikelihoodGap n)) := by
  have hApi : (157 / 50 : ℝ) ≤ A := by nlinarith [Real.pi_gt_d2]
  have hB : 0 < B := by rw [hBA]; linarith
  have hB32 : (3 / 2 : ℝ) ≤ B := by rw [hBA]; linarith
  have hA0 : 0 ≤ A := by linarith [Real.pi_pos]
  have hr0 : 0 ≤ A / B := div_nonneg hA0 hB.le
  have hr2 : A / B ≤ 2 := by
    apply (div_le_iff₀ hB).2
    rw [hBA]
    linarith
  let d := thetaCuspLikelihoodGap n
  have hz : 24 ≤ A * d := by
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hd : 8 ≤ d := by
      dsimp only [d, thetaCuspLikelihoodGap]
      nlinarith
    nlinarith
  have hray : thetaCuspLikelihoodEighthMonomialRayTransform (A / B) (A * d) ≤
      3 * (A * d) ^ 8 :=
    thetaCuspLikelihoodEighthMonomialRayTransform_le_three_mul_pow_eight hr0 hr2 hz
  have hu := thetaCuspLikelihood_normalizedRayCoefficient_le_pow_four
    (show 2 ≤ n by omega) hB32
  rw [thetaCuspLikelihoodAtomEighthMonomialMass_eq n (by omega) A hB]
  unfold thetaCuspLikelihoodAtomWeight thetaCuspLikelihoodRayWeight
  change Real.exp (-(3 / 2) * d) * (n : ℝ) ^ 4 *
        ((A * d) ^ 8 * Real.exp (-(B * d))) +
      (Real.exp (-(3 / 2) * d) * (3 / 2) * (n : ℝ) ^ 2 * d) *
        (Real.exp (-(B * d)) / B *
          thetaCuspLikelihoodEighthMonomialRayTransform (A / B) (A * d)) ≤
    4 * A ^ 8 * (n : ℝ) ^ 4 * d ^ 8 * Real.exp (-(A * d))
  have hexp : Real.exp (-(3 / 2) * d) * Real.exp (-(B * d)) =
      Real.exp (-(A * d)) := by
    rw [← Real.exp_add, hBA]
    congr 1
    ring
  rw [show
      Real.exp (-(3 / 2) * d) * (n : ℝ) ^ 4 *
          ((A * d) ^ 8 * Real.exp (-(B * d))) +
        (Real.exp (-(3 / 2) * d) * (3 / 2) * (n : ℝ) ^ 2 * d) *
          (Real.exp (-(B * d)) / B *
            thetaCuspLikelihoodEighthMonomialRayTransform (A / B) (A * d)) =
      Real.exp (-(A * d)) *
        ((n : ℝ) ^ 4 * (A * d) ^ 8 +
          ((3 / 2) * (n : ℝ) ^ 2 * d / B) *
            thetaCuspLikelihoodEighthMonomialRayTransform (A / B) (A * d)) by
        rw [← hexp]; ring]
  have hray0 : 0 ≤ thetaCuspLikelihoodEighthMonomialRayTransform (A / B) (A * d) := by
    unfold thetaCuspLikelihoodEighthMonomialRayTransform
    positivity
  calc
    Real.exp (-(A * d)) *
          ((n : ℝ) ^ 4 * (A * d) ^ 8 +
            ((3 / 2) * (n : ℝ) ^ 2 * d / B) *
              thetaCuspLikelihoodEighthMonomialRayTransform (A / B) (A * d)) ≤
        Real.exp (-(A * d)) *
          ((n : ℝ) ^ 4 * (A * d) ^ 8 + (n : ℝ) ^ 4 * (3 * (A * d) ^ 8)) := by
            gcongr
    _ = 4 * A ^ 8 * (n : ℝ) ^ 4 * d ^ 8 * Real.exp (-(A * d)) := by ring

/-- Stable order-eight Gaussian tail after extracting the dominant exponential `exp (-3A)`. -/
def thetaCuspLikelihoodStableShiftedEighthTail (A : ℝ) : ℝ :=
  ∑' k : ℕ, ((k + 3 : ℕ) : ℝ) ^ 4 * thetaCuspLikelihoodGap (k + 3) ^ 8 *
    Real.exp (-(A * (thetaCuspLikelihoodGap (k + 3) - 3)))

/-- The shifted stable eighth weight has a `582 · 2000⁻ᵏ` envelope. -/
theorem thetaCuspLikelihoodStableShiftedEighthTailTerm_le_geometric (k : ℕ) :
    ((k + 3 : ℕ) : ℝ) ^ 4 * thetaCuspLikelihoodGap (k + 3) ^ 8 *
        Real.exp (-Real.pi * (thetaCuspLikelihoodGap (k + 3) - 3)) ≤
      582 * ((1 / 2000 : ℝ) ^ k) := by
  let n : ℕ := k + 3
  have hpow := thetaCusp_nat_add_three_pow_twenty_le k
  have hexp := thetaCusp_shifted_tail_exponent_seven_add_three_le k
  have hbase : Real.exp (-5 * Real.pi) ≤ (1 : ℝ) / 6000000 :=
    exp_neg_five_pi_lt_one_div_sixMillion.le
  have hratio : 1048576 * Real.exp (-7 * Real.pi) ≤ (1 / 2000 : ℝ) := by
    nlinarith [exp_neg_seven_pi_lt_one_div_threeBillion]
  have hn : (3 : ℝ) ≤ n := by
    exact_mod_cast (by dsimp only [n]; omega : 3 ≤ n)
  have hd : 0 ≤ (n : ℝ) ^ 2 - 1 := by nlinarith
  have hdle : ((n : ℝ) ^ 2 - 1) ^ 8 ≤ ((n : ℝ) ^ 2) ^ 8 :=
    pow_le_pow_left₀ hd (by linarith) 8
  unfold thetaCuspLikelihoodGap
  change (n : ℝ) ^ 4 * ((n : ℝ) ^ 2 - 1) ^ 8 *
      Real.exp (-Real.pi * (((n : ℝ) ^ 2 - 1) - 3)) ≤
    582 * ((1 / 2000 : ℝ) ^ k)
  calc
    (n : ℝ) ^ 4 * ((n : ℝ) ^ 2 - 1) ^ 8 *
          Real.exp (-Real.pi * (((n : ℝ) ^ 2 - 1) - 3)) ≤
        (n : ℝ) ^ 4 * ((n : ℝ) ^ 2) ^ 8 *
          Real.exp (-Real.pi * (((n : ℝ) ^ 2 - 1) - 3)) := by gcongr
    _ = (n : ℝ) ^ 20 * Real.exp (-Real.pi * (((n : ℝ) ^ 2 - 1) - 3)) := by
      rw [← pow_mul, ← pow_add]
    _ ≤ (3486784401 * (1048576 : ℝ) ^ k) *
        (Real.exp (-5 * Real.pi) * (Real.exp (-7 * Real.pi)) ^ k) := by gcongr
    _ = 3486784401 * Real.exp (-5 * Real.pi) *
        (1048576 * Real.exp (-7 * Real.pi)) ^ k := by ring
    _ ≤ 3486784401 * ((1 : ℝ) / 6000000) * ((1 / 2000 : ℝ) ^ k) := by gcongr
    _ ≤ 582 * ((1 / 2000 : ℝ) ^ k) := by
      gcongr
      norm_num

theorem thetaCuspLikelihoodStableShiftedEighthTailTerm_le_pi
    {A : ℝ} (hA : Real.pi ≤ A) (k : ℕ) :
    ((k + 3 : ℕ) : ℝ) ^ 4 * thetaCuspLikelihoodGap (k + 3) ^ 8 *
        Real.exp (-(A * (thetaCuspLikelihoodGap (k + 3) - 3))) ≤
      ((k + 3 : ℕ) : ℝ) ^ 4 * thetaCuspLikelihoodGap (k + 3) ^ 8 *
        Real.exp (-Real.pi * (thetaCuspLikelihoodGap (k + 3) - 3)) := by
  have hgap : 0 ≤ thetaCuspLikelihoodGap (k + 3) - 3 := by
    have hnR : (3 : ℝ) ≤ (k + 3 : ℕ) := by exact_mod_cast (by omega : 3 ≤ k + 3)
    unfold thetaCuspLikelihoodGap
    nlinarith
  have hexponent :
      -(A * (thetaCuspLikelihoodGap (k + 3) - 3)) ≤
        -Real.pi * (thetaCuspLikelihoodGap (k + 3) - 3) := by
    nlinarith
  gcongr

theorem summable_thetaCuspLikelihoodStableShiftedEighthTail
    {A : ℝ} (hA : Real.pi ≤ A) :
    Summable (fun k : ℕ => ((k + 3 : ℕ) : ℝ) ^ 4 *
      thetaCuspLikelihoodGap (k + 3) ^ 8 *
      Real.exp (-(A * (thetaCuspLikelihoodGap (k + 3) - 3)))) := by
  have hgeo : Summable (fun k : ℕ => 582 * ((1 / 2000 : ℝ) ^ k)) :=
    (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 2000 : ℝ)‖ < 1)).mul_left _
  have hpiNonneg : ∀ k : ℕ, 0 ≤ ((k + 3 : ℕ) : ℝ) ^ 4 *
      thetaCuspLikelihoodGap (k + 3) ^ 8 *
      Real.exp (-Real.pi * (thetaCuspLikelihoodGap (k + 3) - 3)) := by
    intro k
    positivity
  have hpi := Summable.of_nonneg_of_le hpiNonneg
    thetaCuspLikelihoodStableShiftedEighthTailTerm_le_geometric hgeo
  apply Summable.of_norm_bounded hpi
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact thetaCuspLikelihoodStableShiftedEighthTailTerm_le_pi hA k
  · positivity

/-- The complete shifted stable eighth tail is below `583`. -/
theorem thetaCuspLikelihoodStableShiftedEighthTail_le
    {A : ℝ} (hA : Real.pi ≤ A) :
    thetaCuspLikelihoodStableShiftedEighthTail A ≤ 583 := by
  have hs := summable_thetaCuspLikelihoodStableShiftedEighthTail hA
  have hgeo : Summable (fun k : ℕ => 582 * ((1 / 2000 : ℝ) ^ k)) :=
    (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 2000 : ℝ)‖ < 1)).mul_left _
  unfold thetaCuspLikelihoodStableShiftedEighthTail
  calc
    (∑' k : ℕ, ((k + 3 : ℕ) : ℝ) ^ 4 * thetaCuspLikelihoodGap (k + 3) ^ 8 *
        Real.exp (-(A * (thetaCuspLikelihoodGap (k + 3) - 3)))) ≤
        ∑' k : ℕ, ((k + 3 : ℕ) : ℝ) ^ 4 * thetaCuspLikelihoodGap (k + 3) ^ 8 *
          Real.exp (-Real.pi * (thetaCuspLikelihoodGap (k + 3) - 3)) :=
      Summable.tsum_le_tsum
        (thetaCuspLikelihoodStableShiftedEighthTailTerm_le_pi hA) hs
        (Summable.of_nonneg_of_le (fun k => by positivity)
          thetaCuspLikelihoodStableShiftedEighthTailTerm_le_geometric hgeo)
    _ ≤ ∑' k : ℕ, 582 * ((1 / 2000 : ℝ) ^ k) :=
      Summable.tsum_le_tsum
        thetaCuspLikelihoodStableShiftedEighthTailTerm_le_geometric
        (Summable.of_nonneg_of_le (fun k => by positivity)
          thetaCuspLikelihoodStableShiftedEighthTailTerm_le_geometric hgeo) hgeo
    _ = 582 * (1 - (1 / 2000 : ℝ))⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    _ ≤ 583 := by norm_num

/-- Complete stable one-particle monomial mass after the dominant atom. -/
def thetaCuspLikelihoodStableEighthMonomialMassTail (A B : ℝ) : ℝ :=
  ∑' k : ℕ, thetaCuspLikelihoodAtomEighthMonomialMass (k + 3) A B

theorem thetaCuspLikelihoodStableEighthMonomialMassTail_le
    {A B : ℝ} (hA : Real.pi ≤ A) (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodStableEighthMonomialMassTail A B ≤
      2332 * A ^ 8 * Real.exp (-(3 * A)) := by
  have hApi : (157 / 50 : ℝ) ≤ A := by nlinarith [Real.pi_gt_d2]
  have hB : 0 < B := by rw [hBA]; linarith
  have hsAll := summable_thetaCuspLikelihoodAtomEighthMonomialMass A hB
  have hs : Summable (fun k : ℕ =>
      thetaCuspLikelihoodAtomEighthMonomialMass (k + 3) A B) := by
    simpa only [Nat.add_assoc] using
      (summable_nat_add_iff 1).2 hsAll
  have hshift := summable_thetaCuspLikelihoodStableShiftedEighthTail hA
  have hmajor := hshift.mul_left (4 * A ^ 8 * Real.exp (-(3 * A)))
  have hpoint : ∀ k : ℕ,
      thetaCuspLikelihoodAtomEighthMonomialMass (k + 3) A B ≤
        4 * A ^ 8 * Real.exp (-(3 * A)) *
          (((k + 3 : ℕ) : ℝ) ^ 4 * thetaCuspLikelihoodGap (k + 3) ^ 8 *
            Real.exp (-(A * (thetaCuspLikelihoodGap (k + 3) - 3)))) := by
    intro k
    have hm := thetaCuspLikelihoodStableAtomEighthMonomialMass_le
      (n := k + 3) (by omega) hA hBA
    have hexp : Real.exp (-(A * thetaCuspLikelihoodGap (k + 3))) =
        Real.exp (-(3 * A)) *
          Real.exp (-(A * (thetaCuspLikelihoodGap (k + 3) - 3))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp] at hm
    nlinarith
  have htail := thetaCuspLikelihoodStableShiftedEighthTail_le hA
  unfold thetaCuspLikelihoodStableEighthMonomialMassTail
  calc
    (∑' k : ℕ, thetaCuspLikelihoodAtomEighthMonomialMass (k + 3) A B) ≤
        ∑' k : ℕ, 4 * A ^ 8 * Real.exp (-(3 * A)) *
          (((k + 3 : ℕ) : ℝ) ^ 4 * thetaCuspLikelihoodGap (k + 3) ^ 8 *
            Real.exp (-(A * (thetaCuspLikelihoodGap (k + 3) - 3)))) :=
      Summable.tsum_le_tsum hpoint hs hmajor
    _ = (4 * A ^ 8 * Real.exp (-(3 * A))) *
        thetaCuspLikelihoodStableShiftedEighthTail A := by
      unfold thetaCuspLikelihoodStableShiftedEighthTail
      rw [tsum_mul_left]
    _ ≤ (4 * A ^ 8 * Real.exp (-(3 * A))) * 583 := by gcongr
    _ = 2332 * A ^ 8 * Real.exp (-(3 * A)) := by ring

/-- Full one-particle eighth monomial mass fits `1.3·10⁶` dominant exponential units. -/
theorem tsum_thetaCuspLikelihoodAtomEighthMonomialMass_le
    {A B : ℝ} (hA : Real.pi ≤ A) (hBA : B = A - 3 / 2) :
    (∑' k : ℕ, thetaCuspLikelihoodAtomEighthMonomialMass (k + 2) A B) ≤
      1300000 * A ^ 8 * Real.exp (-(3 * A)) := by
  have hApi : (157 / 50 : ℝ) ≤ A := by nlinarith [Real.pi_gt_d2]
  have hB : 0 < B := by rw [hBA]; linarith
  have hs := summable_thetaCuspLikelihoodAtomEighthMonomialMass A hB
  have hdom := thetaCuspLikelihoodDominantAtomEighthMonomialMass_le hApi hBA
  have hstable := thetaCuspLikelihoodStableEighthMonomialMassTail_le hA hBA
  have hscale0 : 0 ≤ A ^ 8 * Real.exp (-(3 * A)) := by positivity
  rw [hs.tsum_eq_zero_add]
  change thetaCuspLikelihoodAtomEighthMonomialMass 2 A B +
      thetaCuspLikelihoodStableEighthMonomialMassTail A B ≤ _
  nlinarith

/-! ### Infinite higher-even Fock completion -/

/-- Scale-free logarithmic loss from even grades `4,6,8,…` at order eight. -/
def thetaCuspLikelihoodEighthHigherEvenSectorTail (r : ℝ) : ℝ :=
  ∑' m : ℕ, (((2 * (m + 2) : ℕ) : ℝ) ^ 7) * r ^ (2 * (m + 2) - 1)

private theorem even_shift_pow_seven_le_twelve_pow (m : ℕ) :
    (((2 * (m + 2) : ℕ) : ℝ) ^ 7) ≤
      (12 : ℝ) ^ (2 * (m + 2)) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      let k : ℕ := 2 * (m + 2)
      have hk : (4 : ℝ) ≤ k := by
        dsimp only [k]
        push_cast
        nlinarith [show (0 : ℝ) ≤ m by positivity]
      have hk0 : (0 : ℝ) ≤ k := by positivity
      have hstep : ((k : ℝ) + 2) ≤ (3 / 2 : ℝ) * k := by nlinarith
      have hpow := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ k + 2) hstep 7
      have hcoeff : (3 / 2 : ℝ) ^ 7 < 144 := by norm_num
      have hnonneg : 0 ≤ (k : ℝ) ^ 7 := pow_nonneg hk0 7
      have hscaled : (((k : ℝ) + 2) ^ 7) ≤ 144 * (k : ℝ) ^ 7 := by
        calc
          ((k : ℝ) + 2) ^ 7 ≤ ((3 / 2 : ℝ) * k) ^ 7 := hpow
          _ = (3 / 2 : ℝ) ^ 7 * (k : ℝ) ^ 7 := by ring
          _ ≤ 144 * (k : ℝ) ^ 7 :=
            mul_le_mul_of_nonneg_right hcoeff.le hnonneg
      have hind : ((k : ℝ) ^ 7) ≤ (12 : ℝ) ^ k := by
        simpa only [k, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using ih
      have hmul := mul_le_mul_of_nonneg_left hind (by norm_num : (0 : ℝ) ≤ 144)
      change ((((2 * (m + 1 + 2) : ℕ) : ℝ) ^ 7) ≤
        (12 : ℝ) ^ (2 * (m + 1 + 2)))
      rw [show 2 * (m + 1 + 2) = k + 2 by omega]
      push_cast
      calc
        ((k : ℝ) + 2) ^ 7 ≤ 144 * (k : ℝ) ^ 7 := hscaled
        _ ≤ 144 * (12 : ℝ) ^ k := hmul
        _ = (12 : ℝ) ^ (k + 2) := by rw [pow_add]; norm_num; ring

/-- Higher even grades admit one closed geometric majorant. -/
theorem summable_thetaCuspLikelihoodEighthHigherEvenSectorTail_and_le
    {r : ℝ} (hr0 : 0 ≤ r) (hr : 399 * r < 1) :
    Summable (fun m : ℕ =>
      (((2 * (m + 2) : ℕ) : ℝ) ^ 7) * r ^ (2 * (m + 2) - 1)) ∧
    thetaCuspLikelihoodEighthHigherEvenSectorTail r ≤
      20736 * r ^ 3 * (1 - 144 * r ^ 2)⁻¹ := by
  have hr1 : r < 1 / 399 := by nlinarith
  have hq0 : 0 ≤ 144 * r ^ 2 := by positivity
  have hq1 : 144 * r ^ 2 < 1 := by
    have hrSq := pow_lt_pow_left₀ hr1 hr0 (by norm_num : 2 ≠ 0)
    nlinarith
  have hqNorm : ‖144 * r ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hmajorSummable : Summable (fun m : ℕ =>
      20736 * r ^ 3 * (144 * r ^ 2) ^ m) :=
    (summable_geometric_of_norm_lt_one hqNorm).mul_left _
  have hmajor : ∀ m : ℕ,
      (((2 * (m + 2) : ℕ) : ℝ) ^ 7) * r ^ (2 * (m + 2) - 1) ≤
        20736 * r ^ 3 * (144 * r ^ 2) ^ m := by
    intro m
    have hpow := even_shift_pow_seven_le_twelve_pow m
    have hrpow : 0 ≤ r ^ (2 * (m + 2) - 1) := pow_nonneg hr0 _
    calc
      (((2 * (m + 2) : ℕ) : ℝ) ^ 7) * r ^ (2 * (m + 2) - 1) ≤
          (12 : ℝ) ^ (2 * (m + 2)) * r ^ (2 * (m + 2) - 1) :=
        mul_le_mul_of_nonneg_right hpow hrpow
      _ = 20736 * r ^ 3 * (144 * r ^ 2) ^ m := by
        rw [show 2 * (m + 2) = 2 * m + 4 by omega,
          show 2 * m + 4 - 1 = 2 * m + 3 by omega]
        simp only [pow_add, pow_mul]
        ring
  have htermNonneg : ∀ m : ℕ, 0 ≤
      (((2 * (m + 2) : ℕ) : ℝ) ^ 7) * r ^ (2 * (m + 2) - 1) := by
    intro m
    positivity
  have hsummable := Summable.of_nonneg_of_le htermNonneg hmajor hmajorSummable
  refine ⟨hsummable, ?_⟩
  unfold thetaCuspLikelihoodEighthHigherEvenSectorTail
  calc
    (∑' m : ℕ, (((2 * (m + 2) : ℕ) : ℝ) ^ 7) *
        r ^ (2 * (m + 2) - 1)) ≤
        ∑' m : ℕ, 20736 * r ^ 3 * (144 * r ^ 2) ^ m :=
      Summable.tsum_le_tsum hmajor hsummable hmajorSummable
    _ = 20736 * r ^ 3 * (1 - 144 * r ^ 2)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hqNorm]

/-- Entire higher-even logarithmic scalar is below `1/3000`. -/
theorem thetaCuspLikelihoodEighthHigherEvenSectorTail_lt
    {r : ℝ} (hr0 : 0 ≤ r) (hr : 399 * r < 1) :
    thetaCuspLikelihoodEighthHigherEvenSectorTail r < (1 / 3000 : ℝ) := by
  rcases eq_or_lt_of_le hr0 with rfl | hrpos
  · unfold thetaCuspLikelihoodEighthHigherEvenSectorTail
    have hzero : (fun m : ℕ =>
        (((2 * (m + 2) : ℕ) : ℝ) ^ 7) *
          (0 : ℝ) ^ (2 * (m + 2) - 1)) = (fun _ : ℕ => (0 : ℝ)) := by
      funext m
      rw [zero_pow (by omega), mul_zero]
    rw [hzero]
    norm_num
  have hr1 : r < 1 / 399 := by nlinarith
  have hrSq := pow_lt_pow_left₀ hr1 hr0 (by norm_num : 2 ≠ 0)
  have hq : 144 * r ^ 2 < 1 / 1000 := by nlinarith
  have hden : 0 < 1 - 144 * r ^ 2 := by linarith
  have hinv : (1 - 144 * r ^ 2)⁻¹ < (1000 / 999 : ℝ) := by
    rw [inv_eq_one_div]
    apply (one_div_lt hden (by norm_num)).2
    nlinarith
  have hrCube := pow_lt_pow_left₀ hr1 hr0 (by norm_num : 3 ≠ 0)
  have htail :=
    (summable_thetaCuspLikelihoodEighthHigherEvenSectorTail_and_le hr0 hr).2
  have hfirst :
      20736 * r ^ 3 * (1 - 144 * r ^ 2)⁻¹ <
        20736 * r ^ 3 * (1000 / 999 : ℝ) :=
    mul_lt_mul_of_pos_left hinv (by positivity)
  have hsecond :
      20736 * r ^ 3 * (1000 / 999 : ℝ) <
        20736 * (1 / 399 : ℝ) ^ 3 * (1000 / 999 : ℝ) := by
    gcongr
  calc
    thetaCuspLikelihoodEighthHigherEvenSectorTail r ≤
        20736 * r ^ 3 * (1 - 144 * r ^ 2)⁻¹ := htail
    _ < 20736 * r ^ 3 * (1000 / 999 : ℝ) := hfirst
    _ < 20736 * (1 / 399 : ℝ) ^ 3 * (1000 / 999 : ℝ) := hsecond
    _ < (1 / 3000 : ℝ) := by norm_num

/-- Actual theta likelihood activity lies in the strict order-eight higher-even chamber. -/
theorem thetaCuspLikelihoodEighthHigherEvenSectorTail_actual_lt
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodEighthHigherEvenSectorTail
        (thetaCuspHigherLikelihoodSpectralResponse (thetaCuspLikelihoodCoordinate x)) <
      (1 / 3000 : ℝ) := by
  let B := thetaCuspLikelihoodCoordinate x
  let r := thetaCuspHigherLikelihoodSpectralResponse B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hr0 : 0 ≤ r := by
    dsimp only [r]
    rw [← thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
    exact thetaCuspHigherLikelihoodSpectralMoment_nonneg 0
  have hr : 399 * r < 1 := by
    simpa only [B, r] using
      three_hundred_ninety_nine_mul_thetaCuspHigherLikelihoodSpectralResponse_lt_one hx
  simpa only [B, r] using thetaCuspLikelihoodEighthHigherEvenSectorTail_lt hr0 hr

/-- Higher-even order-eight loss: logarithmic fusion scalar times full one-particle monomial mass. -/
noncomputable def thetaCuspLikelihoodEighthHigherEvenFockLoss (x : ℝ) : ℝ :=
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let r := thetaCuspHigherLikelihoodSpectralResponse B
  thetaCuspLikelihoodEighthHigherEvenSectorTail r *
    ∑' k : ℕ, thetaCuspLikelihoodAtomEighthMonomialMass (k + 2) A B

/-- Every higher even grade costs at most `1300/3` dominant exponential units. -/
theorem thetaCuspLikelihoodEighthHigherEvenFockLoss_le
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodEighthHigherEvenFockLoss x ≤
      (1300 / 3 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 8 *
        Real.exp (-(3 * thetaCuspSingleAtomReflectionScale 1 x)) := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let r := thetaCuspHigherLikelihoodSpectralResponse B
  have hA : Real.pi ≤ A := by
    dsimp only [A, thetaCuspSingleAtomReflectionScale]
    norm_num
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    nlinarith [Real.pi_pos]
  have hBA : B = A - 3 / 2 := by
    dsimp only [A, B]
    unfold thetaCuspLikelihoodCoordinate thetaCuspSingleAtomReflectionScale
    norm_num
    rw [show Real.exp (2 * x) = Real.exp x ^ 2 by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hr0 : 0 ≤ r := by
    dsimp only [r]
    rw [← thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
    exact thetaCuspHigherLikelihoodSpectralMoment_nonneg 0
  have hr : 399 * r < 1 := by
    simpa only [B, r] using
      three_hundred_ninety_nine_mul_thetaCuspHigherLikelihoodSpectralResponse_lt_one hx
  have htail := thetaCuspLikelihoodEighthHigherEvenSectorTail_lt hr0 hr
  have htail0 : 0 ≤ thetaCuspLikelihoodEighthHigherEvenSectorTail r := by
    unfold thetaCuspLikelihoodEighthHigherEvenSectorTail
    exact tsum_nonneg fun k => by positivity
  have hmass := tsum_thetaCuspLikelihoodAtomEighthMonomialMass_le hA hBA
  have hmass0 : 0 ≤
      ∑' k : ℕ, thetaCuspLikelihoodAtomEighthMonomialMass (k + 2) A B := by
    apply tsum_nonneg
    intro k
    unfold thetaCuspLikelihoodAtomEighthMonomialMass
    apply MeasureTheory.integral_nonneg
    intro t
    positivity
  unfold thetaCuspLikelihoodEighthHigherEvenFockLoss
  dsimp only [A, B, r]
  calc
    thetaCuspLikelihoodEighthHigherEvenSectorTail r *
          (∑' k : ℕ, thetaCuspLikelihoodAtomEighthMonomialMass (k + 2) A B) ≤
        (1 / 3000 : ℝ) *
          (∑' k : ℕ, thetaCuspLikelihoodAtomEighthMonomialMass (k + 2) A B) :=
      mul_le_mul_of_nonneg_right htail.le hmass0
    _ ≤ (1 / 3000 : ℝ) *
        (1300000 * A ^ 8 * Real.exp (-(3 * A))) := by gcongr
    _ = (1300 / 3 : ℝ) * A ^ 8 * Real.exp (-(3 * A)) := by ring

/-- Source-defined eighth Fock margin after paying grade two and every higher even grade. -/
noncomputable def thetaCuspLikelihoodEighthFockOddWeight (x : ℝ) : ℝ :=
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  thetaCuspLikelihoodEighthDominantSingleMass A -
    (thetaCuspLikelihoodEighthPairSectorMass A B +
      thetaCuspLikelihoodEighthHigherEvenFockLoss x)

/-- Complete even-grade absorption: dominant one-particle score retains a strict positive margin. -/
theorem thetaCuspLikelihoodEighthFockOddWeight_pos
    {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspLikelihoodEighthFockOddWeight x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  have hA : Real.pi ≤ A := by
    dsimp only [A, thetaCuspSingleAtomReflectionScale]
    norm_num
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    nlinarith [Real.pi_pos]
  have hApi : (157 / 50 : ℝ) ≤ A := by nlinarith [Real.pi_gt_d2]
  have hBA : B = A - 3 / 2 := by
    dsimp only [A, B]
    unfold thetaCuspLikelihoodCoordinate thetaCuspSingleAtomReflectionScale
    norm_num
    rw [show Real.exp (2 * x) = Real.exp x ^ 2 by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have hdominant :=
    three_halves_mul_thetaCuspLikelihoodEighthDominantPairMass_lt_singleMass hApi
  have htwo := thetaCuspLikelihoodAtomPairEighthScoreMass_two_two_eq hApi hBA
  have hnondom := thetaCuspLikelihoodNonDominantPairEighthTail_le_sharp hA hBA
  have hhigher := thetaCuspLikelihoodEighthHigherEvenFockLoss_le hx
  have hsingle :=
    seventeenThousandFourHundredNinetySixFifths_mul_pow_eight_exp_lt_dominantSingleMass
      hA hBA
  have hscale : 0 < A ^ 8 * Real.exp (-(3 * A)) := by
    have hA0 : 0 < A := Real.pi_pos.trans_le hA
    positivity
  have htail :
      thetaCuspLikelihoodNonDominantPairEighthTail A B +
          thetaCuspLikelihoodEighthHigherEvenFockLoss x <
        (1 / 3 : ℝ) * thetaCuspLikelihoodEighthDominantSingleMass A := by
    have hhigher' : thetaCuspLikelihoodEighthHigherEvenFockLoss x ≤
        (1300 / 3 : ℝ) * A ^ 8 * Real.exp (-(3 * A)) := by
      simpa only [A] using hhigher
    nlinarith [show
      (376399 / 1999 : ℝ) + 1300 / 3 < 5832 / 5 by norm_num]
  unfold thetaCuspLikelihoodEighthFockOddWeight
  dsimp only [A, B]
  unfold thetaCuspLikelihoodEighthPairSectorMass
  rw [htwo]
  nlinarith

end

end RHTower

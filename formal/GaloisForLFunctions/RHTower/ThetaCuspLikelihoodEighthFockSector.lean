import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodEighthStablePairCompensation

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

end

end RHTower

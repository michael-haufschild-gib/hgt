import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspReflectionSixthTuran

/-!
# Sixth reflection--Turan law for the complete theta source

This module closes the two atomwise majorants absent from the fourth-order mixture proof.
The fifth bound is imported from the literal sixth-jet ladder; the sixth bound below controls all
eleven Faà di Bruno terms against the exact source Gaussian gap.
-/

namespace RHTower

noncomputable section

set_option maxHeartbeats 2000000 in
theorem thetaCuspAtomLikelihoodRatioJetSix_abs_le
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x) :
    |thetaCuspAtomLikelihoodRatioJetSix n x| ≤
      60000 * (thetaCuspLogConcavityScale x * ((n : ℝ) ^ (2 : ℕ) - 1)) ^ (6 : ℕ) *
        thetaCuspAtomLikelihoodRatio n x := by
  let z := thetaCuspLogConcavityScale x * ((n : ℝ) ^ (2 : ℕ) - 1)
  let p := -thetaCuspAtomLikelihoodLogJetZero n x
  let alpha := -thetaCuspAtomLikelihoodLogJetOne n x
  let beta := -thetaCuspAtomLikelihoodLogJetTwo n x
  let gamma := thetaCuspAtomLikelihoodLogJetThree n x
  let delta := thetaCuspAtomLikelihoodLogJetFour n x
  let epsilon := thetaCuspAtomLikelihoodLogJetFive n x
  have hq := thetaCuspAtomLikelihoodLogJetZero_bounds hn hx
  have hq1 := thetaCuspAtomLikelihoodLogJetOne_bounds hn hx
  have hq2 := thetaCuspAtomLikelihoodLogJetTwo_bounds hn hx
  have hq3 := thetaCuspAtomLikelihoodLogJetThree_abs_le hn hx
  have hq4 := thetaCuspAtomLikelihoodLogJetFour_abs_le hn hx
  have hq5 := thetaCuspAtomLikelihoodLogJetFive_abs_le hn hx
  have hr := thetaCuspAtomLikelihoodRatio_pos (by omega : 0 < n) hx
  have hz := (thetaCuspLikelihoodScaleFacts hn hx.le).2.2.1
  have hp0 : 0 ≤ p := by dsimp [p, z]; linarith
  have hp : p ≤ 3 * z := by dsimp [p, z]; linarith
  have ha0 : 0 ≤ alpha := by dsimp [alpha, z]; linarith
  have ha : alpha ≤ 4 * z := by dsimp [alpha, z]; linarith
  have hb0 : 0 ≤ beta := by dsimp [beta, z]; linarith
  have hb : beta ≤ 14 * z := by dsimp [beta, z]; linarith
  have hg : |gamma| ≤ 32 * z := by simpa only [gamma, z] using hq3
  have hdelta : |delta| ≤ 600 * z := by simpa only [delta, z] using hq4
  have hepsilon : |epsilon| ≤ 8000 * z := by simpa only [epsilon, z] using hq5
  have hz0 : 0 ≤ z := by linarith
  have hz1 : 1 ≤ z := by linarith
  have hp2 : p ^ (2 : ℕ) ≤ 9 * z ^ (2 : ℕ) := by
    have h := pow_le_pow_left₀ hp0 hp 2
    nlinarith
  have hp3 : p ^ (3 : ℕ) ≤ 27 * z ^ (3 : ℕ) := by
    have h := pow_le_pow_left₀ hp0 hp 3
    nlinarith
  have hp4 : p ^ (4 : ℕ) ≤ 81 * z ^ (4 : ℕ) := by
    have h := pow_le_pow_left₀ hp0 hp 4
    nlinarith
  have hp6 : p ^ (6 : ℕ) ≤ 729 * z ^ (6 : ℕ) := by
    have h := pow_le_pow_left₀ hp0 hp 6
    nlinarith
  have ha2 : alpha ^ (2 : ℕ) ≤ 16 * z ^ (2 : ℕ) := by
    have h := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have ha3 : alpha ^ (3 : ℕ) ≤ 64 * z ^ (3 : ℕ) := by
    have h := pow_le_pow_left₀ ha0 ha 3
    nlinarith
  have hb2 : beta ^ (2 : ℕ) ≤ 196 * z ^ (2 : ℕ) := by
    have h := pow_le_pow_left₀ hb0 hb 2
    nlinarith
  have hz2one : 1 ≤ z ^ (2 : ℕ) := one_le_pow₀ hz1
  have hz3one : 1 ≤ z ^ (3 : ℕ) := one_le_pow₀ hz1
  have hz4one : 1 ≤ z ^ (4 : ℕ) := one_le_pow₀ hz1
  have hz5one : 1 ≤ z ^ (5 : ℕ) := one_le_pow₀ hz1
  have hz1to6 : z ≤ z ^ (6 : ℕ) := by
    calc
      z = z * 1 := by ring
      _ ≤ z * z ^ (5 : ℕ) := by gcongr
      _ = z ^ (6 : ℕ) := by ring
  have hz2to6 : z ^ (2 : ℕ) ≤ z ^ (6 : ℕ) := by
    calc
      z ^ (2 : ℕ) = z ^ (2 : ℕ) * 1 := by ring
      _ ≤ z ^ (2 : ℕ) * z ^ (4 : ℕ) := by gcongr
      _ = z ^ (6 : ℕ) := by ring
  have hz3to6 : z ^ (3 : ℕ) ≤ z ^ (6 : ℕ) := by
    calc
      z ^ (3 : ℕ) = z ^ (3 : ℕ) * 1 := by ring
      _ ≤ z ^ (3 : ℕ) * z ^ (3 : ℕ) := by gcongr
      _ = z ^ (6 : ℕ) := by ring
  have hz4to6 : z ^ (4 : ℕ) ≤ z ^ (6 : ℕ) := by
    calc
      z ^ (4 : ℕ) = z ^ (4 : ℕ) * 1 := by ring
      _ ≤ z ^ (4 : ℕ) * z ^ (2 : ℕ) := by gcongr
      _ = z ^ (6 : ℕ) := by ring
  have hz5to6 : z ^ (5 : ℕ) ≤ z ^ (6 : ℕ) := by
    calc
      z ^ (5 : ℕ) = z ^ (5 : ℕ) * 1 := by ring
      _ ≤ z ^ (5 : ℕ) * z := by gcongr
      _ = z ^ (6 : ℕ) := by ring
  have hterm1 : |p ^ (6 : ℕ)| ≤ 729 * z ^ (6 : ℕ) := by
    rw [abs_of_nonneg (pow_nonneg hp0 _)]
    exact hp6
  have hterm2 : |-15 * p ^ (4 : ℕ) * alpha| ≤ 4860 * z ^ (6 : ℕ) := by
    have hbound : 15 * p ^ (4 : ℕ) * alpha ≤ 4860 * z ^ (5 : ℕ) := by
      calc
        15 * p ^ (4 : ℕ) * alpha ≤ 15 * (81 * z ^ (4 : ℕ)) * (4 * z) := by gcongr
        _ = 4860 * z ^ (5 : ℕ) := by ring
    rw [abs_mul, abs_mul, abs_of_neg (by norm_num),
      abs_of_nonneg (pow_nonneg hp0 _), abs_of_nonneg ha0]
    norm_num
    exact hbound.trans (by gcongr)
  have hterm3 : |45 * p ^ (2 : ℕ) * alpha ^ (2 : ℕ)| ≤ 6480 * z ^ (6 : ℕ) := by
    have hbound : 45 * p ^ (2 : ℕ) * alpha ^ (2 : ℕ) ≤ 6480 * z ^ (4 : ℕ) := by
      calc
        45 * p ^ (2 : ℕ) * alpha ^ (2 : ℕ) ≤ 45 * (9 * z ^ (2 : ℕ)) * (16 * z ^ (2 : ℕ)) := by gcongr
        _ = 6480 * z ^ (4 : ℕ) := by ring
    rw [abs_of_nonneg (by positivity)]
    exact hbound.trans (by gcongr)
  have hterm4 : |-15 * alpha ^ (3 : ℕ)| ≤ 960 * z ^ (6 : ℕ) := by
    rw [abs_mul, abs_of_neg (by norm_num), abs_of_nonneg (pow_nonneg ha0 _)]
    norm_num
    exact (show 15 * alpha ^ (3 : ℕ) ≤ 960 * z ^ (3 : ℕ) by
      calc
        15 * alpha ^ (3 : ℕ) ≤ 15 * (64 * z ^ (3 : ℕ)) := by gcongr
        _ = 960 * z ^ (3 : ℕ) := by ring).trans (by gcongr)
  have hterm5 : |20 * p ^ (3 : ℕ) * beta| ≤ 7560 * z ^ (6 : ℕ) := by
    have hbound : 20 * p ^ (3 : ℕ) * beta ≤ 7560 * z ^ (4 : ℕ) := by
      calc
        20 * p ^ (3 : ℕ) * beta ≤ 20 * (27 * z ^ (3 : ℕ)) * (14 * z) := by gcongr
        _ = 7560 * z ^ (4 : ℕ) := by ring
    rw [abs_of_nonneg (by positivity)]
    exact hbound.trans (by gcongr)
  have hterm6 : |-60 * p * alpha * beta| ≤ 10080 * z ^ (6 : ℕ) := by
    have h3z0 : 0 ≤ 3 * z := mul_nonneg (by norm_num) hz0
    have h4z0 : 0 ≤ 4 * z := mul_nonneg (by norm_num) hz0
    have hpa : p * alpha ≤ (3 * z) * (4 * z) :=
      mul_le_mul hp ha ha0 h3z0
    have hpab : p * alpha * beta ≤ ((3 * z) * (4 * z)) * (14 * z) :=
      mul_le_mul hpa hb hb0 (mul_nonneg h3z0 h4z0)
    have hbound : 60 * p * alpha * beta ≤ 10080 * z ^ (3 : ℕ) := by
      calc
        60 * p * alpha * beta = 60 * (p * alpha * beta) := by ring
        _ ≤ 60 * (((3 * z) * (4 * z)) * (14 * z)) :=
          mul_le_mul_of_nonneg_left hpab (by norm_num)
        _ = 10080 * z ^ (3 : ℕ) := by ring
    rw [abs_mul, abs_mul, abs_mul, abs_of_neg (by norm_num),
      abs_of_nonneg hp0, abs_of_nonneg ha0, abs_of_nonneg hb0]
    norm_num
    exact hbound.trans (by gcongr)
  have hterm7 : |10 * beta ^ (2 : ℕ)| ≤ 1960 * z ^ (6 : ℕ) := by
    rw [abs_of_nonneg (by positivity)]
    exact (show 10 * beta ^ (2 : ℕ) ≤ 1960 * z ^ (2 : ℕ) by
      calc
        10 * beta ^ (2 : ℕ) ≤ 10 * (196 * z ^ (2 : ℕ)) := by gcongr
        _ = 1960 * z ^ (2 : ℕ) := by ring).trans (by gcongr)
  have hterm8 : |15 * p ^ (2 : ℕ) * gamma| ≤ 4320 * z ^ (6 : ℕ) := by
    have hbound : 15 * p ^ (2 : ℕ) * |gamma| ≤ 4320 * z ^ (3 : ℕ) := by
      calc
        15 * p ^ (2 : ℕ) * |gamma| ≤ 15 * (9 * z ^ (2 : ℕ)) * (32 * z) := by gcongr
        _ = 4320 * z ^ (3 : ℕ) := by ring
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity),
      abs_of_nonneg (pow_nonneg hp0 _)]
    exact hbound.trans (by gcongr)
  have hterm9 : |-15 * alpha * gamma| ≤ 1920 * z ^ (6 : ℕ) := by
    have hbound : 15 * alpha * |gamma| ≤ 1920 * z ^ (2 : ℕ) := by
      calc
        15 * alpha * |gamma| ≤ 15 * (4 * z) * (32 * z) := by gcongr
        _ = 1920 * z ^ (2 : ℕ) := by ring
    rw [abs_mul, abs_mul, abs_of_neg (by norm_num), abs_of_nonneg ha0]
    norm_num
    exact hbound.trans (by gcongr)
  have hterm10 : |-6 * p * delta| ≤ 10800 * z ^ (6 : ℕ) := by
    have hbound : 6 * p * |delta| ≤ 10800 * z ^ (2 : ℕ) := by
      calc
        6 * p * |delta| ≤ 6 * (3 * z) * (600 * z) := by gcongr
        _ = 10800 * z ^ (2 : ℕ) := by ring
    rw [abs_mul, abs_mul, abs_of_neg (by norm_num), abs_of_nonneg hp0]
    norm_num
    exact hbound.trans (by gcongr)
  have hterm11 : |epsilon| ≤ 8000 * z ^ (6 : ℕ) :=
    hepsilon.trans (by gcongr)
  let t0 := p ^ (6 : ℕ)
  let t1 := -15 * p ^ (4 : ℕ) * alpha
  let t2 := 45 * p ^ (2 : ℕ) * alpha ^ (2 : ℕ)
  let t3 := -15 * alpha ^ (3 : ℕ)
  let t4 := 20 * p ^ (3 : ℕ) * beta
  let t5 := -60 * p * alpha * beta
  let t6 := 10 * beta ^ (2 : ℕ)
  let t7 := 15 * p ^ (2 : ℕ) * gamma
  let t8 := -15 * alpha * gamma
  let t9 := -6 * p * delta
  let t10 := epsilon
  have ht0 : |t0| ≤ 729 * z ^ (6 : ℕ) := by simpa only [t0] using hterm1
  have ht1 : |t1| ≤ 4860 * z ^ (6 : ℕ) := by simpa only [t1] using hterm2
  have ht2 : |t2| ≤ 6480 * z ^ (6 : ℕ) := by simpa only [t2] using hterm3
  have ht3 : |t3| ≤ 960 * z ^ (6 : ℕ) := by simpa only [t3] using hterm4
  have ht4 : |t4| ≤ 7560 * z ^ (6 : ℕ) := by simpa only [t4] using hterm5
  have ht5 : |t5| ≤ 10080 * z ^ (6 : ℕ) := by simpa only [t5] using hterm6
  have ht6 : |t6| ≤ 1960 * z ^ (6 : ℕ) := by simpa only [t6] using hterm7
  have ht7 : |t7| ≤ 4320 * z ^ (6 : ℕ) := by simpa only [t7] using hterm8
  have ht8 : |t8| ≤ 1920 * z ^ (6 : ℕ) := by simpa only [t8] using hterm9
  have ht9 : |t9| ≤ 10800 * z ^ (6 : ℕ) := by simpa only [t9] using hterm10
  have ht10 : |t10| ≤ 8000 * z ^ (6 : ℕ) := by simpa only [t10] using hterm11
  have hsum01 : |t0 + t1| ≤ (729 + 4860 : ℝ) * z ^ (6 : ℕ) := by
    calc
      |t0 + t1| ≤ |t0| + |t1| := abs_add_le _ _
      _ ≤ 729 * z ^ (6 : ℕ) + 4860 * z ^ (6 : ℕ) := add_le_add ht0 ht1
      _ = (729 + 4860 : ℝ) * z ^ (6 : ℕ) := by ring
  have hsum02 : |t0 + t1 + t2| ≤ (729 + 4860 + 6480 : ℝ) * z ^ (6 : ℕ) := by
    calc
      |t0 + t1 + t2| ≤ |t0 + t1| + |t2| := abs_add_le _ _
      _ ≤ (729 + 4860 : ℝ) * z ^ (6 : ℕ) + 6480 * z ^ (6 : ℕ) := add_le_add hsum01 ht2
      _ = (729 + 4860 + 6480 : ℝ) * z ^ (6 : ℕ) := by ring
  have hsum03 : |t0 + t1 + t2 + t3| ≤ (729 + 4860 + 6480 + 960 : ℝ) * z ^ (6 : ℕ) := by
    calc
      |t0 + t1 + t2 + t3| ≤ |t0 + t1 + t2| + |t3| := abs_add_le _ _
      _ ≤ (729 + 4860 + 6480 : ℝ) * z ^ (6 : ℕ) + 960 * z ^ (6 : ℕ) := add_le_add hsum02 ht3
      _ = (729 + 4860 + 6480 + 960 : ℝ) * z ^ (6 : ℕ) := by ring
  have hsum04 : |t0 + t1 + t2 + t3 + t4| ≤ (729 + 4860 + 6480 + 960 + 7560 : ℝ) * z ^ (6 : ℕ) := by
    calc
      |t0 + t1 + t2 + t3 + t4| ≤ |t0 + t1 + t2 + t3| + |t4| := abs_add_le _ _
      _ ≤ (729 + 4860 + 6480 + 960 : ℝ) * z ^ (6 : ℕ) + 7560 * z ^ (6 : ℕ) := add_le_add hsum03 ht4
      _ = (729 + 4860 + 6480 + 960 + 7560 : ℝ) * z ^ (6 : ℕ) := by ring
  have hsum05 : |t0 + t1 + t2 + t3 + t4 + t5| ≤ (729 + 4860 + 6480 + 960 + 7560 + 10080 : ℝ) * z ^ (6 : ℕ) := by
    calc
      |t0 + t1 + t2 + t3 + t4 + t5| ≤ |t0 + t1 + t2 + t3 + t4| + |t5| := abs_add_le _ _
      _ ≤ (729 + 4860 + 6480 + 960 + 7560 : ℝ) * z ^ (6 : ℕ) + 10080 * z ^ (6 : ℕ) := add_le_add hsum04 ht5
      _ = (729 + 4860 + 6480 + 960 + 7560 + 10080 : ℝ) * z ^ (6 : ℕ) := by ring
  have hsum06 : |t0 + t1 + t2 + t3 + t4 + t5 + t6| ≤ (729 + 4860 + 6480 + 960 + 7560 + 10080 + 1960 : ℝ) * z ^ (6 : ℕ) := by
    calc
      |t0 + t1 + t2 + t3 + t4 + t5 + t6| ≤ |t0 + t1 + t2 + t3 + t4 + t5| + |t6| := abs_add_le _ _
      _ ≤ (729 + 4860 + 6480 + 960 + 7560 + 10080 : ℝ) * z ^ (6 : ℕ) + 1960 * z ^ (6 : ℕ) := add_le_add hsum05 ht6
      _ = (729 + 4860 + 6480 + 960 + 7560 + 10080 + 1960 : ℝ) * z ^ (6 : ℕ) := by ring
  have hsum07 : |t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7| ≤ (729 + 4860 + 6480 + 960 + 7560 + 10080 + 1960 + 4320 : ℝ) * z ^ (6 : ℕ) := by
    calc
      |t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7| ≤ |t0 + t1 + t2 + t3 + t4 + t5 + t6| + |t7| := abs_add_le _ _
      _ ≤ (729 + 4860 + 6480 + 960 + 7560 + 10080 + 1960 : ℝ) * z ^ (6 : ℕ) + 4320 * z ^ (6 : ℕ) := add_le_add hsum06 ht7
      _ = (729 + 4860 + 6480 + 960 + 7560 + 10080 + 1960 + 4320 : ℝ) * z ^ (6 : ℕ) := by ring
  have hsum08 : |t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8| ≤ (729 + 4860 + 6480 + 960 + 7560 + 10080 + 1960 + 4320 + 1920 : ℝ) * z ^ (6 : ℕ) := by
    calc
      |t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8| ≤ |t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7| + |t8| := abs_add_le _ _
      _ ≤ (729 + 4860 + 6480 + 960 + 7560 + 10080 + 1960 + 4320 : ℝ) * z ^ (6 : ℕ) + 1920 * z ^ (6 : ℕ) := add_le_add hsum07 ht8
      _ = (729 + 4860 + 6480 + 960 + 7560 + 10080 + 1960 + 4320 + 1920 : ℝ) * z ^ (6 : ℕ) := by ring
  have hsum09 : |t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9| ≤ (729 + 4860 + 6480 + 960 + 7560 + 10080 + 1960 + 4320 + 1920 + 10800 : ℝ) * z ^ (6 : ℕ) := by
    calc
      |t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9| ≤ |t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8| + |t9| := abs_add_le _ _
      _ ≤ (729 + 4860 + 6480 + 960 + 7560 + 10080 + 1960 + 4320 + 1920 : ℝ) * z ^ (6 : ℕ) + 10800 * z ^ (6 : ℕ) := add_le_add hsum08 ht9
      _ = (729 + 4860 + 6480 + 960 + 7560 + 10080 + 1960 + 4320 + 1920 + 10800 : ℝ) * z ^ (6 : ℕ) := by ring
  have hsum10 : |t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10| ≤ 60000 * z ^ (6 : ℕ) := by
    calc
      |t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10| ≤
          |t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9| + |t10| := abs_add_le _ _
      _ ≤ (729 + 4860 + 6480 + 960 + 7560 + 10080 + 1960 + 4320 + 1920 + 10800 : ℝ) * z ^ (6 : ℕ) + 8000 * z ^ (6 : ℕ) := add_le_add hsum09 ht10
      _ = 57669 * z ^ (6 : ℕ) := by ring
      _ ≤ 60000 * z ^ (6 : ℕ) :=
        mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hz0 _)
  have hcoeff :
      |p ^ (6 : ℕ) - 15 * p ^ (4 : ℕ) * alpha + 45 * p ^ (2 : ℕ) * alpha ^ (2 : ℕ) -
          15 * alpha ^ (3 : ℕ) + 20 * p ^ (3 : ℕ) * beta - 60 * p * alpha * beta +
          10 * beta ^ (2 : ℕ) + 15 * p ^ (2 : ℕ) * gamma - 15 * alpha * gamma -
          6 * p * delta + epsilon| ≤ 60000 * z ^ (6 : ℕ) := by
    convert hsum10 using 1 <;>
      dsimp [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10] <;> ring
  unfold thetaCuspAtomLikelihoodRatioJetSix
  rw [abs_mul, abs_of_pos hr]
  apply mul_le_mul_of_nonneg_right _ hr.le
  rw [show thetaCuspAtomLikelihoodLogJetZero n x ^ (6 : ℕ) +
      15 * thetaCuspAtomLikelihoodLogJetZero n x ^ (4 : ℕ) *
        thetaCuspAtomLikelihoodLogJetOne n x +
      45 * thetaCuspAtomLikelihoodLogJetZero n x ^ (2 : ℕ) *
        thetaCuspAtomLikelihoodLogJetOne n x ^ (2 : ℕ) +
      15 * thetaCuspAtomLikelihoodLogJetOne n x ^ (3 : ℕ) +
      20 * thetaCuspAtomLikelihoodLogJetZero n x ^ (3 : ℕ) *
        thetaCuspAtomLikelihoodLogJetTwo n x +
      60 * thetaCuspAtomLikelihoodLogJetZero n x *
        thetaCuspAtomLikelihoodLogJetOne n x * thetaCuspAtomLikelihoodLogJetTwo n x +
      10 * thetaCuspAtomLikelihoodLogJetTwo n x ^ (2 : ℕ) +
      15 * thetaCuspAtomLikelihoodLogJetZero n x ^ (2 : ℕ) *
        thetaCuspAtomLikelihoodLogJetThree n x +
      15 * thetaCuspAtomLikelihoodLogJetOne n x *
        thetaCuspAtomLikelihoodLogJetThree n x +
      6 * thetaCuspAtomLikelihoodLogJetZero n x *
        thetaCuspAtomLikelihoodLogJetFour n x +
      thetaCuspAtomLikelihoodLogJetFive n x =
      p ^ (6 : ℕ) - 15 * p ^ (4 : ℕ) * alpha + 45 * p ^ (2 : ℕ) * alpha ^ (2 : ℕ) -
        15 * alpha ^ (3 : ℕ) + 20 * p ^ (3 : ℕ) * beta - 60 * p * alpha * beta +
        10 * beta ^ (2 : ℕ) + 15 * p ^ (2 : ℕ) * gamma - 15 * alpha * gamma -
        6 * p * delta + epsilon by
    dsimp [p, alpha, beta, gamma, delta, epsilon]
    ring]
  exact hcoeff

end

end RHTower

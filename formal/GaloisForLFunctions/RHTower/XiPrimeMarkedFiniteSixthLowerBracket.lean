import GaloisForLFunctions.RHTower.FiniteReverseResidualSeam
import GaloisForLFunctions.RHTower.XiCenteredOrderTwentyThreeSourceBudgetClosure
import GaloisForLFunctions.RHTower.ThetaGibbsSteinSourceMinor
import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor
import GaloisForLFunctions.RHTower.XiPrimeMarkedPhysicalEndpointRVMQuarticIncidence
import GaloisForLFunctions.RHTower.XiPrimeMarkedQuarticEffectiveRank

/-!
# Quantitative completed-source Hankel margin

The Stein first-atom bounds contain a rational margin strong enough to
dominate the finite reverse-head sixth-moment defect. This module extracts
that margin from the raw theta moments without numerical evaluation.
-/

namespace RHTower

noncomputable section

/-- Exact raw-moment decomposition of the first normalized source Hankel
minor. -/
theorem normalizedPrimeArch_hankelMargin_raw_decomp :
    1080 * thetaCuspRawEvenMoment 0 ^ (3 : ℕ) *
        (normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
          normalizedPrimeArchMoment 1 ^ (2 : ℕ)) =
      thetaCuspRawEvenMoment 0 *
        (9 * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 3 -
          14 * thetaCuspRawEvenMoment 2 ^ (2 : ℕ)) +
      thetaCuspRawEvenMoment 2 *
        (45 * thetaCuspRawEvenMoment 1 ^ (2 : ℕ) -
          16 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2) := by
  have hid := normalizedPrimeArch_firstHankelMinor_scaled_eq_thetaCuspMoments
  calc
    1080 * thetaCuspRawEvenMoment 0 ^ (3 : ℕ) *
        (normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
          normalizedPrimeArchMoment 1 ^ (2 : ℕ)) =
      3 * thetaCuspRawEvenMoment 0 ^ (3 : ℕ) *
        (360 * (normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
          normalizedPrimeArchMoment 1 ^ (2 : ℕ))) := by ring
    _ = 3 * thetaCuspRawEvenMoment 0 ^ (3 : ℕ) *
        (3 * thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 3 +
          15 * thetaCuspNormalizedEvenMoment 1 ^ (2 : ℕ) *
            thetaCuspNormalizedEvenMoment 2 -
          10 * thetaCuspNormalizedEvenMoment 2 ^ (2 : ℕ)) := by rw [hid]
    _ = thetaCuspRawEvenMoment 0 *
          (9 * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 3 -
            14 * thetaCuspRawEvenMoment 2 ^ (2 : ℕ)) +
        thetaCuspRawEvenMoment 2 *
          (45 * thetaCuspRawEvenMoment 1 ^ (2 : ℕ) -
            16 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2) := by
      simp only [thetaCuspNormalizedEvenMoment]
      field_simp [thetaCuspRawEvenMoment_zero_pos.ne']
      ring

private theorem thetaCusp_relaxedFourth_from_stein :
    ThetaCuspRelaxedFourthMomentConcentration := by
  apply thetaCuspRelaxedFourthMomentConcentration_of_first_atom
  rw [thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 0,
    thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 1,
    thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 2]
  have hscaled := mul_le_mul_of_nonneg_left
    thetaCuspFirstAtomWardMoment_stein_ratio_bounds.2
    (sq_nonneg (2 * Real.pi))
  calc
    16 * ((3005 / 2997 : ℝ) *
        (2 * Real.pi * thetaCuspFirstAtomWardMoment 0)) *
        ((3005 / 2997 : ℝ) *
          (2 * Real.pi * thetaCuspFirstAtomWardMoment 2)) =
      (2 * Real.pi) ^ 2 *
        (16 * ((3005 / 2997 : ℝ) * thetaCuspFirstAtomWardMoment 0) *
          ((3005 / 2997 : ℝ) * thetaCuspFirstAtomWardMoment 2)) := by ring
    _ ≤ (2 * Real.pi) ^ 2 *
        (45 * thetaCuspFirstAtomWardMoment 1 ^ 2) := hscaled
    _ = 45 * (2 * Real.pi * thetaCuspFirstAtomWardMoment 1) ^ 2 := by ring

/-- Explicit positive lower bound for the completed source's first Hankel
minor. It is strong enough to cover the reverse-head rounding defect. -/
theorem normalizedPrimeArch_firstHankelMargin_ge_stein :
    (4 / 243 : ℝ) * (17 / 200000 : ℝ) ^ (2 : ℕ) ≤
      normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
        normalizedPrimeArchMoment 1 ^ (2 : ℕ) := by
  let R0 := thetaCuspRawEvenMoment 0
  let R1 := thetaCuspRawEvenMoment 1
  let R2 := thetaCuspRawEvenMoment 2
  let R3 := thetaCuspRawEvenMoment 3
  let H := normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
    normalizedPrimeArchMoment 1 ^ (2 : ℕ)
  let e := Real.exp (-Real.pi)
  let q := 2 * Real.pi * e
  let c : ℝ := 3005 / 2997
  let cap : ℝ := c * (18303 / 10000)
  let δ : ℝ :=
    9 * (423 / 5000) * (441 / 200000) -
      14 * (c * (5457 / 500000)) ^ (2 : ℕ)
  let U := 9 * R1 * R3 - 14 * R2 ^ (2 : ℕ)
  let V := 45 * R1 ^ (2 : ℕ) - 16 * R0 * R2
  have he : 0 < e := Real.exp_pos _
  have hq : 0 < q := by dsimp [q]; positivity
  have hc : 0 < c := by dsimp [c]; norm_num
  have hcap : 0 < cap := by dsimp [cap]; positivity
  have hδ : 0 < δ := by dsimp [δ, c]; norm_num
  have hR0 : 0 < R0 := thetaCuspRawEvenMoment_zero_pos
  have hR1 : 0 ≤ R1 := thetaCuspRawEvenMoment_nonneg 1
  have hR2 : 0 ≤ R2 := thetaCuspRawEvenMoment_nonneg 2
  obtain ⟨hW0lower, hW1lower, hW2upper, hW3lower⟩ :=
    thetaCuspFirstAtomWardMoment_stein_bounds
  have hW0upper :
      thetaCuspFirstAtomWardMoment 0 ≤ (18303 / 10000 : ℝ) * e := by
    dsimp [thetaCuspFirstAtomWardMoment, e]
    linarith
  have hR0upper : R0 ≤ cap * q := by
    have hraw := thetaCuspRawEvenMoment_le_first_atom_factor 0
    rw [thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 0] at hraw
    calc
      R0 ≤ c * (2 * Real.pi * thetaCuspFirstAtomWardMoment 0) := by
        simpa only [R0, c] using hraw
      _ ≤ c * (2 * Real.pi * ((18303 / 10000 : ℝ) * e)) := by
        gcongr
      _ = cap * q := by dsimp [cap, q]; ring
  have hR1lower : q * (423 / 5000 : ℝ) ≤ R1 := by
    have hraw := thetaCuspAtomRawEvenMoment_one_le_raw 1
    rw [thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 1] at hraw
    calc
      q * (423 / 5000 : ℝ) =
          2 * Real.pi * ((423 / 5000 : ℝ) * e) := by dsimp [q]; ring
      _ ≤ 2 * Real.pi * thetaCuspFirstAtomWardMoment 1 :=
        mul_le_mul_of_nonneg_left hW1lower (by positivity)
      _ ≤ R1 := by simpa only [R1] using hraw
  have hR3lower : q * (441 / 200000 : ℝ) ≤ R3 := by
    have hraw := thetaCuspAtomRawEvenMoment_one_le_raw 3
    rw [thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 3] at hraw
    calc
      q * (441 / 200000 : ℝ) =
          2 * Real.pi * ((441 / 200000 : ℝ) * e) := by dsimp [q]; ring
      _ ≤ 2 * Real.pi * thetaCuspFirstAtomWardMoment 3 :=
        mul_le_mul_of_nonneg_left hW3lower (by positivity)
      _ ≤ R3 := by simpa only [R3] using hraw
  have hR2upper : R2 ≤ q * (c * (5457 / 500000 : ℝ)) := by
    have hraw := thetaCuspRawEvenMoment_le_first_atom_factor 2
    rw [thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 2] at hraw
    calc
      R2 ≤ c * (2 * Real.pi * thetaCuspFirstAtomWardMoment 2) := by
        simpa only [R2, c] using hraw
      _ ≤ c * (2 * Real.pi * ((5457 / 500000 : ℝ) * e)) := by
        gcongr
      _ = q * (c * (5457 / 500000 : ℝ)) := by dsimp [q]; ring
  have hproduct :
      (q * (423 / 5000 : ℝ)) * (q * (441 / 200000 : ℝ)) ≤ R1 * R3 := by
    gcongr
  have hR2sq : R2 ^ (2 : ℕ) ≤
      (q * (c * (5457 / 500000 : ℝ))) ^ (2 : ℕ) :=
    (sq_le_sq₀ hR2 (by positivity)).mpr hR2upper
  have hUlower : q ^ (2 : ℕ) * δ ≤ U := by
    dsimp [δ, U]
    nlinarith [hproduct, hR2sq]
  have hrelaxed := thetaCusp_relaxedFourth_from_stein
  rw [ThetaCuspRelaxedFourthMomentConcentration] at hrelaxed
  have hweighted : 0 ≤ R2 * V := by
    dsimp [V]
    exact mul_nonneg hR2 (by simpa only [R0, R1, R2] using sub_nonneg.mpr hrelaxed)
  have hrawIdentity : 1080 * R0 ^ (3 : ℕ) * H = R0 * U + R2 * V := by
    simpa only [R0, R1, R2, R3, H, U, V] using
      normalizedPrimeArch_hankelMargin_raw_decomp
  have hHraw : U ≤ 1080 * R0 ^ (2 : ℕ) * H := by
    by_contra hnot
    have hlt : 1080 * R0 ^ (2 : ℕ) * H < U := lt_of_not_ge hnot
    have hp : 0 < R0 * (U - 1080 * R0 ^ (2 : ℕ) * H) :=
      mul_pos hR0 (sub_pos.mpr hlt)
    nlinarith [hrawIdentity, hweighted]
  have hUpos : 0 < U :=
    lt_of_lt_of_le (mul_pos (sq_pos_of_pos hq) hδ) hUlower
  have hHpos : 0 < H := by
    by_contra hnot
    have hHle : H ≤ 0 := le_of_not_gt hnot
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ 1080 * R0 ^ (2 : ℕ) by positivity) hHle
    linarith
  have hR0sq : R0 ^ (2 : ℕ) ≤ (cap * q) ^ (2 : ℕ) :=
    (sq_le_sq₀ hR0.le (by positivity)).mpr hR0upper
  have hscaled := mul_le_mul_of_nonneg_right hR0sq
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1080) hHpos.le)
  have hcapLower : q ^ (2 : ℕ) * δ ≤
      1080 * (cap * q) ^ (2 : ℕ) * H := by
    nlinarith [hUlower, hHraw, hscaled]
  have hRatLower : δ ≤ 1080 * cap ^ (2 : ℕ) * H := by
    by_contra hnot
    have hlt : 1080 * cap ^ (2 : ℕ) * H < δ := lt_of_not_ge hnot
    have hp := mul_pos (sq_pos_of_pos hq) (sub_pos.mpr hlt)
    nlinarith [hcapLower]
  have hRatCompare :
      (4 / 243 : ℝ) * (17 / 200000 : ℝ) ^ (2 : ℕ) *
          (1080 * cap ^ (2 : ℕ)) ≤ δ := by
    dsimp [cap, c, δ]
    norm_num
  have hTarget :
      (4 / 243 : ℝ) * (17 / 200000 : ℝ) ^ (2 : ℕ) ≤ H := by
    have htotal := hRatCompare.trans hRatLower
    by_contra hnot
    have hlt : H < (4 / 243 : ℝ) * (17 / 200000 : ℝ) ^ (2 : ℕ) :=
      lt_of_not_ge hnot
    have hp := mul_pos
      (show 0 < 1080 * cap ^ (2 : ℕ) by positivity)
      (sub_pos.mpr hlt)
    nlinarith only [htotal, hp]
  simpa only [H] using hTarget

/-- The actual completed source has enough first Hankel margin to cover
the finite reverse-head defect for its effective rank at least ten. -/
theorem normalizedPrimeArch_strongHankel_247_243 :
    247 * normalizedPrimeArchMoment 1 ^ (2 : ℕ) ≤
      243 * normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 := by
  have hM1 := normalizedPrimeArchMoment_one_lt_seventeen_over_twoHundredThousand
  have hM1sq : normalizedPrimeArchMoment 1 ^ (2 : ℕ) ≤
      (17 / 200000 : ℝ) ^ (2 : ℕ) :=
    (sq_le_sq₀ normalizedPrimeArchMoment_one_pos.le (by norm_num)).mpr hM1.le
  have hmargin := normalizedPrimeArch_firstHankelMargin_ge_stein
  nlinarith

/-- The completed source's half-moments obey the exact margin required by
the reverse finite head. -/
theorem routeK_sourceStrongHankel_247_243 :
    247 * routeKQuarticHalfEnergy ^ (2 : ℕ) ≤
      243 * routeKQuarticHalfMass * (normalizedPrimeArchMoment 2 / 2) := by
  have hsource := normalizedPrimeArch_strongHankel_247_243
  rw [routeKQuarticHalfEnergy, routeKQuarticHalfMass,
    routeKSourceZerothMoment_eq_normalizedPrimeArchMoment,
    routeKSourceFirstMoment_eq_normalizedPrimeArchMoment]
  nlinarith

/-- The actual completed source has a finite positive reverse head whose
quadratic and quartic moments match exactly and whose sixth moment does
not exceed the source sixth target. -/
theorem exists_routeKReverseTwoLevelHead_below_sixth :
    ∃ N : ℕ, 10 ≤ N ∧ ∃ a b : ℝ, 0 ≤ b ∧ b < a ∧
      ((N : ℝ) - 1) * a + b = routeKQuarticHalfMass ∧
      ((N : ℝ) - 1) * a ^ (2 : ℕ) + b ^ (2 : ℕ) =
        routeKQuarticHalfEnergy ∧
      ((N : ℝ) - 1) * a ^ (3 : ℕ) + b ^ (3 : ℕ) ≤
        normalizedPrimeArchMoment 2 / 2 ∧
      ThreeLevelSpectralFeasible routeKQuarticHalfMass
        routeKQuarticHalfEnergy a N := by
  obtain ⟨N, hN, a, b, hb, hba, hfirst, hsecond, hfeasible⟩ :=
    exists_routeKReverseTwoLevelHead
  have hNr : (10 : ℝ) ≤ N := by exact_mod_cast hN
  have hk : (9 : ℝ) ≤ (N : ℝ) - 1 := by linarith
  have ha : 0 ≤ a := le_trans hb hba.le
  have hcubic := reverseResidual_lowerBracket_of_strongHankel
    hk routeKQuarticHalfMass_pos ha hb hba.le hfirst hsecond
    routeK_sourceStrongHankel_247_243
  exact ⟨N, hN, a, b, hb, hba, hfirst, hsecond, hcubic, hfeasible⟩

end

end RHTower

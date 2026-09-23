import GaloisForLFunctions.RHTower.FiniteTwoLevelThirdMomentCeiling
import GaloisForLFunctions.RHTower.XiStrictSchwarzSixthSpectralCeiling
import GaloisForLFunctions.RHTower.ThetaGibbsSteinSourceMinor

/-!
# Finite K-RVM sixth-moment head budget

The strict source ceiling gives a finite, positive, exact quadratic/quartic
head whose sixth Hilbert--Schmidt energy is strictly above the source's sixth
target.  The sign of this gap agrees with the three-level deformation law.
-/

namespace RHTower

noncomputable section

/-- The explicit Stein enclosure leaves a strict margin in the first raw
moment-ratio defect, hence in the first prime--archimedean Hankel minor. -/
theorem normalizedPrimeArch_firstHankelMinor_pos_from_stein :
    0 < normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
      normalizedPrimeArchMoment 1 ^ (2 : ℕ) := by
  obtain ⟨_, hW1, hW2, hW3⟩ := thetaCuspFirstAtomWardMoment_stein_bounds
  let e := Real.exp (-Real.pi)
  have he : 0 < e := Real.exp_pos _
  have hrat :
      (14 : ℝ) * ((3005 / 2997) * (5457 / 500000)) ^ (2 : ℕ) <
        9 * (423 / 5000) * (441 / 200000) := by norm_num
  have hratScaled :
      14 * ((3005 / 2997 : ℝ) * ((5457 / 500000 : ℝ) * e)) ^ (2 : ℕ) <
        9 * ((423 / 5000 : ℝ) * e) * ((441 / 200000 : ℝ) * e) := by
    calc
      14 * ((3005 / 2997 : ℝ) * ((5457 / 500000 : ℝ) * e)) ^ (2 : ℕ) =
          (14 * ((3005 / 2997 : ℝ) * (5457 / 500000)) ^ (2 : ℕ)) * e ^ 2 := by ring
      _ < (9 * (423 / 5000 : ℝ) * (441 / 200000)) * e ^ 2 :=
        mul_lt_mul_of_pos_right hrat (sq_pos_of_pos he)
      _ = 9 * ((423 / 5000 : ℝ) * e) * ((441 / 200000 : ℝ) * e) := by ring
  have hWstrict :
      14 * ((3005 / 2997 : ℝ) * thetaCuspFirstAtomWardMoment 2) ^ (2 : ℕ) <
        9 * thetaCuspFirstAtomWardMoment 1 * thetaCuspFirstAtomWardMoment 3 := by
    calc
      14 * ((3005 / 2997 : ℝ) * thetaCuspFirstAtomWardMoment 2) ^ (2 : ℕ) ≤
          14 * ((3005 / 2997 : ℝ) * ((5457 / 500000 : ℝ) * e)) ^ (2 : ℕ) := by
        gcongr
        exact mul_nonneg (by norm_num) (thetaCuspFirstAtomWardMoment_nonneg 2)
      _ < 9 * ((423 / 5000 : ℝ) * e) * ((441 / 200000 : ℝ) * e) := hratScaled
      _ ≤ 9 * thetaCuspFirstAtomWardMoment 1 *
          thetaCuspFirstAtomWardMoment 3 := by
        gcongr
        nlinarith [thetaCuspFirstAtomWardMoment_nonneg 1]
  have hfirstStrict :
      14 * ((3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 2 1) ^ (2 : ℕ) <
        9 * thetaCuspAtomRawEvenMoment 1 1 *
          thetaCuspAtomRawEvenMoment 3 1 := by
    rw [thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 1,
      thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 2,
      thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 3]
    have hscaled := mul_lt_mul_of_pos_left hWstrict
      (sq_pos_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos))
    calc
      14 * ((3005 / 2997 : ℝ) *
          (2 * Real.pi * thetaCuspFirstAtomWardMoment 2)) ^ (2 : ℕ) =
          (2 * Real.pi) ^ 2 *
            (14 * ((3005 / 2997 : ℝ) * thetaCuspFirstAtomWardMoment 2) ^ 2) := by ring
      _ < (2 * Real.pi) ^ 2 *
          (9 * thetaCuspFirstAtomWardMoment 1 *
            thetaCuspFirstAtomWardMoment 3) := hscaled
      _ = 9 * (2 * Real.pi * thetaCuspFirstAtomWardMoment 1) *
          (2 * Real.pi * thetaCuspFirstAtomWardMoment 3) := by ring
  have hrawUpper :
      14 * thetaCuspRawEvenMoment 2 ^ (2 : ℕ) <
        9 * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 3 := by
    have hm2 := thetaCuspRawEvenMoment_le_first_atom_factor 2
    have hm1 := thetaCuspAtomRawEvenMoment_one_le_raw 1
    have hm3 := thetaCuspAtomRawEvenMoment_one_le_raw 3
    calc
      14 * thetaCuspRawEvenMoment 2 ^ (2 : ℕ) ≤
          14 * ((3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 2 1) ^ (2 : ℕ) := by
        gcongr
        exact thetaCuspRawEvenMoment_nonneg 2
      _ < 9 * thetaCuspAtomRawEvenMoment 1 1 *
          thetaCuspAtomRawEvenMoment 3 1 := hfirstStrict
      _ ≤ 9 * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 3 := by
        gcongr
        · exact thetaCuspAtomRawEvenMoment_nonneg 3 1
        · exact thetaCuspRawEvenMoment_nonneg 1
  have hrelaxed : ThetaCuspRelaxedFourthMomentConcentration := by
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
  have hweightUpper :
      0 < thetaCuspRawEvenMoment 0 *
        (9 * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 3 -
          14 * thetaCuspRawEvenMoment 2 ^ (2 : ℕ)) :=
    mul_pos thetaCuspRawEvenMoment_zero_pos (sub_pos.mpr hrawUpper)
  have hweightRelaxed :
      0 ≤ thetaCuspRawEvenMoment 2 *
        (45 * thetaCuspRawEvenMoment 1 ^ (2 : ℕ) -
          16 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2) := by
    rw [ThetaCuspRelaxedFourthMomentConcentration] at hrelaxed
    exact mul_nonneg (thetaCuspRawEvenMoment_nonneg 2) (sub_nonneg.mpr hrelaxed)
  have hrawCubic :
      0 < 3 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 1 *
          thetaCuspRawEvenMoment 3 +
        15 * thetaCuspRawEvenMoment 1 ^ (2 : ℕ) * thetaCuspRawEvenMoment 2 -
        10 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 ^ (2 : ℕ) := by
    nlinarith [thetaCusp_ratioSplit_exact_identity]
  have hnormalized :
      0 < 3 * thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 3 +
        15 * thetaCuspNormalizedEvenMoment 1 ^ (2 : ℕ) *
          thetaCuspNormalizedEvenMoment 2 -
        10 * thetaCuspNormalizedEvenMoment 2 ^ (2 : ℕ) := by
    have hden := pow_pos thetaCuspRawEvenMoment_zero_pos 3
    have heq :
        3 * thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 3 +
          15 * thetaCuspNormalizedEvenMoment 1 ^ (2 : ℕ) *
            thetaCuspNormalizedEvenMoment 2 -
          10 * thetaCuspNormalizedEvenMoment 2 ^ (2 : ℕ) =
        (3 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 1 *
            thetaCuspRawEvenMoment 3 +
          15 * thetaCuspRawEvenMoment 1 ^ (2 : ℕ) *
            thetaCuspRawEvenMoment 2 -
          10 * thetaCuspRawEvenMoment 0 *
            thetaCuspRawEvenMoment 2 ^ (2 : ℕ)) /
          thetaCuspRawEvenMoment 0 ^ (3 : ℕ) := by
      simp only [thetaCuspNormalizedEvenMoment]
      field_simp [thetaCuspRawEvenMoment_zero_pos.ne']
      ring
    rw [heq]
    exact div_pos hrawCubic hden
  nlinarith [normalizedPrimeArch_firstHankelMinor_scaled_eq_thetaCuspMoments]

/-- The prime--archimedean source's sixth target lies below the cubic spectral
ceiling of its quartic target. -/
theorem routeKHalfSixth_sq_lt_halfFourth_cube :
    (normalizedPrimeArchMoment 2 / 2) ^ (2 : ℕ) <
      routeKQuarticHalfEnergy ^ (3 : ℕ) := by
  have h := normalizedPrimeArchMoment_strict_sixth_spectral_ceiling
  rw [routeKQuarticHalfEnergy,
    routeKSourceFirstMoment_eq_normalizedPrimeArchMoment]
  nlinarith

/-- There is a finite positive two-level head with the exact K-RVM second and
fourth source moments and a strict sixth-moment surplus. -/
theorem exists_routeKFiniteHead_sixth_surplus :
    ∃ N : ℕ, 3 ≤ N ∧
      routeKQuarticHalfMass ^ (2 : ℕ) / N < routeKQuarticHalfEnergy ∧
      normalizedPrimeArchMoment 2 / 2 <
        twoLevelLarge routeKQuarticHalfMass routeKQuarticHalfEnergy N ^ (3 : ℕ) +
          ((N : ℝ) - 1) *
            twoLevelSmall routeKQuarticHalfMass routeKQuarticHalfEnergy N ^ (3 : ℕ) := by
  have hhigh : routeKQuarticHalfEnergy ≤ routeKQuarticHalfMass ^ (2 : ℕ) := by
    have hgap := routeKQuarticGap_pos
    unfold routeKQuarticGap at hgap
    linarith
  exact exists_twoLevelThirdMoment_gt_of_strict_ceiling
    routeKQuarticHalfMass_pos routeKQuarticHalfEnergy_pos hhigh
    (div_nonneg normalizedPrimeArchMoment_two_pos.le (by norm_num))
    routeKHalfSixth_sq_lt_halfFourth_cube

end

end RHTower

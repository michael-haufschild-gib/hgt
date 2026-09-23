import GaloisForLFunctions.RHTower.PrimeArchThetaSingleGibbsGammaCoordinate

/-!
# Rational enclosure gate for the first theta-cusp Gibbs certificate

This file replaces the two analytic certificate inequalities by one finite list of rational
enclosures for the first nine moments of the single positive Gibbs density and for `exp (-π)`.
The implication is exact: the stated boxes force both the Morse--Fisher certificate and its
relaxed companion, and hence the complete linear prime--archimedean trace-Hankel block.

The theorem deliberately separates exact algebra from certified quadrature.  No numerical
approximation is installed as an axiom: producing the enclosures remains an analytic theorem.
-/

open Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- A finite rational enclosure package for the moments needed by the first-atom Gibbs
certificate. -/
structure ThetaCuspFirstAtomSingleGibbsRationalMomentEnclosure : Prop where
  exp_neg_pi_lower : (0.0432139182637 : ℝ) ≤ Real.exp (-Real.pi)
  exp_neg_pi_upper : Real.exp (-Real.pi) ≤ (0.0432139182638 : ℝ)
  moment_zero_lower :
    (0.0073359406266 : ℝ) ≤ thetaCuspLiouvilleGibbsMoment 0 1
  moment_zero_upper :
    thetaCuspLiouvilleGibbsMoment 0 1 ≤ (0.0073359406267 : ℝ)
  moment_one_lower :
    (0.0009673899917 : ℝ) ≤ thetaCuspLiouvilleGibbsMoment 1 1
  moment_one_upper :
    thetaCuspLiouvilleGibbsMoment 1 1 ≤ (0.0009673899918 : ℝ)
  moment_two_lower :
    (0.0002135451243 : ℝ) ≤ thetaCuspLiouvilleGibbsMoment 2 1
  moment_two_upper :
    thetaCuspLiouvilleGibbsMoment 2 1 ≤ (0.0002135451244 : ℝ)
  moment_three_lower :
    (0.00006158723110 : ℝ) ≤ thetaCuspLiouvilleGibbsMoment 3 1
  moment_three_upper :
    thetaCuspLiouvilleGibbsMoment 3 1 ≤ (0.00006158723112 : ℝ)
  moment_four_lower :
    (0.00002114705517 : ℝ) ≤ thetaCuspLiouvilleGibbsMoment 4 1
  moment_four_upper :
    thetaCuspLiouvilleGibbsMoment 4 1 ≤ (0.00002114705518 : ℝ)
  moment_five_lower :
    (0.00000824395875 : ℝ) ≤ thetaCuspLiouvilleGibbsMoment 5 1
  moment_five_upper :
    thetaCuspLiouvilleGibbsMoment 5 1 ≤ (0.00000824395876 : ℝ)
  moment_six_lower :
    (0.00000354662642 : ℝ) ≤ thetaCuspLiouvilleGibbsMoment 6 1
  moment_six_upper :
    thetaCuspLiouvilleGibbsMoment 6 1 ≤ (0.00000354662643 : ℝ)
  moment_seven_lower :
    (0.00000165261304 : ℝ) ≤ thetaCuspLiouvilleGibbsMoment 7 1
  moment_seven_upper :
    thetaCuspLiouvilleGibbsMoment 7 1 ≤ (0.00000165261305 : ℝ)
  moment_eight_lower :
    (0.00000082318420 : ℝ) ≤ thetaCuspLiouvilleGibbsMoment 8 1
  moment_eight_upper :
    thetaCuspLiouvilleGibbsMoment 8 1 ≤ (0.00000082318421 : ℝ)

/-- A rational interval for the only non-moment coefficient in the Morse--Fisher envelope. -/
theorem thetaCuspFirstAtomMorseFisherDecayFactor_rationalBounds :
    (0.91374677920 : ℝ) < thetaCuspFirstAtomMorseFisherDecayFactor ∧
      thetaCuspFirstAtomMorseFisherDecayFactor < (0.91374677923 : ℝ) := by
  have hden : 0 < Real.pi - 3 / 2 := by nlinarith [Real.pi_gt_three]
  rw [thetaCuspFirstAtomMorseFisherDecayFactor]
  constructor
  · rw [lt_div_iff₀ hden]
    nlinarith [Real.pi_lt_d20]
  · rw [div_lt_iff₀ hden]
    nlinarith [Real.pi_gt_d20]

/-- The rational moment enclosure forces both low-degree Gibbs certificates. -/
theorem thetaCuspFirstAtomSingleGibbsLowDegreeCertificate_of_rationalMomentEnclosure
    (h : ThetaCuspFirstAtomSingleGibbsRationalMomentEnclosure) :
    ThetaCuspFirstAtomSingleGibbsLowDegreeCertificate := by
  let L : ℕ → ℝ := fun m => thetaCuspLiouvilleGibbsMoment m 1
  let A : ℝ := thetaCuspFirstAtomMorseFisherDecayFactor
  let J0 : ℝ := 4 * L 1 - L 2
  let J1 : ℝ := 8 * L 3 - L 4
  let C : ℝ := 8 * L 3 - 6 * L 4 + (1 / 2 : ℝ) * L 5
  let B : ℝ := 3 * L 1 + (21 / 4 : ℝ) * L 2 -
    (25 / 8 : ℝ) * L 4 - (15 / 4 : ℝ) * L 5 + (39 / 16 : ℝ) * L 6
  let D : ℝ := 6 * L 4 - 18 * L 5 + (51 / 2 : ℝ) * L 6 -
    15 * L 7 + 3 * L 8
  let U : ℝ := B + A * D
  let E0 : ℝ := 2 * Real.exp (-Real.pi) - L 0
  have hA := thetaCuspFirstAtomMorseFisherDecayFactor_rationalBounds
  have hApos : 0 ≤ A := by
    dsimp [A]
    linarith [hA.1]
  have hJ0lo : (0.0036560148424 : ℝ) ≤ J0 := by
    dsimp [J0, L]
    linarith [h.moment_one_lower, h.moment_two_upper]
  have hJ0pos : 0 ≤ J0 := le_trans (by norm_num) hJ0lo
  have hJ1lo : (0.00047155079362 : ℝ) ≤ J1 := by
    dsimp [J1, L]
    linarith [h.moment_three_lower, h.moment_four_upper]
  have hJ1hi : J1 ≤ (0.00047155079379 : ℝ) := by
    dsimp [J1, L]
    linarith [h.moment_three_upper, h.moment_four_lower]
  have hJ1pos : 0 ≤ J1 := le_trans (by norm_num) hJ1lo
  have hClo : (0.000369937497095 : ℝ) ≤ C := by
    dsimp [C, L]
    linarith [h.moment_three_lower, h.moment_four_upper, h.moment_five_lower]
  have hCpos : 0 ≤ C := le_trans (by norm_num) hClo
  have hBhi : B ≤ (0.003934927387704375 : ℝ) := by
    dsimp [B, L]
    linarith [h.moment_one_upper, h.moment_two_upper, h.moment_four_lower,
      h.moment_five_lower, h.moment_six_upper]
  have hBlo : (0.0039 : ℝ) ≤ B := by
    dsimp [B, L]
    linarith [h.moment_one_lower, h.moment_two_lower, h.moment_four_upper,
      h.moment_five_upper, h.moment_six_lower]
  have hDlo : (0.000046610403900 : ℝ) ≤ D := by
    dsimp [D, L]
    linarith [h.moment_four_lower, h.moment_five_upper, h.moment_six_lower,
      h.moment_seven_upper, h.moment_eight_lower]
  have hDhi : D ≤ (0.000046610404575 : ℝ) := by
    dsimp [D, L]
    linarith [h.moment_four_upper, h.moment_five_lower, h.moment_six_upper,
      h.moment_seven_lower, h.moment_eight_upper]
  have hDpos : 0 ≤ D := le_trans (by norm_num) hDlo
  have hAUhi : A * D ≤
      (0.91374677923 : ℝ) * (0.000046610404575 : ℝ) := by
    exact mul_le_mul hA.2.le hDhi hDpos (by norm_num)
  have hUhi : U ≤ (0.00397751749476338850697725 : ℝ) := by
    dsimp [U]
    linarith [hBhi, hAUhi]
  have hUpos : 0 ≤ U := by
    dsimp [U]
    exact add_nonneg (le_trans (by norm_num) hBlo) (mul_nonneg hApos hDpos)
  have hE0hi : E0 ≤ (0.0790918959010 : ℝ) := by
    dsimp [E0, L]
    linarith [h.exp_neg_pi_upper, h.moment_zero_lower]
  have hE0pos : 0 ≤ E0 := by
    dsimp [E0, L]
    linarith [h.exp_neg_pi_lower, h.moment_zero_upper]
  have hUeq :
      thetaCuspFirstRadialQuadraticMorseSingleGibbsUpperValue = U := by
    dsimp [thetaCuspFirstRadialQuadraticMorseSingleGibbsUpperValue,
      U, B, D, A, L]
    ring
  rw [ThetaCuspFirstAtomSingleGibbsLowDegreeCertificate,
    ThetaCuspFirstAtomSingleGibbsMorseCertificate,
    ThetaCuspFirstAtomSingleGibbsRelaxedCertificate]
  constructor
  · rw [hUeq]
    change (14 * (3005 / 2997 : ℝ) ^ (2 : ℕ) - 9) * J1 ^ (2 : ℕ) * U ≤
      9 * J0 * C ^ (2 : ℕ)
    calc
      (14 * (3005 / 2997 : ℝ) ^ (2 : ℕ) - 9) * J1 ^ (2 : ℕ) * U ≤
          (14 * (3005 / 2997 : ℝ) ^ (2 : ℕ) - 9) *
            (0.00047155079379 : ℝ) ^ (2 : ℕ) *
              (0.00397751749476338850697725 : ℝ) := by
            gcongr
      _ ≤ 9 * (0.0036560148424 : ℝ) *
          (0.000369937497095 : ℝ) ^ (2 : ℕ) := by norm_num
      _ ≤ 9 * J0 * C ^ (2 : ℕ) := by gcongr
  · change 16 * ((3005 / 2997 : ℝ) * E0) *
      ((3005 / 2997 : ℝ) * J1) ≤ 45 * J0 ^ (2 : ℕ)
    calc
      16 * ((3005 / 2997 : ℝ) * E0) *
          ((3005 / 2997 : ℝ) * J1) ≤
          16 * ((3005 / 2997 : ℝ) * (0.0790918959010 : ℝ)) *
            ((3005 / 2997 : ℝ) * (0.00047155079379 : ℝ)) := by
              gcongr
      _ ≤ 45 * (0.0036560148424 : ℝ) ^ (2 : ℕ) := by norm_num
      _ ≤ 45 * J0 ^ (2 : ℕ) := by gcongr

/-- The finite rational enclosure is already sufficient for every linear source trace-Hankel
test. -/
theorem forall_primeArchSourceTraceHankel_linear_nonneg_of_singleGibbsRationalMomentEnclosure
    (h : ThetaCuspFirstAtomSingleGibbsRationalMomentEnclosure) :
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re :=
  forall_primeArchSourceTraceHankel_linear_nonneg_of_singleGibbsLowDegreeCertificate
    (thetaCuspFirstAtomSingleGibbsLowDegreeCertificate_of_rationalMomentEnclosure h)

end

end RHTower

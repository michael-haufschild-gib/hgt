import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesSquaredCompactMarkovCandidate
import GaloisForLFunctions.RHTower.CriticalHalfApertureJacobiGammaRecovery
import GaloisForLFunctions.RHTower.XiOrderFourteenCornerSourceExclusion
import GaloisForLFunctions.RHTower.ThetaCuspCassiniMarkovBoundaryTransport

/-!
# Critical raw Stokes mass no-go

The P-G71 square-pushforward has the correct positive compact geometry, but hostile zeroth-moment
testing rules out its raw critical normalization.  Four atoms suffice: depths zero and one over
primes two and three already have total mass larger than the entire completed seam mass.

The positive survivor is quantitative.  Any completed Gamma/polar weld of this carrier must carry
a strictly negative central mass correction; positive orthogonal completion and scalar-free direct
identification are impossible.
-/

open Complex Filter Function MeasureTheory Set TopologicalSpace
open scoped BigOperators ENNReal Topology

noncomputable section
namespace RHTower

abbrev gammaSewnMobiusApertureStokesPrimeTwo : Nat.Primes :=
  ⟨2, by norm_num⟩

abbrev gammaSewnMobiusApertureStokesPrimeThree : Nat.Primes :=
  ⟨3, by norm_num⟩

private theorem gammaSewnMobiusApertureStokesCriticalSquaredWeight_eq
    (p : Nat.Primes) (e : ℕ) :
    gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) (p, e) =
      2 * gammaSewnMobiusValuationContractionMultiplier (1 / 2) p ^ 2 *
        (xiTransversePrimeApertureDiskNode 1 p /
          (1 + xiTransversePrimeApertureDiskNode 1 p)) ^ 2 *
        (1 - xiMobiusContinuousApertureDiskNode (1 / 2) p) ^ 2 *
        xiMobiusContinuousApertureDiskNode (1 / 2) p ^ e /
        (((e + 1 : ℕ) : ℝ) ^ 2 * Real.log (p : ℝ) *
          xiMobiusContinuousApertureDiskNode (1 / 2) p) := by
  let c := gammaSewnMobiusValuationContractionMultiplier (1 / 2) p
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode (1 / 2) p
  have hc : c ≠ 0 :=
    (gammaSewnMobiusValuationContractionMultiplier_pos (1 / 2) p).ne'
  have hq : q ≠ 0 := (xiTransversePrimeApertureDiskNode_pos 1 p).ne'
  have hq1 : 1 + q ≠ 0 := by
    linarith [xiTransversePrimeApertureDiskNode_pos 1 p]
  have hr : r ≠ 0 := (xiMobiusContinuousApertureDiskNode_pos (1 / 2) p).ne'
  have hr1 : 1 - r ≠ 0 := sub_ne_zero.mpr
    (xiMobiusContinuousApertureDiskNode_lt_one (by norm_num) p).ne'
  have hlog : Real.log (p : ℝ) ≠ 0 := by
    exact (Real.log_pos (by exact_mod_cast p.2.one_lt)).ne'
  have he : (e : ℝ) + 1 ≠ 0 := by positivity
  rw [gammaSewnMobiusApertureStokesSquaredWeight,
    gammaSewnMobiusApertureStokesReflectedWeight,
    gammaSewnMobiusApertureStokesDualFeatureCoefficient,
    gammaSewnMobiusApertureStokesGap,
    gammaSewnMobiusApertureStokesInverseTilt,
    gammaSewnMobiusContinuousApertureFeature,
    xiMobiusPrimeSchurContinuousForwardDifference_eq_geometric]
  simp only [Nat.cast_add, Nat.cast_one]
  change 2 * ((c * (q / (1 + q) * (1 - r) * r ^ e) /
      ((e : ℝ) + 1)) /
      (((e : ℝ) + 1) *
        (Real.log (p : ℝ) * r / (c * (q / (1 + q)) * (1 - r))))) =
    2 * c ^ 2 * (q / (1 + q)) ^ 2 * (1 - r) ^ 2 * r ^ e /
      (((e : ℝ) + 1) ^ 2 * Real.log (p : ℝ) * r)
  field_simp [hc, hq, hq1, hr, hr1, hlog, he]

private theorem four_fifths_lt_gammaSewnMobiusValuationContractionMultiplier_half
    (p : Nat.Primes)
    (hqhalf : (1 / 2 : ℝ) ≤ xiMobiusContinuousApertureDiskNode (1 / 2) p) :
    (4 / 5 : ℝ) < gammaSewnMobiusValuationContractionMultiplier (1 / 2) p := by
  let q := xiMobiusContinuousApertureDiskNode (1 / 2) p
  let c := gammaSewnMobiusValuationContractionMultiplier (1 / 2) p
  have hq0 : 0 < q := xiMobiusContinuousApertureDiskNode_pos (1 / 2) p
  have hq1 : q < 1 := xiMobiusContinuousApertureDiskNode_lt_one (by norm_num) p
  have hden : 0 < 8 * (1 + q ^ 4) := by positivity
  have hq2 : (1 / 4 : ℝ) ≤ q ^ 2 := by nlinarith
  have hq4q3 : q ^ 4 ≤ q ^ 3 := by
    nlinarith [mul_nonneg (pow_nonneg hq0.le 3) (sub_nonneg.mpr hq1.le)]
  have hc4 : (4 / 5 : ℝ) ^ 4 < c ^ 4 := by
    rw [gammaSewnMobiusValuationContractionMultiplier_pow_four]
    change (4 / 5 : ℝ) ^ 4 < (1 + q) ^ 4 / (8 * (1 + q ^ 4))
    rw [lt_div_iff₀ hden]
    norm_num
    nlinarith
  have hc0 : 0 < c := gammaSewnMobiusValuationContractionMultiplier_pos (1 / 2) p
  by_contra h
  have hc : c ≤ 4 / 5 := le_of_not_gt h
  have hc2 : c ^ 2 ≤ (4 / 5 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc)
      (add_nonneg hc0.le (by norm_num : (0 : ℝ) ≤ 4 / 5))]
  have hc4le : c ^ 4 ≤ (4 / 5 : ℝ) ^ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2)
      (add_nonneg (sq_nonneg c) (sq_nonneg (4 / 5 : ℝ)))]
  linarith

private theorem gammaSewnMobiusApertureStokesPrimeTwo_half_node_bounds :
    (1 / 2 : ℝ) <
        xiMobiusContinuousApertureDiskNode (1 / 2)
          gammaSewnMobiusApertureStokesPrimeTwo ∧
      xiMobiusContinuousApertureDiskNode (1 / 2)
          gammaSewnMobiusApertureStokesPrimeTwo < 5 / 7 := by
  let r := xiMobiusContinuousApertureDiskNode (1 / 2)
    gammaSewnMobiusApertureStokesPrimeTwo
  have hr0 : 0 < r := xiMobiusContinuousApertureDiskNode_pos _ _
  have hr2 : r ^ 2 = 1 / 2 := by
    simpa [r, xiTransversePrimeApertureDiskNode_one_eq_inv] using
      xiMobiusContinuousApertureDiskNode_half_sq
        gammaSewnMobiusApertureStokesPrimeTwo
  constructor
  · by_contra h
    have hr : r ≤ 1 / 2 := le_of_not_gt h
    nlinarith [mul_nonneg (sub_nonneg.mpr hr)
      (add_nonneg hr0.le (by norm_num : (0 : ℝ) ≤ 1 / 2))]
  · by_contra h
    have hr : 5 / 7 ≤ r := le_of_not_gt h
    nlinarith [mul_nonneg (sub_nonneg.mpr hr)
      (add_nonneg hr0.le (by norm_num : (0 : ℝ) ≤ 5 / 7))]

private theorem gammaSewnMobiusApertureStokesPrimeThree_half_node_bounds :
    (1 / 2 : ℝ) <
        xiMobiusContinuousApertureDiskNode (1 / 2)
          gammaSewnMobiusApertureStokesPrimeThree ∧
      xiMobiusContinuousApertureDiskNode (1 / 2)
          gammaSewnMobiusApertureStokesPrimeThree < 3 / 5 := by
  let r := xiMobiusContinuousApertureDiskNode (1 / 2)
    gammaSewnMobiusApertureStokesPrimeThree
  have hr0 : 0 < r := xiMobiusContinuousApertureDiskNode_pos _ _
  have hr2 : r ^ 2 = 1 / 3 := by
    simpa [r, xiTransversePrimeApertureDiskNode_one_eq_inv] using
      xiMobiusContinuousApertureDiskNode_half_sq
        gammaSewnMobiusApertureStokesPrimeThree
  constructor
  · by_contra h
    have hr : r ≤ 1 / 2 := le_of_not_gt h
    nlinarith [mul_nonneg (sub_nonneg.mpr hr)
      (add_nonneg hr0.le (by norm_num : (0 : ℝ) ≤ 1 / 2))]
  · by_contra h
    have hr : 3 / 5 ≤ r := le_of_not_gt h
    nlinarith [mul_nonneg (sub_nonneg.mpr hr)
      (add_nonneg hr0.le (by norm_num : (0 : ℝ) ≤ 3 / 5))]

theorem gammaSewnMobiusApertureStokesCriticalPrimeTwoDepthZero_lower :
    (256 / 11025 : ℝ) <
      gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
        (gammaSewnMobiusApertureStokesPrimeTwo, 0) := by
  let p := gammaSewnMobiusApertureStokesPrimeTwo
  let r := xiMobiusContinuousApertureDiskNode (1 / 2) p
  let c := gammaSewnMobiusValuationContractionMultiplier (1 / 2) p
  have hr := gammaSewnMobiusApertureStokesPrimeTwo_half_node_bounds
  have hc : (4 / 5 : ℝ) < c :=
    four_fifths_lt_gammaSewnMobiusValuationContractionMultiplier_half p hr.1.le
  have hc2 : (16 / 25 : ℝ) < c ^ 2 := by nlinarith [sq_nonneg (c - 4 / 5)]
  have hgap : (4 / 49 : ℝ) < (1 - r) ^ 2 := by nlinarith [sq_nonneg (r - 5 / 7)]
  have hprod : (64 / 1225 : ℝ) < c ^ 2 * (1 - r) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hc2) (sub_pos.mpr hgap)]
  have hlog : Real.log 2 < 7 / 10 := Real.log_two_lt_d9.trans (by norm_num)
  have hdenpos : 0 < Real.log 2 * r :=
    mul_pos (Real.log_pos (by norm_num))
      (xiMobiusContinuousApertureDiskNode_pos _ _)
  have hden : Real.log 2 * r < 1 / 2 := by
    calc
      Real.log 2 * r < (7 / 10 : ℝ) * r :=
        mul_lt_mul_of_pos_right hlog
          (xiMobiusContinuousApertureDiskNode_pos _ _)
      _ < (7 / 10 : ℝ) * (5 / 7) := mul_lt_mul_of_pos_left hr.2 (by norm_num)
      _ = 1 / 2 := by norm_num
  rw [gammaSewnMobiusApertureStokesCriticalSquaredWeight_eq]
  simp only [gammaSewnMobiusApertureStokesPrimeTwo,
    xiTransversePrimeApertureDiskNode_one_eq_inv]
  norm_num only [Nat.cast_ofNat, invOf_eq_inv, pow_zero, mul_one, Nat.reduceAdd,
    Nat.cast_one, one_pow]
  simp only [one_mul]
  change (256 / 11025 : ℝ) < 2 * c ^ 2 * (1 / 9) * (1 - r) ^ 2 /
    (Real.log 2 * r)
  rw [lt_div_iff₀ hdenpos]
  nlinarith

theorem gammaSewnMobiusApertureStokesCriticalPrimeThreeDepthZero_lower :
    (16 / 825 : ℝ) <
      gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
        (gammaSewnMobiusApertureStokesPrimeThree, 0) := by
  let p := gammaSewnMobiusApertureStokesPrimeThree
  let r := xiMobiusContinuousApertureDiskNode (1 / 2) p
  let c := gammaSewnMobiusValuationContractionMultiplier (1 / 2) p
  have hr := gammaSewnMobiusApertureStokesPrimeThree_half_node_bounds
  have hc : (4 / 5 : ℝ) < c :=
    four_fifths_lt_gammaSewnMobiusValuationContractionMultiplier_half p hr.1.le
  have hc2 : (16 / 25 : ℝ) < c ^ 2 := by nlinarith [sq_nonneg (c - 4 / 5)]
  have hgap : (4 / 25 : ℝ) < (1 - r) ^ 2 := by nlinarith [sq_nonneg (r - 3 / 5)]
  have hprod : (64 / 625 : ℝ) < c ^ 2 * (1 - r) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hc2) (sub_pos.mpr hgap)]
  have hlog : Real.log 3 < 11 / 10 := Real.log_three_lt_d9.trans (by norm_num)
  have hdenpos : 0 < Real.log 3 * r :=
    mul_pos (Real.log_pos (by norm_num))
      (xiMobiusContinuousApertureDiskNode_pos _ _)
  have hden : Real.log 3 * r < 33 / 50 := by
    calc
      Real.log 3 * r < (11 / 10 : ℝ) * r :=
        mul_lt_mul_of_pos_right hlog
          (xiMobiusContinuousApertureDiskNode_pos _ _)
      _ < (11 / 10 : ℝ) * (3 / 5) := mul_lt_mul_of_pos_left hr.2 (by norm_num)
      _ = 33 / 50 := by norm_num
  rw [gammaSewnMobiusApertureStokesCriticalSquaredWeight_eq]
  simp only [gammaSewnMobiusApertureStokesPrimeThree,
    xiTransversePrimeApertureDiskNode_one_eq_inv]
  norm_num only [Nat.cast_ofNat, invOf_eq_inv, pow_zero, mul_one, Nat.reduceAdd,
    Nat.cast_one, one_pow]
  simp only [one_mul]
  change (16 / 825 : ℝ) < 2 * c ^ 2 * (1 / 16) * (1 - r) ^ 2 /
    (Real.log 3 * r)
  rw [lt_div_iff₀ hdenpos]
  nlinarith

/-- The first critical Stokes gap is bounded above by source rational data. -/
theorem gammaSewnMobiusApertureStokesCriticalPrimeTwoDepthZero_gap_lt :
    gammaSewnMobiusApertureStokesGap (1 / 2)
        (gammaSewnMobiusApertureStokesPrimeTwo, 0) < 105 / 16 := by
  let p := gammaSewnMobiusApertureStokesPrimeTwo
  let r := xiMobiusContinuousApertureDiskNode (1 / 2) p
  let c := gammaSewnMobiusValuationContractionMultiplier (1 / 2) p
  have hr := gammaSewnMobiusApertureStokesPrimeTwo_half_node_bounds
  have hc : (4 / 5 : ℝ) < c :=
    four_fifths_lt_gammaSewnMobiusValuationContractionMultiplier_half p hr.1.le
  have hrgap : (2 / 7 : ℝ) < 1 - r := by linarith
  have hcr : (8 / 35 : ℝ) < c * (1 - r) := by
    nlinarith [mul_pos (sub_pos.mpr hc) (sub_pos.mpr hrgap)]
  have hsourceDen : (8 / 105 : ℝ) < c * (1 / 3) * (1 - r) := by
    nlinarith
  have hdenpos : 0 < c * (1 / 3) * (1 - r) := by linarith
  have hlog : Real.log 2 < 7 / 10 := Real.log_two_lt_d9.trans (by norm_num)
  have hnum : Real.log 2 * r < 1 / 2 := by
    calc
      Real.log 2 * r < (7 / 10 : ℝ) * r :=
        mul_lt_mul_of_pos_right hlog
          (xiMobiusContinuousApertureDiskNode_pos _ _)
      _ < (7 / 10 : ℝ) * (5 / 7) := mul_lt_mul_of_pos_left hr.2 (by norm_num)
      _ = 1 / 2 := by norm_num
  rw [gammaSewnMobiusApertureStokesGap,
    gammaSewnMobiusApertureStokesInverseTilt]
  simp only [gammaSewnMobiusApertureStokesPrimeTwo,
    xiTransversePrimeApertureDiskNode_one_eq_inv]
  norm_num only [Nat.cast_ofNat, invOf_eq_inv, Nat.reduceAdd, Nat.cast_one,
    one_mul]
  change Real.log 2 * r / (c * (1 / 3) * (1 - r)) < 105 / 16
  rw [div_lt_iff₀ hdenpos]
  nlinarith

/-- Consequently the first squared reciprocal-gap node has a rational floor. -/
theorem gammaSewnMobiusApertureStokesCriticalPrimeTwoDepthZero_node_lower :
    (256 / 11025 : ℝ) <
      gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2)
        (gammaSewnMobiusApertureStokesPrimeTwo, 0) := by
  let g := gammaSewnMobiusApertureStokesGap (1 / 2)
    (gammaSewnMobiusApertureStokesPrimeTwo, 0)
  have hg0 : 0 < g := gammaSewnMobiusApertureStokesGap_pos (by norm_num) _
  have hg : g < 105 / 16 :=
    gammaSewnMobiusApertureStokesCriticalPrimeTwoDepthZero_gap_lt
  have hinv : (16 / 105 : ℝ) < g⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ hg0]
    nlinarith [mul_lt_mul_of_pos_left hg (by norm_num : (0 : ℝ) < 16 / 105)]
  rw [gammaSewnMobiusApertureStokesSquaredReciprocalGapNode,
    gammaSewnMobiusApertureStokesReciprocalGapNode]
  change (256 / 11025 : ℝ) < g⁻¹ ^ 2
  nlinarith [sq_nonneg (g⁻¹ - 16 / 105)]

private theorem gammaSewnMobiusApertureStokesCriticalSquaredWeight_depthOne_eq
    (p : Nat.Primes) :
    gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) (p, 1) =
      xiMobiusContinuousApertureDiskNode (1 / 2) p / 4 *
        gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) (p, 0) := by
  rw [gammaSewnMobiusApertureStokesCriticalSquaredWeight_eq,
    gammaSewnMobiusApertureStokesCriticalSquaredWeight_eq]
  have hr := (xiMobiusContinuousApertureDiskNode_pos (1 / 2) p).ne'
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hlog := (Real.log_pos hp).ne'
  norm_num
  field_simp [hr, hlog]

theorem gammaSewnMobiusApertureStokesCriticalFourAtomMass_lower :
    (29 / 625 : ℝ) <
      gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
          (gammaSewnMobiusApertureStokesPrimeTwo, 0) +
        gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
          (gammaSewnMobiusApertureStokesPrimeTwo, 1) +
        gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
          (gammaSewnMobiusApertureStokesPrimeThree, 0) +
        gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
          (gammaSewnMobiusApertureStokesPrimeThree, 1) := by
  let f20 := gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
    (gammaSewnMobiusApertureStokesPrimeTwo, 0)
  let f21 := gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
    (gammaSewnMobiusApertureStokesPrimeTwo, 1)
  let f30 := gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
    (gammaSewnMobiusApertureStokesPrimeThree, 0)
  let f31 := gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
    (gammaSewnMobiusApertureStokesPrimeThree, 1)
  have h20 : (256 / 11025 : ℝ) < f20 :=
    gammaSewnMobiusApertureStokesCriticalPrimeTwoDepthZero_lower
  have h30 : (16 / 825 : ℝ) < f30 :=
    gammaSewnMobiusApertureStokesCriticalPrimeThreeDepthZero_lower
  have hr2 := gammaSewnMobiusApertureStokesPrimeTwo_half_node_bounds.1
  have hr3 := gammaSewnMobiusApertureStokesPrimeThree_half_node_bounds.1
  have hf20 : 0 < f20 := gammaSewnMobiusApertureStokesSquaredWeight_pos (by norm_num) _
  have hf30 : 0 < f30 := gammaSewnMobiusApertureStokesSquaredWeight_pos (by norm_num) _
  have h21eq : f21 =
      xiMobiusContinuousApertureDiskNode (1 / 2)
        gammaSewnMobiusApertureStokesPrimeTwo / 4 * f20 :=
    gammaSewnMobiusApertureStokesCriticalSquaredWeight_depthOne_eq _
  have h31eq : f31 =
      xiMobiusContinuousApertureDiskNode (1 / 2)
        gammaSewnMobiusApertureStokesPrimeThree / 4 * f30 :=
    gammaSewnMobiusApertureStokesCriticalSquaredWeight_depthOne_eq _
  have h21 : (1 / 8 : ℝ) * f20 < f21 := by
    rw [h21eq]
    nlinarith [mul_pos (sub_pos.mpr hr2) hf20]
  have h31 : (1 / 8 : ℝ) * f30 < f31 := by
    rw [h31eq]
    nlinarith [mul_pos (sub_pos.mpr hr3) hf30]
  change (29 / 625 : ℝ) < f20 + f21 + f30 + f31
  nlinarith

/-- Four raw critical source atoms exceed the whole completed seam zeroth moment. -/
theorem normalizedPrimeArchMoment_zero_lt_gammaSewnMobiusApertureStokesCriticalFourAtomMass :
    normalizedPrimeArchMoment 0 <
      gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
          (gammaSewnMobiusApertureStokesPrimeTwo, 0) +
        gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
          (gammaSewnMobiusApertureStokesPrimeTwo, 1) +
        gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
          (gammaSewnMobiusApertureStokesPrimeThree, 0) +
        gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
          (gammaSewnMobiusApertureStokesPrimeThree, 1) :=
  normalizedPrimeArchMoment_zero_lt_twentyNine_over_sixHundredTwentyFive.trans
    gammaSewnMobiusApertureStokesCriticalFourAtomMass_lower

/-- The full raw critical squared carrier has too much mass to represent the completed source. -/
theorem normalizedPrimeArchMoment_zero_lt_integral_criticalSquaredCompactCarrier :
    normalizedPrimeArchMoment 0 <
      ∫ y : ℝ, y ^ 0 ∂gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier := by
  rw [gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier,
    integral_pow_gammaSewnMobiusApertureStokesSquaredCompactCarrier_eq_tsum (by norm_num)]
  simp only [pow_zero, mul_one]
  let S : Finset (Nat.Primes × ℕ) :=
    {(gammaSewnMobiusApertureStokesPrimeTwo, 0),
      (gammaSewnMobiusApertureStokesPrimeTwo, 1),
      (gammaSewnMobiusApertureStokesPrimeThree, 0),
      (gammaSewnMobiusApertureStokesPrimeThree, 1)}
  have hsum := summable_gammaSewnMobiusApertureStokesSquaredWeight
    (s := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hle := hsum.sum_le_tsum S (fun pk _ =>
    (gammaSewnMobiusApertureStokesSquaredWeight_pos (by norm_num) pk).le)
  have hfinite :
      gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
          (gammaSewnMobiusApertureStokesPrimeTwo, 0) +
        gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
          (gammaSewnMobiusApertureStokesPrimeTwo, 1) +
        gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
          (gammaSewnMobiusApertureStokesPrimeThree, 0) +
        gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
          (gammaSewnMobiusApertureStokesPrimeThree, 1) ≤
        ∑' pk : Nat.Primes × ℕ,
          gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) pk := by
    have hpne : gammaSewnMobiusApertureStokesPrimeTwo ≠
        gammaSewnMobiusApertureStokesPrimeThree := by
      intro h
      have := congrArg Subtype.val h
      norm_num at this
    simpa [S, hpne, add_assoc, add_comm, add_left_comm] using hle
  exact normalizedPrimeArchMoment_zero_lt_gammaSewnMobiusApertureStokesCriticalFourAtomMass.trans_le
    hfinite

/-- The first prime-two atom alone also exceeds the complete first seam moment. -/
theorem normalizedPrimeArchMoment_one_lt_integral_criticalSquaredCompactCarrier :
    normalizedPrimeArchMoment 1 <
      ∫ y : ℝ, y ^ 1 ∂gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier := by
  rw [gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier,
    integral_pow_gammaSewnMobiusApertureStokesSquaredCompactCarrier_eq_tsum (by norm_num)]
  simp only [pow_one]
  let f := fun pk : Nat.Primes × ℕ =>
    gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) pk *
      gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2) pk
  have hfnonneg : ∀ pk, 0 ≤ f pk := fun pk => mul_nonneg
    (gammaSewnMobiusApertureStokesSquaredWeight_pos (by norm_num) pk).le
    (gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_pos (by norm_num) pk).le
  have hfsum : Summable f := by
    refine Summable.of_nonneg_of_le hfnonneg (fun pk => ?_)
      ((summable_gammaSewnMobiusApertureStokesSquaredWeight
        (s := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left
          (((Real.log 2)⁻¹) ^ 2))
    have hw := (gammaSewnMobiusApertureStokesSquaredWeight_pos
      (s := (1 / 2 : ℝ)) (by norm_num) pk).le
    have hn := gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_le
      (s := (1 / 2 : ℝ)) (by norm_num) (by norm_num) pk
    dsimp only [f]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hn hw
  have hselected :
      gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
          (gammaSewnMobiusApertureStokesPrimeTwo, 0) *
        gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2)
          (gammaSewnMobiusApertureStokesPrimeTwo, 0) ≤ ∑' pk, f pk := by
    have hle := hfsum.sum_le_tsum
      ({(gammaSewnMobiusApertureStokesPrimeTwo, 0)} : Finset (Nat.Primes × ℕ))
      (fun pk _ => hfnonneg pk)
    simpa only [Finset.sum_singleton] using hle
  have hatom : (9 / 50000 : ℝ) <
      gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
          (gammaSewnMobiusApertureStokesPrimeTwo, 0) *
        gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2)
          (gammaSewnMobiusApertureStokesPrimeTwo, 0) := by
    have hw := gammaSewnMobiusApertureStokesCriticalPrimeTwoDepthZero_lower
    have hn := gammaSewnMobiusApertureStokesCriticalPrimeTwoDepthZero_node_lower
    have hprod : (256 / 11025 : ℝ) ^ 2 <
        gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
            (gammaSewnMobiusApertureStokesPrimeTwo, 0) *
          gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2)
            (gammaSewnMobiusApertureStokesPrimeTwo, 0) := by
      nlinarith [mul_pos (sub_pos.mpr hw) (sub_pos.mpr hn)]
    norm_num at hprod ⊢
    linarith
  exact normalizedPrimeArchMoment_one_lt_nine_over_fiftyThousand.trans
    (hatom.trans_le hselected)

/-- **Raw critical identification no-go.**  P-G71's explicit critical carrier cannot equal the
completed seam germ, already at order zero. -/
theorem not_gammaSewnMobiusApertureStokesCriticalMomentIdentification :
    ¬ GammaSewnMobiusApertureStokesCriticalMomentIdentification := by
  intro h
  have hmass := normalizedPrimeArchMoment_zero_eq_measureReal_univ_of_compactMarkovGerm
    gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier h
  have hzero : normalizedPrimeArchMoment 0 =
      ∫ y : ℝ, y ^ 0 ∂gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier := by
    rw [hmass]
    simp [MeasureTheory.integral_const]
  linarith [normalizedPrimeArchMoment_zero_lt_integral_criticalSquaredCompactCarrier]

/-- Any additive completed correction at the central Markov value must have negative real mass. -/
theorem gammaSewnMobiusApertureStokesCriticalCorrection_mass_neg
    {C : ℝ}
    (hC : (∫ y : ℝ, y ^ 0 ∂gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier) + C =
      normalizedPrimeArchMoment 0) :
    C < 0 := by
  linarith [normalizedPrimeArchMoment_zero_lt_integral_criticalSquaredCompactCarrier]

/-- A corrected all-degree weld must also subtract first moment; a constant counterterm cannot
repair the raw carrier. -/
theorem gammaSewnMobiusApertureStokesCriticalCorrection_firstMoment_neg
    {C₁ : ℝ}
    (hC₁ : (∫ y : ℝ, y ^ 1 ∂gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier) + C₁ =
      normalizedPrimeArchMoment 1) :
    C₁ < 0 := by
  linarith [normalizedPrimeArchMoment_one_lt_integral_criticalSquaredCompactCarrier]

end RHTower

import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesPhysicalPluckerOrdinaryDeterminant
import GaloisForLFunctions.RHTower.ThetaCuspCassiniCalibratedReciprocalMomentNoGo

/-!
# First-trace no-go for the physical Pluecker determinant

The source-native physical Pluecker operator has a canonical ordinary Fredholm determinant, but
its first trace is too small to equal completed Xi.  Coordinate inclusion is Bernoulli, every
packet node sum is below `2/25`, and therefore every local trace is below `1/50`.  Normalized block
weights preserve this ceiling globally.  The theta source independently has first square-coordinate
coefficient strictly above `1/50`.

Thus neither `det₂` nor its canonical ordinary trace restoration can be completed Xi.  Positivity,
faithfulness, strict negative-real zero location, and finite-section convergence survive as useful
structure; arithmetic identification must use a genuinely source-derived boundary transfer rather
than a scalar trace counterterm.
-/

open Real Set Filter Topology Matrix
open scoped BigOperators InnerProductSpace ComplexOrder

noncomputable section

namespace RHTower

private theorem criticalPrimeTwoNode_bounds :
    let r := criticalStokesNode gammaSewnMobiusApertureStokesPrimeTwo
    (7071 / 10000 : ℝ) < r ∧ r < 7072 / 10000 := by
  let r := criticalStokesNode gammaSewnMobiusApertureStokesPrimeTwo
  have hr0 : 0 < r := criticalStokesNode_pos _
  have hr2 : r ^ 2 = 1 / 2 := by
    simpa [r] using criticalStokesNode_sq gammaSewnMobiusApertureStokesPrimeTwo
  constructor <;> by_contra h
  · have hr : r ≤ 7071 / 10000 := le_of_not_gt h
    nlinarith [mul_nonneg (sub_nonneg.mpr hr)
      (add_nonneg hr0.le (by norm_num : (0 : ℝ) ≤ 7071 / 10000))]
  · have hr : 7072 / 10000 ≤ r := le_of_not_gt h
    nlinarith [mul_nonneg (sub_nonneg.mpr hr)
      (add_nonneg hr0.le (by norm_num : (0 : ℝ) ≤ 7072 / 10000))]

private theorem criticalPrimeThreeNode_bounds :
    let r := criticalStokesNode gammaSewnMobiusApertureStokesPrimeThree
    (5773 / 10000 : ℝ) < r ∧ r < 5774 / 10000 := by
  let r := criticalStokesNode gammaSewnMobiusApertureStokesPrimeThree
  have hr0 : 0 < r := criticalStokesNode_pos _
  have hr2 : r ^ 2 = 1 / 3 := by
    simpa [r] using criticalStokesNode_sq gammaSewnMobiusApertureStokesPrimeThree
  constructor <;> by_contra h
  · have hr : r ≤ 5773 / 10000 := le_of_not_gt h
    nlinarith [mul_nonneg (sub_nonneg.mpr hr)
      (add_nonneg hr0.le (by norm_num : (0 : ℝ) ≤ 5773 / 10000))]
  · have hr : 5774 / 10000 ≤ r := le_of_not_gt h
    nlinarith [mul_nonneg (sub_nonneg.mpr hr)
      (add_nonneg hr0.le (by norm_num : (0 : ℝ) ≤ 5774 / 10000))]

private theorem criticalPrimeThreeContraction_lt :
    gammaSewnMobiusValuationContractionMultiplier (1 / 2)
        gammaSewnMobiusApertureStokesPrimeThree < (23 / 25 : ℝ) := by
  let p := gammaSewnMobiusApertureStokesPrimeThree
  let r := criticalStokesNode p
  let c := gammaSewnMobiusValuationContractionMultiplier (1 / 2) p
  have hr : (5773 / 10000 : ℝ) < r ∧ r < 5774 / 10000 := by
    simpa only [r, p] using criticalPrimeThreeNode_bounds
  have hr0 : 0 < r := criticalStokesNode_pos p
  have hr2 : r ^ 2 = 1 / 3 := by
    have h := criticalStokesNode_sq p
    norm_num [p] at h
    simpa [r] using h
  have hr4 : r ^ 4 = 1 / 9 := by
    calc
      r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ = (1 / 3 : ℝ) ^ 2 := by rw [hr2]
      _ = 1 / 9 := by norm_num
  have hc0 : 0 < c := gammaSewnMobiusValuationContractionMultiplier_pos _ _
  have hbase : (0 : ℝ) ≤ 1 + r := by positivity
  have hnum : (1 + r) ^ 4 < (1 + (5774 / 10000 : ℝ)) ^ 4 :=
    pow_lt_pow_left₀ (by linarith [hr.2]) hbase (by norm_num)
  have hc4eq : c ^ 4 = (1 + r) ^ 4 / (8 * (1 + r ^ 4)) := by
    simpa only [c, r, p, criticalStokesNode] using
      gammaSewnMobiusValuationContractionMultiplier_pow_four (1 / 2) p
  have hc4 : c ^ 4 < (23 / 25 : ℝ) ^ 4 := by
    rw [hc4eq, hr4]
    norm_num at hnum ⊢
    nlinarith
  by_contra h
  have hc : (23 / 25 : ℝ) ≤ c := le_of_not_gt h
  have hc2 : (23 / 25 : ℝ) ^ 2 ≤ c ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc)
      (add_nonneg (by norm_num : (0 : ℝ) ≤ 23 / 25) hc0.le)]
  have hc4le : (23 / 25 : ℝ) ^ 4 ≤ c ^ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2)
      (add_nonneg (sq_nonneg (23 / 25 : ℝ)) (sq_nonneg c))]
  linarith

private theorem criticalPrimeTwoInverseTilt_gt_five :
    5 < gammaSewnMobiusApertureStokesInverseTilt (1 / 2)
      gammaSewnMobiusApertureStokesPrimeTwo := by
  let p := gammaSewnMobiusApertureStokesPrimeTwo
  let r := criticalStokesNode p
  let c := gammaSewnMobiusValuationContractionMultiplier (1 / 2) p
  let L := Real.log (p : ℝ)
  have hr : (7071 / 10000 : ℝ) < r ∧ r < 7072 / 10000 := by
    simpa only [r, p] using criticalPrimeTwoNode_bounds
  have hr0 : 0 < r := criticalStokesNode_pos p
  have hr1 : r < 1 := by linarith [hr.2]
  have hr2 : r ^ 2 = 1 / 2 := by
    have h := criticalStokesNode_sq p
    norm_num [p] at h
    simpa [r] using h
  have hc0 : 0 < c := gammaSewnMobiusValuationContractionMultiplier_pos _ _
  have hc1 : c < 1 := gammaSewnMobiusValuationContractionMultiplier_lt_one
    (x := (1 / 2 : ℝ)) (by norm_num) p
  have hL : (0 : ℝ) < L := by dsimp [L, p]; positivity
  have hden : 0 < r * c * (1 - r) := by positivity
  rw [gammaSewnMobiusApertureStokesCriticalInverseTilt_eq]
  change 5 < L / r * ((1 + r ^ 2) / (c * (1 - r)))
  rw [show L / r * ((1 + r ^ 2) / (c * (1 - r))) =
      L * (1 + r ^ 2) / (r * c * (1 - r)) by field_simp]
  rw [lt_div_iff₀ hden]
  have hcprod : r * c * (1 - r) < r * (1 - r) := by
    calc
      r * c * (1 - r) < r * 1 * (1 - r) := by gcongr
      _ = r * (1 - r) := by ring
  have hnumeric : 5 * (r * (1 - r)) < L * (1 + r ^ 2) := by
    dsimp [L, p]
    nlinarith [Real.log_two_gt_d9]
  nlinarith

private theorem criticalPrimeThreeInverseTilt_gt_thirteen_halves :
    (13 / 2 : ℝ) < gammaSewnMobiusApertureStokesInverseTilt (1 / 2)
      gammaSewnMobiusApertureStokesPrimeThree := by
  let p := gammaSewnMobiusApertureStokesPrimeThree
  let r := criticalStokesNode p
  let c := gammaSewnMobiusValuationContractionMultiplier (1 / 2) p
  let L := Real.log (p : ℝ)
  have hr : (5773 / 10000 : ℝ) < r ∧ r < 5774 / 10000 := by
    simpa only [r, p] using criticalPrimeThreeNode_bounds
  have hr0 : 0 < r := criticalStokesNode_pos p
  have hr1 : r < 1 := by linarith [hr.2]
  have hr2 : r ^ 2 = 1 / 3 := by
    have h := criticalStokesNode_sq p
    norm_num [p] at h
    simpa [r] using h
  have hc0 : 0 < c := gammaSewnMobiusValuationContractionMultiplier_pos _ _
  have hc : c < (23 / 25 : ℝ) := by
    simpa only [c, p] using criticalPrimeThreeContraction_lt
  have hL : (0 : ℝ) < L := by dsimp [L, p]; positivity
  have hden : 0 < r * c * (1 - r) := by positivity
  have hrr : r * (1 - r) < (5774 / 10000 : ℝ) - 1 / 3 := by
    nlinarith
  have hcprod : r * c * (1 - r) <
      (23 / 25 : ℝ) * ((5774 / 10000 : ℝ) - 1 / 3) := by
    calc
      r * c * (1 - r) = c * (r * (1 - r)) := by ring
      _ < (23 / 25 : ℝ) * (r * (1 - r)) := by gcongr
      _ < _ := by gcongr
  rw [gammaSewnMobiusApertureStokesCriticalInverseTilt_eq]
  change (13 / 2 : ℝ) < L / r * ((1 + r ^ 2) / (c * (1 - r)))
  rw [show L / r * ((1 + r ^ 2) / (c * (1 - r))) =
      L * (1 + r ^ 2) / (r * c * (1 - r)) by field_simp]
  rw [lt_div_iff₀ hden]
  dsimp [L, p]
  nlinarith [Real.log_three_gt_d9]

private theorem criticalInverseTilt_gt_four_log
    (p : Nat.Primes) :
    4 * Real.log (p : ℝ) <
      gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p := by
  let r := criticalStokesNode p
  let c := gammaSewnMobiusValuationContractionMultiplier (1 / 2) p
  let L := Real.log (p : ℝ)
  have hr0 : 0 < r := criticalStokesNode_pos p
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one (by norm_num) p
  have hc0 : 0 < c := gammaSewnMobiusValuationContractionMultiplier_pos _ _
  have hc1 : c < 1 := gammaSewnMobiusValuationContractionMultiplier_lt_one
    (x := (1 / 2 : ℝ)) (by norm_num) p
  have hL : 0 < L := Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hden : 0 < r * c * (1 - r) := by positivity
  have hquarter : r * c * (1 - r) < 1 / 4 := by
    have hrc : r * c * (1 - r) < r * (1 - r) := by
      calc
        r * c * (1 - r) < r * 1 * (1 - r) := by gcongr
        _ = r * (1 - r) := by ring
    have hrr : r * (1 - r) ≤ 1 / 4 := by
      nlinarith [sq_nonneg (r - 1 / 2)]
    exact hrc.trans_le hrr
  rw [gammaSewnMobiusApertureStokesCriticalInverseTilt_eq]
  change 4 * L < L / r * ((1 + r ^ 2) / (c * (1 - r)))
  rw [show L / r * ((1 + r ^ 2) / (c * (1 - r))) =
      L * (1 + r ^ 2) / (r * c * (1 - r)) by field_simp]
  rw [lt_div_iff₀ hden]
  have hleft : 4 * L * (r * c * (1 - r)) < L := by
    calc
      4 * L * (r * c * (1 - r)) < 4 * L * (1 / 4) := by gcongr
      _ = L := by ring
  have hright : L < L * (1 + r ^ 2) := by
    nlinarith [sq_pos_of_pos hr0]
  exact hleft.trans hright

private theorem criticalPrimeFiveInverseTilt_gt_thirteen_halves :
    (13 / 2 : ℝ) < gammaSewnMobiusApertureStokesInverseTilt (1 / 2)
      ⟨5, by norm_num⟩ := by
  let p : Nat.Primes := ⟨5, by norm_num⟩
  let r := criticalStokesNode p
  let c := gammaSewnMobiusValuationContractionMultiplier (1 / 2) p
  let L := Real.log (p : ℝ)
  have hr0 : 0 < r := criticalStokesNode_pos p
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one (by norm_num) p
  have hr2 : r ^ 2 = 1 / 5 := by simpa [r, p] using criticalStokesNode_sq p
  have hc0 : 0 < c := gammaSewnMobiusValuationContractionMultiplier_pos _ _
  have hc1 : c < 1 := gammaSewnMobiusValuationContractionMultiplier_lt_one
    (x := (1 / 2 : ℝ)) (by norm_num) p
  have hL : 0 < L := by dsimp [L, p]; positivity
  have hden : 0 < r * c * (1 - r) := by positivity
  have hquarter : r * c * (1 - r) < 1 / 4 := by
    have hrc : r * c * (1 - r) < r * (1 - r) := by
      calc
        r * c * (1 - r) < r * 1 * (1 - r) := by gcongr
        _ = r * (1 - r) := by ring
    exact hrc.trans_le (by nlinarith [sq_nonneg (r - 1 / 2)])
  rw [gammaSewnMobiusApertureStokesCriticalInverseTilt_eq]
  change (13 / 2 : ℝ) < L / r * ((1 + r ^ 2) / (c * (1 - r)))
  rw [show L / r * ((1 + r ^ 2) / (c * (1 - r))) =
      L * (1 + r ^ 2) / (r * c * (1 - r)) by field_simp]
  rw [lt_div_iff₀ hden]
  have hleft : (13 / 2 : ℝ) * (r * c * (1 - r)) < 13 / 8 := by
    nlinarith
  have hright : (13 / 8 : ℝ) < L * (1 + r ^ 2) := by
    dsimp [L, p]
    nlinarith [Real.log_five_gt_d9]
  linarith

private theorem criticalInverseTilt_gt_thirteen_halves_of_seven_le
    (p : Nat.Primes) (hp : 7 ≤ (p : ℕ)) :
    (13 / 2 : ℝ) < gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p := by
  have hfour := criticalInverseTilt_gt_four_log p
  have hlog6 : Real.log 2 + Real.log 3 = Real.log 6 := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  have hlog : Real.log 6 < Real.log (p : ℝ) := by
    exact Real.strictMonoOn_log (by norm_num)
      (show (p : ℝ) ∈ Set.Ioi 0 by
        change 0 < (p : ℝ)
        exact_mod_cast p.2.pos)
      (by exact_mod_cast (show 6 < (p : ℕ) by omega))
  have hbound : (13 / 8 : ℝ) < Real.log (p : ℝ) := by
    rw [← hlog6] at hlog
    nlinarith [Real.log_two_gt_d9, Real.log_three_gt_d9]
  nlinarith

theorem gammaSewnMobiusApertureStokesCriticalInverseTilt_gt_thirteen_halves_of_three_le
    (p : Nat.Primes) (hp : 3 ≤ (p : ℕ)) :
    (13 / 2 : ℝ) < gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p := by
  by_cases h3 : (p : ℕ) = 3
  · have hp' : p = gammaSewnMobiusApertureStokesPrimeThree := Subtype.ext h3
    subst p
    simpa using criticalPrimeThreeInverseTilt_gt_thirteen_halves
  by_cases h5 : (p : ℕ) = 5
  · have hp' : p = (⟨5, by norm_num⟩ : Nat.Primes) := Subtype.ext h5
    subst p
    simpa using criticalPrimeFiveInverseTilt_gt_thirteen_halves
  have h4 : (p : ℕ) ≠ 4 := by
    intro h
    have := p.2
    norm_num [h] at this
  have h6 : (p : ℕ) ≠ 6 := by
    intro h
    have := p.2
    norm_num [h] at this
  exact criticalInverseTilt_gt_thirteen_halves_of_seven_le p (by omega)

theorem gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_depth_eq
    (p : Nat.Primes) (e : ℕ) :
    gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2) (p, e) =
      gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2) (p, 0) /
        ((e : ℝ) + 1) ^ 2 := by
  have hW := (gammaSewnMobiusApertureStokesInverseTilt_pos (by norm_num : (0 : ℝ) < 1 / 2) p).ne'
  have he : (e : ℝ) + 1 ≠ 0 := by positivity
  unfold gammaSewnMobiusApertureStokesSquaredReciprocalGapNode
    gammaSewnMobiusApertureStokesReciprocalGapNode
    gammaSewnMobiusApertureStokesGap
  simp only [Nat.cast_zero, zero_add, one_mul]
  field_simp

theorem gammaSewnMobiusApertureStokesPrimeTwo_baseNode_lt_one_div_twentyFive :
    gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2)
      (gammaSewnMobiusApertureStokesPrimeTwo, 0) < (1 / 25 : ℝ) := by
  let W := gammaSewnMobiusApertureStokesInverseTilt (1 / 2)
    gammaSewnMobiusApertureStokesPrimeTwo
  have hW : 5 < W := criticalPrimeTwoInverseTilt_gt_five
  have hW0 : 0 < W := gammaSewnMobiusApertureStokesInverseTilt_pos (by norm_num) _
  have hW2 : (25 : ℝ) < W ^ 2 := by nlinarith
  unfold gammaSewnMobiusApertureStokesSquaredReciprocalGapNode
    gammaSewnMobiusApertureStokesReciprocalGapNode
    gammaSewnMobiusApertureStokesGap
  simp only [Nat.cast_zero, zero_add, one_mul]
  change W⁻¹ ^ 2 < (1 / 25 : ℝ)
  rw [inv_pow]
  simpa [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 25) hW2

theorem gammaSewnMobiusApertureStokes_baseNode_lt_three_div_oneTwentyFive_of_three_le
    (p : Nat.Primes) (hp : 3 ≤ (p : ℕ)) :
    gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2) (p, 0) <
      (3 / 125 : ℝ) := by
  let W := gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p
  have hW : (13 / 2 : ℝ) < W :=
    gammaSewnMobiusApertureStokesCriticalInverseTilt_gt_thirteen_halves_of_three_le p hp
  have hW0 : 0 < W := gammaSewnMobiusApertureStokesInverseTilt_pos (by norm_num) _
  have hW2 : (125 / 3 : ℝ) < W ^ 2 := by nlinarith
  unfold gammaSewnMobiusApertureStokesSquaredReciprocalGapNode
    gammaSewnMobiusApertureStokesReciprocalGapNode
    gammaSewnMobiusApertureStokesGap
  simp only [Nat.cast_zero, zero_add, one_mul]
  change W⁻¹ ^ 2 < (3 / 125 : ℝ)
  rw [inv_pow]
  have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 125 / 3) hW2
  norm_num at h ⊢
  exact h

end RHTower

namespace RHTower.HedenmalmThetaSource

private theorem squaredReciprocalGapNode_depth_le_base
    (p : Nat.Primes) (e : ℕ) :
    RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2) (p, e) ≤
      RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2) (p, 0) := by
  rw [RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_depth_eq]
  let B := RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2) (p, 0)
  let d := ((e : ℝ) + 1) ^ 2
  have hB : 0 ≤ B :=
    (RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_pos
      (by norm_num) (p, 0)).le
  have hd0 : 0 < d := by positivity
  have hd1 : 1 ≤ d := by
    have he : (0 : ℝ) ≤ e := by positivity
    nlinarith [sq_nonneg ((e : ℝ) + 1)]
  change B / d ≤ B
  rw [div_le_iff₀ hd0]
  nlinarith [mul_nonneg hB (sub_nonneg.mpr hd1)]

private theorem squaredReciprocalGapNode_succ_depth_le_quarter_base
    (p : Nat.Primes) (e : ℕ) :
    RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2) (p, e + 1) ≤
      RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2) (p, 0) / 4 := by
  rw [RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_depth_eq]
  let B := RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2) (p, 0)
  let d := (((e + 1 : ℕ) : ℝ) + 1) ^ 2
  have hB : 0 ≤ B :=
    (RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_pos
      (by norm_num) (p, 0)).le
  have hd0 : 0 < d := by positivity
  have hd4 : 4 ≤ d := by
    dsimp [d]
    push_cast
    have he : (0 : ℝ) ≤ e := by positivity
    nlinarith [sq_nonneg ((e : ℝ) + 2)]
  change B / d ≤ B / 4
  rw [div_le_iff₀ hd0]
  nlinarith [mul_nonneg hB (sub_nonneg.mpr hd4)]

private theorem adjacentPrime_lower_three_le_of_ne_zero
    {n : ℕ} (hn : n ≠ 0) :
    3 ≤ (gammaSewnCriticalAdjacentPrime_lower n : ℕ) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hmono := RHTower.nthPrimeSubtype_strictMono hn0
  change (RHTower.nthPrimeSubtype 0 : ℕ) <
    (RHTower.nthPrimeSubtype n : ℕ) at hmono
  have hzero : (RHTower.nthPrimeSubtype 0 : ℕ) = 2 := by
    norm_num [RHTower.nthPrimeSubtype]
  rw [hzero] at hmono
  change 3 ≤ (RHTower.nthPrimeSubtype n : ℕ)
  omega

private theorem adjacentPrime_upper_three_le (n : ℕ) :
    3 ≤ (gammaSewnCriticalAdjacentPrime_upper n : ℕ) := by
  have hmono := RHTower.nthPrimeSubtype_strictMono (Nat.succ_pos n)
  change (RHTower.nthPrimeSubtype 0 : ℕ) <
    (RHTower.nthPrimeSubtype (n + 1) : ℕ) at hmono
  have hzero : (RHTower.nthPrimeSubtype 0 : ℕ) = 2 := by
    norm_num [RHTower.nthPrimeSubtype]
  rw [hzero] at hmono
  change 3 ≤ (RHTower.nthPrimeSubtype (n + 1) : ℕ)
  omega

private theorem adjacentPrime_baseNode_sum_lt
    (n : ℕ) :
    RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2)
          (gammaSewnCriticalAdjacentPrime_lower n, 0) +
        RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2)
          (gammaSewnCriticalAdjacentPrime_upper n, 0) <
      (8 / 125 : ℝ) := by
  by_cases hn : n = 0
  · subst n
    have hlo := RHTower.gammaSewnMobiusApertureStokesPrimeTwo_baseNode_lt_one_div_twentyFive
    have hhi := RHTower.gammaSewnMobiusApertureStokes_baseNode_lt_three_div_oneTwentyFive_of_three_le
      (gammaSewnCriticalAdjacentPrime_upper 0)
      (adjacentPrime_upper_three_le 0)
    have hloeq : gammaSewnCriticalAdjacentPrime_lower 0 =
        RHTower.gammaSewnMobiusApertureStokesPrimeTwo := by
      apply Subtype.ext
      norm_num [gammaSewnCriticalAdjacentPrime_lower, RHTower.nthPrimeSubtype]
    rw [hloeq]
    nlinarith
  · have hlo := RHTower.gammaSewnMobiusApertureStokes_baseNode_lt_three_div_oneTwentyFive_of_three_le
      (gammaSewnCriticalAdjacentPrime_lower n)
      (adjacentPrime_lower_three_le_of_ne_zero hn)
    have hhi := RHTower.gammaSewnMobiusApertureStokes_baseNode_lt_three_div_oneTwentyFive_of_three_le
      (gammaSewnCriticalAdjacentPrime_upper n)
      (adjacentPrime_upper_three_le n)
    nlinarith

private theorem packetNode_sum_eq (z : ℕ × ℕ) :
    (∑ i : Fin 4,
      gammaSewnCriticalPrimeDepthPacket_node z.1
        (gammaSewnCriticalAdjacentPrime_lower z.2)
        (gammaSewnCriticalAdjacentPrime_upper z.2) i) =
      RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2)
          (gammaSewnCriticalAdjacentPrime_lower z.2, z.1) +
        RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2)
          (gammaSewnCriticalAdjacentPrime_lower z.2, z.1 + 1) +
        RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2)
          (gammaSewnCriticalAdjacentPrime_upper z.2, z.1) +
        RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2)
          (gammaSewnCriticalAdjacentPrime_upper z.2, z.1 + 1) := by
  simp [Fin.sum_univ_succ, gammaSewnCriticalPrimeDepthPacket_node,
    gammaSewnOrderedPrimeDepthPlucker_cell]
  ring

theorem gammaSewnCriticalPhysicalPlucker_packetNode_sum_lt_two_div_twentyFive (z : ℕ × ℕ) :
    (∑ i : Fin 4,
      gammaSewnCriticalPrimeDepthPacket_node z.1
        (gammaSewnCriticalAdjacentPrime_lower z.2)
        (gammaSewnCriticalAdjacentPrime_upper z.2) i) < (2 / 25 : ℝ) := by
  let p := gammaSewnCriticalAdjacentPrime_lower z.2
  let q := gammaSewnCriticalAdjacentPrime_upper z.2
  let Bp := RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode
    (1 / 2) (p, 0)
  let Bq := RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode
    (1 / 2) (q, 0)
  have hp0 := squaredReciprocalGapNode_depth_le_base p z.1
  have hp1 := squaredReciprocalGapNode_succ_depth_le_quarter_base p z.1
  have hq0 := squaredReciprocalGapNode_depth_le_base q z.1
  have hq1 := squaredReciprocalGapNode_succ_depth_le_quarter_base q z.1
  have hbase := adjacentPrime_baseNode_sum_lt z.2
  rw [packetNode_sum_eq]
  change _ < (2 / 25 : ℝ)
  change Bp + Bq < (8 / 125 : ℝ) at hbase
  change _ ≤ Bp at hp0
  change _ ≤ Bp / 4 at hp1
  change _ ≤ Bq at hq0
  change _ ≤ Bq / 4 at hq1
  nlinarith

private theorem coordinateMean_bernoulliVariance_mem
    (z : ℕ × ℕ) (i : Fin 4) :
    gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i *
        (1 - gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i) ∈
      Set.Icc (0 : ℝ) (1 / 4) := by
  have hm := gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean_mem z i
  constructor
  · exact mul_nonneg hm.1 (sub_nonneg.mpr hm.2)
  · nlinarith [sq_nonneg
      (gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i - 1 / 2)]

/-- **Incidence-reweighting wall.** Every real four-coordinate Bernoulli quadratic on the fixed
physical reciprocal-gap nodes stays below the same first-trace ceiling.  No interval assumption is
needed because `m * (1 - m) ≤ 1 / 4` holds for every real `m`.  Thus even arbitrary real changes of
the six Pluecker coordinate means cannot repair the Xi mismatch while nodes stay fixed and positive. -/
theorem gammaSewnCriticalPhysicalPlucker_arbitraryBernoulliTrace_lt_one_div_fifty
    (z : ℕ × ℕ) (m : Fin 4 → ℝ) :
    (∑ i : Fin 4,
      gammaSewnCriticalPrimeDepthPacket_node z.1
          (gammaSewnCriticalAdjacentPrime_lower z.2)
          (gammaSewnCriticalAdjacentPrime_upper z.2) i *
        m i * (1 - m i)) < (1 / 50 : ℝ) := by
  let node : Fin 4 → ℝ := fun i =>
    gammaSewnCriticalPrimeDepthPacket_node z.1
      (gammaSewnCriticalAdjacentPrime_lower z.2)
      (gammaSewnCriticalAdjacentPrime_upper z.2) i
  have hvariance (i : Fin 4) : m i * (1 - m i) ≤ (1 / 4 : ℝ) := by
    nlinarith [sq_nonneg (m i - 1 / 2)]
  have hsum : (∑ i : Fin 4, node i * (m i * (1 - m i))) ≤
      (∑ i : Fin 4, node i) * (1 / 4 : ℝ) := by
    calc
      (∑ i : Fin 4, node i * (m i * (1 - m i))) ≤
          ∑ i : Fin 4, node i * (1 / 4 : ℝ) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hvariance i)
          (gammaSewnCriticalPrimeDepthPacket_node_pos z.1
            (gammaSewnCriticalAdjacentPrime_lower z.2)
            (gammaSewnCriticalAdjacentPrime_upper z.2) i).le
      _ = _ := by rw [Finset.sum_mul]
  have hnode := gammaSewnCriticalPhysicalPlucker_packetNode_sum_lt_two_div_twentyFive z
  change (∑ i : Fin 4, node i) < (2 / 25 : ℝ) at hnode
  have hquarter : (∑ i : Fin 4, node i) * (1 / 4 : ℝ) < (1 / 50 : ℝ) := by
    nlinarith
  have hfinal := hsum.trans_lt hquarter
  simpa only [node, mul_assoc] using hfinal

private theorem localBernoulliTrace_nonneg (z : ℕ × ℕ) :
    0 ≤ ∑ i : Fin 4,
      gammaSewnCriticalPrimeDepthPacket_node z.1
          (gammaSewnCriticalAdjacentPrime_lower z.2)
          (gammaSewnCriticalAdjacentPrime_upper z.2) i *
        gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i *
          (1 - gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i) := by
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg
      (gammaSewnCriticalPrimeDepthPacket_node_pos z.1
        (gammaSewnCriticalAdjacentPrime_lower z.2)
        (gammaSewnCriticalAdjacentPrime_upper z.2) i).le
      (gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean_mem z i).1)
      (sub_nonneg.mpr
        (gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean_mem z i).2)

theorem gammaSewnCriticalPhysicalPlucker_localBernoulliTrace_lt_one_div_fifty (z : ℕ × ℕ) :
    (∑ i : Fin 4,
      gammaSewnCriticalPrimeDepthPacket_node z.1
          (gammaSewnCriticalAdjacentPrime_lower z.2)
          (gammaSewnCriticalAdjacentPrime_upper z.2) i *
        gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i *
          (1 - gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i)) <
      (1 / 50 : ℝ) := by
  exact gammaSewnCriticalPhysicalPlucker_arbitraryBernoulliTrace_lt_one_div_fifty z
    (gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z)

/-- Source trace has a rational ceiling independent of all Xi data. -/
theorem gammaSewnCriticalPhysicalPluckerNuclearTraceMass_le_one_div_fifty :
    gammaSewnCriticalPhysicalPluckerNuclearTraceMass ≤ (1 / 50 : ℝ) := by
  let localTrace : ℕ × ℕ → ℝ := fun z =>
    ∑ i : Fin 4,
      gammaSewnCriticalPrimeDepthPacket_node z.1
          (gammaSewnCriticalAdjacentPrime_lower z.2)
          (gammaSewnCriticalAdjacentPrime_upper z.2) i *
        gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i *
          (1 - gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i)
  let f : ℕ × ℕ → ℝ := fun z =>
    gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z * localTrace z
  let g : ℕ × ℕ → ℝ := fun z =>
    gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z * (1 / 50 : ℝ)
  have hf0 : ∀ z, 0 ≤ f z := by
    intro z
    exact mul_nonneg (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos z).le
      (localBernoulliTrace_nonneg z)
  have hfg : ∀ z, f z ≤ g z := by
    intro z
    exact mul_le_mul_of_nonneg_left
      (gammaSewnCriticalPhysicalPlucker_localBernoulliTrace_lt_one_div_fifty z).le
      (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos z).le
  have hg : Summable g := by
    exact summable_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight.mul_right (1 / 50 : ℝ)
  have hf : Summable f := Summable.of_nonneg_of_le hf0 hfg hg
  rw [gammaSewnCriticalPhysicalPluckerNuclearTraceMass_eq_tsum_bernoulliTrace]
  change ∑' z, f z ≤ (1 / 50 : ℝ)
  calc
    ∑' z, f z ≤ ∑' z, g z := hf.tsum_le_tsum hfg hg
    _ = (∑' z, gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z) *
        (1 / 50 : ℝ) := by rw [tsum_mul_right]
    _ = 1 / 50 := by rw [tsum_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight]; norm_num

/-- The source trace ceiling lies strictly below the completed-Xi first coefficient. -/
theorem gammaSewnCriticalPhysicalPluckerNuclearTraceMass_lt_thetaFirstCoefficient :
    gammaSewnCriticalPhysicalPluckerNuclearTraceMass <
      thetaCuspNormalizedEvenMoment 1 / 2 := by
  have htheta := RHTower.one_div_twentyFive_lt_normalizedPrimeArchMoment_zero
  rw [RHTower.normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment] at htheta
  nlinarith [gammaSewnCriticalPhysicalPluckerNuclearTraceMass_le_one_div_fifty]

/-- Ordinary-determinant first-jet no-go, now source-quantitative rather than regularization-only. -/
theorem gammaSewnCriticalPhysicalPluckerOrdinary_firstJet_ne_theta :
    deriv gammaSewnCriticalPhysicalPluckerOrdinaryStableEntireDet 0 ≠
      ((thetaCuspNormalizedEvenMoment 1 / 2 : ℝ) : ℂ) := by
  intro h
  have hmass := gammaSewnCriticalPhysicalPluckerOrdinary_firstJet_eq_theta_iff.mp h
  linarith [gammaSewnCriticalPhysicalPluckerNuclearTraceMass_lt_thetaFirstCoefficient]

end RHTower.HedenmalmThetaSource

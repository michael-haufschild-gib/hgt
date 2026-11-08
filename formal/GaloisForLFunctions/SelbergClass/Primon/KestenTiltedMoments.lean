import GaloisForLFunctions.SelbergClass.Primon.KestenEdgeAsymptotics
import GaloisForLFunctions.HTGeometry.LogRatioResonance

/-!
# Moments under high even-power weighting

The ratio of consecutive even prime moments tends to the spectral maximum
squared, four. Telescoping gives all fixed-shift ratios. Consequently the
moments after weighting by `x^(2n)` tend to those of equal masses at the two
spectral endpoints. The mean squared-edge gap has universal leading
coefficient six, independent of the prime.
-/

open Filter Topology

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Every even moment is strictly positive, so power weighting can be normalized. -/
theorem kestenMoment_even_pos (p : Nat.Primes) (n : ℕ) : 0 < kestenMoment p (2 * n) :=
  (catalan_real_pos n).trans_le (catalan_le_kestenMoment_even p n)

/-- The Catalan-normalized moments are positive in every degree. -/
theorem kestenMomentRatio_pos (p : Nat.Primes) (n : ℕ) : 0 < kestenMomentRatio p n :=
  div_pos (kestenMoment_even_pos p n) (catalan_real_pos n)

/-- The linear moment recurrence gives an exact successive-ratio formula. -/
theorem kestenMoment_successive_ratio (p : Nat.Primes) (n : ℕ) :
    kestenMoment p (2 * (n + 1)) / kestenMoment p (2 * n) =
      ((p : ℝ) + 1) ^ 2 / (p : ℝ) - ((p : ℝ) + 1) / kestenMomentRatio p n := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  rw [kestenMoment_even_succ, kestenMomentRatio]
  field_simp [hp, (kestenMoment_even_pos p n).ne', (catalan_real_pos n).ne']

private theorem edge_ratio_limit_identity (p : Nat.Primes) :
    ((p : ℝ) + 1) ^ 2 / (p : ℝ) - ((p : ℝ) + 1) / kestenEdgeScale p = 4 := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (by linarith only [hp])
  have hp1 : (p : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith only [hp])
  have hp2 : (p : ℝ) + 1 ≠ 0 := ne_of_gt (by linarith only [hp])
  unfold kestenEdgeScale
  field_simp [hp0, hp1, hp2]
  ring

/-- Consecutive even moments have ratio tending to the squared spectral radius. -/
theorem tendsto_kestenMoment_successive_ratio (p : Nat.Primes) :
    Tendsto (fun n : ℕ => kestenMoment p (2 * (n + 1)) / kestenMoment p (2 * n))
      atTop (𝓝 4) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => ((p : ℝ) + 1) ^ 2 / (p : ℝ))
    atTop (𝓝 (((p : ℝ) + 1) ^ 2 / (p : ℝ)))).sub
      ((tendsto_const_nhds (x := ((p : ℝ) + 1))).div
        (tendsto_kestenMomentRatio p) (kestenEdgeScale_pos p).ne')
  change Tendsto (fun n : ℕ => ((p : ℝ) + 1) ^ 2 / (p : ℝ) -
    ((p : ℝ) + 1) / kestenMomentRatio p n) atTop
    (𝓝 (((p : ℝ) + 1) ^ 2 / (p : ℝ) - ((p : ℝ) + 1) / kestenEdgeScale p)) at h
  simpa only [kestenMoment_successive_ratio, edge_ratio_limit_identity] using h

/-- Every fixed even shift has the corresponding power of the squared spectral radius. -/
theorem tendsto_kestenMoment_even_shift_ratio (p : Nat.Primes) (k : ℕ) :
    Tendsto (fun n : ℕ => kestenMoment p (2 * (n + k)) / kestenMoment p (2 * n))
      atTop (𝓝 ((4 : ℝ) ^ k)) :=
  GaloisForLFunctions.ratio_tendsto_pow
    (Eventually.of_forall fun n => (kestenMoment_even_pos p n).ne')
    (tendsto_kestenMoment_successive_ratio p) k

/-- All moments under even-power weighting tend to equal endpoint masses. -/
theorem tendsto_kestenMoment_weighted_ratio (p : Nat.Primes) (k : ℕ) :
    Tendsto (fun n : ℕ => kestenMoment p (2 * n + k) / kestenMoment p (2 * n))
      atTop (𝓝 (((-2 : ℝ) ^ k + (2 : ℝ) ^ k) / 2)) := by
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hk : k = 2 * j := by omega
    rw [hk]
    have he (n : ℕ) : 2 * n + 2 * j = 2 * (n + j) := by omega
    have hp : ((-2 : ℝ) ^ (2 * j) + (2 : ℝ) ^ (2 * j)) / 2 = 4 ^ j := by
      rw [pow_mul, pow_mul]
      norm_num
    simpa only [he, hp] using tendsto_kestenMoment_even_shift_ratio p j
  · have hk : k = 2 * j + 1 := by omega
    rw [hk]
    have he (n : ℕ) : 2 * n + (2 * j + 1) = 2 * (n + j) + 1 := by omega
    have hp : ((-2 : ℝ) ^ (2 * j + 1) + (2 : ℝ) ^ (2 * j + 1)) / 2 = 0 := by
      rw [pow_succ, pow_succ, pow_mul, pow_mul]
      norm_num
    simpa only [he, kestenMoment_odd, zero_div, hp] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- The squared-edge deficit is an exact positive transform of the Catalan-ratio deficit. -/
theorem kestenMoment_successive_gap (p : Nat.Primes) (n : ℕ) :
    4 - kestenMoment p (2 * (n + 1)) / kestenMoment p (2 * n) =
      ((p : ℝ) + 1) * (kestenEdgeScale p - kestenMomentRatio p n) /
        (kestenMomentRatio p n * kestenEdgeScale p) := by
  rw [kestenMoment_successive_ratio]
  have h := edge_ratio_limit_identity p
  calc
    _ = ((p : ℝ) + 1) / kestenMomentRatio p n - ((p : ℝ) + 1) / kestenEdgeScale p := by
      linarith only [h]
    _ = _ := by
      field_simp [(kestenMomentRatio_pos p n).ne', (kestenEdgeScale_pos p).ne']

/-- The mean squared-edge gap under even-power weighting is asymptotic to `6/(n+2)`. -/
theorem tendsto_kestenMoment_successive_gap_scaled (p : Nat.Primes) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 2) *
      (4 - kestenMoment p (2 * (n + 1)) / kestenMoment p (2 * n))) atTop (𝓝 6) := by
  have h := ((tendsto_kestenMomentRatio_first_correction p).const_mul ((p : ℝ) + 1)).div
    ((tendsto_kestenMomentRatio p).mul_const (kestenEdgeScale p))
    (mul_ne_zero (kestenEdgeScale_pos p).ne' (kestenEdgeScale_pos p).ne')
  change Tendsto (fun n : ℕ => ((p : ℝ) + 1) *
    (((n : ℝ) + 2) * (kestenEdgeScale p - kestenMomentRatio p n)) /
      (kestenMomentRatio p n * kestenEdgeScale p)) atTop
    (𝓝 (((p : ℝ) + 1) * (6 * kestenEdgeScale p * kestenEdgeSlope p) /
      (kestenEdgeScale p * kestenEdgeScale p))) at h
  have hm : kestenEdgeScale p = ((p : ℝ) + 1) * kestenEdgeSlope p := by
    unfold kestenEdgeScale kestenEdgeSlope
    ring
  have hc : ((p : ℝ) + 1) * (6 * kestenEdgeScale p * kestenEdgeSlope p) /
      (kestenEdgeScale p * kestenEdgeScale p) = 6 := by
    rw [show ((p : ℝ) + 1) * (6 * kestenEdgeScale p * kestenEdgeSlope p) =
      6 * kestenEdgeScale p * kestenEdgeScale p by rw [hm]; ring]
    field_simp [(kestenEdgeScale_pos p).ne']
  have he (n : ℕ) : ((n : ℝ) + 2) *
      (4 - kestenMoment p (2 * (n + 1)) / kestenMoment p (2 * n)) =
      ((p : ℝ) + 1) * (((n : ℝ) + 2) * (kestenEdgeScale p - kestenMomentRatio p n)) /
        (kestenMomentRatio p n * kestenEdgeScale p) := by
    rw [kestenMoment_successive_gap]
    ring
  simpa only [he, hc] using h

end
end GaloisForLFunctions.SelbergClass.Primon

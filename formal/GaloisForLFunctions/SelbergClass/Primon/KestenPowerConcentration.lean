import GaloisForLFunctions.SelbergClass.Primon.KestenPowerTilt

/-!
# Universal concentration rates for power-weighted prime laws

The gap `4-x²` is nonnegative on the spectral interval. Its moments under
normalized even-power weighting are the edge moments divided by the prime
normalizing moment. Every rescaled gap moment has a prime-independent
limit, and Markov's inequality bounds the mass remaining in the interior.
-/

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The squared-edge gap is nonnegative throughout the Hecke spectral interval. -/
theorem kestenInterval_gap_nonneg (x : Icc (-2 : ℝ) 2) : 0 ≤ 4 - (x : ℝ) ^ 2 := by
  have h := mul_nonneg (sub_nonneg.mpr x.property.2)
    (show 0 ≤ (x : ℝ) + 2 by linarith only [x.property.1])
  nlinarith only [h]

/-- Moments of the squared-edge gap under the normalized even-power law. -/
def kestenTiltedGapMoment (p : Nat.Primes) (n k : ℕ) : ℝ :=
  ∫ x : Icc (-2 : ℝ) 2, (4 - (x : ℝ) ^ 2) ^ k
    ∂(kestenPowerTilt p n : Measure (Icc (-2 : ℝ) 2))

/-- Every tilted gap moment is nonnegative. -/
theorem kestenTiltedGapMoment_nonneg (p : Nat.Primes) (n k : ℕ) :
    0 ≤ kestenTiltedGapMoment p n k :=
  integral_nonneg fun x => pow_nonneg (kestenInterval_gap_nonneg x) k

/-- Actual tilted gap moments are normalized prime edge integrals. -/
theorem kestenTiltedGapMoment_eq (p : Nat.Primes) (n k : ℕ) :
    kestenTiltedGapMoment p n k = kestenEdgeMoment p n k / kestenMoment p (2 * n) := by
  let f : C(Icc (-2 : ℝ) 2, ℝ) := ⟨fun x => (4 - (x : ℝ) ^ 2) ^ k, by fun_prop⟩
  let g : C(ℝ, ℝ) := ⟨fun x => x ^ (2 * n) * (4 - x ^ 2) ^ k, by fun_prop⟩
  have h := integral_kestenPowerTilt p n f
  have hb := integral_kestenIntervalLaw p g
  rw [integral_kestenSpectralLaw] at hb
  change (∫ x : Icc (-2 : ℝ) 2, (x : ℝ) ^ (2 * n) * (4 - (x : ℝ) ^ 2) ^ k
    ∂(kestenIntervalLaw p : Measure (Icc (-2 : ℝ) 2))) = kestenEdgeMoment p n k at hb
  change kestenTiltedGapMoment p n k =
    (∫ x : Icc (-2 : ℝ) 2, (x : ℝ) ^ (2 * n) * (4 - (x : ℝ) ^ 2) ^ k
      ∂(kestenIntervalLaw p : Measure (Icc (-2 : ℝ) 2))) / kestenMoment p (2 * n) at h
  rw [hb] at h
  exact h

/-- The mean gap is the deficit of the successive even-moment ratio below four. -/
theorem kestenTiltedGapMoment_one (p : Nat.Primes) (n : ℕ) :
    kestenTiltedGapMoment p n 1 =
      4 - kestenMoment p (2 * (n + 1)) / kestenMoment p (2 * n) := by
  have hi : Integrable (fun x : Icc (-2 : ℝ) 2 => (x : ℝ) ^ 2)
      (kestenPowerTilt p n : Measure (Icc (-2 : ℝ) 2)) :=
    (by fun_prop : Continuous (fun x : Icc (-2 : ℝ) 2 => (x : ℝ) ^ 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold kestenTiltedGapMoment
  simp only [pow_one]
  rw [integral_sub (integrable_const 4) hi, integral_const, integral_kestenPowerTilt_pow]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  rw [show 2 * n + 2 = 2 * (n + 1) by omega]

/-- Every rescaled gap moment has the same explicit limit at every prime. -/
theorem tendsto_scaled_kestenTiltedGapMoment (p : Nat.Primes) (k : ℕ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 2) ^ k * kestenTiltedGapMoment p n k)
      atTop (𝓝 (semicircleEdgeCoefficient k)) := by
  have h := (tendsto_scaled_kestenEdgeRemainder p k).div
    ((tendsto_kestenMomentRatio p).const_mul (kestenEdgeSlope p ^ k))
    (mul_ne_zero (pow_ne_zero _ (kestenEdgeSlope_pos p).ne') (kestenEdgeScale_pos p).ne')
  change Tendsto (fun n : ℕ => (((n : ℝ) + 2) ^ k * kestenEdgeRemainder p n k) /
    (kestenEdgeSlope p ^ k * kestenMomentRatio p n)) atTop
    (𝓝 ((kestenEdgeScale p * kestenEdgeSlope p ^ k * semicircleEdgeCoefficient k) /
      (kestenEdgeSlope p ^ k * kestenEdgeScale p))) at h
  have hc : (kestenEdgeScale p * kestenEdgeSlope p ^ k * semicircleEdgeCoefficient k) /
      (kestenEdgeSlope p ^ k * kestenEdgeScale p) = semicircleEdgeCoefficient k := by
    field_simp [(kestenEdgeScale_pos p).ne', (kestenEdgeSlope_pos p).ne']
  have he (n : ℕ) : ((n : ℝ) + 2) ^ k * kestenTiltedGapMoment p n k =
      (((n : ℝ) + 2) ^ k * kestenEdgeRemainder p n k) /
        (kestenEdgeSlope p ^ k * kestenMomentRatio p n) := by
    rw [kestenTiltedGapMoment_eq]
    unfold kestenEdgeRemainder kestenMomentRatio
    field_simp [(kestenMoment_even_pos p n).ne', (catalan_real_pos n).ne',
      (kestenEdgeSlope_pos p).ne']
  simpa only [he, hc] using h

/-- All rescaled gap moments have an explicit bound uniform in the weighting degree. -/
theorem scaled_kestenTiltedGapMoment_le (p : Nat.Primes) (n k : ℕ) :
    ((n : ℝ) + 2) ^ k * kestenTiltedGapMoment p n k ≤
      kestenEdgeScale p * semicircleEdgeCoefficient k := by
  have hb : kestenTiltedGapMoment p n k ≤
      kestenEdgeScale p * (semicircleEdgeMoment n k / (catalan n : ℝ)) := by
    rw [kestenTiltedGapMoment_eq]
    calc
      _ ≤ kestenEdgeMoment p n k / (catalan n : ℝ) :=
        div_le_div_of_nonneg_left (kestenEdgeMoment_nonneg p n k) (catalan_real_pos n)
          (catalan_le_kestenMoment_even p n)
      _ ≤ (kestenEdgeScale p * semicircleEdgeMoment n k) / (catalan n : ℝ) :=
        div_le_div_of_nonneg_right (kestenEdgeMoment_le p n k) (catalan_real_pos n).le
      _ = _ := by ring
  have hj := mul_le_mul_of_nonneg_left (semicircleEdgeMoment_ratio_le n k)
    (show 0 ≤ ((n : ℝ) + 2) ^ k by positivity)
  have hc : ((n : ℝ) + 2) ^ k *
      (semicircleEdgeCoefficient k / ((n : ℝ) + 2) ^ k) = semicircleEdgeCoefficient k := by
    have hn : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp [hn]
  rw [hc] at hj
  calc
    _ ≤ ((n : ℝ) + 2) ^ k *
        (kestenEdgeScale p * (semicircleEdgeMoment n k / (catalan n : ℝ))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = kestenEdgeScale p *
        (((n : ℝ) + 2) ^ k * (semicircleEdgeMoment n k / (catalan n : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hj (kestenEdgeScale_pos p).le

/-- The first rescaled gap moment tends to six, independently of the prime. -/
theorem tendsto_kestenTiltedGapMoment_one_scaled (p : Nat.Primes) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 2) * kestenTiltedGapMoment p n 1) atTop (𝓝 6) := by
  have hc : semicircleEdgeCoefficient 1 = 6 := by norm_num [semicircleEdgeCoefficient]
  simpa only [pow_one, hc] using tendsto_scaled_kestenTiltedGapMoment p 1

/-- The second rescaled gap moment tends to sixty, independently of the prime. -/
theorem tendsto_kestenTiltedGapMoment_two_scaled (p : Nat.Primes) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 2) ^ 2 * kestenTiltedGapMoment p n 2) atTop (𝓝 60) := by
  have hc : semicircleEdgeCoefficient 2 = 60 := by norm_num [semicircleEdgeCoefficient, Finset.prod_range_succ]
  simpa only [hc] using tendsto_scaled_kestenTiltedGapMoment p 2

/-- The mean gap tends to zero under high even-power weighting. -/
theorem tendsto_kestenTiltedGapMoment_one (p : Nat.Primes) :
    Tendsto (fun n : ℕ => kestenTiltedGapMoment p n 1) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (𝓝 4)).sub
    (tendsto_kestenMoment_successive_ratio p)
  simpa only [kestenTiltedGapMoment_one, sub_self] using h

/-- An explicit Markov bound controls mass separated from both spectral endpoints. -/
theorem kestenPowerTilt_interior_bound (p : Nat.Primes) (n : ℕ) (r : ℝ) :
    (kestenPowerTilt p n : Measure (Icc (-2 : ℝ) 2)).real
        {x | Real.exp r ≤ 4 - (x : ℝ) ^ 2} ≤
      kestenTiltedGapMoment p n 1 / Real.exp r := by
  have hi : Integrable (fun x : Icc (-2 : ℝ) 2 => 4 - (x : ℝ) ^ 2)
      (kestenPowerTilt p n : Measure (Icc (-2 : ℝ) 2)) :=
    (by fun_prop : Continuous (fun x : Icc (-2 : ℝ) 2 => 4 - (x : ℝ) ^ 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall kestenInterval_gap_nonneg) hi (Real.exp r)
  apply (le_div_iff₀ (Real.exp_pos r)).mpr
  simpa only [kestenTiltedGapMoment, pow_one, mul_comm] using h

/-- Every fixed interior region loses all mass in the high-power limit. -/
theorem tendsto_kestenPowerTilt_interior_mass (p : Nat.Primes) (r : ℝ) :
    Tendsto (fun n : ℕ => (kestenPowerTilt p n : Measure (Icc (-2 : ℝ) 2)).real
      {x | Real.exp r ≤ 4 - (x : ℝ) ^ 2}) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => measureReal_nonneg) (fun n => kestenPowerTilt_interior_bound p n r)
  simpa only [zero_div] using (tendsto_kestenTiltedGapMoment_one p).div_const (Real.exp r)

end
end GaloisForLFunctions.SelbergClass.Primon

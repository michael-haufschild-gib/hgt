import GaloisForLFunctions.SelbergClass.Primon.KestenEdgeExpansion

/-!
# Sharp spectral-edge asymptotics at every order

For each fixed prime, even moments divided by Catalan numbers tend to the
endpoint density ratio. More generally, every remainder in the finite
edge expansion has a sharp leading coefficient. The mixed Wallis
recurrence proves these limits and an explicit bound for the first correction.
-/

open Filter Topology Finset
open scoped BigOperators

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

private theorem tendsto_edgeDenominator_inv (j : ℕ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + j + 2)⁻¹) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) + j + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2
      (tendsto_atTop_add_const_right _ (j : ℝ) tendsto_natCast_atTop_atTop)
  exact tendsto_inv_atTop_zero.comp h

private theorem tendsto_edgeDenominator_ratio (j : ℕ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 2) / ((n : ℝ) + j + 2)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
    ((tendsto_edgeDenominator_inv j).const_mul (j : ℝ))
  have he (n : ℕ) : ((n : ℝ) + 2) / ((n : ℝ) + j + 2) =
      1 - (j : ℝ) * ((n : ℝ) + j + 2)⁻¹ := by
    have hn : (n : ℝ) + j + 2 ≠ 0 := by positivity
    field_simp [hn]
    ring
  simpa only [mul_zero, sub_zero, ← he] using h

/-- The exact leading coefficient of every normalized semicircle edge moment. -/
theorem tendsto_scaled_semicircleEdgeMoment (K : ℕ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 2) ^ K *
      (semicircleEdgeMoment n K / (catalan n : ℝ))) atTop (𝓝 (semicircleEdgeCoefficient K)) := by
  induction K with
  | zero =>
    have he (n : ℕ) : ((n : ℝ) + 2) ^ 0 *
        (semicircleEdgeMoment n 0 / (catalan n : ℝ)) = 1 := by
      rw [pow_zero, one_mul, semicircleEdgeMoment_zero, div_self (catalan_real_pos n).ne']
    simpa only [he, semicircleEdgeCoefficient, prod_range_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  | succ K ih =>
    have h := ((tendsto_edgeDenominator_ratio K).const_mul (2 * (2 * (K : ℝ) + 3))).mul ih
    have he (n : ℕ) : ((n : ℝ) + 2) ^ (K + 1) *
        (semicircleEdgeMoment n (K + 1) / (catalan n : ℝ)) =
        (2 * (2 * (K : ℝ) + 3) * (((n : ℝ) + 2) / ((n : ℝ) + K + 2))) *
          (((n : ℝ) + 2) ^ K * (semicircleEdgeMoment n K / (catalan n : ℝ))) := by
      rw [semicircleEdgeMoment_succ, pow_succ]
      ring
    rw [show semicircleEdgeCoefficient (K + 1) =
      (2 * (2 * (K : ℝ) + 3)) * semicircleEdgeCoefficient K by
        unfold semicircleEdgeCoefficient
        rw [prod_range_succ, mul_comm]]
    simpa only [he, mul_one] using h

/-- After scaling by one lower power, the next remainder vanishes. -/
theorem tendsto_scaled_kestenEdgeRemainder_succ (p : Nat.Primes) (K : ℕ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 2) ^ K * kestenEdgeRemainder p n (K + 1))
      atTop (𝓝 0) := by
  have hb (n : ℕ) : ((n : ℝ) + 2) ^ K * kestenEdgeRemainder p n (K + 1) ≤
      (kestenEdgeScale p * kestenEdgeSlope p ^ (K + 1) * semicircleEdgeCoefficient (K + 1)) *
        ((n : ℝ) + 2)⁻¹ := by
    have h := mul_le_mul_of_nonneg_left (kestenEdgeRemainder_le p n (K + 1))
      (show 0 ≤ ((n : ℝ) + 2) ^ K by positivity)
    calc
      _ ≤ ((n : ℝ) + 2) ^ K *
          (kestenEdgeScale p * kestenEdgeSlope p ^ (K + 1) * semicircleEdgeCoefficient (K + 1) /
            ((n : ℝ) + 2) ^ (K + 1)) := h
      _ = _ := by
        have hn : (n : ℝ) + 2 ≠ 0 := by positivity
        rw [pow_succ]
        field_simp [hn]
        rw [pow_succ]
        ring
  have ht := (tendsto_edgeDenominator_inv 0).const_mul
    (kestenEdgeScale p * kestenEdgeSlope p ^ (K + 1) * semicircleEdgeCoefficient (K + 1))
  apply squeeze_zero (fun n => mul_nonneg (by positivity) (kestenEdgeRemainder_nonneg p n (K + 1))) hb
  simpa only [Nat.cast_zero, add_zero, mul_zero] using ht

/-- Every finite expansion has a sharp, nonzero leading remainder coefficient. -/
theorem tendsto_scaled_kestenEdgeRemainder (p : Nat.Primes) (K : ℕ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 2) ^ K * kestenEdgeRemainder p n K)
      atTop (𝓝 (kestenEdgeScale p * kestenEdgeSlope p ^ K * semicircleEdgeCoefficient K)) := by
  have h := ((tendsto_scaled_semicircleEdgeMoment K).const_mul
    (kestenEdgeScale p * kestenEdgeSlope p ^ K)).sub (tendsto_scaled_kestenEdgeRemainder_succ p K)
  have he (n : ℕ) : ((n : ℝ) + 2) ^ K * kestenEdgeRemainder p n K =
      (kestenEdgeScale p * kestenEdgeSlope p ^ K) *
        (((n : ℝ) + 2) ^ K * (semicircleEdgeMoment n K / (catalan n : ℝ))) -
          ((n : ℝ) + 2) ^ K * kestenEdgeRemainder p n (K + 1) := by
    linear_combination ((n : ℝ) + 2) ^ K * (kestenEdgeRemainder_step p n K)
  simpa only [he, sub_zero] using h

/-- High even moments retain exactly the density ratio at the spectral endpoints. -/
theorem tendsto_kestenMomentRatio (p : Nat.Primes) :
    Tendsto (kestenMomentRatio p) atTop (𝓝 (kestenEdgeScale p)) := by
  simpa only [pow_zero, one_mul, mul_one, kestenEdgeRemainder_zero,
    semicircleEdgeCoefficient, prod_range_zero] using tendsto_scaled_kestenEdgeRemainder p 0

/-- The signed approximation error has the predicted sharp coefficient at every order. -/
theorem tendsto_scaled_kestenMomentRatio_error (p : Nat.Primes) (K : ℕ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 2) ^ K *
      (kestenMomentRatio p n - kestenEdgeApproximation p n K)) atTop
      (𝓝 ((-1 : ℝ) ^ K *
        (kestenEdgeScale p * kestenEdgeSlope p ^ K * semicircleEdgeCoefficient K))) := by
  have h := (tendsto_scaled_kestenEdgeRemainder p K).const_mul ((-1 : ℝ) ^ K)
  have he (n : ℕ) : ((n : ℝ) + 2) ^ K *
      (kestenMomentRatio p n - kestenEdgeApproximation p n K) =
      (-1 : ℝ) ^ K * (((n : ℝ) + 2) ^ K * kestenEdgeRemainder p n K) := by
    linear_combination ((n : ℝ) + 2) ^ K *
      (kestenMomentRatio_eq_edgeApproximation_add p n K)
  simpa only [he] using h

/-- The high-order prime moments have an explicit prime-dependent Catalan ratio. -/
theorem tendsto_kestenMoment_div_catalan (p : Nat.Primes) :
    Tendsto (fun n : ℕ => kestenMoment p (2 * n) / (catalan n : ℝ)) atTop
      (𝓝 ((p : ℝ) * ((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 2)) :=
  tendsto_kestenMomentRatio p

/-- The first approach to the endpoint ratio has coefficient `6 M a`. -/
theorem tendsto_kestenMomentRatio_first_correction (p : Nat.Primes) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 2) * (kestenEdgeScale p - kestenMomentRatio p n))
      atTop (𝓝 (6 * kestenEdgeScale p * kestenEdgeSlope p)) := by
  have h := tendsto_scaled_kestenEdgeRemainder p 1
  have hc : semicircleEdgeCoefficient 1 = 6 := by norm_num [semicircleEdgeCoefficient]
  rw [hc, show kestenEdgeScale p * kestenEdgeSlope p ^ 1 * 6 =
    6 * kestenEdgeScale p * kestenEdgeSlope p by ring] at h
  simpa only [pow_one, kestenEdgeRemainder_one] using h

/-- The first correction coefficient, expressed directly in the prime. -/
theorem tendsto_kestenMoment_div_catalan_first_correction (p : Nat.Primes) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 2) *
      ((p : ℝ) * ((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 2 -
        kestenMoment p (2 * n) / (catalan n : ℝ))) atTop
      (𝓝 (6 * (p : ℝ) ^ 2 * ((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 4)) := by
  have he : 6 * kestenEdgeScale p * kestenEdgeSlope p =
      6 * (p : ℝ) ^ 2 * ((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 4 := by
    have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
    have hp1 : (p : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith only [hp])
    unfold kestenEdgeScale kestenEdgeSlope
    field_simp [hp1]
  have h := tendsto_kestenMomentRatio_first_correction p
  rw [he] at h
  exact h

/-- An explicit second-order bound controls the first scaled correction. -/
theorem kestenMomentRatio_first_correction_bounds (p : Nat.Primes) (n : ℕ) :
    0 ≤ 6 * kestenEdgeScale p * kestenEdgeSlope p -
        ((n : ℝ) + 2) * (kestenEdgeScale p - kestenMomentRatio p n) ∧
      6 * kestenEdgeScale p * kestenEdgeSlope p -
        ((n : ℝ) + 2) * (kestenEdgeScale p - kestenMomentRatio p n) ≤
          60 * kestenEdgeScale p * kestenEdgeSlope p ^ 2 / ((n : ℝ) + 3) := by
  have hn : (n : ℝ) + 2 ≠ 0 := by positivity
  have hs := kestenEdgeRemainder_step p n 1
  rw [pow_one, semicircleEdgeMoment_ratio_one] at hs
  have he : 6 * kestenEdgeScale p * kestenEdgeSlope p -
      ((n : ℝ) + 2) * (kestenEdgeScale p - kestenMomentRatio p n) =
      ((n : ℝ) + 2) * kestenEdgeRemainder p n 2 := by
    rw [← kestenEdgeRemainder_one]
    have hh := congrArg (fun x : ℝ => ((n : ℝ) + 2) * x) hs
    field_simp [hn] at hh
    nlinarith only [hh]
  rw [he]
  refine ⟨mul_nonneg (by positivity) (kestenEdgeRemainder_nonneg p n 2), ?_⟩
  have h := mul_le_mul_of_nonneg_left (kestenEdgeRemainder_le_moment p n 2)
    (show 0 ≤ (n : ℝ) + 2 by positivity)
  rw [semicircleEdgeMoment_ratio_two] at h
  calc
    _ ≤ ((n : ℝ) + 2) * (kestenEdgeScale p * kestenEdgeSlope p ^ 2 *
      (60 / (((n : ℝ) + 2) * ((n : ℝ) + 3)))) := h
    _ = _ := by
      have hn3 : (n : ℝ) + 3 ≠ 0 := by positivity
      field_simp [hn, hn3]

end
end GaloisForLFunctions.SelbergClass.Primon

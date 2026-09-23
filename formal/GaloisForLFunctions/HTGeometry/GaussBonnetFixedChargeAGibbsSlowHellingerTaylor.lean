import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsInformationRatios

/-!
# Square-root remainder for the critical thermal kernel

A mathematical consequence of the prescription-A critical kernel extracted from
arXiv:2609.00025. The corpus's mass-dispersion rationalization argument motivates
an exact real square-root factorization for the positive slow Gibbs family.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

private theorem sqrt_distance_cubic_remainder (x : ℝ) (hx : 0 ≤ 1 + x) :
    |(Real.sqrt (1 + x) - 1) ^ (2 : ℕ) - x ^ (2 : ℕ) / 4| ≤ |x| ^ (3 : ℕ) := by
  set s := Real.sqrt (1 + x)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s ^ (2 : ℕ) = 1 + x := Real.sq_sqrt hx
  have hx' : x = (s - 1) * (s + 1) := by nlinarith
  have he : (s - 1) ^ (2 : ℕ) - x ^ (2 : ℕ) / 4 = -((s - 1) ^ (3 : ℕ) * (s + 3) / 4) := by
    rw [hx']
    ring
  change |(s - 1) ^ (2 : ℕ) - x ^ (2 : ℕ) / 4| ≤ |x| ^ (3 : ℕ)
  rw [he, abs_neg, abs_div, abs_mul, abs_pow,
    abs_of_nonneg (by linarith : 0 ≤ s + 3), abs_of_pos (by norm_num : (0 : ℝ) < 4),
    hx', abs_mul, abs_of_nonneg (by linarith : 0 ≤ s + 1), mul_pow]
  have hc : (s + 3) / 4 ≤ (s + 1) ^ (3 : ℕ) := by
    nlinarith [pow_nonneg hs 3, sq_nonneg s]
  calc
    _ = |s - 1| ^ (3 : ℕ) * ((s + 3) / 4) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (pow_nonneg (abs_nonneg _) 3)

/-- Each slow Gibbs coordinate has a controlled cubic Hellinger remainder. -/
theorem egbFixedChargeAGibbsSlow_hellinger_coordinate_remainder
    (n m : ℕ) (i : Fin (2 ^ (n + 3))) :
    |(Real.sqrt (1 + egbFixedChargeAGibbsSlowDisplacement n m i) - 1) ^ (2 : ℕ) -
        egbFixedChargeAGibbsSlowDisplacement n m i ^ (2 : ℕ) / 4| ≤
      |egbFixedChargeAGibbsSlowDisplacement n m i| ^ (3 : ℕ) := by
  apply sqrt_distance_cubic_remainder
  have h := egbFixedChargeAGibbsSlowDisplacement_half_bound n m i
  have hl := neg_abs_le (egbFixedChargeAGibbsSlowDisplacement n m i)
  linarith

/-- Hellinger distance of the actual Gibbs evolution in displacement coordinates. -/
theorem egbFixedChargeAGibbsSlow_hellinger_displacement_formula (n m : ℕ) :
    finitePacketHellinger
        (egbFixedChargeAGibbsMarkovPopulation n m 1 (egbFixedChargeAGibbsSlowEnergy n))
        (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) ^ (2 : ℕ) =
      (∑ i : Fin (2 ^ (n + 3)),
        (Real.sqrt (1 + egbFixedChargeAGibbsSlowDisplacement n m i) - 1) ^ (2 : ℕ)) /
          (2 : ℝ) ^ (n + 3) := by
  have hn : (0 : ℝ) < 2 ^ (n + 3) := by positivity
  have hs : Real.sqrt ((2 : ℝ) ^ (n + 3)) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  rw [egbFixedChargeAHellinger_coordinate_square, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [egbFixedChargeAGibbsSlowDisplacement_population,
    Real.sqrt_div' _ hn.le, Real.sqrt_inv]
  calc
    _ = ((Real.sqrt (1 + egbFixedChargeAGibbsSlowDisplacement n m i) - 1) /
        Real.sqrt ((2 : ℝ) ^ (n + 3))) ^ (2 : ℕ) := by field_simp <;> ring
    _ = _ := by rw [div_pow, Real.sq_sqrt hn.le]

end
end GaloisForLFunctions.HTGeometry

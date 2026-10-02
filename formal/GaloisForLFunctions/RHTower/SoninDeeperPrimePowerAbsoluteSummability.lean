import GaloisForLFunctions.RHTower.SoninRegularizedPrimeCoefficientBudget

noncomputable section
namespace RHTower

/-- Increasing depth retains an extra inverse-square-root prime factor. -/
theorem norm_soninLogPrimePowerCoefficient_succ_le
    (p : Nat.Primes) (k : ℕ) :
    ‖soninLogPrimePowerCoefficient (p, k + 1)‖ ≤
      (Real.sqrt (p : ℝ))⁻¹ * ‖soninLogPrimePowerCoefficient (p, k)‖ := by
  let r := (Real.sqrt (p : ℝ))⁻¹
  have hr : 0 ≤ r := by positivity
  rw [soninLogPrimePowerCoefficient_eq_sqrtInvPow_div,
    soninLogPrimePowerCoefficient_eq_sqrtInvPow_div]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt (p : ℝ))⁻¹^(k+1+2) / ((k+1 : ℕ) + 2 : ℝ)),
    abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt (p : ℝ))⁻¹^(k+2) / (k+2 : ℝ))]
  change r^(k+1+2) / ((k+1 : ℕ) + 2 : ℝ) ≤ r * (r^(k+2) / (k+2 : ℝ))
  rw [show k+1+2 = (k+2)+1 by omega, pow_succ]
  calc
    _ ≤ (r^(k+2) * r) / (k+2 : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by push_cast; linarith)
    _ = _ := by ring

private theorem sum_deeper_norm_le (p : Nat.Primes) (s : Finset ℕ) :
    ∑ k ∈ s, ‖soninLogPrimePowerCoefficient (p, k+1)‖ ≤
      (Real.sqrt (p : ℝ))⁻¹ * (2 / (p : ℝ)) := by
  calc
    _ ≤ ∑ k ∈ s, (Real.sqrt (p : ℝ))⁻¹ * ‖soninLogPrimePowerCoefficient (p, k)‖ :=
      Finset.sum_le_sum (fun k _ => norm_soninLogPrimePowerCoefficient_succ_le p k)
    _ = (Real.sqrt (p : ℝ))⁻¹ * ∑ k ∈ s, ‖soninLogPrimePowerCoefficient (p, k)‖ :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_depth_norm_soninLogPrimePowerCoefficient_le p s)
      (by positivity)

private theorem deeper_prime_majorant_eq_rpow (p : Nat.Primes) :
    (Real.sqrt (p : ℝ))⁻¹ * (2 / (p : ℝ)) = 2 * (p : ℝ)^(-(3 : ℝ)/2) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  calc
    _ = 2 * ((Real.sqrt (p : ℝ))⁻¹ * (p : ℝ)⁻¹) := by ring
    _ = 2 * ((p : ℝ)^(-(1/(2:ℝ))) * (p : ℝ)^(-(1:ℝ))) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_neg hp.le, Real.rpow_neg_one]
    _ = _ := by rw [← Real.rpow_add hp]; congr 2; ring

/-- All original depths at least three are jointly absolutely summable. -/
theorem summable_norm_soninLogPrimePowerCoefficient_deeper :
    Summable (fun pk : Nat.Primes × ℕ => ‖soninLogPrimePowerCoefficient (pk.1, pk.2+1)‖) := by
  have hprime : Summable (fun p : Nat.Primes => (Real.sqrt (p : ℝ))⁻¹ * (2 / (p : ℝ))) := by
    have hn : Summable (fun n : ℕ => (n : ℝ)^(-(3 : ℝ)/2)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    have hp := hn.comp_injective (i := fun p : Nat.Primes => (p : ℕ))
      (fun _ _ h => Subtype.ext h)
    exact (hp.mul_left 2).congr (fun p => (deeper_prime_majorant_eq_rpow p).symm)
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  constructor
  · intro p
    exact summable_of_sum_le (fun _ => norm_nonneg _) (sum_deeper_norm_le p)
  · exact Summable.of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => norm_nonneg _))
      (fun p => Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) (sum_deeper_norm_le p)) hprime
end RHTower

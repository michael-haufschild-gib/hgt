import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheResonatorMeanOfZeta
import GaloisForLFunctions.RHTower.Sieve.DivisorBound
import GaloisForLFunctions.RHTower.Sieve.SubCriticalPowerSum
import GaloisForLFunctions.RHTower.SqrtCarrierCertificate

/-!
# Divisor bounds for growing resonator coefficients

Cauchy–Schwarz is applied on each product fibre, whose cardinality is
bounded by the divisor function. This retains only an arbitrarily small
power of the resonator support in the coefficient energy.
-/

noncomputable section
open Real Finset Filter Topology
open _root_.RHTower

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

/-- The fibre cost is the number of divisors of the product, independently
of the size of the full resonator support. -/
theorem norm_resonator_divisor_sum_sq_le {ε : ℝ} (hε : 0 < ε)
    {k : ℕ} (hk : k ≠ 0) {B : Finset ℕ} (hB : B ⊆ k.divisors)
    (r : ℕ → ℂ) (σ : ℝ) :
    ‖∑ m ∈ B, r m * lineWeight σ (k / m)‖ ^ 2 ≤
      Sieve.divisorBoundConst ε * (k : ℝ) ^ ε *
        ∑ m ∈ B, ‖r m‖ ^ 2 * ((k / m : ℕ) : ℝ) ^ (-2 * σ) := by
  have hcard : (B.card : ℝ) ≤ Sieve.divisorBoundConst ε * (k : ℝ) ^ ε :=
    (Nat.cast_le.mpr (Finset.card_le_card hB)).trans (Sieve.card_divisors_le_rpow hε hk)
  have hterm (m : ℕ) : ‖r m * lineWeight σ (k / m)‖ ^ 2 =
      ‖r m‖ ^ 2 * ((k / m : ℕ) : ℝ) ^ (-2 * σ) := by
    rw [norm_mul, norm_lineWeight, mul_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    norm_num
    ring
  calc
    _ ≤ (∑ m ∈ B, ‖r m * lineWeight σ (k / m)‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (B.card : ℝ) * ∑ m ∈ B, ‖r m * lineWeight σ (k / m)‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ (Sieve.divisorBoundConst ε * (k : ℝ) ^ ε) *
        ∑ m ∈ B, ‖r m * lineWeight σ (k / m)‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hcard (sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by simp_rw [hterm]

/-- Full convolution coefficients obey the divisor-weighted energy bound. -/
theorem norm_resonatorCoeff_sq_le_divisor_weight {ε : ℝ} (hε : 0 < ε)
    (A : Finset ℕ) (r : ℕ → ℂ) (σ : ℝ) {k : ℕ} (hk : k ≠ 0) :
    ‖resonatorCoeff A r σ k‖ ^ 2 ≤
      Sieve.divisorBoundConst ε * (k : ℝ) ^ ε *
        ∑ m ∈ A.filter (· ∣ k), ‖r m‖ ^ 2 * ((k / m : ℕ) : ℝ) ^ (-2 * σ) := by
  apply norm_resonator_divisor_sum_sq_le hε hk
  intro m hm
  exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hm).2, hk⟩

/-- The same bound holds for every finite zeta truncation. -/
theorem norm_truncResonatorCoeff_sq_le_divisor_weight {ε : ℝ} (hε : 0 < ε)
    (A : Finset ℕ) (r : ℕ → ℂ) (σ : ℝ) (N : ℕ) {k : ℕ} (hk : k ≠ 0) :
    ‖truncResonatorCoeff A r σ N k‖ ^ 2 ≤
      Sieve.divisorBoundConst ε * (k : ℝ) ^ ε *
        ∑ m ∈ A.filter (fun m => m ∣ k ∧ k / m ≤ N),
          ‖r m‖ ^ 2 * ((k / m : ℕ) : ℝ) ^ (-2 * σ) := by
  apply norm_resonator_divisor_sum_sq_le hε hk
  intro m hm
  exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hm).2.1, hk⟩

#print axioms norm_resonatorCoeff_sq_le_divisor_weight

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.PrimeConductorDilationEnergy

/-!
# A fixed conductor has bounded upward square rows

Complete-period prime-dilation energy equals conductor adjunction.
Every individual residue is bounded by the full period square mass, giving
a horizon-independent bound for its upward square row.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open RenormalizedArithmeticPotentialTheory SuccessorShellArithmetic
  ArithmeticIntersectionTheory BezoutValuationIncidence

/-- Averaged square jumps of one normalized mode sum to its adjunction weight. -/
theorem hasSum_normalizedMode_period_square {m : ℕ} (hm : 0 < m) :
    HasSum (fun k : ℕ => (1 / (m : ℝ)) * Λ k / k *
      ∑ n ∈ range m, (normalizedRamanujanMode m (k * n) - normalizedRamanujanMode m n) ^ 2)
      (Real.log m + tameDifferent m) := by
  have hmm : m ∈ m.divisors := Nat.mem_divisors.mpr ⟨dvd_refl m, hm.ne'⟩
  let f : ℕ → ℝ := fun d => if d = m then 1 else 0
  have hpacket (n : ℕ) : divisorRamanujanPacket m f n = ramanujanLagCoefficient m n := by
    simp only [divisorRamanujanPacket, f, ite_mul, one_mul, zero_mul,
      sum_ite_eq', if_pos hmm]
  have h := hasSum_primeDilationPacket_sq hm f
  simp only [hpacket, f, ite_pow, one_pow, zero_pow two_ne_zero, mul_ite,
    mul_one, mul_zero, sum_ite_eq', if_pos hmm] at h
  have hphi : (m.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hm).ne'
  have h' := h.mul_left ((m.totient : ℝ)⁻¹)
  have he : (m.totient : ℝ)⁻¹ * ((m.totient : ℝ) * (Real.log m + tameDifferent m)) =
      Real.log m + tameDifferent m := by field_simp [hphi]
  rw [he] at h'
  apply h'.congr_fun
  intro k
  simp only [normalizedRamanujanMode_eq_coefficient hm, ← sub_div, div_pow,
    Real.sq_sqrt (Nat.cast_nonneg m.totient), ← sum_div]
  ring

/-- Every finite upward square row is bounded by one full period's adjunction mass. -/
theorem normalizedMode_upward_square_le {m : ℕ} (hm : 0 < m) (Y n : ℕ) :
    (∑ k ∈ Icc 1 Y, Λ k / k *
      (normalizedRamanujanMode m (k * n) - normalizedRamanujanMode m n) ^ 2) ≤
      (m : ℝ) * (Real.log m + tameDifferent m) := by
  have hsum := hasSum_normalizedMode_period_square hm
  have hnonneg (k : ℕ) : 0 ≤ (1 / (m : ℝ)) * Λ k / k *
      ∑ r ∈ range m, (normalizedRamanujanMode m (k * r) - normalizedRamanujanMode m r) ^ 2 := by
    exact mul_nonneg (div_nonneg (mul_nonneg (by positivity) vonMangoldt_nonneg)
      (Nat.cast_nonneg k)) (sum_nonneg fun _ _ => sq_nonneg _)
  have htotal := hsum.summable.sum_le_tsum (Icc 1 Y) (fun k _ => hnonneg k)
  rw [hsum.tsum_eq] at htotal
  have hperiod (k : ℕ) : Function.Periodic
      (fun r => (normalizedRamanujanMode m (k * r) - normalizedRamanujanMode m r) ^ 2) m := by
    intro r
    have h := (normalizedRamanujanMode_periodic hm).nat_mul k (k * r)
    simp only [Nat.cast_id] at h
    dsimp only
    rw [Nat.mul_add, h, normalizedRamanujanMode_periodic hm r]
  have hpoint (k : ℕ) :
      (normalizedRamanujanMode m (k * n) - normalizedRamanujanMode m n) ^ 2 ≤
        ∑ r ∈ range m, (normalizedRamanujanMode m (k * r) - normalizedRamanujanMode m r) ^ 2 := by
    rw [← (hperiod k).map_mod_nat n]
    exact single_le_sum
      (f := fun r => (normalizedRamanujanMode m (k * r) - normalizedRamanujanMode m r) ^ 2)
      (fun r _ => sq_nonneg _)
      (mem_range.mpr (Nat.mod_lt n hm))
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  calc
    _ ≤ ∑ k ∈ Icc 1 Y, Λ k / k *
        ∑ r ∈ range m, (normalizedRamanujanMode m (k * r) - normalizedRamanujanMode m r) ^ 2 :=
      sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hpoint k)
        (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))
    _ = (m : ℝ) * ∑ k ∈ Icc 1 Y, (1 / (m : ℝ)) * Λ k / k *
        ∑ r ∈ range m, (normalizedRamanujanMode m (k * r) - normalizedRamanujanMode m r) ^ 2 := by
      rw [mul_sum]
      exact sum_congr rfl fun k _ => by field_simp [hmR]
    _ ≤ _ := mul_le_mul_of_nonneg_left htotal (Nat.cast_nonneg m)

#print axioms hasSum_normalizedMode_period_square
#print axioms normalizedMode_upward_square_le

end GaloisForLFunctions.CriticalScaleArithmeticRigidity

import GaloisForLFunctions.BezoutValuationIncidence.Sieve.ResidueSlices
import GaloisForLFunctions.BezoutValuationIncidence.Sieve.WeightedResidueCovariance

/-!
# Prime covariance with fixed periodic factors

Expansion by residue slices preserves the cross-prime cancellation and
retains the exact period mean in each equal-prime collision block.
-/

noncomputable section
set_option autoImplicit false
open Finset
namespace GaloisForLFunctions.BezoutValuationIncidence

/-- A finite residue profile is exactly its indicator expansion. -/
theorem residue_profile_expansion {M : ℕ} (hM : 0 < M) (z : ℕ → ℝ) (n : ℕ) :
    z (n % M) = ∑ r ∈ range M, z r * residueIndicator M r n := by
  have he (r : ℕ) (hr : r ∈ range M) : z r * residueIndicator M r n =
      if n % M = r then z r else 0 := by
    simp only [residueIndicator, Nat.ModEq, Nat.mod_eq_of_lt (mem_range.mp hr),
      mul_ite, mul_one, mul_zero]
  rw [sum_congr rfl he, sum_ite_eq, if_pos (mem_range.mpr (Nat.mod_lt n hM))]

private theorem residue_profile_product_sum {M : ℕ} (hM : 0 < M)
    (z x y : ℕ → ℝ) (S : Finset ℕ) :
    (∑ n ∈ S, z (n % M) * x n * y n) =
      ∑ r ∈ range M, z r * ∑ n ∈ S, residueIndicator M r n * x n * y n := by
  simp_rw [residue_profile_expansion hM z, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro r _
  rw [mul_sum]
  exact sum_congr rfl fun n _ => by ring

/-- Any fixed coprime periodic factor preserves zero cross-prime covariance. -/
theorem periodic_coprime_covariance {A B M p q a b : ℕ}
    (hAB : A ≤ B) (hM : 0 < M) (hp : 0 < p) (hq : 0 < q)
    (hMp : M.Coprime p) (hMq : M.Coprime q) (hpq : p.Coprime q) (z : ℕ → ℝ) :
    |∑ n ∈ Ioc A B, z (n % M) * centeredResidue p a n * centeredResidue q b n| ≤
      ((1 + 1 / (p : ℝ)) * (1 + 1 / (q : ℝ))) * ∑ r ∈ range M, |z r| := by
  rw [residue_profile_product_sum hM]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ r ∈ range M, |z r| * ((1 + 1 / (p : ℝ)) * (1 + 1 / (q : ℝ))) := by
      apply sum_le_sum
      intro r _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (coprime_covariance_residue_slice (r := r) (a := a) (b := b) hAB hM hp hq hMp hMq hpq)
        (abs_nonneg _)
    _ = _ := by rw [← sum_mul, mul_comm]

/-- Equal-prime covariance is multiplied by the exact finite-period mean of the periodic factor. -/
theorem periodic_same_covariance {A B M p a b : ℕ}
    (hAB : A ≤ B) (hM : 0 < M) (hp : 0 < p) (hMp : M.Coprime p) (z : ℕ → ℝ) :
    |(∑ n ∈ Ioc A B, z (n % M) * centeredResidue p a n * centeredResidue p b n) -
      ((B : ℝ) - A) *
        ((if a ≡ b [MOD p] then 1 / (p : ℝ) else 0) - 1 / (p : ℝ) ^ 2) *
          ((∑ r ∈ range M, z r) / M)| ≤
      (1 + 1 / (p : ℝ)) ^ 2 * ∑ r ∈ range M, |z r| := by
  let μ : ℝ := (if a ≡ b [MOD p] then 1 / (p : ℝ) else 0) - 1 / (p : ℝ) ^ 2
  have he : (∑ n ∈ Ioc A B, z (n % M) * centeredResidue p a n * centeredResidue p b n) -
      ((B : ℝ) - A) * μ * ((∑ r ∈ range M, z r) / M) =
      ∑ r ∈ range M, z r *
        ((∑ n ∈ Ioc A B, residueIndicator M r n * centeredResidue p a n * centeredResidue p b n) -
          (((B : ℝ) - A) / M) * μ) := by
    rw [residue_profile_product_sum hM]
    rw [show ((B : ℝ) - A) * μ * ((∑ r ∈ range M, z r) / M) =
      ((((B : ℝ) - A) / M) * μ) * ∑ r ∈ range M, z r by ring,
      mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun r _ => by ring
  change |(∑ n ∈ Ioc A B, z (n % M) * centeredResidue p a n * centeredResidue p b n) -
    ((B : ℝ) - A) * μ * ((∑ r ∈ range M, z r) / M)| ≤ _
  rw [he]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ r ∈ range M, |z r| * (1 + 1 / (p : ℝ)) ^ 2 := by
      apply sum_le_sum
      intro r _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (same_covariance_residue_slice (r := r) (a := a) (b := b) hAB hM hp hMp)
        (abs_nonneg _)
    _ = _ := by rw [← sum_mul, mul_comm]

#print axioms periodic_coprime_covariance
#print axioms periodic_same_covariance

end GaloisForLFunctions.BezoutValuationIncidence

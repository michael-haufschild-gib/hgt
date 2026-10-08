import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticFiniteWeight
import Mathlib.Analysis.PSeries

/-!
# Explicit length cost in the finite-polynomial energy

Both the pole budget and the extraction budget cost at most a universal
constant times the coefficient energy and `(N+1)^(9/8)`.
-/

open Complex

noncomputable section

namespace RHTower.WeilSingularArithmetic

def sourceFiniteEnergy (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, (c m) ^ 2 / m

private theorem energy_nonneg (N : ℕ) (c : ℕ → ℝ) : 0 ≤ sourceFiniteEnergy N c :=
  Finset.sum_nonneg fun m _ => by positivity

private theorem moment_sq_le (N : ℕ) (c : ℕ → ℝ) (α : ℝ) :
    (∑ m ∈ Finset.Icc 1 N, |c m| * (m : ℝ) ^ α) ^ 2 ≤
      sourceFiniteEnergy N c * ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (2 * α + 1) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
    (fun m _ => by positivity) (fun m _ => by positivity)
  intro m hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  apply le_of_eq
  calc
    _ = (c m) ^ 2 * (m : ℝ) ^ (α * 2) := by
      rw [mul_pow, sq_abs, ← Real.rpow_mul_natCast hmR.le]
      norm_num
    _ = ((c m) ^ 2 / m) * (m : ℝ) ^ (2 * α + 1) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one, mul_assoc, ← Real.rpow_add hmR]
      congr 1
      congr 1
      ring

private theorem sum_nonneg_rpow_le (N : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    (∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ α) ≤ ((N : ℝ) + 1) ^ (α + 1) := by
  have hR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  calc
    _ ≤ ∑ _m ∈ Finset.Icc 1 N, ((N : ℝ) + 1) ^ α := by
      apply Finset.sum_le_sum
      intro m hm
      apply Real.rpow_le_rpow (by positivity) _ hα
      have : (m : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hm).2
      linarith
    _ = (N : ℝ) * ((N : ℝ) + 1) ^ α := by simp [Nat.card_Icc]
    _ ≤ ((N : ℝ) + 1) * ((N : ℝ) + 1) ^ α := by gcongr; linarith
    _ = _ := by rw [Real.rpow_add hR, Real.rpow_one]; ring

private theorem product_moment_le (N : ℕ) (c : ℕ → ℝ) (α β Z : ℝ)
    (hZ : 0 ≤ Z)
    (hb : (∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (2 * α + 1)) *
      (∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (2 * β + 1)) ≤
        Z * ((N : ℝ) + 1) ^ (9 / 4 : ℝ)) :
    (∑ m ∈ Finset.Icc 1 N, |c m| * (m : ℝ) ^ α) *
      (∑ m ∈ Finset.Icc 1 N, |c m| * (m : ℝ) ^ β) ≤
        Real.sqrt Z * sourceFiniteEnergy N c * ((N : ℝ) + 1) ^ (9 / 8 : ℝ) := by
  have hE := energy_nonneg N c
  have hR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hA : 0 ≤ ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (2 * α + 1) :=
    Finset.sum_nonneg fun m _ => by positivity
  have h := mul_le_mul (moment_sq_le N c α) (moment_sq_le N c β)
    (sq_nonneg _) (mul_nonneg hE hA)
  have hbudget := mul_le_mul_of_nonneg_left hb (sq_nonneg (sourceFiniteEnergy N c))
  have hsquare : ((∑ m ∈ Finset.Icc 1 N, |c m| * (m : ℝ) ^ α) *
      (∑ m ∈ Finset.Icc 1 N, |c m| * (m : ℝ) ^ β)) ^ 2 ≤
        (Real.sqrt Z * sourceFiniteEnergy N c * ((N : ℝ) + 1) ^ (9 / 8 : ℝ)) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hZ,
      ← Real.rpow_mul_natCast hR.le]
    norm_num only [Nat.cast_ofNat, show (9 / 8 : ℝ) * 2 = 9 / 4 by norm_num]
    nlinarith only [h, hbudget]
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsquare

/-- A single universal energy constant pays both arithmetic budgets at every length. -/
theorem exists_sourceFiniteEnergy_budget_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (c : ℕ → ℝ),
      (∑ m ∈ Finset.Icc 1 N, |c m| * (m : ℝ) ^ (-9 / 8 : ℝ)) *
        (∑ n ∈ Finset.Icc 1 N, |c n| * (n : ℝ) ^ (1 / 8 : ℝ)) ≤
          K * sourceFiniteEnergy N c * ((N : ℝ) + 1) ^ (9 / 8 : ℝ) ∧
      ‖sourceFiniteWeight N c 1‖ ≤
          K * sourceFiniteEnergy N c * ((N : ℝ) + 1) ^ (9 / 8 : ℝ) := by
  let Z : ℝ := ∑' m : ℕ, (m : ℝ) ^ (-5 / 4 : ℝ)
  have hZs : Summable (fun m : ℕ => (m : ℝ) ^ (-5 / 4 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hZ : 0 ≤ Z := tsum_nonneg fun m => by positivity
  refine ⟨Real.sqrt Z, Real.sqrt_nonneg _, fun N c => ?_⟩
  have hR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hsum : (∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-5 / 4 : ℝ)) ≤ Z :=
    Summable.sum_le_tsum _ (fun m _ => by positivity) hZs
  have h54 : (∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (5 / 4 : ℝ)) ≤
      ((N : ℝ) + 1) ^ (9 / 4 : ℝ) := by
    simpa only [show (5 / 4 : ℝ) + 1 = 9 / 4 by norm_num] using
      sum_nonneg_rpow_le N (show (0 : ℝ) ≤ 5 / 4 by norm_num)
  have h1 : (∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (1 : ℝ)) ≤ ((N : ℝ) + 1) ^ (2 : ℝ) := by
    simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using
      sum_nonneg_rpow_le N (show (0 : ℝ) ≤ 1 by norm_num)
  have hharm : (∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-1 : ℝ)) ≤
      Z * ((N : ℝ) + 1) ^ (1 / 4 : ℝ) := by
    calc
      _ ≤ ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-5 / 4 : ℝ) * ((N : ℝ) + 1) ^ (1 / 4 : ℝ) := by
        apply Finset.sum_le_sum
        intro m hm
        have hmR : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
        have hmN : (m : ℝ) ≤ (N : ℝ) + 1 := by
          have : (m : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hm).2
          linarith
        calc
          _ = (m : ℝ) ^ (-5 / 4 : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ) := by
            rw [← Real.rpow_add hmR]; norm_num
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hmR.le hmN (by norm_num)) (by positivity)
      _ = (∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-5 / 4 : ℝ)) * ((N : ℝ) + 1) ^ (1 / 4 : ℝ) :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hsum (by positivity)
  constructor
  · apply product_moment_le N c (-9 / 8) (1 / 8) Z hZ
    simpa only [show 2 * (-9 / 8 : ℝ) + 1 = -5 / 4 by norm_num,
      show 2 * (1 / 8 : ℝ) + 1 = 5 / 4 by norm_num] using
      mul_le_mul hsum h54 (Finset.sum_nonneg fun m _ => by positivity) hZ
  · apply (norm_sourceFiniteWeight_one_le N c).trans
    have h := product_moment_le N c (-1) 0 Z hZ
    simp only [Real.rpow_neg_one, Real.rpow_zero, mul_one] at h
    apply h
    have hb := mul_le_mul hharm h1 (Finset.sum_nonneg fun m _ => by positivity) (by positivity)
    have hb' : (∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-1 : ℝ)) *
        (∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (1 : ℝ)) ≤ Z * ((N : ℝ) + 1) ^ (9 / 4 : ℝ) := by
      calc
        _ ≤ (Z * ((N : ℝ) + 1) ^ (1 / 4 : ℝ)) * ((N : ℝ) + 1) ^ (2 : ℝ) := hb
        _ = Z * ((N : ℝ) + 1) ^ (9 / 4 : ℝ) := by
          rw [mul_assoc, ← Real.rpow_add hR]
          norm_num
    simpa only [show 2 * (-1 : ℝ) + 1 = -1 by norm_num,
      show 2 * (0 : ℝ) + 1 = 1 by norm_num] using hb'

end RHTower.WeilSingularArithmetic

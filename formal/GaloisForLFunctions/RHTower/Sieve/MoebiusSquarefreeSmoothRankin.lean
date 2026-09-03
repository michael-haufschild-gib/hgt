import GaloisForLFunctions.RHTower.PrimeRpowUniformUpper
import GaloisForLFunctions.RHTower.Sieve.SmoothSum
import GaloisForLFunctions.RHTower.Sieve.DivisorMomentMeanSquare
import GaloisForLFunctions.RHTower.Sieve.EulerExpansion
import GaloisForLFunctions.RHTower.Sieve.RankinTruncation

namespace RHTower.Sieve

open Finset Nat

noncomputable section

/-- Squarefree integers up to `Y` supported on primes at most `z`. -/
def squarefreeSmoothUpTo (z Y : ℕ) : Finset ℕ :=
  (smoothUpTo (Nat.primesLE z) Y).filter Squarefree

theorem mem_squarefreeSmoothUpTo {z Y n : ℕ} :
    n ∈ squarefreeSmoothUpTo z Y ↔
      ((1 ≤ n ∧ n ≤ Y) ∧ n.primeFactors ⊆ Nat.primesLE z) ∧ Squarefree n := by
  rw [squarefreeSmoothUpTo, Finset.mem_filter, mem_smoothUpTo]

/-- Exact squarefree smooth weighted sum is bounded by its full Euler product. -/
theorem sum_squarefreeSmoothUpTo_rpow_le_prod (z Y : ℕ) (b : ℝ) :
    ∑ n ∈ squarefreeSmoothUpTo z Y, (n : ℝ) ^ b ≤
      ∏ p ∈ Nat.primesLE z, (1 + (p : ℝ) ^ b) := by
  classical
  let F : ℕ → Finset ℕ := fun n => n.primeFactors
  let w : Finset ℕ → ℝ := fun T => ∏ p ∈ T, (p : ℝ) ^ b
  have hsub : (squarefreeSmoothUpTo z Y).image F ⊆ (Nat.primesLE z).powerset := by
    intro T hT
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hT
    rw [Finset.mem_powerset]
    exact (mem_squarefreeSmoothUpTo.1 hn).1.2
  have hinj : ∀ n ∈ squarefreeSmoothUpTo z Y, ∀ m ∈ squarefreeSmoothUpTo z Y,
      F n = F m → n = m := by
    intro n hn m hm hnm
    have hnSq := (mem_squarefreeSmoothUpTo.1 hn).2
    have hmSq := (mem_squarefreeSmoothUpTo.1 hm).2
    have hnprod := Nat.prod_primeFactors_of_squarefree hnSq
    have hmprod := Nat.prod_primeFactors_of_squarefree hmSq
    dsimp [F] at hnm
    rw [hnm] at hnprod
    exact hnprod.symm.trans hmprod
  have hrewrite : ∑ n ∈ squarefreeSmoothUpTo z Y, (n : ℝ) ^ b =
      ∑ T ∈ (squarefreeSmoothUpTo z Y).image F, w T := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun n hn => by
      dsimp [F, w]
      exact natCast_rpow_eq_prod_primeFactors (mem_squarefreeSmoothUpTo.1 hn).2 b
  have hnonneg : ∀ T ∈ (Nat.primesLE z).powerset, 0 ≤ w T := by
    intro T _
    dsimp [w]
    positivity
  calc
    ∑ n ∈ squarefreeSmoothUpTo z Y, (n : ℝ) ^ b
      = ∑ T ∈ (squarefreeSmoothUpTo z Y).image F, w T := hrewrite
    _ ≤ ∑ T ∈ (Nat.primesLE z).powerset, w T :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun T hT _ => hnonneg T hT
    _ = ∏ p ∈ Nat.primesLE z, ((p : ℝ) ^ b + 1) := by
      rw [prod_one_add_eq_sum_powerset_real]
    _ = ∏ p ∈ Nat.primesLE z, (1 + (p : ℝ) ^ b) := by
      exact Finset.prod_congr rfl fun p _ => by ring

/-- Rankin's bound for the squarefree smooth count. -/
theorem card_squarefreeSmoothUpTo_le_rankin {a : ℝ} (ha1 : a ≤ 1)
    (z : ℕ) {Y : ℕ} (hY : 1 ≤ Y) :
    ((squarefreeSmoothUpTo z Y).card : ℝ) ≤
      (Y : ℝ) ^ (1 - a) * ∏ p ∈ Nat.primesLE z, (1 + (p : ℝ) ^ (a - 1)) := by
  have hYR : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hY0 : (0 : ℝ) < (Y : ℝ) := lt_of_lt_of_le zero_lt_one hYR
  have hpoint : ∀ n ∈ squarefreeSmoothUpTo z Y,
      (1 : ℝ) ≤ (Y : ℝ) ^ (1 - a) * (n : ℝ) ^ (a - 1) := by
    intro n hn
    have hnData := mem_squarefreeSmoothUpTo.1 hn
    have hn1 : 1 ≤ n := hnData.1.1.1
    have hnY : n ≤ Y := hnData.1.1.2
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hnYR : (n : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hnY
    have hneg : a - 1 ≤ 0 := by linarith
    have hpow : (Y : ℝ) ^ (a - 1) ≤ (n : ℝ) ^ (a - 1) :=
      Real.rpow_le_rpow_of_nonpos hn0 hnYR hneg
    have hfac0 : 0 ≤ (Y : ℝ) ^ (1 - a) := Real.rpow_nonneg hY0.le _
    calc
      (1 : ℝ) = (Y : ℝ) ^ (1 - a) * (Y : ℝ) ^ (a - 1) := by
        rw [← Real.rpow_add hY0]
        norm_num
      _ ≤ (Y : ℝ) ^ (1 - a) * (n : ℝ) ^ (a - 1) :=
        mul_le_mul_of_nonneg_left hpow hfac0
  have hsum : ((squarefreeSmoothUpTo z Y).card : ℝ) ≤
      ∑ n ∈ squarefreeSmoothUpTo z Y,
        ((Y : ℝ) ^ (1 - a) * (n : ℝ) ^ (a - 1)) := by
    have hcard : ((squarefreeSmoothUpTo z Y).card : ℝ) =
        ∑ _n ∈ squarefreeSmoothUpTo z Y, (1 : ℝ) := by simp
    rw [hcard]
    exact Finset.sum_le_sum fun n hn => hpoint n hn
  calc
    ((squarefreeSmoothUpTo z Y).card : ℝ)
      ≤ ∑ n ∈ squarefreeSmoothUpTo z Y,
          ((Y : ℝ) ^ (1 - a) * (n : ℝ) ^ (a - 1)) := hsum
    _ = (Y : ℝ) ^ (1 - a) *
        ∑ n ∈ squarefreeSmoothUpTo z Y, (n : ℝ) ^ (a - 1) := by rw [Finset.mul_sum]
    _ ≤ (Y : ℝ) ^ (1 - a) *
        ∏ p ∈ Nat.primesLE z, (1 + (p : ℝ) ^ (a - 1)) := by
      exact mul_le_mul_of_nonneg_left
        (sum_squarefreeSmoothUpTo_rpow_le_prod z Y (a - 1))
        (Real.rpow_nonneg hY0.le _)

/-- Explicit uniform Rankin--Euler bound for squarefree smooth integers. -/
theorem card_squarefreeSmoothUpTo_le_uniform {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (z : ℕ) {Y : ℕ} (hY : 1 ≤ Y) :
    ((squarefreeSmoothUpTo z Y).card : ℝ) ≤
      (Y : ℝ) ^ (1 - a) *
        Real.exp (Real.exp 1 * mertensS z + RHTower.uniformPrimeLogRpowConst * (z : ℝ) ^ a) := by
  have hY0 : (0 : ℝ) ≤ (Y : ℝ) ^ (1 - a) := Real.rpow_nonneg (Nat.cast_nonneg Y) _
  exact (card_squarefreeSmoothUpTo_le_rankin ha1 z hY).trans
    (mul_le_mul_of_nonneg_left
      (RHTower.prod_primesLE_one_add_rpow_sub_one_le_uniform ha0 ha1 z) hY0)

end

end RHTower.Sieve

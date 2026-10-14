import GaloisForLFunctions.HTGeometry.RpowHarmonicTailAsymptotic
import Mathlib.NumberTheory.EulerProduct.Basic

/-! # A sharp elementary bound for finite positive Euler products -/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

theorem tsum_nat_rpow_neg_le_one_add_inv {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ, (n : ℝ) ^ (-σ) ≤ 1 + (σ - 1)⁻¹ := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have htail := tsum_shift_rpow_le (q := 1 - σ) (by linarith) (N := 1) (by rfl)
  rw [show 1 - σ - 1 = -σ by ring, show -(1 - σ) = σ - 1 by ring] at htail
  have hhead : ∑ n ∈ Finset.range 2, (n : ℝ) ^ (-σ) = 1 := by
    simp [Finset.sum_range_succ, Real.zero_rpow (by linarith : -σ ≠ 0)]
  rw [← hs.sum_add_tsum_nat_add 2, hhead]
  refine add_le_add le_rfl ?_
  simp only [Nat.cast_one, Real.one_rpow, one_div] at htail
  have heq : (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-σ)) =
      ∑' n : ℕ, (1 + 1 + (n : ℝ)) ^ (-σ) := by
    apply tsum_congr
    intro n
    congr 1
    push_cast
    ring
  rw [heq]
  exact htail

theorem finite_prime_eulerProduct_le_one_add_inv {σ : ℝ} (hσ : 1 < σ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    ∏ p ∈ P, (1 - (p : ℝ) ^ (-σ))⁻¹ ≤ 1 + (σ - 1)⁻¹ := by
  classical
  let f : ℕ →* ℝ :=
    { toFun := fun n => (n : ℝ) ^ (-σ)
      map_one' := by simp
      map_mul' := fun m n => by
        rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)] }
  have hp : ∀ {p : ℕ}, Nat.Prime p → ‖f p‖ < 1 := by
    intro p hp
    change ‖(p : ℝ) ^ (-σ)‖ < 1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  obtain ⟨_, hsum⟩ :=
    EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric hp P
  have hfilter : P.filter Nat.Prime = P := Finset.filter_eq_self.mpr hP
  rw [hfilter] at hsum
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  calc
    _ = ∑' n : Nat.factoredNumbers P, f n := hsum.tsum_eq.symm
    _ ≤ ∑' n : ℕ, f n :=
      hs.tsum_subtype_le (fun n : ℕ => (n : ℝ) ^ (-σ)) (Nat.factoredNumbers P)
        (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ ≤ _ := tsum_nat_rpow_neg_le_one_add_inv hσ

end GaloisForLFunctions.HTGeometry

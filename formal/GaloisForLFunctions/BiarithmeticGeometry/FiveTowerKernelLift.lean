import GaloisForLFunctions.ArithmeticOrientationTheory.LocalFactorsAreTheUnitsOfTheWienerMonoid

/-!
# Arbitrary kernels on the prime-five tower

Extending a coefficient sequence by zero off powers of five preserves its exact
critical Wiener norm. At every integer horizon, its cofactor action is a finite
sum over precisely the powers visible below that horizon.
-/

noncomputable section
open Finset
open GaloisForLFunctions.ArithmeticOrientationTheory
open GaloisForLFunctions.TransHorizonIncidenceMechanics
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Lift arbitrary real coefficients to powers of five, with zero elsewhere. -/
def fiveTowerKernelLift (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  if 5 ^ Nat.log 5 n = n then f (Nat.log 5 n) else 0

theorem fiveTowerKernelLift_pow (f : ℕ → ℝ) (r : ℕ) :
    fiveTowerKernelLift f (5 ^ r) = f r := by
  simp [fiveTowerKernelLift, Nat.log_pow (by omega : 1 < 5)]

theorem fiveTowerKernelLift_zero (f : ℕ → ℝ) : fiveTowerKernelLift f 0 = 0 := by
  simp [fiveTowerKernelLift]

theorem fiveTowerKernelLift_off_support (f : ℕ → ℝ) (n : ℕ)
    (hn : n ∉ Set.range (fun r : ℕ => 5 ^ r)) : fiveTowerKernelLift f n = 0 := by
  have hnot : 5 ^ Nat.log 5 n ≠ n := fun h => hn ⟨Nat.log 5 n, h⟩
  simp only [fiveTowerKernelLift, hnot, if_false]

/-- Reading and lifting a tower-supported row recovers the entire row. -/
theorem fiveTowerKernelLift_read_of_support (v : ℕ → ℝ)
    (hv : ∀ n, n ∉ Set.range (fun r : ℕ => 5 ^ r) → v n = 0) :
    fiveTowerKernelLift (fun r => v (5 ^ r)) = v := by
  funext n
  by_cases hn : 5 ^ Nat.log 5 n = n
  · simp only [fiveTowerKernelLift, hn, if_true]
  · have hnot : n ∉ Set.range (fun r : ℕ => 5 ^ r) := by
      rintro ⟨r, rfl⟩
      exact hn (by rw [Nat.log_pow (by omega : 1 < 5)])
    rw [fiveTowerKernelLift_off_support _ _ hnot, hv n hnot]

private theorem fiveTower_critical_weight (r : ℕ) :
    ((5 ^ r : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt 5 ^ r)⁻¹ := by
  have h := abs_localFactorInverse_mul_rpow (by norm_num : Nat.Prime 5) (1 : ℝ) r
  simp only [localFactorInverse_pow (by omega : 1 < 5), one_pow, abs_one, one_mul,
    Nat.cast_ofNat] at h
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 5), ← Real.sqrt_eq_rpow, inv_pow] at h
  exact h

/-- The critical Wiener condition is exactly the normalized coefficient `ell1` condition. -/
theorem criticalWiener_fiveTowerKernelLift_iff (f : ℕ → ℝ) :
    CriticalWiener (fiveTowerKernelLift f) ↔
      Summable (fun r : ℕ => |f r| / Real.sqrt 5 ^ r) := by
  unfold CriticalWiener
  rw [← (Nat.pow_right_injective (by omega : 2 ≤ 5)).summable_iff
    (fun n hn => by rw [fiveTowerKernelLift_off_support f n hn, abs_zero, zero_mul])]
  have he : ((fun n : ℕ => |fiveTowerKernelLift f n| * (n : ℝ) ^ (-(1 / 2 : ℝ))) ∘
      (fun r : ℕ => 5 ^ r)) = fun r : ℕ => |f r| / Real.sqrt 5 ^ r := by
    funext r
    rw [Function.comp_apply, fiveTowerKernelLift_pow, fiveTower_critical_weight, div_eq_mul_inv]
  rw [he]

/-- Prime-five support reduces the entire ordinary cofactor packet to its visible powers. -/
theorem fiveTowerKernelLift_cofactor_sum (f v : ℕ → ℝ) (hv0 : v 0 = 0) (n : ℕ) :
    (∑ j ∈ Icc 1 n, fiveTowerKernelLift f j * v (n / j)) =
      ∑ r ∈ range (Nat.log 5 n + 1), f r * v (n / 5 ^ r) := by
  by_cases hn : n = 0
  · subst n
    simp [hv0]
  · let S := (range (Nat.log 5 n + 1)).image (fun r : ℕ => 5 ^ r)
    have hS : S ⊆ Icc 1 n := by
      intro j hj
      obtain ⟨r, hr, rfl⟩ := mem_image.mp hj
      exact mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega)),
        Nat.pow_le_of_le_log hn (by have := mem_range.mp hr; omega)⟩
    have hsum : (∑ j ∈ Icc 1 n, fiveTowerKernelLift f j * v (n / j)) =
        ∑ j ∈ S, fiveTowerKernelLift f j * v (n / j) := by
      symm
      apply sum_subset hS
      intro j hj hjS
      by_cases hpow : 5 ^ Nat.log 5 j = j
      · have hr : Nat.log 5 j ∈ range (Nat.log 5 n + 1) :=
          mem_range.mpr (Nat.lt_succ_of_le
            (Nat.le_log_of_pow_le (by omega : 1 < 5) (hpow.trans_le (mem_Icc.mp hj).2)))
        exact False.elim (hjS (mem_image.mpr ⟨Nat.log 5 j, hr, hpow⟩))
      · simp only [fiveTowerKernelLift, hpow, if_false, zero_mul]
    rw [hsum]
    dsimp only [S]
    rw [sum_image (fun r _ s _ h => Nat.pow_right_injective (by omega : 2 ≤ 5) h)]
    apply sum_congr rfl
    intro r _
    rw [fiveTowerKernelLift_pow]

end GaloisForLFunctions.BiarithmeticGeometry

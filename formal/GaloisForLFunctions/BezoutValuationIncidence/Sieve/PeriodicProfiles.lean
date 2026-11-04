import GaloisForLFunctions.BezoutValuationIncidence.Sieve.ResidueCovariance
import Mathlib.Data.Nat.Periodic

/-!
# Exact affine samples of periodic profiles

Both offset signs depend only on the receiving residue. Negative offsets
use a lifted residue to preserve genuine natural-number subtraction.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.BezoutValuationIncidence
open Finset

theorem periodic_eq_of_modEq {α : Type*} {G : ℕ → α} {M n r : ℕ}
    (hG : Function.Periodic G M) (hnr : n ≡ r [MOD M]) : G n = G r := by
  rw [← hG.map_mod_nat n, ← hG.map_mod_nat r, hnr]

/-- Positive affine samples of a periodic profile depend only on the receiving residue. -/
theorem periodic_positive_sample {G : ℕ → ℝ} {M : ℕ}
    (hG : Function.Periodic G M) (k h n : ℕ) :
    G (k * n + h) = G (k * (n % M) + h) := by
  apply periodic_eq_of_modEq hG
  change (k * n + h) % M = (k * (n % M) + h) % M
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

/-- Lift the receiving residue far enough before subtracting the negative offset. -/
def negativePeriodicProfile (G : ℕ → ℝ) (M k h r : ℕ) : ℝ :=
  G (k * (r + M * h) - h)

theorem periodic_negative_sample {G : ℕ → ℝ} {M k h n : ℕ}
    (hM : 0 < M) (hG : Function.Periodic G M) (hk : 1 ≤ k) (hn : h ≤ k * n) :
    G (k * n - h) = negativePeriodicProfile G M k h (n % M) := by
  have href : h ≤ k * (n % M + M * h) := by
    have h1 : h ≤ M * h := by
      simpa only [one_mul] using Nat.mul_le_mul_right h (show 1 ≤ M from hM)
    have h2 : n % M + M * h ≤ k * (n % M + M * h) := by
      simpa only [one_mul] using Nat.mul_le_mul_right (n % M + M * h) hk
    exact (h1.trans (Nat.le_add_left _ _)).trans h2
  have hmod : n ≡ n % M + M * h [MOD M] := by
    change n % M = (n % M + M * h) % M
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.mod_self, zero_mul, Nat.zero_mod, add_zero]
  exact periodic_eq_of_modEq hG (Nat.ModEq.sub hn href (hmod.mul_left k) (.refl h))

/-- One finite period bounds every value of a periodic profile. -/
theorem periodic_profile_bound {G : ℕ → ℝ} {M : ℕ}
    (hM : 0 < M) (hG : Function.Periodic G M) (n : ℕ) :
    |G n| ≤ ∑ r ∈ range M, |G r| := by
  rw [← hG.map_mod_nat n]
  exact single_le_sum (fun r _ => abs_nonneg (G r)) (mem_range.mpr (Nat.mod_lt n hM))

/-- Products of affine residue profiles retain a uniform finite-period mass. -/
theorem periodic_product_mass {M : ℕ} {G H : ℕ → ℝ} {U V : ℝ}
    (hU : 0 ≤ U) (hG : ∀ n, |G n| ≤ U) (hH : ∀ n, |H n| ≤ V)
    (a b : ℕ → ℕ) :
    (∑ r ∈ range M, |G (a r) * H (b r)|) ≤ (M : ℝ) * U * V := by
  calc
    _ ≤ ∑ r ∈ range M, U * V := by
      apply sum_le_sum
      intro r _
      rw [abs_mul]
      exact mul_le_mul (hG _) (hH _) (abs_nonneg _) hU
    _ = _ := by rw [sum_const, card_range, nsmul_eq_mul, mul_assoc]

#print axioms periodic_positive_sample
#print axioms periodic_negative_sample
#print axioms periodic_product_mass

end GaloisForLFunctions.BezoutValuationIncidence

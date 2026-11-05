import GaloisForLFunctions.ZeroConfigurationGeometry.IsolatingWindowsVarySlowlyAtTheirTarget
import GaloisForLFunctions.RHTower.GammaDampedVerticalBound

/-!
# A numerical lattice rate for the zero camera

Pairing integer indices bounds the Lorentzian lattice sum by five.
The relative camera rate is therefore dominated by a finite expression.
-/

open Complex MeasureTheory Set
open scoped Real
open RHTower

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry


private theorem summable_lattice_positive :
    Summable (fun n : ℕ => (1 + ((n : ℝ) + 1) ^ 2)⁻¹) := by
  have h : Summable (fun n : ℕ => (1 + (((n : ℤ) + 1 : ℤ) : ℝ) ^ 2)⁻¹) :=
    summable_inv_one_add_sq_int.comp_injective
      (i := fun n : ℕ => (n : ℤ) + 1)
      (fun a b h => Nat.cast_injective (add_right_cancel h))
  simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using h

private theorem tsum_lattice_positive_le_two :
    (∑' n : ℕ, (1 + ((n : ℝ) + 1) ^ 2)⁻¹) ≤ 2 := by
  have hs : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr summable_inv_natCast_sq
  have he := summable_inv_natCast_sq.tsum_eq_zero_add
  norm_num only [Nat.cast_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), inv_zero,
    zero_add, Nat.cast_add, Nat.cast_one] at he
  have hbound (n : ℕ) : (1 + ((n : ℝ) + 1) ^ 2)⁻¹ ≤ (((n : ℝ) + 1) ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (by linarith only [])
  calc
    _ ≤ ∑' n : ℕ, (((n : ℝ) + 1) ^ 2)⁻¹ :=
      summable_lattice_positive.tsum_le_tsum hbound hs
    _ = ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ := he.symm
    _ ≤ 2 := tsum_inv_natCast_sq_le

/-- A numerical bound for the lattice sum in the relative camera rate. -/
theorem latticeSumConst_le_five : latticeSumConst ≤ 5 := by
  have hp : Summable (fun n : ℕ => (1 + (((n : ℤ) + 1 : ℤ) : ℝ) ^ 2)⁻¹) := by
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using summable_lattice_positive
  have hn : Summable (fun n : ℕ => (1 + ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2)⁻¹) := by
    simpa only [Int.cast_neg, neg_sq] using hp
  have he := tsum_of_add_one_of_neg_add_one
    (f := fun k : ℤ => (1 + (k : ℝ) ^ 2)⁻¹) hp hn
  simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, Int.cast_neg, neg_sq,
    Int.cast_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, inv_one] at he
  unfold latticeSumConst
  rw [he]
  linarith only [tsum_lattice_positive_le_two]

/-- A finite expression dominating the relative camera rate constant. -/
def cameraSlowConstant (lam ℓ M' : ℝ) : ℝ :=
  Real.pi * lam + 2 + 320 * slackBound ℓ * lam ^ 2 *
    (1 + slackBound ℓ * (2 * Real.pi) ^ M' + slackBound ℓ * lam)

theorem slowConst_le_cameraSlowConstant {lam ℓ M' : ℝ}
    (hlam : 0 < lam) (hℓ : 0 ≤ ℓ) :
    slowConst lam ℓ M' ≤ cameraSlowConstant lam ℓ M' := by
  have hs : 0 ≤ slackBound ℓ := by unfold slackBound; linarith only [hℓ]
  have hbr : 0 ≤ 1 + slackBound ℓ * (2 * Real.pi) ^ M' + slackBound ℓ * lam := by positivity
  have hmul := mul_le_mul_of_nonneg_left latticeSumConst_le_five
    (show 0 ≤ 64 * slackBound ℓ * lam ^ 2 by positivity)
  have h := mul_le_mul_of_nonneg_right hmul hbr
  unfold slowConst cameraSlowConstant
  nlinarith only [h]

end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.latticeSumConst_le_five
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.slowConst_le_cameraSlowConstant

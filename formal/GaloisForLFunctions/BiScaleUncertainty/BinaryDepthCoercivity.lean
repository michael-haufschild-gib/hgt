import GaloisForLFunctions.BiScaleUncertainty.FiniteHorizonPositiveCoercivity

/-!
# Depth weights for binary-parent coercivity

Geometric Cauchy--Schwarz weights and explicit descendant counts give a
depth-by-depth charging bound. The clipped-window anchor estimate
retains the stated constant eight, including incomplete last generations.
-/

noncomputable section
open Finset
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
set_option autoImplicit false

/-- Exact reciprocal-weight budget along a path of any finite length. -/
theorem binary_path_geometric_sum (m : ℕ) :
    (∑ k ∈ range m, (3 / 4 : ℝ) ^ (k + 1)) = 3 * (1 - (3 / 4 : ℝ) ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

/-- The literal geometric weighted Cauchy--Schwarz inequality and its constant four. -/
theorem binary_path_geometric_cauchy (m : ℕ) (Δ : ℕ → ℝ) :
    (∑ k ∈ range m, Δ k) ^ 2 ≤
        (∑ k ∈ range m, (3 / 4 : ℝ) ^ (k + 1)) *
          (∑ k ∈ range m, (4 / 3 : ℝ) ^ (k + 1) * (Δ k) ^ 2) ∧
      (∑ k ∈ range m, (3 / 4 : ℝ) ^ (k + 1)) *
          (∑ k ∈ range m, (4 / 3 : ℝ) ^ (k + 1) * (Δ k) ^ 2) ≤
        4 * ∑ k ∈ range m, (4 / 3 : ℝ) ^ (k + 1) * (Δ k) ^ 2 := by
  constructor
  · apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (range m)
      (r := Δ) (f := fun k => (3 / 4 : ℝ) ^ (k + 1))
      (g := fun k => (4 / 3 : ℝ) ^ (k + 1) * (Δ k) ^ 2)
      (fun _ _ => by positivity) (fun _ _ => by positivity)
    intro k _
    rw [← mul_assoc, ← mul_pow]
    norm_num
  · apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [binary_path_geometric_sum]
    have hp : 0 ≤ (3 / 4 : ℝ) ^ m := by positivity
    linarith only [hp]

/-- An edge at its actual binary depth has at most twice the window divided by that level size. -/
theorem binary_descendant_depth_bound (N k : ℕ) (hk : 2 ≤ k) (hkN : k ≤ N) :
    (((Icc 1 N).filter (fun n => k ∈ binaryAncestors n)).card : ℝ) ≤
      2 * (N : ℝ) / (2 : ℝ) ^ Nat.log 2 k := by
  have hlevel : (2 : ℝ) ^ Nat.log 2 k ≤ (k : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (show k ≠ 0 by omega)
  have hcard : (k : ℝ) * (((Icc 1 N).filter (fun n => k ∈ binaryAncestors n)).card : ℝ) ≤
      2 * (N : ℝ) := by exact_mod_cast binary_descendant_card_bound N k hk hkN
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ Nat.log 2 k)).mpr
  have hm := mul_le_mul_of_nonneg_right hlevel
    (Nat.cast_nonneg ((Icc 1 N).filter (fun n => k ∈ binaryAncestors n)).card)
  simpa only [mul_comm] using hm.trans hcard

/-- Summing path charges retains the precise exponentially decreasing depth factor. -/
theorem binary_descendant_depth_charge (N k : ℕ) (hk : 2 ≤ k) (hkN : k ≤ N) :
    4 * (4 / 3 : ℝ) ^ Nat.log 2 k *
        (((Icc 1 N).filter (fun n => k ∈ binaryAncestors n)).card : ℝ) ≤
      8 * (N : ℝ) * (2 / 3 : ℝ) ^ Nat.log 2 k := by
  have hb := mul_le_mul_of_nonneg_left (binary_descendant_depth_bound N k hk hkN)
    (by positivity : (0 : ℝ) ≤ 4 * (4 / 3 : ℝ) ^ Nat.log 2 k)
  calc
    _ ≤ 4 * (4 / 3 : ℝ) ^ Nat.log 2 k * (2 * (N : ℝ) / (2 : ℝ) ^ Nat.log 2 k) := hb
    _ = 8 * (N : ℝ) * ((4 / 3 : ℝ) ^ Nat.log 2 k / (2 : ℝ) ^ Nat.log 2 k) := by ring
    _ = _ := by rw [← div_pow]; norm_num

/-- Each depth charge is at most eight times the window size. -/
theorem binary_descendant_depth_charge_le (N k : ℕ) :
    8 * (N : ℝ) * (2 / 3 : ℝ) ^ Nat.log 2 k ≤ 8 * (N : ℝ) := by
  apply mul_le_of_le_one_right (by positivity)
  simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2 / 3)
    (by norm_num : (2 / 3 : ℝ) ≤ 1) (Nat.log 2 k)

/-- The stated tree constant follows on every clipped window, with no height restriction. -/
theorem binary_parent_window_bound_eight (N : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, (f n - f 1) ^ 2) ≤
      8 * (N : ℝ) * (∑ k ∈ Icc 2 N, (f k - f (k / 2)) ^ 2) := by
  apply (binary_parent_window_bound N f).trans
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg (fun _ _ => sq_nonneg _))
  have hN := Nat.cast_nonneg (α := ℝ) N
  linarith only [hN]

end GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon

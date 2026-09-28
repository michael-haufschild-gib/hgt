import GaloisForLFunctions.RHTower.AutocorrelationChainDamping
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The complete finite-chain sine certificate

The scalar two- and three-vertex bounds extend to every chain length. Positive
sine weights make the weighted Young inequalities telescope exactly. The
result bounds the modulus of the complete complex Hilbert-space pairing sum.
-/

open scoped BigOperators InnerProduct
noncomputable section
namespace RHTower

def autocorrelationSineWeight (n k : ℕ) : ℝ :=
  Real.sin ((k : ℝ) * (Real.pi / ((n : ℝ) + 1)))

theorem autocorrelationSineWeight_zero (n : ℕ) :
    autocorrelationSineWeight n 0 = 0 := by simp [autocorrelationSineWeight]

theorem autocorrelationSineWeight_end (n : ℕ) :
    autocorrelationSineWeight n (n + 1) = 0 := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have he : ((n + 1 : ℕ) : ℝ) * (Real.pi / ((n : ℝ) + 1)) = Real.pi := by
    push_cast
    field_simp
  rw [autocorrelationSineWeight, he, Real.sin_pi]

theorem autocorrelationSineWeight_pos {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    0 < autocorrelationSineWeight n k := by
  have hd : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · rw [← mul_div_assoc, div_lt_iff₀ hd]
    nlinarith [Real.pi_pos]

theorem autocorrelationSineWeight_recurrence (n : ℕ) {k : ℕ} (hk : 0 < k) :
    autocorrelationSineWeight n (k - 1) + autocorrelationSineWeight n (k + 1) =
      2 * Real.cos (Real.pi / ((n : ℝ) + 1)) * autocorrelationSineWeight n k := by
  have hkm : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_of_lt hk), Nat.cast_one]
  unfold autocorrelationSineWeight
  rw [hkm, Nat.cast_add, Nat.cast_one]
  rw [sub_mul, add_mul, one_mul]
  exact sin_sub_add_sin_add _ _

private theorem chain_edge_young (n : ℕ) (x : ℕ → ℝ)
    (hzero : x 0 = 0) (hend : x (n + 1) = 0) {k : ℕ} (hk : k ≤ n) :
    2 * x k * x (k + 1) ≤
      autocorrelationSineWeight n (k + 1) / autocorrelationSineWeight n k * x k ^ 2 +
      autocorrelationSineWeight n k / autocorrelationSineWeight n (k + 1) * x (k + 1) ^ 2 := by
  by_cases hk0 : k = 0
  · subst k
    simp [hzero, autocorrelationSineWeight_zero]
  · by_cases hkn : k = n
    · subst k
      simp [hend, autocorrelationSineWeight_end]
    · have hp := autocorrelationSineWeight_pos (Nat.pos_of_ne_zero hk0) hk
      have hnext := autocorrelationSineWeight_pos (Nat.succ_pos k)
        (Nat.succ_le_of_lt (lt_of_le_of_ne hk hkn))
      simpa only [inv_div] using
        (two_mul_le_weighted (x := x k) (y := x (k + 1)) (div_pos hnext hp))

/-- Sharp sine-weighted path bound for every finite chain, with zero boundary values. -/
theorem autocorrelation_chain_sine_bound (n : ℕ) (x : ℕ → ℝ)
    (hzero : x 0 = 0) (hend : x (n + 1) = 0) :
    (∑ k ∈ Finset.range (n + 1), x k * x (k + 1)) ≤
      Real.cos (Real.pi / ((n : ℝ) + 1)) * (∑ k ∈ Finset.range (n + 1), x k ^ 2) := by
  let w := autocorrelationSineWeight n
  let G : ℕ → ℝ := fun k => w (k - 1) / w k * x k ^ 2
  have hG0 : G 0 = 0 := by simp [G, hzero]
  have hGe : G (n + 1) = 0 := by simp [G, hend]
  have hshift : (∑ k ∈ Finset.range (n + 1), G (k + 1)) =
      ∑ k ∈ Finset.range (n + 1), G k := by
    have h1 := Finset.sum_range_succ' G (n + 1)
    have h2 := Finset.sum_range_succ G (n + 1)
    rw [hG0, add_zero] at h1
    rw [hGe, add_zero] at h2
    exact h1.symm.trans h2
  have hcoeff {k : ℕ} (hk : k ∈ Finset.range (n + 1)) :
      w (k + 1) / w k * x k ^ 2 + G k =
        (2 * Real.cos (Real.pi / ((n : ℝ) + 1))) * x k ^ 2 := by
    by_cases hk0 : k = 0
    · subst k; simp [G, hzero]
    · have hkpos := Nat.pos_of_ne_zero hk0
      have hw : w k ≠ 0 := ne_of_gt (autocorrelationSineWeight_pos hkpos
        (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
      dsimp only [G]
      rw [← add_mul, ← add_div, add_comm (w (k + 1)),
        autocorrelationSineWeight_recurrence n hkpos, mul_div_cancel_right₀ _ hw]
  have hsum : (2 : ℝ) * (∑ k ∈ Finset.range (n + 1), x k * x (k + 1)) ≤
      (2 * Real.cos (Real.pi / ((n : ℝ) + 1))) *
        (∑ k ∈ Finset.range (n + 1), x k ^ 2) := by
    calc
      _ = ∑ k ∈ Finset.range (n + 1), 2 * x k * x (k + 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _; ring
      _ ≤ ∑ k ∈ Finset.range (n + 1),
          (w (k + 1) / w k * x k ^ 2 + G (k + 1)) := by
        apply Finset.sum_le_sum
        intro k hk
        simpa only [G, Nat.add_sub_cancel] using chain_edge_young n x hzero hend
          (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
      _ = ∑ k ∈ Finset.range (n + 1), (w (k + 1) / w k * x k ^ 2 + G k) := by
        rw [Finset.sum_add_distrib, hshift, ← Finset.sum_add_distrib]
      _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k hk => hcoeff hk
  linarith only [hsum]

/-- All complex phases and every adjacent cross term remain in the Hilbert chain. -/
theorem norm_autocorrelation_chain_inner_sum_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (n : ℕ) (v : ℕ → E) (hzero : v 0 = 0) (hend : v (n + 1) = 0) :
    ‖∑ k ∈ Finset.range (n + 1), inner ℂ (v k) (v (k + 1))‖ ≤
      Real.cos (Real.pi / ((n : ℝ) + 1)) *
        (∑ k ∈ Finset.range (n + 1), ‖v k‖ ^ 2) := by
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1), ‖inner ℂ (v k) (v (k + 1))‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), ‖v k‖ * ‖v (k + 1)‖ :=
      Finset.sum_le_sum fun k _ => norm_inner_le_norm (𝕜 := ℂ) _ _
    _ ≤ _ := autocorrelation_chain_sine_bound n (fun k => ‖v k‖)
      (by rw [hzero, norm_zero]) (by rw [hend, norm_zero])

end RHTower

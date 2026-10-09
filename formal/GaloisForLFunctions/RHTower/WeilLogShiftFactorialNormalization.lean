import GaloisForLFunctions.RHTower.WeilLogShiftFactorialMajorant

/-!
# Factorial majorants and summable normalizations

An eventual finite factorial majorant yields summability after one extra
unit of exponential damping. Conversely, summability already forces such
a majorant. Summability also upgrades the eventual envelope to a global one.
-/

noncomputable section

open Filter Topology Real

namespace RHTower

/-- One extra unit of exponential damping turns a factorial envelope into
a geometric bound for the absolute normalized term. -/
theorem weilLogShift_factorial_normalization_abs_le (f : ℕ → ℝ) (m : ℕ)
    (A D : ℝ) (n : ℕ)
    (h : |f n| ≤ D * exp (A * n) * (n.factorial : ℝ) ^ m) :
    |exp (-((A + 1) * n)) * f n / (n.factorial : ℝ) ^ m| ≤ D * exp (-n) := by
  have hF : 0 < (n.factorial : ℝ) ^ m := pow_pos (by exact_mod_cast Nat.factorial_pos n) _
  rw [abs_div, abs_mul, abs_of_pos (exp_pos _), abs_of_pos hF]
  apply (div_le_iff₀ hF).mpr
  have he : exp (-((A + 1) * n)) * exp (A * n) = exp (-n) := by
    rw [← exp_add]
    congr 1
    ring
  calc
    _ ≤ exp (-((A + 1) * n)) * (D * exp (A * n) * (n.factorial : ℝ) ^ m) :=
      mul_le_mul_of_nonneg_left h (exp_pos _).le
    _ = D * (exp (-((A + 1) * n)) * exp (A * n)) * (n.factorial : ℝ) ^ m := by ring
    _ = _ := by rw [he]

/-- Existence of a finite factorial majorant is exactly existence of a
summable factorial normalization with strictly positive exponential rate. -/
theorem weilLogShiftHasFactorialMajorant_iff_exists_summable_normalization (f : ℕ → ℝ) :
    WeilLogShiftHasFactorialMajorant f ↔ ∃ (m : ℕ) (B : ℝ), 0 < B ∧
      Summable (fun n : ℕ => exp (-(B * n)) * f n / (n.factorial : ℝ) ^ m) := by
  constructor
  · rintro ⟨m, A, D, N, hf⟩
    refine ⟨m, max A 0 + 1, by have := le_max_right A 0; linarith, ?_⟩
    apply (summable_exp_neg_nat.mul_left |D|).of_norm_bounded_eventually_nat
    refine eventually_atTop.mpr ⟨N, ?_⟩
    intro n hn
    have hF : 0 ≤ (n.factorial : ℝ) ^ m := by positivity
    have hrate : exp (A * n) ≤ exp (max A 0 * n) :=
      exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left A 0)
        (Nat.cast_nonneg (α := ℝ) n))
    have hbound : |f n| ≤ |D| * exp (max A 0 * n) * (n.factorial : ℝ) ^ m := by
      calc
        _ ≤ D * exp (A * n) * (n.factorial : ℝ) ^ m := hf n hn
        _ ≤ |D| * exp (A * n) * (n.factorial : ℝ) ^ m :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_abs_self D) (exp_pos _).le) hF
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrate (abs_nonneg D)) hF
    simpa only [Real.norm_eq_abs] using
      weilLogShift_factorial_normalization_abs_le f m (max A 0) |D| n hbound
  · rintro ⟨m, B, _, hs⟩
    exact weilLogShiftHasFactorialMajorant_of_summable_normalization f m B hs

/-- A finite factorial majorant can always be chosen with positive rate,
nonnegative prefactor, and no discarded initial segment. -/
theorem weilLogShiftHasFactorialMajorant_global_bound (f : ℕ → ℝ)
    (hf : WeilLogShiftHasFactorialMajorant f) :
    ∃ (m : ℕ) (A D : ℝ), 0 < A ∧ 0 ≤ D ∧ ∀ n : ℕ,
      |f n| ≤ D * exp (A * n) * (n.factorial : ℝ) ^ m := by
  obtain ⟨m, A, hA, hs⟩ :=
    (weilLogShiftHasFactorialMajorant_iff_exists_summable_normalization f).mp hf
  let D := ∑' n : ℕ, |exp (-(A * n)) * f n / (n.factorial : ℝ) ^ m|
  have hsabs : Summable (fun n : ℕ => |exp (-(A * n)) * f n / (n.factorial : ℝ) ^ m|) := by
    simpa only [Real.norm_eq_abs] using hs.norm
  refine ⟨m, A, D, hA, tsum_nonneg (fun _ => abs_nonneg _), ?_⟩
  intro n
  have hF : 0 < (n.factorial : ℝ) ^ m := pow_pos (by exact_mod_cast Nat.factorial_pos n) _
  have hle : |exp (-(A * n)) * f n / (n.factorial : ℝ) ^ m| ≤ D :=
    hsabs.le_tsum n (fun _ _ => abs_nonneg _)
  rw [abs_div, abs_mul, abs_of_pos (exp_pos _), abs_of_pos hF] at hle
  have hm := mul_le_mul_of_nonneg_left ((div_le_iff₀ hF).mp hle) (exp_pos (A * n)).le
  rw [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul] at hm
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hm

/-- A global factorial envelope gives a summable normalization and an
absolute-sum bound using the same prefactor and the geometric exponential sum. -/
theorem weilLogShift_factorial_normalization_summable_bound (f : ℕ → ℝ) (m : ℕ)
    (A D : ℝ) (hf : ∀ n : ℕ, |f n| ≤ D * exp (A * n) * (n.factorial : ℝ) ^ m) :
    Summable (fun n : ℕ => exp (-((A + 1) * n)) * f n / (n.factorial : ℝ) ^ m) ∧
      (∑' n : ℕ, |exp (-((A + 1) * n)) * f n / (n.factorial : ℝ) ^ m|) ≤
        D * ∑' n : ℕ, exp (-n) := by
  have hbound (n : ℕ) := weilLogShift_factorial_normalization_abs_le f m A D n (hf n)
  have hg : Summable (fun n : ℕ => D * exp (-n)) := summable_exp_neg_nat.mul_left D
  have hs : Summable (fun n : ℕ => exp (-((A + 1) * n)) * f n / (n.factorial : ℝ) ^ m) :=
    hg.of_norm_bounded (fun n => by simpa only [Real.norm_eq_abs] using hbound n)
  have hsabs : Summable (fun n : ℕ => |exp (-((A + 1) * n)) * f n / (n.factorial : ℝ) ^ m|) := by
    simpa only [Real.norm_eq_abs] using hs.norm
  refine ⟨hs, ?_⟩
  simpa only [tsum_mul_left] using Summable.tsum_le_tsum hbound hsabs hg

end RHTower

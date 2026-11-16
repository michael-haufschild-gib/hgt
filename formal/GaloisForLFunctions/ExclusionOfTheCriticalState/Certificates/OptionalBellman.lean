import GaloisForLFunctions.ExclusionOfTheCriticalState.Certificates.FiniteBellman

/-!
# The information lost by allowing zero-duration steps

The optional Bellman operator takes the smaller of the present candidate and
the stopped step. Its fixed points have an exact classification: accumulated
cost minus an arbitrary nonnegative accumulated deficit. The true value is
their greatest member, but a zero optional residual does not determine it.

This specializes Proposition 7 of arXiv:2611.16663 to signed finite chains.
-/

open scoped BigOperators

namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FiniteBellman

noncomputable section

/-- Permit either remaining at the current node or taking one descending step. -/
def optional (c W : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => min (W (n + 1)) (c n + W n)

/-- Optional fixed points are exactly the candidates with nonpositive edge defects. -/
theorem optional_fixed_iff (c W : ℕ → ℝ) :
    optional c W = W ↔ W 0 = 0 ∧ ∀ n, residual c W n ≤ 0 := by
  constructor
  · intro h
    refine ⟨(congrFun h 0).symm, fun n => ?_⟩
    have hn := congrFun h (n + 1)
    change min (W (n + 1)) (c n + W n) = W (n + 1) at hn
    have hle := min_eq_left_iff.mp hn
    unfold residual
    linarith only [hle]
  · rintro ⟨h0, hr⟩
    funext n
    cases n with
    | zero => exact h0.symm
    | succ n =>
      apply min_eq_left
      have h := hr n
      unfold residual at h
      linarith only [h]

/-- Complete fixed-point classification by nonnegative deficit increments. -/
theorem optional_fixed_classification (c W : ℕ → ℝ) :
    optional c W = W ↔
      ∃ d : ℕ → ℝ, (∀ j, 0 ≤ d j) ∧ W = fun n => value c n - value d n := by
  rw [optional_fixed_iff]
  constructor
  · rintro ⟨h0, hr⟩
    refine ⟨fun j => -residual c W j, fun j => neg_nonneg.mpr (hr j), ?_⟩
    funext n
    have h := error_eq c W n
    rw [h0, zero_add] at h
    simp only [value, Finset.sum_neg_distrib]
    unfold value at h
    linarith only [h]
  · rintro ⟨d, hd, rfl⟩
    refine ⟨by simp, fun n => ?_⟩
    simp only [residual, value_succ]
    linarith only [hd n]

/-- The true value is the greatest optional fixed point. -/
theorem optional_greatest_fixed (c : ℕ → ℝ) :
    optional c (value c) = value c ∧
      ∀ W, optional c W = W → ∀ n, W n ≤ value c n := by
  constructor
  · apply (optional_fixed_iff c _).mpr
    refine ⟨value_zero c, fun n => ?_⟩
    simp only [residual, value_succ]
    linarith
  · intro W hW n
    obtain ⟨d, hd, rfl⟩ := (optional_fixed_classification c W).mp hW
    exact sub_le_self _ (Finset.sum_nonneg fun j _ => hd j)

/-- Arbitrarily large errors coexist with a zero optional residual, for every cost sequence. -/
theorem optional_arbitrary_error (c : ℕ → ℝ) (a : ℝ) :
    ∃ W : ℕ → ℝ, optional c W = W ∧
      ∀ n, value c n - W n = (n : ℝ) * |a| := by
  refine ⟨fun n => value c n - value (fun _ => |a|) n, ?_, fun n => ?_⟩
  · exact (optional_fixed_classification c _).mpr
      ⟨fun _ => |a|, fun _ => abs_nonneg a, rfl⟩
  · simp only [value, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring

/-- For an optional fixed point, the stopped residual records the whole missing value. -/
theorem deficit_reconstruction (c d : ℕ → ℝ) (n : ℕ) :
    residual c (fun j => value c j - value d j) n = -d n ∧
      value c n - (value c n - value d n) = value d n := by
  simp only [residual, value_succ]
  constructor <;> ring

#print axioms optional_fixed_classification
#print axioms optional_greatest_fixed
#print axioms optional_arbitrary_error

end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FiniteBellman

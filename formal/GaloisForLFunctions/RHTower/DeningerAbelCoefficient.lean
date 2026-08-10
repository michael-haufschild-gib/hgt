import GaloisForLFunctions.RHTower.DeningerMobiusAbel
import GaloisForLFunctions.RHTower.DeningerLogPullDeriv

/-!
# The Abel coefficient sequence

Integrating one Abel difference against `dx` produces the coefficient `1/(i(i+1))`: the set of
dilations carrying a fixed point `u` into the `i`-th window is the interval `[u/(i+1), u/i]`, of
length `u/(i(i+1))`.

Summing those coefficients against the summatory function is therefore controlled by the same
inverse-square series that the unconditional Möbius saving already gives.

* `deningerAbelWindow_volume` : the window has length `u/(i(i+1))`.
* `deningerAbelCoefficient_summable` : **`∑_i |M(i)|/(i(i+1)) < ∞`.**
-/

namespace RHTower

open MeasureTheory

noncomputable section

/-- **The dilation window.**  For `u > 0` and `i ≥ 1`, the dilations carrying `u` into the `i`-th
Abel window form the interval `[u/(i+1), u/i]`, whose length is `u/(i(i+1))`. -/
theorem deningerAbelWindow_volume {i : ℕ} (hi : 0 < i) (u : ℝ) :
    {x : ℝ | (i : ℝ) * x ≤ u ∧ u ≤ ((i : ℝ) + 1) * x}
      = Set.Icc (u / ((i : ℝ) + 1)) (u / (i : ℝ)) := by
  have hir : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
  have hi1 : (0 : ℝ) < (i : ℝ) + 1 := by linarith
  ext x
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [div_le_iff₀ hi1, mul_comm]
      exact h2
    · rw [le_div_iff₀ hir, mul_comm]
      exact h1
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have hx := (le_div_iff₀ hir).mp h2
      rw [mul_comm]
      exact hx
    · have hx := (div_le_iff₀ hi1).mp h1
      rw [mul_comm]
      exact hx

/-- The length of the dilation window. -/
theorem deningerAbelWindow_length {i : ℕ} (hi : 0 < i) (u : ℝ) :
    u / (i : ℝ) - u / ((i : ℝ) + 1) = u / ((i : ℝ) * ((i : ℝ) + 1)) := by
  have hir : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
  have hi1 : (0 : ℝ) < (i : ℝ) + 1 := by linarith
  field_simp
  ring

/-- **The Abel coefficient sequence is summable.**  The coefficients `1/(i(i+1))` are dominated by
`1/i²`, so the unconditional saving already controls them. -/
theorem deningerAbelCoefficient_summable :
    Summable fun i : ℕ => |Sieve.mertensM i| / ((i : ℝ) * ((i : ℝ) + 1)) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
    deningerMertensM_invSq_summable
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · have hir : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
      positivity
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · have hir : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
      have hsq : (i : ℝ) ^ 2 ≤ (i : ℝ) * ((i : ℝ) + 1) := by nlinarith
      refine div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hsq
end

end RHTower

/-! ## The window as a measurable set of the plane -/

namespace RHTower

noncomputable section

open MeasureTheory

/-- **The measure of the dilation window.** -/
theorem deningerAbelWindow_measure {i : ℕ} (hi : 0 < i) (u : ℝ) :
    volume {x : ℝ | (i : ℝ) * x ≤ u ∧ u ≤ ((i : ℝ) + 1) * x}
      = ENNReal.ofReal (u / ((i : ℝ) * ((i : ℝ) + 1))) := by
  rw [deningerAbelWindow_volume hi u, Real.volume_Icc, deningerAbelWindow_length hi u]

/-- The window, as a set of the plane, is measurable: it is cut out by two closed conditions. -/
theorem deningerAbelWindow_measurableSet (i : ℕ) :
    MeasurableSet {p : ℝ × ℝ | (i : ℝ) * p.1 ≤ p.2 ∧ p.2 ≤ ((i : ℝ) + 1) * p.1} := by
  have h1 : MeasurableSet {p : ℝ × ℝ | (i : ℝ) * p.1 ≤ p.2} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have h2 : MeasurableSet {p : ℝ × ℝ | p.2 ≤ ((i : ℝ) + 1) * p.1} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  exact h1.inter h2

end

end RHTower

import Mathlib

/-!
# The Guth–Maynard large values estimate as a statement

Guth–Maynard, Theorem 1.1: let `(b_n)` be complex with `|b_n| ≤ 1`, let `W` be a `1`-separated set
in an interval of length `T`, and let `|Σ_{N < n ≤ 2N} b_n n^{it}| ≥ V` for every `t ∈ W`.  Then

`|W| ≤ T^{o(1)} (N² V⁻² + N^{18/5} V⁻⁴ + T N^{12/5} V⁻⁴)`.

`GuthMaynardLargeValuesBound` is this statement with `T^{o(1)}` written as `C_ε T^ε`.  Its
consequence `GuthMaynardLargeValuesBound.scaled` treats coefficients bounded by any `B > 0`:
the right-hand side becomes `B² N² V⁻² + B⁴ N^{18/5} V⁻⁴ + T B⁴ N^{12/5} V⁻⁴`.
-/

set_option autoImplicit false

namespace RHTower.GuthMaynard

/-- **Guth–Maynard, Theorem 1.1.**  For every `ε > 0` there is `C ≥ 0` such that every
`1`-separated set `W ⊆ [T₀, T₀ + T]` on which `|Σ_{N < n ≤ 2N} b_n n^{it}| ≥ V` (`|b_n| ≤ 1`) has
`|W| ≤ C T^ε (N²/V² + N^{18/5}/V⁴ + T N^{12/5}/V⁴)`. -/
def GuthMaynardLargeValuesBound : Prop :=
  ∀ {ε : ℝ}, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (T T₀ V : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
    1 ≤ N → 2 ≤ T → 0 < V → (∀ n, ‖b n‖ ≤ 1) → (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) →
    (∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) →
    (∀ t ∈ W, V ≤ ‖∑ n ∈ Finset.Ioc N (2 * N), b n * Complex.exp (Complex.I * t * Real.log n)‖) →
    (W.card : ℝ) ≤ C * T ^ ε * ((N : ℝ) ^ 2 / V ^ 2 + (N : ℝ) ^ (18/5 : ℝ) / V ^ 4
      + T * (N : ℝ) ^ (12/5 : ℝ) / V ^ 4)

/-- **Coefficients bounded by `B`.**  Dividing `b` and `V` by `B` turns the three terms into
`B² N²/V²`, `B⁴ N^{18/5}/V⁴` and `T B⁴ N^{12/5}/V⁴`. -/
theorem GuthMaynardLargeValuesBound.scaled (hGM : GuthMaynardLargeValuesBound) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (T T₀ V B : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      1 ≤ N → 2 ≤ T → 0 < V → 0 < B → (∀ n, ‖b n‖ ≤ B) → (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) →
      (∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) →
      (∀ t ∈ W, V ≤ ‖∑ n ∈ Finset.Ioc N (2 * N), b n * Complex.exp (Complex.I * t * Real.log n)‖) →
      (W.card : ℝ) ≤ C * T ^ ε * (B ^ 2 * (N : ℝ) ^ 2 / V ^ 2
        + B ^ 4 * (N : ℝ) ^ (18/5 : ℝ) / V ^ 4 + T * B ^ 4 * (N : ℝ) ^ (12/5 : ℝ) / V ^ 4) := by
  obtain ⟨C, hC, hbound⟩ := hGM hε
  refine ⟨C, hC, fun N T T₀ V B b W hN hT hV hB hb hW hsep hbig => ?_⟩
  have hBc : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hB.ne'
  -- the normalized coefficients `b/B` and level `V/B`
  have hnorm : ∀ n, ‖b n / (B : ℂ)‖ ≤ 1 := fun n => by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hB.le, div_le_one hB]
    exact hb n
  have hbig' : ∀ t ∈ W, V / B ≤
      ‖∑ n ∈ Finset.Ioc N (2 * N), b n / (B : ℂ) * Complex.exp (Complex.I * t * Real.log n)‖ := by
    intro t ht
    have hsum : ∑ n ∈ Finset.Ioc N (2 * N), b n / (B : ℂ) * Complex.exp (Complex.I * t * Real.log n)
        = (∑ n ∈ Finset.Ioc N (2 * N), b n * Complex.exp (Complex.I * t * Real.log n)) / (B : ℂ) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [hsum, norm_div, Complex.norm_real, Real.norm_of_nonneg hB.le]
    exact div_le_div_of_nonneg_right (hbig t ht) hB.le
  have h := hbound N T T₀ (V / B) (fun n => b n / (B : ℂ)) W hN hT (div_pos hV hB) hnorm hW hsep
    hbig'
  refine le_trans h (le_of_eq ?_)
  field_simp

end RHTower.GuthMaynard

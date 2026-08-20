import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Uniform gap of a blockwise scalar operator on a weighted Hilbert direct sum

The Hodge Laplacian of a coordinate-facet descent complex is the orthogonal direct sum of scalars
`n_α` over the monomial blocks, with `1 ≤ n_α ≤ N`.  This file proves, for an arbitrary Hilbert
direct sum `lp E 2` and an arbitrary diagonal real family, the three facts such an operator has:

* it is bounded by the uniform bound of the family;
* a lower bound `1 ≤ n_α` gives a uniform spectral gap `‖x‖ ≤ ‖Box x‖`, so `Box` is injective with
  closed range and zero is excluded from its spectrum;
* the pointwise inverse is again a blockwise operator, of norm at most one.

No compactness, finite-dimensionality, Fredholm assumption, or a priori closed-image hypothesis is
used: the statements are pure blockwise comparisons of `ℓ²` sums.
-/

noncomputable section

open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} {E : α → Type*} [∀ a, NormedAddCommGroup (E a)]
  [∀ a, NormedSpace ℝ (E a)]

theorem hasSum_sq_norm_lp (x : lp E 2) :
    HasSum (fun a => ‖(x : ∀ a, E a) a‖ ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (E := E) (p := 2) (by norm_num) x
  simpa using h

/-- **Blockwise upper bound.**  A diagonal family bounded by `N` gives an operator bounded by
`N`. -/
theorem norm_le_of_blockScalar {n : α → ℝ} {N : ℝ} (hN : 0 ≤ N) (hn : ∀ a, |n a| ≤ N)
    {x y : lp E 2} (hxy : ∀ a, (y : ∀ a, E a) a = n a • (x : ∀ a, E a) a) :
    ‖y‖ ≤ N * ‖x‖ := by
  have hle : ∀ a, ‖(y : ∀ a, E a) a‖ ^ 2 ≤ N ^ 2 * ‖(x : ∀ a, E a) a‖ ^ 2 := by
    intro a
    rw [hxy a, norm_smul, Real.norm_eq_abs, mul_pow]
    have h1 : |n a| ^ 2 ≤ N ^ 2 := by
      have := hn a
      nlinarith [abs_nonneg (n a)]
    have h2 : (0 : ℝ) ≤ ‖(x : ∀ a, E a) a‖ ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right h1 h2
  have hsq : ‖y‖ ^ 2 ≤ N ^ 2 * ‖x‖ ^ 2 :=
    hasSum_le hle (hasSum_sq_norm_lp y) ((hasSum_sq_norm_lp x).mul_left (N ^ 2))
  nlinarith [norm_nonneg y, norm_nonneg x, mul_nonneg hN (norm_nonneg x)]

/-- **The uniform spectral gap.**  A diagonal family bounded below by one gives an operator bounded
below by one, hence injective with closed range. -/
theorem norm_le_of_one_le_blockScalar {n : α → ℝ} (hn : ∀ a, 1 ≤ n a)
    {x y : lp E 2} (hxy : ∀ a, (y : ∀ a, E a) a = n a • (x : ∀ a, E a) a) :
    ‖x‖ ≤ ‖y‖ := by
  have hle : ∀ a, ‖(x : ∀ a, E a) a‖ ^ 2 ≤ ‖(y : ∀ a, E a) a‖ ^ 2 := by
    intro a
    rw [hxy a, norm_smul, Real.norm_eq_abs, mul_pow]
    have h1 : (1 : ℝ) ≤ |n a| ^ 2 := by
      have h := hn a
      have habs : (1 : ℝ) ≤ |n a| := le_trans h (le_abs_self (n a))
      nlinarith
    nlinarith [sq_nonneg ‖(x : ∀ a, E a) a‖]
  have hsq : ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 :=
    hasSum_le hle (hasSum_sq_norm_lp x) (hasSum_sq_norm_lp y)
  nlinarith [norm_nonneg x, norm_nonneg y]

/-- **The blockwise inverse.**  A diagonal family bounded below by one has a blockwise inverse of
norm at most one. -/
theorem exists_blockScalar_inverse {n : α → ℝ} (hn : ∀ a, 1 ≤ n a) (x : lp E 2) :
    ∃ z : lp E 2, (∀ a, n a • (z : ∀ a, E a) a = (x : ∀ a, E a) a) ∧ ‖z‖ ≤ ‖x‖ := by
  have hne : ∀ a, n a ≠ 0 := fun a => ne_of_gt (lt_of_lt_of_le zero_lt_one (hn a))
  have hmem : Memℓp (fun a => (n a)⁻¹ • (x : ∀ a, E a) a) 2 := by
    refine memℓp_gen ?_
    have hsum : Summable (fun a => ‖(x : ∀ a, E a) a‖ ^ (2 : ℝ)) := by
      have h := lp.hasSum_norm (E := E) (p := 2) (by norm_num) x
      simpa using h.summable
    refine Summable.of_nonneg_of_le (fun a => by positivity) (fun a => ?_) hsum
    have hxa : ‖(n a)⁻¹ • (x : ∀ a, E a) a‖ ≤ ‖(x : ∀ a, E a) a‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv]
      have h1 : (1 : ℝ) ≤ |n a| := le_trans (hn a) (le_abs_self (n a))
      have h2 : |n a|⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]; right; exact h1
      nlinarith [norm_nonneg ((x : ∀ a, E a) a)]
    have h2 : ((2 : ℝ≥0∞).toReal) = 2 := by norm_num
    rw [h2]
    exact Real.rpow_le_rpow (norm_nonneg _) hxa (by norm_num)
  refine ⟨⟨fun a => (n a)⁻¹ • (x : ∀ a, E a) a, hmem⟩, fun a => ?_, ?_⟩
  · show n a • ((n a)⁻¹ • (x : ∀ a, E a) a) = (x : ∀ a, E a) a
    rw [smul_smul, mul_inv_cancel₀ (hne a), one_smul]
  · refine norm_le_of_blockScalar (n := fun a => (n a)⁻¹) (N := 1) zero_le_one (fun a => ?_)
      (x := x) (y := ⟨fun a => (n a)⁻¹ • (x : ∀ a, E a) a, hmem⟩) (fun a => rfl) |>.trans ?_
    · rw [abs_inv]
      have h1 : (1 : ℝ) ≤ |n a| := le_trans (hn a) (le_abs_self (n a))
      rw [inv_le_one_iff₀]; right; exact h1
    · rw [one_mul]

end GaloisForLFunctions.HTGeometry

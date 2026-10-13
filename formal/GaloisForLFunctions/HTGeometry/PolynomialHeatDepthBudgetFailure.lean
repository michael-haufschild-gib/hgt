import GaloisForLFunctions.HTGeometry.PolynomialHeatNonrealCount
import GaloisForLFunctions.HTGeometry.ShiftAverageNonrealCount

/-!
# The heat flow has no depth-threshold budget for nonreal roots

For a real polynomial `p` the cosine shift obeys the depth budget
`Z_c(cos(hD)p) ≤ 2·#{roots w of p : Im w > h}` (`nonrealRootCount_shiftAvg_le`). The heat flow
`e^{−τD²}` agrees with `cos(hD)` to second order when `h² = 2τ`, and an isolated pair `±iy` is real
from `τ = y²/2` on. The analogous budget for the heat flow is false.

**Theorem** (`twoPairQuartic_depthBudget_fails`). Let `p = (X² + 1)(X² + 9)`. For `½ ≤ τ < 1` the
heat flow `e^{−τD²}p = X⁴ + (10 − 12τ)X² + (9 − 20τ + 12τ²)` has four nonreal roots, while only the
root `3i` of `p` has `Im w > √(2τ)`. Hence (`not_forall_nonrealRootCount_polyHeat_le_depth`) no
budget `Z_c(e^{−τD²}p) ≤ 2·#{Im w > √(2τ)}` holds for all real polynomials.

**Mechanism.** The deep pair `±3i` holds the shallow pair `±i` off the real axis. The quartic
has no real root for every `τ < 1` (`polyHeat_twoPairQuartic_eval_pos`): for `τ ≤ 5/6` all
coefficients are positive, and for `5/6 < τ < 1` it equals
`(x² + 5 − 6τ)² + 8(3τ − 2)(1 − τ)`. Both pairs reach the real axis together, as the double roots
`±1` of `e^{−D²}p = (X² − 1)²` (`polyHeat_one_twoPairQuartic`). The shallow pair is thus delayed
from `τ = ½` to `τ = 1`, and the deep pair is accelerated from `τ = 9/2` to `τ = 1`.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The quartic `(X² + 1)(X² + 9) = X⁴ + 10X² + 9`. -/
def twoPairQuartic : ℝ[X] := X ^ 4 + 10 * X ^ 2 + 9

/-- `p'' = 12X² + 20`. -/
theorem derivative_derivative_twoPairQuartic :
    derivative (derivative twoPairQuartic) = 12 * X ^ 2 + 20 := by
  apply Polynomial.funext; intro x
  simp [twoPairQuartic, derivative_mul]
  ring

/-- `p⁽⁴⁾ = 24`. -/
theorem iterate_four_derivative_twoPairQuartic :
    derivative^[4] twoPairQuartic = 24 := by
  apply Polynomial.funext; intro x
  simp [twoPairQuartic, derivative_mul, Function.iterate_succ_apply']
  norm_num

theorem natDegree_twoPairQuartic : twoPairQuartic.natDegree = 4 := by
  rw [twoPairQuartic]; compute_degree!

/-- `e^{−τD²}p = X⁴ + (10 − 12τ)X² + (9 − 20τ + 12τ²)`. -/
theorem polyHeat_twoPairQuartic (τ : ℝ) :
    polyHeat τ twoPairQuartic = X ^ 4 + C (10 - 12 * τ) * X ^ 2 + C (9 - 20 * τ + 12 * τ ^ 2) := by
  rw [polyHeat, natDegree_twoPairQuartic]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h6 : derivative^[2 * 3] twoPairQuartic = 0 :=
    iterate_derivative_eq_zero (by rw [natDegree_twoPairQuartic]; norm_num)
  have h8 : derivative^[2 * 4] twoPairQuartic = 0 :=
    iterate_derivative_eq_zero (by rw [natDegree_twoPairQuartic]; norm_num)
  have h2 : derivative^[2 * 1] twoPairQuartic = 12 * X ^ 2 + 20 := by
    rw [show 2 * 1 = 2 by rfl, Function.iterate_succ_apply', Function.iterate_one]
    exact derivative_derivative_twoPairQuartic
  have h4 : derivative^[2 * 2] twoPairQuartic = 24 := iterate_four_derivative_twoPairQuartic
  rw [h6, h8, h2, h4]
  apply Polynomial.funext; intro x
  simp [twoPairQuartic, Nat.factorial]
  ring

/-- The heat flow of `p` has no real root before `τ = 1`. -/
theorem polyHeat_twoPairQuartic_eval_pos {τ : ℝ} (hτ1 : τ < 1) (x : ℝ) :
    0 < (polyHeat τ twoPairQuartic).eval x := by
  rw [polyHeat_twoPairQuartic]
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  rcases le_or_gt τ (5 / 6) with h | h
  · nlinarith [sq_nonneg (τ - 5 / 6), mul_nonneg hx2 (by linarith : (0 : ℝ) ≤ 10 - 12 * τ),
      pow_two_nonneg (x ^ 2)]
  · nlinarith [sq_nonneg (x ^ 2 + 5 - 6 * τ), mul_pos (by linarith : (0 : ℝ) < 3 * τ - 2)
      (by linarith : (0 : ℝ) < 1 - τ)]

theorem polyHeat_twoPairQuartic_ne_zero (τ : ℝ) : polyHeat τ twoPairQuartic ≠ 0 :=
  (natDegree_polyHeat τ (p := twoPairQuartic) (fun h => by
    have := natDegree_twoPairQuartic; rw [h, natDegree_zero] at this; norm_num at this)).2

/-- **All four roots stay nonreal for `τ < 1`.** -/
theorem nonrealRootCount_polyHeat_twoPairQuartic {τ : ℝ} (hτ1 : τ < 1) :
    nonrealRootCount (polyHeat τ twoPairQuartic) = 4 := by
  have hne : twoPairQuartic ≠ 0 := fun h => by
    have := natDegree_twoPairQuartic; rw [h, natDegree_zero] at this; norm_num at this
  have hroots : (polyHeat τ twoPairQuartic).roots = 0 := by
    refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
    rw [mem_roots (polyHeat_twoPairQuartic_ne_zero τ), IsRoot.def] at hx
    exact (polyHeat_twoPairQuartic_eval_pos hτ1 x).ne' hx
  rw [nonrealRootCount, hroots, Multiset.card_zero, (natDegree_polyHeat τ hne).1,
    natDegree_twoPairQuartic]

/-- **The collapse.** At `τ = 1` both pairs have reached the real axis together:
`e^{−D²}(X⁴ + 10X² + 9) = (X² − 1)²`. -/
theorem polyHeat_one_twoPairQuartic : polyHeat 1 twoPairQuartic = (X ^ 2 - 1) ^ 2 := by
  rw [polyHeat_twoPairQuartic]
  apply Polynomial.funext; intro x
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C, eval_sub, eval_one]
  ring

/-- Over `ℂ`, `p = (X − i)(X + i)(X − 3i)(X + 3i)`. -/
theorem map_twoPairQuartic_eq :
    twoPairQuartic.map Complex.ofRealHom =
      (X - C Complex.I) * (X - C (-Complex.I)) * (X - C (3 * Complex.I)) *
        (X - C (-(3 * Complex.I))) := by
  apply Polynomial.funext; intro z
  simp only [twoPairQuartic, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_X,
    Polynomial.map_ofNat, eval_add, eval_mul, eval_pow, eval_X, eval_sub, eval_C, eval_ofNat]
  linear_combination (10 * z ^ 2 - 9 * (Complex.I ^ 2 - 1)) * Complex.I_sq

theorem roots_map_twoPairQuartic :
    (twoPairQuartic.map Complex.ofRealHom).roots =
      {Complex.I} + {-Complex.I} + {3 * Complex.I} + {-(3 * Complex.I)} := by
  rw [map_twoPairQuartic_eq]
  have h1 : ∀ a : ℂ, (X - C a) ≠ 0 := fun a => X_sub_C_ne_zero a
  rw [roots_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (h1 _) (h1 _)) (h1 _)) (h1 _)),
    roots_mul (mul_ne_zero (mul_ne_zero (h1 _) (h1 _)) (h1 _)),
    roots_mul (mul_ne_zero (h1 _) (h1 _)), roots_X_sub_C, roots_X_sub_C, roots_X_sub_C,
    roots_X_sub_C]

/-- Only the root `3i` lies above height `√(2τ)` for `½ ≤ τ < 1`. -/
theorem card_deep_roots_twoPairQuartic {τ : ℝ} (hτ0 : 1 / 2 ≤ τ) (hτ1 : τ < 1) :
    Multiset.card ((twoPairQuartic.map Complex.ofRealHom).roots.filter
      (fun w => Real.sqrt (2 * τ) < w.im)) = 1 := by
  have hs1 : 1 ≤ Real.sqrt (2 * τ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hs3 : Real.sqrt (2 * τ) < 3 := by
    rw [show (3 : ℝ) = Real.sqrt 9 by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
  rw [roots_map_twoPairQuartic]
  generalize Real.sqrt (2 * τ) = s at hs1 hs3
  have e1 : ¬ s < 1 := not_lt.mpr hs1
  have e2 : ¬ s < -1 := by linarith
  have e3 : ¬ s < -3 := by linarith
  simp [Multiset.filter_singleton, e1, e2, e3, hs3]

/-- **The heat flow has no depth-threshold budget.** For `½ ≤ τ < 1` the heat flow of
`(X² + 1)(X² + 9)` has four nonreal roots, while the cosine budget at the matched depth
`h = √(2τ)` would allow only `2·#{roots w : Im w > h} = 2`. -/
theorem twoPairQuartic_depthBudget_fails {τ : ℝ} (hτ0 : 1 / 2 ≤ τ) (hτ1 : τ < 1) :
    2 * Multiset.card ((twoPairQuartic.map Complex.ofRealHom).roots.filter
      (fun w => Real.sqrt (2 * τ) < w.im)) < nonrealRootCount (polyHeat τ twoPairQuartic) := by
  rw [card_deep_roots_twoPairQuartic hτ0 hτ1,
    nonrealRootCount_polyHeat_twoPairQuartic hτ1]
  norm_num

/-- The bound of `nonrealRootCount_shiftAvg_le` does not transfer to the heat flow at the
matched depth `√(2τ)`. -/
theorem not_forall_nonrealRootCount_polyHeat_le_depth :
    ¬ ∀ p : ℝ[X], p ≠ 0 → ∀ τ : ℝ, 0 < τ →
      nonrealRootCount (polyHeat τ p) ≤
        2 * Multiset.card ((p.map Complex.ofRealHom).roots.filter
          (fun w => Real.sqrt (2 * τ) < w.im)) := by
  intro h
  have hne : twoPairQuartic ≠ 0 := fun h0 => by
    have := natDegree_twoPairQuartic; rw [h0, natDegree_zero] at this; norm_num at this
  have := h twoPairQuartic hne (3 / 4) (by norm_num)
  exact absurd this (not_le.mpr (twoPairQuartic_depthBudget_fails (by norm_num) (by norm_num)))

end

end GaloisForLFunctions.HTGeometry

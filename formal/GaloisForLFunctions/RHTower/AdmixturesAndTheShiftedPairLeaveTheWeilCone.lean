import GaloisForLFunctions.RHTower.WeilConeUniquenessUnconditional
import GaloisForLFunctions.RHTower.WeilConeDegreeTwinRigidity
import GaloisForLFunctions.RHTower.NonTemperedShiftedZetaPairCountermodel

/-!
# Admixtures and the shifted pair leave the Weil cone

The full Weil cone of `ζ` is `{Λ}` under the Riemann hypothesis and empty otherwise
(`weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt`). Two obstructions that are usually
stated separately are readings of this one fact.

* **Admixture.** For every weight system `λ₀` and every `t ≠ 1`, the admixture
  `tΛ + (1 − t)λ₀` is full-cone Weil-positive iff RH holds and `λ₀ = Λ` on `n ≥ 2`
  (`weilPositiveFull_admixture_iff`): deforming any producer toward `Λ` by any amount keeps the
  whole RH content, because the cone has no second point to move toward.
* **The temperedness gate.** The weights `Λ_a(n) = Λ(n)(n^a + n^{−a})` of the shifted pair
  `ζ(s − a)ζ(s + a)` lie outside the full Weil cone of `ζ` for every `a`
  (`not_weilPositiveFull_shiftedPairVonMangoldt`), and in the degree-two cone, the cone of
  `ζ(s)^2`, they are positive exactly when RH holds and `a = 0`
  (`weilPositiveDegree_two_shiftedPairVonMangoldt_iff`). The cone reads the coefficient size at
  one node: `2^a + 2^{−a} = 2` forces `a = 0`.
-/

open Complex

namespace RHTower

open WeilSpectral

/-! ### 1. The admixture reading of uniqueness -/

/-- **Admixtures toward `Λ` keep the full RH content.** For `t ≠ 1`, `tΛ + (1 − t)λ₀` is full-cone
Weil-positive iff RH holds and `λ₀ = Λ` on `n ≥ 2`. -/
theorem weilPositiveFull_admixture_iff {t : ℝ} (ht : t ≠ 1) (lam₀ : ℕ → ℝ) :
    WeilPositiveFull (fun n => t * (ArithmeticFunction.vonMangoldt n : ℝ) + (1 - t) * lam₀ n) ↔
      RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam₀ n = ArithmeticFunction.vonMangoldt n := by
  rw [weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt]
  refine and_congr_right fun _ => ⟨fun h n hn => ?_, fun h n hn => ?_⟩
  · have h1 : (1 - t) * (lam₀ n - ArithmeticFunction.vonMangoldt n) = 0 := by
      linarith [h n hn]
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd (by linarith : t = 1) ht
    · linarith
  · rw [h n hn]; ring

/-! ### 2. The shifted pair at the node `2` -/

/-- `2 ≤ 2^a + 2^{−a}`: the arithmetic–geometric mean inequality at the node `2`. -/
theorem two_le_two_rpow_add_two_rpow_neg (a : ℝ) : 2 ≤ (2 : ℝ) ^ a + (2 : ℝ) ^ (-a) := by
  have hx : 0 < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
  rw [Real.rpow_neg (by norm_num)]
  have : (2 : ℝ) ^ a + ((2 : ℝ) ^ a)⁻¹ - 2 = ((2 : ℝ) ^ a - 1) ^ 2 / (2 : ℝ) ^ a := by
    field_simp; ring
  have h := div_nonneg (sq_nonneg ((2 : ℝ) ^ a - 1)) hx.le
  linarith

/-- Equality in the arithmetic–geometric mean inequality at the node `2` forces `a = 0`. -/
theorem eq_zero_of_two_rpow_add_two_rpow_neg_le {a : ℝ}
    (h : (2 : ℝ) ^ a + (2 : ℝ) ^ (-a) ≤ 2) : a = 0 := by
  have hx : 0 < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
  rw [Real.rpow_neg (by norm_num)] at h
  have h1 : ((2 : ℝ) ^ a - 1) ^ 2 / (2 : ℝ) ^ a ≤ 0 := by
    have : ((2 : ℝ) ^ a - 1) ^ 2 / (2 : ℝ) ^ a = (2 : ℝ) ^ a + ((2 : ℝ) ^ a)⁻¹ - 2 := by
      field_simp; ring
    linarith
  have h2 : ((2 : ℝ) ^ a - 1) ^ 2 = 0 := by
    have h3 : ((2 : ℝ) ^ a - 1) ^ 2 / (2 : ℝ) ^ a = 0 :=
      le_antisymm h1 (div_nonneg (sq_nonneg _) hx.le)
    rcases div_eq_zero_iff.mp h3 with h | h
    · exact h
    · exact absurd h hx.ne'
  have h4 : (2 : ℝ) ^ a = 1 := by nlinarith [sq_nonneg ((2 : ℝ) ^ a - 1)]
  have h5 := congrArg Real.log h4
  rw [Real.log_rpow (by norm_num), Real.log_one] at h5
  rcases mul_eq_zero.mp h5 with h | h
  · exact h
  · exact absurd h (Real.log_pos (by norm_num)).ne'

/-- **The shifted pair is outside the full Weil cone of `ζ` for every shift.** Uniqueness of the
cone would force `Λ_a(2) = Λ(2)`, that is `2^a + 2^{−a} = 1 < 2`. -/
theorem not_weilPositiveFull_shiftedPairVonMangoldt (a : ℝ) :
    ¬ WeilPositiveFull (shiftedPairVonMangoldt a) := by
  intro hW
  have h := eq_vonMangoldt_of_weilPositiveFull hW 2 le_rfl
  simp only [shiftedPairVonMangoldt, Nat.cast_ofNat,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two] at h
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hX : Real.log 2 * ((2 : ℝ) ^ a + (2 : ℝ) ^ (-a)) = Real.log 2 * 1 := by rw [h, mul_one]
  have := mul_left_cancel₀ hlog.ne' hX
  linarith [two_le_two_rpow_add_two_rpow_neg a]

/-- **In the degree-two cone the shifted-pair family meets positivity only at `ζ²` under RH.**
`Λ_a` is degree-two Weil-positive iff RH holds and `a = 0`. -/
theorem weilPositiveDegree_two_shiftedPairVonMangoldt_iff (a : ℝ) :
    WeilPositiveDegree 2 (shiftedPairVonMangoldt a) ↔ RiemannHypothesis ∧ a = 0 := by
  rw [weilPositiveDegree_iff (by norm_num : (0 : ℝ) < 2)]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h n hn => ?_⟩
  · have h2 := h 2 le_rfl
    simp only [shiftedPairVonMangoldt, Nat.cast_ofNat,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two] at h2
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hX : Real.log 2 * ((2 : ℝ) ^ a + (2 : ℝ) ^ (-a)) = Real.log 2 * 2 := by
      rw [h2]; ring
    exact eq_zero_of_two_rpow_add_two_rpow_neg_le (mul_left_cancel₀ hlog.ne' hX).le
  · subst h
    simp only [shiftedPairVonMangoldt, neg_zero, Real.rpow_zero]
    ring

end RHTower

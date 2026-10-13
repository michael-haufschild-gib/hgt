import Zeta23.Assembly

/-!
# The rank–trace counting step with weighted on-line contributions

Alpöge–Furman's counting step assumes each on-line zero contributes trace `1`.  If the zero vectors are
augmented by a second component — `u_ρ ⊗ (1, t g(ρ))` with `g = (χ^{-1/2} ζ)'` real on the line, so that
consecutive simple zeros carry opposite signs — then an on-line zero contributes `1 + t²|g(ρ)|²` and the
on-line trace is `N_on + E`, `E = t² ∑_on |g|²`.  The counting step survives with the excess
(`zeroside_rank_core_excess`):

`4 tr Â − 2N − 2E − ‖Â‖_F² ≤ rank P`.

With `tr Â = N + t²S`, `‖Â‖² = ‖Ĝ‖² + 2t²(S + O₁) + t⁴M₄` (`O₁` the `|K|²`-weighted correlation of `g`
over distinct zeros, `M₄` the weighted fourth moment) and `E ≤ t²S`, the certificate is the
Alpöge–Furman value `4N − 2N − ‖Ĝ‖²` plus `−2t²O₁ − t⁴M₄`, whose maximum over `t` is exactly `O₁²/M₄`
when `O₁ < 0` (`augmented_gain_max`, `augmented_gain_le`).  So the augmentation beats the pair-correlation
certificate precisely when the signs of `g` at nearby zeros are negatively correlated, and by
`O₁²/M₄`.
-/

open Matrix RHLinalg
open scoped ComplexOrder

noncomputable section

namespace RHTower

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The counting step with an on-line trace excess.** -/
theorem zeroside_rank_core_excess {Ahat P Q : Matrix n n 𝕜}
    (hPQ : Ahat = P + Q) (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hrank : P.rank ≤ r) (hpos : posIndex hQ ≤ b)
    {Non NI' E : ℝ} (htrP : rtrace P ≤ Non + E) (hNcount : Non + 2 * b ≤ NI') :
    4 * rtrace Ahat - 2 * NI' - 2 * E - frobSq Ahat ≤ r := by
  have h := rank_trace_ineq_two hP hQ hrank hpos
  subst hPQ
  rw [rtrace_add]
  linarith

/-- The augmented certificate as a function of `s = t²`. -/
def augmentedGain (O₁ M₄ s : ℝ) : ℝ := -2 * s * O₁ - s ^ 2 * M₄

/-- **The gain is at most `O₁²/M₄`.** -/
theorem augmented_gain_le {O₁ M₄ : ℝ} (hM : 0 < M₄) (s : ℝ) : augmentedGain O₁ M₄ s ≤ O₁ ^ 2 / M₄ := by
  unfold augmentedGain
  rw [le_div_iff₀ hM]
  nlinarith [sq_nonneg (s * M₄ + O₁)]

/-- **…and it is attained at `s = −O₁/M₄`, which is admissible (`s ≥ 0`) exactly when `O₁ ≤ 0`.** -/
theorem augmented_gain_max {O₁ M₄ : ℝ} (hM : 0 < M₄) :
    augmentedGain O₁ M₄ (-O₁ / M₄) = O₁ ^ 2 / M₄ := by
  unfold augmentedGain
  field_simp
  ring

theorem augmented_gain_nonpos_of_nonneg {O₁ M₄ : ℝ} (hO : 0 ≤ O₁) (hM : 0 ≤ M₄) {s : ℝ} (hs : 0 ≤ s) :
    augmentedGain O₁ M₄ s ≤ 0 := by
  unfold augmentedGain
  have : 0 ≤ s * O₁ := mul_nonneg hs hO
  have : 0 ≤ s ^ 2 * M₄ := mul_nonneg (sq_nonneg s) hM
  linarith

end RHTower
